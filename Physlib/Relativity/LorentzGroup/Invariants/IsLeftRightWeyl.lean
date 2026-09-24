/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Invariants.LorentzCovariance
public import Physlib.Mathematics.InvariantReduction
/-!
# Lorentz invariants of a left-handed and a right-handed Weyl index

A bispinor `T^{α α'}`, carrying one left-handed and one right-handed Weyl index, has no
Lorentz invariant in the span of its four components but `0`: the pair carries the
`(1/2, 1/2)` representation, a single four-vector index, which has nothing to contract with.
That is `eq_zero_of_invariant`, and `mem_of_invariant_of_mem_sup` is the same statement modulo
a Lorentz-stable subspace `S`, the form the Standard Model files use.

The components are vectors `T a` of a complex vector space `B` carrying a representation
`repLorentz` of `SL(2,ℂ)`, and `IsLeftRightWeyl` says the group moves the left index by the
matrix of `g` and the right index by its complex conjugate (A). An invariant of
`componentSpan T` is `∑_a c_a • T a` for a coefficient function `c` fixed by the action `act`
(A, from `Invariants.Basic`), and two elements of `SL(2,ℂ)` already force such a `c` to vanish
(B). Both are diagonal, and a diagonal `g = diag (λ₀, λ₁)` multiplies `c (a₁, a₂)` by
`λ_{a₁} * conj λ_{a₂}`. The boost `diag (t, t⁻¹)` along `z` scales `c (0, 0)` by `t²` and
`c (1, 1)` by `t⁻²`, so these vanish, and the half turn `diag (-i, i)` about `z` multiplies
`c (0, 1)` and `c (1, 0)` by `-i * conj i = -1`, so these vanish too. Invariance under the whole
group implies invariance under these two elements; nothing is claimed about the group they
generate. Section C divides out `S`.

The dual law, `(g⁻¹)ᵀ` on the undotted and `(g⁻¹)ᴴ` on the dotted slot, is
`IsDualLeftRightWeyl` in `IsVectorLeftRightWeyl`, which transports this classification to it.
-/

@[expose] public section

namespace Lorentz

open TensorProduct Matrix MatrixGroups SL2C Invariants

/-!

## A. Left-right bispinors and their coefficient functions

-/

/-- A family `T` indexed by one left-handed and one right-handed Weyl index, moved by
  `repLorentz` as a bispinor `T^{α α'}`: the left index by the matrix of `g` and the right
  index by its complex conjugate, the summed index first in each factor. -/
structure IsLeftRightWeyl (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B)
    (T : Fin 2 × Fin 2 → B) : Prop where
  repLorentz_T : ∀ (g : SL(2,ℂ)) l,
    repLorentz g (T l) = ∑ (a : Fin 2 × Fin 2),
      (g.1 a.1 l.1 * star (g.1 a.2 l.2)) • T a

namespace IsLeftRightWeyl

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {T : Fin 2 × Fin 2 → B}
  (hT : IsLeftRightWeyl B repLorentz T)

/-- The action of `g : SL(2,ℂ)` on coefficient functions,
  `act g c a = ∑ d, c d * (g a.1 d.1 * star (g a.2 d.2))`: the component matrix applied to `c`,
  with the free index first in each factor and the summed one second. -/
def act (g : SL(2,ℂ)) (c : Fin 2 × Fin 2 → ℂ) (a : Fin 2 × Fin 2) : ℂ :=
  ∑ d : Fin 2 × Fin 2, c d * (g.1 a.1 d.1 * star (g.1 a.2 d.2))

/-- A coefficient function fixed by every `g : SL(2,ℂ)`. -/
def IsInvariantCoeff (c : Fin 2 × Fin 2 → ℂ) : Prop := ∀ g : SL(2,ℂ), act g c = c

include hT in
/-- An invariant of the span is the contraction of an invariant coefficient function: the
  adjoint of the action of `g` is the action of `g†`. -/
lemma exists_isInvariantCoeff_of_mem_componentSpan {x : B} (hx : x ∈ componentSpan T)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ c : Fin 2 × Fin 2 → ℂ, IsInvariantCoeff c ∧ x = ∑ d, c d • T d := by
  obtain ⟨c, hc, hx'⟩ := Invariants.exists_invariantCoeff_matrix T (fun g => repLorentz g)
    (fun g a d => g.1 a.1 d.1 * star (g.1 a.2 d.2)) hT.repLorentz_T
    (fun g => ⟨Invariants.dagger g, fun a d => by
      simp [Invariants.dagger, Matrix.conjTranspose_apply, mul_comm]⟩)
    hx hinv
  exact ⟨c, hc, hx'⟩

/-!

## B. The boost and the half turn along `z` force the coefficients to vanish

Both elements used are diagonal, so `act` rescales each coefficient: `diag (λ₀, λ₁)` multiplies
`c (a₁, a₂)` by `λ_{a₁} * conj λ_{a₂}`, the right index taking the complex conjugate. The boost
along `z` at `t = 2` kills the two diagonal coefficients, and the half turn about `z` kills the
two mixed ones.

-/

/-- The boost `diag (t, t⁻¹)` along `z` scales `c (0, 0)` by `t * conj t = t²` and `c (1, 1)`
  by `t⁻²`; at `t = 2` invariance forces both to vanish. -/
lemma IsInvariantCoeff.apply_self_eq_zero {c : Fin 2 × Fin 2 → ℂ} (hc : IsInvariantCoeff c)
    (k : Fin 2) : c (k, k) = 0 := by
  have h := hc (SL2C.boostAxis 2 2 two_ne_zero)
  revert k
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · have h00 := congrFun h (0, 0)
    simp [act, Fintype.sum_prod_type, Fin.sum_univ_two, map_ofNat] at h00
    linear_combination h00 / 3
  · have h11 := congrFun h (1, 1)
    simp [act, Fintype.sum_prod_type, Fin.sum_univ_two, map_ofNat] at h11
    linear_combination -(4 / 3 : ℂ) * h11

/-- The half turn `diag (-i, i)` about `z` multiplies `c (0, 1)` by `-i * conj i = -1` and
  `c (1, 0)` by `i * conj (-i) = -1`, so invariance forces both mixed coefficients to vanish. -/
lemma IsInvariantCoeff.apply_eq_zero_of_ne {c : Fin 2 × Fin 2 → ℂ} (hc : IsInvariantCoeff c)
    {a : Fin 2 × Fin 2} (ha : a.1 ≠ a.2) : c a = 0 := by
  have h := hc (SL2C.halfTurn 2)
  have h01 := congrFun h (0, 1)
  have h10 := congrFun h (1, 0)
  simp [act, Fintype.sum_prod_type, Fin.sum_univ_two] at h01 h10
  obtain ⟨a₁, a₂⟩ := a
  fin_cases a₁ <;> fin_cases a₂
  · exact absurd rfl ha
  · show c (0, 1) = 0
    linear_combination -h01 / 2
  · show c (1, 0) = 0
    linear_combination -h10 / 2
  · exact absurd rfl ha

/-- An invariant coefficient function is zero: the boost kills its diagonal and the half turn
  its mixed coefficients. -/
lemma IsInvariantCoeff.eq_zero {c : Fin 2 × Fin 2 → ℂ} (hc : IsInvariantCoeff c) : c = 0 := by
  funext a
  by_cases ha : a.1 = a.2
  · obtain ⟨a₁, a₂⟩ := a
    simp only at ha
    subst ha
    exact hc.apply_self_eq_zero a₁
  · exact hc.apply_eq_zero_of_ne ha

include hT in
/-- Every Lorentz invariant in the span of the components is zero: the pair of indices carries
  the four-vector representation, which has no invariant contraction. -/
theorem eq_zero_of_invariant {x : B} (hx : x ∈ componentSpan T)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x = 0 := by
  obtain ⟨c, hc, rfl⟩ := hT.exists_isInvariantCoeff_of_mem_componentSpan hx hinv
  simp [hc.eq_zero]

/-!

## C. The classification modulo a Lorentz-stable submodule

A stable subspace `S` is divided out by passing to the quotient `B ⧸ S`: the classes of the
components again form a bispinor, so the classification applies there and lifts back with an
error term in `S`.

-/

include hT in
/-- The images of the components in the quotient by a Lorentz-stable submodule again
  form a left-right bispinor. -/
lemma isLeftRightWeyl_quotient (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) :
    IsLeftRightWeyl (B ⧸ S) (repLorentz.quotient S fun g y hy => hS g y hy)
      (fun l => S.mkQ (T l)) where
  repLorentz_T g l := by
    rw [quotient_apply_mkQ, hT.repLorentz_T g l, map_sum]
    exact Finset.sum_congr rfl fun a _ => map_smul _ _ _

include hT in
/-- A Lorentz invariant of `componentSpan T ⊔ S`, for a Lorentz-stable subspace `S`, already
  lies in `S`. -/
lemma mem_of_invariant_of_mem_sup {x : B} (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S)
    (hx : x ∈ componentSpan T ⊔ S) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  have h := IsStableUnder.mem_sup_of_quotient (σ := fun g : SL(2,ℂ) => repLorentz g) (W := ⊥) hS
    (fun y hy hyinv => by
      rw [Submodule.map_bot, Submodule.mem_bot]
      exact (hT.isLeftRightWeyl_quotient S hS).eq_zero_of_invariant
        ((Submodule.map_iSup_span_singleton S.mkQ T).le hy) hyinv) hx hinv
  rwa [bot_sup_eq] at h

end IsLeftRightWeyl

end Lorentz
