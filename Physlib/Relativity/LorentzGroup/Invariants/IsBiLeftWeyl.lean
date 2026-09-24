/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Invariants.IsLeftRightWeyl
public import Physlib.Relativity.Fermions.Weyl.Metric
public import Physlib.Mathematics.InvariantReduction
/-!
# Lorentz invariants of two left-handed Weyl indices

Every Lorentz invariant in the span of the components of a family `T^{α₁ α₂}` carrying two
left-handed Weyl indices is a multiple of the antisymmetric contraction

`epsilonContraction = ε_{α β} T^{α β}`,

the shape of a Majorana or Dirac mass term. That is
`exists_smul_epsilonContraction_of_invariant`, with
`exists_smul_epsilonContraction_of_invariant_subset` the same statement modulo a
Lorentz-stable subspace `S`; `repLorentz_epsilonContraction` checks that the contraction is
invariant.

The components are vectors `T a` of a complex vector space `B` carrying a representation
`repLorentz` of `SL(2,ℂ)`, and `IsBiLeftWeyl` says the group moves each index by the matrix
of `g` (A). An invariant of `componentSpan T` is `∑_a c_a • T a` for a coefficient function `c`
fixed by the action `act` (A, from `Invariants.Basic`), where `g` moves `c` by the component
matrix `g_{a₁ d₁} g_{a₂ d₂}`, with no complex conjugation. Two elements of `SL(2,ℂ)` pin `c`
down (C). The boost `diag (t, t⁻¹)` along `z` scales `c (0, 0)` by `t²` and `c (1, 1)` by
`t⁻²`, so these vanish. The half turn `!![0, -i; -i, 0]` about `x` swaps the two values of each
index with a factor `-i`, so it sends `c (a₁, a₂)` to `(-i)² c (1 - a₁, 1 - a₂)`, and invariance
gives `c (1, 0) = -c (0, 1)`. What is left is `c (0, 1)` times the `ε` symbol (B). Invariance
under the whole group implies invariance under these two elements; nothing is claimed about
the group they generate. Section D divides out `S`.

Sections E and F transport the classification to dual Weyl indices, which transform by
`(g⁻¹)ᵀ` on an undotted slot and by `(g⁻¹)ᴴ` on a dotted one. The symplectic form `ε` of
`Fermions.Weyl.Metric` satisfies `ε g⁻¹ = gᵀ ε`, so re-indexing both slots by `ε` turns a
dual family into a fundamental one for the same representation. Entrywise conjugation is the
involutive automorphism `SL2C.conjHom` of `SL(2,ℂ)`, so a dotted family is an undotted one for
the twisted representation `repLorentz.comp conjHom`, and invariance under the twist is
invariance under `repLorentz`, the twist being surjective.
-/

@[expose] public section

namespace Lorentz

open TensorProduct Matrix MatrixGroups SL2C Invariants

/-!

## A. Bi-left-handed Weyl tensors and their coefficient functions

-/

/-- A family `T` indexed by two left-handed Weyl indices, moved by `repLorentz` as a tensor
  `T^{α₁ α₂}`: each index by the matrix of `g`, the summed index first in each factor. -/
structure IsBiLeftWeyl (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B)
    (T : Fin 2 × Fin 2 → B) : Prop where
  repLorentz_T : ∀ (g : SL(2,ℂ)) l,
    repLorentz g (T l) = ∑ (a : Fin 2 × Fin 2), (g.1 a.1 l.1 * g.1 a.2 l.2) • T a

namespace IsBiLeftWeyl

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {T : Fin 2 × Fin 2 → B}
  (hT : IsBiLeftWeyl B repLorentz T)

/-- The action of `g : SL(2,ℂ)` on coefficient functions,
  `act g c a = ∑ d, c d * (g a.1 d.1 * g a.2 d.2)`: the component matrix applied to `c`, with
  the free index first in each factor and the summed one second. -/
def act (g : SL(2,ℂ)) (c : Fin 2 × Fin 2 → ℂ) (a : Fin 2 × Fin 2) : ℂ :=
  ∑ d : Fin 2 × Fin 2, c d * (g.1 a.1 d.1 * g.1 a.2 d.2)

/-- A coefficient function fixed by every `g : SL(2,ℂ)`. -/
def IsInvariantCoeff (c : Fin 2 × Fin 2 → ℂ) : Prop := ∀ g : SL(2,ℂ), act g c = c

include hT in
/-- An invariant of the span is the contraction of an invariant coefficient function: the
  adjoint of the action of `g` is the action of `g†`. -/
lemma exists_isInvariantCoeff_of_mem_componentSpan {x : B} (hx : x ∈ componentSpan T)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ c : Fin 2 × Fin 2 → ℂ, IsInvariantCoeff c ∧ x = ∑ d, c d • T d := by
  obtain ⟨c, hc, hx'⟩ := Invariants.exists_invariantCoeff_matrix T (fun g => repLorentz g)
    (fun g a d => g.1 a.1 d.1 * g.1 a.2 d.2) hT.repLorentz_T
    (fun g => ⟨Invariants.dagger g, fun a d => by
      simp [Invariants.dagger, Matrix.conjTranspose_apply]⟩)
    hx hinv
  exact ⟨c, hc, hx'⟩

/-!

## B. The epsilon contraction

The `ε` symbol, in the convention of `Fermion.metricRaw`, contracts the two indices
antisymmetrically, and the contraction is invariant because `det g = 1`.

-/

/-- The `ε` symbol on a pair of same-handedness spinor indices, in the convention of
  `Fermion.metricRaw`: `epsZ (0, 1) = 1`. -/
def epsZ (α : Fin 2 × Fin 2) : ℤ :=
  if α = (0, 1) then 1 else if α = (1, 0) then -1 else 0

/-- The `ε` contraction `ε_{α β} T^{α β}` of two same-handedness Weyl indices, the shape of a
  fermion mass term. -/
noncomputable def epsilonContraction : B :=
  ∑ α : Fin 2 × Fin 2, ((epsZ α : ℤ) : ℂ) • T α

/-- The `ε` contraction written out: the antisymmetric combination of the two mixed
  components. -/
lemma epsilonContraction_eq :
    epsilonContraction (T := T) = T (0, 1) - T (1, 0) := by
  rw [epsilonContraction]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, epsZ]
  module

include hT in
/-- The `ε` contraction is Lorentz invariant: the antisymmetric combination picks out
  the determinant of the `SL(2,ℂ)` matrix, which is one. -/
lemma repLorentz_epsilonContraction (g : SL(2,ℂ)) :
    repLorentz g (epsilonContraction (T := T)) = epsilonContraction (T := T) := by
  have hdet : g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0 = 1 := by
    have h := g.2
    rwa [Matrix.det_fin_two] at h
  rw [epsilonContraction_eq, map_sub, hT.repLorentz_T, hT.repLorentz_T]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  match_scalars
  · ring
  · linear_combination hdet
  · linear_combination -hdet
  · ring

/-!

## C. The boost along `z` and the half turn about `x` force the `ε` form

The boost along `z` is diagonal, so `act` rescales each coefficient and kills the two diagonal
ones. The half turn about `x` is antidiagonal, so `act` moves each coefficient to the opposite
pair of index values with the factor `(-i)² = -1`, which makes the coefficients antisymmetric.

-/

/-- The boost `diag (t, t⁻¹)` along `z` scales `c (0, 0)` by `t²` and `c (1, 1)` by `t⁻²`; at
  `t = 2` invariance forces both to vanish. -/
lemma IsInvariantCoeff.apply_self_eq_zero {c : Fin 2 × Fin 2 → ℂ} (hc : IsInvariantCoeff c)
    (k : Fin 2) : c (k, k) = 0 := by
  have h := hc (SL2C.boostAxis 2 2 two_ne_zero)
  revert k
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · have h00 := congrFun h (0, 0)
    simp [act, Fintype.sum_prod_type, Fin.sum_univ_two] at h00
    linear_combination h00 / 3
  · have h11 := congrFun h (1, 1)
    simp [act, Fintype.sum_prod_type, Fin.sum_univ_two] at h11
    linear_combination -(4 / 3 : ℂ) * h11

/-- An invariant coefficient function is antisymmetric. The half turn `!![0, -i; -i, 0]` about
  `x` sends `c (0, 1)` to `(-i)² c (1, 0) = -c (1, 0)`, and the diagonal coefficients vanish by
  the boost. -/
lemma IsInvariantCoeff.eq_neg_swap {c : Fin 2 × Fin 2 → ℂ} (hc : IsInvariantCoeff c)
    (a : Fin 2 × Fin 2) : c a = -c a.swap := by
  have h01 := congrFun (hc (SL2C.halfTurn 0)) (0, 1)
  simp [act, Fintype.sum_prod_type, Fin.sum_univ_two] at h01
  obtain ⟨a₁, a₂⟩ := a
  fin_cases a₁ <;> fin_cases a₂
  · simp [hc.apply_self_eq_zero 0]
  · show c (0, 1) = -c (1, 0)
    linear_combination -h01
  · show c (1, 0) = -c (0, 1)
    linear_combination -h01
  · simp [hc.apply_self_eq_zero 1]

/-- An invariant coefficient function is `c (0, 1)` times the `ε` symbol. -/
lemma IsInvariantCoeff.eq_smul_epsZ {c : Fin 2 × Fin 2 → ℂ} (hc : IsInvariantCoeff c)
    (a : Fin 2 × Fin 2) : c a = c (0, 1) * ((epsZ a : ℤ) : ℂ) := by
  obtain ⟨a₁, a₂⟩ := a
  fin_cases a₁ <;> fin_cases a₂
  · simp [hc.apply_self_eq_zero 0, epsZ]
  · simp [epsZ]
  · simpa [epsZ] using hc.eq_neg_swap (1, 0)
  · simp [hc.apply_self_eq_zero 1, epsZ]

include hT in
/-- The classification of the Lorentz invariants: every element of the span of the
  components fixed by the Lorentz group is a scalar multiple of the `ε` contraction. -/
theorem exists_smul_epsilonContraction_of_invariant {x : B} (hx : x ∈ componentSpan T)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, x = a • epsilonContraction (T := T) := by
  obtain ⟨c, hc, rfl⟩ := hT.exists_isInvariantCoeff_of_mem_componentSpan hx hinv
  refine ⟨c (0, 1), ?_⟩
  rw [epsilonContraction, Finset.smul_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [smul_smul, ← hc.eq_smul_epsZ a]

/-!

## D. The classification modulo a Lorentz-stable submodule

A stable subspace `S` is divided out by passing to the quotient `B ⧸ S`: the classes of the
components again form a bi-left-handed tensor, so the classification applies there and lifts
back with an error term in `S`.

-/

include hT in
/-- The images of the components in the quotient by a Lorentz-stable submodule again
  form a bi-left-handed Weyl tensor. -/
lemma isBiLeftWeyl_quotient (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) :
    IsBiLeftWeyl (B ⧸ S) (repLorentz.quotient S fun g y hy => hS g y hy)
      (fun l => S.mkQ (T l)) where
  repLorentz_T g l := by
    rw [quotient_apply_mkQ, hT.repLorentz_T g l, map_sum]
    exact Finset.sum_congr rfl fun a _ => map_smul _ _ _

/-- The quotient map carries the `ε` contraction to the `ε` contraction of the
  images. -/
lemma mkQ_epsilonContraction (S : Submodule ℂ B) :
    S.mkQ (epsilonContraction (T := T))
      = epsilonContraction (T := fun l => S.mkQ (T l)) := by
  rw [epsilonContraction, epsilonContraction, map_sum]
  exact Finset.sum_congr rfl fun α _ => map_smul _ _ _

include hT in
/-- The same modulo a Lorentz-stable subspace `S`: a multiple of the `ε` contraction plus an
  error in `S`. -/
lemma exists_smul_epsilonContraction_of_invariant_subset {x : B} (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S)
    (hx : x ∈ componentSpan T ⊔ S) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, ∃ y ∈ S, x = a • epsilonContraction (T := T) + y := by
  obtain ⟨a, y, hy, rfl, -⟩ := IsStableUnder.exists_smul_add_of_quotient
    (σ := fun g : SL(2,ℂ) => repLorentz g) hS hT.repLorentz_epsilonContraction
    (fun z hz hzinv => by
      rw [mkQ_epsilonContraction]
      exact (hT.isBiLeftWeyl_quotient S hS).exists_smul_epsilonContraction_of_invariant
        ((Submodule.map_iSup_span_singleton S.mkQ T).le hz) hzinv) hx hinv
  exact ⟨a, y, hy, rfl⟩

end IsBiLeftWeyl

/-!

## E. Dual-index families and the `ε` re-index

`IsBiDualLeftWeyl` and `IsBiDualRightWeyl` are the laws the Standard Model's fermion symbols
carry: one factor of `(g⁻¹)ᵀ` per index for an undotted pair, one of `(g⁻¹)ᴴ` for a dotted
pair; `isBiDualLeftWeyl_dualLeftHandedWeyl` and `isBiDualRightWeyl_dualRightHandedWeyl` pin
them to the tensor squares of the repository's dual Weyl representations, and both laws are
closed under finite sums and differences of families. The re-index
`epsReindex` sends both slots through `ε`: it converts the undotted law into the fundamental
one for the same representation, is an involution, leaves the span unchanged and leaves the
`ε` contraction exactly as it was, with no sign or scalar. For a dotted family the same
re-index works once the representation is twisted by `SL2C.conjHom`, conjugating the group
argument undoing the conjugation of the entries.

-/

/-- A family `T` indexed by two dual left-handed Weyl indices, moved as `T_{α₁ α₂}`: one factor
  of the inverse transpose `(g⁻¹)ᵀ` per index. -/
structure IsBiDualLeftWeyl (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B)
    (T : Fin 2 × Fin 2 → B) : Prop where
  repLorentz_T : ∀ (g : SL(2,ℂ)) l,
    repLorentz g (T l) = ∑ (a : Fin 2 × Fin 2),
      ((g.1⁻¹)ᵀ a.1 l.1 * (g.1⁻¹)ᵀ a.2 l.2) • T a

/-- The same for two dual right-handed indices, `T_{α̇₁ α̇₂}`: one factor of the inverse
  conjugate transpose `(g⁻¹)ᴴ` per index. -/
structure IsBiDualRightWeyl (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B)
    (T : Fin 2 × Fin 2 → B) : Prop where
  repLorentz_T : ∀ (g : SL(2,ℂ)) l,
    repLorentz g (T l) = ∑ (a : Fin 2 × Fin 2),
      ((g.1⁻¹)ᴴ a.1 l.1 * (g.1⁻¹)ᴴ a.2 l.2) • T a

open Fermion in
/-- The tensor square of the dual left-handed Weyl representation, on the products of
  basis vectors, carries the undotted dual law. -/
lemma isBiDualLeftWeyl_dualLeftHandedWeyl :
    IsBiDualLeftWeyl (DualLeftHandedWeyl ⊗[ℂ] DualLeftHandedWeyl)
      (DualLeftHandedWeyl.rep.tprod DualLeftHandedWeyl.rep)
      (fun l => DualLeftHandedWeyl.basis l.1 ⊗ₜ[ℂ] DualLeftHandedWeyl.basis l.2) where
  repLorentz_T g l := by
    rw [Representation.tprod_apply, TensorProduct.map_tmul,
      DualLeftHandedWeyl.rep_apply_basis, DualLeftHandedWeyl.rep_apply_basis,
      TensorProduct.sum_tmul]
    simp only [TensorProduct.smul_tmul', TensorProduct.tmul_sum, TensorProduct.tmul_smul,
      smul_smul, Fintype.sum_prod_type, Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
      rw [mul_comm]

open Fermion in
/-- The tensor square of the dual right-handed Weyl representation carries the dotted dual
  law. -/
lemma isBiDualRightWeyl_dualRightHandedWeyl :
    IsBiDualRightWeyl (DualRightHandedWeyl ⊗[ℂ] DualRightHandedWeyl)
      (DualRightHandedWeyl.rep.tprod DualRightHandedWeyl.rep)
      (fun l => DualRightHandedWeyl.basis l.1 ⊗ₜ[ℂ] DualRightHandedWeyl.basis l.2) where
  repLorentz_T g l := by
    rw [Representation.tprod_apply, TensorProduct.map_tmul,
      DualRightHandedWeyl.rep_apply_basis, DualRightHandedWeyl.rep_apply_basis,
      TensorProduct.sum_tmul]
    simp only [TensorProduct.smul_tmul', TensorProduct.tmul_sum, TensorProduct.tmul_smul,
      smul_smul, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
      rw [mul_comm]

/-- A finite sum of families carrying two dual left-handed Weyl indices is such a family
  again. -/
lemma IsBiDualLeftWeyl.sum {M : Type*} [AddCommGroup M] [Module ℂ M]
    {rep : Representation ℂ SL(2,ℂ) M} {ι : Type} [Fintype ι]
    {T : ι → Fin 2 × Fin 2 → M} (hT : ∀ i, IsBiDualLeftWeyl M rep (T i)) :
    IsBiDualLeftWeyl M rep (fun l => ∑ i, T i l) where
  repLorentz_T Λ l := by
    rw [map_sum, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => (hT i).repLorentz_T Λ l,
      Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.smul_sum.symm

/-- A difference of two families carrying two dual left-handed Weyl indices is such a
  family again. -/
lemma IsBiDualLeftWeyl.sub {M : Type*} [AddCommGroup M] [Module ℂ M]
    {rep : Representation ℂ SL(2,ℂ) M} {T T' : Fin 2 × Fin 2 → M}
    (hT : IsBiDualLeftWeyl M rep T) (hT' : IsBiDualLeftWeyl M rep T') :
    IsBiDualLeftWeyl M rep (fun l => T l - T' l) where
  repLorentz_T Λ l := by
    rw [map_sub, hT.repLorentz_T Λ l, hT'.repLorentz_T Λ l, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => (smul_sub _ _ _).symm

/-- A finite sum of families carrying two dual right-handed Weyl indices is such a family
  again. -/
lemma IsBiDualRightWeyl.sum {M : Type*} [AddCommGroup M] [Module ℂ M]
    {rep : Representation ℂ SL(2,ℂ) M} {ι : Type} [Fintype ι]
    {T : ι → Fin 2 × Fin 2 → M} (hT : ∀ i, IsBiDualRightWeyl M rep (T i)) :
    IsBiDualRightWeyl M rep (fun l => ∑ i, T i l) where
  repLorentz_T Λ l := by
    rw [map_sum, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => (hT i).repLorentz_T Λ l,
      Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.smul_sum.symm

/-- A difference of two families carrying two dual right-handed Weyl indices is such a
  family again. -/
lemma IsBiDualRightWeyl.sub {M : Type*} [AddCommGroup M] [Module ℂ M]
    {rep : Representation ℂ SL(2,ℂ) M} {T T' : Fin 2 × Fin 2 → M}
    (hT : IsBiDualRightWeyl M rep T) (hT' : IsBiDualRightWeyl M rep T') :
    IsBiDualRightWeyl M rep (fun l => T l - T' l) where
  repLorentz_T Λ l := by
    rw [map_sub, hT.repLorentz_T Λ l, hT'.repLorentz_T Λ l, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => (smul_sub _ _ _).symm

/-- The `ε` re-index of a family indexed by two Weyl indices: both index slots are
  transported through the symplectic form. -/
noncomputable def epsReindex {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (T : Fin 2 × Fin 2 → B) : Fin 2 × Fin 2 → B :=
  fun l => ∑ k : Fin 2 × Fin 2, (epsilon.1 l.1 k.1 * epsilon.1 l.2 k.2) • T k

section Reindex

variable {B : Type*} [AddCommGroup B] [Module ℂ B] (T : Fin 2 × Fin 2 → B)

/-- The re-index written out on the diagonal component `(0, 0)`. -/
lemma epsReindex_zero_zero : epsReindex T (0, 0) = T (1, 1) := by
  simp [epsReindex, Fintype.sum_prod_type, Fin.sum_univ_two, SL2C.epsilon_coe]

/-- The re-index written out on the mixed component `(0, 1)`. -/
lemma epsReindex_zero_one : epsReindex T (0, 1) = - T (1, 0) := by
  simp [epsReindex, Fintype.sum_prod_type, Fin.sum_univ_two, SL2C.epsilon_coe]

/-- The re-index written out on the mixed component `(1, 0)`. -/
lemma epsReindex_one_zero : epsReindex T (1, 0) = - T (0, 1) := by
  simp [epsReindex, Fintype.sum_prod_type, Fin.sum_univ_two, SL2C.epsilon_coe]

/-- The re-index written out on the diagonal component `(1, 1)`. -/
lemma epsReindex_one_one : epsReindex T (1, 1) = T (0, 0) := by
  simp [epsReindex, Fintype.sum_prod_type, Fin.sum_univ_two, SL2C.epsilon_coe]

/-- The `ε` re-index is an involution, because `ε² = -1` on each index slot. -/
lemma epsReindex_epsReindex : epsReindex (epsReindex T) = T := by
  funext l
  obtain ⟨l₁, l₂⟩ := l
  fin_cases l₁ <;> fin_cases l₂ <;>
    simp [epsReindex_zero_zero, epsReindex_zero_one, epsReindex_one_zero,
      epsReindex_one_one]

/-- The `ε` re-index leaves the `ε` contraction unchanged, with no sign or scalar, so a
  conclusion about the re-indexed family is one about the original. -/
lemma epsilonContraction_epsReindex :
    IsBiLeftWeyl.epsilonContraction (T := epsReindex T)
      = IsBiLeftWeyl.epsilonContraction (T := T) := by
  rw [IsBiLeftWeyl.epsilonContraction_eq, IsBiLeftWeyl.epsilonContraction_eq,
    epsReindex_zero_one, epsReindex_one_zero]
  abel

/-- The re-index does not change the span of the components. -/
lemma componentSpan_epsReindex : componentSpan (epsReindex T) = componentSpan T := by
  refine le_antisymm ((componentSpan_le_iff _ _).2 fun d => sum_smul_mem_componentSpan T _)
    ((componentSpan_le_iff _ _).2 fun d => ?_)
  have h : T d = epsReindex (epsReindex T) d := by rw [epsReindex_epsReindex]
  rw [h]
  exact sum_smul_mem_componentSpan (epsReindex T) _

end Reindex

/-- The two-slot form of the symplectic identity `sum_epsilon_mul_inv_transpose`: moving both
  factors of `(g⁻¹)ᵀ` across `ε` turns them into factors of `g` on the other slots. -/
lemma sum_biEpsilon_mul_inv_transpose (g : SL(2,ℂ)) (l a : Fin 2 × Fin 2) :
    ∑ k : Fin 2 × Fin 2, (epsilon.1 l.1 k.1 * epsilon.1 l.2 k.2)
        * ((g.1⁻¹)ᵀ a.1 k.1 * (g.1⁻¹)ᵀ a.2 k.2)
      = ∑ b : Fin 2 × Fin 2, (g.1 b.1 l.1 * g.1 b.2 l.2)
        * (epsilon.1 b.1 a.1 * epsilon.1 b.2 a.2) := by
  have hL : (∑ k₁, epsilon.1 l.1 k₁ * (g.1⁻¹)ᵀ a.1 k₁)
      * (∑ k₂, epsilon.1 l.2 k₂ * (g.1⁻¹)ᵀ a.2 k₂)
      = ∑ k : Fin 2 × Fin 2, (epsilon.1 l.1 k.1 * epsilon.1 l.2 k.2)
        * ((g.1⁻¹)ᵀ a.1 k.1 * (g.1⁻¹)ᵀ a.2 k.2) := by
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun k₁ _ => Finset.sum_congr rfl fun k₂ _ => by ring
  have hR : (∑ b₁, g.1 b₁ l.1 * epsilon.1 b₁ a.1)
      * (∑ b₂, g.1 b₂ l.2 * epsilon.1 b₂ a.2)
      = ∑ b : Fin 2 × Fin 2, (g.1 b.1 l.1 * g.1 b.2 l.2)
        * (epsilon.1 b.1 a.1 * epsilon.1 b.2 a.2) := by
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ => by ring
  rw [← hL, ← hR, sum_epsilon_mul_inv_transpose, sum_epsilon_mul_inv_transpose]

/-- The `ε` re-index turns the undotted dual law into the fundamental one for the same
  representation: the symplectic identity `sum_biEpsilon_mul_inv_transpose` is the only
  mathematical step. -/
lemma IsBiDualLeftWeyl.isBiLeftWeyl_epsReindex {B : Type*} [AddCommGroup B] [Module ℂ B]
    {repLorentz : Representation ℂ SL(2,ℂ) B} {T : Fin 2 × Fin 2 → B}
    (hT : IsBiDualLeftWeyl B repLorentz T) :
    IsBiLeftWeyl B repLorentz (epsReindex T) where
  repLorentz_T g l := by
    have h := (repLorentz g).map_sum_smul_of_forall_eq T T
      (fun a k => (g.1⁻¹)ᵀ a.1 k.1 * (g.1⁻¹)ᵀ a.2 k.2) (hT.repLorentz_T g)
      (fun k => epsilon.1 l.1 k.1 * epsilon.1 l.2 k.2)
    simp only [sum_biEpsilon_mul_inv_transpose] at h
    rw [Fintype.sum_sum_mul_smul (fun (a b : Fin 2 × Fin 2) =>
      epsilon.1 b.1 a.1 * epsilon.1 b.2 a.2)] at h
    exact h

/-- A family with the dotted dual law is a family with the undotted dual law for the
  representation twisted by `conjHom`. -/
lemma IsBiDualRightWeyl.isBiDualLeftWeyl_comp {B : Type*} [AddCommGroup B] [Module ℂ B]
    {repLorentz : Representation ℂ SL(2,ℂ) B} {T : Fin 2 × Fin 2 → B}
    (hT : IsBiDualRightWeyl B repLorentz T) :
    IsBiDualLeftWeyl B (repLorentz.comp SL2C.conjHom) T where
  repLorentz_T g l := by
    have h := hT.repLorentz_T (SL2C.conjHom g) l
    rwa [conjHom_inv_conjTranspose] at h

/-- The `ε` re-index turns a family with the dotted dual law into a family with the
  fundamental law for the conjugation-twisted representation. -/
lemma IsBiDualRightWeyl.isBiLeftWeyl_epsReindex {B : Type*} [AddCommGroup B]
    [Module ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B} {T : Fin 2 × Fin 2 → B}
    (hT : IsBiDualRightWeyl B repLorentz T) :
    IsBiLeftWeyl B (repLorentz.comp SL2C.conjHom) (epsReindex T) :=
  hT.isBiDualLeftWeyl_comp.isBiLeftWeyl_epsReindex

/-!

## F. The classification of the invariants of a dual-index family

The re-index leaves the `ε` contraction alone, so the contraction in the conclusions is that
of the original family, `T (0, 1) - T (1, 0)`, with no sign or scalar attached. For the dotted
law the twist by `conjHom` is surjective, so invariance under the twisted representation is
invariance under `repLorentz`.

-/

section DualClassification

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B} {T : Fin 2 × Fin 2 → B}

/-- The `ε` contraction of a family with the undotted dual law is Lorentz invariant. -/
lemma IsBiDualLeftWeyl.repLorentz_epsilonContraction
    (hT : IsBiDualLeftWeyl B repLorentz T) (g : SL(2,ℂ)) :
    repLorentz g (IsBiLeftWeyl.epsilonContraction (T := T))
      = IsBiLeftWeyl.epsilonContraction (T := T) := by
  have h := hT.isBiLeftWeyl_epsReindex.repLorentz_epsilonContraction g
  rwa [epsilonContraction_epsReindex] at h

/-- The `ε` contraction of a family with the dotted dual law is Lorentz invariant. -/
lemma IsBiDualRightWeyl.repLorentz_epsilonContraction
    (hT : IsBiDualRightWeyl B repLorentz T) (g : SL(2,ℂ)) :
    repLorentz g (IsBiLeftWeyl.epsilonContraction (T := T))
      = IsBiLeftWeyl.epsilonContraction (T := T) := by
  have h := hT.isBiLeftWeyl_epsReindex.repLorentz_epsilonContraction
  rw [epsilonContraction_epsReindex] at h
  exact (conjHom_involutive.surjective.forall (p := fun g =>
    repLorentz g (IsBiLeftWeyl.epsilonContraction (T := T))
      = IsBiLeftWeyl.epsilonContraction (T := T))).2 h g

/-- For the undotted dual law, every Lorentz invariant of the span is a multiple of the `ε`
  contraction of that family. -/
theorem IsBiDualLeftWeyl.exists_smul_epsilonContraction_of_invariant
    (hT : IsBiDualLeftWeyl B repLorentz T) {x : B} (hx : x ∈ componentSpan T)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, x = a • IsBiLeftWeyl.epsilonContraction (T := T) := by
  obtain ⟨a, ha⟩ := hT.isBiLeftWeyl_epsReindex.exists_smul_epsilonContraction_of_invariant
    (by rwa [componentSpan_epsReindex]) hinv
  exact ⟨a, by rwa [epsilonContraction_epsReindex] at ha⟩

/-- The same modulo a Lorentz-stable submodule `S`. -/
theorem IsBiDualLeftWeyl.exists_smul_epsilonContraction_of_invariant_subset
    (hT : IsBiDualLeftWeyl B repLorentz T) {x : B} (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S)
    (hx : x ∈ componentSpan T ⊔ S) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, ∃ y ∈ S, x = a • IsBiLeftWeyl.epsilonContraction (T := T) + y := by
  obtain ⟨a, y, hy, ha⟩ :=
    hT.isBiLeftWeyl_epsReindex.exists_smul_epsilonContraction_of_invariant_subset S hS
      (by rwa [componentSpan_epsReindex]) hinv
  exact ⟨a, y, hy, by rwa [epsilonContraction_epsReindex] at ha⟩

/-- For the dotted dual law, every Lorentz invariant of the span is a multiple of the `ε`
  contraction of that family. -/
theorem IsBiDualRightWeyl.exists_smul_epsilonContraction_of_invariant
    (hT : IsBiDualRightWeyl B repLorentz T) {x : B} (hx : x ∈ componentSpan T)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, x = a • IsBiLeftWeyl.epsilonContraction (T := T) :=
  hT.isBiDualLeftWeyl_comp.exists_smul_epsilonContraction_of_invariant hx
    fun g => hinv (SL2C.conjHom g)

/-- The same modulo a Lorentz-stable submodule `S`. -/
theorem IsBiDualRightWeyl.exists_smul_epsilonContraction_of_invariant_subset
    (hT : IsBiDualRightWeyl B repLorentz T) {x : B} (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S)
    (hx : x ∈ componentSpan T ⊔ S) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, ∃ y ∈ S, x = a • IsBiLeftWeyl.epsilonContraction (T := T) + y :=
  hT.isBiDualLeftWeyl_comp.exists_smul_epsilonContraction_of_invariant_subset S
    (fun g y hy => hS (SL2C.conjHom g) y hy) hx fun g => hinv (SL2C.conjHom g)

/-- For the undotted dual law, the Lorentz invariants of the component span reduce to the span
  of the `ε` contraction. -/
noncomputable def IsBiDualLeftWeyl.invariantReductionToSpan
    (hT : IsBiDualLeftWeyl B repLorentz T) :
    InvariantReductionToSpan (fun g : SL(2,ℂ) => repLorentz g) (⨆ l, ℂ ∙ T l) where
  spanningVector := IsBiLeftWeyl.epsilonContraction (T := T)
  stable := isStableUnder_iSup_span_singleton_of_sum fun g l => ⟨_, hT.repLorentz_T g l⟩
  spanningVector_fixed := hT.repLorentz_epsilonContraction
  reduce S hS _ hx hinv := hT.exists_smul_epsilonContraction_of_invariant_subset S hS hx hinv

/-- For the dotted dual law, the Lorentz invariants of the component span reduce to the span
  of the `ε` contraction. -/
noncomputable def IsBiDualRightWeyl.invariantReductionToSpan
    (hT : IsBiDualRightWeyl B repLorentz T) :
    InvariantReductionToSpan (fun g : SL(2,ℂ) => repLorentz g) (⨆ l, ℂ ∙ T l) where
  spanningVector := IsBiLeftWeyl.epsilonContraction (T := T)
  stable := isStableUnder_iSup_span_singleton_of_sum fun g l => ⟨_, hT.repLorentz_T g l⟩
  spanningVector_fixed := hT.repLorentz_epsilonContraction
  reduce S hS _ hx hinv := hT.exists_smul_epsilonContraction_of_invariant_subset S hS hx hinv

end DualClassification

end Lorentz
