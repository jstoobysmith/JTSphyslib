/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.AdjointMatrix
public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.Basic
/-!
# Families with two `su(2)` adjoint indices

A family `T : (Fin 2 → Fin 3) → B` obeys the `su(2)` bi-adjoint law when an isospin rotation
`U` moves it by one factor of `su2AdjointMatrix U` per index. The adjoint matrix is real and
orthogonal, so this law is its own dual and the symbol convention of `Invariants.Basic` plays
no role.

Modulo an isospin-stable submodule, every isospin invariant of the span of the family is a
multiple of the trace contraction `∑ a, T ![a, a]`.

The classification uses four rotations. Each half turn `su2Flip k` reverses two of the three
Pauli directions, so a fixed coefficient vector vanishes off the diagonal. The third of a turn
`su2Cyc` cycles the three directions, so the diagonal entries agree.

- A. The transformation law
- B. The coefficient matrix and the trace contraction
- C. Four isospin rotations on coefficients
- D. An invariant coefficient is a multiple of the Kronecker delta
- E. The reduction modulo a stable submodule
-/

@[expose] public section

namespace StandardModel

open Matrix

/-!

## A. The transformation law

`IsSU2BiAdjointMat U f T` relates one element of `SU(2)` to one linear map on `B`.
`IsSU2BiAdjoint` asks it of the isospin rotations `repGauge (1, U, 1)` alone.

-/

/-- The linear map `f` moves the components of `T` as `U ∈ SU(2)` moves a tensor with two
  adjoint indices: one factor of `su2AdjointMatrix U` per index, with the summed index in
  the row slot. -/
def IsSU2BiAdjointMat {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (U : specialUnitaryGroup (Fin 2) ℂ) (f : B →ₗ[ℂ] B)
    (T : (Fin 2 → Fin 3) → B) : Prop :=
  ∀ l : Fin 2 → Fin 3,
    f (T l) = ∑ a : Fin 2 → Fin 3,
      (∏ i : Fin 2, ((su2AdjointMatrix U (a i) (l i) : ℝ) : ℂ)) • T a

/-- A family `T` of elements of `B`, indexed by two `su(2)` adjoint indices, transforms as a
  tensor `T^{a b}` under the isospin factor of the gauge group. Nothing is asked of the
  colour and hypercharge factors. -/
structure IsSU2BiAdjoint (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B)
    (T : (Fin 2 → Fin 3) → B) : Prop where
  repGauge_T : ∀ g : specialUnitaryGroup (Fin 2) ℂ,
    IsSU2BiAdjointMat g (repGauge (1, g, 1)) T

namespace IsSU2BiAdjoint

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B} {T : (Fin 2 → Fin 3) → B}

/-!

## B. The coefficient matrix and the trace contraction

The law acts on coefficient vectors by the Kronecker square of the complex adjoint matrix,
whose conjugate transpose is the matrix of `U⁻¹`. It fixes the Kronecker delta because the
rows of the adjoint matrix are orthonormal.

-/

/-- The matrix by which the law acts on coefficient vectors: one factor of the adjoint matrix
  per index. The law says `f (T l) = ∑ a, coeffMatrix U a l • T a` by definition. -/
noncomputable def coeffMatrix (U : specialUnitaryGroup (Fin 2) ℂ) :
    Matrix (Fin 2 → Fin 3) (Fin 2 → Fin 3) ℂ :=
  Family.powMatrix (su2AdjointCoeffMatrix U) 2

/-- The coefficient matrix acting on a coefficient vector, written out. -/
lemma coeffMatrix_mulVec_apply (U : specialUnitaryGroup (Fin 2) ℂ) (c : (Fin 2 → Fin 3) → ℂ)
    (a : Fin 2 → Fin 3) :
    (coeffMatrix U *ᵥ c) a
      = ∑ l, (∏ i : Fin 2, ((su2AdjointMatrix U (a i) (l i) : ℝ) : ℂ)) * c l :=
  rfl

/-- The coefficient matrix of `U⁻¹` is the conjugate transpose of that of `U`. -/
lemma coeffMatrix_inv (U : specialUnitaryGroup (Fin 2) ℂ) :
    coeffMatrix U⁻¹ = (coeffMatrix U)ᴴ := by
  rw [coeffMatrix, coeffMatrix, Family.powMatrix_conjTranspose, su2AdjointCoeffMatrix_inv]

/-- The Kronecker delta is fixed by every coefficient matrix. -/
lemma coeffMatrix_mulVec_deltaCoeff (U : specialUnitaryGroup (Fin 2) ℂ) :
    coeffMatrix U *ᵥ Family.deltaCoeff = Family.deltaCoeff := by
  rw [coeffMatrix, Family.powMatrix_two]
  exact Family.pairMatrix_mulVec_deltaCoeff (su2AdjointCoeffMatrix_mul_transpose U)

/-- The trace contraction: the Kronecker contraction of the two isospin indices. -/
def traceContraction (T : (Fin 2 → Fin 3) → B) : B := ∑ a : Fin 3, T ![a, a]

/-- Any map moving the components by an `SU(2)` matrix fixes the trace contraction. -/
lemma map_traceContraction {U : specialUnitaryGroup (Fin 2) ℂ} {f : B →ₗ[ℂ] B}
    (hf : IsSU2BiAdjointMat U f T) : f (traceContraction T) = traceContraction T := by
  have h := f.map_sum_smul_eq_self_of_mulVec_eq T (coeffMatrix U) hf
    (coeffMatrix_mulVec_deltaCoeff U)
  rwa [Family.sum_deltaCoeff_smul] at h

/-!

## C. Four isospin rotations on coefficients

The adjoint matrices of the rotations are computed in `GaugeGroup.AdjointMatrix`. The flip
`su2Flip k` multiplies a coefficient `c ![a, b]` by the product of the signs of `a` and `b`,
and the third of a turn `su2Cyc` carries each diagonal entry to the next.

-/

/-- An isospin flip multiplies a coefficient by the product of the signs of its two
  indices. -/
lemma coeffMatrix_su2Flip_mulVec (k : Fin 3) (c : (Fin 2 → Fin 3) → ℂ) (a b : Fin 3) :
    (coeffMatrix (su2Flip k) *ᵥ c) ![a, b]
      = ((su2FlipSign k a : ℤ) : ℂ) * ((su2FlipSign k b : ℤ) : ℂ) * c ![a, b] := by
  rw [coeffMatrix_mulVec_apply, Family.sum_pi_two, Finset.sum_eq_single a,
    Finset.sum_eq_single b]
  · simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      su2AdjointMatrix_su2Flip, ite_true, Complex.ofReal_intCast]
  · intro y _ hy
    simp [-su2AdjointMatrix_apply, su2AdjointMatrix_su2Flip, Ne.symm hy]
  · simp
  · intro x _ hx
    simp [-su2AdjointMatrix_apply, su2AdjointMatrix_su2Flip, Ne.symm hx]
  · simp

/-- The third of a turn carries the second diagonal coefficient to the first. -/
lemma coeffMatrix_su2Cyc_mulVec_zero_zero (c : (Fin 2 → Fin 3) → ℂ) :
    (coeffMatrix su2Cyc *ᵥ c) ![0, 0] = c ![1, 1] := by
  rw [coeffMatrix_mulVec_apply, Family.sum_pi_two, su2AdjointMatrix_su2Cyc]
  simp [Fin.sum_univ_three, Fin.prod_univ_two]

/-- The third of a turn carries the first diagonal coefficient to the third. -/
lemma coeffMatrix_su2Cyc_mulVec_two_two (c : (Fin 2 → Fin 3) → ℂ) :
    (coeffMatrix su2Cyc *ᵥ c) ![2, 2] = c ![0, 0] := by
  rw [coeffMatrix_mulVec_apply, Family.sum_pi_two, su2AdjointMatrix_su2Cyc]
  simp [Fin.sum_univ_three, Fin.prod_univ_two]

/-!

## D. An invariant coefficient is a multiple of the Kronecker delta

The flip about the axis `a` reverses every other direction, so it changes the sign of
`c ![a, b]` for `b ≠ a`: an invariant coefficient is diagonal. The third of a turn cycles the
diagonal entries, so they agree.

-/

/-- A coefficient vector fixed by every coefficient matrix is a multiple of the Kronecker
  delta. -/
lemma exists_eq_smul_deltaCoeff_of_forall_mulVec_eq {c : (Fin 2 → Fin 3) → ℂ}
    (hc : ∀ U : specialUnitaryGroup (Fin 2) ℂ, coeffMatrix U *ᵥ c = c) :
    ∃ z : ℂ, c = z • Family.deltaCoeff := by
  have hoff : ∀ a b : Fin 3, a ≠ b → c ![a, b] = 0 := by
    intro a b hab
    have hs : su2FlipSign a a = 1 ∧ su2FlipSign a b = -1 := by
      revert a b
      decide
    have h := congrFun (hc (su2Flip a)) ![a, b]
    rw [coeffMatrix_su2Flip_mulVec, hs.1, hs.2] at h
    push_cast at h
    linear_combination (-1 / 2 : ℂ) * h
  have hdiag : ∀ a : Fin 3, c ![a, a] = c ![0, 0] := by
    have h1 := congrFun (hc su2Cyc) ![0, 0]
    have h2 := congrFun (hc su2Cyc) ![2, 2]
    rw [coeffMatrix_su2Cyc_mulVec_zero_zero] at h1
    rw [coeffMatrix_su2Cyc_mulVec_two_two] at h2
    intro a
    have ha : a = 0 ∨ a = 1 ∨ a = 2 := by
      revert a
      decide
    rcases ha with rfl | rfl | rfl
    · rfl
    · exact h1
    · exact h2.symm
  refine ⟨c ![0, 0], funext fun l => ?_⟩
  obtain ⟨a, b, rfl⟩ : ∃ a b, l = ![a, b] := ⟨l 0, l 1, by ext i; fin_cases i <;> rfl⟩
  by_cases h : a = b
  · subst h
    simp [Family.deltaCoeff, hdiag]
  · simp [Family.deltaCoeff, h, hoff a b h]

/-!

## E. The reduction modulo a stable submodule

`reducesInvariantsTo_span_singleton_of_mulVec_eq` applies section D in every quotient by a
stable submodule. In the gauge form the law constrains only the isospin factor, so the
invariance of the trace contraction under the whole gauge group is a hypothesis.

-/

/-- For any family of maps `σ U` obeying the law, a `σ`-invariant of the span joined with a
  `σ`-stable submodule `S` is a multiple of the trace contraction plus an element of `S`. -/
lemma reducesInvariantsTo_span_traceContraction
    (σ : specialUnitaryGroup (Fin 2) ℂ → B →ₗ[ℂ] B) (hT : ∀ U, IsSU2BiAdjointMat U (σ U) T) :
    ReducesInvariantsTo σ (Submodule.span ℂ (Set.range T)) (ℂ ∙ traceContraction T) := by
  have h := reducesInvariantsTo_span_singleton_of_mulVec_eq (σ := σ) T coeffMatrix hT
    (fun U => ⟨U⁻¹, coeffMatrix_inv U⟩) Family.deltaCoeff fun _ hc =>
      exists_eq_smul_deltaCoeff_of_forall_mulVec_eq hc
  rwa [Family.sum_deltaCoeff_smul] at h

/-- A gauge invariant of the span joined with a gauge-stable submodule is a multiple of the
  trace contraction plus a gauge-invariant remainder, once the trace contraction is known to
  be gauge invariant. -/
lemma exists_smul_add_of_gauge_invariant (hT : IsSU2BiAdjoint B repGauge T) (x : B)
    (S : Submodule ℂ B) (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (htc : ∀ g : GaugeGroupI, repGauge g (traceContraction T) = traceContraction T)
    (hx : x ∈ Submodule.span ℂ (Set.range T) ⊔ S) (hinv : ∀ g : GaugeGroupI, repGauge g x = x) :
    ∃ c : ℂ, ∃ y ∈ S, x = c • traceContraction T + y
      ∧ ∀ g : GaugeGroupI, repGauge g y = y := by
  obtain ⟨w, hw, y, hy, rfl, hyinv⟩ := (isFixedBy_span_singleton htc).exists_add_of_mem_sup
    ((reducesInvariantsTo_span_traceContraction _ hT.repGauge_T).comp
      (σ := fun g => repGauge g) (fun U => (1, U, 1)) S hS x hx hinv) hinv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
  exact ⟨c, y, hy, rfl, hyinv⟩

end IsSU2BiAdjoint

end StandardModel
