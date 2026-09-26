/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeAlgebra.RootDecomposition
public import Physlib.Particles.StandardModel.GaugeGroup.SU2PermDecomposition
public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.Basic
/-!
# Gauge tensors carrying two `su(2)` adjoint indices

A `W`-boson field strength `W^a` carries one isospin index `a`, running over the three Pauli
directions of `su(2)`. A product of two field strengths carries two, and the combination that
enters the Yang–Mills Lagrangian is the isospin trace `∑ a, W^a W^a`. Modulo an
isospin-stable submodule, every isospin invariant of the span of the components of such a
product is a multiple of the trace contraction. In representation theory the adjoint of
`SU(2)` is the vector representation of the rotation group and the dot product is the singlet
of `3 ⊗ 3 = 1 ⊕ 3 ⊕ 5`; only the spanning statement is formalized here.

`IsSU2BiAdjoint B repGauge T` records the transformation law: an isospin rotation
`U ∈ SU(2)` moves the components by one factor of the real adjoint matrix of `U` per index,
the summed index in the row slot. Nothing is asked of the colour and hypercharge factors.

The law acts on coefficient vectors by the Kronecker square of the adjoint matrix, whose
conjugate transpose is the matrix of `U⁻¹` because the adjoint matrix is orthogonal;
orthogonality also fixes the Kronecker delta. Four rotations pin the fixed coefficient
vectors down. The three half turns about the isospin axes, the elements `i σ₁`, `i σ₂`,
`i σ₃` of `SU(2)`, each fix one Pauli direction and reverse the other two, so they change the
sign of every entry `c ![a, b]` with `a ≠ b`. A third of a turn about the diagonal axis cycles
the three Pauli directions, so the diagonal entries agree.

- A. The adjoint matrix and the transformation law
- B. The coefficient matrix and the trace contraction
- C. Four isospin rotations on coefficients
- D. An invariant coefficient is a multiple of the Kronecker delta
- E. The reduction modulo a stable submodule
- Aside: the weight basis of the adjoint, for `MassDimEight`
-/

@[expose] public section

namespace StandardModel

open Matrix

/-!

## A. The adjoint matrix and the transformation law

## A.1. The adjoint matrix

An isospin rotation `U` acts on the Lie algebra `su(2)` by conjugation, `X ↦ U X U⁻¹`, and
its adjoint matrix is the matrix of that action in the Pauli basis, read off with the trace
pairing `(X, Y) ↦ ½ tr (X Y)`. The matrix is real, and orthogonal because conjugation
preserves the trace pairing; it is the `su(2)` block of `GaugeAlgebra.adjointMatrix` at the
gauge element `(1, U, 1)`, which is where those two facts are proved.
`su2AdjointCoeffMatrix U` is the same matrix with complex entries.

-/

open PauliMatrix in
/-- The adjoint matrix of an element of `SU(2)`: the trace pairing of the Pauli basis of
  `su(2)` with the Pauli basis conjugated by that element. -/
noncomputable def su2AdjointMatrix (U : specialUnitaryGroup (Fin 2) ℂ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j =>
    2⁻¹ * (Matrix.trace (pauliMatrix (Sum.inr i) *
      (U.1 * pauliMatrix (Sum.inr j) * star U.1))).re

open PauliMatrix in
/-- The entries of the adjoint matrix. -/
@[simp]
lemma su2AdjointMatrix_apply (U : specialUnitaryGroup (Fin 2) ℂ) (i j : Fin 3) :
    su2AdjointMatrix U i j
      = 2⁻¹ * (Matrix.trace (pauliMatrix (Sum.inr i) *
          (U.1 * pauliMatrix (Sum.inr j) * star U.1))).re := rfl

/-- The rows of the adjoint matrix are orthonormal. -/
lemma sum_su2AdjointMatrix_row_mul (U : specialUnitaryGroup (Fin 2) ℂ) (c d : Fin 3) :
    ∑ a : Fin 3, su2AdjointMatrix U c a * su2AdjointMatrix U d a
      = if c = d then 1 else 0 :=
  GaugeAlgebra.sum_adjointMatrix_inr_inl_row_mul (1, U, 1) c d

/-- The adjoint matrix of the inverse is the transpose. -/
lemma su2AdjointMatrix_inv (U : specialUnitaryGroup (Fin 2) ℂ) (a b : Fin 3) :
    su2AdjointMatrix U⁻¹ a b = su2AdjointMatrix U b a := by
  have h := GaugeAlgebra.adjointMatrix_inv_apply (1, U, 1) (Sum.inr (Sum.inl a))
    (Sum.inr (Sum.inl b))
  rwa [show ((1, U, 1) : GaugeGroupI)⁻¹ = (1, U⁻¹, 1) from by simp] at h

/-- The adjoint matrix with complex entries: the matrix by which the law of one adjoint index
  acts on complex coefficient vectors. -/
noncomputable def su2AdjointCoeffMatrix (U : specialUnitaryGroup (Fin 2) ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  (su2AdjointMatrix U).map (↑)

/-- The complex adjoint matrix of the inverse is the conjugate transpose, the entries being
  real. -/
lemma su2AdjointCoeffMatrix_inv (U : specialUnitaryGroup (Fin 2) ℂ) :
    su2AdjointCoeffMatrix U⁻¹ = (su2AdjointCoeffMatrix U)ᴴ := by
  ext a b
  simp only [su2AdjointCoeffMatrix, map_apply, conjTranspose_apply, su2AdjointMatrix_inv,
    Complex.star_def, Complex.conj_ofReal]

/-- The rows of the complex adjoint matrix are orthonormal. -/
lemma su2AdjointCoeffMatrix_mul_transpose (U : specialUnitaryGroup (Fin 2) ℂ) :
    su2AdjointCoeffMatrix U * (su2AdjointCoeffMatrix U)ᵀ = 1 := by
  ext c d
  simp only [mul_apply, transpose_apply, su2AdjointCoeffMatrix, map_apply,
    ← Complex.ofReal_mul, ← Complex.ofReal_sum, sum_su2AdjointMatrix_row_mul, one_apply]
  split_ifs <;> simp

/-!

## A.2. Bi-adjoint families

The transformation law carries one factor of the adjoint matrix per index, with the summed
index in the row slot. It is recorded as `IsSU2BiAdjointMat`, a relation between one element
of `SU(2)` and one linear map on `B` in which no other factor of the gauge group appears.
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

/- `traceContraction` takes the hypothesis `hT` only to hang off it by dot notation. -/
set_option linter.unusedVariables false

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B} {T : (Fin 2 → Fin 3) → B}

/-!

## B. The coefficient matrix and the trace contraction

The law acts on coefficient vectors by the Kronecker square of the complex adjoint matrix,
whose conjugate transpose is the matrix of `U⁻¹`. It fixes the Kronecker delta because the
rows of the adjoint matrix are orthonormal, so the trace contraction `∑ a, T ![a, a]` is
isospin invariant.

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
@[nolint unusedArguments]
def traceContraction (hT : IsSU2BiAdjoint B repGauge T) : B := ∑ a : Fin 3, T ![a, a]

/-- Any map moving the components by an `SU(2)` matrix fixes the trace contraction. -/
lemma map_traceContraction (hT : IsSU2BiAdjoint B repGauge T)
    {U : specialUnitaryGroup (Fin 2) ℂ} {f : B →ₗ[ℂ] B} (hf : IsSU2BiAdjointMat U f T) :
    f hT.traceContraction = hT.traceContraction := by
  have h := f.map_sum_smul_eq_self_of_mulVec_eq T (coeffMatrix U) hf
    (coeffMatrix_mulVec_deltaCoeff U)
  rwa [Family.sum_deltaCoeff_smul] at h

/-!

## C. Four isospin rotations on coefficients

The adjoint action of `SU(2)` is the rotation group acting on three-dimensional space, and
four rotations suffice for the classification. C.1 has the three half turns about the isospin
axes, and C.2 a third of a turn about the diagonal axis `σ₁ + σ₂ + σ₃`, which cycles the
three Pauli directions.

## C.1. The isospin flips

The flip `su2Flip k = i σ_k` conjugates `σ_k` to itself and the other two Pauli matrices to
their negatives: it is the half turn about the `k`-th isospin axis, its adjoint matrix is
diagonal with entries `±1`, and it multiplies a coefficient `c ![a, b]` by the product of
the signs of `a` and `b`.

-/

/-- The sign by which the `k`-th isospin flip scales each Pauli direction: `1` on its own
  axis and `-1` on the other two. -/
def su2FlipSign : Fin 3 → Fin 3 → ℤ
  | 0 => ![1, -1, -1]
  | 1 => ![-1, 1, -1]
  | 2 => ![-1, -1, 1]

open PauliMatrix in
/-- The adjoint matrix of an isospin flip is diagonal, with the sign of each Pauli direction
  on the diagonal. -/
lemma su2AdjointMatrix_su2Flip (k : Fin 3) (a b : Fin 3) :
    su2AdjointMatrix (su2Flip k) a b = if a = b then (su2FlipSign k b : ℝ) else 0 := by
  rw [su2AdjointMatrix_apply, su2Flip_coe, star_su2FlipMatrix]
  fin_cases k <;> fin_cases a <;> fin_cases b <;>
    simp only [su2FlipMatrix, su2FlipStarMatrix, su2FlipSign, pauliMatrix,
      Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.of_apply] <;>
    norm_num [Complex.ext_iff]

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

/-!

## C.2. A third of a turn about the diagonal axis

The element `su2Cyc = (1 + i(σ₁ + σ₂ + σ₃))/2` of `SU(2)` is a rotation through a third of a
turn about the axis `σ₁ + σ₂ + σ₃`, and its adjoint matrix is the cyclic permutation of the
three Pauli directions. On coefficients it carries each diagonal entry to the next.

-/

open PauliMatrix in
/-- The adjoint matrix of the third of a turn: the cyclic permutation of the three Pauli
  directions. -/
lemma su2AdjointMatrix_su2Cyc :
    su2AdjointMatrix su2Cyc = !![0, 1, 0; 0, 0, 1; 1, 0, 0] := by
  ext a b
  rw [su2AdjointMatrix_apply, star_su2Cyc_coe, su2Cyc_coe]
  fin_cases a <;> fin_cases b <;>
    simp only [pauliMatrix, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.of_apply] <;>
    norm_num [Complex.ext_iff]

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
stable submodule. The gauge form, used by `MassDimEight`, lets the other two factors act as
well: once the trace contraction is known to be gauge invariant, so is the remainder.

-/

/-- For any family of maps `σ U` obeying the law, a `σ`-invariant of the span joined with a
  `σ`-stable submodule `S` is a multiple of the trace plus an element of `S`. -/
lemma reducesInvariantsTo_span_trace (σ : specialUnitaryGroup (Fin 2) ℂ → B →ₗ[ℂ] B)
    (hT : ∀ U, IsSU2BiAdjointMat U (σ U) T) :
    ReducesInvariantsTo σ (Submodule.span ℂ (Set.range T)) (ℂ ∙ ∑ a : Fin 3, T ![a, a]) := by
  have h := reducesInvariantsTo_span_singleton_of_mulVec_eq (σ := σ) T coeffMatrix hT
    (fun U => ⟨U⁻¹, coeffMatrix_inv U⟩) Family.deltaCoeff fun _ hc =>
      exists_eq_smul_deltaCoeff_of_forall_mulVec_eq hc
  rwa [Family.sum_deltaCoeff_smul] at h

/-- A gauge invariant of the span joined with a gauge-stable submodule is a multiple of the
  trace contraction plus a gauge-invariant remainder, once the trace contraction is known to
  be gauge invariant. -/
lemma exists_smul_add_of_gauge_invariant (hT : IsSU2BiAdjoint B repGauge T) (x : B)
    (S : Submodule ℂ B) (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (htc : ∀ g : GaugeGroupI, repGauge g hT.traceContraction = hT.traceContraction)
    (hx : x ∈ Submodule.span ℂ (Set.range T) ⊔ S) (hinv : ∀ g : GaugeGroupI, repGauge g x = x) :
    ∃ c : ℂ, ∃ y ∈ S, x = c • hT.traceContraction + y
      ∧ ∀ g : GaugeGroupI, repGauge g y = y := by
  have h := reducesInvariantsTo_span_trace _ hT.repGauge_T S (fun U => hS (1, U, 1)) x hx
    fun U => hinv (1, U, 1)
  obtain ⟨w, hw, y, hy, rfl, hyinv⟩ :=
    IsFixedBy.exists_add_of_mem_sup (isFixedBy_span_singleton htc) h hinv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
  exact ⟨c, y, hy, rfl, hyinv⟩

/-!

## Aside: the weight basis of the adjoint, for `MassDimEight`

Nothing here is used by the classification. The Pauli basis of `su(2)` can be traded for the
weight basis: the two root directions `σ₁ ± i σ₂`, on which the Cartan generator `σ₃` acts by
`±2`, and `σ₃` itself. `wtCoeff` gives the Pauli coordinates of the weight basis, indexed by
`WeightIdx`; `MassDimEight` matches the `W`-boson field strengths with the components of a
bi-adjoint family through it, using that its root pair and Cartan index are those of the
whole gauge algebra.

-/

/-- The index type of the `su(2)` adjoint weight basis: the positive root, the negative
  root and the Cartan direction. -/
abbrev WeightIdx : Type := Fin 1 ⊕ Fin 1 ⊕ Fin 1

/-- The pair of Pauli indices making up the root direction of `su(2)`. -/
def rootPair : Fin 3 × Fin 3 := (0, 1)

/-- The root direction here is the `su(2)` root direction of the full gauge algebra. -/
lemma rootIdx_three :
    GaugeAlgebra.rootIdx 3
      = (Sum.inr (Sum.inl rootPair.1), Sum.inr (Sum.inl rootPair.2)) := rfl

/-- The Cartan direction here is the `su(2)` Cartan direction of the full gauge
  algebra. -/
lemma cartanIdx_two :
    GaugeAlgebra.cartanIdx 2 = Sum.inr (Sum.inl GaugeAlgebra.su2CartanId) := rfl

/-- The Pauli coordinates of the `su(2)` adjoint weight basis: for the root the two
  combinations `x₁ ± i x₂` of the paired coordinates, and for the Cartan direction the
  coordinate itself. -/
noncomputable def wtCoeff : WeightIdx → Fin 3 → ℂ
  | Sum.inl _, a => (if a = rootPair.1 then 1 else 0)
      + Complex.I * (if a = rootPair.2 then 1 else 0)
  | Sum.inr (Sum.inl _), a => (if a = rootPair.1 then 1 else 0)
      - Complex.I * (if a = rootPair.2 then 1 else 0)
  | Sum.inr (Sum.inr _), a => if a = GaugeAlgebra.su2CartanId then 1 else 0

end IsSU2BiAdjoint

end StandardModel
