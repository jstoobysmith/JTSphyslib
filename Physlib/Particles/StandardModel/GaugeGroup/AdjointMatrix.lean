/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Nathaneal Sajan
-/
module

public import Physlib.Particles.StandardModel.GaugeAlgebra.Basis
public import Physlib.Particles.StandardModel.GaugeGroup.SU2PermDecomposition
public import Physlib.Particles.StandardModel.GaugeGroup.SU3PermDecomposition
/-!
# The adjoint matrices of `SU(2)` and `SU(3)`

`su2AdjointMatrix U` and `su3AdjointMatrix U` are the real matrices of `X ↦ U X U⁻¹` on
`su(2)` and `su(3)` in the Pauli and Gell-Mann bases, read off with the trace pairing
`(X, Y) ↦ ½ tr (X Y)`. They are the `su(2)` and `su(3)` blocks of `GaugeAlgebra.adjointMatrix`,
which gives their orthonormal rows and their transposition at `U⁻¹`. The `…CoeffMatrix`
versions have complex entries, and act on the complex coefficient vectors of the adjoint
classifiers in `GaugeGroup.Invariants`.

Sections C and D compute these matrices at the group elements those classifiers test with.

- A. The adjoint matrix of `SU(2)`
- B. The adjoint matrix of `SU(3)`
- C. `SU(2)` test elements
- D. `SU(3)` test elements
-/

@[expose] public section

namespace StandardModel

open Matrix

/-!

## A. The adjoint matrix of `SU(2)`

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

## B. The adjoint matrix of `SU(3)`

-/

/-- The adjoint matrix of `U ∈ SU(3)`: the trace pairing of the Gell-Mann basis with the
  Gell-Mann basis conjugated by `U`. -/
noncomputable def su3AdjointMatrix (U : specialUnitaryGroup (Fin 3) ℂ) :
    Matrix (Fin 8) (Fin 8) ℝ :=
  Matrix.of fun i j =>
    2⁻¹ * (Matrix.trace (gellMannMatrix i * (U.1 * gellMannMatrix j * star U.1))).re

@[simp]
lemma su3AdjointMatrix_apply (U : specialUnitaryGroup (Fin 3) ℂ) (i j : Fin 8) :
    su3AdjointMatrix U i j
      = 2⁻¹ * (Matrix.trace (gellMannMatrix i * (U.1 * gellMannMatrix j * star U.1))).re :=
  rfl

/-- The rows of the adjoint matrix are orthonormal. -/
lemma sum_su3AdjointMatrix_row_mul (U : specialUnitaryGroup (Fin 3) ℂ) (c d : Fin 8) :
    ∑ a : Fin 8, su3AdjointMatrix U c a * su3AdjointMatrix U d a
      = if c = d then 1 else 0 :=
  GaugeAlgebra.sum_adjointMatrix_inl_row_mul (U, 1, 1) c d

/-- The adjoint matrix of the inverse is the transpose. -/
lemma su3AdjointMatrix_inv (U : specialUnitaryGroup (Fin 3) ℂ) (a b : Fin 8) :
    su3AdjointMatrix U⁻¹ a b = su3AdjointMatrix U b a := by
  have h := GaugeAlgebra.adjointMatrix_inv_apply (U, 1, 1) (Sum.inl a) (Sum.inl b)
  rwa [show ((U, 1, 1) : GaugeGroupI)⁻¹ = (U⁻¹, 1, 1) from by simp] at h

/-- An entry of the adjoint matrix is a Gell-Mann coordinate of a conjugated Gell-Mann
  matrix, which is how the adjoint matrices of section D are computed. -/
lemma su3AdjointMatrix_eq_gellMannCoeff (U : specialUnitaryGroup (Fin 3) ℂ) (a b : Fin 8) :
    su3AdjointMatrix U a b = gellMannCoeff (U.1 * gellMannMatrix b * star U.1) a := by
  have hmem := GaugeAlgebra.conj_mem U.2.1
    (gellMannMatrix_selfAdjoint b) (gellMannMatrix_trace b)
  rw [su3AdjointMatrix_apply, gellMannCoeff_eq_trace hmem.1 hmem.2]

/-- The adjoint matrix with complex entries: the matrix by which the law of one adjoint index
  acts on complex coefficient vectors. -/
noncomputable def su3AdjointCoeffMatrix (U : specialUnitaryGroup (Fin 3) ℂ) :
    Matrix (Fin 8) (Fin 8) ℂ :=
  (su3AdjointMatrix U).map (↑)

/-- The transpose of the complex adjoint matrix is the complex adjoint matrix of the
  inverse. -/
lemma su3AdjointCoeffMatrix_transpose (U : specialUnitaryGroup (Fin 3) ℂ) :
    (su3AdjointCoeffMatrix U)ᵀ = su3AdjointCoeffMatrix U⁻¹ := by
  ext a b
  simp only [transpose_apply, su3AdjointCoeffMatrix, map_apply, su3AdjointMatrix_inv]

/-- The complex adjoint matrix of the inverse is the conjugate transpose, the entries being
  real. -/
lemma su3AdjointCoeffMatrix_inv (U : specialUnitaryGroup (Fin 3) ℂ) :
    su3AdjointCoeffMatrix U⁻¹ = (su3AdjointCoeffMatrix U)ᴴ := by
  ext a b
  simp only [su3AdjointCoeffMatrix, map_apply, conjTranspose_apply, su3AdjointMatrix_inv,
    Complex.star_def, Complex.conj_ofReal]

/-- The rows of the complex adjoint matrix are orthonormal. -/
lemma su3AdjointCoeffMatrix_mul_transpose (U : specialUnitaryGroup (Fin 3) ℂ) :
    su3AdjointCoeffMatrix U * (su3AdjointCoeffMatrix U)ᵀ = 1 := by
  ext c d
  simp only [mul_apply, transpose_apply, su3AdjointCoeffMatrix, map_apply,
    ← Complex.ofReal_mul, ← Complex.ofReal_sum, sum_su3AdjointMatrix_row_mul, one_apply]
  split_ifs <;> simp

/-!

## C. `SU(2)` test elements

The flip `su2Flip k = i σ_k` is the half turn about the `k`-th isospin axis: its adjoint
matrix is diagonal, with `1` on that axis and `-1` on the other two. The element `su2Cyc` is
a third of a turn about the axis `σ₁ + σ₂ + σ₃`: its adjoint matrix permutes the three Pauli
directions cyclically.

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

/-!

## D. `SU(3)` test elements

## D.1. Coordinate vectors of one index

`gellMannUnitVec a` is the coordinate vector of the Gell-Mann direction `a`. The complex
adjoint matrix carries `gellMannUnitVec b` to its column `b`, so computing what a rotation does
to the Gell-Mann directions is computing its adjoint matrix, column by column.

-/

/-- The coordinate vector of a single Gell-Mann direction. -/
def gellMannUnitVec (a : Fin 8) : Fin 8 → ℂ := fun x => if x = a then 1 else 0

/-- The complex adjoint matrix carries a Gell-Mann direction to a column of the adjoint
  matrix. -/
lemma su3AdjointCoeffMatrix_mulVec_gellMannUnitVec (U : specialUnitaryGroup (Fin 3) ℂ)
    (b a : Fin 8) :
    (su3AdjointCoeffMatrix U *ᵥ gellMannUnitVec b) a = ((su3AdjointMatrix U a b : ℝ) : ℂ) := by
  simp only [mulVec, dotProduct, su3AdjointCoeffMatrix, map_apply, gellMannUnitVec, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-!

## D.2. Three kinds of colour rotation

Each rotation is computed the same way: conjugate the Gell-Mann matrices, read off the
adjoint matrix by `su3AdjointMatrix_eq_gellMannCoeff`, and hence its action on
`gellMannUnitVec`.

The three colour parities `su3Parity k`, the diagonal matrices of `SU(3)` with entries `±1`,
scale each Gell-Mann direction by a sign `su3ParitySign`. The cyclic permutation of colours
`su3Perm` permutes the six root directions up to sign and rotates the Cartan plane through
`2π/3`. The turn `su3Turn`, the element `!![u, v; -conj v, conj u]` of the `SU(2)` of the
first two colours at `u = (1 + i) / 2` and `v = (1 - i) / 2`, is a rotation through `2π/3`
about the axis `λ₁ + λ₂ - λ₃` of that `su(2)`: it carries `λ₁ ↦ -λ₂ ↦ -λ₃ ↦ λ₁` and fixes
`λ₈`, so it links a Cartan direction to the root directions, which nothing normalising the
torus can do.

-/

/-- The sign by which the parity `k` scales each Gell-Mann direction: `-1` on the four root
  directions pairing the colour `k` with another, `1` on the rest. -/
def su3ParitySign : Fin 3 → Fin 8 → ℤ
  | 0 => ![-1, -1, 1, -1, -1, 1, 1, 1]
  | 1 => ![-1, -1, 1, 1, 1, -1, -1, 1]
  | 2 => ![1, 1, 1, -1, -1, -1, -1, 1]

/-- Conjugation by a parity scales each Gell-Mann matrix by its sign. -/
lemma conj_gellMannMatrix_su3Parity (k : Fin 3) (b : Fin 8) :
    (su3Parity k).1 * gellMannMatrix b * star (su3Parity k).1
      = ((su3ParitySign k b : ℤ) : ℂ) • gellMannMatrix b := by
  rw [show (su3Parity k).1 = Matrix.diagonal fun i => if i = k then (1 : ℂ) else -1 from rfl,
    Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases k <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [su3ParitySign, gellMannMatrix_zero, gellMannMatrix_one, gellMannMatrix_two,
      gellMannMatrix_three, gellMannMatrix_four, gellMannMatrix_five, gellMannMatrix_six,
      gellMannMatrix_seven]

/-- The adjoint matrix of a parity is diagonal, with the signs on the diagonal. -/
lemma su3AdjointMatrix_su3Parity (k : Fin 3) (a b : Fin 8) :
    su3AdjointMatrix (su3Parity k) a b = if a = b then (su3ParitySign k b : ℝ) else 0 := by
  rw [su3AdjointMatrix_eq_gellMannCoeff, conj_gellMannMatrix_su3Parity]
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  fin_cases k <;> fin_cases a <;> fin_cases b <;>
    simp [gellMannCoeff, su3ParitySign, gellMannMatrix_zero, gellMannMatrix_one,
      gellMannMatrix_two, gellMannMatrix_three, gellMannMatrix_four, gellMannMatrix_five,
      gellMannMatrix_six, gellMannMatrix_seven] <;>
    field_simp <;> norm_num [Real.sq_sqrt]

/-- A parity scales each Gell-Mann direction by its sign. -/
lemma su3Parity_mulVec_gellMannUnitVec (k : Fin 3) (b : Fin 8) :
    su3AdjointCoeffMatrix (su3Parity k) *ᵥ gellMannUnitVec b
      = ((su3ParitySign k b : ℤ) : ℂ) • gellMannUnitVec b := by
  funext a
  rw [su3AdjointCoeffMatrix_mulVec_gellMannUnitVec, su3AdjointMatrix_su3Parity]
  by_cases h : a = b <;> simp [gellMannUnitVec, h]

/-- The image of each Gell-Mann direction under the cyclic colour rotation: the six root
  directions are permuted up to sign, the two Cartan directions rotated into each other. -/
noncomputable def su3PermCol : Fin 8 → Fin 8 → ℂ
  | 0 => gellMannUnitVec 5
  | 1 => gellMannUnitVec 6
  | 2 => -(2 : ℂ)⁻¹ • gellMannUnitVec 2 + (((Real.sqrt 3 : ℝ) : ℂ) / 2) • gellMannUnitVec 7
  | 3 => gellMannUnitVec 0
  | 4 => -gellMannUnitVec 1
  | 5 => gellMannUnitVec 3
  | 6 => -gellMannUnitVec 4
  | 7 => -((((Real.sqrt 3 : ℝ) : ℂ) / 2) • gellMannUnitVec 2) - (2 : ℂ)⁻¹ • gellMannUnitVec 7

/-- The cyclic colour rotation on the Gell-Mann directions. -/
lemma su3Perm_mulVec_gellMannUnitVec (b : Fin 8) :
    su3AdjointCoeffMatrix su3Perm *ᵥ gellMannUnitVec b = su3PermCol b := by
  funext a
  rw [su3AdjointCoeffMatrix_mulVec_gellMannUnitVec, su3AdjointMatrix_eq_gellMannCoeff,
    su3Perm_coe]
  fin_cases b <;> fin_cases a <;>
    simp [gellMannCoeff, su3PermCol, gellMannUnitVec, Matrix.star_eq_conjTranspose,
      Matrix.mul_apply, Fin.sum_univ_three, gellMannMatrix_zero, gellMannMatrix_one,
      gellMannMatrix_two, gellMannMatrix_three, gellMannMatrix_four, gellMannMatrix_five,
      gellMannMatrix_six, gellMannMatrix_seven]
  all_goals first
    | ring1
    | have hsqrt : (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) = 3 := by
        exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
      linear_combination (-(1 : ℂ) / 6) * hsqrt

/-- The turn: the rotation through `2π/3` about `λ₁ + λ₂ - λ₃` in the `SU(2)` of the first
  two colours, with the third colour fixed. -/
noncomputable def su3Turn : specialUnitaryGroup (Fin 3) ℂ :=
  ⟨!![(1 + Complex.I) / 2, (1 - Complex.I) / 2, 0;
      -(1 + Complex.I) / 2, (1 - Complex.I) / 2, 0;
      0, 0, 1], by
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff, Matrix.det_fin_three]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Fin.sum_univ_three,
          Complex.ext_iff, Complex.star_def, map_ofNat, Complex.div_ofNat_re,
          Complex.div_ofNat_im]
    · norm_num [Complex.ext_iff, Complex.div_ofNat_re, Complex.div_ofNat_im]⟩

/-- The turn on the first root pair and the Cartan directions: a signed cycle of `λ₁`, `λ₂`,
  `λ₃`, and `λ₈` fixed. -/
lemma su3Turn_mulVec_gellMannUnitVec :
    su3AdjointCoeffMatrix su3Turn *ᵥ gellMannUnitVec 0 = (-1 : ℂ) • gellMannUnitVec 1
      ∧ su3AdjointCoeffMatrix su3Turn *ᵥ gellMannUnitVec 1 = (1 : ℂ) • gellMannUnitVec 2
      ∧ su3AdjointCoeffMatrix su3Turn *ᵥ gellMannUnitVec 2 = (-1 : ℂ) • gellMannUnitVec 0
      ∧ su3AdjointCoeffMatrix su3Turn *ᵥ gellMannUnitVec 7 = (1 : ℂ) • gellMannUnitVec 7 := by
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals funext a
  all_goals rw [su3AdjointCoeffMatrix_mulVec_gellMannUnitVec, su3AdjointMatrix_eq_gellMannCoeff]
  all_goals fin_cases a
  all_goals
    norm_num [su3Turn, gellMannCoeff, gellMannUnitVec, Matrix.star_eq_conjTranspose,
      Matrix.mul_apply, Fin.sum_univ_three, gellMannMatrix_zero, gellMannMatrix_one,
      gellMannMatrix_two, gellMannMatrix_seven, Complex.ext_iff, Complex.star_def, map_ofNat,
      Complex.div_ofNat_re, Complex.div_ofNat_im]
  all_goals field_simp
  all_goals norm_num [Real.sq_sqrt]

end StandardModel
