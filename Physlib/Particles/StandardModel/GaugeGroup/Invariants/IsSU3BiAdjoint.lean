/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeAlgebra.RootDecomposition
public import Physlib.Particles.StandardModel.GaugeGroup.SU3PermDecomposition
public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.Basic
/-!
# Gauge tensors carrying two `su(3)` adjoint indices

A product of two gluon field strengths carries two colour indices, and the combination that
enters the Yang–Mills Lagrangian is the trace `∑ a, F^a F^a`. Modulo a colour-stable
submodule, every colour invariant of the span of the components of such a product is a
multiple of the trace contraction. In representation theory the Kronecker delta is the
singlet of `8 ⊗ 8 = 1 ⊕ 8 ⊕ 8 ⊕ 10 ⊕ 10̄ ⊕ 27`; only the spanning statement is formalized
here. The isospin and hypercharge factors are unconstrained throughout.

`IsSU3BiAdjoint` records the transformation law: a colour rotation `U ∈ SU(3)` moves the
components by one factor of the real adjoint matrix of `U` per index, the summed index in the
row slot. The law acts on coefficient vectors by the Kronecker square of the adjoint matrix,
whose conjugate transpose is the matrix of `U⁻¹` because the adjoint matrix is orthogonal;
orthogonality also fixes the Kronecker delta (B).

Five rotations pin the fixed coefficient vectors down (C–E). A coefficient vector is a
bilinear form on Gell-Mann coordinates. The three colour parities and a turn in the `SU(2)` of
the first two colours permute Gell-Mann directions up to sign, and the cyclic permutation of
the colours also rotates the Cartan plane; together they force the form to be a multiple of
the delta.

- A. The adjoint matrix and the transformation law
- B. The coefficient matrix and the trace contraction
- C. Coordinate vectors of one index
- D. Five colour rotations on the Gell-Mann directions
- E. An invariant coefficient is a multiple of the Kronecker delta
- F. The reduction modulo a stable submodule
- Aside: the weight basis of the adjoint, for `MassDimEight`
-/

@[expose] public section

namespace StandardModel

open Matrix

/-!

## A. The adjoint matrix and the transformation law

`su3AdjointMatrix U` holds the Gell-Mann coordinates of the Gell-Mann matrices conjugated by
`U`. It is the `su(3)` block of `GaugeAlgebra.adjointMatrix` at the colour rotation `(U, 1, 1)`,
so it is orthogonal and transposed at `U⁻¹`. `su3AdjointCoeffMatrix U` is the same matrix with
complex entries, acting on complex coefficient vectors. A family is bi-adjoint when a colour
rotation moves its components by one factor of the adjoint matrix per index, the summed index
in the row slot: `IsSU3BiAdjointMat` for one linear map and one `U`, `IsSU3BiAdjoint` for
`repGauge (U, 1, 1)` at every `U`.

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
  matrix, which is how the rotations of section D are computed. -/
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

/-- The linear map `f` moves the components of `T` as `U ∈ SU(3)` moves a tensor with two
  adjoint indices: one factor of the adjoint matrix per index. -/
def IsSU3BiAdjointMat {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (U : specialUnitaryGroup (Fin 3) ℂ) (f : B →ₗ[ℂ] B)
    (T : (Fin 2 → Fin 8) → B) : Prop :=
  ∀ l : Fin 2 → Fin 8,
    f (T l) = ∑ a : Fin 2 → Fin 8,
      (∏ i : Fin 2, ((su3AdjointMatrix U (a i) (l i) : ℝ) : ℂ)) • T a

/-- A family `T` of elements of `B`, indexed by two `su(3)` adjoint indices, transforms as a
  tensor `T^{a b}` under the colour factor of the gauge group. -/
structure IsSU3BiAdjoint (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B)
    (T : (Fin 2 → Fin 8) → B) : Prop where
  repGauge_T : ∀ g : specialUnitaryGroup (Fin 3) ℂ,
    IsSU3BiAdjointMat g (repGauge (g, 1, 1)) T

namespace IsSU3BiAdjoint

/- `span` and `traceContraction` take the hypothesis `hT` only to hang off it by dot
notation. -/
set_option linter.unusedVariables false

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B} {T : (Fin 2 → Fin 8) → B}

/-!

## B. The coefficient matrix and the trace contraction

The law acts on coefficient vectors by the Kronecker square of the complex adjoint matrix. Its
conjugate transpose is the matrix of `U⁻¹`, and it fixes the Kronecker delta because the rows
of the adjoint matrix are orthonormal, so the trace contraction `∑ a, T ![a, a]` is fixed by
every rotation.

-/

/-- The span of the components. -/
@[nolint unusedArguments]
def span (hT : IsSU3BiAdjoint B repGauge T) : Submodule ℂ B := ⨆ d, ℂ ∙ T d

/-- The matrix by which the law acts on coefficient vectors: one factor of the adjoint matrix
  per index. The law says `f (T l) = ∑ a, coeffMatrix U a l • T a` by definition. -/
noncomputable def coeffMatrix (U : specialUnitaryGroup (Fin 3) ℂ) :
    Matrix (Fin 2 → Fin 8) (Fin 2 → Fin 8) ℂ :=
  Family.powMatrix (su3AdjointCoeffMatrix U) 2

/-- The coefficient matrix of `U⁻¹` is the conjugate transpose of that of `U`. -/
lemma coeffMatrix_inv (U : specialUnitaryGroup (Fin 3) ℂ) :
    coeffMatrix U⁻¹ = (coeffMatrix U)ᴴ := by
  rw [coeffMatrix, coeffMatrix, Family.powMatrix_conjTranspose, su3AdjointCoeffMatrix_inv]

/-- The coefficient matrix of `U⁻¹` is also the transpose of that of `U`. -/
lemma coeffMatrix_transpose (U : specialUnitaryGroup (Fin 3) ℂ) :
    (coeffMatrix U)ᵀ = coeffMatrix U⁻¹ := by
  ext a l
  simp only [transpose_apply, coeffMatrix, Family.powMatrix, of_apply,
    ← su3AdjointCoeffMatrix_transpose]

/-- The Kronecker delta is fixed by every coefficient matrix. -/
lemma coeffMatrix_mulVec_deltaCoeff (U : specialUnitaryGroup (Fin 3) ℂ) :
    coeffMatrix U *ᵥ Family.deltaCoeff = Family.deltaCoeff := by
  rw [coeffMatrix, Family.powMatrix_two]
  exact Family.pairMatrix_mulVec_deltaCoeff (su3AdjointCoeffMatrix_mul_transpose U)

/-- The trace contraction: the Kronecker contraction of the two colour indices. -/
@[nolint unusedArguments]
def traceContraction (hT : IsSU3BiAdjoint B repGauge T) : B := ∑ a : Fin 8, T ![a, a]

/-- Any map moving the components by an `SU(3)` matrix fixes the trace contraction. -/
lemma map_traceContraction (hT : IsSU3BiAdjoint B repGauge T)
    {U : specialUnitaryGroup (Fin 3) ℂ} {f : B →ₗ[ℂ] B} (hf : IsSU3BiAdjointMat U f T) :
    f hT.traceContraction = hT.traceContraction := by
  have h := f.map_sum_smul_eq_self_of_mulVec_eq T (coeffMatrix U) hf
    (coeffMatrix_mulVec_deltaCoeff U)
  rwa [Family.sum_deltaCoeff_smul] at h

/-!

## C. Coordinate vectors of one index

`unitVec a` is the coordinate vector of the Gell-Mann direction `a`. The complex adjoint
matrix carries `unitVec b` to its column `b`, so computing what a rotation does to the
Gell-Mann directions is computing its adjoint matrix, column by column.

-/

/-- The coordinate vector of a single Gell-Mann direction. -/
def unitVec (a : Fin 8) : Fin 8 → ℂ := fun x => if x = a then 1 else 0

/-- The complex adjoint matrix carries a Gell-Mann direction to a column of the adjoint
  matrix. -/
lemma su3AdjointCoeffMatrix_mulVec_unitVec (U : specialUnitaryGroup (Fin 3) ℂ) (b a : Fin 8) :
    (su3AdjointCoeffMatrix U *ᵥ unitVec b) a = ((su3AdjointMatrix U a b : ℝ) : ℂ) := by
  simp only [mulVec, dotProduct, su3AdjointCoeffMatrix, map_apply, unitVec, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The square of `√3`, as it appears in the adjoint matrices below. -/
lemma sqrt_three_mul_self : ((Real.sqrt 3 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ) = 3 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

/-!

## D. Five colour rotations on the Gell-Mann directions

Each rotation is computed the same way: conjugate the Gell-Mann matrices, read off the
adjoint matrix by `su3AdjointMatrix_eq_gellMannCoeff`, and hence its action on `unitVec`.

The three colour parities `su3Parity k`, the diagonal matrices of `SU(3)` with entries `±1`,
scale each Gell-Mann direction by a sign `paritySign`. The cyclic permutation of colours
`su3Perm` permutes the six root directions up to sign and rotates the Cartan plane through
`2π/3`. The turn `su3Turn`, the element `!![u, v; -conj v, conj u]` of the `SU(2)` of the
first two colours at `u = (1 + i) / 2` and `v = (1 - i) / 2`, is a rotation through `2π/3`
about the axis `λ₁ + λ₂ - λ₃` of that `su(2)`: it carries `λ₁ ↦ -λ₂ ↦ -λ₃ ↦ λ₁` and fixes
`λ₈`, so it links a Cartan direction to the root directions, which nothing normalising the
torus can do.

-/

/-- The sign by which the parity `k` scales each Gell-Mann direction: `-1` on the four root
  directions pairing the colour `k` with another, `1` on the rest. -/
def paritySign : Fin 3 → Fin 8 → ℤ
  | 0 => ![-1, -1, 1, -1, -1, 1, 1, 1]
  | 1 => ![-1, -1, 1, 1, 1, -1, -1, 1]
  | 2 => ![1, 1, 1, -1, -1, -1, -1, 1]

/-- Conjugation by a parity scales each Gell-Mann matrix by its sign. -/
lemma conj_gellMannMatrix_su3Parity (k : Fin 3) (b : Fin 8) :
    (su3Parity k).1 * gellMannMatrix b * star (su3Parity k).1
      = ((paritySign k b : ℤ) : ℂ) • gellMannMatrix b := by
  rw [show (su3Parity k).1 = Matrix.diagonal fun i => if i = k then (1 : ℂ) else -1 from rfl,
    Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases k <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [paritySign, gellMannMatrix_zero, gellMannMatrix_one, gellMannMatrix_two,
      gellMannMatrix_three, gellMannMatrix_four, gellMannMatrix_five, gellMannMatrix_six,
      gellMannMatrix_seven]

/-- The adjoint matrix of a parity is diagonal, with the signs on the diagonal. -/
lemma su3AdjointMatrix_su3Parity (k : Fin 3) (a b : Fin 8) :
    su3AdjointMatrix (su3Parity k) a b = if a = b then (paritySign k b : ℝ) else 0 := by
  rw [su3AdjointMatrix_eq_gellMannCoeff, conj_gellMannMatrix_su3Parity]
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  fin_cases k <;> fin_cases a <;> fin_cases b <;>
    simp [gellMannCoeff, paritySign, gellMannMatrix_zero, gellMannMatrix_one,
      gellMannMatrix_two, gellMannMatrix_three, gellMannMatrix_four, gellMannMatrix_five,
      gellMannMatrix_six, gellMannMatrix_seven] <;>
    field_simp <;> norm_num [Real.sq_sqrt]

/-- A parity scales each Gell-Mann direction by its sign. -/
lemma su3Parity_mulVec_unitVec (k : Fin 3) (b : Fin 8) :
    su3AdjointCoeffMatrix (su3Parity k) *ᵥ unitVec b
      = ((paritySign k b : ℤ) : ℂ) • unitVec b := by
  funext a
  rw [su3AdjointCoeffMatrix_mulVec_unitVec, su3AdjointMatrix_su3Parity]
  by_cases h : a = b <;> simp [unitVec, h]

/-- The image of each Gell-Mann direction under the cyclic colour rotation: the six root
  directions are permuted up to sign, the two Cartan directions rotated into each other. -/
noncomputable def permCol : Fin 8 → Fin 8 → ℂ
  | 0 => unitVec 5
  | 1 => unitVec 6
  | 2 => -(2 : ℂ)⁻¹ • unitVec 2 + (((Real.sqrt 3 : ℝ) : ℂ) / 2) • unitVec 7
  | 3 => unitVec 0
  | 4 => -unitVec 1
  | 5 => unitVec 3
  | 6 => -unitVec 4
  | 7 => -((((Real.sqrt 3 : ℝ) : ℂ) / 2) • unitVec 2) - (2 : ℂ)⁻¹ • unitVec 7

/-- The cyclic colour rotation on the Gell-Mann directions. -/
lemma su3Perm_mulVec_unitVec (b : Fin 8) :
    su3AdjointCoeffMatrix su3Perm *ᵥ unitVec b = permCol b := by
  funext a
  rw [su3AdjointCoeffMatrix_mulVec_unitVec, su3AdjointMatrix_eq_gellMannCoeff, su3Perm_coe]
  fin_cases b <;> fin_cases a <;>
    simp [gellMannCoeff, permCol, unitVec, Matrix.star_eq_conjTranspose, Matrix.mul_apply,
      Fin.sum_univ_three, gellMannMatrix_zero, gellMannMatrix_one, gellMannMatrix_two,
      gellMannMatrix_three, gellMannMatrix_four, gellMannMatrix_five, gellMannMatrix_six,
      gellMannMatrix_seven]
  all_goals first
    | ring1
    | linear_combination (-(1 : ℂ) / 6) * sqrt_three_mul_self

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
lemma su3Turn_mulVec_unitVec :
    su3AdjointCoeffMatrix su3Turn *ᵥ unitVec 0 = (-1 : ℂ) • unitVec 1
      ∧ su3AdjointCoeffMatrix su3Turn *ᵥ unitVec 1 = (1 : ℂ) • unitVec 2
      ∧ su3AdjointCoeffMatrix su3Turn *ᵥ unitVec 2 = (-1 : ℂ) • unitVec 0
      ∧ su3AdjointCoeffMatrix su3Turn *ᵥ unitVec 7 = (1 : ℂ) • unitVec 7 := by
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals funext a
  all_goals rw [su3AdjointCoeffMatrix_mulVec_unitVec, su3AdjointMatrix_eq_gellMannCoeff]
  all_goals fin_cases a
  all_goals
    norm_num [su3Turn, gellMannCoeff, unitVec, Matrix.star_eq_conjTranspose, Matrix.mul_apply,
      Fin.sum_univ_three, gellMannMatrix_zero, gellMannMatrix_one, gellMannMatrix_two,
      gellMannMatrix_seven, Complex.ext_iff, Complex.star_def, map_ofNat,
      Complex.div_ofNat_re, Complex.div_ofNat_im]
  all_goals field_simp
  all_goals norm_num [Real.sq_sqrt]

/-!

## E. An invariant coefficient is a multiple of the Kronecker delta

A coefficient `c` is a bilinear form `form c` on coordinate vectors, with `c ![a, b]` its value
on two Gell-Mann directions. If `c` is fixed by every coefficient matrix then the form is fixed
by every complex adjoint matrix (`form_mulVec`), so a rotation carrying `unitVec a` to
`s • unitVec a'` and `unitVec b` to `t • unitVec b'` gives `c ![a, b] = s * t * c ![a', b']`
(`entry_eq_of_mulVec`). Section D supplies the rotations: the parities kill every entry
joining two directions of different sign pattern, and the turn and the cyclic rotation carry
the remaining off-diagonal entries onto killed ones (`eq_zero_of_ne`); the turn and the cyclic
rotation equate the diagonal entries, the Cartan pair through the rotation of the Cartan
plane, whose off-diagonal entries are now zero (`diag_eq`).

-/

/-- The bilinear form on coordinate vectors with coefficients `c`. -/
def form (c : (Fin 2 → Fin 8) → ℂ) (v w : Fin 8 → ℂ) : ℂ := ∑ l, v (l 0) * w (l 1) * c l

/-- The form on two scaled Gell-Mann directions is a scaled entry of `c`. -/
lemma form_smul_unitVec (c : (Fin 2 → Fin 8) → ℂ) (s t : ℂ) (a b : Fin 8) :
    form c (s • unitVec a) (t • unitVec b) = s * t * c ![a, b] := by
  rw [form, Family.sum_pi_two, Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.smul_apply, unitVec, ite_true,
      smul_eq_mul, mul_one]
  · intro y _ hy
    simp [unitVec, hy]
  · simp
  · intro x _ hx
    simp [unitVec, hx]
  · simp

variable {c : (Fin 2 → Fin 8) → ℂ}
  (hc : ∀ U : specialUnitaryGroup (Fin 3) ℂ, coeffMatrix U *ᵥ c = c)
include hc

/-- The form of an invariant coefficient is fixed by every complex adjoint matrix: the
  adjoint matrix acting on both arguments is the coefficient matrix acting on their product,
  and the transpose of the coefficient matrix of `U` is that of `U⁻¹`. -/
lemma form_mulVec (U : specialUnitaryGroup (Fin 3) ℂ) (v w : Fin 8 → ℂ) :
    form c (su3AdjointCoeffMatrix U *ᵥ v) (su3AdjointCoeffMatrix U *ᵥ w) = form c v w := by
  have key : ∀ l : Fin 2 → Fin 8,
      (su3AdjointCoeffMatrix U *ᵥ v) (l 0) * (su3AdjointCoeffMatrix U *ᵥ w) (l 1)
        = (coeffMatrix U *ᵥ fun m => v (m 0) * w (m 1)) l := by
    intro l
    simp only [mulVec, dotProduct, coeffMatrix, Family.powMatrix, of_apply, Fin.prod_univ_two]
    rw [Family.sum_pi_two, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  simp only [form, key]
  change (coeffMatrix U *ᵥ fun m => v (m 0) * w (m 1)) ⬝ᵥ c
    = (fun m => v (m 0) * w (m 1)) ⬝ᵥ c
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, coeffMatrix_transpose, hc,
    dotProduct_comm]

/-- The invariance equation on two Gell-Mann directions, for a rotation carrying each to a
  multiple of a Gell-Mann direction. -/
lemma entry_eq_of_mulVec {U : specialUnitaryGroup (Fin 3) ℂ} {a a' b b' : Fin 8} (s t : ℂ)
    (ha : su3AdjointCoeffMatrix U *ᵥ unitVec a = s • unitVec a')
    (hb : su3AdjointCoeffMatrix U *ᵥ unitVec b = t • unitVec b') :
    c ![a, b] = s * t * c ![a', b'] := by
  have h := form_mulVec hc U (unitVec a) (unitVec b)
  rw [ha, hb, form_smul_unitVec, ← one_smul ℂ (unitVec a), ← one_smul ℂ (unitVec b),
    form_smul_unitVec, one_mul, one_mul] at h
  exact h.symm

/-- The invariance equation of the cyclic rotation, read off `permCol`. -/
lemma perm_entry_eq (a b a' b' : Fin 8) (s t : ℂ)
    (ha : permCol a = s • unitVec a') (hb : permCol b = t • unitVec b') :
    c ![a, b] = s * t * c ![a', b'] :=
  entry_eq_of_mulVec hc s t (by rw [su3Perm_mulVec_unitVec, ha])
    (by rw [su3Perm_mulVec_unitVec, hb])

/-- Every off-diagonal entry vanishes. -/
lemma eq_zero_of_ne {a b : Fin 8} (hab : a ≠ b) : c ![a, b] = 0 := by
  -- an entry joining two directions of different sign pattern is its own negative
  have hpar : ∀ {a b : Fin 8} (k : Fin 3), paritySign k a ≠ paritySign k b → c ![a, b] = 0 := by
    intro a b k hk
    have h := entry_eq_of_mulVec hc _ _ (su3Parity_mulVec_unitVec k a)
      (su3Parity_mulVec_unitVec k b)
    have hs : ∀ (k : Fin 3) (a b : Fin 8),
        paritySign k a ≠ paritySign k b → paritySign k a * paritySign k b = -1 := by
      decide
    rw [← Int.cast_mul, hs k a b hk] at h
    push_cast at h
    linear_combination (1 / 2 : ℂ) * h
  -- the turn carries the first root pair and the Cartan pair onto pairs a parity separates
  obtain ⟨h0, h1, h2, h7⟩ := su3Turn_mulVec_unitVec
  have h01 : c ![0, 1] = 0 := by
    rw [entry_eq_of_mulVec hc _ _ h0 h1, hpar (a := 1) (b := 2) 0 (by decide), mul_zero]
  have h10 : c ![1, 0] = 0 := by
    rw [entry_eq_of_mulVec hc _ _ h1 h0, hpar (a := 2) (b := 1) 0 (by decide), mul_zero]
  have h27 : c ![2, 7] = 0 := by
    rw [entry_eq_of_mulVec hc _ _ h2 h7, hpar (a := 0) (b := 7) 0 (by decide), mul_zero]
  have h72 : c ![7, 2] = 0 := by
    rw [entry_eq_of_mulVec hc _ _ h7 h2, hpar (a := 7) (b := 0) 0 (by decide), mul_zero]
  -- the cyclic rotation carries each root pair onto the previous one
  have h34 : c ![3, 4] = 0 := by
    rw [perm_entry_eq hc 3 4 0 1 1 (-1) (by simp [permCol]) (by simp [permCol]), h01, mul_zero]
  have h43 : c ![4, 3] = 0 := by
    rw [perm_entry_eq hc 4 3 1 0 (-1) 1 (by simp [permCol]) (by simp [permCol]), h10, mul_zero]
  have h56 : c ![5, 6] = 0 := by
    rw [perm_entry_eq hc 5 6 3 4 1 (-1) (by simp [permCol]) (by simp [permCol]), h34, mul_zero]
  have h65 : c ![6, 5] = 0 := by
    rw [perm_entry_eq hc 6 5 4 3 (-1) 1 (by simp [permCol]) (by simp [permCol]), h43, mul_zero]
  -- every other pair of distinct directions is separated by a parity
  have key : ∀ a b : Fin 8, a ≠ b → (∃ k, paritySign k a ≠ paritySign k b)
      ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 2 ∧ b = 7) ∨ (a = 7 ∧ b = 2)
      ∨ (a = 3 ∧ b = 4) ∨ (a = 4 ∧ b = 3) ∨ (a = 5 ∧ b = 6) ∨ (a = 6 ∧ b = 5) := by
    decide
  rcases key a b hab with ⟨k, hk⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hpar k hk
  all_goals assumption

/-- Every diagonal entry equals the entry at the first Cartan direction. -/
lemma diag_eq (a : Fin 8) : c ![a, a] = c ![2, 2] := by
  -- the turn cycles `λ₁, λ₂, λ₃`, and the cyclic rotation moves the root directions around
  obtain ⟨h0, h1, -, -⟩ := su3Turn_mulVec_unitVec
  have h01 : c ![0, 0] = c ![1, 1] := by rw [entry_eq_of_mulVec hc _ _ h0 h0]; ring
  have h12 : c ![1, 1] = c ![2, 2] := by rw [entry_eq_of_mulVec hc _ _ h1 h1]; ring
  have h05 : c ![0, 0] = c ![5, 5] := by
    rw [perm_entry_eq hc 0 0 5 5 1 1 (by simp [permCol]) (by simp [permCol])]; ring
  have h16 : c ![1, 1] = c ![6, 6] := by
    rw [perm_entry_eq hc 1 1 6 6 1 1 (by simp [permCol]) (by simp [permCol])]; ring
  have h53 : c ![5, 5] = c ![3, 3] := by
    rw [perm_entry_eq hc 5 5 3 3 1 1 (by simp [permCol]) (by simp [permCol])]; ring
  have h64 : c ![6, 6] = c ![4, 4] := by
    rw [perm_entry_eq hc 6 6 4 4 (-1) (-1) (by simp [permCol]) (by simp [permCol])]; ring
  -- the Cartan plane is rotated through `2π/3`, and its off-diagonal entries vanish
  have h77 : c ![7, 7] = c ![2, 2] := by
    have h := form_mulVec hc su3Perm (unitVec 2) (unitVec 2)
    rw [su3Perm_mulVec_unitVec, ← one_smul ℂ (unitVec 2), form_smul_unitVec] at h
    simp only [form, permCol, Family.sum_pi_two, Fin.sum_univ_eight, Matrix.cons_val_zero,
      Matrix.cons_val_one, Pi.add_apply, Pi.smul_apply, unitVec, smul_eq_mul] at h
    simp only [Fin.isValue, Fin.reduceEq, ite_true, ite_false, mul_one, mul_zero, add_zero,
      zero_add, eq_zero_of_ne hc (show (2 : Fin 8) ≠ 7 by decide),
      eq_zero_of_ne hc (show (7 : Fin 8) ≠ 2 by decide), one_mul] at h
    linear_combination (4 / 3 : ℂ) * h - (c ![7, 7] / 3) * sqrt_three_mul_self
  have key : ∀ a : Fin 8, a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 := by
    decide
  rcases key a with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h01, h12]
  · exact h12
  · rfl
  · rw [← h53, ← h05, h01, h12]
  · rw [← h64, ← h16, h12]
  · rw [← h05, h01, h12]
  · rw [← h16, h12]
  · exact h77

/-- A coefficient vector fixed by every coefficient matrix is a multiple of the Kronecker
  delta. -/
lemma exists_eq_smul_deltaCoeff_of_forall_mulVec_eq : ∃ z : ℂ, c = z • Family.deltaCoeff := by
  refine ⟨c ![2, 2], funext fun l => ?_⟩
  obtain ⟨a, b, rfl⟩ : ∃ a b, l = ![a, b] := ⟨l 0, l 1, by ext i; fin_cases i <;> rfl⟩
  by_cases h : a = b
  · subst h
    simp [Family.deltaCoeff, diag_eq hc]
  · simp [Family.deltaCoeff, h, eq_zero_of_ne hc h]

omit hc

/-!

## F. The reduction modulo a stable submodule

`reducesInvariantsTo_span_singleton_of_mulVec_eq` applies section E in every quotient by a
stable submodule. The gauge form, used by `MassDimEight`, lets the other two factors act as
well: once the trace contraction is known to be gauge invariant, so is the remainder.

-/

/-- For any family of maps `σ U` obeying the law, a `σ`-invariant of the span joined with a
  `σ`-stable submodule `S` is a multiple of the trace plus an element of `S`. -/
lemma reducesInvariantsTo_span_trace (σ : specialUnitaryGroup (Fin 3) ℂ → B →ₗ[ℂ] B)
    (hT : ∀ U, IsSU3BiAdjointMat U (σ U) T) :
    ReducesInvariantsTo σ (⨆ i, ℂ ∙ T i) (ℂ ∙ ∑ a : Fin 8, T ![a, a]) := by
  have h := reducesInvariantsTo_span_singleton_of_mulVec_eq (σ := σ) T coeffMatrix hT
    (fun U => ⟨U⁻¹, coeffMatrix_inv U⟩) Family.deltaCoeff fun _ hc =>
      exists_eq_smul_deltaCoeff_of_forall_mulVec_eq hc
  rwa [Family.sum_deltaCoeff_smul] at h

/-- A gauge invariant of the span joined with a gauge-stable submodule is a multiple of the
  trace contraction plus a gauge-invariant remainder, once the trace contraction is known to
  be gauge invariant. -/
lemma exists_smul_add_of_gauge_invariant (hT : IsSU3BiAdjoint B repGauge T) (x : B)
    (S : Submodule ℂ B) (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (htc : ∀ g : GaugeGroupI, repGauge g hT.traceContraction = hT.traceContraction)
    (hx : x ∈ hT.span ⊔ S) (hinv : ∀ g : GaugeGroupI, repGauge g x = x) :
    ∃ c : ℂ, ∃ y ∈ S, x = c • hT.traceContraction + y
      ∧ ∀ g : GaugeGroupI, repGauge g y = y := by
  have h := reducesInvariantsTo_span_trace _ hT.repGauge_T S (fun U => hS (U, 1, 1)) x hx
    fun U => hinv (U, 1, 1)
  obtain ⟨w, hw, y, hy, rfl, hyinv⟩ :=
    IsFixedBy.exists_add_of_mem_sup (isFixedBy_span_singleton htc) h hinv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
  exact ⟨c, y, hy, rfl, hyinv⟩

/-!

## Aside: the weight basis of the adjoint, for `MassDimEight`

Nothing here is used by the classification. The eigenvectors of the colour torus are, for
each root direction, the two combinations `x₁ ± i x₂` of the paired Gell-Mann coordinates, and
the two Cartan directions: `wtCoeff`, indexed by `WeightIdx`. `MassDimEight` matches the gluon
field strengths with the components of a bi-adjoint family through this basis, using that its
root pairs and Cartan indices are those of the whole gauge algebra.

-/

/-- The index type of the adjoint weight basis: three positive roots, three negative roots
  and two Cartan directions. -/
abbrev WeightIdx : Type := Fin 3 ⊕ Fin 3 ⊕ Fin 2

/-- The pairs of Gell-Mann indices making up the three root directions. -/
def rootPair : Fin 3 → Fin 8 × Fin 8
  | 0 => (0, 1)
  | 1 => (3, 4)
  | 2 => (5, 6)

/-- The root pairs are the `su(3)` root pairs of the whole gauge algebra. -/
lemma rootIdx_castSucc (r : Fin 3) :
    GaugeAlgebra.rootIdx r.castSucc
      = (Sum.inl (rootPair r).1, Sum.inl (rootPair r).2) := by
  fin_cases r <;> rfl

/-- The Cartan indices are the `su(3)` Cartan indices of the whole gauge algebra. -/
lemma cartanIdx_castSucc (c : Fin 2) :
    GaugeAlgebra.cartanIdx c.castSucc.castSucc = Sum.inl (GaugeAlgebra.su3CartanId c) := by
  fin_cases c <;> rfl

/-- The weight basis of the adjoint in Gell-Mann coordinates: `x₁ ± i x₂` on each root
  pair, and the Cartan directions themselves. -/
noncomputable def wtCoeff : WeightIdx → Fin 8 → ℂ
  | Sum.inl r, a => (if a = (rootPair r).1 then 1 else 0)
      + Complex.I * (if a = (rootPair r).2 then 1 else 0)
  | Sum.inr (Sum.inl r), a => (if a = (rootPair r).1 then 1 else 0)
      - Complex.I * (if a = (rootPair r).2 then 1 else 0)
  | Sum.inr (Sum.inr c), a => if a = GaugeAlgebra.su3CartanId c then 1 else 0

end IsSU3BiAdjoint

end StandardModel
