/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeAlgebra.Basis
public import Physlib.Particles.StandardModel.GaugeGroup.GaugeWeightDecomposition
/-!
# The root decomposition of the gauge algebra

The gauge torus acts on the gauge algebra by conjugation with a diagonal matrix, so it
scales the matrix entry `(j, k)` of the `su(3)` and `su(2)` blocks by `d j * star (d k)`.
Off the diagonal this makes the real and imaginary parts of an entry a rotating pair —
the root directions, recorded by `rootIdx`, `rootEntry` and `rootWeight` — while the
diagonal directions and the `u(1)` generator are fixed, and are recorded by `cartanIdx`.

This is the adjoint analogue of the weights carried by the matter representations, and
is what the gauge sector's gauge weight decomposition is built from.

-/

@[expose] public section

namespace StandardModel

open Matrix MatrixGroups

/-- Conjugation inverts a power of `expI`. -/
lemma star_expI_zpow (z : ℤ) : star ((expI : ℂ) ^ z) = (expI : ℂ) ^ (-z) := by
  rw [Complex.star_def, starRingEnd_expI_zpow]

/-!

## A. The coordinates of the standard basis

-/

namespace GaugeAlgebra

/-- coords -/
noncomputable def stdCoeff (x : GaugeAlgebra) : Fin 8 ⊕ Fin 3 ⊕ Fin 1 → ℝ
  | Sum.inl k => gellMannCoeff x.toSU3Matrix k
  | Sum.inr (Sum.inl i) => pauliCoeff x.toSU2Matrix i
  | Sum.inr (Sum.inr _) => (x.toU1Value).re

lemma eq_sum_stdCoeff (x : GaugeAlgebra) : x = ∑ y, stdCoeff x y • stdBasis y := by
  refine ext_of_matrix ?_ ?_ ?_
  · rw [toSU3Matrix_sum]
    simp only [Fintype.sum_sum_type, smul_toSU3Matrix, stdBasis_inl_toSU3Matrix,
      stdBasis_inr_inl_toSU3Matrix, stdBasis_inr_inr_toSU3Matrix, smul_zero,
      Finset.sum_const_zero, add_zero]
    exact eq_sum_gellMannCoeff_smul x.1.2.1 x.1.2.2
  · rw [toSU2Matrix_sum]
    simp only [Fintype.sum_sum_type, smul_toSU2Matrix, stdBasis_inl_toSU2Matrix,
      stdBasis_inr_inl_toSU2Matrix, stdBasis_inr_inr_toSU2Matrix, smul_zero,
      Finset.sum_const_zero, zero_add, add_zero]
    exact eq_sum_pauliCoeff_smul x.2.1.2.1 x.2.1.2.2
  · have h1 : ((x.toU1Value.re : ℝ) : ℂ) = x.toU1Value :=
      Complex.conj_eq_iff_re.mp x.2.2.2
    rw [toU1Value_sum]
    simp only [Fintype.sum_sum_type, smul_toU1Value, stdBasis_inl_toU1Value,
      stdBasis_inr_inl_toU1Value, stdBasis_inr_inr_toU1Value, stdCoeff,
      Complex.real_smul, mul_zero, Finset.sum_const_zero, zero_add, mul_one,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul, h1]

/-- The coordinate functionals of `stdBasis` read off a gauge-algebra element's matrix
  entries. -/
lemma stdBasis_coord_apply (y : GaugeAlgebra) (a : Fin 8 ⊕ Fin 3 ⊕ Fin 1) :
    stdBasis.coord a y = stdCoeff y a := by
  conv_lhs => rw [eq_sum_stdCoeff y]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ a fun b => stdCoeff y b]
  simp

end GaugeAlgebra

/-!

## B. The torus acts by conjugation with a diagonal matrix

-/

/-- su3 diagonals of inverse torus gens -/
noncomputable def torusSU3Diag : Fin 4 → Fin 3 → ℂ :=
  ![![star (expI : ℂ), (expI : ℂ), 1], ![1, star (expI : ℂ), (expI : ℂ)], 1, 1]

/-- su2 -/
noncomputable def torusSU2Diag : Fin 4 → Fin 2 → ℂ :=
  ![1, 1, ![star (expI : ℂ), (expI : ℂ)], 1]

lemma toSU3_inv_gaugeTorusGen (i : Fin 4) :
    ((GaugeGroupI.toSU3 (gaugeTorusGen i)⁻¹ : specialUnitaryGroup (Fin 3) ℂ) :
      Matrix (Fin 3) (Fin 3) ℂ) = Matrix.diagonal (torusSU3Diag i) := by
  rw [map_inv, ← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star]
  fin_cases i <;>
  · ext a b
    fin_cases a <;> fin_cases b <;>
      simp [gaugeTorusGen, GaugeGroupI.toSU3, su3ExpIOne, su3ExpITwo, torusSU3Diag,
        Matrix.diagonal]

lemma toSU2_inv_gaugeTorusGen (i : Fin 4) :
    ((GaugeGroupI.toSU2 (gaugeTorusGen i)⁻¹ : specialUnitaryGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = Matrix.diagonal (torusSU2Diag i) := by
  rw [map_inv, ← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star]
  fin_cases i <;>
  · ext a b
    fin_cases a <;> fin_cases b <;>
      simp [gaugeTorusGen, GaugeGroupI.toSU2, su2ExpI, torusSU2Diag,
        Matrix.diagonal]

namespace GaugeAlgebra

lemma adjointMap_toSU3Matrix_apply_diagonal {g : GaugeGroupI} {d : Fin 3 → ℂ}
    (hg : ((GaugeGroupI.toSU3 g : specialUnitaryGroup (Fin 3) ℂ) :
      Matrix (Fin 3) (Fin 3) ℂ) = Matrix.diagonal d)
    (x : GaugeAlgebra) (j k : Fin 3) :
    (adjointMap g x).toSU3Matrix j k = d j * star (d k) * x.toSU3Matrix j k := by
  rw [adjointMap_toSU3Matrix, hg, Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.star_apply]
  ring

lemma adjointMap_toSU2Matrix_apply_diagonal {g : GaugeGroupI} {d : Fin 2 → ℂ}
    (hg : ((GaugeGroupI.toSU2 g : specialUnitaryGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = Matrix.diagonal d)
    (x : GaugeAlgebra) (j k : Fin 2) :
    (adjointMap g x).toSU2Matrix j k = d j * star (d k) * x.toSU2Matrix j k := by
  rw [adjointMap_toSU2Matrix, hg, Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.star_apply]
  ring

end GaugeAlgebra

lemma torusSU3Diag_mul_star (i : Fin 4) (j : Fin 3) :
    torusSU3Diag i j * star (torusSU3Diag i j) = 1 := by
  fin_cases i <;> fin_cases j <;>
    simp [torusSU3Diag, expI_mul_conj, conj_mul_expI]

lemma torusSU2Diag_mul_star (i : Fin 4) (j : Fin 2) :
    torusSU2Diag i j * star (torusSU2Diag i j) = 1 := by
  fin_cases i <;> fin_cases j <;>
    simp [torusSU2Diag, expI_mul_conj, conj_mul_expI]

namespace GaugeAlgebra

/-!

## C. An entrywise scaling rotates the real pair of coordinate functionals

-/

lemma dualMap_pair_of_entry {g : GaugeGroupI} {e : GaugeAlgebra → ℂ}
    {φ₁ φ₂ : Module.Dual ℝ GaugeAlgebra} {z : ℂ}
    (h1 : ∀ x, φ₁ x = (e x).re) (h2 : ∀ x, φ₂ x = -(e x).im)
    (he : ∀ x, e (adjointMap g x) = star z * e x) :
    (adjointMap g).dualMap φ₁ = z.re • φ₁ - z.im • φ₂ ∧
      (adjointMap g).dualMap φ₂ = z.im • φ₁ + z.re • φ₂ := by
  constructor <;> refine LinearMap.ext fun x => ?_ <;>
    simp only [LinearMap.dualMap_apply, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, h1, h2, he, Complex.mul_re, Complex.mul_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im] <;> ring

end GaugeAlgebra

/-!

## D. The root and Cartan directions of the adjoint

The `su(3)` and `su(2)` blocks each contribute root directions — pairs of standard
basis indices whose coordinate functionals are the real part and minus the imaginary
part of one matrix entry — together with Cartan directions on which the torus acts
trivially; the `u(1)` generator is also fixed.

-/

namespace GaugeAlgebra

/-- The four root directions of the adjoint. -/
def rootIdx : Fin 4 → (Fin 8 ⊕ Fin 3 ⊕ Fin 1) × (Fin 8 ⊕ Fin 3 ⊕ Fin 1)
  | 0 => (Sum.inl 0, Sum.inl 1)
  | 1 => (Sum.inl 3, Sum.inl 4)
  | 2 => (Sum.inl 5, Sum.inl 6)
  | 3 => (Sum.inr (Sum.inl 0), Sum.inr (Sum.inl 1))

/-- The gauge weight of each root direction. -/
def rootWeight : Fin 4 → GaugeWeight
  | 0 => (2, -1, 0, 0)
  | 1 => (1, 1, 0, 0)
  | 2 => (-1, 2, 0, 0)
  | 3 => (0, 0, 2, 0)

/-- The matrix entry scaled by the torus along each root direction. -/
def rootEntry : Fin 4 → GaugeAlgebra → ℂ
  | 0, x => x.toSU3Matrix 0 1
  | 1, x => x.toSU3Matrix 0 2
  | 2, x => x.toSU3Matrix 1 2
  | 3, x => x.toSU2Matrix 0 1

/-- The four weight-zero directions: the two `su(3)` Cartan generators, the `su(2)`
  Cartan generator and the `u(1)` generator. -/
def cartanIdx : Fin 4 → (Fin 8 ⊕ Fin 3 ⊕ Fin 1)
  | 0 => Sum.inl 2
  | 1 => Sum.inl 7
  | 2 => Sum.inr (Sum.inl 2)
  | 3 => Sum.inr (Sum.inr 0)

lemma coord_rootIdx_fst (r : Fin 4) (x : GaugeAlgebra) :
    stdBasis.coord (rootIdx r).1 x = (rootEntry r x).re := by
  fin_cases r <;> (rw [stdBasis_coord_apply]; rfl)

lemma coord_rootIdx_snd (r : Fin 4) (x : GaugeAlgebra) :
    stdBasis.coord (rootIdx r).2 x = -(rootEntry r x).im := by
  fin_cases r <;> (rw [stdBasis_coord_apply]; rfl)

lemma rootEntry_adjointMap (r : Fin 4) (i : Fin 4) (x : GaugeAlgebra) :
    rootEntry r (adjointMap (gaugeTorusGen i)⁻¹ x)
      = star ((expI : ℂ) ^ GaugeWeight.coord (rootWeight r) i) * rootEntry r x := by
  fin_cases r
  · show (adjointMap (gaugeTorusGen i)⁻¹ x).toSU3Matrix 0 1 = _
    rw [adjointMap_toSU3Matrix_apply_diagonal (toSU3_inv_gaugeTorusGen i) x 0 1]
    congr 1
    fin_cases i <;>
      simp [torusSU3Diag, rootWeight, GaugeWeight.coord,
        expI_inv_eq_star, _root_.zpow_neg, zpow_two, zpow_one]
  · show (adjointMap (gaugeTorusGen i)⁻¹ x).toSU3Matrix 0 2 = _
    rw [adjointMap_toSU3Matrix_apply_diagonal (toSU3_inv_gaugeTorusGen i) x 0 2]
    congr 1
    fin_cases i <;>
      simp [torusSU3Diag, rootWeight, GaugeWeight.coord,
        zpow_one]
  · show (adjointMap (gaugeTorusGen i)⁻¹ x).toSU3Matrix 1 2 = _
    rw [adjointMap_toSU3Matrix_apply_diagonal (toSU3_inv_gaugeTorusGen i) x 1 2]
    congr 1
    fin_cases i <;>
      simp [torusSU3Diag, rootWeight, GaugeWeight.coord,
        expI_inv_eq_star, _root_.zpow_neg, zpow_two, zpow_one]
  · show (adjointMap (gaugeTorusGen i)⁻¹ x).toSU2Matrix 0 1 = _
    rw [adjointMap_toSU2Matrix_apply_diagonal (toSU2_inv_gaugeTorusGen i) x 0 1]
    congr 1
    fin_cases i <;>
      simp [torusSU2Diag, rootWeight, GaugeWeight.coord,
        zpow_two]

lemma dualMap_coord_cartanIdx (c : Fin 4) (i : Fin 4) :
    (adjointMap (gaugeTorusGen i)⁻¹).dualMap (stdBasis.coord (cartanIdx c))
      = stdBasis.coord (cartanIdx c) := by
  refine LinearMap.ext fun x => ?_
  have h3 : ∀ j : Fin 3, (adjointMap (gaugeTorusGen i)⁻¹ x).toSU3Matrix j j
      = x.toSU3Matrix j j := fun j => by
    rw [adjointMap_toSU3Matrix_apply_diagonal (toSU3_inv_gaugeTorusGen i) x j j,
      torusSU3Diag_mul_star, one_mul]
  have h2 : ∀ j : Fin 2, (adjointMap (gaugeTorusGen i)⁻¹ x).toSU2Matrix j j
      = x.toSU2Matrix j j := fun j => by
    rw [adjointMap_toSU2Matrix_apply_diagonal (toSU2_inv_gaugeTorusGen i) x j j,
      torusSU2Diag_mul_star, one_mul]
  have h1 : (adjointMap (gaugeTorusGen i)⁻¹ x).toU1Value = x.toU1Value :=
    adjointMap_toU1Value _ _
  fin_cases c <;>
    simp only [LinearMap.dualMap_apply, cartanIdx, stdBasis_coord_apply, stdCoeff,
      gellMannCoeff, pauliCoeff, h3, h2, h1]

end GaugeAlgebra

end StandardModel
