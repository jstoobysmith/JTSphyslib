/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsGaugeSector.Basic
public import Physlib.Particles.StandardModel.GaugeAlgebra.Basis
public import Physlib.Particles.StandardModel.GaugeGroup.GaugeWeightDecomposition
/-!
# The gauge weight decomposition of the gauge sector

The field strength takes values in the *adjoint* representation, where — unlike the
fundamental representations carrying the fermions — the standard (Gell-Mann and Pauli)
basis is not a basis of torus eigenvectors.  The eigenvectors appear only after
complexification: the torus scales the matrix entry `(j, k)` of the `su(3)` and `su(2)`
blocks by `d j * star (d k)`, so the combinations `φ ± i ψ` of the real and imaginary
parts of an entry functional are eigenvectors, while the Cartan and `u(1)` directions
are fixed.

This file collects that computation: the torus elements act by conjugation with the
diagonal matrices `torusSU3Diag` and `torusSU2Diag`, `dualMap_pair_of_entry` turns an
entrywise scaling into the rotation of a real pair of coordinate functionals, and
`repGauge_pair_add` / `repGauge_pair_sub` / `repGauge_fixed` convert those into
eigenvector statements for the field-strength symbols in the algebra `B`.

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

/-!

## E. Eigenvectors of the gauge action among the field-strength symbols

-/

namespace IsGaugeSector

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {hrepGauge_mul : ∀ (g : GaugeGroupI) (b₁ b₂ : B),
    repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {hrepLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂}
  {F : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) →
    Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : IsGaugeSector B repGauge hrepGauge_mul repLorentz hrepLorentz_mul
      F massWeightPoly)

lemma real_smul_eq (r : ℝ) (b : B) : r • b = ((r : ℂ)) • b := by
  rw [← Complex.coe_algebraMap, algebraMap_smul]

include h in
lemma repGauge_pair_add (g : GaugeGroupI) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (φ₁ φ₂ : Module.Dual ℝ GaugeAlgebra) (z : ℂ)
    (h1 : (GaugeAlgebra.adjointMap g⁻¹).dualMap φ₁ = z.re • φ₁ - z.im • φ₂)
    (h2 : (GaugeAlgebra.adjointMap g⁻¹).dualMap φ₂ = z.im • φ₁ + z.re • φ₂) :
    repGauge g (F l μ ν φ₁ + Complex.I • F l μ ν φ₂)
      = z • (F l μ ν φ₁ + Complex.I • F l μ ν φ₂) := by
  rw [map_add, map_smul, h.repGauge_F, h.repGauge_F, h1, h2, map_sub, map_add,
    map_smul, map_smul, map_smul, map_smul, real_smul_eq z.re, real_smul_eq z.im,
    real_smul_eq z.im, real_smul_eq z.re]
  conv_rhs => rw [← Complex.re_add_im z]
  match_scalars <;> · ring_nf; try rw [Complex.I_sq]; try ring

include h in
lemma repGauge_pair_sub (g : GaugeGroupI) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (φ₁ φ₂ : Module.Dual ℝ GaugeAlgebra) (z : ℂ)
    (h1 : (GaugeAlgebra.adjointMap g⁻¹).dualMap φ₁ = z.re • φ₁ - z.im • φ₂)
    (h2 : (GaugeAlgebra.adjointMap g⁻¹).dualMap φ₂ = z.im • φ₁ + z.re • φ₂) :
    repGauge g (F l μ ν φ₁ - Complex.I • F l μ ν φ₂)
      = (starRingEnd ℂ z) • (F l μ ν φ₁ - Complex.I • F l μ ν φ₂) := by
  rw [map_sub, map_smul, h.repGauge_F, h.repGauge_F, h1, h2, map_sub, map_add,
    map_smul, map_smul, map_smul, map_smul, real_smul_eq z.re, real_smul_eq z.im,
    real_smul_eq z.im, real_smul_eq z.re]
  rw [show (starRingEnd ℂ) z = (z.re : ℂ) - (z.im : ℂ) * Complex.I by
    rw [Complex.ext_iff]; simp]
  match_scalars <;> · ring_nf; try rw [Complex.I_sq]; try ring

include h in
lemma repGauge_fixed (g : GaugeGroupI) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra)
    (h1 : (GaugeAlgebra.adjointMap g⁻¹).dualMap φ = φ) :
    repGauge g (F l μ ν φ) = F l μ ν φ := by
  rw [h.repGauge_F, h1]

/-!

## F. The gauge weight decomposition

-/

set_option linter.unusedVariables false in
open GaugeAlgebra in
/-- The weight vectors of the adjoint: for each root the two complex combinations of
  the paired coordinate symbols, and for each Cartan direction the symbol itself. -/
noncomputable def adjVec (h : IsGaugeSector B repGauge hrepGauge_mul repLorentz
      hrepLorentz_mul F massWeightPoly) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) : Fin 4 ⊕ Fin 4 ⊕ Fin 4 → B
  | Sum.inl r => F l μ ν (stdBasis.coord (rootIdx r).1)
      + Complex.I • F l μ ν (stdBasis.coord (rootIdx r).2)
  | Sum.inr (Sum.inl r) => F l μ ν (stdBasis.coord (rootIdx r).1)
      - Complex.I • F l μ ν (stdBasis.coord (rootIdx r).2)
  | Sum.inr (Sum.inr c) => F l μ ν (stdBasis.coord (cartanIdx c))

/-- The gauge weight of each adjoint weight vector. -/
def adjWeight : Fin 4 ⊕ Fin 4 ⊕ Fin 4 → GaugeWeight
  | Sum.inl r => GaugeAlgebra.rootWeight r
  | Sum.inr (Sum.inl r) => -(GaugeAlgebra.rootWeight r)
  | Sum.inr (Sum.inr _) => 0

open GaugeAlgebra in
/-- Each adjoint weight vector is a simultaneous eigenvector of the gauge torus. -/
lemma repGauge_adjVec {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (k : Fin 4 ⊕ Fin 4 ⊕ Fin 4) (i : Fin 4) :
    repGauge (gaugeTorusGen i) (h.adjVec l μ ν k)
      = ((expI : ℂ) ^ GaugeWeight.coord (adjWeight k) i) • h.adjVec l μ ν k := by
  match k with
  | Sum.inl r =>
    show repGauge (gaugeTorusGen i) (F l μ ν (stdBasis.coord (rootIdx r).1)
        + Complex.I • F l μ ν (stdBasis.coord (rootIdx r).2)) = _
    obtain ⟨p1, p2⟩ := dualMap_pair_of_entry (coord_rootIdx_fst r) (coord_rootIdx_snd r)
      (rootEntry_adjointMap r i)
    exact h.repGauge_pair_add _ l μ ν _ _ _ p1 p2
  | Sum.inr (Sum.inl r) =>
    show repGauge (gaugeTorusGen i) (F l μ ν (stdBasis.coord (rootIdx r).1)
        - Complex.I • F l μ ν (stdBasis.coord (rootIdx r).2)) = _
    obtain ⟨p1, p2⟩ := dualMap_pair_of_entry (coord_rootIdx_fst r) (coord_rootIdx_snd r)
      (rootEntry_adjointMap r i)
    rw [h.repGauge_pair_sub _ l μ ν _ _ _ p1 p2]
    congr 1
    rw [show GaugeWeight.coord (adjWeight (Sum.inr (Sum.inl r) :
        Fin 4 ⊕ Fin 4 ⊕ Fin 4)) i = -(GaugeWeight.coord (rootWeight r) i) from by
      simp [adjWeight, GaugeWeight.coord_neg]]
    rw [← Complex.star_def, star_expI_zpow]
  | Sum.inr (Sum.inr c) =>
    show repGauge (gaugeTorusGen i) (F l μ ν (stdBasis.coord (cartanIdx c))) = _
    rw [h.repGauge_fixed _ l μ ν _ (dualMap_coord_cartanIdx c i)]
    show _ = ((expI : ℂ) ^ GaugeWeight.coord (0 : GaugeWeight) i) • _
    simp [adjVec]

open GaugeAlgebra in
/-- The first symbol of a root pair, recovered from the two weight vectors. -/
lemma F_coord_rootIdx_fst {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (r : Fin 4) :
    F l μ ν (stdBasis.coord (rootIdx r).1)
      = (2 : ℂ)⁻¹ • (h.adjVec l μ ν (Sum.inl r)
        + h.adjVec l μ ν (Sum.inr (Sum.inl r))) := by
  show _ = (2 : ℂ)⁻¹ • ((F l μ ν (stdBasis.coord (rootIdx r).1)
      + Complex.I • F l μ ν (stdBasis.coord (rootIdx r).2))
    + (F l μ ν (stdBasis.coord (rootIdx r).1)
      - Complex.I • F l μ ν (stdBasis.coord (rootIdx r).2)))
  match_scalars <;> · field_simp; try ring

open GaugeAlgebra in
/-- The second symbol of a root pair, recovered from the two weight vectors. -/
lemma F_coord_rootIdx_snd {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (r : Fin 4) :
    F l μ ν (stdBasis.coord (rootIdx r).2)
      = (-(Complex.I / 2)) • (h.adjVec l μ ν (Sum.inl r)
        - h.adjVec l μ ν (Sum.inr (Sum.inl r))) := by
  show _ = (-(Complex.I / 2)) • ((F l μ ν (stdBasis.coord (rootIdx r).1)
      + Complex.I • F l μ ν (stdBasis.coord (rootIdx r).2))
    - (F l μ ν (stdBasis.coord (rootIdx r).1)
      - Complex.I • F l μ ν (stdBasis.coord (rootIdx r).2)))
  match_scalars <;> · ring_nf; try rw [Complex.I_sq]; try ring

open GaugeAlgebra in
/-- Every standard coordinate symbol lies in the join of the weight-vector lines. -/
lemma F_coord_mem_iSup {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (a : Fin 8 ⊕ Fin 3 ⊕ Fin 1) :
    F l μ ν (stdBasis.coord a)
      ∈ ⨆ k, Submodule.span ℂ {h.adjVec l μ ν k} := by
  have hmem : ∀ k, h.adjVec l μ ν k ∈ ⨆ k, Submodule.span ℂ {h.adjVec l μ ν k} :=
    fun k => Submodule.mem_iSup_of_mem k (Submodule.mem_span_singleton_self _)
  have hfst : ∀ r : Fin 4, F l μ ν (stdBasis.coord (rootIdx r).1)
      ∈ ⨆ k, Submodule.span ℂ {h.adjVec l μ ν k} := fun r => by
    rw [h.F_coord_rootIdx_fst l μ ν r]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ (hmem _) (hmem _))
  have hsnd : ∀ r : Fin 4, F l μ ν (stdBasis.coord (rootIdx r).2)
      ∈ ⨆ k, Submodule.span ℂ {h.adjVec l μ ν k} := fun r => by
    rw [h.F_coord_rootIdx_snd l μ ν r]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hmem _) (hmem _))
  have hcar : ∀ c : Fin 4, F l μ ν (stdBasis.coord (cartanIdx c))
      ∈ ⨆ k, Submodule.span ℂ {h.adjVec l μ ν k} := fun c => hmem (Sum.inr (Sum.inr c))
  match a with
  | Sum.inl k =>
    fin_cases k
    · exact hfst 0
    · exact hsnd 0
    · exact hcar 0
    · exact hfst 1
    · exact hsnd 1
    · exact hfst 2
    · exact hsnd 2
    · exact hcar 1
  | Sum.inr (Sum.inl j) =>
    fin_cases j
    · exact hfst 3
    · exact hsnd 3
    · exact hcar 2
  | Sum.inr (Sum.inr u) =>
    fin_cases u
    · exact hcar 3

open GaugeAlgebra in
/-- The span of the field-strength symbols is the join of the twelve weight lines. -/
lemma span_range_eq_iSup {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3) :
    Submodule.span ℂ (Set.range (F l μ ν))
      = ⨆ k, Submodule.span ℂ {h.adjVec l μ ν k} := by
  refine le_antisymm (Submodule.span_le.mpr ?_) (iSup_le fun k => ?_)
  · rintro x ⟨φ, rfl⟩
    rw [← stdBasis.sum_dual_apply_smul_coord φ, map_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [map_smul, real_smul_eq]
    exact Submodule.smul_mem _ _ (h.F_coord_mem_iSup l μ ν a)
  · refine (Submodule.span_singleton_le_iff_mem _ _).mpr ?_
    have hF : ∀ φ, F l μ ν φ ∈ Submodule.span ℂ (Set.range (F l μ ν)) :=
      fun φ => Submodule.subset_span ⟨φ, rfl⟩
    match k with
    | Sum.inl r =>
      exact Submodule.add_mem _ (hF _) (Submodule.smul_mem _ _ (hF _))
    | Sum.inr (Sum.inl r) =>
      exact Submodule.sub_mem _ (hF _) (Submodule.smul_mem _ _ (hF _))
    | Sum.inr (Sum.inr c) => exact hF _

/-- The gauge weight decomposition of the span of one field-strength symbol map. -/
@[implicit_reducible]
noncomputable def rangeGaugeWeight {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) :
    GaugeWeightDecomposition repGauge (Submodule.span ℂ (Set.range (F l μ ν))) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup hrepGauge_mul fun k =>
      GaugeWeightDecomposition.spanSingleton hrepGauge_mul (h.adjVec l μ ν k) (adjWeight k)
        (fun i => h.repGauge_adjVec l μ ν k i))
    _ (h.span_range_eq_iSup l μ ν)

/-- **The gauge weight decomposition of the gauge derivative submodules**, for any
  number of covariant derivatives. -/
@[implicit_reducible]
noncomputable instance derivSubmoduleGaugeWeight (n : ℕ) :
    GaugeWeightDecomposition repGauge (h.derivSubmodule n) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup hrepGauge_mul fun l : Fin n → Fin 1 ⊕ Fin 3 =>
      GaugeWeightDecomposition.iSup hrepGauge_mul fun μ : Fin 1 ⊕ Fin 3 =>
      GaugeWeightDecomposition.iSup hrepGauge_mul fun ν : Fin 1 ⊕ Fin 3 =>
        h.rangeGaugeWeight l μ ν)
    _ (by rw [derivSubmodule])
end IsGaugeSector


end StandardModel
