/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.Invariants.Subgroups.AxisBoosts
/-!
# Boosts acting on the field strength

For each axis `T ∈ {Z, X, Y}` the paired boost actions
`rep(boost t) + rep(boost t⁻¹)` act on the weight-eight monomials with
coefficients polynomial in `t^2` and `t⁻²`. This file records those actions on
the single field strengths `F_{ab}` (`boostZ_*`, `boostX_*`, `boostY_*`) and on the
second derivatives `∂_r ∂_s F_{ab}` (`boostZ_dd*`, `boostX_dd*`, `boostY_dd*`).
-/

@[expose] public section

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace LeptonGaugeSector
open TensorProduct StandardModel

namespace JetAlgebra

open scoped minkowskiMatrix PauliMatrix
open Matrix MatrixGroups

/-!

### The symmetrised boost average on the weight-eight sector

For each axis `T ∈ {Z, X, Y}` the paired boost actions `rep(boost) + rep(boost⁻¹)`
at `t` and `t⁻¹` act on the rotation-symmetric weight-eight basis vectors with
even coefficients in the boost parameter.  A rational combination of the
paired boosts at `t = 2, 3, 4` together with the identity (`boostAvgZ/X/Y`)
realises the rotation-averaged single-axis averages, and their mean `boostAvg`
fixes every Lorentz-invariant vector while acting on the weight-eight basis
by an explicit rational matrix (the `boostAvg_*` stage lemmas below).

-/

/-- Reordering the two derivative indices of a second-derivative field
  strength. -/
lemma fieldStrengthDeriv_pair_swap (r s a b : Fin 1 ⊕ Fin 3) :
    fieldStrengthDeriv {r, s} a b = fieldStrengthDeriv {s, r} a b := by
  have h : ({r, s} : Multiset (Fin 1 ⊕ Fin 3)) = {s, r} := Multiset.cons_swap r s 0
  rw [h]

lemma boostMatZ_00 (t : ℝ) : boostMatZ t (Sum.inl 0) (Sum.inl 0) = (t ^ 2 + t⁻¹ ^ 2) / 2 := rfl
lemma boostMatZ_01 (t : ℝ) : boostMatZ t (Sum.inl 0) (Sum.inr 0) = 0 := rfl
lemma boostMatZ_02 (t : ℝ) : boostMatZ t (Sum.inl 0) (Sum.inr 1) = 0 := rfl
lemma boostMatZ_03 (t : ℝ) : boostMatZ t (Sum.inl 0) (Sum.inr 2) = -((t ^ 2 - t⁻¹ ^ 2) / 2) := rfl
lemma boostMatZ_10 (t : ℝ) : boostMatZ t (Sum.inr 0) (Sum.inl 0) = 0 := rfl
lemma boostMatZ_11 (t : ℝ) : boostMatZ t (Sum.inr 0) (Sum.inr 0) = 1 := rfl
lemma boostMatZ_12 (t : ℝ) : boostMatZ t (Sum.inr 0) (Sum.inr 1) = 0 := rfl
lemma boostMatZ_13 (t : ℝ) : boostMatZ t (Sum.inr 0) (Sum.inr 2) = 0 := rfl
lemma boostMatZ_20 (t : ℝ) : boostMatZ t (Sum.inr 1) (Sum.inl 0) = 0 := rfl
lemma boostMatZ_21 (t : ℝ) : boostMatZ t (Sum.inr 1) (Sum.inr 0) = 0 := rfl
lemma boostMatZ_22 (t : ℝ) : boostMatZ t (Sum.inr 1) (Sum.inr 1) = 1 := rfl
lemma boostMatZ_23 (t : ℝ) : boostMatZ t (Sum.inr 1) (Sum.inr 2) = 0 := rfl
lemma boostMatZ_30 (t : ℝ) : boostMatZ t (Sum.inr 2) (Sum.inl 0) = -((t ^ 2 - t⁻¹ ^ 2) / 2) := rfl
lemma boostMatZ_31 (t : ℝ) : boostMatZ t (Sum.inr 2) (Sum.inr 0) = 0 := rfl
lemma boostMatZ_32 (t : ℝ) : boostMatZ t (Sum.inr 2) (Sum.inr 1) = 0 := rfl
lemma boostMatZ_33 (t : ℝ) : boostMatZ t (Sum.inr 2) (Sum.inr 2) = (t ^ 2 + t⁻¹ ^ 2) / 2 := rfl

lemma boostMatX_00 (t : ℝ) : boostMatX t (Sum.inl 0) (Sum.inl 0) = (t ^ 2 + t⁻¹ ^ 2) / 2 := rfl
lemma boostMatX_01 (t : ℝ) : boostMatX t (Sum.inl 0) (Sum.inr 0) = -((t ^ 2 - t⁻¹ ^ 2) / 2) := rfl
lemma boostMatX_02 (t : ℝ) : boostMatX t (Sum.inl 0) (Sum.inr 1) = 0 := rfl
lemma boostMatX_03 (t : ℝ) : boostMatX t (Sum.inl 0) (Sum.inr 2) = 0 := rfl
lemma boostMatX_10 (t : ℝ) : boostMatX t (Sum.inr 0) (Sum.inl 0) = -((t ^ 2 - t⁻¹ ^ 2) / 2) := rfl
lemma boostMatX_11 (t : ℝ) : boostMatX t (Sum.inr 0) (Sum.inr 0) = (t ^ 2 + t⁻¹ ^ 2) / 2 := rfl
lemma boostMatX_12 (t : ℝ) : boostMatX t (Sum.inr 0) (Sum.inr 1) = 0 := rfl
lemma boostMatX_13 (t : ℝ) : boostMatX t (Sum.inr 0) (Sum.inr 2) = 0 := rfl
lemma boostMatX_20 (t : ℝ) : boostMatX t (Sum.inr 1) (Sum.inl 0) = 0 := rfl
lemma boostMatX_21 (t : ℝ) : boostMatX t (Sum.inr 1) (Sum.inr 0) = 0 := rfl
lemma boostMatX_22 (t : ℝ) : boostMatX t (Sum.inr 1) (Sum.inr 1) = 1 := rfl
lemma boostMatX_23 (t : ℝ) : boostMatX t (Sum.inr 1) (Sum.inr 2) = 0 := rfl
lemma boostMatX_30 (t : ℝ) : boostMatX t (Sum.inr 2) (Sum.inl 0) = 0 := rfl
lemma boostMatX_31 (t : ℝ) : boostMatX t (Sum.inr 2) (Sum.inr 0) = 0 := rfl
lemma boostMatX_32 (t : ℝ) : boostMatX t (Sum.inr 2) (Sum.inr 1) = 0 := rfl
lemma boostMatX_33 (t : ℝ) : boostMatX t (Sum.inr 2) (Sum.inr 2) = 1 := rfl

lemma boostMatY_00 (t : ℝ) : boostMatY t (Sum.inl 0) (Sum.inl 0) = (t ^ 2 + t⁻¹ ^ 2) / 2 := rfl
lemma boostMatY_01 (t : ℝ) : boostMatY t (Sum.inl 0) (Sum.inr 0) = 0 := rfl
lemma boostMatY_02 (t : ℝ) : boostMatY t (Sum.inl 0) (Sum.inr 1) = -((t ^ 2 - t⁻¹ ^ 2) / 2) := rfl
lemma boostMatY_03 (t : ℝ) : boostMatY t (Sum.inl 0) (Sum.inr 2) = 0 := rfl
lemma boostMatY_10 (t : ℝ) : boostMatY t (Sum.inr 0) (Sum.inl 0) = 0 := rfl
lemma boostMatY_11 (t : ℝ) : boostMatY t (Sum.inr 0) (Sum.inr 0) = 1 := rfl
lemma boostMatY_12 (t : ℝ) : boostMatY t (Sum.inr 0) (Sum.inr 1) = 0 := rfl
lemma boostMatY_13 (t : ℝ) : boostMatY t (Sum.inr 0) (Sum.inr 2) = 0 := rfl
lemma boostMatY_20 (t : ℝ) : boostMatY t (Sum.inr 1) (Sum.inl 0) = -((t ^ 2 - t⁻¹ ^ 2) / 2) := rfl
lemma boostMatY_21 (t : ℝ) : boostMatY t (Sum.inr 1) (Sum.inr 0) = 0 := rfl
lemma boostMatY_22 (t : ℝ) : boostMatY t (Sum.inr 1) (Sum.inr 1) = (t ^ 2 + t⁻¹ ^ 2) / 2 := rfl
lemma boostMatY_23 (t : ℝ) : boostMatY t (Sum.inr 1) (Sum.inr 2) = 0 := rfl
lemma boostMatY_30 (t : ℝ) : boostMatY t (Sum.inr 2) (Sum.inl 0) = 0 := rfl
lemma boostMatY_31 (t : ℝ) : boostMatY t (Sum.inr 2) (Sum.inr 0) = 0 := rfl
lemma boostMatY_32 (t : ℝ) : boostMatY t (Sum.inr 2) (Sum.inr 1) = 0 := rfl
lemma boostMatY_33 (t : ℝ) : boostMatY t (Sum.inr 2) (Sum.inr 2) = 1 := rfl

set_option maxHeartbeats 2000000 in
/-- The Lorentz action on a fermion pair `ψ̄_α (Dψ_μ)_β` with one derivative on
  the unbarred factor. -/
lemma repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (Λ : SL(2,ℂ))
    (μ : Fin 1 ⊕ Fin 3) (α β : Fin 2) :
    repLorentzGroup Λ (Dbarψ [] α * Dψ [μ] β) =
      ∑ γ, ∑ ν, ∑ δ, ((Λ⁻¹).1 α γ *
        ((((Lorentz.SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) *
          star ((Λ⁻¹).1 β δ))) • (Dbarψ [] γ * Dψ [ν] δ) := by
  have hsm : ∀ (f : Fin 2 → JetAlgebra) (y : JetAlgebra),
      (∑ x, f x) * y = ∑ x, f x * y := fun f y => by
    rw [show (∑ x, f x) * y = LinearMap.mulRight ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hms : ∀ (f : (Fin 1 ⊕ Fin 3) → JetAlgebra) (y : JetAlgebra),
      y * (∑ x, f x) = ∑ x, y * f x := fun f y => by
    rw [show y * (∑ x, f x) = LinearMap.mulLeft ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hms₂ : ∀ (f : Fin 2 → JetAlgebra) (y : JetAlgebra),
      y * (∑ x, f x) = ∑ x, y * f x := fun f y => by
    rw [show y * (∑ x, f x) = LinearMap.mulLeft ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hsmul : ∀ (c d : ℂ) (x y : JetAlgebra),
      (c • x) * (d • y) = (c * d) • (x * y) := fun c d x y => by
    rw [smul_mul_smul_comm]
  rw [repLorentzGroup_apply_mul, repLorentzGroup_Dbarψ_nil, repLorentzGroup_Dψ_singleton]
  simp only [hsm, hms, hms₂, hsmul]

set_option maxHeartbeats 2000000 in
/-- The Lorentz action on a fermion pair `(D̄ψ̄_μ)_α ψ_β` with one derivative on
  the barred factor. -/
lemma repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (Λ : SL(2,ℂ))
    (μ : Fin 1 ⊕ Fin 3) (α β : Fin 2) :
    repLorentzGroup Λ (Dbarψ [μ] α * Dψ [] β) =
      ∑ ν, ∑ γ, ∑ δ, (((((Lorentz.SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) *
        (Λ⁻¹).1 α γ) * star ((Λ⁻¹).1 β δ)) • (Dbarψ [ν] γ * Dψ [] δ) := by
  have hsm : ∀ (f : (Fin 1 ⊕ Fin 3) → JetAlgebra) (y : JetAlgebra),
      (∑ x, f x) * y = ∑ x, f x * y := fun f y => by
    rw [show (∑ x, f x) * y = LinearMap.mulRight ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hsm₂ : ∀ (f : Fin 2 → JetAlgebra) (y : JetAlgebra),
      (∑ x, f x) * y = ∑ x, f x * y := fun f y => by
    rw [show (∑ x, f x) * y = LinearMap.mulRight ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hms : ∀ (f : Fin 2 → JetAlgebra) (y : JetAlgebra),
      y * (∑ x, f x) = ∑ x, y * f x := fun f y => by
    rw [show y * (∑ x, f x) = LinearMap.mulLeft ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hsmul : ∀ (c d : ℂ) (x y : JetAlgebra),
      (c • x) * (d • y) = (c * d) • (x * y) := fun c d x y => by
    rw [smul_mul_smul_comm]
  rw [repLorentzGroup_apply_mul, repLorentzGroup_Dbarψ_singleton, repLorentzGroup_Dψ_nil]
  simp only [hsm, hsm₂, hms, hsmul]

set_option maxHeartbeats 2000000 in
/-- The `Z`-boost action on the field strength `F01`. -/
lemma boostZ_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) =
      (((t ^ 4 + 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) +
      (((t ^ 4 - 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_antisymm {} (Sum.inr 0) (Sum.inr 2),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 2000000 in
/-- The `Z`-boost action on the field strength `F02`. -/
lemma boostZ_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) =
      (((t ^ 4 + 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) +
      (((t ^ 4 - 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_antisymm {} (Sum.inr 1) (Sum.inr 2),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 2000000 in
/-- The `Z`-boost action on the field strength `F03`. -/
lemma boostZ_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) =
      fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 2),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 2000000 in
/-- The `Z`-boost action on the field strength `F12`. -/
lemma boostZ_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) =
      fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    fieldStrengthDeriv_self,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 2000000 in
/-- The `Z`-boost action on the field strength `F13`. -/
lemma boostZ_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) =
      (((t ^ 4 + 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) +
      (((t ^ 4 - 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 0),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 2000000 in
/-- The `Z`-boost action on the field strength `F23`. -/
lemma boostZ_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) =
      (((t ^ 4 + 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) +
      (((t ^ 4 - 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 1),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 2000000 in
/-- The `X`-boost action on the field strength `F01`. -/
lemma boostX_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) =
      fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostXel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 0),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 2000000 in
/-- The `X`-boost action on the field strength `F02`. -/
lemma boostX_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) =
      (((t ^ 4 + 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) +
      (((-t ^ 4 + 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostXel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    fieldStrengthDeriv_self,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 2000000 in
/-- The `X`-boost action on the field strength `F03`. -/
lemma boostX_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) =
      (((t ^ 4 + 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) +
      (((-t ^ 4 + 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostXel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    fieldStrengthDeriv_self,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 2000000 in
/-- The `X`-boost action on the field strength `F12`. -/
lemma boostX_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) =
      (((t ^ 4 + 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) +
      (((-t ^ 4 + 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostXel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    fieldStrengthDeriv_self,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 2000000 in
/-- The `X`-boost action on the field strength `F13`. -/
lemma boostX_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) =
      (((t ^ 4 + 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) +
      (((-t ^ 4 + 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostXel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    fieldStrengthDeriv_self,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 2000000 in
/-- The `X`-boost action on the field strength `F23`. -/
lemma boostX_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) =
      fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostXel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    fieldStrengthDeriv_self,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 2000000 in
/-- The `Y`-boost action on the field strength `F01`. -/
lemma boostY_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) =
      (((t ^ 4 + 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) +
      (((t ^ 4 - 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostYel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_antisymm {} (Sum.inr 0) (Sum.inr 1),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 2000000 in
/-- The `Y`-boost action on the field strength `F02`. -/
lemma boostY_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) =
      fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostYel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 1),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 2000000 in
/-- The `Y`-boost action on the field strength `F03`. -/
lemma boostY_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) =
      (((t ^ 4 + 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) +
      (((-t ^ 4 + 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostYel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    fieldStrengthDeriv_self,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 2000000 in
/-- The `Y`-boost action on the field strength `F12`. -/
lemma boostY_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) =
      (((t ^ 4 + 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) +
      (((t ^ 4 - 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostYel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 0),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 2000000 in
/-- The `Y`-boost action on the field strength `F13`. -/
lemma boostY_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) =
      fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostYel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    fieldStrengthDeriv_self,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 2000000 in
/-- The `Y`-boost action on the field strength `F23`. -/
lemma boostY_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) =
      (((t ^ 4 + 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) +
      (((-t ^ 4 + 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostYel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    fieldStrengthDeriv_self,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))
  try (match_scalars <;> (push_cast; try field_simp; try ring))
end JetAlgebra

end LeptonGaugeSector
