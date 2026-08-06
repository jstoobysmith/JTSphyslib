/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.QED.JetAlgebra.Invariants.BoostTransforms
/-!
# Boost transformations of the second-derivative field strengths

The paired boost actions `rep(boost t) + rep(boost t⁻¹)` on the weight-eight
monomials `∂_r ∂_s F_{ab}`, for each of the three coordinate axes.
-/

@[expose] public section

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace QED
open TensorProduct StandardModel

namespace JetAlgebra

open scoped minkowskiMatrix PauliMatrix
open Matrix MatrixGroups
set_option maxHeartbeats 4000000 in
/-- The `Z`-boost action on the derivative field strength
  `∂∂F01` with derivative indices `(0, 1)`. -/
lemma genZ_dd01_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0) +
      (((t ^ 8 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 0) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 0) +
      (((-t ^ 8 + 2 * t ^ 4 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inr 0),
    fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 0} (Sum.inr 0) (Sum.inr 2),
    fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Z`-boost action on the derivative field strength
  `∂∂F23` with derivative indices `(0, 1)`. -/
lemma genZ_dd01_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2) +
      (((t ^ 8 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 1) +
      (((-t ^ 8 + 2 * t ^ 4 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 1) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inr 0),
    fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 1),
    fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Z`-boost action on the derivative field strength
  `∂∂F02` with derivative indices `(0, 2)`. -/
lemma genZ_dd02_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1) +
      (((t ^ 8 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 1) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 1) +
      (((-t ^ 8 + 2 * t ^ 4 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inr 1),
    fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 1} (Sum.inr 1) (Sum.inr 2),
    fieldStrengthDeriv_antisymm {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Z`-boost action on the derivative field strength
  `∂∂F13` with derivative indices `(0, 2)`. -/
lemma genZ_dd02_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2) +
      (((t ^ 8 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 0) +
      (((-t ^ 8 + 2 * t ^ 4 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inr 1),
    fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 0),
    fieldStrengthDeriv_antisymm {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Z`-boost action on the derivative field strength
  `∂∂F03` with derivative indices `(0, 3)`. -/
lemma genZ_dd03_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) =
      (((t ^ 8 + 1) / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inl 0} (Sum.inl 0) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 2, Sum.inr 2} (Sum.inl 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inl 0),
    fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inl 0} (Sum.inl 0) (Sum.inr 2),
    fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2),
    fieldStrengthDeriv_antisymm {Sum.inr 2, Sum.inr 2} (Sum.inl 0) (Sum.inr 2),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Z`-boost action on the derivative field strength
  `∂∂F12` with derivative indices `(0, 3)`. -/
lemma genZ_dd03_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) =
      (((t ^ 8 + 1) / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inl 0} (Sum.inr 0) (Sum.inr 1) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 2, Sum.inr 2} (Sum.inr 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inl 0),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Z`-boost action on the derivative field strength
  `∂∂F03` with derivative indices `(1, 2)`. -/
lemma genZ_dd12_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2)) =
      fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Z`-boost action on the derivative field strength
  `∂∂F12` with derivative indices `(1, 2)`. -/
lemma genZ_dd12_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1)) =
      fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
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

set_option maxHeartbeats 4000000 in
/-- The `Z`-boost action on the derivative field strength
  `∂∂F02` with derivative indices `(1, 3)`. -/
lemma genZ_dd13_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 1) +
      (((-t ^ 8 + 2 * t ^ 4 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2) +
      (((t ^ 8 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 1) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_pair_swap (Sum.inr 0) (Sum.inl 0),
    fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2),
    fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 2} (Sum.inr 1) (Sum.inr 2),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Z`-boost action on the derivative field strength
  `∂∂F13` with derivative indices `(1, 3)`. -/
lemma genZ_dd13_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2) +
      (((-t ^ 8 + 2 * t ^ 4 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 0) (Sum.inr 2) +
      (((t ^ 8 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_pair_swap (Sum.inr 0) (Sum.inl 0),
    fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0),
    fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 0),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Z`-boost action on the derivative field strength
  `∂∂F01` with derivative indices `(2, 3)`. -/
lemma genZ_dd23_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 0) +
      (((-t ^ 8 + 2 * t ^ 4 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2) +
      (((t ^ 8 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_pair_swap (Sum.inr 1) (Sum.inl 0),
    fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2),
    fieldStrengthDeriv_antisymm {Sum.inr 1, Sum.inr 2} (Sum.inr 0) (Sum.inr 2),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Z`-boost action on the derivative field strength
  `∂∂F23` with derivative indices `(2, 3)`. -/
lemma genZ_dd23_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2) +
      (((-t ^ 8 + 2 * t ^ 4 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 1) (Sum.inr 2) +
      (((t ^ 8 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_pair_swap (Sum.inr 1) (Sum.inl 0),
    fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1),
    fieldStrengthDeriv_antisymm {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 1),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `X`-boost action on the derivative field strength
  `∂∂F01` with derivative indices `(0, 1)`. -/
lemma genX_dd01_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0)) =
      (((t ^ 8 + 1) / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inl 0} (Sum.inl 0) (Sum.inr 0) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostXel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_pair_swap (Sum.inr 0) (Sum.inl 0),
    fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inl 0} (Sum.inl 0) (Sum.inr 0),
    fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0),
    fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `X`-boost action on the derivative field strength
  `∂∂F23` with derivative indices `(0, 1)`. -/
lemma genX_dd01_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2)) =
      (((t ^ 8 + 1) / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inl 0} (Sum.inr 1) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostXel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_pair_swap (Sum.inr 0) (Sum.inl 0),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `X`-boost action on the derivative field strength
  `∂∂F02` with derivative indices `(0, 2)`. -/
lemma genX_dd02_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1) +
      (((t ^ 8 - 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
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

set_option maxHeartbeats 4000000 in
/-- The `X`-boost action on the derivative field strength
  `∂∂F13` with derivative indices `(0, 2)`. -/
lemma genX_dd02_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2) +
      (((t ^ 8 - 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
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

set_option maxHeartbeats 4000000 in
/-- The `X`-boost action on the derivative field strength
  `∂∂F03` with derivative indices `(0, 3)`. -/
lemma genX_dd03_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2) +
      (((t ^ 8 - 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
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

set_option maxHeartbeats 4000000 in
/-- The `X`-boost action on the derivative field strength
  `∂∂F12` with derivative indices `(0, 3)`. -/
lemma genX_dd03_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1) +
      (((t ^ 8 - 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
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

set_option maxHeartbeats 4000000 in
/-- The `X`-boost action on the derivative field strength
  `∂∂F03` with derivative indices `(1, 2)`. -/
lemma genX_dd12_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2) +
      (((t ^ 8 - 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
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

set_option maxHeartbeats 4000000 in
/-- The `X`-boost action on the derivative field strength
  `∂∂F12` with derivative indices `(1, 2)`. -/
lemma genX_dd12_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1) +
      (((t ^ 8 - 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
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

set_option maxHeartbeats 4000000 in
/-- The `X`-boost action on the derivative field strength
  `∂∂F02` with derivative indices `(1, 3)`. -/
lemma genX_dd13_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1) +
      (((t ^ 8 - 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
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

set_option maxHeartbeats 4000000 in
/-- The `X`-boost action on the derivative field strength
  `∂∂F13` with derivative indices `(1, 3)`. -/
lemma genX_dd13_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2) +
      (((t ^ 8 - 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
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

set_option maxHeartbeats 4000000 in
/-- The `X`-boost action on the derivative field strength
  `∂∂F01` with derivative indices `(2, 3)`. -/
lemma genX_dd23_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) =
      fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostXel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_antisymm {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `X`-boost action on the derivative field strength
  `∂∂F23` with derivative indices `(2, 3)`. -/
lemma genX_dd23_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) =
      fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
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

set_option maxHeartbeats 4000000 in
/-- The `Y`-boost action on the derivative field strength
  `∂∂F01` with derivative indices `(0, 1)`. -/
lemma genY_dd01_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0) +
      (((t ^ 8 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 0) (Sum.inr 1) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 0) +
      (((-t ^ 8 + 2 * t ^ 4 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostYel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_pair_swap (Sum.inr 1) (Sum.inr 0),
    fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 0} (Sum.inr 0) (Sum.inr 1),
    fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Y`-boost action on the derivative field strength
  `∂∂F23` with derivative indices `(0, 1)`. -/
lemma genY_dd01_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 2) +
      (((t ^ 8 - 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 1) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostYel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_pair_swap (Sum.inr 1) (Sum.inr 0),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Y`-boost action on the derivative field strength
  `∂∂F02` with derivative indices `(0, 2)`. -/
lemma genY_dd02_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) =
      (((t ^ 8 + 1) / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inl 0} (Sum.inl 0) (Sum.inr 1) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 1} (Sum.inl 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostYel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_pair_swap (Sum.inr 1) (Sum.inl 0),
    fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inl 0} (Sum.inl 0) (Sum.inr 1),
    fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1),
    fieldStrengthDeriv_antisymm {Sum.inr 1, Sum.inr 1} (Sum.inl 0) (Sum.inr 1),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Y`-boost action on the derivative field strength
  `∂∂F13` with derivative indices `(0, 2)`. -/
lemma genY_dd02_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) =
      (((t ^ 8 + 1) / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inl 0} (Sum.inr 0) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 1} (Sum.inr 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostYel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_pair_swap (Sum.inr 1) (Sum.inl 0),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Y`-boost action on the derivative field strength
  `∂∂F03` with derivative indices `(0, 3)`. -/
lemma genY_dd03_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 1) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 2) +
      (((t ^ 8 - 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
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

set_option maxHeartbeats 4000000 in
/-- The `Y`-boost action on the derivative field strength
  `∂∂F12` with derivative indices `(0, 3)`. -/
lemma genY_dd03_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1) +
      (((t ^ 8 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 0) +
      (((-t ^ 8 + 2 * t ^ 4 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostYel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 0),
    fieldStrengthDeriv_antisymm {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Y`-boost action on the derivative field strength
  `∂∂F03` with derivative indices `(1, 2)`. -/
lemma genY_dd12_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 2) +
      (((t ^ 8 - 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 1) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostYel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_pair_swap (Sum.inr 0) (Sum.inl 0),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Y`-boost action on the derivative field strength
  `∂∂F12` with derivative indices `(1, 2)`. -/
lemma genY_dd12_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1) +
      (((-t ^ 8 + 2 * t ^ 4 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 0) (Sum.inr 1) +
      (((t ^ 8 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostYel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_pair_swap (Sum.inr 0) (Sum.inl 0),
    fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0),
    fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 0),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Y`-boost action on the derivative field strength
  `∂∂F02` with derivative indices `(1, 3)`. -/
lemma genY_dd13_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) =
      fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostYel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Y`-boost action on the derivative field strength
  `∂∂F13` with derivative indices `(1, 3)`. -/
lemma genY_dd13_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) =
      fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
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

set_option maxHeartbeats 4000000 in
/-- The `Y`-boost action on the derivative field strength
  `∂∂F01` with derivative indices `(2, 3)`. -/
lemma genY_dd23_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 0) +
      (((-t ^ 8 + 2 * t ^ 4 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1) +
      (((t ^ 8 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostYel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1),
    fieldStrengthDeriv_antisymm {Sum.inr 1, Sum.inr 2} (Sum.inr 0) (Sum.inr 1),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Y`-boost action on the derivative field strength
  `∂∂F23` with derivative indices `(2, 3)`. -/
lemma genY_dd23_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2) +
      (((t ^ 8 - 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 1) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
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
end JetAlgebra

end QED
