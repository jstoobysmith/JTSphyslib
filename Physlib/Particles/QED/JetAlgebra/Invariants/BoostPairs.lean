/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.QED.JetAlgebra.Invariants.BoostSecondDerivatives
/-!
# Boost transformations of the field-strength pairs

The paired boost actions on the weight-eight products `F_{ab} F_{cd}`
(`pairZ_*`, `pairX_*`, `pairY_*`) and on the second-derivative field strengths
`∂_r ∂_s F_{ab}` (`pairZ_dd*`, `pairX_dd*`, `pairY_dd*`).
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
/-- The paired boost action (`t` and `t⁻¹` together) of the `Z`-boost on
  `F01 * F01`. -/
lemma pairZ_F01_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genZ_F01 t ht,
    genZ_F01 t⁻¹ (inv_ne_zero ht)]
  simp only [add_mul, mul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 2) (Sum.inl 0) (Sum.inr 0)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Z`-boost on
  `F01 * F23`. -/
lemma pairZ_F01_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genZ_F01 t ht,
    genZ_F01 t⁻¹ (inv_ne_zero ht),
    genZ_F23 t ht,
    genZ_F23 t⁻¹ (inv_ne_zero ht)]
  simp only [add_mul, mul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 2) (Sum.inl 0) (Sum.inr 1)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Z`-boost on
  `F02 * F02`. -/
lemma pairZ_F02_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genZ_F02 t ht,
    genZ_F02 t⁻¹ (inv_ne_zero ht)]
  simp only [add_mul, mul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 1) (Sum.inr 2) (Sum.inl 0) (Sum.inr 1)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Z`-boost on
  `F02 * F13`. -/
lemma pairZ_F02_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genZ_F02 t ht,
    genZ_F02 t⁻¹ (inv_ne_zero ht),
    genZ_F13 t ht,
    genZ_F13 t⁻¹ (inv_ne_zero ht)]
  simp only [add_mul, mul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inl 0) (Sum.inr 1) (Sum.inl 0) (Sum.inr 0),
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 1) (Sum.inr 2) (Sum.inl 0) (Sum.inr 0),
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 1) (Sum.inr 2) (Sum.inr 0) (Sum.inr 2)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Z`-boost on
  `F03 * F03`. -/
lemma pairZ_F03_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) =
      ((2 : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genZ_F03 t ht,
    genZ_F03 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Z`-boost on
  `F03 * F12`. -/
lemma pairZ_F03_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) =
      ((2 : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genZ_F03 t ht,
    genZ_F03 t⁻¹ (inv_ne_zero ht),
    genZ_F12 t ht,
    genZ_F12 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Z`-boost on
  `F12 * F12`. -/
lemma pairZ_F12_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) =
      ((2 : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genZ_F12 t ht,
    genZ_F12 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Z`-boost on
  `F13 * F13`. -/
lemma pairZ_F13_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genZ_F13 t ht,
    genZ_F13 t⁻¹ (inv_ne_zero ht)]
  simp only [add_mul, mul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 2) (Sum.inl 0) (Sum.inr 0)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Z`-boost on
  `F23 * F23`. -/
lemma pairZ_F23_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genZ_F23 t ht,
    genZ_F23 t⁻¹ (inv_ne_zero ht)]
  simp only [add_mul, mul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 1) (Sum.inr 2) (Sum.inl 0) (Sum.inr 1)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `X`-boost on
  `F01 * F01`. -/
lemma pairX_F01_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) =
      ((2 : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genX_F01 t ht,
    genX_F01 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `X`-boost on
  `F01 * F23`. -/
lemma pairX_F01_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) =
      ((2 : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genX_F01 t ht,
    genX_F01 t⁻¹ (inv_ne_zero ht),
    genX_F23 t ht,
    genX_F23 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `X`-boost on
  `F02 * F02`. -/
lemma pairX_F02_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genX_F02 t ht,
    genX_F02 t⁻¹ (inv_ne_zero ht)]
  simp only [add_mul, mul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 1) (Sum.inl 0) (Sum.inr 1)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `X`-boost on
  `F02 * F13`. -/
lemma pairX_F02_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genX_F02 t ht,
    genX_F02 t⁻¹ (inv_ne_zero ht),
    genX_F13 t ht,
    genX_F13 t⁻¹ (inv_ne_zero ht)]
  simp only [add_mul, mul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 1) (Sum.inl 0) (Sum.inr 2)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `X`-boost on
  `F03 * F03`. -/
lemma pairX_F03_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genX_F03 t ht,
    genX_F03 t⁻¹ (inv_ne_zero ht)]
  simp only [add_mul, mul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 2) (Sum.inl 0) (Sum.inr 2)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `X`-boost on
  `F03 * F12`. -/
lemma pairX_F03_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genX_F03 t ht,
    genX_F03 t⁻¹ (inv_ne_zero ht),
    genX_F12 t ht,
    genX_F12 t⁻¹ (inv_ne_zero ht)]
  simp only [add_mul, mul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inl 0) (Sum.inr 2) (Sum.inl 0) (Sum.inr 1),
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 2) (Sum.inl 0) (Sum.inr 1),
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 2) (Sum.inr 0) (Sum.inr 1)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `X`-boost on
  `F12 * F12`. -/
lemma pairX_F12_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genX_F12 t ht,
    genX_F12 t⁻¹ (inv_ne_zero ht)]
  simp only [add_mul, mul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 1) (Sum.inl 0) (Sum.inr 1)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `X`-boost on
  `F13 * F13`. -/
lemma pairX_F13_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genX_F13 t ht,
    genX_F13 t⁻¹ (inv_ne_zero ht)]
  simp only [add_mul, mul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 2) (Sum.inl 0) (Sum.inr 2)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `X`-boost on
  `F23 * F23`. -/
lemma pairX_F23_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) =
      ((2 : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genX_F23 t ht,
    genX_F23 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Y`-boost on
  `F01 * F01`. -/
lemma pairY_F01_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genY_F01 t ht,
    genY_F01 t⁻¹ (inv_ne_zero ht)]
  simp only [add_mul, mul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 1) (Sum.inl 0) (Sum.inr 0)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Y`-boost on
  `F01 * F23`. -/
lemma pairY_F01_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) +
      ((-((t ^ 4 - 1) ^ 2 / (2 * t ^ 4)) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genY_F01 t ht,
    genY_F01 t⁻¹ (inv_ne_zero ht),
    genY_F23 t ht,
    genY_F23 t⁻¹ (inv_ne_zero ht)]
  simp only [add_mul, mul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 1) (Sum.inl 0) (Sum.inr 2)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Y`-boost on
  `F02 * F02`. -/
lemma pairY_F02_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) =
      ((2 : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genY_F02 t ht,
    genY_F02 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Y`-boost on
  `F02 * F13`. -/
lemma pairY_F02_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) =
      ((2 : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genY_F02 t ht,
    genY_F02 t⁻¹ (inv_ne_zero ht),
    genY_F13 t ht,
    genY_F13 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Y`-boost on
  `F03 * F03`. -/
lemma pairY_F03_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genY_F03 t ht,
    genY_F03 t⁻¹ (inv_ne_zero ht)]
  simp only [add_mul, mul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 1) (Sum.inr 2) (Sum.inl 0) (Sum.inr 2)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Y`-boost on
  `F03 * F12`. -/
lemma pairY_F03_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) +
      ((-((t ^ 4 - 1) ^ 2 / (2 * t ^ 4)) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genY_F03 t ht,
    genY_F03 t⁻¹ (inv_ne_zero ht),
    genY_F12 t ht,
    genY_F12 t⁻¹ (inv_ne_zero ht)]
  simp only [add_mul, mul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inl 0) (Sum.inr 2) (Sum.inl 0) (Sum.inr 0),
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 1) (Sum.inr 2) (Sum.inl 0) (Sum.inr 0),
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 1) (Sum.inr 2) (Sum.inr 0) (Sum.inr 1)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Y`-boost on
  `F12 * F12`. -/
lemma pairY_F12_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genY_F12 t ht,
    genY_F12 t⁻¹ (inv_ne_zero ht)]
  simp only [add_mul, mul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 1) (Sum.inl 0) (Sum.inr 0)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Y`-boost on
  `F13 * F13`. -/
lemma pairY_F13_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) =
      ((2 : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genY_F13 t ht,
    genY_F13 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Y`-boost on
  `F23 * F23`. -/
lemma pairY_F23_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genY_F23 t ht,
    genY_F23 t⁻¹ (inv_ne_zero ht)]
  simp only [add_mul, mul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 1) (Sum.inr 2) (Sum.inl 0) (Sum.inr 2)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Z`-boost on `∂∂F01` with
  derivative indices `(0, 1)`. -/
lemma pairZ_dd01_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0) +
      ((-((t ^ 4 - 1) ^ 2 / (2 * t ^ 4)) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [genZ_dd01_F01 t ht, genZ_dd01_F01 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Z`-boost on `∂∂F23` with
  derivative indices `(0, 1)`. -/
lemma pairZ_dd01_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2) +
      ((-((t ^ 4 - 1) ^ 2 / (2 * t ^ 4)) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [genZ_dd01_F23 t ht, genZ_dd01_F23 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Z`-boost on `∂∂F02` with
  derivative indices `(0, 2)`. -/
lemma pairZ_dd02_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1) +
      ((-((t ^ 4 - 1) ^ 2 / (2 * t ^ 4)) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [genZ_dd02_F02 t ht, genZ_dd02_F02 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Z`-boost on `∂∂F13` with
  derivative indices `(0, 2)`. -/
lemma pairZ_dd02_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2) +
      ((-((t ^ 4 - 1) ^ 2 / (2 * t ^ 4)) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [genZ_dd02_F13 t ht, genZ_dd02_F13 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Z`-boost on `∂∂F03` with
  derivative indices `(0, 3)`. -/
lemma pairZ_dd03_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) =
      (((t ^ 8 + 1) / t ^ 4 : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [genZ_dd03_F03 t ht, genZ_dd03_F03 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Z`-boost on `∂∂F12` with
  derivative indices `(0, 3)`. -/
lemma pairZ_dd03_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) =
      (((t ^ 8 + 1) / t ^ 4 : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [genZ_dd03_F12 t ht, genZ_dd03_F12 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Z`-boost on `∂∂F03` with
  derivative indices `(1, 2)`. -/
lemma pairZ_dd12_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2)) =
      ((2 : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [genZ_dd12_F03 t ht, genZ_dd12_F03 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Z`-boost on `∂∂F12` with
  derivative indices `(1, 2)`. -/
lemma pairZ_dd12_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1)) =
      ((2 : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [genZ_dd12_F12 t ht, genZ_dd12_F12 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Z`-boost on `∂∂F02` with
  derivative indices `(1, 3)`. -/
lemma pairZ_dd13_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1) +
      ((-((t ^ 4 - 1) ^ 2 / (2 * t ^ 4)) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [genZ_dd13_F02 t ht, genZ_dd13_F02 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Z`-boost on `∂∂F13` with
  derivative indices `(1, 3)`. -/
lemma pairZ_dd13_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2) +
      ((-((t ^ 4 - 1) ^ 2 / (2 * t ^ 4)) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [genZ_dd13_F13 t ht, genZ_dd13_F13 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Z`-boost on `∂∂F01` with
  derivative indices `(2, 3)`. -/
lemma pairZ_dd23_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0) +
      ((-((t ^ 4 - 1) ^ 2 / (2 * t ^ 4)) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [genZ_dd23_F01 t ht, genZ_dd23_F01 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Z`-boost on `∂∂F23` with
  derivative indices `(2, 3)`. -/
lemma pairZ_dd23_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2) +
      ((-((t ^ 4 - 1) ^ 2 / (2 * t ^ 4)) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [genZ_dd23_F23 t ht, genZ_dd23_F23 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `X`-boost on `∂∂F01` with
  derivative indices `(0, 1)`. -/
lemma pairX_dd01_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0)) =
      (((t ^ 8 + 1) / t ^ 4 : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [genX_dd01_F01 t ht, genX_dd01_F01 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `X`-boost on `∂∂F23` with
  derivative indices `(0, 1)`. -/
lemma pairX_dd01_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2)) =
      (((t ^ 8 + 1) / t ^ 4 : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [genX_dd01_F23 t ht, genX_dd01_F23 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `X`-boost on `∂∂F02` with
  derivative indices `(0, 2)`. -/
lemma pairX_dd02_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [genX_dd02_F02 t ht, genX_dd02_F02 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `X`-boost on `∂∂F13` with
  derivative indices `(0, 2)`. -/
lemma pairX_dd02_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [genX_dd02_F13 t ht, genX_dd02_F13 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `X`-boost on `∂∂F03` with
  derivative indices `(0, 3)`. -/
lemma pairX_dd03_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [genX_dd03_F03 t ht, genX_dd03_F03 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `X`-boost on `∂∂F12` with
  derivative indices `(0, 3)`. -/
lemma pairX_dd03_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [genX_dd03_F12 t ht, genX_dd03_F12 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `X`-boost on `∂∂F03` with
  derivative indices `(1, 2)`. -/
lemma pairX_dd12_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [genX_dd12_F03 t ht, genX_dd12_F03 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `X`-boost on `∂∂F12` with
  derivative indices `(1, 2)`. -/
lemma pairX_dd12_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [genX_dd12_F12 t ht, genX_dd12_F12 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `X`-boost on `∂∂F02` with
  derivative indices `(1, 3)`. -/
lemma pairX_dd13_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [genX_dd13_F02 t ht, genX_dd13_F02 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `X`-boost on `∂∂F13` with
  derivative indices `(1, 3)`. -/
lemma pairX_dd13_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [genX_dd13_F13 t ht, genX_dd13_F13 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `X`-boost on `∂∂F01` with
  derivative indices `(2, 3)`. -/
lemma pairX_dd23_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) =
      ((2 : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [genX_dd23_F01 t ht, genX_dd23_F01 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `X`-boost on `∂∂F23` with
  derivative indices `(2, 3)`. -/
lemma pairX_dd23_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) =
      ((2 : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [genX_dd23_F23 t ht, genX_dd23_F23 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Y`-boost on `∂∂F01` with
  derivative indices `(0, 1)`. -/
lemma pairY_dd01_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0) +
      ((-((t ^ 4 - 1) ^ 2 / (2 * t ^ 4)) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [genY_dd01_F01 t ht, genY_dd01_F01 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Y`-boost on `∂∂F23` with
  derivative indices `(0, 1)`. -/
lemma pairY_dd01_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [genY_dd01_F23 t ht, genY_dd01_F23 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Y`-boost on `∂∂F02` with
  derivative indices `(0, 2)`. -/
lemma pairY_dd02_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) =
      (((t ^ 8 + 1) / t ^ 4 : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [genY_dd02_F02 t ht, genY_dd02_F02 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Y`-boost on `∂∂F13` with
  derivative indices `(0, 2)`. -/
lemma pairY_dd02_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) =
      (((t ^ 8 + 1) / t ^ 4 : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [genY_dd02_F13 t ht, genY_dd02_F13 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Y`-boost on `∂∂F03` with
  derivative indices `(0, 3)`. -/
lemma pairY_dd03_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [genY_dd03_F03 t ht, genY_dd03_F03 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Y`-boost on `∂∂F12` with
  derivative indices `(0, 3)`. -/
lemma pairY_dd03_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1) +
      ((-((t ^ 4 - 1) ^ 2 / (2 * t ^ 4)) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [genY_dd03_F12 t ht, genY_dd03_F12 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Y`-boost on `∂∂F03` with
  derivative indices `(1, 2)`. -/
lemma pairY_dd12_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [genY_dd12_F03 t ht, genY_dd12_F03 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Y`-boost on `∂∂F12` with
  derivative indices `(1, 2)`. -/
lemma pairY_dd12_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1) +
      ((-((t ^ 4 - 1) ^ 2 / (2 * t ^ 4)) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [genY_dd12_F12 t ht, genY_dd12_F12 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Y`-boost on `∂∂F02` with
  derivative indices `(1, 3)`. -/
lemma pairY_dd13_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) =
      ((2 : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [genY_dd13_F02 t ht, genY_dd13_F02 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Y`-boost on `∂∂F13` with
  derivative indices `(1, 3)`. -/
lemma pairY_dd13_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) =
      ((2 : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [genY_dd13_F13 t ht, genY_dd13_F13 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Y`-boost on `∂∂F01` with
  derivative indices `(2, 3)`. -/
lemma pairY_dd23_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0) +
      ((-((t ^ 4 - 1) ^ 2 / (2 * t ^ 4)) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [genY_dd23_F01 t ht, genY_dd23_F01 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Y`-boost on `∂∂F23` with
  derivative indices `(2, 3)`. -/
lemma pairY_dd23_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [genY_dd23_F23 t ht, genY_dd23_F23 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)
end JetAlgebra

end QED
