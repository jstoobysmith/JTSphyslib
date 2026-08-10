/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.Invariants.Subgroups.BoostsOnFieldStrengthDerivatives
/-!
# Boosts acting on the photon terms

The paired boost actions on the weight-eight products `F_{ab} F_{cd}`
(`boostPairZ_*`, `boostPairX_*`, `boostPairY_*`) and on the second-derivative field strengths
`∂_r ∂_s F_{ab}` (`boostPairZ_dd*`, `boostPairX_dd*`, `boostPairY_dd*`).
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

/-- Right distributivity on the jet algebra. The generic `add_mul` does not fire
  here: the multiplication of the jet algebra comes from the tensor-product
  instance, which typeclass search does not connect to `RightDistribClass`. -/
lemma jetAdd_mul (u v w : JetAlgebra) : (u + v) * w = u * w + v * w := by grind

/-- Left distributivity on the jet algebra; see `jetAdd_mul`. -/
lemma jetMul_add (u v w : JetAlgebra) : u * (v + w) = u * v + u * w := by grind

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Z`-boost on
  `F01 * F01`. -/
lemma boostPairZ_F01_F01 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostZ_F01 t ht,
    boostZ_F01 t⁻¹ (inv_ne_zero ht)]
  simp only [jetAdd_mul, jetMul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 2) (Sum.inl 0) (Sum.inr 0)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Z`-boost on
  `F01 * F23`. -/
lemma boostPairZ_F01_F23 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostZ_F01 t ht,
    boostZ_F01 t⁻¹ (inv_ne_zero ht),
    boostZ_F23 t ht,
    boostZ_F23 t⁻¹ (inv_ne_zero ht)]
  simp only [jetAdd_mul, jetMul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 2) (Sum.inl 0) (Sum.inr 1)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Z`-boost on
  `F02 * F02`. -/
lemma boostPairZ_F02_F02 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostZ_F02 t ht,
    boostZ_F02 t⁻¹ (inv_ne_zero ht)]
  simp only [jetAdd_mul, jetMul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 1) (Sum.inr 2) (Sum.inl 0) (Sum.inr 1)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Z`-boost on
  `F02 * F13`. -/
lemma boostPairZ_F02_F13 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostZ_F02 t ht,
    boostZ_F02 t⁻¹ (inv_ne_zero ht),
    boostZ_F13 t ht,
    boostZ_F13 t⁻¹ (inv_ne_zero ht)]
  simp only [jetAdd_mul, jetMul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inl 0) (Sum.inr 1) (Sum.inl 0) (Sum.inr 0),
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 1) (Sum.inr 2) (Sum.inl 0) (Sum.inr 0),
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 1) (Sum.inr 2) (Sum.inr 0) (Sum.inr 2)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Z`-boost on
  `F03 * F03`. -/
lemma boostPairZ_F03_F03 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostZ_F03 t ht,
    boostZ_F03 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Z`-boost on
  `F03 * F12`. -/
lemma boostPairZ_F03_F12 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostZ_F03 t ht,
    boostZ_F03 t⁻¹ (inv_ne_zero ht),
    boostZ_F12 t ht,
    boostZ_F12 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Z`-boost on
  `F12 * F12`. -/
lemma boostPairZ_F12_F12 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostZ_F12 t ht,
    boostZ_F12 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Z`-boost on
  `F13 * F13`. -/
lemma boostPairZ_F13_F13 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostZ_F13 t ht,
    boostZ_F13 t⁻¹ (inv_ne_zero ht)]
  simp only [jetAdd_mul, jetMul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 2) (Sum.inl 0) (Sum.inr 0)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Z`-boost on
  `F23 * F23`. -/
lemma boostPairZ_F23_F23 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostZ_F23 t ht,
    boostZ_F23 t⁻¹ (inv_ne_zero ht)]
  simp only [jetAdd_mul, jetMul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 1) (Sum.inr 2) (Sum.inl 0) (Sum.inr 1)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `X`-boost on
  `F01 * F01`. -/
lemma boostPairX_F01_F01 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostX_F01 t ht,
    boostX_F01 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `X`-boost on
  `F01 * F23`. -/
lemma boostPairX_F01_F23 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostX_F01 t ht,
    boostX_F01 t⁻¹ (inv_ne_zero ht),
    boostX_F23 t ht,
    boostX_F23 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `X`-boost on
  `F02 * F02`. -/
lemma boostPairX_F02_F02 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostX_F02 t ht,
    boostX_F02 t⁻¹ (inv_ne_zero ht)]
  simp only [jetAdd_mul, jetMul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 1) (Sum.inl 0) (Sum.inr 1)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `X`-boost on
  `F02 * F13`. -/
lemma boostPairX_F02_F13 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostX_F02 t ht,
    boostX_F02 t⁻¹ (inv_ne_zero ht),
    boostX_F13 t ht,
    boostX_F13 t⁻¹ (inv_ne_zero ht)]
  simp only [jetAdd_mul, jetMul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 1) (Sum.inl 0) (Sum.inr 2)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `X`-boost on
  `F03 * F03`. -/
lemma boostPairX_F03_F03 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostX_F03 t ht,
    boostX_F03 t⁻¹ (inv_ne_zero ht)]
  simp only [jetAdd_mul, jetMul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 2) (Sum.inl 0) (Sum.inr 2)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `X`-boost on
  `F03 * F12`. -/
lemma boostPairX_F03_F12 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostX_F03 t ht,
    boostX_F03 t⁻¹ (inv_ne_zero ht),
    boostX_F12 t ht,
    boostX_F12 t⁻¹ (inv_ne_zero ht)]
  simp only [jetAdd_mul, jetMul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inl 0) (Sum.inr 2) (Sum.inl 0) (Sum.inr 1),
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 2) (Sum.inl 0) (Sum.inr 1),
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 2) (Sum.inr 0) (Sum.inr 1)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `X`-boost on
  `F12 * F12`. -/
lemma boostPairX_F12_F12 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostX_F12 t ht,
    boostX_F12 t⁻¹ (inv_ne_zero ht)]
  simp only [jetAdd_mul, jetMul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 1) (Sum.inl 0) (Sum.inr 1)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `X`-boost on
  `F13 * F13`. -/
lemma boostPairX_F13_F13 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostX_F13 t ht,
    boostX_F13 t⁻¹ (inv_ne_zero ht)]
  simp only [jetAdd_mul, jetMul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 2) (Sum.inl 0) (Sum.inr 2)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `X`-boost on
  `F23 * F23`. -/
lemma boostPairX_F23_F23 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostX_F23 t ht,
    boostX_F23 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Y`-boost on
  `F01 * F01`. -/
lemma boostPairY_F01_F01 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostY_F01 t ht,
    boostY_F01 t⁻¹ (inv_ne_zero ht)]
  simp only [jetAdd_mul, jetMul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 1) (Sum.inl 0) (Sum.inr 0)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Y`-boost on
  `F01 * F23`. -/
lemma boostPairY_F01_F23 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostY_F01 t ht,
    boostY_F01 t⁻¹ (inv_ne_zero ht),
    boostY_F23 t ht,
    boostY_F23 t⁻¹ (inv_ne_zero ht)]
  simp only [jetAdd_mul, jetMul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 1) (Sum.inl 0) (Sum.inr 2)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Y`-boost on
  `F02 * F02`. -/
lemma boostPairY_F02_F02 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostY_F02 t ht,
    boostY_F02 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Y`-boost on
  `F02 * F13`. -/
lemma boostPairY_F02_F13 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostY_F02 t ht,
    boostY_F02 t⁻¹ (inv_ne_zero ht),
    boostY_F13 t ht,
    boostY_F13 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Y`-boost on
  `F03 * F03`. -/
lemma boostPairY_F03_F03 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostY_F03 t ht,
    boostY_F03 t⁻¹ (inv_ne_zero ht)]
  simp only [jetAdd_mul, jetMul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 1) (Sum.inr 2) (Sum.inl 0) (Sum.inr 2)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Y`-boost on
  `F03 * F12`. -/
lemma boostPairY_F03_F12 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostY_F03 t ht,
    boostY_F03 t⁻¹ (inv_ne_zero ht),
    boostY_F12 t ht,
    boostY_F12 t⁻¹ (inv_ne_zero ht)]
  simp only [jetAdd_mul, jetMul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inl 0) (Sum.inr 2) (Sum.inl 0) (Sum.inr 0),
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 1) (Sum.inr 2) (Sum.inl 0) (Sum.inr 0),
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 1) (Sum.inr 2) (Sum.inr 0) (Sum.inr 1)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Y`-boost on
  `F12 * F12`. -/
lemma boostPairY_F12_F12 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostY_F12 t ht,
    boostY_F12 t⁻¹ (inv_ne_zero ht)]
  simp only [jetAdd_mul, jetMul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 1) (Sum.inl 0) (Sum.inr 0)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Y`-boost on
  `F13 * F13`. -/
lemma boostPairY_F13_F13 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostY_F13 t ht,
    boostY_F13 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Y`-boost on
  `F23 * F23`. -/
lemma boostPairY_F23_F23 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostY_F23 t ht,
    boostY_F23 t⁻¹ (inv_ne_zero ht)]
  simp only [jetAdd_mul, jetMul_add, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 1) (Sum.inr 2) (Sum.inl 0) (Sum.inr 2)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Z`-boost on `∂∂F01` with
  derivative indices `(0, 1)`. -/
lemma boostPairZ_dd01_F01 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostZ_dd01_F01 t ht, boostZ_dd01_F01 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Z`-boost on `∂∂F23` with
  derivative indices `(0, 1)`. -/
lemma boostPairZ_dd01_F23 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostZ_dd01_F23 t ht, boostZ_dd01_F23 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Z`-boost on `∂∂F02` with
  derivative indices `(0, 2)`. -/
lemma boostPairZ_dd02_F02 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostZ_dd02_F02 t ht, boostZ_dd02_F02 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Z`-boost on `∂∂F13` with
  derivative indices `(0, 2)`. -/
lemma boostPairZ_dd02_F13 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostZ_dd02_F13 t ht, boostZ_dd02_F13 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Z`-boost on `∂∂F03` with
  derivative indices `(0, 3)`. -/
lemma boostPairZ_dd03_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) =
      (((t ^ 8 + 1) / t ^ 4 : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [boostZ_dd03_F03 t ht, boostZ_dd03_F03 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Z`-boost on `∂∂F12` with
  derivative indices `(0, 3)`. -/
lemma boostPairZ_dd03_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) =
      (((t ^ 8 + 1) / t ^ 4 : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [boostZ_dd03_F12 t ht, boostZ_dd03_F12 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Z`-boost on `∂∂F03` with
  derivative indices `(1, 2)`. -/
lemma boostPairZ_dd12_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2)) =
      ((2 : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [boostZ_dd12_F03 t ht, boostZ_dd12_F03 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Z`-boost on `∂∂F12` with
  derivative indices `(1, 2)`. -/
lemma boostPairZ_dd12_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1)) =
      ((2 : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [boostZ_dd12_F12 t ht, boostZ_dd12_F12 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Z`-boost on `∂∂F02` with
  derivative indices `(1, 3)`. -/
lemma boostPairZ_dd13_F02 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostZ_dd13_F02 t ht, boostZ_dd13_F02 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Z`-boost on `∂∂F13` with
  derivative indices `(1, 3)`. -/
lemma boostPairZ_dd13_F13 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostZ_dd13_F13 t ht, boostZ_dd13_F13 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Z`-boost on `∂∂F01` with
  derivative indices `(2, 3)`. -/
lemma boostPairZ_dd23_F01 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostZ_dd23_F01 t ht, boostZ_dd23_F01 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Z`-boost on `∂∂F23` with
  derivative indices `(2, 3)`. -/
lemma boostPairZ_dd23_F23 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostZ_dd23_F23 t ht, boostZ_dd23_F23 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `X`-boost on `∂∂F01` with
  derivative indices `(0, 1)`. -/
lemma boostPairX_dd01_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0)) =
      (((t ^ 8 + 1) / t ^ 4 : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [boostX_dd01_F01 t ht, boostX_dd01_F01 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `X`-boost on `∂∂F23` with
  derivative indices `(0, 1)`. -/
lemma boostPairX_dd01_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2)) =
      (((t ^ 8 + 1) / t ^ 4 : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [boostX_dd01_F23 t ht, boostX_dd01_F23 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `X`-boost on `∂∂F02` with
  derivative indices `(0, 2)`. -/
lemma boostPairX_dd02_F02 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostX_dd02_F02 t ht, boostX_dd02_F02 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `X`-boost on `∂∂F13` with
  derivative indices `(0, 2)`. -/
lemma boostPairX_dd02_F13 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostX_dd02_F13 t ht, boostX_dd02_F13 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `X`-boost on `∂∂F03` with
  derivative indices `(0, 3)`. -/
lemma boostPairX_dd03_F03 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostX_dd03_F03 t ht, boostX_dd03_F03 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `X`-boost on `∂∂F12` with
  derivative indices `(0, 3)`. -/
lemma boostPairX_dd03_F12 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostX_dd03_F12 t ht, boostX_dd03_F12 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `X`-boost on `∂∂F03` with
  derivative indices `(1, 2)`. -/
lemma boostPairX_dd12_F03 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostX_dd12_F03 t ht, boostX_dd12_F03 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `X`-boost on `∂∂F12` with
  derivative indices `(1, 2)`. -/
lemma boostPairX_dd12_F12 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostX_dd12_F12 t ht, boostX_dd12_F12 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `X`-boost on `∂∂F02` with
  derivative indices `(1, 3)`. -/
lemma boostPairX_dd13_F02 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostX_dd13_F02 t ht, boostX_dd13_F02 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `X`-boost on `∂∂F13` with
  derivative indices `(1, 3)`. -/
lemma boostPairX_dd13_F13 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostX_dd13_F13 t ht, boostX_dd13_F13 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `X`-boost on `∂∂F01` with
  derivative indices `(2, 3)`. -/
lemma boostPairX_dd23_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) =
      ((2 : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [boostX_dd23_F01 t ht, boostX_dd23_F01 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `X`-boost on `∂∂F23` with
  derivative indices `(2, 3)`. -/
lemma boostPairX_dd23_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) =
      ((2 : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [boostX_dd23_F23 t ht, boostX_dd23_F23 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Y`-boost on `∂∂F01` with
  derivative indices `(0, 1)`. -/
lemma boostPairY_dd01_F01 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostY_dd01_F01 t ht, boostY_dd01_F01 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Y`-boost on `∂∂F23` with
  derivative indices `(0, 1)`. -/
lemma boostPairY_dd01_F23 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostY_dd01_F23 t ht, boostY_dd01_F23 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Y`-boost on `∂∂F02` with
  derivative indices `(0, 2)`. -/
lemma boostPairY_dd02_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) =
      (((t ^ 8 + 1) / t ^ 4 : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [boostY_dd02_F02 t ht, boostY_dd02_F02 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Y`-boost on `∂∂F13` with
  derivative indices `(0, 2)`. -/
lemma boostPairY_dd02_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) =
      (((t ^ 8 + 1) / t ^ 4 : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [boostY_dd02_F13 t ht, boostY_dd02_F13 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Y`-boost on `∂∂F03` with
  derivative indices `(0, 3)`. -/
lemma boostPairY_dd03_F03 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostY_dd03_F03 t ht, boostY_dd03_F03 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Y`-boost on `∂∂F12` with
  derivative indices `(0, 3)`. -/
lemma boostPairY_dd03_F12 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostY_dd03_F12 t ht, boostY_dd03_F12 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Y`-boost on `∂∂F03` with
  derivative indices `(1, 2)`. -/
lemma boostPairY_dd12_F03 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostY_dd12_F03 t ht, boostY_dd12_F03 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Y`-boost on `∂∂F12` with
  derivative indices `(1, 2)`. -/
lemma boostPairY_dd12_F12 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostY_dd12_F12 t ht, boostY_dd12_F12 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Y`-boost on `∂∂F02` with
  derivative indices `(1, 3)`. -/
lemma boostPairY_dd13_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) =
      ((2 : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [boostY_dd13_F02 t ht, boostY_dd13_F02 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Y`-boost on `∂∂F13` with
  derivative indices `(1, 3)`. -/
lemma boostPairY_dd13_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) =
      ((2 : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [boostY_dd13_F13 t ht, boostY_dd13_F13 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Y`-boost on `∂∂F01` with
  derivative indices `(2, 3)`. -/
lemma boostPairY_dd23_F01 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostY_dd23_F01 t ht, boostY_dd23_F01 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Y`-boost on `∂∂F23` with
  derivative indices `(2, 3)`. -/
lemma boostPairY_dd23_F23 (t : ℝ) (ht : t ≠ 0) :
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
  simp only [boostY_dd23_F23 t ht, boostY_dd23_F23 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)
end JetAlgebra

end LeptonGaugeSector
