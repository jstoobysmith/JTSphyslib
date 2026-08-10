/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.Invariants.Subgroups.BoostsOnPhotonTerms
/-!
# Boosts acting on the fermion terms

The paired boost actions on the weight-eight fermion bilinears
`ψ̄_α (D_μ ψ)_β` and `(D̄_μ ψ̄)_α ψ_β`.
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

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `Z`-boost on the σ-contracted fermion
  pair `u0`. -/
lemma boostPairZ_u0 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostZel t ht) (Sum.inl 0) 0 0,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostZel t ht) (Sum.inl 0) 1 1,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostZel t⁻¹ (inv_ne_zero ht)) (Sum.inl 0) 0 0,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostZel t⁻¹ (inv_ne_zero ht)) (Sum.inl 0) 1 1,
    toLorentzGroup_boostZel, boostZel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `Z`-boost on the σ-contracted fermion
  pair `u1`. -/
lemma boostPairZ_u1 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0) =
      ((2 : ℝ) : ℂ) •
        (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostZel t ht) (Sum.inr 0) 0 1,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostZel t ht) (Sum.inr 0) 1 0,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostZel t⁻¹ (inv_ne_zero ht)) (Sum.inr 0) 0 1,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostZel t⁻¹ (inv_ne_zero ht)) (Sum.inr 0) 1 0,
    toLorentzGroup_boostZel, boostZel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `Z`-boost on the σ-contracted fermion
  pair `u2`. -/
lemma boostPairZ_u2 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0) =
      ((2 : ℝ) : ℂ) •
        (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostZel t ht) (Sum.inr 1) 0 1,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostZel t ht) (Sum.inr 1) 1 0,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostZel t⁻¹ (inv_ne_zero ht)) (Sum.inr 1) 0 1,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostZel t⁻¹ (inv_ne_zero ht)) (Sum.inr 1) 1 0,
    toLorentzGroup_boostZel, boostZel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `Z`-boost on the σ-contracted fermion
  pair `u3`. -/
lemma boostPairZ_u3 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostZel t ht) (Sum.inr 2) 0 0,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostZel t ht) (Sum.inr 2) 1 1,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostZel t⁻¹ (inv_ne_zero ht)) (Sum.inr 2) 0 0,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostZel t⁻¹ (inv_ne_zero ht)) (Sum.inr 2) 1 1,
    toLorentzGroup_boostZel, boostZel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `X`-boost on the σ-contracted fermion
  pair `u0`. -/
lemma boostPairX_u0 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostXel t ht) (Sum.inl 0) 0 0,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostXel t ht) (Sum.inl 0) 1 1,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostXel t⁻¹ (inv_ne_zero ht)) (Sum.inl 0) 0 0,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostXel t⁻¹ (inv_ne_zero ht)) (Sum.inl 0) 1 1,
    toLorentzGroup_boostXel, boostXel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `X`-boost on the σ-contracted fermion
  pair `u1`. -/
lemma boostPairX_u1 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostXel t ht) (Sum.inr 0) 0 1,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostXel t ht) (Sum.inr 0) 1 0,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostXel t⁻¹ (inv_ne_zero ht)) (Sum.inr 0) 0 1,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostXel t⁻¹ (inv_ne_zero ht)) (Sum.inr 0) 1 0,
    toLorentzGroup_boostXel, boostXel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `X`-boost on the σ-contracted fermion
  pair `u2`. -/
lemma boostPairX_u2 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0) =
      ((2 : ℝ) : ℂ) •
        (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostXel t ht) (Sum.inr 1) 0 1,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostXel t ht) (Sum.inr 1) 1 0,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostXel t⁻¹ (inv_ne_zero ht)) (Sum.inr 1) 0 1,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostXel t⁻¹ (inv_ne_zero ht)) (Sum.inr 1) 1 0,
    toLorentzGroup_boostXel, boostXel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `X`-boost on the σ-contracted fermion
  pair `u3`. -/
lemma boostPairX_u3 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1) =
      ((2 : ℝ) : ℂ) •
        (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostXel t ht) (Sum.inr 2) 0 0,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostXel t ht) (Sum.inr 2) 1 1,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostXel t⁻¹ (inv_ne_zero ht)) (Sum.inr 2) 0 0,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostXel t⁻¹ (inv_ne_zero ht)) (Sum.inr 2) 1 1,
    toLorentzGroup_boostXel, boostXel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `Y`-boost on the σ-contracted fermion
  pair `u0`. -/
lemma boostPairY_u0 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) +
      (Complex.I * (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ)) •
        (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostYel t ht) (Sum.inl 0) 0 0,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostYel t ht) (Sum.inl 0) 1 1,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostYel t⁻¹ (inv_ne_zero ht)) (Sum.inl 0) 0 0,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostYel t⁻¹ (inv_ne_zero ht)) (Sum.inl 0) 1 1,
    toLorentzGroup_boostYel, boostYel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring_nf; try simp only [Complex.I_sq]; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `Y`-boost on the σ-contracted fermion
  pair `u1`. -/
lemma boostPairY_u1 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0) =
      ((2 : ℝ) : ℂ) •
        (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostYel t ht) (Sum.inr 0) 0 1,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostYel t ht) (Sum.inr 0) 1 0,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostYel t⁻¹ (inv_ne_zero ht)) (Sum.inr 0) 0 1,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostYel t⁻¹ (inv_ne_zero ht)) (Sum.inr 0) 1 0,
    toLorentzGroup_boostYel, boostYel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring_nf; try simp only [Complex.I_sq]; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `Y`-boost on the σ-contracted fermion
  pair `u2`. -/
lemma boostPairY_u2 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0) +
      (-(Complex.I * (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ))) •
        (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostYel t ht) (Sum.inr 1) 0 1,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostYel t ht) (Sum.inr 1) 1 0,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostYel t⁻¹ (inv_ne_zero ht)) (Sum.inr 1) 0 1,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostYel t⁻¹ (inv_ne_zero ht)) (Sum.inr 1) 1 0,
    toLorentzGroup_boostYel, boostYel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring_nf; try simp only [Complex.I_sq]; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `Y`-boost on the σ-contracted fermion
  pair `u3`. -/
lemma boostPairY_u3 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1) =
      ((2 : ℝ) : ℂ) •
        (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostYel t ht) (Sum.inr 2) 0 0,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostYel t ht) (Sum.inr 2) 1 1,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostYel t⁻¹ (inv_ne_zero ht)) (Sum.inr 2) 0 0,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostYel t⁻¹ (inv_ne_zero ht)) (Sum.inr 2) 1 1,
    toLorentzGroup_boostYel, boostYel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring_nf; try simp only [Complex.I_sq]; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `Z`-boost on the σ-contracted fermion
  pair `ubar0`. -/
lemma boostPairZ_ubar0 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostZel t ht) (Sum.inl 0) 0 0,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostZel t ht) (Sum.inl 0) 1 1,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostZel t⁻¹ (inv_ne_zero ht)) (Sum.inl 0) 0 0,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostZel t⁻¹ (inv_ne_zero ht)) (Sum.inl 0) 1 1,
    toLorentzGroup_boostZel, boostZel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `Z`-boost on the σ-contracted fermion
  pair `ubar1`. -/
lemma boostPairZ_ubar1 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0) =
      ((2 : ℝ) : ℂ) •
        (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostZel t ht) (Sum.inr 0) 0 1,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostZel t ht) (Sum.inr 0) 1 0,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostZel t⁻¹ (inv_ne_zero ht)) (Sum.inr 0) 0 1,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostZel t⁻¹ (inv_ne_zero ht)) (Sum.inr 0) 1 0,
    toLorentzGroup_boostZel, boostZel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `Z`-boost on the σ-contracted fermion
  pair `ubar2`. -/
lemma boostPairZ_ubar2 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0) =
      ((2 : ℝ) : ℂ) •
        (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostZel t ht) (Sum.inr 1) 0 1,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostZel t ht) (Sum.inr 1) 1 0,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostZel t⁻¹ (inv_ne_zero ht)) (Sum.inr 1) 0 1,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostZel t⁻¹ (inv_ne_zero ht)) (Sum.inr 1) 1 0,
    toLorentzGroup_boostZel, boostZel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `Z`-boost on the σ-contracted fermion
  pair `ubar3`. -/
lemma boostPairZ_ubar3 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostZel t ht) (Sum.inr 2) 0 0,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostZel t ht) (Sum.inr 2) 1 1,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostZel t⁻¹ (inv_ne_zero ht)) (Sum.inr 2) 0 0,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostZel t⁻¹ (inv_ne_zero ht)) (Sum.inr 2) 1 1,
    toLorentzGroup_boostZel, boostZel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `X`-boost on the σ-contracted fermion
  pair `ubar0`. -/
lemma boostPairX_ubar0 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostXel t ht) (Sum.inl 0) 0 0,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostXel t ht) (Sum.inl 0) 1 1,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostXel t⁻¹ (inv_ne_zero ht)) (Sum.inl 0) 0 0,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostXel t⁻¹ (inv_ne_zero ht)) (Sum.inl 0) 1 1,
    toLorentzGroup_boostXel, boostXel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `X`-boost on the σ-contracted fermion
  pair `ubar1`. -/
lemma boostPairX_ubar1 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostXel t ht) (Sum.inr 0) 0 1,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostXel t ht) (Sum.inr 0) 1 0,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostXel t⁻¹ (inv_ne_zero ht)) (Sum.inr 0) 0 1,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostXel t⁻¹ (inv_ne_zero ht)) (Sum.inr 0) 1 0,
    toLorentzGroup_boostXel, boostXel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `X`-boost on the σ-contracted fermion
  pair `ubar2`. -/
lemma boostPairX_ubar2 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0) =
      ((2 : ℝ) : ℂ) •
        (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostXel t ht) (Sum.inr 1) 0 1,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostXel t ht) (Sum.inr 1) 1 0,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostXel t⁻¹ (inv_ne_zero ht)) (Sum.inr 1) 0 1,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostXel t⁻¹ (inv_ne_zero ht)) (Sum.inr 1) 1 0,
    toLorentzGroup_boostXel, boostXel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `X`-boost on the σ-contracted fermion
  pair `ubar3`. -/
lemma boostPairX_ubar3 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1) =
      ((2 : ℝ) : ℂ) •
        (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostXel t ht) (Sum.inr 2) 0 0,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostXel t ht) (Sum.inr 2) 1 1,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostXel t⁻¹ (inv_ne_zero ht)) (Sum.inr 2) 0 0,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostXel t⁻¹ (inv_ne_zero ht)) (Sum.inr 2) 1 1,
    toLorentzGroup_boostXel, boostXel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `Y`-boost on the σ-contracted fermion
  pair `ubar0`. -/
lemma boostPairY_ubar0 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) +
      (Complex.I * (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ)) •
        (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostYel t ht) (Sum.inl 0) 0 0,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostYel t ht) (Sum.inl 0) 1 1,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostYel t⁻¹ (inv_ne_zero ht)) (Sum.inl 0) 0 0,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostYel t⁻¹ (inv_ne_zero ht)) (Sum.inl 0) 1 1,
    toLorentzGroup_boostYel, boostYel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring_nf; try simp only [Complex.I_sq]; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `Y`-boost on the σ-contracted fermion
  pair `ubar1`. -/
lemma boostPairY_ubar1 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0) =
      ((2 : ℝ) : ℂ) •
        (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostYel t ht) (Sum.inr 0) 0 1,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostYel t ht) (Sum.inr 0) 1 0,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostYel t⁻¹ (inv_ne_zero ht)) (Sum.inr 0) 0 1,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostYel t⁻¹ (inv_ne_zero ht)) (Sum.inr 0) 1 0,
    toLorentzGroup_boostYel, boostYel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring_nf; try simp only [Complex.I_sq]; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `Y`-boost on the σ-contracted fermion
  pair `ubar2`. -/
lemma boostPairY_ubar2 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0) +
      (-(Complex.I * (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ))) •
        (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostYel t ht) (Sum.inr 1) 0 1,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostYel t ht) (Sum.inr 1) 1 0,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostYel t⁻¹ (inv_ne_zero ht)) (Sum.inr 1) 0 1,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostYel t⁻¹ (inv_ne_zero ht)) (Sum.inr 1) 1 0,
    toLorentzGroup_boostYel, boostYel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring_nf; try simp only [Complex.I_sq]; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `Y`-boost on the σ-contracted fermion
  pair `ubar3`. -/
lemma boostPairY_ubar3 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1) =
      ((2 : ℝ) : ℂ) •
        (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostYel t ht) (Sum.inr 2) 0 0,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostYel t ht) (Sum.inr 2) 1 1,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostYel t⁻¹ (inv_ne_zero ht)) (Sum.inr 2) 0 0,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostYel t⁻¹ (inv_ne_zero ht)) (Sum.inr 2) 1 1,
    toLorentzGroup_boostYel, boostYel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring_nf; try simp only [Complex.I_sq]; try ring)
end JetAlgebra

end LeptonGaugeSector
