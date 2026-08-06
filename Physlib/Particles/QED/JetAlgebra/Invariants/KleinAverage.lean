/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.QED.JetAlgebra.Invariants.ProjectorValues
/-!
# The Klein average on the weight-eight monomials

The entries of the Lorentz matrices of the three parity rotations, and the
values of the Klein four-group average `kleinAvg` on the weight-eight
monomials.
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
/-- Entries of the Lorentz matrix of `parityZ`. -/
lemma parityMatZ_00 :
    (Lorentz.SL2C.toLorentzGroup parityZ).1 (Sum.inl 0) (Sum.inl 0) = 1 := by
  rw [toLorentzGroup_parityZ]
  norm_num [paritySignZ]
  all_goals decide

lemma parityMatZ_01 :
    (Lorentz.SL2C.toLorentzGroup parityZ).1 (Sum.inl 0) (Sum.inr 0) = 0 := by
  rw [toLorentzGroup_parityZ]
  norm_num [paritySignZ]
  all_goals decide

lemma parityMatZ_02 :
    (Lorentz.SL2C.toLorentzGroup parityZ).1 (Sum.inl 0) (Sum.inr 1) = 0 := by
  rw [toLorentzGroup_parityZ]
  norm_num [paritySignZ]
  all_goals decide

lemma parityMatZ_03 :
    (Lorentz.SL2C.toLorentzGroup parityZ).1 (Sum.inl 0) (Sum.inr 2) = 0 := by
  rw [toLorentzGroup_parityZ]
  norm_num [paritySignZ]
  all_goals decide

lemma parityMatZ_10 :
    (Lorentz.SL2C.toLorentzGroup parityZ).1 (Sum.inr 0) (Sum.inl 0) = 0 := by
  rw [toLorentzGroup_parityZ]
  norm_num [paritySignZ]
  all_goals decide

lemma parityMatZ_11 :
    (Lorentz.SL2C.toLorentzGroup parityZ).1 (Sum.inr 0) (Sum.inr 0) = -1 := by
  rw [toLorentzGroup_parityZ]
  norm_num [paritySignZ]
  all_goals decide

lemma parityMatZ_12 :
    (Lorentz.SL2C.toLorentzGroup parityZ).1 (Sum.inr 0) (Sum.inr 1) = 0 := by
  rw [toLorentzGroup_parityZ]
  norm_num [paritySignZ]
  all_goals decide

lemma parityMatZ_13 :
    (Lorentz.SL2C.toLorentzGroup parityZ).1 (Sum.inr 0) (Sum.inr 2) = 0 := by
  rw [toLorentzGroup_parityZ]
  norm_num [paritySignZ]
  all_goals decide

lemma parityMatZ_20 :
    (Lorentz.SL2C.toLorentzGroup parityZ).1 (Sum.inr 1) (Sum.inl 0) = 0 := by
  rw [toLorentzGroup_parityZ]
  norm_num [paritySignZ]
  all_goals decide

lemma parityMatZ_21 :
    (Lorentz.SL2C.toLorentzGroup parityZ).1 (Sum.inr 1) (Sum.inr 0) = 0 := by
  rw [toLorentzGroup_parityZ]
  norm_num [paritySignZ]
  all_goals decide

lemma parityMatZ_22 :
    (Lorentz.SL2C.toLorentzGroup parityZ).1 (Sum.inr 1) (Sum.inr 1) = -1 := by
  rw [toLorentzGroup_parityZ]
  norm_num [paritySignZ]
  all_goals decide

lemma parityMatZ_23 :
    (Lorentz.SL2C.toLorentzGroup parityZ).1 (Sum.inr 1) (Sum.inr 2) = 0 := by
  rw [toLorentzGroup_parityZ]
  norm_num [paritySignZ]
  all_goals decide

lemma parityMatZ_30 :
    (Lorentz.SL2C.toLorentzGroup parityZ).1 (Sum.inr 2) (Sum.inl 0) = 0 := by
  rw [toLorentzGroup_parityZ]
  norm_num [paritySignZ]
  all_goals decide

lemma parityMatZ_31 :
    (Lorentz.SL2C.toLorentzGroup parityZ).1 (Sum.inr 2) (Sum.inr 0) = 0 := by
  rw [toLorentzGroup_parityZ]
  norm_num [paritySignZ]
  all_goals decide

lemma parityMatZ_32 :
    (Lorentz.SL2C.toLorentzGroup parityZ).1 (Sum.inr 2) (Sum.inr 1) = 0 := by
  rw [toLorentzGroup_parityZ]
  norm_num [paritySignZ]
  all_goals decide

lemma parityMatZ_33 :
    (Lorentz.SL2C.toLorentzGroup parityZ).1 (Sum.inr 2) (Sum.inr 2) = 1 := by
  rw [toLorentzGroup_parityZ]
  norm_num [paritySignZ]
  all_goals decide

/-- Entries of the Lorentz matrix of `parityX`. -/
lemma parityMatX_00 :
    (Lorentz.SL2C.toLorentzGroup parityX).1 (Sum.inl 0) (Sum.inl 0) = 1 := by
  rw [toLorentzGroup_parityX]
  norm_num [paritySignX]
  all_goals decide

lemma parityMatX_01 :
    (Lorentz.SL2C.toLorentzGroup parityX).1 (Sum.inl 0) (Sum.inr 0) = 0 := by
  rw [toLorentzGroup_parityX]
  norm_num [paritySignX]
  all_goals decide

lemma parityMatX_02 :
    (Lorentz.SL2C.toLorentzGroup parityX).1 (Sum.inl 0) (Sum.inr 1) = 0 := by
  rw [toLorentzGroup_parityX]
  norm_num [paritySignX]
  all_goals decide

lemma parityMatX_03 :
    (Lorentz.SL2C.toLorentzGroup parityX).1 (Sum.inl 0) (Sum.inr 2) = 0 := by
  rw [toLorentzGroup_parityX]
  norm_num [paritySignX]
  all_goals decide

lemma parityMatX_10 :
    (Lorentz.SL2C.toLorentzGroup parityX).1 (Sum.inr 0) (Sum.inl 0) = 0 := by
  rw [toLorentzGroup_parityX]
  norm_num [paritySignX]
  all_goals decide

lemma parityMatX_11 :
    (Lorentz.SL2C.toLorentzGroup parityX).1 (Sum.inr 0) (Sum.inr 0) = 1 := by
  rw [toLorentzGroup_parityX]
  norm_num [paritySignX]
  all_goals decide

lemma parityMatX_12 :
    (Lorentz.SL2C.toLorentzGroup parityX).1 (Sum.inr 0) (Sum.inr 1) = 0 := by
  rw [toLorentzGroup_parityX]
  norm_num [paritySignX]
  all_goals decide

lemma parityMatX_13 :
    (Lorentz.SL2C.toLorentzGroup parityX).1 (Sum.inr 0) (Sum.inr 2) = 0 := by
  rw [toLorentzGroup_parityX]
  norm_num [paritySignX]
  all_goals decide

lemma parityMatX_20 :
    (Lorentz.SL2C.toLorentzGroup parityX).1 (Sum.inr 1) (Sum.inl 0) = 0 := by
  rw [toLorentzGroup_parityX]
  norm_num [paritySignX]
  all_goals decide

lemma parityMatX_21 :
    (Lorentz.SL2C.toLorentzGroup parityX).1 (Sum.inr 1) (Sum.inr 0) = 0 := by
  rw [toLorentzGroup_parityX]
  norm_num [paritySignX]
  all_goals decide

lemma parityMatX_22 :
    (Lorentz.SL2C.toLorentzGroup parityX).1 (Sum.inr 1) (Sum.inr 1) = -1 := by
  rw [toLorentzGroup_parityX]
  norm_num [paritySignX]
  all_goals decide

lemma parityMatX_23 :
    (Lorentz.SL2C.toLorentzGroup parityX).1 (Sum.inr 1) (Sum.inr 2) = 0 := by
  rw [toLorentzGroup_parityX]
  norm_num [paritySignX]
  all_goals decide

lemma parityMatX_30 :
    (Lorentz.SL2C.toLorentzGroup parityX).1 (Sum.inr 2) (Sum.inl 0) = 0 := by
  rw [toLorentzGroup_parityX]
  norm_num [paritySignX]
  all_goals decide

lemma parityMatX_31 :
    (Lorentz.SL2C.toLorentzGroup parityX).1 (Sum.inr 2) (Sum.inr 0) = 0 := by
  rw [toLorentzGroup_parityX]
  norm_num [paritySignX]
  all_goals decide

lemma parityMatX_32 :
    (Lorentz.SL2C.toLorentzGroup parityX).1 (Sum.inr 2) (Sum.inr 1) = 0 := by
  rw [toLorentzGroup_parityX]
  norm_num [paritySignX]
  all_goals decide

lemma parityMatX_33 :
    (Lorentz.SL2C.toLorentzGroup parityX).1 (Sum.inr 2) (Sum.inr 2) = -1 := by
  rw [toLorentzGroup_parityX]
  norm_num [paritySignX]
  all_goals decide

/-- Entries of the Lorentz matrix of `parityY`. -/
lemma parityMatY_00 :
    (Lorentz.SL2C.toLorentzGroup parityY).1 (Sum.inl 0) (Sum.inl 0) = 1 := by
  rw [toLorentzGroup_parityY]
  norm_num [paritySignY]
  all_goals decide

lemma parityMatY_01 :
    (Lorentz.SL2C.toLorentzGroup parityY).1 (Sum.inl 0) (Sum.inr 0) = 0 := by
  rw [toLorentzGroup_parityY]
  norm_num [paritySignY]
  all_goals decide

lemma parityMatY_02 :
    (Lorentz.SL2C.toLorentzGroup parityY).1 (Sum.inl 0) (Sum.inr 1) = 0 := by
  rw [toLorentzGroup_parityY]
  norm_num [paritySignY]
  all_goals decide

lemma parityMatY_03 :
    (Lorentz.SL2C.toLorentzGroup parityY).1 (Sum.inl 0) (Sum.inr 2) = 0 := by
  rw [toLorentzGroup_parityY]
  norm_num [paritySignY]
  all_goals decide

lemma parityMatY_10 :
    (Lorentz.SL2C.toLorentzGroup parityY).1 (Sum.inr 0) (Sum.inl 0) = 0 := by
  rw [toLorentzGroup_parityY]
  norm_num [paritySignY]
  all_goals decide

lemma parityMatY_11 :
    (Lorentz.SL2C.toLorentzGroup parityY).1 (Sum.inr 0) (Sum.inr 0) = -1 := by
  rw [toLorentzGroup_parityY]
  norm_num [paritySignY]
  all_goals decide

lemma parityMatY_12 :
    (Lorentz.SL2C.toLorentzGroup parityY).1 (Sum.inr 0) (Sum.inr 1) = 0 := by
  rw [toLorentzGroup_parityY]
  norm_num [paritySignY]
  all_goals decide

lemma parityMatY_13 :
    (Lorentz.SL2C.toLorentzGroup parityY).1 (Sum.inr 0) (Sum.inr 2) = 0 := by
  rw [toLorentzGroup_parityY]
  norm_num [paritySignY]
  all_goals decide

lemma parityMatY_20 :
    (Lorentz.SL2C.toLorentzGroup parityY).1 (Sum.inr 1) (Sum.inl 0) = 0 := by
  rw [toLorentzGroup_parityY]
  norm_num [paritySignY]
  all_goals decide

lemma parityMatY_21 :
    (Lorentz.SL2C.toLorentzGroup parityY).1 (Sum.inr 1) (Sum.inr 0) = 0 := by
  rw [toLorentzGroup_parityY]
  norm_num [paritySignY]
  all_goals decide

lemma parityMatY_22 :
    (Lorentz.SL2C.toLorentzGroup parityY).1 (Sum.inr 1) (Sum.inr 1) = 1 := by
  rw [toLorentzGroup_parityY]
  norm_num [paritySignY]
  all_goals decide

lemma parityMatY_23 :
    (Lorentz.SL2C.toLorentzGroup parityY).1 (Sum.inr 1) (Sum.inr 2) = 0 := by
  rw [toLorentzGroup_parityY]
  norm_num [paritySignY]
  all_goals decide

lemma parityMatY_30 :
    (Lorentz.SL2C.toLorentzGroup parityY).1 (Sum.inr 2) (Sum.inl 0) = 0 := by
  rw [toLorentzGroup_parityY]
  norm_num [paritySignY]
  all_goals decide

lemma parityMatY_31 :
    (Lorentz.SL2C.toLorentzGroup parityY).1 (Sum.inr 2) (Sum.inr 0) = 0 := by
  rw [toLorentzGroup_parityY]
  norm_num [paritySignY]
  all_goals decide

lemma parityMatY_32 :
    (Lorentz.SL2C.toLorentzGroup parityY).1 (Sum.inr 2) (Sum.inr 1) = 0 := by
  rw [toLorentzGroup_parityY]
  norm_num [paritySignY]
  all_goals decide

lemma parityMatY_33 :
    (Lorentz.SL2C.toLorentzGroup parityY).1 (Sum.inr 2) (Sum.inr 2) = -1 := by
  rw [toLorentzGroup_parityY]
  norm_num [paritySignY]
  all_goals decide

set_option maxHeartbeats 2000000 in
/-- The Klein average acts diagonally on products of two field strengths, by
  the average of the four parity signs. -/
lemma kleinAvg_fieldStrengthDeriv_nil_mul (a b c d : Fin 1 ⊕ Fin 3) :
    kleinAvg (fieldStrengthDeriv {} a b * fieldStrengthDeriv {} c d) =
      (((1 + paritySignZ a * paritySignZ b * (paritySignZ c * paritySignZ d) +
        paritySignY a * paritySignY b * (paritySignY c * paritySignY d) +
        paritySignX a * paritySignX b * (paritySignX c * paritySignX d)) / 4 : ℝ) : ℂ) •
        (fieldStrengthDeriv {} a b * fieldStrengthDeriv {} c d) := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_apply_mul,
    repLorentzGroup_diag_fieldStrengthDeriv toLorentzGroup_parityZ,
    repLorentzGroup_diag_fieldStrengthDeriv toLorentzGroup_parityY,
    repLorentzGroup_diag_fieldStrengthDeriv toLorentzGroup_parityX,
    smul_mul_smul_comm]
  push_cast
  module

/-- Under a diagonal Lorentz transformation the second-derivative field
  strength scales by the product of the signs of its four indices. -/
lemma repLorentzGroup_diag_fieldStrengthDeriv_pair {M : SL(2,ℂ)}
    {sgn : Fin 1 ⊕ Fin 3 → ℝ}
    (hM : ∀ a b, (Lorentz.SL2C.toLorentzGroup M).1 a b =
      if a = b then sgn a else 0) (ρ τ μ ν : Fin 1 ⊕ Fin 3) :
    repLorentzGroup M (fieldStrengthDeriv {ρ, τ} μ ν) =
      ((sgn ρ * (sgn τ * (sgn μ * sgn ν)) : ℝ) : ℂ) •
        fieldStrengthDeriv {ρ, τ} μ ν := by
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  rw [Finset.sum_eq_single ρ (fun r _ hr => Finset.sum_eq_zero fun s _ =>
      Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => by
        rw [hM r ρ, if_neg hr, zero_mul, Complex.ofReal_zero, zero_smul])
    (fun h => absurd (Finset.mem_univ ρ) h)]
  rw [Finset.sum_eq_single τ (fun s _ hs => Finset.sum_eq_zero fun a _ =>
      Finset.sum_eq_zero fun b _ => by
        rw [hM s τ, if_neg hs, zero_mul, mul_zero, Complex.ofReal_zero, zero_smul])
    (fun h => absurd (Finset.mem_univ τ) h)]
  rw [Finset.sum_eq_single μ (fun a _ ha => Finset.sum_eq_zero fun b _ => by
      rw [hM a μ, if_neg ha, zero_mul, mul_zero, mul_zero, Complex.ofReal_zero,
        zero_smul])
    (fun h => absurd (Finset.mem_univ μ) h)]
  rw [Finset.sum_eq_single ν (fun b _ hb => by
      rw [hM b ν, if_neg hb, mul_zero, mul_zero, mul_zero, Complex.ofReal_zero,
        zero_smul])
    (fun h => absurd (Finset.mem_univ ν) h)]
  rw [hM ρ ρ, if_pos rfl, hM τ τ, if_pos rfl, hM μ μ, if_pos rfl, hM ν ν,
    if_pos rfl]

/-- The Klein average acts diagonally on the second-derivative field
  strengths. -/
lemma kleinAvg_fieldStrengthDeriv_pair (r t a b : Fin 1 ⊕ Fin 3) :
    kleinAvg (fieldStrengthDeriv {r, t} a b) =
      (((1 + paritySignZ r * (paritySignZ t * (paritySignZ a * paritySignZ b)) +
        paritySignY r * (paritySignY t * (paritySignY a * paritySignY b)) +
        paritySignX r * (paritySignX t * (paritySignX a * paritySignX b))) / 4 : ℝ) : ℂ) •
        fieldStrengthDeriv {r, t} a b := by
  rw [kleinAvg_apply,
    repLorentzGroup_diag_fieldStrengthDeriv_pair toLorentzGroup_parityZ,
    repLorentzGroup_diag_fieldStrengthDeriv_pair toLorentzGroup_parityY,
    repLorentzGroup_diag_fieldStrengthDeriv_pair toLorentzGroup_parityX]
  push_cast
  module

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[0,0,0]` (u-family). -/
lemma kleinAvg_u_e000 :
    kleinAvg (Dbarψ [] 0 * Dψ [Sum.inl 0] 0) =
      (1/2 : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11,
        parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23,
        parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01,
        parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13,
        parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31,
        parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03,
        parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21,
        parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 : JetAlgebra) = X0, (Dbarψ [] 1 * Dψ [Sum.inl 0] 1 :
      JetAlgebra) = X1, (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 : JetAlgebra) = X2, (Dbarψ [] 1 * Dψ [Sum.inr
      0] 0 : JetAlgebra) = X3, (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 : JetAlgebra) = X4, (Dbarψ [] 1 * Dψ
      [Sum.inr 1] 0 : JetAlgebra) = X5, (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 : JetAlgebra) = X6, (Dbarψ []
      1 * Dψ [Sum.inr 2] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[0,0,1]` (u-family). -/
lemma kleinAvg_u_e001 :
    kleinAvg (Dbarψ [] 0 * Dψ [Sum.inl 0] 1) =
      0 := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11,
        parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23,
        parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01,
        parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13,
        parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31,
        parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03,
        parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21,
        parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 : JetAlgebra) = X0, (Dbarψ [] 1 * Dψ [Sum.inl 0] 1 :
      JetAlgebra) = X1, (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 : JetAlgebra) = X2, (Dbarψ [] 1 * Dψ [Sum.inr
      0] 0 : JetAlgebra) = X3, (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 : JetAlgebra) = X4, (Dbarψ [] 1 * Dψ
      [Sum.inr 1] 0 : JetAlgebra) = X5, (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 : JetAlgebra) = X6, (Dbarψ []
      1 * Dψ [Sum.inr 2] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[0,1,0]` (u-family). -/
lemma kleinAvg_u_e010 :
    kleinAvg (Dbarψ [] 1 * Dψ [Sum.inl 0] 0) =
      0 := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11,
        parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23,
        parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01,
        parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13,
        parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31,
        parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03,
        parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21,
        parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 : JetAlgebra) = X0, (Dbarψ [] 1 * Dψ [Sum.inl 0] 1 :
      JetAlgebra) = X1, (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 : JetAlgebra) = X2, (Dbarψ [] 1 * Dψ [Sum.inr
      0] 0 : JetAlgebra) = X3, (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 : JetAlgebra) = X4, (Dbarψ [] 1 * Dψ
      [Sum.inr 1] 0 : JetAlgebra) = X5, (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 : JetAlgebra) = X6, (Dbarψ []
      1 * Dψ [Sum.inr 2] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[0,1,1]` (u-family). -/
lemma kleinAvg_u_e011 :
    kleinAvg (Dbarψ [] 1 * Dψ [Sum.inl 0] 1) =
      (1/2 : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11,
        parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23,
        parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01,
        parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13,
        parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31,
        parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03,
        parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21,
        parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 : JetAlgebra) = X0, (Dbarψ [] 1 * Dψ [Sum.inl 0] 1 :
      JetAlgebra) = X1, (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 : JetAlgebra) = X2, (Dbarψ [] 1 * Dψ [Sum.inr
      0] 0 : JetAlgebra) = X3, (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 : JetAlgebra) = X4, (Dbarψ [] 1 * Dψ
      [Sum.inr 1] 0 : JetAlgebra) = X5, (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 : JetAlgebra) = X6, (Dbarψ []
      1 * Dψ [Sum.inr 2] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[1,0,0]` (u-family). -/
lemma kleinAvg_u_e100 :
    kleinAvg (Dbarψ [] 0 * Dψ [Sum.inr 0] 0) =
      0 := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11,
        parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23,
        parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01,
        parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13,
        parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31,
        parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03,
        parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21,
        parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 : JetAlgebra) = X0, (Dbarψ [] 1 * Dψ [Sum.inl 0] 1 :
      JetAlgebra) = X1, (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 : JetAlgebra) = X2, (Dbarψ [] 1 * Dψ [Sum.inr
      0] 0 : JetAlgebra) = X3, (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 : JetAlgebra) = X4, (Dbarψ [] 1 * Dψ
      [Sum.inr 1] 0 : JetAlgebra) = X5, (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 : JetAlgebra) = X6, (Dbarψ []
      1 * Dψ [Sum.inr 2] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[1,0,1]` (u-family). -/
lemma kleinAvg_u_e101 :
    kleinAvg (Dbarψ [] 0 * Dψ [Sum.inr 0] 1) =
      (1/2 : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0) := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11,
        parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23,
        parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01,
        parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13,
        parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31,
        parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03,
        parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21,
        parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 : JetAlgebra) = X0, (Dbarψ [] 1 * Dψ [Sum.inl 0] 1 :
      JetAlgebra) = X1, (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 : JetAlgebra) = X2, (Dbarψ [] 1 * Dψ [Sum.inr
      0] 0 : JetAlgebra) = X3, (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 : JetAlgebra) = X4, (Dbarψ [] 1 * Dψ
      [Sum.inr 1] 0 : JetAlgebra) = X5, (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 : JetAlgebra) = X6, (Dbarψ []
      1 * Dψ [Sum.inr 2] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[1,1,0]` (u-family). -/
lemma kleinAvg_u_e110 :
    kleinAvg (Dbarψ [] 1 * Dψ [Sum.inr 0] 0) =
      (1/2 : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0) := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11,
        parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23,
        parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01,
        parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13,
        parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31,
        parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03,
        parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21,
        parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 : JetAlgebra) = X0, (Dbarψ [] 1 * Dψ [Sum.inl 0] 1 :
      JetAlgebra) = X1, (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 : JetAlgebra) = X2, (Dbarψ [] 1 * Dψ [Sum.inr
      0] 0 : JetAlgebra) = X3, (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 : JetAlgebra) = X4, (Dbarψ [] 1 * Dψ
      [Sum.inr 1] 0 : JetAlgebra) = X5, (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 : JetAlgebra) = X6, (Dbarψ []
      1 * Dψ [Sum.inr 2] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[1,1,1]` (u-family). -/
lemma kleinAvg_u_e111 :
    kleinAvg (Dbarψ [] 1 * Dψ [Sum.inr 0] 1) =
      0 := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11,
        parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23,
        parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01,
        parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13,
        parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31,
        parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03,
        parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21,
        parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 : JetAlgebra) = X0, (Dbarψ [] 1 * Dψ [Sum.inl 0] 1 :
      JetAlgebra) = X1, (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 : JetAlgebra) = X2, (Dbarψ [] 1 * Dψ [Sum.inr
      0] 0 : JetAlgebra) = X3, (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 : JetAlgebra) = X4, (Dbarψ [] 1 * Dψ
      [Sum.inr 1] 0 : JetAlgebra) = X5, (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 : JetAlgebra) = X6, (Dbarψ []
      1 * Dψ [Sum.inr 2] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[2,0,0]` (u-family). -/
lemma kleinAvg_u_e200 :
    kleinAvg (Dbarψ [] 0 * Dψ [Sum.inr 1] 0) =
      0 := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11,
        parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23,
        parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01,
        parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13,
        parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31,
        parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03,
        parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21,
        parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 : JetAlgebra) = X0, (Dbarψ [] 1 * Dψ [Sum.inl 0] 1 :
      JetAlgebra) = X1, (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 : JetAlgebra) = X2, (Dbarψ [] 1 * Dψ [Sum.inr
      0] 0 : JetAlgebra) = X3, (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 : JetAlgebra) = X4, (Dbarψ [] 1 * Dψ
      [Sum.inr 1] 0 : JetAlgebra) = X5, (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 : JetAlgebra) = X6, (Dbarψ []
      1 * Dψ [Sum.inr 2] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[2,0,1]` (u-family). -/
lemma kleinAvg_u_e201 :
    kleinAvg (Dbarψ [] 0 * Dψ [Sum.inr 1] 1) =
      (1/2 : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0) := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11,
        parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23,
        parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01,
        parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13,
        parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31,
        parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03,
        parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21,
        parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 : JetAlgebra) = X0, (Dbarψ [] 1 * Dψ [Sum.inl 0] 1 :
      JetAlgebra) = X1, (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 : JetAlgebra) = X2, (Dbarψ [] 1 * Dψ [Sum.inr
      0] 0 : JetAlgebra) = X3, (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 : JetAlgebra) = X4, (Dbarψ [] 1 * Dψ
      [Sum.inr 1] 0 : JetAlgebra) = X5, (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 : JetAlgebra) = X6, (Dbarψ []
      1 * Dψ [Sum.inr 2] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[2,1,0]` (u-family). -/
lemma kleinAvg_u_e210 :
    kleinAvg (Dbarψ [] 1 * Dψ [Sum.inr 1] 0) =
      (-(1/2) : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0) := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11,
        parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23,
        parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01,
        parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13,
        parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31,
        parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03,
        parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21,
        parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 : JetAlgebra) = X0, (Dbarψ [] 1 * Dψ [Sum.inl 0] 1 :
      JetAlgebra) = X1, (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 : JetAlgebra) = X2, (Dbarψ [] 1 * Dψ [Sum.inr
      0] 0 : JetAlgebra) = X3, (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 : JetAlgebra) = X4, (Dbarψ [] 1 * Dψ
      [Sum.inr 1] 0 : JetAlgebra) = X5, (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 : JetAlgebra) = X6, (Dbarψ []
      1 * Dψ [Sum.inr 2] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[2,1,1]` (u-family). -/
lemma kleinAvg_u_e211 :
    kleinAvg (Dbarψ [] 1 * Dψ [Sum.inr 1] 1) =
      0 := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11,
        parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23,
        parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01,
        parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13,
        parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31,
        parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03,
        parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21,
        parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 : JetAlgebra) = X0, (Dbarψ [] 1 * Dψ [Sum.inl 0] 1 :
      JetAlgebra) = X1, (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 : JetAlgebra) = X2, (Dbarψ [] 1 * Dψ [Sum.inr
      0] 0 : JetAlgebra) = X3, (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 : JetAlgebra) = X4, (Dbarψ [] 1 * Dψ
      [Sum.inr 1] 0 : JetAlgebra) = X5, (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 : JetAlgebra) = X6, (Dbarψ []
      1 * Dψ [Sum.inr 2] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[3,0,0]` (u-family). -/
lemma kleinAvg_u_e300 :
    kleinAvg (Dbarψ [] 0 * Dψ [Sum.inr 2] 0) =
      (1/2 : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1) := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11,
        parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23,
        parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01,
        parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13,
        parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31,
        parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03,
        parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21,
        parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 : JetAlgebra) = X0, (Dbarψ [] 1 * Dψ [Sum.inl 0] 1 :
      JetAlgebra) = X1, (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 : JetAlgebra) = X2, (Dbarψ [] 1 * Dψ [Sum.inr
      0] 0 : JetAlgebra) = X3, (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 : JetAlgebra) = X4, (Dbarψ [] 1 * Dψ
      [Sum.inr 1] 0 : JetAlgebra) = X5, (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 : JetAlgebra) = X6, (Dbarψ []
      1 * Dψ [Sum.inr 2] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[3,0,1]` (u-family). -/
lemma kleinAvg_u_e301 :
    kleinAvg (Dbarψ [] 0 * Dψ [Sum.inr 2] 1) =
      0 := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11,
        parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23,
        parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01,
        parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13,
        parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31,
        parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03,
        parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21,
        parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 : JetAlgebra) = X0, (Dbarψ [] 1 * Dψ [Sum.inl 0] 1 :
      JetAlgebra) = X1, (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 : JetAlgebra) = X2, (Dbarψ [] 1 * Dψ [Sum.inr
      0] 0 : JetAlgebra) = X3, (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 : JetAlgebra) = X4, (Dbarψ [] 1 * Dψ
      [Sum.inr 1] 0 : JetAlgebra) = X5, (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 : JetAlgebra) = X6, (Dbarψ []
      1 * Dψ [Sum.inr 2] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[3,1,0]` (u-family). -/
lemma kleinAvg_u_e310 :
    kleinAvg (Dbarψ [] 1 * Dψ [Sum.inr 2] 0) =
      0 := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11,
        parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23,
        parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01,
        parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13,
        parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31,
        parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03,
        parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21,
        parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 : JetAlgebra) = X0, (Dbarψ [] 1 * Dψ [Sum.inl 0] 1 :
      JetAlgebra) = X1, (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 : JetAlgebra) = X2, (Dbarψ [] 1 * Dψ [Sum.inr
      0] 0 : JetAlgebra) = X3, (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 : JetAlgebra) = X4, (Dbarψ [] 1 * Dψ
      [Sum.inr 1] 0 : JetAlgebra) = X5, (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 : JetAlgebra) = X6, (Dbarψ []
      1 * Dψ [Sum.inr 2] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[3,1,1]` (u-family). -/
lemma kleinAvg_u_e311 :
    kleinAvg (Dbarψ [] 1 * Dψ [Sum.inr 2] 1) =
      (-(1/2) : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1) := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11,
        parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23,
        parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01,
        parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13,
        parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31,
        parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03,
        parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21,
        parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 : JetAlgebra) = X0, (Dbarψ [] 1 * Dψ [Sum.inl 0] 1 :
      JetAlgebra) = X1, (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 : JetAlgebra) = X2, (Dbarψ [] 1 * Dψ [Sum.inr
      0] 0 : JetAlgebra) = X3, (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 : JetAlgebra) = X4, (Dbarψ [] 1 * Dψ
      [Sum.inr 1] 0 : JetAlgebra) = X5, (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 : JetAlgebra) = X6, (Dbarψ []
      1 * Dψ [Sum.inr 2] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[0,0,0]` (ubar-family). -/
lemma kleinAvg_ubar_e000 :
    kleinAvg (Dbarψ [Sum.inl 0] 0 * Dψ [] 0) =
      (1/2 : ℂ) • (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11,
        parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23,
        parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01,
        parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13,
        parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31,
        parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03,
        parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21,
        parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 : JetAlgebra) = X0, (Dbarψ [Sum.inl 0] 1 * Dψ [] 1 :
      JetAlgebra) = X1, (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 : JetAlgebra) = X2, (Dbarψ [Sum.inr 0] 1 * Dψ
      [] 0 : JetAlgebra) = X3, (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 : JetAlgebra) = X4, (Dbarψ [Sum.inr 1]
      1 * Dψ [] 0 : JetAlgebra) = X5, (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 : JetAlgebra) = X6, (Dbarψ
      [Sum.inr 2] 1 * Dψ [] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[0,0,1]` (ubar-family). -/
lemma kleinAvg_ubar_e001 :
    kleinAvg (Dbarψ [Sum.inl 0] 0 * Dψ [] 1) =
      0 := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11,
        parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23,
        parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01,
        parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13,
        parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31,
        parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03,
        parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21,
        parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 : JetAlgebra) = X0, (Dbarψ [Sum.inl 0] 1 * Dψ [] 1 :
      JetAlgebra) = X1, (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 : JetAlgebra) = X2, (Dbarψ [Sum.inr 0] 1 * Dψ
      [] 0 : JetAlgebra) = X3, (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 : JetAlgebra) = X4, (Dbarψ [Sum.inr 1]
      1 * Dψ [] 0 : JetAlgebra) = X5, (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 : JetAlgebra) = X6, (Dbarψ
      [Sum.inr 2] 1 * Dψ [] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[0,1,0]` (ubar-family). -/
lemma kleinAvg_ubar_e010 :
    kleinAvg (Dbarψ [Sum.inl 0] 1 * Dψ [] 0) =
      0 := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11,
        parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23,
        parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01,
        parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13,
        parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31,
        parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03,
        parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21,
        parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 : JetAlgebra) = X0, (Dbarψ [Sum.inl 0] 1 * Dψ [] 1 :
      JetAlgebra) = X1, (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 : JetAlgebra) = X2, (Dbarψ [Sum.inr 0] 1 * Dψ
      [] 0 : JetAlgebra) = X3, (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 : JetAlgebra) = X4, (Dbarψ [Sum.inr 1]
      1 * Dψ [] 0 : JetAlgebra) = X5, (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 : JetAlgebra) = X6, (Dbarψ
      [Sum.inr 2] 1 * Dψ [] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[0,1,1]` (ubar-family). -/
lemma kleinAvg_ubar_e011 :
    kleinAvg (Dbarψ [Sum.inl 0] 1 * Dψ [] 1) =
      (1/2 : ℂ) • (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11,
        parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23,
        parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01,
        parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13,
        parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31,
        parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03,
        parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21,
        parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 : JetAlgebra) = X0, (Dbarψ [Sum.inl 0] 1 * Dψ [] 1 :
      JetAlgebra) = X1, (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 : JetAlgebra) = X2, (Dbarψ [Sum.inr 0] 1 * Dψ
      [] 0 : JetAlgebra) = X3, (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 : JetAlgebra) = X4, (Dbarψ [Sum.inr 1]
      1 * Dψ [] 0 : JetAlgebra) = X5, (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 : JetAlgebra) = X6, (Dbarψ
      [Sum.inr 2] 1 * Dψ [] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[1,0,0]` (ubar-family). -/
lemma kleinAvg_ubar_e100 :
    kleinAvg (Dbarψ [Sum.inr 0] 0 * Dψ [] 0) =
      0 := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11,
        parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23,
        parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01,
        parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13,
        parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31,
        parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03,
        parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21,
        parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 : JetAlgebra) = X0, (Dbarψ [Sum.inl 0] 1 * Dψ [] 1 :
      JetAlgebra) = X1, (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 : JetAlgebra) = X2, (Dbarψ [Sum.inr 0] 1 * Dψ
      [] 0 : JetAlgebra) = X3, (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 : JetAlgebra) = X4, (Dbarψ [Sum.inr 1]
      1 * Dψ [] 0 : JetAlgebra) = X5, (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 : JetAlgebra) = X6, (Dbarψ
      [Sum.inr 2] 1 * Dψ [] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[1,0,1]` (ubar-family). -/
lemma kleinAvg_ubar_e101 :
    kleinAvg (Dbarψ [Sum.inr 0] 0 * Dψ [] 1) =
      (1/2 : ℂ) • (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0) := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11,
        parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23,
        parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01,
        parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13,
        parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31,
        parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03,
        parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21,
        parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 : JetAlgebra) = X0, (Dbarψ [Sum.inl 0] 1 * Dψ [] 1 :
      JetAlgebra) = X1, (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 : JetAlgebra) = X2, (Dbarψ [Sum.inr 0] 1 * Dψ
      [] 0 : JetAlgebra) = X3, (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 : JetAlgebra) = X4, (Dbarψ [Sum.inr 1]
      1 * Dψ [] 0 : JetAlgebra) = X5, (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 : JetAlgebra) = X6, (Dbarψ
      [Sum.inr 2] 1 * Dψ [] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[1,1,0]` (ubar-family). -/
lemma kleinAvg_ubar_e110 :
    kleinAvg (Dbarψ [Sum.inr 0] 1 * Dψ [] 0) =
      (1/2 : ℂ) • (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0) := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11,
        parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23,
        parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01,
        parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13,
        parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31,
        parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03,
        parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21,
        parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 : JetAlgebra) = X0, (Dbarψ [Sum.inl 0] 1 * Dψ [] 1 :
      JetAlgebra) = X1, (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 : JetAlgebra) = X2, (Dbarψ [Sum.inr 0] 1 * Dψ
      [] 0 : JetAlgebra) = X3, (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 : JetAlgebra) = X4, (Dbarψ [Sum.inr 1]
      1 * Dψ [] 0 : JetAlgebra) = X5, (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 : JetAlgebra) = X6, (Dbarψ
      [Sum.inr 2] 1 * Dψ [] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[1,1,1]` (ubar-family). -/
lemma kleinAvg_ubar_e111 :
    kleinAvg (Dbarψ [Sum.inr 0] 1 * Dψ [] 1) =
      0 := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11,
        parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23,
        parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01,
        parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13,
        parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31,
        parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03,
        parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21,
        parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 : JetAlgebra) = X0, (Dbarψ [Sum.inl 0] 1 * Dψ [] 1 :
      JetAlgebra) = X1, (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 : JetAlgebra) = X2, (Dbarψ [Sum.inr 0] 1 * Dψ
      [] 0 : JetAlgebra) = X3, (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 : JetAlgebra) = X4, (Dbarψ [Sum.inr 1]
      1 * Dψ [] 0 : JetAlgebra) = X5, (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 : JetAlgebra) = X6, (Dbarψ
      [Sum.inr 2] 1 * Dψ [] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[2,0,0]` (ubar-family). -/
lemma kleinAvg_ubar_e200 :
    kleinAvg (Dbarψ [Sum.inr 1] 0 * Dψ [] 0) =
      0 := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11,
        parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23,
        parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01,
        parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13,
        parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31,
        parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03,
        parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21,
        parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 : JetAlgebra) = X0, (Dbarψ [Sum.inl 0] 1 * Dψ [] 1 :
      JetAlgebra) = X1, (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 : JetAlgebra) = X2, (Dbarψ [Sum.inr 0] 1 * Dψ
      [] 0 : JetAlgebra) = X3, (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 : JetAlgebra) = X4, (Dbarψ [Sum.inr 1]
      1 * Dψ [] 0 : JetAlgebra) = X5, (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 : JetAlgebra) = X6, (Dbarψ
      [Sum.inr 2] 1 * Dψ [] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[2,0,1]` (ubar-family). -/
lemma kleinAvg_ubar_e201 :
    kleinAvg (Dbarψ [Sum.inr 1] 0 * Dψ [] 1) =
      (1/2 : ℂ) • (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0) := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11,
        parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23,
        parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01,
        parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13,
        parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31,
        parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03,
        parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21,
        parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 : JetAlgebra) = X0, (Dbarψ [Sum.inl 0] 1 * Dψ [] 1 :
      JetAlgebra) = X1, (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 : JetAlgebra) = X2, (Dbarψ [Sum.inr 0] 1 * Dψ
      [] 0 : JetAlgebra) = X3, (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 : JetAlgebra) = X4, (Dbarψ [Sum.inr 1]
      1 * Dψ [] 0 : JetAlgebra) = X5, (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 : JetAlgebra) = X6, (Dbarψ
      [Sum.inr 2] 1 * Dψ [] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[2,1,0]` (ubar-family). -/
lemma kleinAvg_ubar_e210 :
    kleinAvg (Dbarψ [Sum.inr 1] 1 * Dψ [] 0) =
      (-(1/2) : ℂ) • (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0) := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11,
        parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23,
        parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01,
        parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13,
        parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31,
        parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03,
        parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21,
        parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 : JetAlgebra) = X0, (Dbarψ [Sum.inl 0] 1 * Dψ [] 1 :
      JetAlgebra) = X1, (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 : JetAlgebra) = X2, (Dbarψ [Sum.inr 0] 1 * Dψ
      [] 0 : JetAlgebra) = X3, (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 : JetAlgebra) = X4, (Dbarψ [Sum.inr 1]
      1 * Dψ [] 0 : JetAlgebra) = X5, (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 : JetAlgebra) = X6, (Dbarψ
      [Sum.inr 2] 1 * Dψ [] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[2,1,1]` (ubar-family). -/
lemma kleinAvg_ubar_e211 :
    kleinAvg (Dbarψ [Sum.inr 1] 1 * Dψ [] 1) =
      0 := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11,
        parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23,
        parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01,
        parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13,
        parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31,
        parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03,
        parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21,
        parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 : JetAlgebra) = X0, (Dbarψ [Sum.inl 0] 1 * Dψ [] 1 :
      JetAlgebra) = X1, (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 : JetAlgebra) = X2, (Dbarψ [Sum.inr 0] 1 * Dψ
      [] 0 : JetAlgebra) = X3, (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 : JetAlgebra) = X4, (Dbarψ [Sum.inr 1]
      1 * Dψ [] 0 : JetAlgebra) = X5, (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 : JetAlgebra) = X6, (Dbarψ
      [Sum.inr 2] 1 * Dψ [] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[3,0,0]` (ubar-family). -/
lemma kleinAvg_ubar_e300 :
    kleinAvg (Dbarψ [Sum.inr 2] 0 * Dψ [] 0) =
      (1/2 : ℂ) • (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1) := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11,
        parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23,
        parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01,
        parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13,
        parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31,
        parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03,
        parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21,
        parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 : JetAlgebra) = X0, (Dbarψ [Sum.inl 0] 1 * Dψ [] 1 :
      JetAlgebra) = X1, (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 : JetAlgebra) = X2, (Dbarψ [Sum.inr 0] 1 * Dψ
      [] 0 : JetAlgebra) = X3, (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 : JetAlgebra) = X4, (Dbarψ [Sum.inr 1]
      1 * Dψ [] 0 : JetAlgebra) = X5, (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 : JetAlgebra) = X6, (Dbarψ
      [Sum.inr 2] 1 * Dψ [] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[3,0,1]` (ubar-family). -/
lemma kleinAvg_ubar_e301 :
    kleinAvg (Dbarψ [Sum.inr 2] 0 * Dψ [] 1) =
      0 := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11,
        parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23,
        parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01,
        parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13,
        parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31,
        parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03,
        parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21,
        parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 : JetAlgebra) = X0, (Dbarψ [Sum.inl 0] 1 * Dψ [] 1 :
      JetAlgebra) = X1, (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 : JetAlgebra) = X2, (Dbarψ [Sum.inr 0] 1 * Dψ
      [] 0 : JetAlgebra) = X3, (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 : JetAlgebra) = X4, (Dbarψ [Sum.inr 1]
      1 * Dψ [] 0 : JetAlgebra) = X5, (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 : JetAlgebra) = X6, (Dbarψ
      [Sum.inr 2] 1 * Dψ [] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[3,1,0]` (ubar-family). -/
lemma kleinAvg_ubar_e310 :
    kleinAvg (Dbarψ [Sum.inr 2] 1 * Dψ [] 0) =
      0 := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11,
        parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23,
        parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01,
        parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13,
        parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31,
        parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03,
        parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21,
        parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 : JetAlgebra) = X0, (Dbarψ [Sum.inl 0] 1 * Dψ [] 1 :
      JetAlgebra) = X1, (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 : JetAlgebra) = X2, (Dbarψ [Sum.inr 0] 1 * Dψ
      [] 0 : JetAlgebra) = X3, (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 : JetAlgebra) = X4, (Dbarψ [Sum.inr 1]
      1 * Dψ [] 0 : JetAlgebra) = X5, (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 : JetAlgebra) = X6, (Dbarψ
      [Sum.inr 2] 1 * Dψ [] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[3,1,1]` (ubar-family). -/
lemma kleinAvg_ubar_e311 :
    kleinAvg (Dbarψ [Sum.inr 2] 1 * Dψ [] 1) =
      (-(1/2) : ℂ) • (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1) := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11,
        parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23,
        parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01,
        parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13,
        parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31,
        parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03,
        parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21,
        parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 : JetAlgebra) = X0, (Dbarψ [Sum.inl 0] 1 * Dψ [] 1 :
      JetAlgebra) = X1, (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 : JetAlgebra) = X2, (Dbarψ [Sum.inr 0] 1 * Dψ
      [] 0 : JetAlgebra) = X3, (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 : JetAlgebra) = X4, (Dbarψ [Sum.inr 1]
      1 * Dψ [] 0 : JetAlgebra) = X5, (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 : JetAlgebra) = X6, (Dbarψ
      [Sum.inr 2] 1 * Dψ [] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
end JetAlgebra

end QED
