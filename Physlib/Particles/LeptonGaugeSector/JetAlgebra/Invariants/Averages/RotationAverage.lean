/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.Invariants.Subgroups.BoostsOnFermionTerms
/-!
# The average over the rotations by `π`

The average `rotationPiAvg` over the Klein four-group of rotations by `π`
defined in `Subgroups/RotationsPi`. Being a finite subgroup it admits an honest
invariant average — the Reynolds operator — unlike the boosts of
`Averages/BoostAverage`.

By the averaging principle of `Invariants/GroupAverage` an invariant element of
the span of a family lies in the span of the averages of that family, so it
suffices to evaluate `rotationPiAvg` on the monomials of `Grading/NeutralSectors`.
Every field strength averages to zero, which already settles the weight-four
sector (`eq_zero_of_mem_chargeCovSpan_four`); the values on the weight-eight
monomials are tabulated in the rest of the file.
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

/-- The average over the rotations by `π`: the mean of the identity and the three
  lifted rotations, an honest average over the Klein four-group (its lift to
  `SL(2,ℂ)` is the quaternion group, which acts through the same four operators on
  the even sectors met here). -/
noncomputable def rotationPiAvg : Module.End ℂ JetAlgebra :=
  (4 : ℂ)⁻¹ • (LinearMap.id + repLorentzGroup rotationPiZ +
    repLorentzGroup rotationPiY + repLorentzGroup rotationPiX)

/-- The rotation average, termwise. -/
lemma rotationPiAvg_apply (v : JetAlgebra) :
    rotationPiAvg v = (4 : ℂ)⁻¹ • (v + repLorentzGroup rotationPiZ v +
      repLorentzGroup rotationPiY v + repLorentzGroup rotationPiX v) := by
  simp only [rotationPiAvg, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.id_apply]

/-- The rotation average fixes every Lorentz-invariant element. Its four weights sum
  to one, so this is the instance of `Representation.weightedSum_apply_of_invariant`
  at the four lifted rotations by `π`. -/
lemma rotationPiAvg_apply_of_invariant {y : JetAlgebra}
    (hinv : ∀ Λ : SL(2,ℂ), repLorentzGroup Λ y = y) : rotationPiAvg y = y := by
  rw [rotationPiAvg_apply, hinv, hinv, hinv]
  module

/-- The averaging principle for the rotation average: a Lorentz-invariant element of
  the span of a family lies in the span of the rotation averages of that family.
  This is `Submodule.mem_span_range_of_apply_eq_self` for `rotationPiAvg`. -/
lemma mem_span_range_rotationPiAvg {ι : Type} {v : ι → JetAlgebra} {y : JetAlgebra}
    (hy : y ∈ Submodule.span ℂ (Set.range v))
    (hinv : ∀ Λ : SL(2,ℂ), repLorentzGroup Λ y = y) :
    y ∈ Submodule.span ℂ (Set.range fun i => rotationPiAvg (v i)) :=
  Submodule.mem_span_range_of_apply_eq_self hy (rotationPiAvg_apply_of_invariant hinv)

set_option maxHeartbeats 2000000 in
/-- The rotation average annihilates every field strength: `F_{μμ}` vanishes, and for
  `μ ≠ ν` the pair `F_{μν}` is odd under two of the three rotations by `π`, so the
  four signs cancel. -/
lemma rotationPiAvg_fieldStrengthDeriv_nil (μ ν : Fin 1 ⊕ Fin 3) :
    rotationPiAvg (fieldStrengthDeriv {} μ ν) = 0 := by
  rw [rotationPiAvg_apply]
  rcases eq_or_ne μ ν with hp | hp
  · rw [hp, fieldStrengthDeriv_self]
    simp
  · rw [repLorentzGroup_diag_fieldStrengthDeriv toLorentzGroup_rotationPiZ,
      repLorentzGroup_diag_fieldStrengthDeriv toLorentzGroup_rotationPiY,
      repLorentzGroup_diag_fieldStrengthDeriv toLorentzGroup_rotationPiX]
    have hs : (1 : ℂ) + ((rotationPiSignZ μ * rotationPiSignZ ν : ℝ) : ℂ) +
        ((rotationPiSignY μ * rotationPiSignY ν : ℝ) : ℂ) +
        ((rotationPiSignX μ * rotationPiSignX ν : ℝ) : ℂ) = 0 := by
      rcases μ with μ | μ <;> rcases ν with ν | ν <;>
        first
          | (exact absurd rfl (by simpa using hp))
          | (fin_cases μ <;> fin_cases ν <;>
              simp_all [rotationPiSignZ, rotationPiSignY, rotationPiSignX] <;>
              norm_num [Complex.ext_iff] <;> ring)
    have hcomb : ∀ (a b c : ℂ) (x : JetAlgebra),
        x + a • x + b • x + c • x = (1 + a + b + c) • x := by
      intro a b c x
      module
    rw [hcomb, hs, zero_smul, smul_zero]

/-- No Lorentz invariant of mass weight four: an invariant combination of the
  field strengths `F_{μν}` lies, by the averaging principle, in the span of their
  rotation averages, and each of those vanishes. -/
lemma eq_zero_of_mem_chargeCovSpan_four {y : JetAlgebra}
    (hy : y ∈ chargeCovSpan 4 0)
    (hinv : ∀ Λ : SL(2,ℂ), repLorentzGroup Λ y = y) : y = 0 := by
  have h := mem_span_range_rotationPiAvg (chargeCovSpan_four_le hy) hinv
  have hle : Submodule.span ℂ (Set.range fun p : (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) =>
      rotationPiAvg (fieldStrengthDeriv {} p.1 p.2)) ≤ ⊥ := by
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    simpa using rotationPiAvg_fieldStrengthDeriv_nil p.1 p.2
  exact (Submodule.mem_bot ℂ).mp (hle h)


set_option maxHeartbeats 2000000 in
/-- The rotation average acts diagonally on products of two field strengths, by
  the average of the four parity signs. -/
lemma rotationPiAvg_fieldStrengthDeriv_nil_mul (a b c d : Fin 1 ⊕ Fin 3) :
    rotationPiAvg (fieldStrengthDeriv {} a b * fieldStrengthDeriv {} c d) =
      (((1 + rotationPiSignZ a * rotationPiSignZ b * (rotationPiSignZ c * rotationPiSignZ d) +
        rotationPiSignY a * rotationPiSignY b * (rotationPiSignY c * rotationPiSignY d) +
        rotationPiSignX a * rotationPiSignX b * (rotationPiSignX c * rotationPiSignX d)) / 4 : ℝ) : ℂ) •
        (fieldStrengthDeriv {} a b * fieldStrengthDeriv {} c d) := by
  rw [rotationPiAvg_apply]
  simp only [repLorentzGroup_apply_mul,
    repLorentzGroup_diag_fieldStrengthDeriv toLorentzGroup_rotationPiZ,
    repLorentzGroup_diag_fieldStrengthDeriv toLorentzGroup_rotationPiY,
    repLorentzGroup_diag_fieldStrengthDeriv toLorentzGroup_rotationPiX,
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

/-- The rotation average acts diagonally on the second-derivative field
  strengths. -/
lemma rotationPiAvg_fieldStrengthDeriv_pair (r t a b : Fin 1 ⊕ Fin 3) :
    rotationPiAvg (fieldStrengthDeriv {r, t} a b) =
      (((1 + rotationPiSignZ r * (rotationPiSignZ t * (rotationPiSignZ a * rotationPiSignZ b)) +
        rotationPiSignY r * (rotationPiSignY t * (rotationPiSignY a * rotationPiSignY b)) +
        rotationPiSignX r * (rotationPiSignX t * (rotationPiSignX a * rotationPiSignX b))) / 4 : ℝ) : ℂ) •
        fieldStrengthDeriv {r, t} a b := by
  rw [rotationPiAvg_apply,
    repLorentzGroup_diag_fieldStrengthDeriv_pair toLorentzGroup_rotationPiZ,
    repLorentzGroup_diag_fieldStrengthDeriv_pair toLorentzGroup_rotationPiY,
    repLorentzGroup_diag_fieldStrengthDeriv_pair toLorentzGroup_rotationPiX]
  push_cast
  module

set_option maxHeartbeats 4000000 in
/-- The rotation average of the fermion pair monomial `e[0,0,0]` (u-family). -/
lemma rotationPiAvg_u_e000 :
    rotationPiAvg (Dbarψ [] 0 * Dψ [Sum.inl 0] 0) =
      (1/2 : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) := by
  rw [rotationPiAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    rotationPiZ_inv_coe, rotationPiY_inv_coe, rotationPiX_inv_coe,
    rotationPiMatZ_00, rotationPiMatZ_01, rotationPiMatZ_02, rotationPiMatZ_03, rotationPiMatZ_10, rotationPiMatZ_11,
        rotationPiMatZ_12, rotationPiMatZ_13, rotationPiMatZ_20, rotationPiMatZ_21, rotationPiMatZ_22, rotationPiMatZ_23,
        rotationPiMatZ_30, rotationPiMatZ_31, rotationPiMatZ_32, rotationPiMatZ_33, rotationPiMatX_00, rotationPiMatX_01,
        rotationPiMatX_02, rotationPiMatX_03, rotationPiMatX_10, rotationPiMatX_11, rotationPiMatX_12, rotationPiMatX_13,
        rotationPiMatX_20, rotationPiMatX_21, rotationPiMatX_22, rotationPiMatX_23, rotationPiMatX_30, rotationPiMatX_31,
        rotationPiMatX_32, rotationPiMatX_33, rotationPiMatY_00, rotationPiMatY_01, rotationPiMatY_02, rotationPiMatY_03,
        rotationPiMatY_10, rotationPiMatY_11, rotationPiMatY_12, rotationPiMatY_13, rotationPiMatY_20, rotationPiMatY_21,
        rotationPiMatY_22, rotationPiMatY_23, rotationPiMatY_30, rotationPiMatY_31, rotationPiMatY_32, rotationPiMatY_33,
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
/-- The rotation average of the fermion pair monomial `e[0,0,1]` (u-family). -/
lemma rotationPiAvg_u_e001 :
    rotationPiAvg (Dbarψ [] 0 * Dψ [Sum.inl 0] 1) =
      0 := by
  rw [rotationPiAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    rotationPiZ_inv_coe, rotationPiY_inv_coe, rotationPiX_inv_coe,
    rotationPiMatZ_00, rotationPiMatZ_01, rotationPiMatZ_02, rotationPiMatZ_03, rotationPiMatZ_10, rotationPiMatZ_11,
        rotationPiMatZ_12, rotationPiMatZ_13, rotationPiMatZ_20, rotationPiMatZ_21, rotationPiMatZ_22, rotationPiMatZ_23,
        rotationPiMatZ_30, rotationPiMatZ_31, rotationPiMatZ_32, rotationPiMatZ_33, rotationPiMatX_00, rotationPiMatX_01,
        rotationPiMatX_02, rotationPiMatX_03, rotationPiMatX_10, rotationPiMatX_11, rotationPiMatX_12, rotationPiMatX_13,
        rotationPiMatX_20, rotationPiMatX_21, rotationPiMatX_22, rotationPiMatX_23, rotationPiMatX_30, rotationPiMatX_31,
        rotationPiMatX_32, rotationPiMatX_33, rotationPiMatY_00, rotationPiMatY_01, rotationPiMatY_02, rotationPiMatY_03,
        rotationPiMatY_10, rotationPiMatY_11, rotationPiMatY_12, rotationPiMatY_13, rotationPiMatY_20, rotationPiMatY_21,
        rotationPiMatY_22, rotationPiMatY_23, rotationPiMatY_30, rotationPiMatY_31, rotationPiMatY_32, rotationPiMatY_33,
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
/-- The rotation average of the fermion pair monomial `e[0,1,0]` (u-family). -/
lemma rotationPiAvg_u_e010 :
    rotationPiAvg (Dbarψ [] 1 * Dψ [Sum.inl 0] 0) =
      0 := by
  rw [rotationPiAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    rotationPiZ_inv_coe, rotationPiY_inv_coe, rotationPiX_inv_coe,
    rotationPiMatZ_00, rotationPiMatZ_01, rotationPiMatZ_02, rotationPiMatZ_03, rotationPiMatZ_10, rotationPiMatZ_11,
        rotationPiMatZ_12, rotationPiMatZ_13, rotationPiMatZ_20, rotationPiMatZ_21, rotationPiMatZ_22, rotationPiMatZ_23,
        rotationPiMatZ_30, rotationPiMatZ_31, rotationPiMatZ_32, rotationPiMatZ_33, rotationPiMatX_00, rotationPiMatX_01,
        rotationPiMatX_02, rotationPiMatX_03, rotationPiMatX_10, rotationPiMatX_11, rotationPiMatX_12, rotationPiMatX_13,
        rotationPiMatX_20, rotationPiMatX_21, rotationPiMatX_22, rotationPiMatX_23, rotationPiMatX_30, rotationPiMatX_31,
        rotationPiMatX_32, rotationPiMatX_33, rotationPiMatY_00, rotationPiMatY_01, rotationPiMatY_02, rotationPiMatY_03,
        rotationPiMatY_10, rotationPiMatY_11, rotationPiMatY_12, rotationPiMatY_13, rotationPiMatY_20, rotationPiMatY_21,
        rotationPiMatY_22, rotationPiMatY_23, rotationPiMatY_30, rotationPiMatY_31, rotationPiMatY_32, rotationPiMatY_33,
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
/-- The rotation average of the fermion pair monomial `e[0,1,1]` (u-family). -/
lemma rotationPiAvg_u_e011 :
    rotationPiAvg (Dbarψ [] 1 * Dψ [Sum.inl 0] 1) =
      (1/2 : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) := by
  rw [rotationPiAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    rotationPiZ_inv_coe, rotationPiY_inv_coe, rotationPiX_inv_coe,
    rotationPiMatZ_00, rotationPiMatZ_01, rotationPiMatZ_02, rotationPiMatZ_03, rotationPiMatZ_10, rotationPiMatZ_11,
        rotationPiMatZ_12, rotationPiMatZ_13, rotationPiMatZ_20, rotationPiMatZ_21, rotationPiMatZ_22, rotationPiMatZ_23,
        rotationPiMatZ_30, rotationPiMatZ_31, rotationPiMatZ_32, rotationPiMatZ_33, rotationPiMatX_00, rotationPiMatX_01,
        rotationPiMatX_02, rotationPiMatX_03, rotationPiMatX_10, rotationPiMatX_11, rotationPiMatX_12, rotationPiMatX_13,
        rotationPiMatX_20, rotationPiMatX_21, rotationPiMatX_22, rotationPiMatX_23, rotationPiMatX_30, rotationPiMatX_31,
        rotationPiMatX_32, rotationPiMatX_33, rotationPiMatY_00, rotationPiMatY_01, rotationPiMatY_02, rotationPiMatY_03,
        rotationPiMatY_10, rotationPiMatY_11, rotationPiMatY_12, rotationPiMatY_13, rotationPiMatY_20, rotationPiMatY_21,
        rotationPiMatY_22, rotationPiMatY_23, rotationPiMatY_30, rotationPiMatY_31, rotationPiMatY_32, rotationPiMatY_33,
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
/-- The rotation average of the fermion pair monomial `e[1,0,0]` (u-family). -/
lemma rotationPiAvg_u_e100 :
    rotationPiAvg (Dbarψ [] 0 * Dψ [Sum.inr 0] 0) =
      0 := by
  rw [rotationPiAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    rotationPiZ_inv_coe, rotationPiY_inv_coe, rotationPiX_inv_coe,
    rotationPiMatZ_00, rotationPiMatZ_01, rotationPiMatZ_02, rotationPiMatZ_03, rotationPiMatZ_10, rotationPiMatZ_11,
        rotationPiMatZ_12, rotationPiMatZ_13, rotationPiMatZ_20, rotationPiMatZ_21, rotationPiMatZ_22, rotationPiMatZ_23,
        rotationPiMatZ_30, rotationPiMatZ_31, rotationPiMatZ_32, rotationPiMatZ_33, rotationPiMatX_00, rotationPiMatX_01,
        rotationPiMatX_02, rotationPiMatX_03, rotationPiMatX_10, rotationPiMatX_11, rotationPiMatX_12, rotationPiMatX_13,
        rotationPiMatX_20, rotationPiMatX_21, rotationPiMatX_22, rotationPiMatX_23, rotationPiMatX_30, rotationPiMatX_31,
        rotationPiMatX_32, rotationPiMatX_33, rotationPiMatY_00, rotationPiMatY_01, rotationPiMatY_02, rotationPiMatY_03,
        rotationPiMatY_10, rotationPiMatY_11, rotationPiMatY_12, rotationPiMatY_13, rotationPiMatY_20, rotationPiMatY_21,
        rotationPiMatY_22, rotationPiMatY_23, rotationPiMatY_30, rotationPiMatY_31, rotationPiMatY_32, rotationPiMatY_33,
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
/-- The rotation average of the fermion pair monomial `e[1,0,1]` (u-family). -/
lemma rotationPiAvg_u_e101 :
    rotationPiAvg (Dbarψ [] 0 * Dψ [Sum.inr 0] 1) =
      (1/2 : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0) := by
  rw [rotationPiAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    rotationPiZ_inv_coe, rotationPiY_inv_coe, rotationPiX_inv_coe,
    rotationPiMatZ_00, rotationPiMatZ_01, rotationPiMatZ_02, rotationPiMatZ_03, rotationPiMatZ_10, rotationPiMatZ_11,
        rotationPiMatZ_12, rotationPiMatZ_13, rotationPiMatZ_20, rotationPiMatZ_21, rotationPiMatZ_22, rotationPiMatZ_23,
        rotationPiMatZ_30, rotationPiMatZ_31, rotationPiMatZ_32, rotationPiMatZ_33, rotationPiMatX_00, rotationPiMatX_01,
        rotationPiMatX_02, rotationPiMatX_03, rotationPiMatX_10, rotationPiMatX_11, rotationPiMatX_12, rotationPiMatX_13,
        rotationPiMatX_20, rotationPiMatX_21, rotationPiMatX_22, rotationPiMatX_23, rotationPiMatX_30, rotationPiMatX_31,
        rotationPiMatX_32, rotationPiMatX_33, rotationPiMatY_00, rotationPiMatY_01, rotationPiMatY_02, rotationPiMatY_03,
        rotationPiMatY_10, rotationPiMatY_11, rotationPiMatY_12, rotationPiMatY_13, rotationPiMatY_20, rotationPiMatY_21,
        rotationPiMatY_22, rotationPiMatY_23, rotationPiMatY_30, rotationPiMatY_31, rotationPiMatY_32, rotationPiMatY_33,
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
/-- The rotation average of the fermion pair monomial `e[1,1,0]` (u-family). -/
lemma rotationPiAvg_u_e110 :
    rotationPiAvg (Dbarψ [] 1 * Dψ [Sum.inr 0] 0) =
      (1/2 : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0) := by
  rw [rotationPiAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    rotationPiZ_inv_coe, rotationPiY_inv_coe, rotationPiX_inv_coe,
    rotationPiMatZ_00, rotationPiMatZ_01, rotationPiMatZ_02, rotationPiMatZ_03, rotationPiMatZ_10, rotationPiMatZ_11,
        rotationPiMatZ_12, rotationPiMatZ_13, rotationPiMatZ_20, rotationPiMatZ_21, rotationPiMatZ_22, rotationPiMatZ_23,
        rotationPiMatZ_30, rotationPiMatZ_31, rotationPiMatZ_32, rotationPiMatZ_33, rotationPiMatX_00, rotationPiMatX_01,
        rotationPiMatX_02, rotationPiMatX_03, rotationPiMatX_10, rotationPiMatX_11, rotationPiMatX_12, rotationPiMatX_13,
        rotationPiMatX_20, rotationPiMatX_21, rotationPiMatX_22, rotationPiMatX_23, rotationPiMatX_30, rotationPiMatX_31,
        rotationPiMatX_32, rotationPiMatX_33, rotationPiMatY_00, rotationPiMatY_01, rotationPiMatY_02, rotationPiMatY_03,
        rotationPiMatY_10, rotationPiMatY_11, rotationPiMatY_12, rotationPiMatY_13, rotationPiMatY_20, rotationPiMatY_21,
        rotationPiMatY_22, rotationPiMatY_23, rotationPiMatY_30, rotationPiMatY_31, rotationPiMatY_32, rotationPiMatY_33,
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
/-- The rotation average of the fermion pair monomial `e[1,1,1]` (u-family). -/
lemma rotationPiAvg_u_e111 :
    rotationPiAvg (Dbarψ [] 1 * Dψ [Sum.inr 0] 1) =
      0 := by
  rw [rotationPiAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    rotationPiZ_inv_coe, rotationPiY_inv_coe, rotationPiX_inv_coe,
    rotationPiMatZ_00, rotationPiMatZ_01, rotationPiMatZ_02, rotationPiMatZ_03, rotationPiMatZ_10, rotationPiMatZ_11,
        rotationPiMatZ_12, rotationPiMatZ_13, rotationPiMatZ_20, rotationPiMatZ_21, rotationPiMatZ_22, rotationPiMatZ_23,
        rotationPiMatZ_30, rotationPiMatZ_31, rotationPiMatZ_32, rotationPiMatZ_33, rotationPiMatX_00, rotationPiMatX_01,
        rotationPiMatX_02, rotationPiMatX_03, rotationPiMatX_10, rotationPiMatX_11, rotationPiMatX_12, rotationPiMatX_13,
        rotationPiMatX_20, rotationPiMatX_21, rotationPiMatX_22, rotationPiMatX_23, rotationPiMatX_30, rotationPiMatX_31,
        rotationPiMatX_32, rotationPiMatX_33, rotationPiMatY_00, rotationPiMatY_01, rotationPiMatY_02, rotationPiMatY_03,
        rotationPiMatY_10, rotationPiMatY_11, rotationPiMatY_12, rotationPiMatY_13, rotationPiMatY_20, rotationPiMatY_21,
        rotationPiMatY_22, rotationPiMatY_23, rotationPiMatY_30, rotationPiMatY_31, rotationPiMatY_32, rotationPiMatY_33,
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
/-- The rotation average of the fermion pair monomial `e[2,0,0]` (u-family). -/
lemma rotationPiAvg_u_e200 :
    rotationPiAvg (Dbarψ [] 0 * Dψ [Sum.inr 1] 0) =
      0 := by
  rw [rotationPiAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    rotationPiZ_inv_coe, rotationPiY_inv_coe, rotationPiX_inv_coe,
    rotationPiMatZ_00, rotationPiMatZ_01, rotationPiMatZ_02, rotationPiMatZ_03, rotationPiMatZ_10, rotationPiMatZ_11,
        rotationPiMatZ_12, rotationPiMatZ_13, rotationPiMatZ_20, rotationPiMatZ_21, rotationPiMatZ_22, rotationPiMatZ_23,
        rotationPiMatZ_30, rotationPiMatZ_31, rotationPiMatZ_32, rotationPiMatZ_33, rotationPiMatX_00, rotationPiMatX_01,
        rotationPiMatX_02, rotationPiMatX_03, rotationPiMatX_10, rotationPiMatX_11, rotationPiMatX_12, rotationPiMatX_13,
        rotationPiMatX_20, rotationPiMatX_21, rotationPiMatX_22, rotationPiMatX_23, rotationPiMatX_30, rotationPiMatX_31,
        rotationPiMatX_32, rotationPiMatX_33, rotationPiMatY_00, rotationPiMatY_01, rotationPiMatY_02, rotationPiMatY_03,
        rotationPiMatY_10, rotationPiMatY_11, rotationPiMatY_12, rotationPiMatY_13, rotationPiMatY_20, rotationPiMatY_21,
        rotationPiMatY_22, rotationPiMatY_23, rotationPiMatY_30, rotationPiMatY_31, rotationPiMatY_32, rotationPiMatY_33,
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
/-- The rotation average of the fermion pair monomial `e[2,0,1]` (u-family). -/
lemma rotationPiAvg_u_e201 :
    rotationPiAvg (Dbarψ [] 0 * Dψ [Sum.inr 1] 1) =
      (1/2 : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0) := by
  rw [rotationPiAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    rotationPiZ_inv_coe, rotationPiY_inv_coe, rotationPiX_inv_coe,
    rotationPiMatZ_00, rotationPiMatZ_01, rotationPiMatZ_02, rotationPiMatZ_03, rotationPiMatZ_10, rotationPiMatZ_11,
        rotationPiMatZ_12, rotationPiMatZ_13, rotationPiMatZ_20, rotationPiMatZ_21, rotationPiMatZ_22, rotationPiMatZ_23,
        rotationPiMatZ_30, rotationPiMatZ_31, rotationPiMatZ_32, rotationPiMatZ_33, rotationPiMatX_00, rotationPiMatX_01,
        rotationPiMatX_02, rotationPiMatX_03, rotationPiMatX_10, rotationPiMatX_11, rotationPiMatX_12, rotationPiMatX_13,
        rotationPiMatX_20, rotationPiMatX_21, rotationPiMatX_22, rotationPiMatX_23, rotationPiMatX_30, rotationPiMatX_31,
        rotationPiMatX_32, rotationPiMatX_33, rotationPiMatY_00, rotationPiMatY_01, rotationPiMatY_02, rotationPiMatY_03,
        rotationPiMatY_10, rotationPiMatY_11, rotationPiMatY_12, rotationPiMatY_13, rotationPiMatY_20, rotationPiMatY_21,
        rotationPiMatY_22, rotationPiMatY_23, rotationPiMatY_30, rotationPiMatY_31, rotationPiMatY_32, rotationPiMatY_33,
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
/-- The rotation average of the fermion pair monomial `e[2,1,0]` (u-family). -/
lemma rotationPiAvg_u_e210 :
    rotationPiAvg (Dbarψ [] 1 * Dψ [Sum.inr 1] 0) =
      (-(1/2) : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0) := by
  rw [rotationPiAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    rotationPiZ_inv_coe, rotationPiY_inv_coe, rotationPiX_inv_coe,
    rotationPiMatZ_00, rotationPiMatZ_01, rotationPiMatZ_02, rotationPiMatZ_03, rotationPiMatZ_10, rotationPiMatZ_11,
        rotationPiMatZ_12, rotationPiMatZ_13, rotationPiMatZ_20, rotationPiMatZ_21, rotationPiMatZ_22, rotationPiMatZ_23,
        rotationPiMatZ_30, rotationPiMatZ_31, rotationPiMatZ_32, rotationPiMatZ_33, rotationPiMatX_00, rotationPiMatX_01,
        rotationPiMatX_02, rotationPiMatX_03, rotationPiMatX_10, rotationPiMatX_11, rotationPiMatX_12, rotationPiMatX_13,
        rotationPiMatX_20, rotationPiMatX_21, rotationPiMatX_22, rotationPiMatX_23, rotationPiMatX_30, rotationPiMatX_31,
        rotationPiMatX_32, rotationPiMatX_33, rotationPiMatY_00, rotationPiMatY_01, rotationPiMatY_02, rotationPiMatY_03,
        rotationPiMatY_10, rotationPiMatY_11, rotationPiMatY_12, rotationPiMatY_13, rotationPiMatY_20, rotationPiMatY_21,
        rotationPiMatY_22, rotationPiMatY_23, rotationPiMatY_30, rotationPiMatY_31, rotationPiMatY_32, rotationPiMatY_33,
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
/-- The rotation average of the fermion pair monomial `e[2,1,1]` (u-family). -/
lemma rotationPiAvg_u_e211 :
    rotationPiAvg (Dbarψ [] 1 * Dψ [Sum.inr 1] 1) =
      0 := by
  rw [rotationPiAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    rotationPiZ_inv_coe, rotationPiY_inv_coe, rotationPiX_inv_coe,
    rotationPiMatZ_00, rotationPiMatZ_01, rotationPiMatZ_02, rotationPiMatZ_03, rotationPiMatZ_10, rotationPiMatZ_11,
        rotationPiMatZ_12, rotationPiMatZ_13, rotationPiMatZ_20, rotationPiMatZ_21, rotationPiMatZ_22, rotationPiMatZ_23,
        rotationPiMatZ_30, rotationPiMatZ_31, rotationPiMatZ_32, rotationPiMatZ_33, rotationPiMatX_00, rotationPiMatX_01,
        rotationPiMatX_02, rotationPiMatX_03, rotationPiMatX_10, rotationPiMatX_11, rotationPiMatX_12, rotationPiMatX_13,
        rotationPiMatX_20, rotationPiMatX_21, rotationPiMatX_22, rotationPiMatX_23, rotationPiMatX_30, rotationPiMatX_31,
        rotationPiMatX_32, rotationPiMatX_33, rotationPiMatY_00, rotationPiMatY_01, rotationPiMatY_02, rotationPiMatY_03,
        rotationPiMatY_10, rotationPiMatY_11, rotationPiMatY_12, rotationPiMatY_13, rotationPiMatY_20, rotationPiMatY_21,
        rotationPiMatY_22, rotationPiMatY_23, rotationPiMatY_30, rotationPiMatY_31, rotationPiMatY_32, rotationPiMatY_33,
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
/-- The rotation average of the fermion pair monomial `e[3,0,0]` (u-family). -/
lemma rotationPiAvg_u_e300 :
    rotationPiAvg (Dbarψ [] 0 * Dψ [Sum.inr 2] 0) =
      (1/2 : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1) := by
  rw [rotationPiAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    rotationPiZ_inv_coe, rotationPiY_inv_coe, rotationPiX_inv_coe,
    rotationPiMatZ_00, rotationPiMatZ_01, rotationPiMatZ_02, rotationPiMatZ_03, rotationPiMatZ_10, rotationPiMatZ_11,
        rotationPiMatZ_12, rotationPiMatZ_13, rotationPiMatZ_20, rotationPiMatZ_21, rotationPiMatZ_22, rotationPiMatZ_23,
        rotationPiMatZ_30, rotationPiMatZ_31, rotationPiMatZ_32, rotationPiMatZ_33, rotationPiMatX_00, rotationPiMatX_01,
        rotationPiMatX_02, rotationPiMatX_03, rotationPiMatX_10, rotationPiMatX_11, rotationPiMatX_12, rotationPiMatX_13,
        rotationPiMatX_20, rotationPiMatX_21, rotationPiMatX_22, rotationPiMatX_23, rotationPiMatX_30, rotationPiMatX_31,
        rotationPiMatX_32, rotationPiMatX_33, rotationPiMatY_00, rotationPiMatY_01, rotationPiMatY_02, rotationPiMatY_03,
        rotationPiMatY_10, rotationPiMatY_11, rotationPiMatY_12, rotationPiMatY_13, rotationPiMatY_20, rotationPiMatY_21,
        rotationPiMatY_22, rotationPiMatY_23, rotationPiMatY_30, rotationPiMatY_31, rotationPiMatY_32, rotationPiMatY_33,
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
/-- The rotation average of the fermion pair monomial `e[3,0,1]` (u-family). -/
lemma rotationPiAvg_u_e301 :
    rotationPiAvg (Dbarψ [] 0 * Dψ [Sum.inr 2] 1) =
      0 := by
  rw [rotationPiAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    rotationPiZ_inv_coe, rotationPiY_inv_coe, rotationPiX_inv_coe,
    rotationPiMatZ_00, rotationPiMatZ_01, rotationPiMatZ_02, rotationPiMatZ_03, rotationPiMatZ_10, rotationPiMatZ_11,
        rotationPiMatZ_12, rotationPiMatZ_13, rotationPiMatZ_20, rotationPiMatZ_21, rotationPiMatZ_22, rotationPiMatZ_23,
        rotationPiMatZ_30, rotationPiMatZ_31, rotationPiMatZ_32, rotationPiMatZ_33, rotationPiMatX_00, rotationPiMatX_01,
        rotationPiMatX_02, rotationPiMatX_03, rotationPiMatX_10, rotationPiMatX_11, rotationPiMatX_12, rotationPiMatX_13,
        rotationPiMatX_20, rotationPiMatX_21, rotationPiMatX_22, rotationPiMatX_23, rotationPiMatX_30, rotationPiMatX_31,
        rotationPiMatX_32, rotationPiMatX_33, rotationPiMatY_00, rotationPiMatY_01, rotationPiMatY_02, rotationPiMatY_03,
        rotationPiMatY_10, rotationPiMatY_11, rotationPiMatY_12, rotationPiMatY_13, rotationPiMatY_20, rotationPiMatY_21,
        rotationPiMatY_22, rotationPiMatY_23, rotationPiMatY_30, rotationPiMatY_31, rotationPiMatY_32, rotationPiMatY_33,
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
/-- The rotation average of the fermion pair monomial `e[3,1,0]` (u-family). -/
lemma rotationPiAvg_u_e310 :
    rotationPiAvg (Dbarψ [] 1 * Dψ [Sum.inr 2] 0) =
      0 := by
  rw [rotationPiAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    rotationPiZ_inv_coe, rotationPiY_inv_coe, rotationPiX_inv_coe,
    rotationPiMatZ_00, rotationPiMatZ_01, rotationPiMatZ_02, rotationPiMatZ_03, rotationPiMatZ_10, rotationPiMatZ_11,
        rotationPiMatZ_12, rotationPiMatZ_13, rotationPiMatZ_20, rotationPiMatZ_21, rotationPiMatZ_22, rotationPiMatZ_23,
        rotationPiMatZ_30, rotationPiMatZ_31, rotationPiMatZ_32, rotationPiMatZ_33, rotationPiMatX_00, rotationPiMatX_01,
        rotationPiMatX_02, rotationPiMatX_03, rotationPiMatX_10, rotationPiMatX_11, rotationPiMatX_12, rotationPiMatX_13,
        rotationPiMatX_20, rotationPiMatX_21, rotationPiMatX_22, rotationPiMatX_23, rotationPiMatX_30, rotationPiMatX_31,
        rotationPiMatX_32, rotationPiMatX_33, rotationPiMatY_00, rotationPiMatY_01, rotationPiMatY_02, rotationPiMatY_03,
        rotationPiMatY_10, rotationPiMatY_11, rotationPiMatY_12, rotationPiMatY_13, rotationPiMatY_20, rotationPiMatY_21,
        rotationPiMatY_22, rotationPiMatY_23, rotationPiMatY_30, rotationPiMatY_31, rotationPiMatY_32, rotationPiMatY_33,
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
/-- The rotation average of the fermion pair monomial `e[3,1,1]` (u-family). -/
lemma rotationPiAvg_u_e311 :
    rotationPiAvg (Dbarψ [] 1 * Dψ [Sum.inr 2] 1) =
      (-(1/2) : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1) := by
  rw [rotationPiAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    rotationPiZ_inv_coe, rotationPiY_inv_coe, rotationPiX_inv_coe,
    rotationPiMatZ_00, rotationPiMatZ_01, rotationPiMatZ_02, rotationPiMatZ_03, rotationPiMatZ_10, rotationPiMatZ_11,
        rotationPiMatZ_12, rotationPiMatZ_13, rotationPiMatZ_20, rotationPiMatZ_21, rotationPiMatZ_22, rotationPiMatZ_23,
        rotationPiMatZ_30, rotationPiMatZ_31, rotationPiMatZ_32, rotationPiMatZ_33, rotationPiMatX_00, rotationPiMatX_01,
        rotationPiMatX_02, rotationPiMatX_03, rotationPiMatX_10, rotationPiMatX_11, rotationPiMatX_12, rotationPiMatX_13,
        rotationPiMatX_20, rotationPiMatX_21, rotationPiMatX_22, rotationPiMatX_23, rotationPiMatX_30, rotationPiMatX_31,
        rotationPiMatX_32, rotationPiMatX_33, rotationPiMatY_00, rotationPiMatY_01, rotationPiMatY_02, rotationPiMatY_03,
        rotationPiMatY_10, rotationPiMatY_11, rotationPiMatY_12, rotationPiMatY_13, rotationPiMatY_20, rotationPiMatY_21,
        rotationPiMatY_22, rotationPiMatY_23, rotationPiMatY_30, rotationPiMatY_31, rotationPiMatY_32, rotationPiMatY_33,
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
/-- The rotation average of the fermion pair monomial `e[0,0,0]` (ubar-family). -/
lemma rotationPiAvg_ubar_e000 :
    rotationPiAvg (Dbarψ [Sum.inl 0] 0 * Dψ [] 0) =
      (1/2 : ℂ) • (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) := by
  rw [rotationPiAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    rotationPiZ_inv_coe, rotationPiY_inv_coe, rotationPiX_inv_coe,
    rotationPiMatZ_00, rotationPiMatZ_01, rotationPiMatZ_02, rotationPiMatZ_03, rotationPiMatZ_10, rotationPiMatZ_11,
        rotationPiMatZ_12, rotationPiMatZ_13, rotationPiMatZ_20, rotationPiMatZ_21, rotationPiMatZ_22, rotationPiMatZ_23,
        rotationPiMatZ_30, rotationPiMatZ_31, rotationPiMatZ_32, rotationPiMatZ_33, rotationPiMatX_00, rotationPiMatX_01,
        rotationPiMatX_02, rotationPiMatX_03, rotationPiMatX_10, rotationPiMatX_11, rotationPiMatX_12, rotationPiMatX_13,
        rotationPiMatX_20, rotationPiMatX_21, rotationPiMatX_22, rotationPiMatX_23, rotationPiMatX_30, rotationPiMatX_31,
        rotationPiMatX_32, rotationPiMatX_33, rotationPiMatY_00, rotationPiMatY_01, rotationPiMatY_02, rotationPiMatY_03,
        rotationPiMatY_10, rotationPiMatY_11, rotationPiMatY_12, rotationPiMatY_13, rotationPiMatY_20, rotationPiMatY_21,
        rotationPiMatY_22, rotationPiMatY_23, rotationPiMatY_30, rotationPiMatY_31, rotationPiMatY_32, rotationPiMatY_33,
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
/-- The rotation average of the fermion pair monomial `e[0,0,1]` (ubar-family). -/
lemma rotationPiAvg_ubar_e001 :
    rotationPiAvg (Dbarψ [Sum.inl 0] 0 * Dψ [] 1) =
      0 := by
  rw [rotationPiAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    rotationPiZ_inv_coe, rotationPiY_inv_coe, rotationPiX_inv_coe,
    rotationPiMatZ_00, rotationPiMatZ_01, rotationPiMatZ_02, rotationPiMatZ_03, rotationPiMatZ_10, rotationPiMatZ_11,
        rotationPiMatZ_12, rotationPiMatZ_13, rotationPiMatZ_20, rotationPiMatZ_21, rotationPiMatZ_22, rotationPiMatZ_23,
        rotationPiMatZ_30, rotationPiMatZ_31, rotationPiMatZ_32, rotationPiMatZ_33, rotationPiMatX_00, rotationPiMatX_01,
        rotationPiMatX_02, rotationPiMatX_03, rotationPiMatX_10, rotationPiMatX_11, rotationPiMatX_12, rotationPiMatX_13,
        rotationPiMatX_20, rotationPiMatX_21, rotationPiMatX_22, rotationPiMatX_23, rotationPiMatX_30, rotationPiMatX_31,
        rotationPiMatX_32, rotationPiMatX_33, rotationPiMatY_00, rotationPiMatY_01, rotationPiMatY_02, rotationPiMatY_03,
        rotationPiMatY_10, rotationPiMatY_11, rotationPiMatY_12, rotationPiMatY_13, rotationPiMatY_20, rotationPiMatY_21,
        rotationPiMatY_22, rotationPiMatY_23, rotationPiMatY_30, rotationPiMatY_31, rotationPiMatY_32, rotationPiMatY_33,
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
/-- The rotation average of the fermion pair monomial `e[0,1,0]` (ubar-family). -/
lemma rotationPiAvg_ubar_e010 :
    rotationPiAvg (Dbarψ [Sum.inl 0] 1 * Dψ [] 0) =
      0 := by
  rw [rotationPiAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    rotationPiZ_inv_coe, rotationPiY_inv_coe, rotationPiX_inv_coe,
    rotationPiMatZ_00, rotationPiMatZ_01, rotationPiMatZ_02, rotationPiMatZ_03, rotationPiMatZ_10, rotationPiMatZ_11,
        rotationPiMatZ_12, rotationPiMatZ_13, rotationPiMatZ_20, rotationPiMatZ_21, rotationPiMatZ_22, rotationPiMatZ_23,
        rotationPiMatZ_30, rotationPiMatZ_31, rotationPiMatZ_32, rotationPiMatZ_33, rotationPiMatX_00, rotationPiMatX_01,
        rotationPiMatX_02, rotationPiMatX_03, rotationPiMatX_10, rotationPiMatX_11, rotationPiMatX_12, rotationPiMatX_13,
        rotationPiMatX_20, rotationPiMatX_21, rotationPiMatX_22, rotationPiMatX_23, rotationPiMatX_30, rotationPiMatX_31,
        rotationPiMatX_32, rotationPiMatX_33, rotationPiMatY_00, rotationPiMatY_01, rotationPiMatY_02, rotationPiMatY_03,
        rotationPiMatY_10, rotationPiMatY_11, rotationPiMatY_12, rotationPiMatY_13, rotationPiMatY_20, rotationPiMatY_21,
        rotationPiMatY_22, rotationPiMatY_23, rotationPiMatY_30, rotationPiMatY_31, rotationPiMatY_32, rotationPiMatY_33,
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
/-- The rotation average of the fermion pair monomial `e[0,1,1]` (ubar-family). -/
lemma rotationPiAvg_ubar_e011 :
    rotationPiAvg (Dbarψ [Sum.inl 0] 1 * Dψ [] 1) =
      (1/2 : ℂ) • (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) := by
  rw [rotationPiAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    rotationPiZ_inv_coe, rotationPiY_inv_coe, rotationPiX_inv_coe,
    rotationPiMatZ_00, rotationPiMatZ_01, rotationPiMatZ_02, rotationPiMatZ_03, rotationPiMatZ_10, rotationPiMatZ_11,
        rotationPiMatZ_12, rotationPiMatZ_13, rotationPiMatZ_20, rotationPiMatZ_21, rotationPiMatZ_22, rotationPiMatZ_23,
        rotationPiMatZ_30, rotationPiMatZ_31, rotationPiMatZ_32, rotationPiMatZ_33, rotationPiMatX_00, rotationPiMatX_01,
        rotationPiMatX_02, rotationPiMatX_03, rotationPiMatX_10, rotationPiMatX_11, rotationPiMatX_12, rotationPiMatX_13,
        rotationPiMatX_20, rotationPiMatX_21, rotationPiMatX_22, rotationPiMatX_23, rotationPiMatX_30, rotationPiMatX_31,
        rotationPiMatX_32, rotationPiMatX_33, rotationPiMatY_00, rotationPiMatY_01, rotationPiMatY_02, rotationPiMatY_03,
        rotationPiMatY_10, rotationPiMatY_11, rotationPiMatY_12, rotationPiMatY_13, rotationPiMatY_20, rotationPiMatY_21,
        rotationPiMatY_22, rotationPiMatY_23, rotationPiMatY_30, rotationPiMatY_31, rotationPiMatY_32, rotationPiMatY_33,
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
/-- The rotation average of the fermion pair monomial `e[1,0,0]` (ubar-family). -/
lemma rotationPiAvg_ubar_e100 :
    rotationPiAvg (Dbarψ [Sum.inr 0] 0 * Dψ [] 0) =
      0 := by
  rw [rotationPiAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    rotationPiZ_inv_coe, rotationPiY_inv_coe, rotationPiX_inv_coe,
    rotationPiMatZ_00, rotationPiMatZ_01, rotationPiMatZ_02, rotationPiMatZ_03, rotationPiMatZ_10, rotationPiMatZ_11,
        rotationPiMatZ_12, rotationPiMatZ_13, rotationPiMatZ_20, rotationPiMatZ_21, rotationPiMatZ_22, rotationPiMatZ_23,
        rotationPiMatZ_30, rotationPiMatZ_31, rotationPiMatZ_32, rotationPiMatZ_33, rotationPiMatX_00, rotationPiMatX_01,
        rotationPiMatX_02, rotationPiMatX_03, rotationPiMatX_10, rotationPiMatX_11, rotationPiMatX_12, rotationPiMatX_13,
        rotationPiMatX_20, rotationPiMatX_21, rotationPiMatX_22, rotationPiMatX_23, rotationPiMatX_30, rotationPiMatX_31,
        rotationPiMatX_32, rotationPiMatX_33, rotationPiMatY_00, rotationPiMatY_01, rotationPiMatY_02, rotationPiMatY_03,
        rotationPiMatY_10, rotationPiMatY_11, rotationPiMatY_12, rotationPiMatY_13, rotationPiMatY_20, rotationPiMatY_21,
        rotationPiMatY_22, rotationPiMatY_23, rotationPiMatY_30, rotationPiMatY_31, rotationPiMatY_32, rotationPiMatY_33,
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
/-- The rotation average of the fermion pair monomial `e[1,0,1]` (ubar-family). -/
lemma rotationPiAvg_ubar_e101 :
    rotationPiAvg (Dbarψ [Sum.inr 0] 0 * Dψ [] 1) =
      (1/2 : ℂ) • (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0) := by
  rw [rotationPiAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    rotationPiZ_inv_coe, rotationPiY_inv_coe, rotationPiX_inv_coe,
    rotationPiMatZ_00, rotationPiMatZ_01, rotationPiMatZ_02, rotationPiMatZ_03, rotationPiMatZ_10, rotationPiMatZ_11,
        rotationPiMatZ_12, rotationPiMatZ_13, rotationPiMatZ_20, rotationPiMatZ_21, rotationPiMatZ_22, rotationPiMatZ_23,
        rotationPiMatZ_30, rotationPiMatZ_31, rotationPiMatZ_32, rotationPiMatZ_33, rotationPiMatX_00, rotationPiMatX_01,
        rotationPiMatX_02, rotationPiMatX_03, rotationPiMatX_10, rotationPiMatX_11, rotationPiMatX_12, rotationPiMatX_13,
        rotationPiMatX_20, rotationPiMatX_21, rotationPiMatX_22, rotationPiMatX_23, rotationPiMatX_30, rotationPiMatX_31,
        rotationPiMatX_32, rotationPiMatX_33, rotationPiMatY_00, rotationPiMatY_01, rotationPiMatY_02, rotationPiMatY_03,
        rotationPiMatY_10, rotationPiMatY_11, rotationPiMatY_12, rotationPiMatY_13, rotationPiMatY_20, rotationPiMatY_21,
        rotationPiMatY_22, rotationPiMatY_23, rotationPiMatY_30, rotationPiMatY_31, rotationPiMatY_32, rotationPiMatY_33,
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
/-- The rotation average of the fermion pair monomial `e[1,1,0]` (ubar-family). -/
lemma rotationPiAvg_ubar_e110 :
    rotationPiAvg (Dbarψ [Sum.inr 0] 1 * Dψ [] 0) =
      (1/2 : ℂ) • (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0) := by
  rw [rotationPiAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    rotationPiZ_inv_coe, rotationPiY_inv_coe, rotationPiX_inv_coe,
    rotationPiMatZ_00, rotationPiMatZ_01, rotationPiMatZ_02, rotationPiMatZ_03, rotationPiMatZ_10, rotationPiMatZ_11,
        rotationPiMatZ_12, rotationPiMatZ_13, rotationPiMatZ_20, rotationPiMatZ_21, rotationPiMatZ_22, rotationPiMatZ_23,
        rotationPiMatZ_30, rotationPiMatZ_31, rotationPiMatZ_32, rotationPiMatZ_33, rotationPiMatX_00, rotationPiMatX_01,
        rotationPiMatX_02, rotationPiMatX_03, rotationPiMatX_10, rotationPiMatX_11, rotationPiMatX_12, rotationPiMatX_13,
        rotationPiMatX_20, rotationPiMatX_21, rotationPiMatX_22, rotationPiMatX_23, rotationPiMatX_30, rotationPiMatX_31,
        rotationPiMatX_32, rotationPiMatX_33, rotationPiMatY_00, rotationPiMatY_01, rotationPiMatY_02, rotationPiMatY_03,
        rotationPiMatY_10, rotationPiMatY_11, rotationPiMatY_12, rotationPiMatY_13, rotationPiMatY_20, rotationPiMatY_21,
        rotationPiMatY_22, rotationPiMatY_23, rotationPiMatY_30, rotationPiMatY_31, rotationPiMatY_32, rotationPiMatY_33,
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
/-- The rotation average of the fermion pair monomial `e[1,1,1]` (ubar-family). -/
lemma rotationPiAvg_ubar_e111 :
    rotationPiAvg (Dbarψ [Sum.inr 0] 1 * Dψ [] 1) =
      0 := by
  rw [rotationPiAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    rotationPiZ_inv_coe, rotationPiY_inv_coe, rotationPiX_inv_coe,
    rotationPiMatZ_00, rotationPiMatZ_01, rotationPiMatZ_02, rotationPiMatZ_03, rotationPiMatZ_10, rotationPiMatZ_11,
        rotationPiMatZ_12, rotationPiMatZ_13, rotationPiMatZ_20, rotationPiMatZ_21, rotationPiMatZ_22, rotationPiMatZ_23,
        rotationPiMatZ_30, rotationPiMatZ_31, rotationPiMatZ_32, rotationPiMatZ_33, rotationPiMatX_00, rotationPiMatX_01,
        rotationPiMatX_02, rotationPiMatX_03, rotationPiMatX_10, rotationPiMatX_11, rotationPiMatX_12, rotationPiMatX_13,
        rotationPiMatX_20, rotationPiMatX_21, rotationPiMatX_22, rotationPiMatX_23, rotationPiMatX_30, rotationPiMatX_31,
        rotationPiMatX_32, rotationPiMatX_33, rotationPiMatY_00, rotationPiMatY_01, rotationPiMatY_02, rotationPiMatY_03,
        rotationPiMatY_10, rotationPiMatY_11, rotationPiMatY_12, rotationPiMatY_13, rotationPiMatY_20, rotationPiMatY_21,
        rotationPiMatY_22, rotationPiMatY_23, rotationPiMatY_30, rotationPiMatY_31, rotationPiMatY_32, rotationPiMatY_33,
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
/-- The rotation average of the fermion pair monomial `e[2,0,0]` (ubar-family). -/
lemma rotationPiAvg_ubar_e200 :
    rotationPiAvg (Dbarψ [Sum.inr 1] 0 * Dψ [] 0) =
      0 := by
  rw [rotationPiAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    rotationPiZ_inv_coe, rotationPiY_inv_coe, rotationPiX_inv_coe,
    rotationPiMatZ_00, rotationPiMatZ_01, rotationPiMatZ_02, rotationPiMatZ_03, rotationPiMatZ_10, rotationPiMatZ_11,
        rotationPiMatZ_12, rotationPiMatZ_13, rotationPiMatZ_20, rotationPiMatZ_21, rotationPiMatZ_22, rotationPiMatZ_23,
        rotationPiMatZ_30, rotationPiMatZ_31, rotationPiMatZ_32, rotationPiMatZ_33, rotationPiMatX_00, rotationPiMatX_01,
        rotationPiMatX_02, rotationPiMatX_03, rotationPiMatX_10, rotationPiMatX_11, rotationPiMatX_12, rotationPiMatX_13,
        rotationPiMatX_20, rotationPiMatX_21, rotationPiMatX_22, rotationPiMatX_23, rotationPiMatX_30, rotationPiMatX_31,
        rotationPiMatX_32, rotationPiMatX_33, rotationPiMatY_00, rotationPiMatY_01, rotationPiMatY_02, rotationPiMatY_03,
        rotationPiMatY_10, rotationPiMatY_11, rotationPiMatY_12, rotationPiMatY_13, rotationPiMatY_20, rotationPiMatY_21,
        rotationPiMatY_22, rotationPiMatY_23, rotationPiMatY_30, rotationPiMatY_31, rotationPiMatY_32, rotationPiMatY_33,
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
/-- The rotation average of the fermion pair monomial `e[2,0,1]` (ubar-family). -/
lemma rotationPiAvg_ubar_e201 :
    rotationPiAvg (Dbarψ [Sum.inr 1] 0 * Dψ [] 1) =
      (1/2 : ℂ) • (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0) := by
  rw [rotationPiAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    rotationPiZ_inv_coe, rotationPiY_inv_coe, rotationPiX_inv_coe,
    rotationPiMatZ_00, rotationPiMatZ_01, rotationPiMatZ_02, rotationPiMatZ_03, rotationPiMatZ_10, rotationPiMatZ_11,
        rotationPiMatZ_12, rotationPiMatZ_13, rotationPiMatZ_20, rotationPiMatZ_21, rotationPiMatZ_22, rotationPiMatZ_23,
        rotationPiMatZ_30, rotationPiMatZ_31, rotationPiMatZ_32, rotationPiMatZ_33, rotationPiMatX_00, rotationPiMatX_01,
        rotationPiMatX_02, rotationPiMatX_03, rotationPiMatX_10, rotationPiMatX_11, rotationPiMatX_12, rotationPiMatX_13,
        rotationPiMatX_20, rotationPiMatX_21, rotationPiMatX_22, rotationPiMatX_23, rotationPiMatX_30, rotationPiMatX_31,
        rotationPiMatX_32, rotationPiMatX_33, rotationPiMatY_00, rotationPiMatY_01, rotationPiMatY_02, rotationPiMatY_03,
        rotationPiMatY_10, rotationPiMatY_11, rotationPiMatY_12, rotationPiMatY_13, rotationPiMatY_20, rotationPiMatY_21,
        rotationPiMatY_22, rotationPiMatY_23, rotationPiMatY_30, rotationPiMatY_31, rotationPiMatY_32, rotationPiMatY_33,
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
/-- The rotation average of the fermion pair monomial `e[2,1,0]` (ubar-family). -/
lemma rotationPiAvg_ubar_e210 :
    rotationPiAvg (Dbarψ [Sum.inr 1] 1 * Dψ [] 0) =
      (-(1/2) : ℂ) • (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0) := by
  rw [rotationPiAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    rotationPiZ_inv_coe, rotationPiY_inv_coe, rotationPiX_inv_coe,
    rotationPiMatZ_00, rotationPiMatZ_01, rotationPiMatZ_02, rotationPiMatZ_03, rotationPiMatZ_10, rotationPiMatZ_11,
        rotationPiMatZ_12, rotationPiMatZ_13, rotationPiMatZ_20, rotationPiMatZ_21, rotationPiMatZ_22, rotationPiMatZ_23,
        rotationPiMatZ_30, rotationPiMatZ_31, rotationPiMatZ_32, rotationPiMatZ_33, rotationPiMatX_00, rotationPiMatX_01,
        rotationPiMatX_02, rotationPiMatX_03, rotationPiMatX_10, rotationPiMatX_11, rotationPiMatX_12, rotationPiMatX_13,
        rotationPiMatX_20, rotationPiMatX_21, rotationPiMatX_22, rotationPiMatX_23, rotationPiMatX_30, rotationPiMatX_31,
        rotationPiMatX_32, rotationPiMatX_33, rotationPiMatY_00, rotationPiMatY_01, rotationPiMatY_02, rotationPiMatY_03,
        rotationPiMatY_10, rotationPiMatY_11, rotationPiMatY_12, rotationPiMatY_13, rotationPiMatY_20, rotationPiMatY_21,
        rotationPiMatY_22, rotationPiMatY_23, rotationPiMatY_30, rotationPiMatY_31, rotationPiMatY_32, rotationPiMatY_33,
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
/-- The rotation average of the fermion pair monomial `e[2,1,1]` (ubar-family). -/
lemma rotationPiAvg_ubar_e211 :
    rotationPiAvg (Dbarψ [Sum.inr 1] 1 * Dψ [] 1) =
      0 := by
  rw [rotationPiAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    rotationPiZ_inv_coe, rotationPiY_inv_coe, rotationPiX_inv_coe,
    rotationPiMatZ_00, rotationPiMatZ_01, rotationPiMatZ_02, rotationPiMatZ_03, rotationPiMatZ_10, rotationPiMatZ_11,
        rotationPiMatZ_12, rotationPiMatZ_13, rotationPiMatZ_20, rotationPiMatZ_21, rotationPiMatZ_22, rotationPiMatZ_23,
        rotationPiMatZ_30, rotationPiMatZ_31, rotationPiMatZ_32, rotationPiMatZ_33, rotationPiMatX_00, rotationPiMatX_01,
        rotationPiMatX_02, rotationPiMatX_03, rotationPiMatX_10, rotationPiMatX_11, rotationPiMatX_12, rotationPiMatX_13,
        rotationPiMatX_20, rotationPiMatX_21, rotationPiMatX_22, rotationPiMatX_23, rotationPiMatX_30, rotationPiMatX_31,
        rotationPiMatX_32, rotationPiMatX_33, rotationPiMatY_00, rotationPiMatY_01, rotationPiMatY_02, rotationPiMatY_03,
        rotationPiMatY_10, rotationPiMatY_11, rotationPiMatY_12, rotationPiMatY_13, rotationPiMatY_20, rotationPiMatY_21,
        rotationPiMatY_22, rotationPiMatY_23, rotationPiMatY_30, rotationPiMatY_31, rotationPiMatY_32, rotationPiMatY_33,
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
/-- The rotation average of the fermion pair monomial `e[3,0,0]` (ubar-family). -/
lemma rotationPiAvg_ubar_e300 :
    rotationPiAvg (Dbarψ [Sum.inr 2] 0 * Dψ [] 0) =
      (1/2 : ℂ) • (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1) := by
  rw [rotationPiAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    rotationPiZ_inv_coe, rotationPiY_inv_coe, rotationPiX_inv_coe,
    rotationPiMatZ_00, rotationPiMatZ_01, rotationPiMatZ_02, rotationPiMatZ_03, rotationPiMatZ_10, rotationPiMatZ_11,
        rotationPiMatZ_12, rotationPiMatZ_13, rotationPiMatZ_20, rotationPiMatZ_21, rotationPiMatZ_22, rotationPiMatZ_23,
        rotationPiMatZ_30, rotationPiMatZ_31, rotationPiMatZ_32, rotationPiMatZ_33, rotationPiMatX_00, rotationPiMatX_01,
        rotationPiMatX_02, rotationPiMatX_03, rotationPiMatX_10, rotationPiMatX_11, rotationPiMatX_12, rotationPiMatX_13,
        rotationPiMatX_20, rotationPiMatX_21, rotationPiMatX_22, rotationPiMatX_23, rotationPiMatX_30, rotationPiMatX_31,
        rotationPiMatX_32, rotationPiMatX_33, rotationPiMatY_00, rotationPiMatY_01, rotationPiMatY_02, rotationPiMatY_03,
        rotationPiMatY_10, rotationPiMatY_11, rotationPiMatY_12, rotationPiMatY_13, rotationPiMatY_20, rotationPiMatY_21,
        rotationPiMatY_22, rotationPiMatY_23, rotationPiMatY_30, rotationPiMatY_31, rotationPiMatY_32, rotationPiMatY_33,
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
/-- The rotation average of the fermion pair monomial `e[3,0,1]` (ubar-family). -/
lemma rotationPiAvg_ubar_e301 :
    rotationPiAvg (Dbarψ [Sum.inr 2] 0 * Dψ [] 1) =
      0 := by
  rw [rotationPiAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    rotationPiZ_inv_coe, rotationPiY_inv_coe, rotationPiX_inv_coe,
    rotationPiMatZ_00, rotationPiMatZ_01, rotationPiMatZ_02, rotationPiMatZ_03, rotationPiMatZ_10, rotationPiMatZ_11,
        rotationPiMatZ_12, rotationPiMatZ_13, rotationPiMatZ_20, rotationPiMatZ_21, rotationPiMatZ_22, rotationPiMatZ_23,
        rotationPiMatZ_30, rotationPiMatZ_31, rotationPiMatZ_32, rotationPiMatZ_33, rotationPiMatX_00, rotationPiMatX_01,
        rotationPiMatX_02, rotationPiMatX_03, rotationPiMatX_10, rotationPiMatX_11, rotationPiMatX_12, rotationPiMatX_13,
        rotationPiMatX_20, rotationPiMatX_21, rotationPiMatX_22, rotationPiMatX_23, rotationPiMatX_30, rotationPiMatX_31,
        rotationPiMatX_32, rotationPiMatX_33, rotationPiMatY_00, rotationPiMatY_01, rotationPiMatY_02, rotationPiMatY_03,
        rotationPiMatY_10, rotationPiMatY_11, rotationPiMatY_12, rotationPiMatY_13, rotationPiMatY_20, rotationPiMatY_21,
        rotationPiMatY_22, rotationPiMatY_23, rotationPiMatY_30, rotationPiMatY_31, rotationPiMatY_32, rotationPiMatY_33,
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
/-- The rotation average of the fermion pair monomial `e[3,1,0]` (ubar-family). -/
lemma rotationPiAvg_ubar_e310 :
    rotationPiAvg (Dbarψ [Sum.inr 2] 1 * Dψ [] 0) =
      0 := by
  rw [rotationPiAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    rotationPiZ_inv_coe, rotationPiY_inv_coe, rotationPiX_inv_coe,
    rotationPiMatZ_00, rotationPiMatZ_01, rotationPiMatZ_02, rotationPiMatZ_03, rotationPiMatZ_10, rotationPiMatZ_11,
        rotationPiMatZ_12, rotationPiMatZ_13, rotationPiMatZ_20, rotationPiMatZ_21, rotationPiMatZ_22, rotationPiMatZ_23,
        rotationPiMatZ_30, rotationPiMatZ_31, rotationPiMatZ_32, rotationPiMatZ_33, rotationPiMatX_00, rotationPiMatX_01,
        rotationPiMatX_02, rotationPiMatX_03, rotationPiMatX_10, rotationPiMatX_11, rotationPiMatX_12, rotationPiMatX_13,
        rotationPiMatX_20, rotationPiMatX_21, rotationPiMatX_22, rotationPiMatX_23, rotationPiMatX_30, rotationPiMatX_31,
        rotationPiMatX_32, rotationPiMatX_33, rotationPiMatY_00, rotationPiMatY_01, rotationPiMatY_02, rotationPiMatY_03,
        rotationPiMatY_10, rotationPiMatY_11, rotationPiMatY_12, rotationPiMatY_13, rotationPiMatY_20, rotationPiMatY_21,
        rotationPiMatY_22, rotationPiMatY_23, rotationPiMatY_30, rotationPiMatY_31, rotationPiMatY_32, rotationPiMatY_33,
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
/-- The rotation average of the fermion pair monomial `e[3,1,1]` (ubar-family). -/
lemma rotationPiAvg_ubar_e311 :
    rotationPiAvg (Dbarψ [Sum.inr 2] 1 * Dψ [] 1) =
      (-(1/2) : ℂ) • (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1) := by
  rw [rotationPiAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    rotationPiZ_inv_coe, rotationPiY_inv_coe, rotationPiX_inv_coe,
    rotationPiMatZ_00, rotationPiMatZ_01, rotationPiMatZ_02, rotationPiMatZ_03, rotationPiMatZ_10, rotationPiMatZ_11,
        rotationPiMatZ_12, rotationPiMatZ_13, rotationPiMatZ_20, rotationPiMatZ_21, rotationPiMatZ_22, rotationPiMatZ_23,
        rotationPiMatZ_30, rotationPiMatZ_31, rotationPiMatZ_32, rotationPiMatZ_33, rotationPiMatX_00, rotationPiMatX_01,
        rotationPiMatX_02, rotationPiMatX_03, rotationPiMatX_10, rotationPiMatX_11, rotationPiMatX_12, rotationPiMatX_13,
        rotationPiMatX_20, rotationPiMatX_21, rotationPiMatX_22, rotationPiMatX_23, rotationPiMatX_30, rotationPiMatX_31,
        rotationPiMatX_32, rotationPiMatX_33, rotationPiMatY_00, rotationPiMatY_01, rotationPiMatY_02, rotationPiMatY_03,
        rotationPiMatY_10, rotationPiMatY_11, rotationPiMatY_12, rotationPiMatY_13, rotationPiMatY_20, rotationPiMatY_21,
        rotationPiMatY_22, rotationPiMatY_23, rotationPiMatY_30, rotationPiMatY_31, rotationPiMatY_32, rotationPiMatY_33,
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

end LeptonGaugeSector
