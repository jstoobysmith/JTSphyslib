/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.Invariants.Averages.RotationAverage
/-!
# The rotation average weighted against two boosts

The operator `rotationPiBoostAvg`: the rotation average of
`Averages/RotationAverage` followed by a weighting of the identity against the
two `z`-boosts `boostZ2`, `boostZ3` of `Subgroups/AxisBoosts`.

The three weights `-13/24, 8/3, -9/8` sum to one, so the operator still fixes
every Lorentz-invariant element, but they are chosen so that
`w₁ + w₂ t² + w₃ s² = 0` for `t² ∈ {4, 1/4}` and `s² ∈ {9, 1/9}`, which kills
both eigendirections of the two boosts. Since the boosts are non-compact this
weighting is what stands in for an invariant average — the same device that
`Averages/BoostAverage` uses on the weight-eight sector. It annihilates the
neutral weight-six sector outright (`eq_zero_of_mem_chargeCovSpan_six`).
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

/-- The boost-weighted rotation average: an operator fixing every
  Lorentz-invariant vector and annihilating the neutral weight-six sector.
  The weights `-13/24, 8/3, -9/8` sum to one and are chosen so that
  `w₁ + w₂ t² + w₃ s² = 0` for `t² ∈ {4, 1/4}` and `s² ∈ {9, 1/9}`
  respectively, killing both eigendirections of the two boosts. -/
noncomputable def rotationPiBoostAvg : Module.End ℂ JetAlgebra :=
  ((-13/24 : ℂ) • LinearMap.id + (8/3 : ℂ) • repLorentzGroup boostZ2 +
    (-9/8 : ℂ) • repLorentzGroup boostZ3) ∘ₗ rotationPiAvg

/-- The kill operator, termwise. -/
lemma rotationPiBoostAvg_apply (v : JetAlgebra) :
    rotationPiBoostAvg v = (-13/24 : ℂ) • rotationPiAvg v +
      (8/3 : ℂ) • repLorentzGroup boostZ2 (rotationPiAvg v) +
      (-9/8 : ℂ) • repLorentzGroup boostZ3 (rotationPiAvg v) := by
  simp only [rotationPiBoostAvg, LinearMap.comp_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.id_apply]

set_option maxHeartbeats 8000000 in
/-- The kill operator annihilates every embedded derivative field strength:
  the rotation average kills every component with an odd index pattern, and the
  boost combination kills the twelve surviving components. -/
lemma rotationPiBoostAvg_fieldStrengthDeriv_singleton (ρ μ ν : Fin 1 ⊕ Fin 3) :
    rotationPiBoostAvg (fieldStrengthDeriv {ρ} μ ν) = 0 := by
  rcases eq_or_ne μ ν with rfl | hμν
  · rw [fieldStrengthDeriv_self]
    exact map_zero _
  · have hK : rotationPiAvg (fieldStrengthDeriv {ρ} μ ν) =
        (((1 + rotationPiSignZ ρ * (rotationPiSignZ μ * rotationPiSignZ ν) +
          rotationPiSignY ρ * (rotationPiSignY μ * rotationPiSignY ν) +
          rotationPiSignX ρ * (rotationPiSignX μ * rotationPiSignX ν)) / 4 : ℝ) : ℂ) •
          fieldStrengthDeriv {ρ} μ ν := by
      rw [rotationPiAvg_apply,
        repLorentzGroup_diag_fieldStrengthDeriv_singleton toLorentzGroup_rotationPiZ,
        repLorentzGroup_diag_fieldStrengthDeriv_singleton toLorentzGroup_rotationPiY,
        repLorentzGroup_diag_fieldStrengthDeriv_singleton toLorentzGroup_rotationPiX]
      push_cast
      module
    rw [rotationPiBoostAvg_apply, hK, map_smul, map_smul]
    rcases ρ with ρ | ρ <;> rcases μ with μ | μ <;> rcases ν with ν | ν <;>
      fin_cases ρ <;> fin_cases μ <;> fin_cases ν <;>
      first
      | (simp only [fieldStrengthDeriv_self, map_zero, smul_zero, add_zero]; done)
      | (norm_num [rotationPiSignZ, rotationPiSignY, rotationPiSignX]; done)
      | (norm_num [rotationPiSignZ, rotationPiSignY, rotationPiSignX]
         rw [repLorentzGroup_fieldStrengthDeriv_singleton boostZ2,
           repLorentzGroup_fieldStrengthDeriv_singleton boostZ3]
         simp only [Fintype.sum_sum_type, Fin.sum_univ_three, Fin.sum_univ_one,
           toLorentzGroup_boostZ2, toLorentzGroup_boostZ3]
         norm_num [boostMatA, boostMatB, fieldStrengthDeriv_self,
           fieldStrengthDeriv_inr_inl]
         push_cast
         module)

set_option maxHeartbeats 4000000 in
/-- The kill operator annihilates every zero-derivative pair `ψ̄_α ψ_β`: the
  rotation average kills the off-diagonal pairs and symmetrises the diagonal
  ones, which the boost combination then kills. -/
lemma rotationPiBoostAvg_Dbarψ_mul_Dψ (α β : Fin 2) :
    rotationPiBoostAvg (Dbarψ [] α * Dψ [] β) = 0 := by
  rw [rotationPiBoostAvg_apply, rotationPiAvg_apply]
  fin_cases α <;> fin_cases β <;>
    · simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_nil, map_add, map_smul,
        map_sum, rotationPiZ_inv_coe, rotationPiY_inv_coe, rotationPiX_inv_coe,
        boostZ2_inv_coe, boostZ3_inv_coe, Fin.sum_univ_two, Fin.zero_eta,
        Fin.mk_one, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
        Matrix.cons_val_fin_one,
        star_zero, star_neg, star_one, Complex.star_def, Complex.conj_I,
        Complex.conj_ofReal, map_one, map_zero, map_neg, neg_mul, mul_neg,
        neg_neg,
        zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
        Complex.I_mul_I, one_mul, mul_one, smul_add, smul_smul, Finset.smul_sum]
      try push_cast
      try module

set_option maxHeartbeats 4000000 in
/-- The kill operator annihilates every zero-derivative pair `ψ_α ψ̄_β`. -/
lemma rotationPiBoostAvg_Dψ_mul_Dbarψ (α β : Fin 2) :
    rotationPiBoostAvg (Dψ [] α * Dbarψ [] β) = 0 := by
  rw [rotationPiBoostAvg_apply, rotationPiAvg_apply]
  fin_cases α <;> fin_cases β <;>
    · simp only [repLorentzGroup_Dψ_nil_mul_Dbarψ_nil, map_add, map_smul,
        map_sum, rotationPiZ_inv_coe, rotationPiY_inv_coe, rotationPiX_inv_coe,
        boostZ2_inv_coe, boostZ3_inv_coe, Fin.sum_univ_two, Fin.zero_eta,
        Fin.mk_one, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
        Matrix.cons_val_fin_one,
        star_zero, star_neg, star_one, Complex.star_def, Complex.conj_I,
        Complex.conj_ofReal, map_one, map_zero, map_neg, neg_mul, mul_neg,
        neg_neg,
        zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
        Complex.I_mul_I, one_mul, mul_one, smul_add, smul_smul, Finset.smul_sum]
      try push_cast
      try module

/-- No Lorentz invariant of mass weight six: an invariant combination of the
  field-strength derivatives `∂_ρ F_{μν}` and the fermion pairs `ψ̄_α ψ_β`
  vanishes. -/
lemma eq_zero_of_mem_chargeCovSpan_six {y : JetAlgebra}
    (hy : y ∈ chargeCovSpan 6 0)
    (hinv : ∀ Λ : SL(2,ℂ), repLorentzGroup Λ y = y) : y = 0 := by
  have h := chargeCovSpan_six_le hy
  rw [Submodule.span_union, Submodule.span_union] at h
  obtain ⟨u, hu, w, hw, hy'⟩ := Submodule.mem_sup.mp h
  obtain ⟨u1, hu1, u2, hu2, hu'⟩ := Submodule.mem_sup.mp hu
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hu1
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hu2
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hw
  have hKy : rotationPiAvg y = y := by
    rw [rotationPiAvg_apply, hinv rotationPiZ, hinv rotationPiY, hinv rotationPiX]
    module
  have hself : rotationPiBoostAvg y = y := by
    rw [rotationPiBoostAvg_apply, hKy, hinv boostZ2, hinv boostZ3]
    module
  have hkill : rotationPiBoostAvg y = 0 := by
    rw [← hy', ← hu', ← ha, ← hd, ← he]
    simp only [map_add, map_sum, map_smul, rotationPiBoostAvg_fieldStrengthDeriv_singleton,
      rotationPiBoostAvg_Dbarψ_mul_Dψ, rotationPiBoostAvg_Dψ_mul_Dbarψ, smul_zero,
      Finset.sum_const_zero, add_zero]
  exact hself.symm.trans hkill

end JetAlgebra

end LeptonGaugeSector
