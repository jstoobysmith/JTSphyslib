/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.MassDim
/-!
# The Maxwell term

The kinetic term `F_{μν} F^{μν}` of the photon: the square of the field strength
with both indices raised by the Minkowski metric. It is gauge invariant because
the field strength is, Lorentz invariant by the defining identity of the Lorentz
group, and of mass weight eight, that is mass dimension four.
-/

@[expose] public section

set_option maxHeartbeats 1000000

namespace LeptonGaugeSector
open TensorProduct StandardModel

namespace JetAlgebra

open scoped minkowskiMatrix PauliMatrix
open Matrix MatrixGroups

/-- The Maxwell kinetic term `F_{μν} F^{μν}`: the field-strength square with
  both indices raised by the (diagonal) Minkowski metric. Mass weight eight. -/
noncomputable def maxwellTerm : JetAlgebra :=
  ∑ μ, ∑ ν, ((η μ μ * η ν ν : ℝ) : ℂ) •
    (fieldStrengthDeriv {} μ ν * fieldStrengthDeriv {} μ ν)

lemma repJetGaugeGroupI_maxwellTerm (U : JetGaugeGroupI) :
    repJetGaugeGroupI U maxwellTerm = maxwellTerm := by
  rw [maxwellTerm, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [map_smul]
  congr 1
  rw [repJetGaugeGroupI_mul', repJetGaugeGroupI_fieldStrengthDeriv]

/-- The component form of the Lorentz-group defining identity: contracting two
  Lorentz matrices with the (diagonal, involutive) Minkowski metric over their
  second indices reproduces the metric. -/
lemma toLorentzGroup_sum_η_mul_mul (Λ : SL(2,ℂ)) (a a' : Fin 1 ⊕ Fin 3) :
    ∑ ν, η ν ν * (Lorentz.SL2C.toLorentzGroup Λ).1 a ν *
      (Lorentz.SL2C.toLorentzGroup Λ).1 a' ν = η a a' := by
  have hsq : η a' a' * η a' a' = 1 := by
    rcases a' with i | i
    · rw [show i = (0 : Fin 1) from Subsingleton.elim i 0,
        minkowskiMatrix.inl_0_inl_0]
      norm_num
    · rw [minkowskiMatrix.inr_i_inr_i]
      norm_num
  have h := congrFun (congrFun ((LorentzGroup.mem_iff_self_mul_dual).mp
    (Lorentz.SL2C.toLorentzGroup Λ).2) a) a'
  rw [Matrix.mul_apply] at h
  simp only [minkowskiMatrix.dual_apply] at h
  have h2 := congrArg (fun t => t * η a' a') h
  simp only [Finset.sum_mul] at h2
  rw [show (∑ ν, (Lorentz.SL2C.toLorentzGroup Λ).1 a ν *
        (η ν ν * (Lorentz.SL2C.toLorentzGroup Λ).1 a' ν * η a' a') * η a' a') =
      ∑ ν, (η ν ν * (Lorentz.SL2C.toLorentzGroup Λ).1 a ν *
        (Lorentz.SL2C.toLorentzGroup Λ).1 a' ν) * (η a' a' * η a' a') from
      Finset.sum_congr rfl fun ν _ => by ring, hsq] at h2
  simp only [mul_one] at h2
  rw [h2, Matrix.one_apply]
  by_cases haa : a = a'
  · subst haa
    simp
  · rw [if_neg haa, minkowskiMatrix.as_diagonal, Matrix.diagonal_apply_ne _ haa]
    simp

/-- Lorentz invariance of the Maxwell term, by the `η`-contraction identity. -/
lemma repLorentzGroup_maxwellTerm (Λ : SL(2,ℂ)) :
    repLorentzGroup Λ maxwellTerm = maxwellTerm := by
  have hscal : ∀ a b a' b' : Fin 1 ⊕ Fin 3,
      (∑ μ, ∑ ν, η μ μ * η ν ν *
        ((Lorentz.SL2C.toLorentzGroup Λ).1 a μ *
          (Lorentz.SL2C.toLorentzGroup Λ).1 b ν *
          ((Lorentz.SL2C.toLorentzGroup Λ).1 a' μ *
            (Lorentz.SL2C.toLorentzGroup Λ).1 b' ν))) = η a a' * η b b' := by
    intro a b a' b'
    rw [show (∑ μ, ∑ ν, η μ μ * η ν ν *
        ((Lorentz.SL2C.toLorentzGroup Λ).1 a μ *
          (Lorentz.SL2C.toLorentzGroup Λ).1 b ν *
          ((Lorentz.SL2C.toLorentzGroup Λ).1 a' μ *
            (Lorentz.SL2C.toLorentzGroup Λ).1 b' ν))) =
        ∑ μ, (η μ μ * (Lorentz.SL2C.toLorentzGroup Λ).1 a μ *
            (Lorentz.SL2C.toLorentzGroup Λ).1 a' μ) *
          ∑ ν, (η ν ν * (Lorentz.SL2C.toLorentzGroup Λ).1 b ν *
            (Lorentz.SL2C.toLorentzGroup Λ).1 b' ν) from
      Finset.sum_congr rfl fun μ _ => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun ν _ => by ring,
      ← Finset.sum_mul, toLorentzGroup_sum_η_mul_mul, toLorentzGroup_sum_η_mul_mul]
  have hFt : ∀ μ ν : Fin 1 ⊕ Fin 3, repLorentzGroup Λ
      (fieldStrengthDeriv {} μ ν * fieldStrengthDeriv {} μ ν) =
      ∑ a, ∑ b, ∑ a', ∑ b',
        ((((Lorentz.SL2C.toLorentzGroup Λ).1 a μ *
          (Lorentz.SL2C.toLorentzGroup Λ).1 b ν : ℝ) : ℂ) *
          (((Lorentz.SL2C.toLorentzGroup Λ).1 a' μ *
            (Lorentz.SL2C.toLorentzGroup Λ).1 b' ν : ℝ) : ℂ)) •
        (fieldStrengthDeriv {} a b * fieldStrengthDeriv {} a' b') := by
    intro μ ν
    rw [repLorentzGroup_apply_mul, repLorentzGroup_fieldStrengthDeriv_nil]
    have hsm : ∀ (f : (Fin 1 ⊕ Fin 3) → JetAlgebra) (y : JetAlgebra),
        (∑ x, f x) * y = ∑ x, f x * y := fun f y => by
      rw [show (∑ x, f x) * y = LinearMap.mulRight ℂ y (∑ x, f x) from rfl, map_sum]
      rfl
    have hms : ∀ (f : (Fin 1 ⊕ Fin 3) → JetAlgebra) (y : JetAlgebra),
        y * (∑ x, f x) = ∑ x, y * f x := fun f y => by
      rw [show y * (∑ x, f x) = LinearMap.mulLeft ℂ y (∑ x, f x) from rfl, map_sum]
      rfl
    have hsmul : ∀ (c d : ℂ) (x y : JetAlgebra),
        (c • x) * (d • y) = (c * d) • (x * y) := fun c d x y => by
      rw [smul_mul_smul_comm]
    simp only [hsm, hms, hsmul]
  rw [maxwellTerm, map_sum]
  conv_lhs => enter [2, μ]; rw [map_sum]
  conv_lhs => enter [2, μ, 2, ν]; rw [map_smul, hFt μ ν]
  simp only [Finset.smul_sum, smul_smul, ← Complex.ofReal_mul]
  conv_lhs => enter [2, μ]; rw [Finset.sum_comm]
  conv_lhs => enter [2, μ, 2, a]; rw [Finset.sum_comm]
  conv_lhs => enter [2, μ, 2, a, 2, b]; rw [Finset.sum_comm]
  conv_lhs => enter [2, μ, 2, a, 2, b, 2, a']; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, a]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a, 2, b]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a, 2, b, 2, a']; rw [Finset.sum_comm]
  conv_lhs => enter [2, a, 2, b, 2, a', 2, b', 2, μ]; rw [← Finset.sum_smul]
  conv_lhs => enter [2, a, 2, b, 2, a', 2, b']; rw [← Finset.sum_smul]
  simp only [← Complex.ofReal_sum, hscal]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single a (fun a'' _ ha'' => Finset.sum_eq_zero fun b'' _ => by
      rw [show η a a'' = 0 from by
          rw [minkowskiMatrix.as_diagonal, Matrix.diagonal_apply_ne _ (Ne.symm ha'')],
        zero_mul, Complex.ofReal_zero, zero_smul])
    (fun h => absurd (Finset.mem_univ a) h),
    Finset.sum_eq_single b (fun b'' _ hb'' => by
      rw [show η b b'' = 0 from by
          rw [minkowskiMatrix.as_diagonal, Matrix.diagonal_apply_ne _ (Ne.symm hb'')],
        mul_zero, Complex.ofReal_zero, zero_smul])
    (fun h => absurd (Finset.mem_univ b) h)]

lemma maxwellTerm_mem_massWeightLESubmodule :
    maxwellTerm ∈ MassWeightLESubmodule 8 := by
  rw [maxwellTerm]
  refine Submodule.sum_mem _ fun μ _ => Submodule.sum_mem _ fun ν _ =>
    Submodule.smul_mem _ _ ?_
  have h4 : (fieldStrengthDeriv {} μ ν : JetAlgebra) ∈ massWeightSubmodule 4 := by
    simpa using fieldStrengthDeriv_mem_massWeightSubmodule {} μ ν
  exact mem_massWeightLESubmodule_of_mem (m := 4 + 4) le_rfl
    (mul_mem_massWeightSubmodule h4 h4)

/-- The Maxwell term as an explicit combination of the six independent
  field-strength squares. -/
lemma maxwellTerm_eq : maxwellTerm =
    (-2 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0))
    + (-2 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1))
    + (-2 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2))
    + (2 : ℂ) • (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1))
    + (2 : ℂ) • (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2))
    + (2 : ℂ) • (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) := by
  have hnm : ∀ u v : JetAlgebra, (-u) * v = -(u * v) := by grind
  have hmn : ∀ u v : JetAlgebra, u * (-v) = -(u * v) := by grind
  rw [maxwellTerm]
  simp only [Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three,
    minkowskiMatrix.inl_0_inl_0, minkowskiMatrix.inr_i_inr_i,
    fieldStrengthDeriv_self, mul_zero, smul_zero, add_zero, zero_add]
  simp only [
      fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 0),
      fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 1),
      fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 2),
      fieldStrengthDeriv_antisymm {} (Sum.inr 0) (Sum.inr 1),
      fieldStrengthDeriv_antisymm {} (Sum.inr 0) (Sum.inr 2),
      fieldStrengthDeriv_antisymm {} (Sum.inr 1) (Sum.inr 2),
    hnm, hmn, neg_neg]
  push_cast
  module

end JetAlgebra

end LeptonGaugeSector
