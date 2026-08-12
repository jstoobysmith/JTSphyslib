/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.Grading.BoostWeight
public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.Terms.KineticTerms
public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.FermionicKineticTerm.LinearIndependence
/-!
# The boost weight zero parts of the photon pairs and the fermion kinetic bilinears

Boost weights give us the invariance under the Lorentz group. This is in the following
way. Consider all terms in the span of `ψ̄_α ∂_μ ψ_β`.

-/

@[expose] public section

namespace LeptonGaugeSector
open TensorProduct StandardModel Lorentz
open scoped minkowskiMatrix PauliMatrix Pointwise
open Matrix MatrixGroups

namespace JetAlgebra

private lemma algebraMap_real_complex (t : ℝ) : (algebraMap ℝ ℂ) t = ((t : ℝ) : ℂ) := rfl

/-- **The boost weight zero part of the fermion kinetic bilinears.** An element of the span of
  the products `ψ̄_α ∂_μ ψ_β` has boost weight zero exactly when it is a combination of the six
  bilinears listed. Both spinor indices carry `z`-boost weight `∓1` for the index `0, 1` and the
  derivative index carries `±2` on the light-cone combinations `∂_0 ∓ ∂_z` and `0` on `∂_x, ∂_y`,
  so the weight-zero bilinears pair the spinor indices `(0,0)` and `(1,1)` with the matching
  light-cone derivative and the mixed spinor indices with a transverse derivative.

  The six spanning elements are chosen with the later restriction by the boost weights in the
  `x`- and `y`-directions in mind: they pair into a `∂_0/∂_z` block and `∂_x` and `∂_y` blocks,
  and in each transverse block the two sign combinations `ψ̄_0 ∂_i ψ_1 ± ψ̄_1 ∂_i ψ_0` split the
  spinor content into the part that is diagonal for the boost in the `i`-direction and the part
  that is not, so their weight decompositions in those directions are immediate. -/
theorem boostWeight_inter_fermionic_kinetic_term :
    BoostWeight.boostWeightSubmodule repLorentzGroup 2 0 ⊓ Submodule.span ℂ
        {x | ∃ α μ β, x = Dbarψ [] α * Dψ [μ] β} =
      Submodule.span ℂ
        {Dbarψ [] 0 * (Dψ [Sum.inl 0] 0 - Dψ [Sum.inr 2] 0) +
            Dbarψ [] 1 * (Dψ [Sum.inl 0] 1 + Dψ [Sum.inr 2] 1),
          Dbarψ [] 0 * (Dψ [Sum.inl 0] 0 - Dψ [Sum.inr 2] 0) -
            Dbarψ [] 1 * (Dψ [Sum.inl 0] 1 + Dψ [Sum.inr 2] 1),
          Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0,
          Dbarψ [] 0 * Dψ [Sum.inr 0] 1 - Dbarψ [] 1 * Dψ [Sum.inr 0] 0,
          Dbarψ [] 0 * Dψ [Sum.inr 1] 1 + Dbarψ [] 1 * Dψ [Sum.inr 1] 0,
          Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0} := by
  -- ### A. The boost eigenvectors among the first-order fermion coordinates
  -- `ψ̄_α` is an eigenvector of weight `∓1` for `α = 0, 1`; on `∂_μ ψ_β` the spinor index
  -- contributes `∓1` and the light-cone derivative combinations `(∂_0 ∓ ∂_z) ψ_β` add `±2`.
  set B0 := Dbarψ [] 0 with hB0
  set B1 := Dbarψ [] 1 with hB1
  set P0 := Dψ [Sum.inl 0] 0 - Dψ [Sum.inr 2] 0 with hP0
  set P1 := Dψ [Sum.inl 0] 1 - Dψ [Sum.inr 2] 1 with hP1
  set M0 := Dψ [Sum.inl 0] 0 + Dψ [Sum.inr 2] 0 with hM0
  set M1 := Dψ [Sum.inl 0] 1 + Dψ [Sum.inr 2] 1 with hM1
  set X0 := Dψ [Sum.inr 0] 0 with hX0
  set X1 := Dψ [Sum.inr 0] 1 with hX1
  set Y0 := Dψ [Sum.inr 1] 0 with hY0
  set Y1 := Dψ [Sum.inr 1] 1 with hY1
  set FF : Set JetAlgebra := {x | ∃ α μ β, x = Dbarψ [] α * Dψ [μ] β} with hFF
  set S : Set JetAlgebra := {B0 * P0 + B1 * M1, B0 * P0 - B1 * M1, B0 * X1 + B1 * X0,
    B0 * X1 - B1 * X0, B0 * Y1 + B1 * Y0, B0 * Y1 - B1 * Y0} with hS
  set W := Submodule.span ℂ S ⊔ ⨆ (j : ℤ) (_ : j ≠ 0), BoostWeight.boostWeightSubmodule repLorentzGroup 2 j with hW
  have hB0w : B0 ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 2 (-1) := Dbarψ_nil_zero_mem_neg_one
  have hB1w : B1 ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 2 1 := Dbarψ_nil_one_mem_one
  obtain ⟨hP0w, hP1w, hM0w, hM1w, hX0w, hX1w, hY0w, hY1w⟩ :
      P0 ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 2 1 ∧ P1 ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 2 3 ∧
      M0 ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 2 (-3) ∧ M1 ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 2 (-1) ∧
      X0 ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 2 (-1) ∧ X1 ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 2 1 ∧
      Y0 ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 2 (-1) ∧ Y1 ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 2 1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro t ht
    all_goals
      have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
      simp only [hP0, hP1, hM0, hM1, hX0, hX1, hY0, hY1, map_sub, map_add, boostAxis_two,
        algebraMap_real_complex,
        repLorentzGroup_Dψ_singleton, toLorentzGroup_boostZel, boostZel_inv_coe, boostMatZ,
        Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
        Complex.star_def, map_zero, star_zero, Complex.conj_ofReal, Complex.ofReal_zero,
        Complex.ofReal_one, mul_zero, zero_mul, mul_one, one_mul, zero_smul, smul_zero,
        add_zero, zero_add]
      push_cast
      match_scalars <;> (field_simp; try ring)
  -- ### B. The six weight-zero bilinears lie in the span of the pairs
  have hSW : Submodule.span ℂ S ≤ W := le_sup_left
  have hpm : ∀ {u v : JetAlgebra}, u + v ∈ S → u - v ∈ S → u ∈ W ∧ v ∈ W := by
    intro u v h₁ h₂
    have e₁ : u + v ∈ W := hSW (Submodule.subset_span h₁)
    have e₂ : u - v ∈ W := hSW (Submodule.subset_span h₂)
    constructor
    · rw [show u = (2⁻¹ : ℂ) • (u + v) + (2⁻¹ : ℂ) • (u - v) from by module]
      exact add_mem (Submodule.smul_mem _ _ e₁) (Submodule.smul_mem _ _ e₂)
    · rw [show v = (2⁻¹ : ℂ) • (u + v) - (2⁻¹ : ℂ) • (u - v) from by module]
      exact sub_mem (Submodule.smul_mem _ _ e₁) (Submodule.smul_mem _ _ e₂)
  obtain ⟨k1, k8⟩ : B0 * P0 ∈ W ∧ B1 * M1 ∈ W := hpm (by simp [hS]) (by simp [hS])
  obtain ⟨kx0, kx1⟩ : B0 * X1 ∈ W ∧ B1 * X0 ∈ W := hpm (by simp [hS]) (by simp [hS])
  obtain ⟨ky0, ky1⟩ : B0 * Y1 ∈ W ∧ B1 * Y0 ∈ W := hpm (by simp [hS]) (by simp [hS])
  -- ### C. Every bilinear splits into eigen bilinears of a single weight
  -- The ten bilinears of nonzero weight, and the decomposition of `∂_0 ψ_β` and `∂_z ψ_β` into
  -- the light-cone combinations.
  have hm : ∀ {k l : ℤ} {x y : JetAlgebra}, x ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 2 k →
      y ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 2 l → k + l ≠ 0 → x * y ∈ W := fun hx hy h =>
    Submodule.mem_sup_right (Submodule.mem_iSup_of_mem _
      (Submodule.mem_iSup_of_mem h (BoostWeight.mul_mem repLorentzGroup hx hy)))
  have k2 : B0 * M0 ∈ W := hm hB0w hM0w (by norm_num)
  have k3 : B0 * P1 ∈ W := hm hB0w hP1w (by norm_num)
  have k4 : B0 * M1 ∈ W := hm hB0w hM1w (by norm_num)
  have k5 : B1 * P0 ∈ W := hm hB1w hP0w (by norm_num)
  have k6 : B1 * M0 ∈ W := hm hB1w hM0w (by norm_num)
  have k7 : B1 * P1 ∈ W := hm hB1w hP1w (by norm_num)
  have key : ∀ {a u v : JetAlgebra} (c d : ℂ) {y : JetAlgebra}, a * u ∈ W → a * v ∈ W →
      y = c • u + d • v → a * y ∈ W := by
    rintro a u v c d y hu hv rfl
    rw [mul_add, mul_smul_comm, mul_smul_comm]
    exact add_mem (Submodule.smul_mem _ _ hu) (Submodule.smul_mem _ _ hv)
  have hkey : Submodule.span ℂ FF ≤ W := by
    rw [hFF]
    refine Submodule.span_le.2 ?_
    rintro x ⟨α, μ, β, rfl⟩
    match α, μ, β with
    | 0, Sum.inl 0, 0 => exact key 2⁻¹ 2⁻¹ k1 k2 (by rw [hP0, hM0]; module)
    | 0, Sum.inr 2, 0 => exact key (-2⁻¹) 2⁻¹ k1 k2 (by rw [hP0, hM0]; module)
    | 0, Sum.inl 0, 1 => exact key 2⁻¹ 2⁻¹ k3 k4 (by rw [hP1, hM1]; module)
    | 0, Sum.inr 2, 1 => exact key (-2⁻¹) 2⁻¹ k3 k4 (by rw [hP1, hM1]; module)
    | 1, Sum.inl 0, 0 => exact key 2⁻¹ 2⁻¹ k5 k6 (by rw [hP0, hM0]; module)
    | 1, Sum.inr 2, 0 => exact key (-2⁻¹) 2⁻¹ k5 k6 (by rw [hP0, hM0]; module)
    | 1, Sum.inl 0, 1 => exact key 2⁻¹ 2⁻¹ k7 k8 (by rw [hP1, hM1]; module)
    | 1, Sum.inr 2, 1 => exact key (-2⁻¹) 2⁻¹ k7 k8 (by rw [hP1, hM1]; module)
    | 0, Sum.inr 0, 0 => exact hm hB0w hX0w (by norm_num)
    | 0, Sum.inr 0, 1 => exact kx0
    | 0, Sum.inr 1, 0 => exact hm hB0w hY0w (by norm_num)
    | 0, Sum.inr 1, 1 => exact ky0
    | 1, Sum.inr 0, 0 => exact kx1
    | 1, Sum.inr 0, 1 => exact hm hB1w hX1w (by norm_num)
    | 1, Sum.inr 1, 0 => exact ky1
    | 1, Sum.inr 1, 1 => exact hm hB1w hY1w (by norm_num)
  -- ### D. The intersection
  have hz : ∀ {k l : ℤ} {x y : JetAlgebra}, x ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 2 k →
      y ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 2 l → k + l = 0 → x * y ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 2 0 := by
    intro k l x y hx hy h
    rw [← h]; exact BoostWeight.mul_mem repLorentzGroup hx hy
  have hSw : Submodule.span ℂ S ≤ BoostWeight.boostWeightSubmodule repLorentzGroup 2 0 := by
    rw [hS]
    refine Submodule.span_le.2 ?_
    rintro x (rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [add_mem (hz hB0w hP0w (by norm_num)) (hz hB1w hM1w (by norm_num)),
      sub_mem (hz hB0w hP0w (by norm_num)) (hz hB1w hM1w (by norm_num)),
      add_mem (hz hB0w hX1w (by norm_num)) (hz hB1w hX0w (by norm_num)),
      sub_mem (hz hB0w hX1w (by norm_num)) (hz hB1w hX0w (by norm_num)),
      add_mem (hz hB0w hY1w (by norm_num)) (hz hB1w hY0w (by norm_num)),
      sub_mem (hz hB0w hY1w (by norm_num)) (hz hB1w hY0w (by norm_num))]
  have hFm : ∀ α μ β, Dbarψ [] α * Dψ [μ] β ∈ Submodule.span ℂ FF := fun α μ β => by
    rw [hFF]; exact Submodule.subset_span ⟨α, μ, β, rfl⟩
  have hSF : Submodule.span ℂ S ≤ Submodule.span ℂ FF := by
    rw [hS]
    refine Submodule.span_le.2 ?_
    rintro x (rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp only [hB0, hB1, hP0, hM1, hX0, hX1, hY0, hY1, mul_sub, mul_add] <;>
      repeat' first | exact hFm _ _ _ | apply add_mem | apply sub_mem | apply neg_mem
  refine le_antisymm (le_trans (inf_le_inf_left _ hkey) ?_) (le_inf hSw hSF)
  rw [hW, inf_comm, sup_inf_assoc_of_le _ hSw,
    disjoint_iff.mp (BoostWeight.boostWeightSubmodule_iSupIndep repLorentzGroup (i := 2) 0).symm, sup_bot_eq]


/-- **The boost weight zero part of the fermion kinetic bilinears, `x`-direction.** The `x`-boost
  is not diagonal on the coordinate spinors, so the eigenvectors are the combinations
  `ψ̄_0 ± ψ̄_1` of weight `∓1`, and likewise on the spinor index of `∂_μ ψ_β`; the light-cone
  derivative combinations are `∂_0 ∓ ∂_x`, and `∂_y`, `∂_z` are the transverse directions. -/
theorem boostWeight_inter_fermionic_kinetic_term_x :
    BoostWeight.boostWeightSubmodule repLorentzGroup 0 0 ⊓ Submodule.span ℂ
        {x | ∃ α μ β, x = Dbarψ [] α * Dψ [μ] β} =
      Submodule.span ℂ
        {(Dbarψ [] 0 + Dbarψ [] 1) *
              (Dψ [Sum.inl 0] 0 + Dψ [Sum.inl 0] 1 - (Dψ [Sum.inr 0] 0 + Dψ [Sum.inr 0] 1)) +
            (Dbarψ [] 0 - Dbarψ [] 1) *
              (Dψ [Sum.inl 0] 0 - Dψ [Sum.inl 0] 1 + (Dψ [Sum.inr 0] 0 - Dψ [Sum.inr 0] 1)),
          (Dbarψ [] 0 + Dbarψ [] 1) *
              (Dψ [Sum.inl 0] 0 + Dψ [Sum.inl 0] 1 - (Dψ [Sum.inr 0] 0 + Dψ [Sum.inr 0] 1)) -
            (Dbarψ [] 0 - Dbarψ [] 1) *
              (Dψ [Sum.inl 0] 0 - Dψ [Sum.inl 0] 1 + (Dψ [Sum.inr 0] 0 - Dψ [Sum.inr 0] 1)),
          (Dbarψ [] 0 + Dbarψ [] 1) * (Dψ [Sum.inr 1] 0 - Dψ [Sum.inr 1] 1) +
            (Dbarψ [] 0 - Dbarψ [] 1) * (Dψ [Sum.inr 1] 0 + Dψ [Sum.inr 1] 1),
          (Dbarψ [] 0 + Dbarψ [] 1) * (Dψ [Sum.inr 1] 0 - Dψ [Sum.inr 1] 1) -
            (Dbarψ [] 0 - Dbarψ [] 1) * (Dψ [Sum.inr 1] 0 + Dψ [Sum.inr 1] 1),
          (Dbarψ [] 0 + Dbarψ [] 1) * (Dψ [Sum.inr 2] 0 - Dψ [Sum.inr 2] 1) +
            (Dbarψ [] 0 - Dbarψ [] 1) * (Dψ [Sum.inr 2] 0 + Dψ [Sum.inr 2] 1),
          (Dbarψ [] 0 + Dbarψ [] 1) * (Dψ [Sum.inr 2] 0 - Dψ [Sum.inr 2] 1) -
            (Dbarψ [] 0 - Dbarψ [] 1) * (Dψ [Sum.inr 2] 0 + Dψ [Sum.inr 2] 1)} := by
  -- ### A. The boost eigenvectors among the first-order fermion coordinates
  set Bp := Dbarψ [] 0 + Dbarψ [] 1 with hBp
  set Bm := Dbarψ [] 0 - Dbarψ [] 1 with hBm
  set P := Dψ [Sum.inl 0] 0 + Dψ [Sum.inl 0] 1 - (Dψ [Sum.inr 0] 0 + Dψ [Sum.inr 0] 1) with hP
  set Q := Dψ [Sum.inl 0] 0 - Dψ [Sum.inl 0] 1 - (Dψ [Sum.inr 0] 0 - Dψ [Sum.inr 0] 1) with hQ
  set N := Dψ [Sum.inl 0] 0 + Dψ [Sum.inl 0] 1 + (Dψ [Sum.inr 0] 0 + Dψ [Sum.inr 0] 1) with hN
  set M := Dψ [Sum.inl 0] 0 - Dψ [Sum.inl 0] 1 + (Dψ [Sum.inr 0] 0 - Dψ [Sum.inr 0] 1) with hM
  set T0p := Dψ [Sum.inr 1] 0 + Dψ [Sum.inr 1] 1 with hT0p
  set T0m := Dψ [Sum.inr 1] 0 - Dψ [Sum.inr 1] 1 with hT0m
  set T1p := Dψ [Sum.inr 2] 0 + Dψ [Sum.inr 2] 1 with hT1p
  set T1m := Dψ [Sum.inr 2] 0 - Dψ [Sum.inr 2] 1 with hT1m
  set FF : Set JetAlgebra := {x | ∃ α μ β, x = Dbarψ [] α * Dψ [μ] β} with hFF
  set S : Set JetAlgebra := {Bp * P + Bm * M, Bp * P - Bm * M, Bp * T0m + Bm * T0p,
    Bp * T0m - Bm * T0p, Bp * T1m + Bm * T1p, Bp * T1m - Bm * T1p} with hS
  set W := Submodule.span ℂ S ⊔ ⨆ (j : ℤ) (_ : j ≠ 0), BoostWeight.boostWeightSubmodule repLorentzGroup 0 j with hW
  obtain ⟨hBpw, hBmw, hPw, hQw, hNw, hMw, hT0pw, hT0mw, hT1pw, hT1mw⟩ :
      Bp ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 0 (-1) ∧ Bm ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 0 1 ∧
      P ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 0 1 ∧ Q ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 0 3 ∧
      N ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 0 (-3) ∧ M ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 0 (-1) ∧
      T0p ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 0 (-1) ∧ T0m ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 0 1 ∧
      T1p ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 0 (-1) ∧ T1m ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 0 1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro t ht
    all_goals
      have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
      simp only [hBp, hBm, hP, hQ, hN, hM, hT0p, hT0m, hT1p, hT1m, map_sub, map_add, map_smul,
        boostAxis_zero, toLorentzGroup_boostXel, boostXel_inv_coe, boostMatX,
        algebraMap_real_complex,
        repLorentzGroup_Dbarψ_nil, repLorentzGroup_Dψ_singleton,
        Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
        Complex.star_def, map_div₀, map_neg, map_inv₀, map_ofNat, map_mul,
        Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_zero, Complex.ofReal_one,
        mul_zero, zero_mul, mul_one, one_mul, zero_smul, smul_zero, add_zero, zero_add]
      push_cast
      match_scalars <;> (field_simp; try ring)
  -- ### B. The six weight-zero bilinears lie in the span of the pairs
  have hSW : Submodule.span ℂ S ≤ W := le_sup_left
  have hpm : ∀ {u v : JetAlgebra}, u + v ∈ S → u - v ∈ S → u ∈ W ∧ v ∈ W := by
    intro u v h₁ h₂
    have e₁ : u + v ∈ W := hSW (Submodule.subset_span h₁)
    have e₂ : u - v ∈ W := hSW (Submodule.subset_span h₂)
    constructor
    · rw [show u = (2⁻¹ : ℂ) • (u + v) + (2⁻¹ : ℂ) • (u - v) from by module]
      exact add_mem (Submodule.smul_mem _ _ e₁) (Submodule.smul_mem _ _ e₂)
    · rw [show v = (2⁻¹ : ℂ) • (u + v) - (2⁻¹ : ℂ) • (u - v) from by module]
      exact sub_mem (Submodule.smul_mem _ _ e₁) (Submodule.smul_mem _ _ e₂)
  obtain ⟨k1, k8⟩ : Bp * P ∈ W ∧ Bm * M ∈ W := hpm (by simp [hS]) (by simp [hS])
  obtain ⟨kx0, kx1⟩ : Bp * T0m ∈ W ∧ Bm * T0p ∈ W := hpm (by simp [hS]) (by simp [hS])
  obtain ⟨ky0, ky1⟩ : Bp * T1m ∈ W ∧ Bm * T1p ∈ W := hpm (by simp [hS]) (by simp [hS])
  -- ### C. Every bilinear splits into eigen bilinears of a single weight
  have hm : ∀ {k l : ℤ} {x y : JetAlgebra}, x ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 0 k →
      y ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 0 l → k + l ≠ 0 → x * y ∈ W := fun hx hy h =>
    Submodule.mem_sup_right (Submodule.mem_iSup_of_mem _
      (Submodule.mem_iSup_of_mem h (BoostWeight.mul_mem repLorentzGroup hx hy)))
  have hbil : ∀ x ∈ Submodule.span ℂ ({Bp, Bm} : Set JetAlgebra),
      ∀ y ∈ Submodule.span ℂ ({P, Q, N, M, T0p, T0m, T1p, T1m} : Set JetAlgebra),
      x * y ∈ W := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem a ha =>
      intro y hy
      induction hy using Submodule.span_induction with
      | mem b hb =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
        rcases ha with rfl | rfl <;>
          rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        exacts [k1, hm hBpw hQw (by norm_num), hm hBpw hNw (by norm_num),
          hm hBpw hMw (by norm_num), hm hBpw hT0pw (by norm_num), kx0,
          hm hBpw hT1pw (by norm_num), ky0,
          hm hBmw hPw (by norm_num), hm hBmw hQw (by norm_num), hm hBmw hNw (by norm_num), k8,
          kx1, hm hBmw hT0mw (by norm_num), ky1, hm hBmw hT1mw (by norm_num)]
      | zero => simp
      | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
      | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hy
    | zero => intro y _; simp
    | add x z _ _ hx hz => intro y hy; rw [add_mul]; exact add_mem (hx y hy) (hz y hy)
    | smul c x _ hx => intro y hy; rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ (hx y hy)
  have hc4 : ∀ (c1 c2 c3 c4 : ℂ) {z : JetAlgebra}, z = c1 • P + c2 • Q + c3 • N + c4 • M →
      z ∈ Submodule.span ℂ ({P, Q, N, M, T0p, T0m, T1p, T1m} : Set JetAlgebra) := by
    rintro c1 c2 c3 c4 z rfl
    exact add_mem (add_mem (add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hc0 : ∀ (c1 c2 : ℂ) {z : JetAlgebra}, z = c1 • T0p + c2 • T0m →
      z ∈ Submodule.span ℂ ({P, Q, N, M, T0p, T0m, T1p, T1m} : Set JetAlgebra) := by
    rintro c1 c2 z rfl
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hc1 : ∀ (c1 c2 : ℂ) {z : JetAlgebra}, z = c1 • T1p + c2 • T1m →
      z ∈ Submodule.span ℂ ({P, Q, N, M, T0p, T0m, T1p, T1m} : Set JetAlgebra) := by
    rintro c1 c2 z rfl
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hkey : Submodule.span ℂ FF ≤ W := by
    rw [hFF]
    refine Submodule.span_le.2 ?_
    rintro x ⟨α, μ, β, rfl⟩
    refine hbil _ ?_ _ ?_
    · rw [Submodule.mem_span_pair]
      match α with
      | 0 => exact ⟨2⁻¹, 2⁻¹, by rw [hBp, hBm]; module⟩
      | 1 => exact ⟨2⁻¹, -2⁻¹, by rw [hBp, hBm]; module⟩
    · match μ, β with
      | Sum.inl 0, 0 => exact hc4 4⁻¹ 4⁻¹ 4⁻¹ 4⁻¹ (by rw [hP, hQ, hN, hM]; module)
      | Sum.inl 0, 1 => exact hc4 4⁻¹ (-4⁻¹) 4⁻¹ (-4⁻¹) (by rw [hP, hQ, hN, hM]; module)
      | Sum.inr 0, 0 => exact hc4 (-4⁻¹) (-4⁻¹) 4⁻¹ 4⁻¹ (by rw [hP, hQ, hN, hM]; module)
      | Sum.inr 0, 1 => exact hc4 (-4⁻¹) 4⁻¹ 4⁻¹ (-4⁻¹) (by rw [hP, hQ, hN, hM]; module)
      | Sum.inr 1, 0 => exact hc0 2⁻¹ 2⁻¹ (by rw [hT0p, hT0m]; module)
      | Sum.inr 1, 1 => exact hc0 2⁻¹ (-2⁻¹) (by rw [hT0p, hT0m]; module)
      | Sum.inr 2, 0 => exact hc1 2⁻¹ 2⁻¹ (by rw [hT1p, hT1m]; module)
      | Sum.inr 2, 1 => exact hc1 2⁻¹ (-2⁻¹) (by rw [hT1p, hT1m]; module)
  -- ### D. The intersection
  have hz : ∀ {k l : ℤ} {x y : JetAlgebra}, x ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 0 k →
      y ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 0 l → k + l = 0 → x * y ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 0 0 := by
    intro k l x y hx hy h
    rw [← h]; exact BoostWeight.mul_mem repLorentzGroup hx hy
  have hSw : Submodule.span ℂ S ≤ BoostWeight.boostWeightSubmodule repLorentzGroup 0 0 := by
    rw [hS]
    refine Submodule.span_le.2 ?_
    rintro x (rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [add_mem (hz hBpw hPw (by norm_num)) (hz hBmw hMw (by norm_num)),
      sub_mem (hz hBpw hPw (by norm_num)) (hz hBmw hMw (by norm_num)),
      add_mem (hz hBpw hT0mw (by norm_num)) (hz hBmw hT0pw (by norm_num)),
      sub_mem (hz hBpw hT0mw (by norm_num)) (hz hBmw hT0pw (by norm_num)),
      add_mem (hz hBpw hT1mw (by norm_num)) (hz hBmw hT1pw (by norm_num)),
      sub_mem (hz hBpw hT1mw (by norm_num)) (hz hBmw hT1pw (by norm_num))]
  have hFm : ∀ α μ β, Dbarψ [] α * Dψ [μ] β ∈ Submodule.span ℂ FF := fun α μ β => by
    rw [hFF]; exact Submodule.subset_span ⟨α, μ, β, rfl⟩
  have hSF : Submodule.span ℂ S ≤ Submodule.span ℂ FF := by
    rw [hS]
    refine Submodule.span_le.2 ?_
    rintro x (rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp only [hBp, hBm, hP, hM, hT0p, hT0m, hT1p, hT1m, mul_sub, mul_add, sub_mul, add_mul,
        mul_smul_comm, smul_mul_assoc] <;>
      repeat' first
        | exact hFm _ _ _
        | apply add_mem
        | apply sub_mem
        | apply neg_mem
  refine le_antisymm (le_trans (inf_le_inf_left _ hkey) ?_) (le_inf hSw hSF)
  rw [hW, inf_comm, sup_inf_assoc_of_le _ hSw,
    disjoint_iff.mp (BoostWeight.boostWeightSubmodule_iSupIndep repLorentzGroup (i := 0) 0).symm, sup_bot_eq]

/-- **The boost weight zero part of the fermion kinetic bilinears, `y`-direction.** As for the
  `x`-boost, but the rotated spinor combinations now carry a factor of `i`: `ψ̄_0 ∓ i ψ̄_1` has
  weight `∓1`, and on `∂_μ ψ_β` the combinations `∂_μ ψ_0 ± i ∂_μ ψ_1` carry the spinor weight
  `∓1`; the light-cone derivative combinations are `∂_0 ∓ ∂_y`, and `∂_x`, `∂_z` are transverse. -/
theorem boostWeight_inter_fermionic_kinetic_term_y :
    BoostWeight.boostWeightSubmodule repLorentzGroup 1 0 ⊓ Submodule.span ℂ
        {x | ∃ α μ β, x = Dbarψ [] α * Dψ [μ] β} =
      Submodule.span ℂ
        {(Dbarψ [] 0 - Complex.I • Dbarψ [] 1) *
              (Dψ [Sum.inl 0] 0 + Complex.I • Dψ [Sum.inl 0] 1 -
                (Dψ [Sum.inr 1] 0 + Complex.I • Dψ [Sum.inr 1] 1)) +
            (Dbarψ [] 0 + Complex.I • Dbarψ [] 1) *
              (Dψ [Sum.inl 0] 0 - Complex.I • Dψ [Sum.inl 0] 1 +
                (Dψ [Sum.inr 1] 0 - Complex.I • Dψ [Sum.inr 1] 1)),
          (Dbarψ [] 0 - Complex.I • Dbarψ [] 1) *
              (Dψ [Sum.inl 0] 0 + Complex.I • Dψ [Sum.inl 0] 1 -
                (Dψ [Sum.inr 1] 0 + Complex.I • Dψ [Sum.inr 1] 1)) -
            (Dbarψ [] 0 + Complex.I • Dbarψ [] 1) *
              (Dψ [Sum.inl 0] 0 - Complex.I • Dψ [Sum.inl 0] 1 +
                (Dψ [Sum.inr 1] 0 - Complex.I • Dψ [Sum.inr 1] 1)),
          (Dbarψ [] 0 - Complex.I • Dbarψ [] 1) *
              (Dψ [Sum.inr 0] 0 - Complex.I • Dψ [Sum.inr 0] 1) +
            (Dbarψ [] 0 + Complex.I • Dbarψ [] 1) *
              (Dψ [Sum.inr 0] 0 + Complex.I • Dψ [Sum.inr 0] 1),
          (Dbarψ [] 0 - Complex.I • Dbarψ [] 1) *
              (Dψ [Sum.inr 0] 0 - Complex.I • Dψ [Sum.inr 0] 1) -
            (Dbarψ [] 0 + Complex.I • Dbarψ [] 1) *
              (Dψ [Sum.inr 0] 0 + Complex.I • Dψ [Sum.inr 0] 1),
          (Dbarψ [] 0 - Complex.I • Dbarψ [] 1) *
              (Dψ [Sum.inr 2] 0 - Complex.I • Dψ [Sum.inr 2] 1) +
            (Dbarψ [] 0 + Complex.I • Dbarψ [] 1) *
              (Dψ [Sum.inr 2] 0 + Complex.I • Dψ [Sum.inr 2] 1),
          (Dbarψ [] 0 - Complex.I • Dbarψ [] 1) *
              (Dψ [Sum.inr 2] 0 - Complex.I • Dψ [Sum.inr 2] 1) -
            (Dbarψ [] 0 + Complex.I • Dbarψ [] 1) *
              (Dψ [Sum.inr 2] 0 + Complex.I • Dψ [Sum.inr 2] 1)} := by
  -- ### A. The boost eigenvectors among the first-order fermion coordinates
  set Bp := Dbarψ [] 0 - Complex.I • Dbarψ [] 1 with hBp
  set Bm := Dbarψ [] 0 + Complex.I • Dbarψ [] 1 with hBm
  set P := Dψ [Sum.inl 0] 0 + Complex.I • Dψ [Sum.inl 0] 1 -
    (Dψ [Sum.inr 1] 0 + Complex.I • Dψ [Sum.inr 1] 1) with hP
  set Q := Dψ [Sum.inl 0] 0 - Complex.I • Dψ [Sum.inl 0] 1 -
    (Dψ [Sum.inr 1] 0 - Complex.I • Dψ [Sum.inr 1] 1) with hQ
  set N := Dψ [Sum.inl 0] 0 + Complex.I • Dψ [Sum.inl 0] 1 +
    (Dψ [Sum.inr 1] 0 + Complex.I • Dψ [Sum.inr 1] 1) with hN
  set M := Dψ [Sum.inl 0] 0 - Complex.I • Dψ [Sum.inl 0] 1 +
    (Dψ [Sum.inr 1] 0 - Complex.I • Dψ [Sum.inr 1] 1) with hM
  set T0p := Dψ [Sum.inr 0] 0 + Complex.I • Dψ [Sum.inr 0] 1 with hT0p
  set T0m := Dψ [Sum.inr 0] 0 - Complex.I • Dψ [Sum.inr 0] 1 with hT0m
  set T1p := Dψ [Sum.inr 2] 0 + Complex.I • Dψ [Sum.inr 2] 1 with hT1p
  set T1m := Dψ [Sum.inr 2] 0 - Complex.I • Dψ [Sum.inr 2] 1 with hT1m
  set FF : Set JetAlgebra := {x | ∃ α μ β, x = Dbarψ [] α * Dψ [μ] β} with hFF
  set S : Set JetAlgebra := {Bp * P + Bm * M, Bp * P - Bm * M, Bp * T0m + Bm * T0p,
    Bp * T0m - Bm * T0p, Bp * T1m + Bm * T1p, Bp * T1m - Bm * T1p} with hS
  set W := Submodule.span ℂ S ⊔ ⨆ (j : ℤ) (_ : j ≠ 0), BoostWeight.boostWeightSubmodule repLorentzGroup 1 j with hW
  obtain ⟨hBpw, hBmw, hPw, hQw, hNw, hMw, hT0pw, hT0mw, hT1pw, hT1mw⟩ :
      Bp ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 1 (-1) ∧ Bm ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 1 1 ∧
      P ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 1 1 ∧ Q ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 1 3 ∧
      N ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 1 (-3) ∧ M ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 1 (-1) ∧
      T0p ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 1 (-1) ∧ T0m ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 1 1 ∧
      T1p ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 1 (-1) ∧ T1m ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 1 1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro t ht
    all_goals
      have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
      simp only [hBp, hBm, hP, hQ, hN, hM, hT0p, hT0m, hT1p, hT1m, map_sub, map_add, map_smul,
        boostAxis_one, toLorentzGroup_boostYel, boostYel_inv_coe, boostMatY,
        algebraMap_real_complex,
        repLorentzGroup_Dbarψ_nil, repLorentzGroup_Dψ_singleton,
        Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
        Complex.star_def, map_div₀, map_neg, map_inv₀, map_ofNat, map_mul,
        Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_zero, Complex.ofReal_one,
        mul_zero, zero_mul, mul_one, one_mul, zero_smul, smul_zero, add_zero, zero_add]
      push_cast
      match_scalars <;> field_simp <;> ring_nf <;> (try simp only [Complex.I_sq]) <;>
        (try ring_nf)
  -- ### B. The six weight-zero bilinears lie in the span of the pairs
  have hSW : Submodule.span ℂ S ≤ W := le_sup_left
  have hpm : ∀ {u v : JetAlgebra}, u + v ∈ S → u - v ∈ S → u ∈ W ∧ v ∈ W := by
    intro u v h₁ h₂
    have e₁ : u + v ∈ W := hSW (Submodule.subset_span h₁)
    have e₂ : u - v ∈ W := hSW (Submodule.subset_span h₂)
    constructor
    · rw [show u = (2⁻¹ : ℂ) • (u + v) + (2⁻¹ : ℂ) • (u - v) from by module]
      exact add_mem (Submodule.smul_mem _ _ e₁) (Submodule.smul_mem _ _ e₂)
    · rw [show v = (2⁻¹ : ℂ) • (u + v) - (2⁻¹ : ℂ) • (u - v) from by module]
      exact sub_mem (Submodule.smul_mem _ _ e₁) (Submodule.smul_mem _ _ e₂)
  obtain ⟨k1, k8⟩ : Bp * P ∈ W ∧ Bm * M ∈ W := hpm (by simp [hS]) (by simp [hS])
  obtain ⟨kx0, kx1⟩ : Bp * T0m ∈ W ∧ Bm * T0p ∈ W := hpm (by simp [hS]) (by simp [hS])
  obtain ⟨ky0, ky1⟩ : Bp * T1m ∈ W ∧ Bm * T1p ∈ W := hpm (by simp [hS]) (by simp [hS])
  -- ### C. Every bilinear splits into eigen bilinears of a single weight
  have hm : ∀ {k l : ℤ} {x y : JetAlgebra}, x ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 1 k →
      y ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 1 l → k + l ≠ 0 → x * y ∈ W := fun hx hy h =>
    Submodule.mem_sup_right (Submodule.mem_iSup_of_mem _
      (Submodule.mem_iSup_of_mem h (BoostWeight.mul_mem repLorentzGroup hx hy)))
  have hbil : ∀ x ∈ Submodule.span ℂ ({Bp, Bm} : Set JetAlgebra),
      ∀ y ∈ Submodule.span ℂ ({P, Q, N, M, T0p, T0m, T1p, T1m} : Set JetAlgebra),
      x * y ∈ W := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem a ha =>
      intro y hy
      induction hy using Submodule.span_induction with
      | mem b hb =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
        rcases ha with rfl | rfl <;>
          rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        exacts [k1, hm hBpw hQw (by norm_num), hm hBpw hNw (by norm_num),
          hm hBpw hMw (by norm_num), hm hBpw hT0pw (by norm_num), kx0,
          hm hBpw hT1pw (by norm_num), ky0,
          hm hBmw hPw (by norm_num), hm hBmw hQw (by norm_num), hm hBmw hNw (by norm_num), k8,
          kx1, hm hBmw hT0mw (by norm_num), ky1, hm hBmw hT1mw (by norm_num)]
      | zero => simp
      | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
      | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hy
    | zero => intro y _; simp
    | add x z _ _ hx hz => intro y hy; rw [add_mul]; exact add_mem (hx y hy) (hz y hy)
    | smul c x _ hx => intro y hy; rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ (hx y hy)
  have hc4 : ∀ (c1 c2 c3 c4 : ℂ) {z : JetAlgebra}, z = c1 • P + c2 • Q + c3 • N + c4 • M →
      z ∈ Submodule.span ℂ ({P, Q, N, M, T0p, T0m, T1p, T1m} : Set JetAlgebra) := by
    rintro c1 c2 c3 c4 z rfl
    exact add_mem (add_mem (add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hc0 : ∀ (c1 c2 : ℂ) {z : JetAlgebra}, z = c1 • T0p + c2 • T0m →
      z ∈ Submodule.span ℂ ({P, Q, N, M, T0p, T0m, T1p, T1m} : Set JetAlgebra) := by
    rintro c1 c2 z rfl
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hc1 : ∀ (c1 c2 : ℂ) {z : JetAlgebra}, z = c1 • T1p + c2 • T1m →
      z ∈ Submodule.span ℂ ({P, Q, N, M, T0p, T0m, T1p, T1m} : Set JetAlgebra) := by
    rintro c1 c2 z rfl
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hkey : Submodule.span ℂ FF ≤ W := by
    rw [hFF]
    refine Submodule.span_le.2 ?_
    rintro x ⟨α, μ, β, rfl⟩
    refine hbil _ ?_ _ ?_
    · rw [Submodule.mem_span_pair]
      match α with
      | 0 => exact ⟨2⁻¹, 2⁻¹, by rw [hBp, hBm]; module⟩
      | 1 =>
        exact ⟨Complex.I / 2, -(Complex.I / 2), by
          rw [hBp, hBm]
          match_scalars <;> ring_nf <;> (try simp only [Complex.I_sq]) <;>
            (try ring_nf)⟩
    · match μ, β with
      | Sum.inl 0, 0 => exact hc4 4⁻¹ 4⁻¹ 4⁻¹ 4⁻¹ (by rw [hP, hQ, hN, hM]; module)
      | Sum.inl 0, 1 =>
        exact hc4 (-(Complex.I / 4)) (Complex.I / 4) (-(Complex.I / 4)) (Complex.I / 4)
          (by rw [hP, hQ, hN, hM]
              match_scalars <;> ring_nf <;> (try simp only [Complex.I_sq]) <;>
                (try ring_nf))
      | Sum.inr 1, 0 => exact hc4 (-4⁻¹) (-4⁻¹) 4⁻¹ 4⁻¹ (by rw [hP, hQ, hN, hM]; module)
      | Sum.inr 1, 1 =>
        exact hc4 (Complex.I / 4) (-(Complex.I / 4)) (-(Complex.I / 4)) (Complex.I / 4)
          (by rw [hP, hQ, hN, hM]
              match_scalars <;> ring_nf <;> (try simp only [Complex.I_sq]) <;>
                (try ring_nf))
      | Sum.inr 0, 0 => exact hc0 2⁻¹ 2⁻¹ (by rw [hT0p, hT0m]; module)
      | Sum.inr 0, 1 =>
        exact hc0 (-(Complex.I / 2)) (Complex.I / 2)
          (by rw [hT0p, hT0m]
              match_scalars <;> ring_nf <;> (try simp only [Complex.I_sq]) <;>
                (try ring_nf))
      | Sum.inr 2, 0 => exact hc1 2⁻¹ 2⁻¹ (by rw [hT1p, hT1m]; module)
      | Sum.inr 2, 1 =>
        exact hc1 (-(Complex.I / 2)) (Complex.I / 2)
          (by rw [hT1p, hT1m]
              match_scalars <;> ring_nf <;> (try simp only [Complex.I_sq]) <;>
                (try ring_nf))
  -- ### D. The intersection
  have hz : ∀ {k l : ℤ} {x y : JetAlgebra}, x ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 1 k →
      y ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 1 l → k + l = 0 → x * y ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 1 0 := by
    intro k l x y hx hy h
    rw [← h]; exact BoostWeight.mul_mem repLorentzGroup hx hy
  have hSw : Submodule.span ℂ S ≤ BoostWeight.boostWeightSubmodule repLorentzGroup 1 0 := by
    rw [hS]
    refine Submodule.span_le.2 ?_
    rintro x (rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [add_mem (hz hBpw hPw (by norm_num)) (hz hBmw hMw (by norm_num)),
      sub_mem (hz hBpw hPw (by norm_num)) (hz hBmw hMw (by norm_num)),
      add_mem (hz hBpw hT0mw (by norm_num)) (hz hBmw hT0pw (by norm_num)),
      sub_mem (hz hBpw hT0mw (by norm_num)) (hz hBmw hT0pw (by norm_num)),
      add_mem (hz hBpw hT1mw (by norm_num)) (hz hBmw hT1pw (by norm_num)),
      sub_mem (hz hBpw hT1mw (by norm_num)) (hz hBmw hT1pw (by norm_num))]
  have hFm : ∀ α μ β, Dbarψ [] α * Dψ [μ] β ∈ Submodule.span ℂ FF := fun α μ β => by
    rw [hFF]; exact Submodule.subset_span ⟨α, μ, β, rfl⟩
  have hSF : Submodule.span ℂ S ≤ Submodule.span ℂ FF := by
    rw [hS]
    refine Submodule.span_le.2 ?_
    rintro x (rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp only [hBp, hBm, hP, hM, hT0p, hT0m, hT1p, hT1m, mul_sub, mul_add, sub_mul, add_mul,
        mul_smul_comm, smul_mul_assoc] <;>
      repeat' first
        | apply add_mem
        | apply sub_mem
        | apply neg_mem
        | apply Submodule.smul_mem
        | exact hFm _ _ _
  refine le_antisymm (le_trans (inf_le_inf_left _ hkey) ?_) (le_inf hSw hSF)
  rw [hW, inf_comm, sup_inf_assoc_of_le _ hSw,
    disjoint_iff.mp (BoostWeight.boostWeightSubmodule_iSupIndep repLorentzGroup (i := 1) 0).symm, sup_bot_eq]

/-- **The fermion kinetic term is the only bilinear of boost weight zero in every direction.**
  An element of the span of the products `ψ̄_α D_μ ψ_β` has boost weight zero along all three
  axes exactly when it is a multiple of `i ψ̄ σ̄^μ D_μ ψ`.

  *Here the proof is not a certificate.* The three one-axis theorems above cut the span of the
  sixteen bilinears down to a six-dimensional space each, and the three sixes have to be
  intersected; the intersection is read off from the coefficients, which is where the linear
  independence of the bilinears (`fermionDual_apply`) enters. The `z`-axis theorem provides the
  six coefficients `a₁, …, a₆`, and five functionals, each a combination of two of the duals
  `fermionDual` chosen to annihilate the `x`- or the `y`-axis span, cut them down to one. -/
lemma boostWeight_inter_fermionic_kinetic_term_full :
    BoostWeight.boostWeightSubmodule repLorentzGroup 0 0 ⊓ BoostWeight.boostWeightSubmodule repLorentzGroup 1 0 ⊓
    BoostWeight.boostWeightSubmodule repLorentzGroup 2 0 ⊓ Submodule.span ℂ {x | ∃ α μ β, x = Dbarψ [] α * Dψ [μ] β} =
        Submodule.span ℂ {fermionKineticTerm} := by
  have hFm : ∀ α μ β, Dbarψ [] α * Dψ [μ] β ∈
      Submodule.span ℂ {x : JetAlgebra | ∃ α μ β, x = Dbarψ [] α * Dψ [μ] β} :=
    fun α μ β => Submodule.subset_span ⟨α, μ, β, rfl⟩
  have hinv : IsInvariant fermionKineticTerm :=
    ⟨repJetGaugeGroupI_fermionKineticTerm, repLorentzGroup_fermionKineticTerm⟩
  refine le_antisymm ?_ ?_
  -- ### A. The three one-axis intersections
  · intro x hx
    rw [Submodule.mem_inf, Submodule.mem_inf, Submodule.mem_inf] at hx
    obtain ⟨⟨⟨hx0, hx1⟩, hx2⟩, hxF⟩ := hx
    have hz := boostWeight_inter_fermionic_kinetic_term.le (Submodule.mem_inf.2 ⟨hx2, hxF⟩)
    have hbx := boostWeight_inter_fermionic_kinetic_term_x.le (Submodule.mem_inf.2 ⟨hx0, hxF⟩)
    have hby := boostWeight_inter_fermionic_kinetic_term_y.le (Submodule.mem_inf.2 ⟨hx1, hxF⟩)
    -- ### B. Pairs of dual functionals annihilating the `x`- and `y`-axis spans
    have hpair : ∀ (c₁ c₂ : ℂ) (q₁ q₂ : Fin 2 × (Fin 1 ⊕ Fin 3) × Fin 2) {T : Set JetAlgebra},
        (∀ s ∈ T, c₁ * fermionDual q₁ s + c₂ * fermionDual q₂ s = 0) →
        ∀ y ∈ Submodule.span ℂ T, c₁ * fermionDual q₁ y + c₂ * fermionDual q₂ y = 0 := by
      intro c₁ c₂ q₁ q₂ T hT y hy
      induction hy using Submodule.span_induction with
      | mem s hs => exact hT s hs
      | zero => simp
      | add u v _ _ hu hv => rw [map_add, map_add]; linear_combination hu + hv
      | smul c u _ hu =>
        rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul]; linear_combination c * hu
    obtain ⟨e1, e2, e3⟩ :
        (-1 : ℂ) * fermionDual (0, Sum.inl 0, 0) x + 1 * fermionDual (1, Sum.inl 0, 1) x = 0 ∧
        (1 : ℂ) * fermionDual (0, Sum.inl 0, 0) x + 1 * fermionDual (0, Sum.inr 0, 1) x = 0 ∧
        (1 : ℂ) * fermionDual (0, Sum.inl 0, 0) x + 1 * fermionDual (1, Sum.inr 0, 0) x = 0 := by
      refine ⟨hpair _ _ _ _ ?_ x hbx, hpair _ _ _ _ ?_ x hbx, hpair _ _ _ _ ?_ x hbx⟩ <;>
        intro s hs <;>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs <;>
        rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [mul_add, add_mul, mul_sub, sub_mul, map_add, map_sub, map_smul, smul_eq_mul,
          smul_mul_assoc, mul_smul_comm, fermionDual_apply] <;>
        simp only [Prod.mk.injEq, reduceCtorEq, Fin.isValue, Fin.reduceEq, and_false, false_and,
          if_false, and_true, true_and, if_true] <;> norm_num [Fin.ext_iff]
    obtain ⟨e4, e5⟩ :
        Complex.I * fermionDual (0, Sum.inl 0, 0) x +
            1 * fermionDual (0, Sum.inr 1, 1) x = 0 ∧
        (-Complex.I) * fermionDual (0, Sum.inl 0, 0) x +
            1 * fermionDual (1, Sum.inr 1, 0) x = 0 := by
      refine ⟨hpair _ _ _ _ ?_ x hby, hpair _ _ _ _ ?_ x hby⟩ <;>
        intro s hs <;>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs <;>
        rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [mul_add, add_mul, mul_sub, sub_mul, map_add, map_sub, map_smul, smul_eq_mul,
          smul_mul_assoc, mul_smul_comm, fermionDual_apply] <;>
        simp only [Prod.mk.injEq, reduceCtorEq, Fin.isValue, Fin.reduceEq, and_false, false_and,
          if_false, and_true, true_and, if_true] <;> norm_num [Fin.ext_iff]
    -- ### C. The six coefficients of the `z`-axis span, and the five relations on them
    rw [Submodule.mem_span_insert] at hz
    obtain ⟨a1, y1, hy1, rfl⟩ := hz
    rw [Submodule.mem_span_insert] at hy1
    obtain ⟨a2, y2, hy2, rfl⟩ := hy1
    rw [Submodule.mem_span_insert] at hy2
    obtain ⟨a3, y3, hy3, rfl⟩ := hy2
    rw [Submodule.mem_span_insert] at hy3
    obtain ⟨a4, y4, hy4, rfl⟩ := hy3
    rw [Submodule.mem_span_insert] at hy4
    obtain ⟨a5, y5, hy5, rfl⟩ := hy4
    obtain ⟨a6, rfl⟩ := Submodule.mem_span_singleton.1 hy5
    simp only [mul_add, mul_sub, add_mul, sub_mul, map_add, map_smul, map_sub, smul_eq_mul,
      fermionDual_apply, Prod.mk.injEq, Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq, Fin.isValue,
      Fin.reduceEq, and_false, false_and, if_false, and_true, true_and, if_true, mul_zero, mul_one,
      add_zero, zero_add, sub_zero, zero_sub] at e1 e2 e3 e4 e5
    -- ### D. One coefficient is left, and it is the kinetic term
    have ha2 : a2 = 0 := by linear_combination -e1 / 2
    have ha4 : a4 = 0 := by linear_combination (e2 - e3) / 2
    have ha3 : a3 = -(a1 + a2) := by linear_combination (e2 + e3) / 2
    have ha5 : a5 = 0 := by linear_combination (e4 + e5) / 2
    have ha6 : a6 = -Complex.I * (a1 + a2) := by linear_combination (e4 - e5) / 2
    subst ha2 ha4 ha5 ha3 ha6
    rw [Submodule.mem_span_singleton]
    refine ⟨-Complex.I * a1, ?_⟩
    rw [fermionKineticTerm_eq]
    simp only [mul_add, mul_sub, add_zero]
    have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq, neg_one_mul]
    match_scalars <;> ring_nf <;> (try simp only [Complex.I_sq, hI3]) <;> (try ring_nf)
  -- ### E. The kinetic term is invariant, hence of weight zero along every axis
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    refine ⟨⟨⟨mem_boostWeightSubmodule_zero_of_isInvariant hinv,
      mem_boostWeightSubmodule_zero_of_isInvariant hinv⟩,
      mem_boostWeightSubmodule_zero_of_isInvariant hinv⟩, ?_⟩
    rw [fermionKineticTerm_eq]
    exact Submodule.smul_mem _ _ (sub_mem (sub_mem (sub_mem
      (add_mem (hFm _ _ _) (hFm _ _ _)) (add_mem (hFm _ _ _) (hFm _ _ _)))
      (Submodule.smul_mem _ _ (sub_mem (hFm _ _ _) (hFm _ _ _))))
      (sub_mem (hFm _ _ _) (hFm _ _ _)))

/-!

## The key theorem

-/

lemma mem_fermionic_kinetic_span_eq_kineticTerm_of_isInvariant {x : JetAlgebra}
    (hx : IsInvariant x) (ht : x ∈ Submodule.span ℂ {y | ∃ α μ β, y = Dbarψ [] α * Dψ [μ] β}) :
    x ∈ Submodule.span ℂ {fermionKineticTerm} := by
  rw [← boostWeight_inter_fermionic_kinetic_term_full]
  exact ⟨⟨⟨mem_boostWeightSubmodule_zero_of_isInvariant hx,
    mem_boostWeightSubmodule_zero_of_isInvariant hx⟩,
    mem_boostWeightSubmodule_zero_of_isInvariant hx⟩, ht⟩

end JetAlgebra

end LeptonGaugeSector

end
