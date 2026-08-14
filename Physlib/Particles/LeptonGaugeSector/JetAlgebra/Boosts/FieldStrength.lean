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
# Relation between field strength and boosts
-/

@[expose] public section

namespace LeptonGaugeSector
open TensorProduct StandardModel Lorentz
open scoped minkowskiMatrix PauliMatrix Pointwise
open Matrix MatrixGroups BoostWeight IsLorentzDeriv

namespace JetAlgebra

/-!

## A. The homogeneous combinations

-/

/-- The scalar action of a real parameter on the jet algebra, in the form the weight condition
  presents it. -/
private lemma algebraMap_real_complex (t : ℝ) : (algebraMap ℝ ℂ) t = ((t : ℝ) : ℂ) := rfl


/-!

## B. Boosts in given directions

-/

/-!

## B.3. Boosts in the z-direction

-/

/-- The light-cone combination `F_{0x} - F_{zx}` has boost weight `2`. -/
lemma fieldStrengthDeriv_lightCone_mem_two :
    fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) -
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 2 2 := by
  intro t ht
  simp only [algebraMap_real_complex]
  have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [map_sub, repLorentzGroup_fieldStrengthDeriv_nil, repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [boostAxis_two, toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ, fieldStrengthDeriv_self,
    mul_zero, mul_one, Complex.ofReal_zero,
    zero_smul, smul_zero, add_zero, zero_add]
  push_cast
  match_scalars <;> (field_simp; ring)

/-- The light-cone combination `F_{0x} + F_{zx}` has boost weight `-2`. -/
lemma fieldStrengthDeriv_lightCone_mem_neg_two :
    fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) +
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 2 (-2) := by
  intro t ht
  simp only [algebraMap_real_complex]
  have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [map_add, repLorentzGroup_fieldStrengthDeriv_nil, repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [boostAxis_two, toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ, fieldStrengthDeriv_self,
    mul_zero, mul_one, Complex.ofReal_zero,
    zero_smul, smul_zero, add_zero, zero_add]
  push_cast
  match_scalars <;> (field_simp; ring)

/-- The transverse component `F_{xy}` has boost weight zero. -/
lemma fieldStrengthDeriv_transverse_mem_zero :
    fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 2 0 := by
  intro t ht
  simp only [algebraMap_real_complex]
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [boostAxis_two, toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ, fieldStrengthDeriv_self,
    mul_zero, mul_one, Complex.ofReal_zero, Complex.ofReal_one,
    zero_smul, smul_zero, add_zero, zero_add]
  match_scalars; norm_num

/-- The light-cone combination `F_{0y} - F_{zy}` has boost weight `2`. -/
lemma fieldStrengthDeriv_lightCone_y_mem_two :
    fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) -
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 2 2 := by
  intro t ht
  simp only [algebraMap_real_complex]
  have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [map_sub, repLorentzGroup_fieldStrengthDeriv_nil, repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [boostAxis_two, toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ, fieldStrengthDeriv_self,
    mul_zero, mul_one, Complex.ofReal_zero,
    zero_smul, smul_zero, add_zero, zero_add]
  push_cast
  match_scalars <;> (field_simp; ring)

/-- The light-cone combination `F_{0y} + F_{zy}` has boost weight `-2`. -/
lemma fieldStrengthDeriv_lightCone_y_mem_neg_two :
    fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) +
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 2 (-2) := by
  intro t ht
  simp only [algebraMap_real_complex]
  have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [map_add, repLorentzGroup_fieldStrengthDeriv_nil, repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [boostAxis_two, toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ, fieldStrengthDeriv_self,
    mul_zero, mul_one, Complex.ofReal_zero,
    zero_smul, smul_zero, add_zero, zero_add]
  push_cast
  match_scalars <;> (field_simp; ring)

/-- The component along the boost, `F_{0z}`, has boost weight zero: the boost acts on the two
  indices by inverse scalings, which cancel. -/
lemma fieldStrengthDeriv_longitudinal_mem_zero :
    fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 2 0 := by
  intro t ht
  simp only [algebraMap_real_complex]
  have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [boostAxis_two, toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ, fieldStrengthDeriv_self, fieldStrengthDeriv_inr_inl,
    mul_zero, Complex.ofReal_zero,
    zero_smul, smul_zero, add_zero, zero_add]
  push_cast
  match_scalars <;> (field_simp; ring)

lemma fieldStrengthDeriv_nil_span_le_decompose_boostWeight_z :
    Submodule.span ℂ {y | ∃ μ ν, y = fieldStrengthDeriv {} μ ν} ≤
    Submodule.span ℂ {fieldStrengthDeriv 0 (Sum.inl 0) (Sum.inr 2),
      fieldStrengthDeriv 0 (Sum.inr 0) (Sum.inr 1),
      fieldStrengthDeriv 0 (Sum.inl 0) (Sum.inr 1) - fieldStrengthDeriv 0 (Sum.inr 2) (Sum.inr 1),
      fieldStrengthDeriv 0 (Sum.inl 0) (Sum.inr 0) - fieldStrengthDeriv 0 (Sum.inr 2) (Sum.inr 0),
      fieldStrengthDeriv 0 (Sum.inl 0) (Sum.inr 1) + fieldStrengthDeriv 0 (Sum.inr 2) (Sum.inr 1),
      fieldStrengthDeriv 0 (Sum.inl 0) (Sum.inr 0) +
        fieldStrengthDeriv 0 (Sum.inr 2) (Sum.inr 0)} := by
  rw [Submodule.span_le]
  rintro _ ⟨μ, ν, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_span_insert, Submodule.mem_span_singleton]
  match μ, ν with
  | Sum.inl 0, Sum.inl 0 | Sum.inr 0, Sum.inr 0 | Sum.inr 1, Sum.inr 1 | Sum.inr 2, Sum.inr 2 =>
    exact ⟨0, _, ⟨0, _, ⟨0, _, ⟨0, _, ⟨0, _, ⟨0, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, by simp⟩
  | Sum.inl 0, Sum.inr 0 =>
    exact ⟨0, _, ⟨0, _, ⟨0, _, ⟨2⁻¹, _, ⟨0, _, ⟨2⁻¹, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, by module⟩
  | Sum.inl 0, Sum.inr 1 =>
    exact ⟨0, _, ⟨0, _, ⟨2⁻¹, _, ⟨0, _, ⟨2⁻¹, _, ⟨0, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, by module⟩
  | Sum.inl 0, Sum.inr 2 =>
    exact ⟨1, _, ⟨0, _, ⟨0, _, ⟨0, _, ⟨0, _, ⟨0, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, by module⟩
  | Sum.inr 0, Sum.inl 0 =>
    exact ⟨0, _, ⟨0, _, ⟨0, _, ⟨-2⁻¹, _, ⟨0, _, ⟨-2⁻¹, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, by
      rw [fieldStrengthDeriv_antisymm]; module⟩
  | Sum.inr 0, Sum.inr 1 =>
    exact ⟨0, _, ⟨1, _, ⟨0, _, ⟨0, _, ⟨0, _, ⟨0, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, by module⟩
  | Sum.inr 0, Sum.inr 2 =>
    exact ⟨0, _, ⟨0, _, ⟨0, _, ⟨2⁻¹, _, ⟨0, _, ⟨-2⁻¹, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, by
      rw [fieldStrengthDeriv_antisymm]; module⟩
  | Sum.inr 1, Sum.inl 0 =>
    exact ⟨0, _, ⟨0, _, ⟨-2⁻¹, _, ⟨0, _, ⟨-2⁻¹, _, ⟨0, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, by
      rw [fieldStrengthDeriv_antisymm]; module⟩
  | Sum.inr 1, Sum.inr 0 =>
    exact ⟨0, _, ⟨-1, _, ⟨0, _, ⟨0, _, ⟨0, _, ⟨0, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, by
      rw [fieldStrengthDeriv_antisymm]; module⟩
  | Sum.inr 1, Sum.inr 2 =>
    exact ⟨0, _, ⟨0, _, ⟨2⁻¹, _, ⟨0, _, ⟨-2⁻¹, _, ⟨0, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, by
      rw [fieldStrengthDeriv_antisymm]; module⟩
  | Sum.inr 2, Sum.inl 0 =>
    exact ⟨-1, _, ⟨0, _, ⟨0, _, ⟨0, _, ⟨0, _, ⟨0, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, by
      rw [fieldStrengthDeriv_antisymm]; module⟩
  | Sum.inr 2, Sum.inr 0 =>
    exact ⟨0, _, ⟨0, _, ⟨0, _, ⟨-2⁻¹, _, ⟨0, _, ⟨2⁻¹, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, by module⟩
  | Sum.inr 2, Sum.inr 1 =>
    exact ⟨0, _, ⟨0, _, ⟨-2⁻¹, _, ⟨0, _, ⟨2⁻¹, _, ⟨0, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, by module⟩

/-- **The field strengths, organised by `z`-boost weight.** The span of the `F_{μν}` is the sup
  of its weight-zero, weight-two and weight-minus-two pieces. -/
lemma fieldStrengthDeriv_nil_span_eq_sup_boostWeight_z :
    Submodule.span ℂ {y | ∃ μ ν, y = fieldStrengthDeriv {} μ ν} =
      Submodule.span ℂ {fieldStrengthDeriv 0 (Sum.inl 0) (Sum.inr 2),
        fieldStrengthDeriv 0 (Sum.inr 0) (Sum.inr 1)} ⊔
      Submodule.span ℂ {fieldStrengthDeriv 0 (Sum.inl 0) (Sum.inr 1) -
          fieldStrengthDeriv 0 (Sum.inr 2) (Sum.inr 1),
        fieldStrengthDeriv 0 (Sum.inl 0) (Sum.inr 0) -
          fieldStrengthDeriv 0 (Sum.inr 2) (Sum.inr 0)} ⊔
      Submodule.span ℂ {fieldStrengthDeriv 0 (Sum.inl 0) (Sum.inr 1) +
          fieldStrengthDeriv 0 (Sum.inr 2) (Sum.inr 1),
        fieldStrengthDeriv 0 (Sum.inl 0) (Sum.inr 0) +
          fieldStrengthDeriv 0 (Sum.inr 2) (Sum.inr 0)} := by
  refine le_antisymm (fieldStrengthDeriv_nil_span_le_decompose_boostWeight_z.trans ?_) ?_
  · rw [Submodule.span_le]
    rintro _ (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span (by simp)))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span (by simp)))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span (by simp)))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span (by simp)))
    · exact Submodule.mem_sup_right (Submodule.subset_span (by simp))
    · exact Submodule.mem_sup_right (Submodule.subset_span (by simp))
  · refine sup_le (sup_le ?_ ?_) ?_ <;> refine Submodule.span_le.2 ?_ <;> rintro _ (rfl | rfl)
    · exact Submodule.subset_span ⟨_, _, rfl⟩
    · exact Submodule.subset_span ⟨_, _, rfl⟩
    · exact sub_mem (Submodule.subset_span ⟨_, _, rfl⟩) (Submodule.subset_span ⟨_, _, rfl⟩)
    · exact sub_mem (Submodule.subset_span ⟨_, _, rfl⟩) (Submodule.subset_span ⟨_, _, rfl⟩)
    · exact add_mem (Submodule.subset_span ⟨_, _, rfl⟩) (Submodule.subset_span ⟨_, _, rfl⟩)
    · exact add_mem (Submodule.subset_span ⟨_, _, rfl⟩) (Submodule.subset_span ⟨_, _, rfl⟩)

/-- The longitudinal and transverse components span a subspace of `z`-boost weight zero. -/
lemma fieldStrengthDeriv_span_pair_zero_le :
    Submodule.span ℂ {fieldStrengthDeriv 0 (Sum.inl 0) (Sum.inr 2),
      fieldStrengthDeriv 0 (Sum.inr 0) (Sum.inr 1)} ≤ BoostWeight.boostWeightSubmodule repLorentzGroup 2 0 :=
  Submodule.span_le.2 (by
    rintro _ (rfl | rfl)
    exacts [fieldStrengthDeriv_longitudinal_mem_zero, fieldStrengthDeriv_transverse_mem_zero])

/-- The two light-cone differences span a subspace of `z`-boost weight two. -/
lemma fieldStrengthDeriv_span_pair_two_le :
    Submodule.span ℂ {fieldStrengthDeriv 0 (Sum.inl 0) (Sum.inr 1) -
        fieldStrengthDeriv 0 (Sum.inr 2) (Sum.inr 1),
      fieldStrengthDeriv 0 (Sum.inl 0) (Sum.inr 0) -
        fieldStrengthDeriv 0 (Sum.inr 2) (Sum.inr 0)} ≤ BoostWeight.boostWeightSubmodule repLorentzGroup 2 2 :=
  Submodule.span_le.2 (by
    rintro _ (rfl | rfl)
    exacts [fieldStrengthDeriv_lightCone_y_mem_two, fieldStrengthDeriv_lightCone_mem_two])

/-- The two light-cone sums span a subspace of `z`-boost weight minus two. -/
lemma fieldStrengthDeriv_span_pair_neg_two_le :
    Submodule.span ℂ {fieldStrengthDeriv 0 (Sum.inl 0) (Sum.inr 1) +
        fieldStrengthDeriv 0 (Sum.inr 2) (Sum.inr 1),
      fieldStrengthDeriv 0 (Sum.inl 0) (Sum.inr 0) +
        fieldStrengthDeriv 0 (Sum.inr 2) (Sum.inr 0)} ≤ BoostWeight.boostWeightSubmodule repLorentzGroup 2 (-2) :=
  Submodule.span_le.2 (by
    rintro _ (rfl | rfl)
    exacts [fieldStrengthDeriv_lightCone_y_mem_neg_two, fieldStrengthDeriv_lightCone_mem_neg_two])

lemma boostProj_z_zero_map_fieldStrengthDeriv_span :
    Submodule.map (BoostWeight.boostProj repLorentzGroup 2 0) (Submodule.span ℂ {y | ∃ μ ν, y = fieldStrengthDeriv {} μ ν}) =
      Submodule.span ℂ {fieldStrengthDeriv 0 (Sum.inl 0) (Sum.inr 2),
        fieldStrengthDeriv 0 (Sum.inr 0) (Sum.inr 1)} := by
  rw [fieldStrengthDeriv_nil_span_eq_sup_boostWeight_z, Submodule.map_sup, Submodule.map_sup,
    BoostWeight.map_boostProj_of_le repLorentzGroup fieldStrengthDeriv_span_pair_zero_le,
    BoostWeight.map_boostProj_of_le_ne repLorentzGroup fieldStrengthDeriv_span_pair_two_le (by decide),
    BoostWeight.map_boostProj_of_le_ne repLorentzGroup fieldStrengthDeriv_span_pair_neg_two_le (by decide),
    sup_bot_eq, sup_bot_eq]

lemma boostProj_z_two_map_fieldStrengthDeriv_span :
    Submodule.map (BoostWeight.boostProj repLorentzGroup 2 2) (Submodule.span ℂ {y | ∃ μ ν, y = fieldStrengthDeriv {} μ ν}) =
      Submodule.span ℂ {fieldStrengthDeriv 0 (Sum.inl 0) (Sum.inr 1) -
          fieldStrengthDeriv 0 (Sum.inr 2) (Sum.inr 1),
        fieldStrengthDeriv 0 (Sum.inl 0) (Sum.inr 0) -
          fieldStrengthDeriv 0 (Sum.inr 2) (Sum.inr 0)} := by
  rw [fieldStrengthDeriv_nil_span_eq_sup_boostWeight_z, Submodule.map_sup, Submodule.map_sup,
    BoostWeight.map_boostProj_of_le_ne repLorentzGroup fieldStrengthDeriv_span_pair_zero_le (by decide),
    BoostWeight.map_boostProj_of_le repLorentzGroup fieldStrengthDeriv_span_pair_two_le,
    BoostWeight.map_boostProj_of_le_ne repLorentzGroup fieldStrengthDeriv_span_pair_neg_two_le (by decide),
    bot_sup_eq, sup_bot_eq]

lemma boostProj_z_neg_two_map_fieldStrengthDeriv_span :
    Submodule.map (BoostWeight.boostProj repLorentzGroup 2 (-2))
      (Submodule.span ℂ {y | ∃ μ ν, y = fieldStrengthDeriv {} μ ν}) =
      Submodule.span ℂ {fieldStrengthDeriv 0 (Sum.inl 0) (Sum.inr 1) +
          fieldStrengthDeriv 0 (Sum.inr 2) (Sum.inr 1),
        fieldStrengthDeriv 0 (Sum.inl 0) (Sum.inr 0) +
          fieldStrengthDeriv 0 (Sum.inr 2) (Sum.inr 0)} := by
  rw [fieldStrengthDeriv_nil_span_eq_sup_boostWeight_z, Submodule.map_sup, Submodule.map_sup,
    BoostWeight.map_boostProj_of_le_ne repLorentzGroup fieldStrengthDeriv_span_pair_zero_le (by decide),
    BoostWeight.map_boostProj_of_le_ne repLorentzGroup fieldStrengthDeriv_span_pair_two_le (by decide),
    BoostWeight.map_boostProj_of_le repLorentzGroup fieldStrengthDeriv_span_pair_neg_two_le,
    sup_bot_eq, bot_sup_eq]

/-- Away from the weights `0`, `±2` the projection of the field-strength span vanishes. -/
lemma boostProj_z_map_fieldStrengthDeriv_span_of_ne (k : ℤ) (h0 : k ≠ 0) (h2 : k ≠ 2)
    (hn2 : k ≠ -2) :
    Submodule.map (BoostWeight.boostProj repLorentzGroup 2 k)
      (Submodule.span ℂ {y | ∃ μ ν, y = fieldStrengthDeriv {} μ ν}) = ⊥ := by
  rw [fieldStrengthDeriv_nil_span_eq_sup_boostWeight_z, Submodule.map_sup, Submodule.map_sup,
    BoostWeight.map_boostProj_of_le_ne repLorentzGroup fieldStrengthDeriv_span_pair_zero_le (Ne.symm h0),
    BoostWeight.map_boostProj_of_le_ne repLorentzGroup fieldStrengthDeriv_span_pair_two_le (Ne.symm h2),
    BoostWeight.map_boostProj_of_le_ne repLorentzGroup fieldStrengthDeriv_span_pair_neg_two_le (Ne.symm hn2),
    sup_bot_eq, sup_bot_eq]

/-!

## The Kinetic terms

-/

lemma fieldStrengthDeriv_mul_span_eq_mul_span :
    Submodule.span ℂ {y | ∃ μ ν μ' ν', y = fieldStrengthDeriv {} μ ν *
    fieldStrengthDeriv {} μ' ν'} = Submodule.span ℂ {y | ∃ μ ν, y = fieldStrengthDeriv {} μ ν} *
    Submodule.span ℂ {y | ∃ μ ν, y = fieldStrengthDeriv {} μ ν} := by
  rw [Submodule.span_mul_span]
  refine Submodule.span_eq_span ?_ ?_
  · rintro _ ⟨μ, ν, μ', ν', rfl⟩
    apply Submodule.mem_span_of_mem
    refine Set.mul_mem_mul ?_ ?_
    · refine Set.mem_setOf.mpr ?_
      exact ⟨μ, ν, rfl⟩
    · refine Set.mem_setOf.mpr ?_
      exact ⟨μ', ν', rfl⟩
  · rintro _ ⟨u, ⟨μ, ν, rfl⟩, v, ⟨μ', ν', rfl⟩, rfl⟩
    apply Submodule.mem_span_of_mem
    refine Set.mem_setOf.mpr ?_
    exact ⟨μ, ν, μ', ν', rfl⟩

TODO "Generalize the below result for any axis"

/-- Every weight projection of the field-strength span stays inside the span. -/
lemma boostProj_z_map_fieldStrengthDeriv_span_le (l : ℤ) :
    (Submodule.span ℂ {y | ∃ μ ν, y = fieldStrengthDeriv {} μ ν}).map (BoostWeight.boostProj repLorentzGroup 2 l) ≤
    Submodule.span ℂ {y | ∃ μ ν, y = fieldStrengthDeriv {} μ ν} := by
  have hd : Submodule.span ℂ {y | ∃ μ ν, y = fieldStrengthDeriv {} μ ν} = _ ⊔ _ ⊔ _ :=
    fieldStrengthDeriv_nil_span_eq_sup_boostWeight_z
  by_cases h0 : l = 0
  · subst h0
    rw [boostProj_z_zero_map_fieldStrengthDeriv_span, hd]
    exact le_sup_left.trans le_sup_left
  by_cases h2 : l = 2
  · subst h2
    rw [boostProj_z_two_map_fieldStrengthDeriv_span, hd]
    exact le_sup_right.trans le_sup_left
  by_cases hn2 : l = -2
  · subst hn2
    rw [boostProj_z_neg_two_map_fieldStrengthDeriv_span, hd]
    exact le_sup_right
  · rw [boostProj_z_map_fieldStrengthDeriv_span_of_ne l h0 h2 hn2]
    exact bot_le

lemma boostProj_z_map_fieldStrengthDeriv_mul_eq_boosts :
  let V0 := Submodule.span ℂ {y | ∃ μ ν, y = fieldStrengthDeriv {} μ ν}
  let V2 := (Submodule.span ℂ {y | ∃ μ ν μ' ν', y = fieldStrengthDeriv {} μ ν *
    fieldStrengthDeriv {} μ' ν'})
  V2.map (BoostWeight.boostProj repLorentzGroup 2 0) = V0.map (BoostWeight.boostProj repLorentzGroup 2 0) * V0.map (BoostWeight.boostProj repLorentzGroup 2 0)
  + V0.map (BoostWeight.boostProj repLorentzGroup 2 2) * V0.map (BoostWeight.boostProj repLorentzGroup 2 (-2)) := by
  intro V0 V2
  have hcl : ∀ l : ℤ, V0.map (BoostWeight.boostProj repLorentzGroup 2 l) ≤ V0 :=
    boostProj_z_map_fieldStrengthDeriv_span_le
  have hbot : ∀ l : ℤ, l ≠ 0 → l ≠ 2 → l ≠ -2 →
      V0.map (BoostWeight.boostProj repLorentzGroup 2 l) * V0.map (BoostWeight.boostProj repLorentzGroup 2 (0 - l)) = ⊥ := by
    intro l h0 h2 hn2
    rw [show V0.map (BoostWeight.boostProj repLorentzGroup 2 l) = ⊥ from
      boostProj_z_map_fieldStrengthDeriv_span_of_ne l h0 h2 hn2, Submodule.bot_mul]
  have hbos : V0.map (BoostWeight.boostProj repLorentzGroup 2 (-2)) ≤ bosonic := by
    rw [show V0.map (BoostWeight.boostProj repLorentzGroup 2 (-2)) = _ from boostProj_z_neg_two_map_fieldStrengthDeriv_span]
    refine Submodule.span_le.2 ?_
    rintro _ (rfl | rfl) <;>
      exact add_mem (fieldStrengthDeriv_mem_bosonic _ _ _) (fieldStrengthDeriv_mem_bosonic _ _ _)
  have hV2 : V2 = V0 * V0 := fieldStrengthDeriv_mul_span_eq_mul_span
  rw [hV2, BoostWeight.boostProj_map_mul repLorentzGroup 0 hcl hcl,
    BoostWeight.iSup_eq_sup_zero_two_neg_two _ hbot]
  simp only [sub_self, zero_sub, neg_neg]
  rw [Submodule.add_eq_sup, mul_comm_of_le_bosonic hbos, sup_assoc, sup_idem]

/-- The weight-zero projection keeps the photon-pair span inside itself. -/
lemma boostProj_z_map_fieldStrengthDeriv_mul_span_le :
    (Submodule.span ℂ {y | ∃ μ ν μ' ν', y = fieldStrengthDeriv {} μ ν *
      fieldStrengthDeriv {} μ' ν'}).map (BoostWeight.boostProj repLorentzGroup 2 0) ≤
    Submodule.span ℂ {y | ∃ μ ν μ' ν', y = fieldStrengthDeriv {} μ ν *
      fieldStrengthDeriv {} μ' ν'} := by
  have hmul : _ = _ := boostProj_z_map_fieldStrengthDeriv_mul_eq_boosts
  rw [hmul, fieldStrengthDeriv_mul_span_eq_mul_span, Submodule.add_eq_sup]
  exact sup_le
    (Submodule.mul_le.2 fun a ha b hb => Submodule.mul_mem_mul
      (boostProj_z_map_fieldStrengthDeriv_span_le 0 ha)
      (boostProj_z_map_fieldStrengthDeriv_span_le 0 hb))
    (Submodule.mul_le.2 fun a ha b hb => Submodule.mul_mem_mul
      (boostProj_z_map_fieldStrengthDeriv_span_le 2 ha)
      (boostProj_z_map_fieldStrengthDeriv_span_le (-2) hb))

/-!

## The double derivative terms.

-/
lemma fieldStrengthDeriv_two_deriv_eq_map_span :
    Submodule.span ℂ {y | ∃ α β μ ν, y = fieldStrengthDeriv {α, β} μ ν} =
    ∑ α, (∑ β, (Submodule.span ℂ {y | ∃ μ ν, y = fieldStrengthDeriv {} μ ν}).map (jetDeriv β)).map
    (jetDeriv α) := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨α, β, μ, ν, rfl⟩
    rw [fieldStrengthDeriv_pair_eq_jetDeriv]
    exact Finset.single_le_sum (f := fun γ =>
        (∑ δ, (Submodule.span ℂ {y | ∃ μ ν, y = fieldStrengthDeriv {} μ ν}).map
          (jetDeriv δ)).map (jetDeriv γ))
      (fun i _ => by rw [Submodule.zero_eq_bot]; exact bot_le) (Finset.mem_univ α)
      (Submodule.mem_map_of_mem
        (Finset.single_le_sum (f := fun δ =>
            (Submodule.span ℂ {y | ∃ μ ν, y = fieldStrengthDeriv {} μ ν}).map (jetDeriv δ))
          (fun i _ => by rw [Submodule.zero_eq_bot]; exact bot_le) (Finset.mem_univ β)
          (Submodule.mem_map_of_mem (Submodule.subset_span ⟨μ, ν, rfl⟩))))
  · refine Finset.sum_induction _ (· ≤ _) (fun a b ha hb => ?_) ?_ fun γ _ => ?_
    · rw [Submodule.add_eq_sup]
      exact sup_le ha hb
    · rw [Submodule.zero_eq_bot]
      exact bot_le
    · rw [Submodule.map_le_iff_le_comap]
      refine Finset.sum_induction _ (· ≤ _) (fun a b ha hb => ?_) ?_ fun δ _ => ?_
      · rw [Submodule.add_eq_sup]
        exact sup_le ha hb
      · rw [Submodule.zero_eq_bot]
        exact bot_le
      · rw [← Submodule.map_le_iff_le_comap, Submodule.map_span, Submodule.map_span,
          Submodule.span_le]
        rintro _ ⟨_, ⟨_, ⟨μ, ν, rfl⟩, rfl⟩, rfl⟩
        exact Submodule.subset_span
          ⟨γ, δ, μ, ν, (fieldStrengthDeriv_pair_eq_jetDeriv γ δ μ ν).symm⟩

/-- **The weight-zero part of the twice-differentiated field strengths.** Projecting the span
  of the `F_{{α,β}μν}` onto `z`-boost weight zero redistributes the two derivatives into the
  light-cone combinations `∂_0 ∓ ∂_z`, which shift the weight by `±2`, and the transverse
  derivatives `∂_x`, `∂_y`, which preserve it, applied to the weight-`0`, `±2` parts of the
  span of the `F_{μν}` so that the total weight vanishes. Both orders of each pair of
  derivatives appear separately: no commutation of derivatives is used. -/
lemma boostProj_z_map_fieldStrengthDeriv_jetDeriv_span_eq :
    let D2V0 := Submodule.span ℂ {y | ∃ α β μ ν, y = fieldStrengthDeriv {α, β} μ ν}
    let V0 := Submodule.span ℂ {y | ∃ μ ν, y = fieldStrengthDeriv {} μ ν}
    D2V0.map (boostProj repLorentzGroup 2 0) =
      ((V0.map (boostProj repLorentzGroup 2 0)).map
        (lightConePlus jetDeriv 2)).map
        (lightConeMinus jetDeriv 2)
    + ((V0.map (boostProj repLorentzGroup 2 (-2))).map
        (lightConePlus jetDeriv 2)).map (jetDeriv (Sum.inr 0))
    + ((V0.map (boostProj repLorentzGroup 2 (-2))).map
        (lightConePlus jetDeriv 2)).map (jetDeriv (Sum.inr 1))
    + ((V0.map (boostProj repLorentzGroup 2 0)).map
        (lightConeMinus jetDeriv 2)).map
        (lightConePlus jetDeriv 2)
    + ((V0.map (boostProj repLorentzGroup 2 2)).map
        (lightConeMinus jetDeriv 2)).map (jetDeriv (Sum.inr 0))
    + ((V0.map (boostProj repLorentzGroup 2 2)).map
        (lightConeMinus jetDeriv 2)).map (jetDeriv (Sum.inr 1))
    + ((V0.map (boostProj repLorentzGroup 2 (-2))).map (jetDeriv (Sum.inr 0))).map
        (lightConePlus jetDeriv 2)
    + ((V0.map (boostProj repLorentzGroup 2 2)).map (jetDeriv (Sum.inr 0))).map
        (lightConeMinus jetDeriv 2)
    + ((V0.map (boostProj repLorentzGroup 2 0)).map (jetDeriv (Sum.inr 0))).map
        (jetDeriv (Sum.inr 0))
    + ((V0.map (boostProj repLorentzGroup 2 0)).map (jetDeriv (Sum.inr 0))).map
        (jetDeriv (Sum.inr 1))
    + ((V0.map (boostProj repLorentzGroup 2 (-2))).map (jetDeriv (Sum.inr 1))).map
        (lightConePlus jetDeriv 2)
    + ((V0.map (boostProj repLorentzGroup 2 2)).map (jetDeriv (Sum.inr 1))).map
        (lightConeMinus jetDeriv 2)
    + ((V0.map (boostProj repLorentzGroup 2 0)).map (jetDeriv (Sum.inr 1))).map
        (jetDeriv (Sum.inr 0))
    + ((V0.map (boostProj repLorentzGroup 2 0)).map (jetDeriv (Sum.inr 1))).map
        (jetDeriv (Sum.inr 1)) := by
  intro D2V0 V0
  have hbot : ∀ k : ℤ, k ≠ 0 → k ≠ 2 → k ≠ -2 →
      V0.map (BoostWeight.boostProj repLorentzGroup 2 k) = ⊥ :=
    boostProj_z_map_fieldStrengthDeriv_span_of_ne
  rw [show D2V0 = ∑ α, (∑ β, V0.map (jetDeriv β)).map (jetDeriv α) from
    fieldStrengthDeriv_two_deriv_eq_map_span]
  simp only [IsLorentzDeriv.boostProj_map_deriv_map_submodule,
    show (2 + 1 : Fin 3) = 0 from rfl, show (2 + 2 : Fin 3) = 1 from rfl,
    show (0 : ℤ) - 2 = -2 from by decide, show (0 : ℤ) + 2 = 2 from by decide,
    show (-2 : ℤ) - 2 = -4 from by decide, show (-2 : ℤ) + 2 = 0 from by decide,
    show (2 : ℤ) - 2 = 0 from by decide, show (2 : ℤ) + 2 = 4 from by decide]
  rw [hbot (-4) (by decide) (by decide) (by decide),
    hbot 4 (by decide) (by decide) (by decide)]
  simp only [Submodule.map_bot, Submodule.add_eq_sup, Submodule.map_sup, bot_sup_eq,
    sup_bot_eq]
  simp only [← Submodule.add_eq_sup]
  abel

lemma boostProj_z_map_fieldStrengthDeriv_jetDeriv_span_le :
    (Submodule.span ℂ {y | ∃ α β μ ν, y = fieldStrengthDeriv {α, β} μ ν}).map
    (BoostWeight.boostProj repLorentzGroup 2 0) ≤
    Submodule.span ℂ {y | ∃ α β μ ν, y = fieldStrengthDeriv {α, β} μ ν} := by
  sorry



end JetAlgebra

end LeptonGaugeSector

end
