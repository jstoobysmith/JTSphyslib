/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Mathematics.Distribution.OfFunction
public import Physlib.SpaceAndTime.SpaceTime.TimeSlice

/-!

# Lifting functions on spacetime to distributions

A function `f : SpaceTime d → M` is lifted to a distribution on spacetime in the same way as the
distributions of `Physlib.Electromagnetism.Current.InfiniteWire` and of the point particle are
built: it is written in the coordinates `Time × Space d`, turned into a distribution there by
integration, and transported back to spacetime with `distTimeSlice`. Functions which are not
tempered integrable cannot be lifted, and are sent to `0`.

With this convention the lift pairs with a test function through the measure on `Time × Space d`,
which is `c⁻¹` times the volume on spacetime.

## Main results

- `SpaceTime.lift` : the distribution of a function on spacetime, `0` on junk values.
- `SpaceTime.isTemperedIntegrable_timeSlice` : a tempered integrable function on spacetime is
  tempered integrable in the coordinates `Time × Space d`.
- `SpaceTime.lift_apply` : the lift of a tempered integrable function pairs with a test
  function by integration over spacetime.

## Contents

- A. Tempered integrability in time and space coordinates
- B. The lift

-/

@[expose] public section

open MeasureTheory SchwartzMap Physlib Physlib.Distribution
open scoped SchwartzMap

namespace SpaceTime

variable {d : ℕ} {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M]

/-!

## A. Tempered integrability in time and space coordinates

-/

lemma one_add_norm_symm_le (c : SpeedOfLight) (p : Time × Space d) :
    1 + ‖(toTimeAndSpace c).symm p‖ ≤
      max 1 ‖(toTimeAndSpace (d := d) c).symm.toContinuousLinearMap‖ * (1 + ‖p‖) := by
  have h := (toTimeAndSpace (d := d) c).symm.toContinuousLinearMap.le_opNorm p
  have h1 := le_max_left 1 ‖(toTimeAndSpace (d := d) c).symm.toContinuousLinearMap‖
  have h2 := le_max_right 1 ‖(toTimeAndSpace (d := d) c).symm.toContinuousLinearMap‖
  have hp := norm_nonneg p
  simp only [ContinuousLinearEquiv.coe_coe] at h
  nlinarith

/-- A tempered integrable function on spacetime is tempered integrable in the coordinates
`Time × Space d`. -/
lemma isTemperedIntegrable_timeSlice (c : SpeedOfLight) {f : SpaceTime d → M}
    (hf : IsTemperedIntegrable f) :
    IsTemperedIntegrable (fun p : Time × Space d => f ((toTimeAndSpace c).symm p)) := by
  obtain ⟨k, hk⟩ := hf
  refine ⟨k, ?_⟩
  set L := max 1 ‖(toTimeAndSpace (d := d) c).symm.toContinuousLinearMap‖
  have hk' := (spaceTime_integrable_iff_space_time_integrable c _).mp hk
  have h := hk'.bdd_smul (φ := fun p : Time × Space d =>
      (1 + ‖(toTimeAndSpace c).symm p‖) ^ k * ((1 + ‖p‖) ^ k)⁻¹) (L ^ k)
    ((((continuous_const.add (toTimeAndSpace (d := d) c).symm.continuous.norm).pow k).mul
      (((continuous_const.add continuous_norm).pow k).inv₀ fun p =>
        pow_ne_zero _ (add_pos_of_pos_of_nonneg one_pos (norm_nonneg p)).ne')
      ).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun p => ?_)
  · refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    have h1 : (1 + ‖(toTimeAndSpace (d := d) c).symm p‖) ^ k ≠ 0 := by positivity
    simp only [Pi.smul_apply', Function.comp_apply, smul_smul]
    congr 1
    field_simp
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← div_eq_mul_inv,
      div_le_iff₀ (by positivity), ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (one_add_norm_symm_le c p) k

/-!

## B. The lift

-/

/-- The distribution on spacetime of a function `f : SpaceTime d → M`, built in the coordinates
`Time × Space d` as for the distributions of the thin wire and the point particle. It is `0`
when `f` cannot be lifted, that is when `f` is not tempered integrable in these coordinates. -/
noncomputable def lift (c : SpeedOfLight) (f : SpaceTime d → M) : (SpaceTime d) →d[ℝ] M :=
  (distTimeSlice c).symm (ofFunction fun p : Time × Space d => f ((toTimeAndSpace c).symm p))

lemma lift_apply_timeSlice (c : SpeedOfLight) {f : SpaceTime d → M}
    (hf : IsTemperedIntegrable f) (ε : 𝓢(SpaceTime d, ℝ)) :
    lift c f ε = ∫ p : Time × Space d,
      ε ((toTimeAndSpace c).symm p) • f ((toTimeAndSpace c).symm p) := by
  rw [lift, distTimeSlice_symm_apply, ofFunction_apply (isTemperedIntegrable_timeSlice c hf)]
  rfl

/-- The lift of a tempered integrable function pairs with a test function by integration over
spacetime, with the factor `c⁻¹` relating the volume on spacetime to the measure on
`Time × Space d`. -/
lemma lift_apply (c : SpeedOfLight) {f : SpaceTime d → M} (hf : IsTemperedIntegrable f)
    (ε : 𝓢(SpaceTime d, ℝ)) :
    lift c f ε = (c.val)⁻¹ • ∫ x : SpaceTime d, ε x • f x := by
  rw [lift_apply_timeSlice c hf, spaceTime_integral_eq_time_space_integral c,
    smul_smul, inv_mul_cancel₀ c.val_ne_zero, one_smul]
  rfl

lemma lift_of_not (c : SpeedOfLight) {f : SpaceTime d → M}
    (hf : ¬ IsTemperedIntegrable fun p : Time × Space d => f ((toTimeAndSpace c).symm p)) :
    lift c f = 0 := by
  rw [lift, ofFunction_of_not hf, map_zero]

end SpaceTime
