/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Mathematics.Distribution.Basic

/-!

# Distributions from tempered integrable functions

A function `f : E → F` on a normed space with a measure defines a tempered distribution
`η ↦ ∫ x, η x • f x` as soon as it is integrable against an inverse polynomial weight, that is
`x ↦ ((1 + ‖x‖) ^ k)⁻¹ • f x` is integrable for some `k`. This covers locally integrable
functions of polynomial growth, including functions with integrable singularities such as
`log ‖x‖` in two dimensions or `‖x‖⁻¹` in three.

The map `ofFunction` sends such a function to its distribution, and every other function, which
cannot be lifted, to `0`.

## Main results

- `IsTemperedIntegrable` : the condition under which a function defines a distribution.
- `ofFunction` : the distribution of a function, `0` on functions which are not tempered
  integrable.
- `ofFunction_apply` : the distribution of a tempered integrable function is integration
  against it.
- `ofFunction_of_not` : a function which is not tempered integrable lifts to `0`.

## Contents

- A. Tempered integrable functions
- B. The distribution of a function

-/

@[expose] public section

open MeasureTheory SchwartzMap
open scoped SchwartzMap

namespace Physlib
namespace Distribution

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-!

## A. Tempered integrable functions

-/

/-- A function is tempered integrable if it is integrable against an inverse polynomial weight
`((1 + ‖x‖) ^ k)⁻¹`. Such a function defines a tempered distribution. -/
def IsTemperedIntegrable (f : E → F) : Prop :=
  ∃ k : ℕ, Integrable (fun x => ((1 + ‖x‖) ^ k)⁻¹ • f x)

omit [MeasureSpace E] in
lemma abs_one_add_pow_mul_le (k : ℕ) (η : 𝓢(E, ℝ)) (x : E) :
    |(1 + ‖x‖) ^ k * η x| ≤
      2 ^ k * (Finset.Iic (k, 0)).sup (schwartzSeminormFamily ℝ E ℝ) η := by
  have h0 := one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (k := k) (n := 0) le_rfl
    le_rfl η x
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h0
  rw [abs_mul, abs_of_nonneg (by positivity)]
  exact h0

variable [BorelSpace E]

omit [NormedSpace ℝ E] in
lemma IsTemperedIntegrable.aestronglyMeasurable {f : E → F} (hf : IsTemperedIntegrable f) :
    AEStronglyMeasurable f := by
  obtain ⟨k, hk⟩ := hf
  have hw : Continuous fun x : E => (1 + ‖x‖) ^ k := (continuous_const.add continuous_norm).pow k
  refine (hw.aestronglyMeasurable.smul hk.aestronglyMeasurable).congr
    (Filter.Eventually.of_forall fun x => ?_)
  have hp : (1 + ‖x‖) ^ k ≠ 0 := pow_ne_zero _ (add_pos_of_pos_of_nonneg one_pos
    (norm_nonneg x)).ne'
  change (1 + ‖x‖) ^ k • (((1 + ‖x‖) ^ k)⁻¹ • f x) = f x
  rw [smul_smul, mul_inv_cancel₀ hp, one_smul]

lemma IsTemperedIntegrable.integrable_smul {f : E → F} (hf : IsTemperedIntegrable f)
    (η : 𝓢(E, ℝ)) : Integrable (fun x => η x • f x) := by
  obtain ⟨k, hk⟩ := hf
  have h := hk.bdd_smul (φ := fun x => (1 + ‖x‖) ^ k * η x)
    (2 ^ k * (Finset.Iic (k, 0)).sup (schwartzSeminormFamily ℝ E ℝ) η)
    ((by fun_prop : Continuous fun x => (1 + ‖x‖) ^ k * η x).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => (Real.norm_eq_abs _).trans_le
      (abs_one_add_pow_mul_le k η x))
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  have hp : (1 + ‖x‖) ^ k ≠ 0 := by positivity
  simp only [Pi.smul_apply', smul_smul]
  congr 1
  field_simp

omit [BorelSpace E] in
lemma IsTemperedIntegrable.norm_integral_le {f : E → F} (hf : IsTemperedIntegrable f) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ η : 𝓢(E, ℝ),
      ‖∫ x, η x • f x‖ ≤ C * (s.sup (schwartzSeminormFamily ℝ E ℝ)) η := by
  obtain ⟨k, hk⟩ := hf
  refine ⟨Finset.Iic (k, 0), 2 ^ k * ∫ x, ‖((1 + ‖x‖) ^ k)⁻¹ • f x‖, by positivity,
    fun η => (norm_integral_le_integral_norm _).trans ?_⟩
  set S := (Finset.Iic (k, 0)).sup (schwartzSeminormFamily ℝ E ℝ) η
  calc ∫ x, ‖η x • f x‖
      ≤ ∫ x, 2 ^ k * S * ‖((1 + ‖x‖) ^ k)⁻¹ • f x‖ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _)
          (hk.norm.const_mul _) (Filter.Eventually.of_forall fun x => ?_)
        have hx : η x • f x = ((1 + ‖x‖) ^ k * η x) • (((1 + ‖x‖) ^ k)⁻¹ • f x) := by
          have hp : (1 + ‖x‖) ^ k ≠ 0 := by positivity
          rw [smul_smul]
          congr 1
          field_simp
        beta_reduce
        rw [hx, norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (abs_one_add_pow_mul_le k η x) (norm_nonneg _)
    _ = 2 ^ k * (∫ x, ‖((1 + ‖x‖) ^ k)⁻¹ • f x‖) * S := by
        rw [integral_const_mul]
        ring

/-!

## B. The distribution of a function

-/

/-- The distribution of a tempered integrable function. -/
noncomputable def ofTemperedIntegrable (f : E → F) (hf : IsTemperedIntegrable f) :
    E →d[ℝ] F :=
  mkCLMtoNormedSpace (fun η => ∫ x, η x • f x)
    (fun η κ => by
      simp only [_root_.add_apply, add_smul]
      exact integral_add (hf.integrable_smul η) (hf.integrable_smul κ))
    (fun a η => by
      simp only [_root_.smul_apply, smul_eq_mul, RingHom.id_apply, ← smul_smul]
      exact integral_smul a _)
    hf.norm_integral_le

open Classical in
/-- The distribution of a function `f : E → F`: integration against `f` when `f` is tempered
integrable, and `0` on every other function, which cannot be lifted to a distribution. -/
noncomputable def ofFunction (f : E → F) : E →d[ℝ] F :=
  if hf : IsTemperedIntegrable f then ofTemperedIntegrable f hf else 0

lemma ofFunction_apply {f : E → F} (hf : IsTemperedIntegrable f) (η : 𝓢(E, ℝ)) :
    ofFunction f η = ∫ x, η x • f x := by
  rw [ofFunction, dite_eq_left hf]
  rfl

lemma ofFunction_of_not {f : E → F} (hf : ¬ IsTemperedIntegrable f) : ofFunction f = 0 := by
  rw [ofFunction, dite_eq_right hf]

end Distribution
end Physlib
