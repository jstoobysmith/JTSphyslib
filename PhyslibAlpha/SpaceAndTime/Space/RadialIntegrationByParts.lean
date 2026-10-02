/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.SpaceAndTime.Space.Norm.Basic

/-!

# Integration by parts for radial vector fields

For a radial vector field `x ↦ m ‖x‖ ‖x‖ ^ (-d) • x` whose profile `m` is continuous and bounded
and differentiable away from a countable set, with bounded derivative, the integral of its inner
product with the gradient of a Schwartz function is computed in spherical coordinates: along
each ray it is a one-dimensional integration by parts, which produces the divergence
`m' ‖x‖ ‖x‖ ^ (1 - d)` and a boundary term `m 0` times the area of the unit sphere at the origin.

The profile is allowed to have a kink, so the identity applies to fields which are continuous
but not differentiable across a sphere, such as the field of a uniformly charged ball or the
transverse gradient of the potential of a thick wire.

## Main results

- `Space.integral_Ioi_mul_deriv_of_hasDerivAt_off_countable` : integration by parts on
  `(0, ∞)` against a Schwartz function, with countably many exceptional points.
- `Space.IsDistBounded.radial`, `Space.IsDistBounded.radial_smul_repr` : radial fields with
  bounded profiles are distributionally bounded.
- `Space.integral_inner_radial_grad` : the radial integration by parts.

## Contents

- A. Integration by parts on the half line
- B. Schwartz functions along a ray
- C. Spherical integrals and radial fields
- D. The radial integration by parts

-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped SchwartzMap

namespace Space

/-!

## A. Integration by parts on the half line

-/

/-- Integration by parts on `(0, ∞)` against a Schwartz function, for a bounded continuous
function which is differentiable away from a countable set. -/
lemma integral_Ioi_mul_deriv_of_hasDerivAt_off_countable (m m' : ℝ → ℝ) (ψ : 𝓢(ℝ, ℝ))
    (hm : Continuous m) {C : ℝ} (hmb : ∀ r, |m r| ≤ C) (hm' : Measurable m') {C' : ℝ}
    (hm'b : ∀ r, |m' r| ≤ C') {s : Set ℝ} (hs : s.Countable)
    (hd : ∀ r ∈ Ioi (0 : ℝ) \ s, HasDerivAt m (m' r) r) :
    ∫ r in Ioi (0 : ℝ), m r * _root_.deriv ψ r = - m 0 * ψ 0 - ∫ r in Ioi (0 : ℝ), m' r * ψ r := by
  have hψ' : Integrable (_root_.deriv ψ) := (SchwartzMap.derivCLM ℝ ℝ ψ).integrable
  have hi1 : Integrable fun r => m r * _root_.deriv ψ r :=
    hψ'.bdd_mul hm.aestronglyMeasurable (ae_of_all _ fun r => (Real.norm_eq_abs _).trans_le (hmb r))
  have hi2 : Integrable fun r => m' r * ψ r :=
    ψ.integrable.bdd_mul hm'.aestronglyMeasurable
      (ae_of_all _ fun r => (Real.norm_eq_abs _).trans_le (hm'b r))
  have hsum : Integrable fun r => m' r * ψ r + m r * _root_.deriv ψ r := hi2.add hi1
  -- The fundamental theorem of calculus on `[0, R]`, with countably many exceptions.
  have hFTC (R : ℝ) (hR : 0 ≤ R) :
      ∫ r in (0 : ℝ)..R, (m' r * ψ r + m r * _root_.deriv ψ r) = m R * ψ R - m 0 * ψ 0 :=
    integral_eq_of_hasDerivAt_off_countable_of_le (fun r => m r * ψ r) _ hR hs
      (hm.mul ψ.continuous).continuousOn
      (fun r hr => (hd r ⟨hr.1.1, hr.2⟩).mul (ψ.differentiableAt.hasDerivAt))
      hsum.intervalIntegrable
  have hlim1 := intervalIntegral_tendsto_integral_Ioi 0 hsum.integrableOn tendsto_id
  have hlim2 : Tendsto (fun R => m R * ψ R - m 0 * ψ 0) atTop (𝓝 (0 - m 0 * ψ 0)) := by
    refine Tendsto.sub_const ?_ _
    have h0 := ((ψ.tendsto_cocompact.mono_left atTop_le_cocompact).norm.const_mul C)
    rw [norm_zero, mul_zero] at h0
    refine squeeze_zero_norm (fun R => ?_) h0
    rw [norm_mul, Real.norm_eq_abs (m R)]
    exact mul_le_mul_of_nonneg_right (hmb R) (norm_nonneg _)
  have heq := tendsto_nhds_unique (hlim1.congr' (eventually_ge_atTop 0 |>.mono
    fun R hR => hFTC R hR)) hlim2
  rw [integral_add hi2.integrableOn hi1.integrableOn] at heq
  linarith

/-!

## B. Schwartz functions along a ray

-/

/-- The restriction of a Schwartz function to a line through the origin is a Schwartz
function. -/
lemma exists_schwartz_eq_comp_ray {d} (χ : 𝓢(Space d, ℝ)) {w : Space d} (hw : w ≠ 0) :
    ∃ g : 𝓢(ℝ, ℝ), ∀ s : ℝ, g s = χ (s • w) := by
  let γ : ℝ →L[ℝ] Space d := (ContinuousLinearMap.id ℝ ℝ).smulRight w
  have hγ : AntilipschitzWith ‖w‖₊⁻¹ γ := γ.antilipschitz_of_bound fun s => by
    simp only [γ, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, norm_smul]
    rw [NNReal.coe_inv, coe_nnnorm, mul_comm ‖s‖, ← mul_assoc,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw), one_mul]
  exact ⟨SchwartzMap.compCLMOfAntilipschitz ℝ γ.hasTemperateGrowth hγ χ, fun s => rfl⟩

/-!

## C. Spherical integrals and radial fields

-/

lemma integrable_sphere_integral {d : ℕ} {f : Space d → ℝ} (hf : Integrable f) :
    Integrable (fun n : ↑(Metric.sphere (0 : Space d) 1) =>
      ∫ r : Ioi (0 : ℝ), r.1 ^ (d - 1) * f (r.1 • n.1) ∂(.comap Subtype.val volume))
      (volume (α := Space d).toSphere) := by
  refine (integrable_spherical_of_integrable hf).integral_prod_left.congr
    (ae_of_all _ fun n => ?_)
  simp [Measure.volumeIoiPow]
  erw [integral_withDensity_eq_integral_smul (by fun_prop)]
  congr
  funext r
  have hr : 0 ≤ (r : ℝ) := le_of_lt r.2
  rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hr (d - 1)), smul_eq_mul]

lemma pow_mul_zpow_one_sub {d : ℕ} [NeZero d] {r : ℝ} (hr : 0 < r) :
    r ^ (d - 1) * r ^ (1 - d : ℤ) = 1 := by
  rw [← zpow_natCast, ← zpow_add₀ hr.ne', Nat.cast_pred (Nat.pos_of_neZero d)]
  simp

lemma IsDistBounded.radial {d : ℕ} {m : ℝ → ℝ} (hm : Measurable m) {C : ℝ} (hmb : ∀ r, |m r| ≤ C) :
    IsDistBounded (fun x : Space d => m ‖x‖ * ‖x‖ ^ (1 - d : ℤ)) := by
  refine ((IsDistBounded.pow (d := d) (1 - d : ℤ) (by omega)).const_mul_fun C).mono
    (by fun_prop) fun x => ?_
  rw [norm_mul, norm_mul, Real.norm_eq_abs (m _)]
  exact mul_le_mul_of_nonneg_right ((hmb _).trans (le_abs_self C)) (norm_nonneg _)

lemma IsDistBounded.radial_smul_repr {d : ℕ} {m : ℝ → ℝ} (hm : Measurable m) {C : ℝ}
    (hmb : ∀ r, |m r| ≤ C) :
    IsDistBounded (fun x : Space d => (m ‖x‖ * ‖x‖ ^ (-(d : ℤ))) • basis.repr x) := by
  refine (IsDistBounded.radial hm hmb).mono (by fun_prop) fun x => ?_
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [norm_zero, map_zero, smul_zero]
    positivity
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [norm_smul, LinearIsometryEquiv.norm_map, norm_mul, norm_mul, mul_assoc,
    norm_zpow, norm_zpow, norm_norm, ← zpow_add_one₀ hr.ne']
  ring_nf
  rfl

/-!

## D. The radial integration by parts

-/

open InnerProductSpace

/-- Integration by parts for the radial vector field `x ↦ m ‖x‖ ‖x‖ ^ (-d) • x` against the
gradient of a Schwartz function. The profile `m` is continuous and bounded, and differentiable
away from a countable set with bounded derivative `m'`; the boundary term at the origin is
`m 0` times the area of the unit sphere times `η 0`. -/
lemma integral_inner_radial_grad {d : ℕ} [NeZero d] {m m' : ℝ → ℝ} (hm : Continuous m)
    {C : ℝ} (hmb : ∀ r, |m r| ≤ C) (hm' : Measurable m') {C' : ℝ} (hm'b : ∀ r, |m' r| ≤ C')
    {s : Set ℝ} (hs : s.Countable) (hd : ∀ r ∈ Ioi (0 : ℝ) \ s, HasDerivAt m (m' r) r)
    (η : 𝓢(Space d, ℝ)) :
    ∫ x : Space d, ⟪(m ‖x‖ * ‖x‖ ^ (-(d : ℤ))) • basis.repr x, ∇ η x⟫_ℝ =
      - (∫ x : Space d, η x * (m' ‖x‖ * ‖x‖ ^ (1 - d : ℤ)))
      - m 0 * (d * (volume (α := Space d)).real (Metric.ball 0 1)) * η 0 := by
  have hg := IsDistBounded.radial_smul_repr (d := d) hm.measurable hmb
  have hg' := IsDistBounded.radial (d := d) hm' hm'b
  have hR := integral_volume_eq_spherical_integral (fun x => η x * (m' ‖x‖ * ‖x‖ ^ (1 - d : ℤ)))
    (hg'.integrable_space_mul η)
  rw [integral_volume_eq_spherical_integral _
    (integrable_isDistBounded_inner_grad_schwartzMap hg η)]
  rw [hR]
  simp only [smul_eq_mul]
  have hL (n : ↑(Metric.sphere (0 : Space d) 1)) :
      ∫ r : Ioi (0 : ℝ), r.1 ^ (d - 1) * ⟪(m ‖r.1 • n.1‖ * ‖r.1 • n.1‖ ^ (-(d : ℤ))) •
        basis.repr (r.1 • n.1), ∇ η (r.1 • n.1)⟫_ℝ ∂(.comap Subtype.val volume) =
      - (m 0 * η 0) - ∫ r : Ioi (0 : ℝ), r.1 ^ (d - 1) * (η (r.1 • n.1) *
        (m' ‖r.1 • n.1‖ * ‖r.1 • n.1‖ ^ (1 - d : ℤ))) ∂(.comap Subtype.val volume) := by
    have hn : n.1 ≠ 0 := by
      intro h
      simpa [h] using n.2
    obtain ⟨ψ, hψ⟩ := exists_schwartz_eq_comp_ray η hn
    have hψ' : (⇑ψ) = fun a => η (a • n.1) := funext hψ
    have h1 : ∀ r : Ioi (0 : ℝ), r.1 ^ (d - 1) * ⟪(m ‖r.1 • n.1‖ * ‖r.1 • n.1‖ ^ (-(d : ℤ))) •
        basis.repr (r.1 • n.1), ∇ η (r.1 • n.1)⟫_ℝ = m r.1 * _root_.deriv ψ r.1 := by
      intro r
      have hr : (0 : ℝ) < r.1 := r.2
      rw [norm_smul_sphere n hr.le, map_smul, inner_smul_left, inner_smul_left, real_inner_comm,
        grad_smul_inner_space n η η.differentiable r.1 hr, hψ']
      simp only [conj_trivial]
      have hj : r.1 ^ (d - 1) * (r.1 ^ (-(d : ℤ)) * r.1) = 1 := by
        rw [← zpow_add_one₀ hr.ne', ← pow_mul_zpow_one_sub (d := d) hr]
        ring_nf
      linear_combination (m r.1 * _root_.deriv (fun a => η (a • n.1)) r.1) * hj
    have h2 : ∀ r : Ioi (0 : ℝ), r.1 ^ (d - 1) * (η (r.1 • n.1) *
        (m' ‖r.1 • n.1‖ * ‖r.1 • n.1‖ ^ (1 - d : ℤ))) = m' r.1 * ψ r.1 := by
      intro r
      have hr : (0 : ℝ) < r.1 := r.2
      rw [norm_smul_sphere n hr.le, hψ]
      linear_combination (m' r.1 * η (r.1 • n.1)) * pow_mul_zpow_one_sub (d := d) hr
    simp only [h1, h2]
    rw [integral_subtype_comap measurableSet_Ioi (fun r => m r * _root_.deriv ψ r),
      integral_subtype_comap measurableSet_Ioi (fun r => m' r * ψ r),
      integral_Ioi_mul_deriv_of_hasDerivAt_off_countable m m' ψ hm hmb hm' hm'b hs hd, hψ,
      zero_smul]
    ring
  simp only [hL]
  rw [integral_sub (integrable_const _)
    (integrable_sphere_integral (f := fun x => η x * (m' ‖x‖ * ‖x‖ ^ (1 - d : ℤ)))
      (hg'.integrable_space_mul η)), integral_const]
  simp only [Measure.toSphere_real_apply_univ, finrank_eq_dim, smul_eq_mul]
  ring

end Space
