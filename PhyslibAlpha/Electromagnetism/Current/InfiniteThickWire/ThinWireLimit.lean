/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Electromagnetism.Current.InfiniteThickWire.WeakExtrema
public import Physlib.Electromagnetism.Current.InfiniteWire

/-!

# The thin-wire limit of the thick wire

As the radius `a` of the thick wire tends to zero, the wire becomes the infinitely thin wire of
`Physlib.Electromagnetism.Current.InfiniteWire`, whose current density and potential are
distributions. This file proves it, in the sense of distributions: paired with any test function
on spacetime, the current density of the thick wire tends to that of the thin wire, and so does
the potential, once it is put in the gauge in which it agrees with the thin wire outside the
wire (the potentials differ by the constant `-(μ₀ I / 2π) (log a - 1/2)`, which diverges as
`a → 0` and must be removed).

Both wires are static and translation invariant along their axis, and both are built, in the
manner of the thin wire, by lifting a distribution on the transverse plane `Space 2` to
spacetime. The limits reduce to two statements about test functions on the plane: the average
over discs of radius `a` tends to the value at the centre, and the pairing with the defect
`thickWireDefect a`, by which the shifted thick-wire profile differs from `log ‖q‖`, is `a²`
times a bounded quantity by scaling.

## Main results

- `thickWireCurrentProfile`, `thickWirePotentialProfile` : the transverse profiles of the thick
  wire.
- `thickWireCurrentDensity_axisPoint`, `infiniteThickWire_axisPoint_add_gaugeShift` : the
  profiles are the transverse slices of the thick wire.
- `thickWireCurrentDist`, `infiniteThickWireDist` : the thick wire as a distribution.
- `thickWireCurrentDist_eq_integral` : the distributional current density is the distribution
  of the function `thickWireCurrentDensity`.
- `tendsto_thickWireCurrentDist`, `tendsto_infiniteThickWireDist` : the thin-wire limit.

## Contents

- A. The transverse profiles of the thick wire
  - A.1. Bounds on the profiles
  - A.2. The profiles and the thick wire
- B. The thick wire as a distribution
  - B.1. The distribution of the current density function
- C. The limits of the profiles
  - C.1. The current profile tends to a Dirac delta
  - C.2. The defect of the potential tends to zero
- D. The thin-wire limit

-/

@[expose] public section

namespace Electromagnetism
open Space MeasureTheory Set Filter Topology InnerProductSpace
open scoped SchwartzMap

namespace DistElectromagneticPotential

/-!

## A. The transverse profiles of the thick wire

-/

/-- The transverse profile of the current density of the thick wire: the current `I` spread
uniformly over the disc of radius `a`. -/
noncomputable def thickWireCurrentProfile (a I : ℝ) (q : Space 2) : Lorentz.Vector :=
  (Metric.ball (0 : Space 2) a).indicator (fun _ => I / (Real.pi * a ^ 2)) q •
    Lorentz.Vector.basis (Sum.inr 0)

/-- The amount by which the transverse profile of the potential of the thick wire, shifted by
the constant `log a - 1/2`, differs from the profile `log ‖q‖` of the thin wire. It is supported
in the disc of radius `a`. -/
noncomputable def thickWireDefect (a : ℝ) (q : Space 2) : ℝ :=
  (Metric.ball (0 : Space 2) a).indicator
    (fun q => ‖q‖ ^ 2 / (2 * a ^ 2) - 1 / 2 + Real.log a - Real.log ‖q‖) q

/-- The transverse profile of the vector potential of the thick wire, shifted by the constant
`-(μ₀ I / 2π) (log a - 1/2)` so that it agrees with the potential of the thin wire outside the
wire. -/
noncomputable def thickWirePotentialProfile (𝓕 : FreeSpace) (a I : ℝ) (q : Space 2) :
    Lorentz.Vector :=
  (- (I * 𝓕.μ₀) / (2 * Real.pi) * (Real.log ‖q‖ + thickWireDefect a q)) •
    Lorentz.Vector.basis (Sum.inr 0)

/-- The constant gauge shift of the potential of the thick wire. -/
noncomputable def thickWireGaugeShift (𝓕 : FreeSpace) (a I : ℝ) : Lorentz.Vector :=
  (- (I * 𝓕.μ₀) / (2 * Real.pi) * (Real.log a - 1 / 2)) • Lorentz.Vector.basis (Sum.inr 0)

/-!

### A.1. Bounds on the profiles

-/

lemma abs_thickWireDefect_le (a : ℝ) (q : Space 2) :
    |thickWireDefect a q| ≤ |Real.log ‖q‖| + (|Real.log a| + 1) := by
  rw [thickWireDefect]
  by_cases h : q ∈ Metric.ball (0 : Space 2) a
  · rw [indicator_of_mem h]
    have hq : ‖q‖ < a := by simpa using h
    have ha : 0 < a := (norm_nonneg q).trans_lt hq
    have h1 : ‖q‖ ^ 2 / (2 * a ^ 2) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [norm_nonneg q]
    have h2 : 0 ≤ ‖q‖ ^ 2 / (2 * a ^ 2) := by positivity
    rw [abs_le]
    constructor <;> nlinarith [abs_nonneg (Real.log ‖q‖), abs_nonneg (Real.log a),
      neg_abs_le (Real.log ‖q‖), le_abs_self (Real.log ‖q‖), neg_abs_le (Real.log a),
      le_abs_self (Real.log a)]
  · rw [indicator_of_notMem h, abs_zero]
    positivity

lemma thickWireDefect_measurable (a : ℝ) : Measurable (thickWireDefect a) :=
  (by fun_prop : Measurable fun q : Space 2 =>
    ‖q‖ ^ 2 / (2 * a ^ 2) - 1 / 2 + Real.log a - Real.log ‖q‖).indicator
    Metric.isOpen_ball.measurableSet

lemma isDistBounded_log_norm_add (C : ℝ) :
    IsDistBounded (fun q : Space 2 => |Real.log ‖q‖| + C) :=
  ((IsDistBounded.log_norm (d := 2)).congr
    (IsDistBounded.log_norm (d := 2)).aestronglyMeasurable.norm fun x => by simp).add
    (IsDistBounded.const _)

lemma isDistBounded_thickWireDefect (a : ℝ) : IsDistBounded (thickWireDefect a) := by
  refine (isDistBounded_log_norm_add (|Real.log a| + 1)).mono
    (thickWireDefect_measurable a).aestronglyMeasurable fun q => ?_
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity :
    (0 : ℝ) ≤ |Real.log ‖q‖| + (|Real.log a| + 1))]
  exact abs_thickWireDefect_le a q

lemma isDistBounded_thickWireCurrentProfile (a I : ℝ) :
    IsDistBounded (thickWireCurrentProfile a I) := by
  refine (IsDistBounded.const (d := 2) ((|I / (Real.pi * a ^ 2)|) •
    (Lorentz.Vector.basis (Sum.inr (0 : Fin 3)) : Lorentz.Vector))).mono ?_ fun q => ?_
  · exact (measurable_const.indicator Metric.isOpen_ball.measurableSet |>.smul_const _)
      |>.aestronglyMeasurable
  · rw [thickWireCurrentProfile, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_abs]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    by_cases h : q ∈ Metric.ball (0 : Space 2) a
    · rw [indicator_of_mem h]
    · rw [indicator_of_notMem h, abs_zero]
      exact abs_nonneg _

lemma isDistBounded_thickWirePotentialProfile (𝓕 : FreeSpace) (a I : ℝ) :
    IsDistBounded (thickWirePotentialProfile 𝓕 a I) := by
  unfold thickWirePotentialProfile
  exact (((IsDistBounded.log_norm (d := 2)).add (isDistBounded_thickWireDefect a)).const_mul_fun
    _).smul_const _

/-!

### A.2. The profiles and the thick wire

-/

open ElectromagneticPotential in
/-- The current density of the thick wire along the transverse slice is the current profile. -/
lemma thickWireCurrentDensity_axisPoint (c : SpeedOfLight) {a : ℝ} (ha : 0 < a) (I : ℝ)
    (t : Time) (r : ℝ) (q : Space 2) :
    thickWireCurrentDensity c a I (axisPoint c t r q) = thickWireCurrentProfile a I q := by
  ext μ
  match μ with
  | Sum.inl 0 =>
    simp [thickWireCurrentDensity, thickWireCurrentProfile]
  | Sum.inr i =>
    change thickWireCurrent a I (SpaceTime.toTimeAndSpace c (axisPoint c t r q)).2 i = _
    rw [toTimeAndSpace_axisPoint, thickWireCurrent_apply, axisDistSq_slice_symm]
    simp only [thickWireCurrentProfile, Lorentz.Vector.apply_smul, Lorentz.Vector.basis_apply,
      Sum.inr.injEq]
    by_cases h : ‖q‖ < a
    · rw [indicator_of_mem (show q ∈ Metric.ball (0 : Space 2) a by simpa using h),
        ite_eq_left (pow_lt_pow_left₀ h (norm_nonneg q) two_ne_zero)]
      split_ifs <;> simp_all
    · rw [indicator_of_notMem (show q ∉ Metric.ball (0 : Space 2) a by simpa using h),
        ite_eq_right (fun h' => h (lt_of_pow_lt_pow_left₀ 2 ha.le h'))]
      simp

lemma thickWireDefect_eq {a : ℝ} (ha : 0 < a) (q : Space 2) :
    Real.log ‖q‖ + thickWireDefect a q =
      ElectromagneticPotential.thickWireRadialProfile a (‖q‖ ^ 2) + Real.log a - 1 / 2 := by
  rw [thickWireDefect, ElectromagneticPotential.thickWireRadialProfile]
  by_cases h : ‖q‖ < a
  · rw [indicator_of_mem (show q ∈ Metric.ball (0 : Space 2) a by simpa using h),
      ite_eq_left (pow_le_pow_left₀ (norm_nonneg q) h.le 2)]
    ring
  · rw [indicator_of_notMem (show q ∉ Metric.ball (0 : Space 2) a by simpa using h)]
    have hq : 0 < ‖q‖ := ha.trans_le (not_lt.mp h)
    rcases eq_or_lt_of_le (not_lt.mp h) with h' | h'
    · rw [ite_eq_left (by rw [h'])]
      rw [h']
      field_simp
      ring
    · rw [ite_eq_right (not_le.mpr (pow_lt_pow_left₀ h' ha.le two_ne_zero)),
        Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
      push_cast
      ring

open ElectromagneticPotential in
/-- The potential of the thick wire along the transverse slice, shifted by the constant
gauge term, is the potential profile. -/
lemma infiniteThickWire_axisPoint_add_gaugeShift (𝓕 : FreeSpace) {a : ℝ} (ha : 0 < a)
    (I : ℝ) (t : Time) (r : ℝ) (q : Space 2) :
    infiniteThickWire 𝓕 a I (axisPoint 𝓕.c t r q) + thickWireGaugeShift 𝓕 a I =
      thickWirePotentialProfile 𝓕 a I q := by
  ext μ
  rw [Lorentz.Vector.apply_add, infiniteThickWire_apply, thickWireGaugeShift,
    thickWirePotentialProfile, Lorentz.Vector.apply_smul, Lorentz.Vector.apply_smul,
    Lorentz.Vector.basis_apply, thickWireDefect_eq ha]
  rcases eq_or_ne μ (Sum.inr 0) with rfl | h
  · simp [thickWirePotentialFun, axisDistSqST_axisPoint]
    ring
  · simp [h, Ne.symm h]

/-!

## B. The thick wire as a distribution

-/

/-- The current density of the thick wire as a distribution: the lift of the transverse
current profile, constant in time and along the axis. -/
noncomputable def thickWireCurrentDist (c : SpeedOfLight) (a I : ℝ) :
    DistLorentzCurrentDensity 3 :=
  (SpaceTime.distTimeSlice c).symm <| constantTime <| constantSliceDist 0 <|
    distOfFunction (thickWireCurrentProfile a I) (isDistBounded_thickWireCurrentProfile a I)

/-- The potential of the thick wire as a distribution, in the gauge in which it agrees with the
thin wire outside the wire. -/
noncomputable def infiniteThickWireDist (𝓕 : FreeSpace) (a I : ℝ) :
    DistElectromagneticPotential 3 :=
  (SpaceTime.distTimeSlice 𝓕.c).symm <| constantTime <| constantSliceDist 0 <|
    distOfFunction (thickWirePotentialProfile 𝓕 a I)
      (isDistBounded_thickWirePotentialProfile 𝓕 a I)

/-- The test function on the transverse plane obtained from a test function on spacetime by
integrating over time and along the axis. -/
noncomputable def transverseTest (c : SpeedOfLight) (κ : 𝓢(SpaceTime, ℝ)) : 𝓢(Space 2, ℝ) :=
  sliceSchwartz 0 (timeIntegralSchwartz
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (SpaceTime.toTimeAndSpace c).symm κ))

lemma lift_apply {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] (c : SpeedOfLight)
    (D : (Space 2) →d[ℝ] M) (κ : 𝓢(SpaceTime, ℝ)) :
    ((SpaceTime.distTimeSlice c).symm (constantTime (constantSliceDist 0 D))) κ =
      D (transverseTest c κ) := rfl

lemma thickWireCurrentDist_apply (c : SpeedOfLight) (a I : ℝ) (κ : 𝓢(SpaceTime, ℝ)) :
    thickWireCurrentDist c a I κ =
      (∫ q, transverseTest c κ q *
        (Metric.ball (0 : Space 2) a).indicator (fun _ => I / (Real.pi * a ^ 2)) q) •
        Lorentz.Vector.basis (Sum.inr 0) := by
  rw [thickWireCurrentDist, lift_apply, distOfFunction_apply, ← integral_smul_const]
  simp only [thickWireCurrentProfile, smul_smul]

lemma wireCurrentDensity_apply (c : SpeedOfLight) (I : ℝ) (κ : 𝓢(SpaceTime, ℝ)) :
    wireCurrentDensity c I κ = (I * transverseTest c κ 0) • Lorentz.Vector.basis (Sum.inr 0) := by
  rw [wireCurrentDensity, LinearMap.coe_mk, AddHom.coe_mk, lift_apply]
  simp [smul_smul]

lemma infiniteThickWireDist_apply (𝓕 : FreeSpace) (a I : ℝ) (κ : 𝓢(SpaceTime, ℝ)) :
    infiniteThickWireDist 𝓕 a I κ =
      (- (I * 𝓕.μ₀) / (2 * Real.pi) * ∫ q, transverseTest 𝓕.c κ q *
        (Real.log ‖q‖ + thickWireDefect a q)) • Lorentz.Vector.basis (Sum.inr 0) := by
  rw [infiniteThickWireDist, lift_apply, distOfFunction_apply]
  simp only [thickWirePotentialProfile, smul_smul]
  rw [integral_smul_const, ← integral_const_mul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun q => ?_)
  ring

lemma infiniteWire_apply (𝓕 : FreeSpace) (I : ℝ) (κ : 𝓢(SpaceTime, ℝ)) :
    infiniteWire 𝓕 I κ =
      (- I * 𝓕.μ₀ / (2 * Real.pi) * ∫ q, transverseTest 𝓕.c κ q * Real.log ‖q‖) •
        Lorentz.Vector.basis (Sum.inr 0) := by
  rw [infiniteWire, lift_apply, _root_.smul_apply, distOfFunction_apply]
  simp only [smul_smul]
  rw [integral_smul_const, smul_smul]

/-!

### B.1. The distribution of the current density function

-/

open ElectromagneticPotential in
/-- The distributional current density of the thick wire is the distribution of the function
`thickWireCurrentDensity`, paired with test functions on `Time × Space`. -/
lemma thickWireCurrentDist_eq_integral (c : SpeedOfLight) {a : ℝ} (ha : 0 < a) (I : ℝ)
    (κ : 𝓢(SpaceTime, ℝ)) :
    thickWireCurrentDist c a I κ = ∫ p : Time × Space,
      κ ((SpaceTime.toTimeAndSpace c).symm p) •
        thickWireCurrentDensity c a I ((SpaceTime.toTimeAndSpace c).symm p) := by
  set κ' : 𝓢(Time × Space, ℝ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (SpaceTime.toTimeAndSpace c).symm κ
  set G : Space → Lorentz.Vector := fun y => thickWireCurrentProfile a I (slice 0 y).2 with hGdef
  have hG : IsDistBounded G := by
    refine (IsDistBounded.const (d := 3) ((|I / (Real.pi * a ^ 2)|) •
      (Lorentz.Vector.basis (Sum.inr (0 : Fin 3)) : Lorentz.Vector))).mono ?_ fun y => ?_
    · exact (((measurable_const.indicator Metric.isOpen_ball.measurableSet).comp
        (continuous_snd.comp (slice 0).continuous).measurable).smul_const _).aestronglyMeasurable
    · simp only [hGdef, thickWireCurrentProfile, norm_smul, Real.norm_eq_abs, abs_abs]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      by_cases h : (slice 0 y).2 ∈ Metric.ball (0 : Space 2) a
      · rw [indicator_of_mem h]
      · rw [indicator_of_notMem h, abs_zero]
        exact abs_nonneg _
  have hJ : ∀ p : Time × Space,
      thickWireCurrentDensity c a I ((SpaceTime.toTimeAndSpace c).symm p) = G p.2 := by
    rintro ⟨t, y⟩
    have hy : (SpaceTime.toTimeAndSpace c).symm (t, y) =
        axisPoint c t (slice 0 y).1 (slice 0 y).2 := by
      simp [axisPoint]
    rw [hy, thickWireCurrentDensity_axisPoint c ha I]
  symm
  calc ∫ p : Time × Space, κ ((SpaceTime.toTimeAndSpace c).symm p) •
        thickWireCurrentDensity c a I ((SpaceTime.toTimeAndSpace c).symm p)
      = ∫ p : Time × Space, κ' p • G p.2 := by
        simp only [hJ]
        rfl
    _ = ∫ y : Space, ∫ t : Time, κ' (t, y) • G y :=
        integral_prod_symm _ (hG.integrable_time_space κ')
    _ = ∫ y : Space, timeIntegralSchwartz κ' y • G y := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        beta_reduce
        rw [integral_smul_const, timeIntegralSchwartz_apply]
    _ = ∫ q : Space 2, ∫ r : ℝ, timeIntegralSchwartz κ' ((slice 0).symm (r, q)) •
        G ((slice 0).symm (r, q)) := integral_eq_integral_slice' 0 _ (hG.integrable_space _)
    _ = ∫ q : Space 2, (∫ r : ℝ, timeIntegralSchwartz κ' ((slice 0).symm (r, q))) •
        thickWireCurrentProfile a I q := by
        refine integral_congr_ae (Eventually.of_forall fun q => ?_)
        simp only [hGdef, ContinuousLinearEquiv.apply_symm_apply]
        rw [integral_smul_const]
    _ = thickWireCurrentDist c a I κ := by
        rw [thickWireCurrentDist, lift_apply, distOfFunction_apply]
        rfl

/-!

## C. The limits of the profiles

### C.1. The current profile tends to a Dirac delta

-/

lemma volume_real_ball_two {a : ℝ} (ha : 0 ≤ a) :
    (volume (α := Space 2)).real (Metric.ball 0 a) = Real.pi * a ^ 2 := by
  rw [measureReal_def, Measure.addHaar_ball _ _ ha, volume_metricBall_two, finrank_eq_dim,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal Real.pi_pos.le]
  ring

/-- The average of a Schwartz function over small discs tends to its value at the centre. -/
lemma tendsto_integral_mul_ball_indicator (η : 𝓢(Space 2, ℝ)) :
    Tendsto (fun a : ℝ => ∫ q, η q *
      (Metric.ball (0 : Space 2) a).indicator (fun _ => 1 / (Real.pi * a ^ 2)) q)
      (𝓝[>] 0) (𝓝 (η 0)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨r₀, hr₀, hr₀ε⟩ := Metric.continuousAt_iff.mp
    (η.continuous.continuousAt (x := (0 : Space 2))) (ε / 2) (by positivity)
  refine ⟨r₀, hr₀, fun a ha hd => ?_⟩
  have ha : 0 < a := ha
  have had : a < r₀ := by simpa [Real.dist_eq, abs_of_pos ha] using hd
  have hvol := volume_real_ball_two ha.le
  have hint : (fun q => η q * (Metric.ball (0 : Space 2) a).indicator
      (fun _ => 1 / (Real.pi * a ^ 2)) q) =
      (Metric.ball (0 : Space 2) a).indicator (fun q => 1 / (Real.pi * a ^ 2) * η q) := by
    funext q
    by_cases h : q ∈ Metric.ball (0 : Space 2) a <;> simp [h, mul_comm]
  rw [hint, integral_indicator Metric.isOpen_ball.measurableSet, integral_const_mul]
  have hsub := integral_sub (μ := volume.restrict (Metric.ball (0 : Space 2) a))
    (f := fun q => η q) (g := fun _ => η 0) η.integrable.integrableOn
    (integrableOn_const (C := η 0) measure_ball_lt_top.ne)
  rw [setIntegral_const, hvol, smul_eq_mul] at hsub
  have hbound : |∫ q in Metric.ball (0 : Space 2) a, (η q - η 0)| ≤ ε / 2 * (Real.pi * a ^ 2) := by
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Metric.ball (0 : Space 2) a)
      (f := fun q => η q - η 0) (C := ε / 2) measure_ball_lt_top fun q hq => ?_
    · simpa [Real.norm_eq_abs, hvol] using this
    · rw [Real.norm_eq_abs, ← Real.dist_eq]
      exact (hr₀ε (by rw [dist_zero_right]; exact (mem_ball_zero_iff.mp hq).trans had)).le
  rw [Real.dist_eq]
  calc |1 / (Real.pi * a ^ 2) * (∫ q in Metric.ball (0 : Space 2) a, η q) - η 0|
      = |1 / (Real.pi * a ^ 2) * ∫ q in Metric.ball (0 : Space 2) a, (η q - η 0)| := by
        rw [hsub]
        congr 1
        field_simp
    _ ≤ 1 / (Real.pi * a ^ 2) * (ε / 2 * (Real.pi * a ^ 2)) := by
        rw [abs_mul, abs_of_pos (by positivity)]
        exact mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

/-!

### C.2. The defect of the potential tends to zero

-/

lemma thickWireDefect_eq_smul {a : ℝ} (ha : 0 < a) {q : Space 2} (hq : q ≠ 0) :
    thickWireDefect a q = thickWireDefect 1 (a⁻¹ • q) := by
  simp only [thickWireDefect]
  have hn : ‖a⁻¹ • q‖ = a⁻¹ * ‖q‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
  have hmem : a⁻¹ • q ∈ Metric.ball (0 : Space 2) 1 ↔ q ∈ Metric.ball (0 : Space 2) a := by
    simp [hn, inv_mul_lt_iff₀ ha]
  by_cases h : q ∈ Metric.ball (0 : Space 2) a
  · rw [indicator_of_mem h, indicator_of_mem (hmem.mpr h), hn,
      Real.log_mul (inv_ne_zero ha.ne') (norm_ne_zero_iff.mpr hq), Real.log_inv, Real.log_one]
    field_simp
    ring
  · rw [indicator_of_notMem h, indicator_of_notMem (fun h' => h (hmem.mp h'))]

lemma abs_log_le_of_le_one {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    |Real.log x| ≤ 2 * x ^ (-(1 / 2 : ℝ)) := by
  rcases hx.eq_or_lt with rfl | hx0
  · rw [Real.log_zero, abs_zero, Real.zero_rpow (by norm_num)]
    simp
  · rw [abs_of_nonpos (Real.log_nonpos hx hx1)]
    have h := Real.log_le_rpow_div (x := x⁻¹) (by positivity) (one_half_pos)
    rw [Real.log_inv, Real.inv_rpow hx, ← Real.rpow_neg hx] at h
    have h2 : (x ^ (-(1 / 2 : ℝ))) / (1 / 2) = 2 * x ^ (-(1 / 2 : ℝ)) := by ring
    linarith

lemma integrable_thickWireDefect_one : Integrable (thickWireDefect 1) := by
  show Integrable ((Metric.ball (0 : Space 2) 1).indicator
    fun q => ‖q‖ ^ 2 / (2 * 1 ^ 2) - 1 / 2 + Real.log 1 - Real.log ‖q‖)
  rw [integrable_indicator_iff Metric.isOpen_ball.measurableSet]
  have hg : IntegrableOn (fun q : Space 2 => 1 / 2 + 2 * ‖q‖ ^ (-(1 / 2 : ℝ)))
      (Metric.ball 0 1) :=
    (integrableOn_const (C := (1 / 2 : ℝ)) measure_ball_lt_top.ne).add
      (((integrableOn_norm_rpow_ball_iff one_pos _).mpr (by norm_num)).const_mul 2)
  refine hg.mono' ((by fun_prop : Measurable fun q : Space 2 =>
    ‖q‖ ^ 2 / (2 * 1 ^ 2) - 1 / 2 + Real.log 1 - Real.log ‖q‖).aestronglyMeasurable) ?_
  rw [ae_restrict_iff' Metric.isOpen_ball.measurableSet]
  refine ae_of_all _ fun q hq => ?_
  have hq1 : ‖q‖ ≤ 1 := (mem_ball_zero_iff.mp hq).le
  have hq2 : 0 ≤ ‖q‖ ^ 2 ∧ ‖q‖ ^ 2 ≤ 1 := ⟨by positivity, pow_le_one₀ (norm_nonneg q) hq1⟩
  rw [Real.norm_eq_abs, Real.log_one]
  calc |‖q‖ ^ 2 / (2 * 1 ^ 2) - 1 / 2 + 0 - Real.log ‖q‖|
      ≤ |‖q‖ ^ 2 / (2 * 1 ^ 2) - 1 / 2 + 0| + |Real.log ‖q‖| := abs_sub _ _
    _ ≤ 1 / 2 + 2 * ‖q‖ ^ (-(1 / 2 : ℝ)) := by
        gcongr
        · rw [abs_le]
          constructor <;> nlinarith [hq2.1, hq2.2]
        · exact abs_log_le_of_le_one (norm_nonneg q) hq1

/-- The pairing of the defect with a test function, by scaling. -/
lemma integral_mul_thickWireDefect {a : ℝ} (ha : 0 < a) (η : 𝓢(Space 2, ℝ)) :
    ∫ q, η q * thickWireDefect a q = a ^ 2 * ∫ q, η (a • q) * thickWireDefect 1 q := by
  calc ∫ q, η q * thickWireDefect a q
      = ∫ q, η (a • a⁻¹ • q) * thickWireDefect 1 (a⁻¹ • q) := by
        refine integral_congr_ae ?_
        filter_upwards [Measure.ae_ne volume 0] with q hq
        rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul, thickWireDefect_eq_smul ha hq]
    _ = |((a⁻¹) ^ Module.finrank ℝ (Space 2))⁻¹| •
        ∫ q, η (a • q) * thickWireDefect 1 q :=
        Measure.integral_comp_smul (μ := volume) (fun q => η (a • q) * thickWireDefect 1 q) a⁻¹
    _ = a ^ 2 * ∫ q, η (a • q) * thickWireDefect 1 q := by
        rw [finrank_eq_dim, inv_pow, inv_inv, abs_of_pos (by positivity), smul_eq_mul]

lemma tendsto_integral_mul_thickWireDefect (η : 𝓢(Space 2, ℝ)) :
    Tendsto (fun a => ∫ q, η q * thickWireDefect a q) (𝓝[>] 0) (𝓝 0) := by
  set C := SchwartzMap.seminorm ℝ 0 0 η * ∫ q, |thickWireDefect 1 q| with hC
  have hbound : ∀ a : ℝ, 0 < a → |∫ q, η q * thickWireDefect a q| ≤ a ^ 2 * C := by
    intro a ha
    rw [integral_mul_thickWireDefect ha, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < a ^ 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc |∫ q, η (a • q) * thickWireDefect 1 q|
        ≤ ∫ q, |η (a • q) * thickWireDefect 1 q| := by
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
            (fun q => η (a • q) * thickWireDefect 1 q)
      _ ≤ ∫ q, SchwartzMap.seminorm ℝ 0 0 η * |thickWireDefect 1 q| := by
          refine integral_mono_of_nonneg (ae_of_all _ fun q => abs_nonneg _)
            (integrable_thickWireDefect_one.abs.const_mul _) (ae_of_all _ fun q => ?_)
          beta_reduce
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right
            ((Real.norm_eq_abs _).symm.trans_le (SchwartzMap.norm_le_seminorm ℝ η _))
            (abs_nonneg _)
      _ = C := integral_const_mul _ _
  have hlim : Tendsto (fun a : ℝ => a ^ 2 * C) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun a : ℝ => a ^ 2 * C) (𝓝 0) (𝓝 (0 ^ 2 * C)) :=
      ((continuous_pow 2).mul continuous_const).tendsto 0
    simpa using h.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (Real.norm_eq_abs _).trans_le (hbound a ha)

/-!

## D. The thin-wire limit

-/

/-- As the radius of the wire tends to zero, the current density of the thick wire tends, as a
distribution, to the current density of the infinitely thin wire. -/
theorem tendsto_thickWireCurrentDist (c : SpeedOfLight) (I : ℝ) (κ : 𝓢(SpaceTime, ℝ)) :
    Tendsto (fun a => thickWireCurrentDist c a I κ) (𝓝[>] 0) (𝓝 (wireCurrentDensity c I κ)) := by
  simp only [thickWireCurrentDist_apply, wireCurrentDensity_apply]
  refine Tendsto.smul_const ?_ _
  refine ((tendsto_integral_mul_ball_indicator (transverseTest c κ)).const_mul I).congr' ?_
  filter_upwards with a
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun q => ?_)
  by_cases hq : q ∈ Metric.ball (0 : Space 2) a
  · simp [hq]
    ring
  · simp [hq]

/-- As the radius of the wire tends to zero, the potential of the thick wire, in the gauge in
which it agrees with the thin wire outside the wire, tends as a distribution to the potential
of the infinitely thin wire. -/
theorem tendsto_infiniteThickWireDist (𝓕 : FreeSpace) (I : ℝ) (κ : 𝓢(SpaceTime, ℝ)) :
    Tendsto (fun a => infiniteThickWireDist 𝓕 a I κ) (𝓝[>] 0) (𝓝 (infiniteWire 𝓕 I κ)) := by
  simp only [infiniteThickWireDist_apply, infiniteWire_apply]
  refine Tendsto.smul_const ?_ _
  have hlog : Integrable (fun q => transverseTest 𝓕.c κ q * Real.log ‖q‖) :=
    (IsDistBounded.log_norm (d := 2)).integrable_space_mul _
  have hsplit : ∀ a, ∫ q, transverseTest 𝓕.c κ q * (Real.log ‖q‖ + thickWireDefect a q) =
      (∫ q, transverseTest 𝓕.c κ q * Real.log ‖q‖) +
        ∫ q, transverseTest 𝓕.c κ q * thickWireDefect a q := fun a => by
    rw [← integral_add hlog ((isDistBounded_thickWireDefect a).integrable_space_mul _)]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    ring
  simp only [hsplit]
  have := ((tendsto_integral_mul_thickWireDefect (transverseTest 𝓕.c κ)).const_add
    (∫ q, transverseTest 𝓕.c κ q * Real.log ‖q‖)).const_mul (- I * 𝓕.μ₀ / (2 * Real.pi))
  simpa using this

end DistElectromagneticPotential
end Electromagnetism
