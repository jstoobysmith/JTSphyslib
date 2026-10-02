/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Electromagnetism.Dynamics.Basic
public import Physlib.Electromagnetism.Dynamics.CurrentDensity
public import Physlib.Electromagnetism.Kinematics.MagneticField
public import PhyslibAlpha.SpaceAndTime.Space.Derivatives.Locality

/-!

# The electromagnetic field of an infinite wire of radius `a`

An infinite straight wire of radius `a` along the `x`-axis carries a steady current `I`,
uniformly distributed over its cross-section. Unlike the infinitely thin wire of
`Physlib.Electromagnetism.Current.InfiniteWire`, the fields here are genuine functions: the
vector potential is `C¹`, the magnetic field is continuous, but the current density jumps at
the surface `r = a` of the wire and so the magnetic field is not differentiable there.

The potential is `A = -(μ₀ I / 2π) f(r²) x̂` with `f(s) = s / 2a²` inside the wire and
`f(s) = (log (s / a²) + 1) / 2` outside; the two pieces match to first order at `s = a²`. The
magnetic field circles the axis with magnitude `μ₀ I r / 2π a²` inside and `μ₀ I / 2π r`
outside.

Maxwell's equations are established pointwise away from the surface of the wire, where all the
fields are smooth. The discontinuity of the current at the surface is handled by the integral
form of Ampère's law: the circulation of the magnetic field around a circle of any radius,
including `r = a`, equals `μ₀` times the current through the disc it bounds.

## Main results

- `thickWireRadialProfile`, `thickWireVectorPotential`, `infiniteThickWire` : the potential.
- `thickWireCurrent`, `thickWireCurrentDensity` : the uniform current density.
- `infiniteThickWire_magneticField` : the magnetic field at every point.
- `infiniteThickWire_gaussLawMagnetic`, `infiniteThickWire_ampereLaw` : Gauss's law for the
  magnetic field and Ampère's law, away from the surface of the wire.
- `infiniteThickWire_faradayLaw`, `infiniteThickWire_gaussLawElectric` : Faraday's law and
  Gauss's law for the electric field, everywhere.
- `infiniteThickWire_magneticField_continuous` : the magnetic field is continuous across the
  surface of the wire.
- `infiniteThickWire_ampereLaw_integral` : Ampère's law in integral form, for every radius.

## Contents

- A. The radial profile
- B. Geometry of the axis
- C. The potential and the current
  - C.1. The vector potential
  - C.2. The current density
  - C.3. The scalar potential and the electric field
- D. The magnetic field
  - D.1. The magnetic field at every point
  - D.2. The magnetic field inside and outside the wire
- E. Maxwell's equations away from the surface
- F. The surface of the wire
  - F.1. Continuity of the magnetic field
  - F.2. Ampère's law in integral form

-/

@[expose] public section

namespace Electromagnetism
open Space Time MeasureTheory Set Filter Topology

namespace ElectromagneticPotential

/-!

## A. The radial profile

-/

/-- The radial profile of the potential as a function of the squared distance `s` from the
axis: `s / 2a²` inside the wire and `(log (s / a²) + 1) / 2` outside, matched to first order
at `s = a²`. -/
noncomputable def thickWireRadialProfile (a s : ℝ) : ℝ :=
  if s ≤ a ^ 2 then s / (2 * a ^ 2) else (Real.log (s / a ^ 2) + 1) / 2

lemma hasDerivAt_thickWireRadialProfile {a : ℝ} (ha : 0 < a) (s : ℝ) :
    HasDerivAt (thickWireRadialProfile a) (1 / (2 * max s (a ^ 2))) s := by
  have ha2 : 0 < a ^ 2 := by positivity
  have hin : HasDerivAt (fun s : ℝ => s / (2 * a ^ 2)) (1 / (2 * a ^ 2)) s := by
    have h := (hasDerivAt_id' s).div_const (2 * a ^ 2)
    exact h
  have hout (hs : 0 < s) : HasDerivAt (fun s : ℝ => (Real.log (s / a ^ 2) + 1) / 2)
      (1 / (2 * s)) s := by
    have h := (((hasDerivAt_id' s).div_const (a ^ 2)).log (by positivity)).add_const 1
      |>.div_const 2
    convert h using 1
    field_simp
  rcases lt_trichotomy s (a ^ 2) with hs | hs | hs
  · rw [max_eq_right hs.le]
    exact hin.congr_of_eventuallyEq (Filter.eventually_of_mem (Iio_mem_nhds hs)
      fun t ht => ite_eq_left (le_of_lt ht))
  · subst hs
    rw [max_self]
    have hl : HasDerivWithinAt (thickWireRadialProfile a) (1 / (2 * a ^ 2)) (Iic (a ^ 2))
        (a ^ 2) :=
      hin.hasDerivWithinAt.congr (fun t ht => ite_eq_left ht) (ite_eq_left le_rfl)
    have hr : HasDerivWithinAt (thickWireRadialProfile a) (1 / (2 * a ^ 2)) (Ici (a ^ 2))
        (a ^ 2) := by
      refine (hout ha2).hasDerivWithinAt.congr (fun t ht => ?_) ?_
      · rcases eq_or_lt_of_le (mem_Ici.mp ht) with h | h
        · subst h
          simp [thickWireRadialProfile]
          field_simp
        · exact ite_eq_right (not_le.mpr h)
      · simp [thickWireRadialProfile]
        field_simp
    have h := hl.union hr
    rw [Iic_union_Ici, hasDerivWithinAt_univ] at h
    exact h
  · rw [max_eq_left hs.le]
    exact (hout (ha2.trans hs)).congr_of_eventuallyEq
      (Filter.eventually_of_mem (Ioi_mem_nhds hs) fun t ht => ite_eq_right (not_le.mpr ht))

/-!

## B. Geometry of the axis

-/

/-- The squared distance of a point from the `x`-axis. -/
def axisDistSq (x : Space) : ℝ := x 1 ^ 2 + x 2 ^ 2

lemma axisDistSq_nonneg (x : Space) : 0 ≤ axisDistSq x := by
  unfold axisDistSq
  positivity

@[fun_prop]
lemma axisDistSq_differentiable : Differentiable ℝ axisDistSq := by
  unfold axisDistSq
  fun_prop

lemma deriv_axisDistSq (μ : Fin 3) (x : Space) :
    ∂[μ] axisDistSq x = (if μ = 1 then 2 * x 1 else 0) + (if μ = 2 then 2 * x 2 else 0) := by
  unfold axisDistSq
  rw [Space.deriv_eq, fderiv_fun_add (by fun_prop) (by fun_prop), _root_.add_apply,
    ← Space.deriv_eq, ← Space.deriv_eq, deriv_component_sq, deriv_component_sq]

/-!

## C. The potential and the current

### C.1. The vector potential

-/

/-- The vector potential of an infinite wire of radius `a` along the `x`-axis carrying a
current `I`. -/
noncomputable def thickWireVectorPotential (𝓕 : FreeSpace) (a I : ℝ) (x : Space) :
    EuclideanSpace ℝ (Fin 3) :=
  (- (I * 𝓕.μ₀) / (2 * Real.pi) * thickWireRadialProfile a (axisDistSq x)) •
    EuclideanSpace.single 0 1

/-- The electromagnetic potential of an infinite wire of radius `a` along the `x`-axis carrying
a current `I`. -/
noncomputable def infiniteThickWire (𝓕 : FreeSpace) (a I : ℝ) : ElectromagneticPotential :=
  ofStaticVectorPotential 𝓕.c (thickWireVectorPotential 𝓕 a I)

/-!

### C.2. The current density

-/

/-- The current density of an infinite wire of radius `a` along the `x`-axis carrying a current
`I`, uniformly distributed over its cross-section. -/
noncomputable def thickWireCurrent (a I : ℝ) (x : Space) : EuclideanSpace ℝ (Fin 3) :=
  (if axisDistSq x < a ^ 2 then I / (Real.pi * a ^ 2) else 0) • EuclideanSpace.single 0 1

/-- The Lorentz current density of an infinite wire of radius `a` along the `x`-axis carrying a
current `I`. -/
noncomputable def thickWireCurrentDensity (c : SpeedOfLight) (a I : ℝ) :
    LorentzCurrentDensity 3 := fun p μ =>
  match μ with
  | Sum.inl 0 => 0
  | Sum.inr i => thickWireCurrent a I (SpaceTime.toTimeAndSpace c p).2 i

@[simp]
lemma thickWireCurrentDensity_chargeDensity (c : SpeedOfLight) (a I : ℝ) :
    (thickWireCurrentDensity c a I).chargeDensity c = 0 := by
  funext t x
  simp [LorentzCurrentDensity.chargeDensity, thickWireCurrentDensity]

@[simp]
lemma thickWireCurrentDensity_currentDensity (c : SpeedOfLight) (a I : ℝ) :
    (thickWireCurrentDensity c a I).currentDensity c = fun _ => thickWireCurrent a I := by
  funext t x
  ext i
  simp [LorentzCurrentDensity.currentDensity, thickWireCurrentDensity]

/-!

### C.3. The scalar potential and the electric field

-/

@[simp]
lemma infiniteThickWire_scalarPotential (𝓕 : FreeSpace) (a I : ℝ) :
    (infiniteThickWire 𝓕 a I).scalarPotential 𝓕.c = 0 := by
  funext t x
  simp [scalarPotential, infiniteThickWire, ofStaticVectorPotential, ofVectorPotential,
    SpaceTime.timeSlice]

@[simp]
lemma infiniteThickWire_vectorPotential (𝓕 : FreeSpace) (a I : ℝ) :
    (infiniteThickWire 𝓕 a I).vectorPotential 𝓕.c = fun _ => thickWireVectorPotential 𝓕 a I := by
  simp [infiniteThickWire]

@[simp]
lemma infiniteThickWire_electricField (𝓕 : FreeSpace) (a I : ℝ) :
    (infiniteThickWire 𝓕 a I).electricField 𝓕.c = 0 := by
  funext t x
  simp [electricField_eq]

/-!

## D. The magnetic field

### D.1. The magnetic field at every point

-/

lemma thickWireVectorPotential_apply_zero (𝓕 : FreeSpace) (a I : ℝ) (x : Space) :
    thickWireVectorPotential 𝓕 a I x 0 =
      - (I * 𝓕.μ₀) / (2 * Real.pi) * thickWireRadialProfile a (axisDistSq x) := by
  simp [thickWireVectorPotential]

lemma thickWireVectorPotential_apply_of_ne (𝓕 : FreeSpace) (a I : ℝ) {j : Fin 3} (hj : j ≠ 0) :
    (fun x => thickWireVectorPotential 𝓕 a I x j) = 0 := by
  funext x
  simp [thickWireVectorPotential, hj]

lemma deriv_thickWireVectorPotential_zero (𝓕 : FreeSpace) {a : ℝ} (ha : 0 < a) (I : ℝ)
    (μ : Fin 3) (x : Space) :
    ∂[μ] (fun x => thickWireVectorPotential 𝓕 a I x 0) x =
      - (I * 𝓕.μ₀) / (2 * Real.pi) * (1 / (2 * max (axisDistSq x) (a ^ 2))) *
        ∂[μ] axisDistSq x := by
  simp only [thickWireVectorPotential_apply_zero]
  have h := ((hasDerivAt_thickWireRadialProfile ha (axisDistSq x)).comp_hasFDerivAt x
    (axisDistSq_differentiable x).hasFDerivAt).const_mul (- (I * 𝓕.μ₀) / (2 * Real.pi))
  rw [Space.deriv_eq]
  change fderiv ℝ (fun y => _ * (thickWireRadialProfile a ∘ axisDistSq) y) x (basis μ) = _
  rw [h.fderiv, Space.deriv_eq]
  simp [mul_assoc]

/-- The magnetic field of the wire, at every point: `μ₀ I r / (2 π a²)` inside the wire and
`μ₀ I / (2 π r)` outside, circling the axis. -/
lemma infiniteThickWire_magneticField (𝓕 : FreeSpace) {a : ℝ} (ha : 0 < a) (I : ℝ) (t : Time)
    (x : Space) :
    (infiniteThickWire 𝓕 a I).magneticField 𝓕.c t x =
      (I * 𝓕.μ₀ / (2 * Real.pi * max (axisDistSq x) (a ^ 2))) •
        WithLp.toLp 2 ![0, - x 2, x 1] := by
  have hz (μ : Fin 3) : ∂[μ] (0 : Space → ℝ) x = 0 := by
    rw [Space.deriv_eq, show (0 : Space → ℝ) = fun _ => (0 : ℝ) from rfl, fderiv_const_apply]
    rfl
  rw [magneticField_eq, infiniteThickWire_vectorPotential]
  ext i
  fin_cases i <;>
  simp [curl, thickWireVectorPotential_apply_of_ne, deriv_thickWireVectorPotential_zero 𝓕 ha,
    deriv_axisDistSq, hz] <;> field_simp

/-!

### D.2. The magnetic field inside and outside the wire

-/

lemma deriv_const_mul_component (c : ℝ) (μ ν : Fin 3) (x : Space) :
    ∂[μ] (fun y : Space => c * y ν) x = c * if μ = ν then 1 else 0 := by
  rw [Space.deriv_eq, fderiv_const_mul (eval_differentiable ν x), _root_.smul_apply,
    ← Space.deriv_eq, deriv_component, smul_eq_mul]

lemma deriv_const_mul_component_div_axisDistSq (c : ℝ) (μ ν : Fin 3) {x : Space}
    (hx : axisDistSq x ≠ 0) :
    ∂[μ] (fun y : Space => c * (y ν / axisDistSq y)) x =
      c * (((if μ = ν then 1 else 0) * axisDistSq x - x ν * ∂[μ] axisDistSq x) /
        axisDistSq x ^ 2) := by
  have hinv := (hasDerivAt_inv hx).comp_hasFDerivAt x (axisDistSq_differentiable x).hasFDerivAt
  have h := (((eval_differentiable ν x).hasFDerivAt).mul hinv).const_mul c
  simp only [div_eq_mul_inv]
  rw [Space.deriv_eq]
  change fderiv ℝ (fun y => c * ((fun p : Space => p ν) * (fun t : ℝ => t⁻¹) ∘ axisDistSq) y) x
    (basis μ) = _
  rw [h.fderiv]
  simp only [_root_.smul_apply, smul_eq_mul, _root_.add_apply]
  rw [← Space.deriv_eq, ← Space.deriv_eq, deriv_component, Function.comp_apply]
  field_simp
  ring

lemma deriv_fun_zero (μ : Fin 3) (x : Space) : ∂[μ] (fun _ : Space => (0 : ℝ)) x = 0 := by
  rw [Space.deriv_eq, fderiv_const_apply]
  rfl

/-- The magnetic field inside the wire, `μ₀ I / (2 π a²) (0, -z, y)`. -/
noncomputable def thickWireFieldInside (𝓕 : FreeSpace) (a I : ℝ) (y : Space) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![0, - (I * 𝓕.μ₀ / (2 * Real.pi * a ^ 2)) * y 2,
    I * 𝓕.μ₀ / (2 * Real.pi * a ^ 2) * y 1]

/-- The magnetic field outside the wire, `μ₀ I / (2 π (y² + z²)) (0, -z, y)`. -/
noncomputable def thickWireFieldOutside (𝓕 : FreeSpace) (I : ℝ) (y : Space) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![0, - (I * 𝓕.μ₀ / (2 * Real.pi)) * (y 2 / axisDistSq y),
    I * 𝓕.μ₀ / (2 * Real.pi) * (y 1 / axisDistSq y)]

lemma infiniteThickWire_magneticField_eventuallyEq_inside (𝓕 : FreeSpace) {a : ℝ} (ha : 0 < a)
    (I : ℝ) (t : Time) {x : Space} (hx : axisDistSq x < a ^ 2) :
    (infiniteThickWire 𝓕 a I).magneticField 𝓕.c t =ᶠ[𝓝 x] thickWireFieldInside 𝓕 a I := by
  filter_upwards [(isOpen_lt axisDistSq_differentiable.continuous continuous_const).mem_nhds hx]
    with y hy
  rw [infiniteThickWire_magneticField 𝓕 ha, max_eq_right (le_of_lt hy)]
  ext i
  fin_cases i <;> simp [thickWireFieldInside]

lemma infiniteThickWire_magneticField_eventuallyEq_outside (𝓕 : FreeSpace) {a : ℝ} (ha : 0 < a)
    (I : ℝ) (t : Time) {x : Space} (hx : a ^ 2 < axisDistSq x) :
    (infiniteThickWire 𝓕 a I).magneticField 𝓕.c t =ᶠ[𝓝 x] thickWireFieldOutside 𝓕 I := by
  filter_upwards [(isOpen_lt continuous_const axisDistSq_differentiable.continuous).mem_nhds hx]
    with y hy
  rw [infiniteThickWire_magneticField 𝓕 ha, max_eq_left (le_of_lt hy)]
  ext i
  fin_cases i <;> simp [thickWireFieldOutside] <;> ring

/-!

## E. Maxwell's equations away from the surface

-/

/-- Gauss's law for the magnetic field holds away from the surface of the wire. -/
theorem infiniteThickWire_gaussLawMagnetic (𝓕 : FreeSpace) {a : ℝ} (ha : 0 < a) (I : ℝ)
    (t : Time) {x : Space} (hx : axisDistSq x ≠ a ^ 2) :
    (∇ ⬝ (infiniteThickWire 𝓕 a I).magneticField 𝓕.c t) x = 0 := by
  rcases lt_or_gt_of_ne hx with h | h
  · rw [div_congr_of_eventuallyEq (infiniteThickWire_magneticField_eventuallyEq_inside 𝓕 ha I t h)]
    simp only [div, Fin.sum_univ_three, thickWireFieldInside, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    rw [deriv_fun_zero, deriv_const_mul_component, deriv_const_mul_component]
    simp
  · have hs : axisDistSq x ≠ 0 := (lt_trans (by positivity) h).ne'
    rw [div_congr_of_eventuallyEq
      (infiniteThickWire_magneticField_eventuallyEq_outside 𝓕 ha I t h)]
    simp only [div, Fin.sum_univ_three, thickWireFieldOutside, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    rw [deriv_fun_zero, deriv_const_mul_component_div_axisDistSq _ _ _ hs,
      deriv_const_mul_component_div_axisDistSq _ _ _ hs, deriv_axisDistSq, deriv_axisDistSq]
    simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, zero_add, add_zero, zero_mul]
    field_simp
    ring

/-- Ampère's law holds away from the surface of the wire. -/
theorem infiniteThickWire_ampereLaw (𝓕 : FreeSpace) {a : ℝ} (ha : 0 < a) (I : ℝ)
    (t : Time) {x : Space} (hx : axisDistSq x ≠ a ^ 2) :
    (∇ ⨯ (infiniteThickWire 𝓕 a I).magneticField 𝓕.c t) x =
      𝓕.μ₀ • (thickWireCurrentDensity 𝓕.c a I).currentDensity 𝓕.c t x := by
  rw [thickWireCurrentDensity_currentDensity]
  rcases lt_or_gt_of_ne hx with h | h
  · rw [(curl_eventuallyEq
      (infiniteThickWire_magneticField_eventuallyEq_inside 𝓕 ha I t h)).eq_of_nhds]
    ext i
    fin_cases i <;>
    simp only [curl, thickWireFieldInside, thickWireCurrent, h, Fin.isValue, Fin.zero_eta,
      Fin.mk_one, Fin.reduceFinMk, Fin.reduceAdd, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, ite_true, PiLp.toLp_apply,
      PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]
    · rw [deriv_const_mul_component, deriv_const_mul_component]
      simp only [Fin.isValue, ↓reduceIte, mul_one, sub_neg_eq_add]
      field_simp
      ring
    all_goals
      rw [deriv_fun_zero, deriv_const_mul_component]
      simp
  · have hs : axisDistSq x ≠ 0 := (lt_trans (by positivity) h).ne'
    rw [(curl_eventuallyEq
      (infiniteThickWire_magneticField_eventuallyEq_outside 𝓕 ha I t h)).eq_of_nhds]
    ext i
    fin_cases i <;>
    simp only [curl, thickWireFieldOutside, thickWireCurrent, not_lt.mpr h.le, Fin.isValue,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.reduceAdd, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, ite_false,
      PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul, zero_smul, PiLp.zero_apply, mul_zero]
    · rw [deriv_const_mul_component_div_axisDistSq _ _ _ hs,
        deriv_const_mul_component_div_axisDistSq _ _ _ hs, deriv_axisDistSq, deriv_axisDistSq]
      simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, zero_add, add_zero, one_mul, axisDistSq]
      field_simp
      ring
    all_goals
      rw [deriv_fun_zero, deriv_const_mul_component_div_axisDistSq _ _ _ hs, deriv_axisDistSq]
      simp

/-- Faraday's law holds everywhere: the fields are static and the electric field vanishes. -/
theorem infiniteThickWire_faradayLaw (𝓕 : FreeSpace) (a I : ℝ) (t : Time) (x : Space) :
    (∇ ⨯ (infiniteThickWire 𝓕 a I).electricField 𝓕.c t) x =
      - ∂ₜ (fun t => (infiniteThickWire 𝓕 a I).magneticField 𝓕.c t x) t := by
  simp [magneticField_eq, Time.deriv_eq, curl]
  rfl

/-- Gauss's law for the electric field holds everywhere: the wire is neutral. -/
theorem infiniteThickWire_gaussLawElectric (𝓕 : FreeSpace) (a I : ℝ) (t : Time) (x : Space) :
    (∇ ⬝ (infiniteThickWire 𝓕 a I).electricField 𝓕.c t) x =
      (thickWireCurrentDensity 𝓕.c a I).chargeDensity 𝓕.c t x / 𝓕.ε₀ := by
  simp [div]

/-!

## F. The surface of the wire

### F.1. Continuity of the magnetic field

-/

/-- The magnetic field is continuous across the surface of the wire. -/
lemma infiniteThickWire_magneticField_continuous (𝓕 : FreeSpace) {a : ℝ} (ha : 0 < a) (I : ℝ)
    (t : Time) : Continuous ((infiniteThickWire 𝓕 a I).magneticField 𝓕.c t) := by
  have h : (infiniteThickWire 𝓕 a I).magneticField 𝓕.c t = fun x =>
      (I * 𝓕.μ₀ / (2 * Real.pi * max (axisDistSq x) (a ^ 2))) • WithLp.toLp 2 ![0, - x 2, x 1] :=
    funext fun x => infiniteThickWire_magneticField 𝓕 ha I t x
  rw [h]
  have hne : ∀ x : Space, 2 * Real.pi * max (axisDistSq x) (a ^ 2) ≠ 0 := fun x =>
    mul_ne_zero (by positivity) (lt_max_of_lt_right (by positivity)).ne'
  refine Continuous.smul (Continuous.div continuous_const ?_ hne) ?_
  · exact continuous_const.mul (axisDistSq_differentiable.continuous.max continuous_const)
  · refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    fin_cases i <;> simp <;> fun_prop

/-!

### F.2. Ampère's law in integral form

-/

open InnerProductSpace

/-- The circulation of a vector field around the circle of radius `r` about the `x`-axis, in the
plane `x = 0`. -/
noncomputable def axisCirculation (B : Space → EuclideanSpace ℝ (Fin 3)) (r : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi), ⟪B ⟨![0, r * Real.cos θ, r * Real.sin θ]⟩,
    WithLp.toLp 2 ![0, - r * Real.sin θ, r * Real.cos θ]⟫_ℝ

/-- The current through the disc of radius `r` about the `x`-axis, in the plane `x = 0`. -/
noncomputable def thickWireEnclosedCurrent (a I r : ℝ) : ℝ :=
  ∫ q in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r, thickWireCurrent a I ⟨![0, q 0, q 1]⟩ 0

lemma thickWireCurrent_disc_apply {a : ℝ} (ha_nonneg : 0 ≤ a) (I : ℝ)
    (q : EuclideanSpace ℝ (Fin 2)) :
    thickWireCurrent a I ⟨![0, q 0, q 1]⟩ 0 =
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) a).indicator
        (fun _ => I / (Real.pi * a ^ 2)) q := by
  have hq : axisDistSq ⟨![0, q 0, q 1]⟩ = ‖q‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
    simp [axisDistSq]
  by_cases h : ‖q‖ < a
  · rw [indicator_of_mem (by simpa using h)]
    simp [thickWireCurrent, hq, pow_lt_pow_left₀ h (norm_nonneg q) two_ne_zero]
  · rw [indicator_of_notMem (by simpa using h)]
    have : ¬ ‖q‖ ^ 2 < a ^ 2 := fun h' => h (lt_of_pow_lt_pow_left₀ 2 ha_nonneg h')
    simp [thickWireCurrent, hq, this]

lemma thickWireEnclosedCurrent_eq {a : ℝ} (ha : 0 < a) (I : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    thickWireEnclosedCurrent a I r = I * min (r ^ 2) (a ^ 2) / a ^ 2 := by
  unfold thickWireEnclosedCurrent
  simp only [thickWireCurrent_disc_apply ha.le]
  rw [setIntegral_indicator Metric.isOpen_ball.measurableSet, setIntegral_const, smul_eq_mul]
  have hball : Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r ∩ Metric.ball 0 a =
      Metric.ball 0 (min r a) := by
    ext q
    simp [lt_min_iff]
  rw [hball, measureReal_def, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal Real.pi_pos.le]
  have hmin : min r a ^ 2 = min (r ^ 2) (a ^ 2) := by
    rcases le_total r a with h | h
    · rw [min_eq_left h, min_eq_left (pow_le_pow_left₀ hr h 2)]
    · rw [min_eq_right h, min_eq_right (pow_le_pow_left₀ ha.le h 2)]
  rw [hmin]
  field_simp

/-- Ampère's law in integral form around a circle of any radius `r`, including the radius `a`
of the wire where the differential form breaks down: the circulation of the magnetic field
equals `μ₀` times the enclosed current. -/
theorem infiniteThickWire_ampereLaw_integral (𝓕 : FreeSpace) {a : ℝ} (ha : 0 < a) (I : ℝ)
    (t : Time) {r : ℝ} (hr : 0 ≤ r) :
    axisCirculation ((infiniteThickWire 𝓕 a I).magneticField 𝓕.c t) r =
      𝓕.μ₀ * thickWireEnclosedCurrent a I r := by
  rw [thickWireEnclosedCurrent_eq ha I hr]
  have hc : ∀ θ : ℝ, ⟪(infiniteThickWire 𝓕 a I).magneticField 𝓕.c t
      ⟨![0, r * Real.cos θ, r * Real.sin θ]⟩,
      WithLp.toLp 2 ![0, - r * Real.sin θ, r * Real.cos θ]⟫_ℝ =
      I * 𝓕.μ₀ / (2 * Real.pi * max (r ^ 2) (a ^ 2)) * r ^ 2 := by
    intro θ
    have hs : axisDistSq ⟨![0, r * Real.cos θ, r * Real.sin θ]⟩ = r ^ 2 := by
      simp only [axisDistSq]
      change (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2
      nlinarith [Real.cos_sq_add_sin_sq θ]
    rw [infiniteThickWire_magneticField 𝓕 ha, hs, inner_smul_left]
    simp only [map_div₀, conj_trivial, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
      Matrix.cons_val, Matrix.cons_val_one, Matrix.cons_val_zero, neg_mul,
      inner_self_eq_norm_sq_to_K, RCLike.ofReal_real_eq_id, id_eq, mul_eq_mul_left_iff,
      div_eq_zero_iff, mul_eq_zero, FreeSpace.μ₀_ne_zero, or_false,
      OfNat.ofNat_ne_zero, Real.pi_ne_zero, or_self, false_or]
    left
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Real.norm_eq_abs, sq_abs, norm_zero]
    nlinarith [Real.cos_sq_add_sin_sq θ]
  unfold axisCirculation
  simp only [hc, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  have hmax : 0 < max (r ^ 2) (a ^ 2) := lt_max_of_lt_right (by positivity)
  rcases le_total (r ^ 2) (a ^ 2) with h | h
  · rw [max_eq_right h, min_eq_left h]
    field_simp
  · have hr0 : r ≠ 0 := fun h0 => by
      rw [h0] at h
      nlinarith
    rw [max_eq_left h, min_eq_right h]
    field_simp

end ElectromagneticPotential
end Electromagnetism
