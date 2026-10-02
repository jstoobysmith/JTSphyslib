/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Electromagnetism.Current.InfiniteThickWire.Basic
public import PhyslibAlpha.Electromagnetism.Dynamics.FirstVariation
public import PhyslibAlpha.SpaceAndTime.Space.RadialIntegrationByParts
public import PhyslibAlpha.SpaceAndTime.Space.Integrals.Slice
public import PhyslibAlpha.Electromagnetism.Dynamics.IsWeakExtrema

/-!

# The thick wire is a weak extremum of the action

The potential of the infinite wire of radius `a` is only `C¹`, so the variational gradient
`gradLagrangian`, which is defined through smooth variational calculus, does not apply to it:
`IsExtrema` would hold for it only vacuously. The meaningful statement is `IsWeakExtrema`: the
first variation of the action vanishes for every test-function variation of the potential. This
file proves it.

The first variation of the lagrangian density splits into three pieces: a transverse part
`∇⊥A · ∇⊥δA`, an axial part `∇⊥A · ∂ₓδA⃗`, and the source part `J · δA`. Integrating over
spacetime in the coordinates `(t, x, (y, z))`, the axial part vanishes by the fundamental theorem
of calculus along the axis, and the transverse part is integrated by parts in the `(y, z)`-plane
using the radial integration by parts of `Space.integral_inner_radial_grad`, which is valid
across the surface of the wire where the second derivatives of the potential jump. The result
is minus the source part.

## Main results

- `axisPoint`, `integral_eq_integral_axisPoint` : spacetime integrals as iterated integrals in
  the coordinates adapted to the wire.
- `deriv_lagrangian_infiniteThickWire` : the first variation of the lagrangian density of the
  wire.
- `integral_thickWireVar₂`, `integral_thickWireVar₁_add_thickWireVar₃` : the axial part of the
  first variation integrates to zero, and the transverse and source parts cancel.
- `infiniteThickWire_isWeakExtrema` : the thick wire is a weak extremum of the action.

## Contents

- A. The potential as a function on spacetime
- B. Derivatives of the potential
- C. The first variation of the lagrangian density
- D. Slicing spacetime along the axis
- E. Derivatives along the slices
- F. Integrals over spacetime as iterated integrals
- G. Compactly supported functions on the line
- H. Sections of test functions
- I. The three pieces of the first variation
- J. The axial part integrates to zero
- K. The radial profile of the transverse gradient
- L. The transverse and source parts cancel
- M. The thick wire is a weak extremum

-/

@[expose] public section

namespace Electromagnetism
namespace ElectromagneticPotential
open SpaceTime minkowskiMatrix Lorentz.Vector Space MeasureTheory Set Filter Topology ContDiff
open InnerProductSpace
open scoped SchwartzMap

/-!

## A. The potential as a function on spacetime

-/

/-- The squared distance from the axis, as a function on spacetime. -/
def axisDistSqST (x : SpaceTime) : ℝ := x (Sum.inr 1) ^ 2 + x (Sum.inr 2) ^ 2

lemma axisDistSq_space (x : SpaceTime) : axisDistSq x.space = axisDistSqST x := rfl

/-- The `x`-component of the vector potential of the thick wire, as a function on spacetime. -/
noncomputable def thickWirePotentialFun (𝓕 : FreeSpace) (a I : ℝ) (x : SpaceTime) : ℝ :=
  - (I * 𝓕.μ₀) / (2 * Real.pi) * thickWireRadialProfile a (axisDistSqST x)

lemma thickWireCurrent_apply (a I : ℝ) (y : Space) (i : Fin 3) :
    thickWireCurrent a I y i =
      if i = 0 then (if axisDistSq y < a ^ 2 then I / (Real.pi * a ^ 2) else 0) else 0 := by
  simp only [thickWireCurrent]
  split_ifs <;> simp_all

lemma infiniteThickWire_apply (𝓕 : FreeSpace) (a I : ℝ) (x : SpaceTime) (ν : Fin 1 ⊕ Fin 3) :
    infiniteThickWire 𝓕 a I x ν =
      if ν = Sum.inr 0 then thickWirePotentialFun 𝓕 a I x else 0 := by
  match ν with
  | Sum.inl 0 => rfl
  | Sum.inr i =>
    change thickWireVectorPotential 𝓕 a I x.space i = _
    simp [thickWireVectorPotential, thickWirePotentialFun, axisDistSq_space]

lemma infiniteThickWire_apply_fun (𝓕 : FreeSpace) (a I : ℝ) (ν : Fin 1 ⊕ Fin 3) :
    (fun x => infiniteThickWire 𝓕 a I x ν) =
      if ν = Sum.inr 0 then thickWirePotentialFun 𝓕 a I else 0 := by
  funext x
  rw [infiniteThickWire_apply]
  split_ifs <;> rfl

lemma axisDistSqST_differentiable : Differentiable ℝ axisDistSqST := by
  unfold axisDistSqST
  have h1 : Differentiable ℝ (fun x : SpaceTime => x (Sum.inr 1)) :=
    (Lorentz.Vector.coordCLM (d := 3) (Sum.inr 1)).differentiable
  have h2 : Differentiable ℝ (fun x : SpaceTime => x (Sum.inr 2)) :=
    (Lorentz.Vector.coordCLM (d := 3) (Sum.inr 2)).differentiable
  fun_prop

lemma thickWirePotentialFun_differentiable (𝓕 : FreeSpace) {a : ℝ} (ha : 0 < a) (I : ℝ) :
    Differentiable ℝ (thickWirePotentialFun 𝓕 a I) := fun x =>
  (((hasDerivAt_thickWireRadialProfile ha _).differentiableAt).comp x
    (axisDistSqST_differentiable x)).const_mul _

lemma infiniteThickWire_differentiable (𝓕 : FreeSpace) {a : ℝ} (ha : 0 < a) (I : ℝ) :
    Differentiable ℝ (infiniteThickWire 𝓕 a I) := by
  rw [← SpaceTime.differentiable_vector]
  intro ν
  rw [infiniteThickWire_apply_fun]
  split_ifs
  · exact thickWirePotentialFun_differentiable 𝓕 ha I
  · exact differentiable_const 0

/-!

## B. Derivatives of the potential

-/

lemma deriv_axisDistSqST (μ : Fin 1 ⊕ Fin 3) (x : SpaceTime) :
    ∂_ μ axisDistSqST x = (if μ = Sum.inr 1 then 2 * x (Sum.inr 1) else 0) +
      (if μ = Sum.inr 2 then 2 * x (Sum.inr 2) else 0) := by
  have h1 : Differentiable ℝ (fun x : SpaceTime => x (Sum.inr 1)) :=
    (Lorentz.Vector.coordCLM (d := 3) (Sum.inr 1)).differentiable
  have h2 : Differentiable ℝ (fun x : SpaceTime => x (Sum.inr 2)) :=
    (Lorentz.Vector.coordCLM (d := 3) (Sum.inr 2)).differentiable
  unfold axisDistSqST
  rw [SpaceTime.deriv_eq, fderiv_fun_add (by fun_prop) (by fun_prop), _root_.add_apply,
    ((h1 x).hasFDerivAt.pow 2).fderiv, ((h2 x).hasFDerivAt.pow 2).fderiv, _root_.smul_apply,
    _root_.smul_apply, ← SpaceTime.deriv_eq, ← SpaceTime.deriv_eq, SpaceTime.deriv_coord,
    SpaceTime.deriv_coord]
  simp only [smul_eq_mul]
  split_ifs <;> simp_all

lemma deriv_thickWirePotentialFun (𝓕 : FreeSpace) {a : ℝ} (ha : 0 < a) (I : ℝ)
    (μ : Fin 1 ⊕ Fin 3) (x : SpaceTime) :
    ∂_ μ (thickWirePotentialFun 𝓕 a I) x =
      - (I * 𝓕.μ₀) / (2 * Real.pi) * (1 / (2 * max (axisDistSqST x) (a ^ 2))) *
        ∂_ μ axisDistSqST x := by
  have h := ((hasDerivAt_thickWireRadialProfile ha (axisDistSqST x)).comp_hasFDerivAt x
    (axisDistSqST_differentiable x).hasFDerivAt).const_mul (- (I * 𝓕.μ₀) / (2 * Real.pi))
  rw [SpaceTime.deriv_eq]
  change fderiv ℝ (fun y => _ * (thickWireRadialProfile a ∘ axisDistSqST) y) x
    (Lorentz.Vector.basis μ) = _
  rw [h.fderiv, SpaceTime.deriv_eq]
  simp [mul_assoc]

lemma deriv_infiniteThickWire_apply (𝓕 : FreeSpace) {a : ℝ} (ha : 0 < a) (I : ℝ)
    (μ ν : Fin 1 ⊕ Fin 3) (x : SpaceTime) :
    ∂_ μ (infiniteThickWire 𝓕 a I) x ν =
      if ν = Sum.inr 0 then ∂_ μ (thickWirePotentialFun 𝓕 a I) x else 0 := by
  rw [SpaceTime.deriv_apply_eq μ ν _ (infiniteThickWire_differentiable 𝓕 ha I),
    infiniteThickWire_apply_fun]
  split_ifs
  · rfl
  · simp

/-!

## C. The first variation of the lagrangian density

-/

/-- The first variation of the lagrangian density of the thick wire along a variation `δA`. -/
lemma deriv_lagrangian_infiniteThickWire (𝓕 : FreeSpace) {a : ℝ} (ha : 0 < a) (I : ℝ)
    (δA : SpaceTime → Lorentz.Vector) (hδA : Differentiable ℝ δA) (x : SpaceTime) :
    _root_.deriv (fun s : ℝ => lagrangian 𝓕 ⟨fun x' => infiniteThickWire 𝓕 a I x' + s • δA x'⟩
      (thickWireCurrentDensity 𝓕.c a I) x) 0 =
    I / (2 * Real.pi) * (x (Sum.inr 1) / max (axisDistSqST x) (a ^ 2) *
        (∂_ (Sum.inr 1) δA x (Sum.inr 0) - ∂_ (Sum.inr 0) δA x (Sum.inr 1)) +
      x (Sum.inr 2) / max (axisDistSqST x) (a ^ 2) *
        (∂_ (Sum.inr 2) δA x (Sum.inr 0) - ∂_ (Sum.inr 0) δA x (Sum.inr 2))) +
    δA x (Sum.inr 0) * thickWireCurrent a I (toTimeAndSpace 𝓕.c x).2 0 := by
  rw [deriv_lagrangian_add_smul _ _ _ (infiniteThickWire_differentiable 𝓕 ha I) hδA]
  simp only [deriv_infiniteThickWire_apply 𝓕 ha I, deriv_thickWirePotentialFun 𝓕 ha I,
    deriv_axisDistSqST, minkowskiProduct_toCoord]
  simp [Fintype.sum_sum_type, Fin.sum_univ_three, thickWireCurrentDensity, thickWireCurrent_apply,
    minkowskiMatrix.inr_i_inr_i]
  have hM : max (axisDistSqST x) (a ^ 2) ≠ 0 := (lt_max_of_lt_right (by positivity)).ne'
  field_simp
  ring

/-!

## D. Slicing spacetime along the axis

-/

/-- The point of spacetime at time `t`, coordinate `r` along the axis of the wire and
transverse position `q`. -/
noncomputable def axisPoint (c : SpeedOfLight) (t : Time) (r : ℝ) (q : Space 2) : SpaceTime :=
  (toTimeAndSpace c).symm (t, (slice 0).symm (r, q))

lemma toTimeAndSpace_axisPoint (c : SpeedOfLight) (t : Time) (r : ℝ) (q : Space 2) :
    toTimeAndSpace c (axisPoint c t r q) = (t, (slice 0).symm (r, q)) := by
  simp [axisPoint]

lemma slice_symm_apply_one (r : ℝ) (q : Space 2) : (slice 0).symm (r, q) 1 = q 0 := by
  rw [show (1 : Fin 3) = Fin.succAbove 0 0 from rfl, slice_symm_apply_succAbove]

lemma slice_symm_apply_two (r : ℝ) (q : Space 2) : (slice 0).symm (r, q) 2 = q 1 := by
  rw [show (2 : Fin 3) = Fin.succAbove 0 1 from rfl, slice_symm_apply_succAbove]

lemma axisDistSq_slice_symm (r : ℝ) (q : Space 2) :
    axisDistSq ((slice 0).symm (r, q)) = ‖q‖ ^ 2 := by
  rw [axisDistSq, slice_symm_apply_one, slice_symm_apply_two, ← real_inner_self_eq_norm_sq,
    Space.inner_eq_sum, Fin.sum_univ_two]
  ring

@[simp]
lemma axisPoint_inr_one (c : SpeedOfLight) (t : Time) (r : ℝ) (q : Space 2) :
    axisPoint c t r q (Sum.inr 1) = q 0 := by
  rw [axisPoint, toTimeAndSpace_symm_apply_inr, slice_symm_apply_one]

@[simp]
lemma axisPoint_inr_two (c : SpeedOfLight) (t : Time) (r : ℝ) (q : Space 2) :
    axisPoint c t r q (Sum.inr 2) = q 1 := by
  rw [axisPoint, toTimeAndSpace_symm_apply_inr, slice_symm_apply_two]

lemma axisDistSqST_axisPoint (c : SpeedOfLight) (t : Time) (r : ℝ) (q : Space 2) :
    axisDistSqST (axisPoint c t r q) = ‖q‖ ^ 2 := by
  rw [← axisDistSq_space, axisPoint, space_toTimeAndSpace_symm, axisDistSq_slice_symm]

lemma axisPoint_contDiff (c : SpeedOfLight) (t : Time) (r : ℝ) :
    ContDiff ℝ ∞ (axisPoint c t r) := by
  unfold axisPoint
  fun_prop

lemma axisPoint_isClosedEmbedding (c : SpeedOfLight) (t : Time) (r : ℝ) :
    Topology.IsClosedEmbedding (axisPoint c t r) := by
  have h1 : Topology.IsClosedEmbedding (fun y : Space => (t, y)) :=
    Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap (by fun_prop)
      (fun y y' h => (Prod.mk.inj h).2) (isClosedMap_prodMk_left t)
  have h2 : Topology.IsClosedEmbedding (fun q : Space 2 => (r, q)) :=
    Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap (by fun_prop)
      (fun y y' h => (Prod.mk.inj h).2) (isClosedMap_prodMk_left r)
  exact (toTimeAndSpace c).symm.toHomeomorph.isClosedEmbedding.comp
    (h1.comp ((slice 0).symm.toHomeomorph.isClosedEmbedding.comp h2))

lemma axisPoint_prod_isClosedEmbedding (c : SpeedOfLight) (t : Time) :
    Topology.IsClosedEmbedding (fun p : ℝ × Space 2 => axisPoint c t p.1 p.2) := by
  have h1 : Topology.IsClosedEmbedding (fun y : Space => (t, y)) :=
    Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap (by fun_prop)
      (fun y y' h => (Prod.mk.inj h).2) (isClosedMap_prodMk_left t)
  exact (toTimeAndSpace c).symm.toHomeomorph.isClosedEmbedding.comp
    (h1.comp (slice 0).symm.toHomeomorph.isClosedEmbedding)

/-!

## E. Derivatives along the slices

-/

/-- A transverse derivative on spacetime is a derivative of the transverse slice. -/
lemma deriv_inr_succAbove_axisPoint (c : SpeedOfLight) (f : SpaceTime → ℝ)
    (hf : Differentiable ℝ f) (t : Time) (r : ℝ) (q : Space 2) (j : Fin 2) :
    ∂_ (Sum.inr (Fin.succAbove 0 j)) f (axisPoint c t r q) =
      ∂[j] (fun q => f (axisPoint c t r q)) q := by
  rw [SpaceTime.deriv_sum_inr c f hf, toTimeAndSpace_axisPoint]
  simp only
  rw [Space.deriv_eq, basis_succAbove_eq_slice, Space.deriv_eq,
    ← fderiv_fun_slice_symm_right_apply 0 r q (basis j)
      (fun y => f ((toTimeAndSpace c).symm (t, y))) (by fun_prop)]
  rfl

/-- The derivative along the axis on spacetime is a derivative along the axial slice. -/
lemma deriv_inr_zero_axisPoint (c : SpeedOfLight) (f : SpaceTime → ℝ)
    (hf : Differentiable ℝ f) (t : Time) (r : ℝ) (q : Space 2) :
    ∂_ (Sum.inr 0) f (axisPoint c t r q) = _root_.deriv (fun r => f (axisPoint c t r q)) r := by
  rw [SpaceTime.deriv_sum_inr c f hf, toTimeAndSpace_axisPoint]
  simp only
  rw [Space.deriv_eq, basis_self_eq_slice,
    ← fderiv_fun_slice_symm_left_apply 0 r 1 q _ (by fun_prop)]
  rfl

/-!

## F. Integrals over spacetime as iterated integrals

-/

lemma integral_eq_integral_axisPoint (c : SpeedOfLight) (F : SpaceTime → ℝ) (hF : Integrable F)
    (hF' : ∀ t, Integrable (fun y : Space => F ((toTimeAndSpace c).symm (t, y)))) :
    ∫ x, F x = c.val • ∫ t : Time, ∫ r : ℝ, ∫ q : Space 2, F (axisPoint c t r q) := by
  rw [spaceTime_integral_eq_time_integral_space_integral c F hF]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  exact integral_eq_integral_slice 0 _ (hF' t)

/-!

## G. Compactly supported functions on the line

-/

lemma tendsto_atTop_of_hasCompactSupport {g : ℝ → ℝ} (hg : HasCompactSupport g) :
    Tendsto g atTop (𝓝 0) :=
  tendsto_const_nhds.congr' (((hasCompactSupport_iff_eventuallyEq.mp hg).filter_mono
    (atTop_le_cocompact.trans cocompact_le_coclosedCompact)).symm)

lemma tendsto_atBot_of_hasCompactSupport {g : ℝ → ℝ} (hg : HasCompactSupport g) :
    Tendsto g atBot (𝓝 0) :=
  tendsto_const_nhds.congr' (((hasCompactSupport_iff_eventuallyEq.mp hg).filter_mono
    (atBot_le_cocompact.trans cocompact_le_coclosedCompact)).symm)

/-- The integral of the derivative of a compactly supported `C¹` function vanishes. -/
lemma integral_deriv_eq_zero_of_hasCompactSupport {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hcs : HasCompactSupport g) : ∫ r, _root_.deriv g r = 0 := by
  rw [integral_of_hasDerivAt_of_tendsto (f := g)
    (fun r => (hg.differentiable one_ne_zero r).hasDerivAt)
    ((hg.continuous_deriv le_rfl).integrable_of_hasCompactSupport hcs.deriv)
    (tendsto_atBot_of_hasCompactSupport hcs) (tendsto_atTop_of_hasCompactSupport hcs), sub_zero]

/-!

## H. Sections of test functions

-/

lemma timeSection_isClosedEmbedding (c : SpeedOfLight) (t : Time) :
    Topology.IsClosedEmbedding (fun y : Space => (toTimeAndSpace c).symm (t, y)) := by
  have h1 : Topology.IsClosedEmbedding (fun y : Space => (t, y)) :=
    Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap (by fun_prop)
      (fun y y' h => (Prod.mk.inj h).2) (isClosedMap_prodMk_left t)
  exact (toTimeAndSpace c).symm.toHomeomorph.isClosedEmbedding.comp h1

lemma axisPoint_left_isClosedEmbedding (c : SpeedOfLight) (t : Time) (q : Space 2) :
    Topology.IsClosedEmbedding (fun r : ℝ => axisPoint c t r q) := by
  have h2 : Topology.IsClosedEmbedding (fun r : ℝ => (r, q)) :=
    Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap (by fun_prop)
      (fun y y' h => (Prod.mk.inj h).1) (isClosedMap_prodMk_right q)
  exact (timeSection_isClosedEmbedding c t).comp
    ((slice 0).symm.toHomeomorph.isClosedEmbedding.comp h2)

lemma toTimeAndSpace_snd (c : SpeedOfLight) (x : SpaceTime) : (toTimeAndSpace c x).2 = x.space :=
  rfl

/-- The coordinate derivatives of a test function are continuous. -/
lemma continuous_spaceTime_deriv_apply {δA : SpaceTime → Lorentz.Vector} (hδA : IsTestFunction δA)
    (μ ν : Fin 1 ⊕ Fin 3) : Continuous (fun x => ∂_ μ δA x ν) :=
  (Lorentz.Vector.coordCLM ν).continuous.comp
    ((hδA.smooth.continuous_fderiv (by simp)).clm_apply continuous_const)

/-- The coordinate derivatives of a test function have compact support. -/
lemma hasCompactSupport_spaceTime_deriv_apply {δA : SpaceTime → Lorentz.Vector}
    (hδA : IsTestFunction δA) (μ ν : Fin 1 ⊕ Fin 3) :
    HasCompactSupport (fun x => ∂_ μ δA x ν) :=
  (hδA.supp.fderiv (𝕜 := ℝ)).comp_left
    (g := fun L : SpaceTime →L[ℝ] Lorentz.Vector => L (basis μ) ν) (by simp)

/-!

## I. The three pieces of the first variation

-/

/-- The transverse part of the first variation of the lagrangian of the thick wire. -/
noncomputable def thickWireVar₁ (a I : ℝ) (δA : SpaceTime → Lorentz.Vector) (x : SpaceTime) :
    ℝ :=
  I / (2 * Real.pi) * (x (Sum.inr 1) / max (axisDistSqST x) (a ^ 2) *
    ∂_ (Sum.inr 1) δA x (Sum.inr 0) +
    x (Sum.inr 2) / max (axisDistSqST x) (a ^ 2) * ∂_ (Sum.inr 2) δA x (Sum.inr 0))

/-- The axial part of the first variation of the lagrangian of the thick wire. -/
noncomputable def thickWireVar₂ (a I : ℝ) (δA : SpaceTime → Lorentz.Vector) (x : SpaceTime) :
    ℝ :=
  - I / (2 * Real.pi) * (x (Sum.inr 1) / max (axisDistSqST x) (a ^ 2) *
    ∂_ (Sum.inr 0) δA x (Sum.inr 1) +
    x (Sum.inr 2) / max (axisDistSqST x) (a ^ 2) * ∂_ (Sum.inr 0) δA x (Sum.inr 2))

/-- The source part of the first variation of the lagrangian of the thick wire. -/
noncomputable def thickWireVar₃ (c : SpeedOfLight) (a I : ℝ) (δA : SpaceTime → Lorentz.Vector)
    (x : SpaceTime) : ℝ :=
  thickWireCurrent a I (toTimeAndSpace c x).2 0 * δA x (Sum.inr 0)

lemma deriv_lagrangian_infiniteThickWire_eq (𝓕 : FreeSpace) {a : ℝ} (ha : 0 < a) (I : ℝ)
    (δA : SpaceTime → Lorentz.Vector) (hδA : Differentiable ℝ δA) (x : SpaceTime) :
    _root_.deriv (fun s : ℝ => lagrangian 𝓕 ⟨fun x' => infiniteThickWire 𝓕 a I x' + s • δA x'⟩
      (thickWireCurrentDensity 𝓕.c a I) x) 0 =
    thickWireVar₁ a I δA x + thickWireVar₂ a I δA x + thickWireVar₃ 𝓕.c a I δA x := by
  rw [deriv_lagrangian_infiniteThickWire 𝓕 ha I δA hδA x]
  simp only [thickWireVar₁, thickWireVar₂, thickWireVar₃]
  ring

lemma continuous_div_max {a : ℝ} (ha : 0 < a) (i : Fin 3) :
    Continuous (fun x : SpaceTime => x (Sum.inr i) / max (axisDistSqST x) (a ^ 2)) :=
  (Lorentz.Vector.coordCLM (Sum.inr i)).continuous.div
    (axisDistSqST_differentiable.continuous.max continuous_const)
    fun _ => (lt_max_of_lt_right (pow_pos ha 2)).ne'

lemma thickWireVar₁_continuous {a : ℝ} (ha : 0 < a) (I : ℝ) {δA : SpaceTime → Lorentz.Vector}
    (hδA : IsTestFunction δA) : Continuous (thickWireVar₁ a I δA) := by
  unfold thickWireVar₁
  exact continuous_const.mul (((continuous_div_max ha 1).mul
    (continuous_spaceTime_deriv_apply hδA _ _)).add ((continuous_div_max ha 2).mul
    (continuous_spaceTime_deriv_apply hδA _ _)))

lemma thickWireVar₂_continuous {a : ℝ} (ha : 0 < a) (I : ℝ) {δA : SpaceTime → Lorentz.Vector}
    (hδA : IsTestFunction δA) : Continuous (thickWireVar₂ a I δA) := by
  unfold thickWireVar₂
  exact continuous_const.mul (((continuous_div_max ha 1).mul
    (continuous_spaceTime_deriv_apply hδA _ _)).add ((continuous_div_max ha 2).mul
    (continuous_spaceTime_deriv_apply hδA _ _)))

lemma thickWireVar₁_hasCompactSupport (a I : ℝ) {δA : SpaceTime → Lorentz.Vector}
    (hδA : IsTestFunction δA) : HasCompactSupport (thickWireVar₁ a I δA) := by
  unfold thickWireVar₁
  exact (((hasCompactSupport_spaceTime_deriv_apply hδA _ _).mul_left).add
    (hasCompactSupport_spaceTime_deriv_apply hδA _ _).mul_left).mul_left

lemma thickWireVar₂_hasCompactSupport (a I : ℝ) {δA : SpaceTime → Lorentz.Vector}
    (hδA : IsTestFunction δA) : HasCompactSupport (thickWireVar₂ a I δA) := by
  unfold thickWireVar₂
  exact (((hasCompactSupport_spaceTime_deriv_apply hδA _ _).mul_left).add
    (hasCompactSupport_spaceTime_deriv_apply hδA _ _).mul_left).mul_left

lemma thickWireCurrent_space_zero_eq (c : SpeedOfLight) (a I : ℝ) (x : SpaceTime) :
    thickWireCurrent a I (toTimeAndSpace c x).2 0 =
      if axisDistSqST x < a ^ 2 then I / (Real.pi * a ^ 2) else 0 := by
  rw [thickWireCurrent_apply, ite_eq_left rfl, toTimeAndSpace_snd, axisDistSq_space]

lemma thickWireCurrent_space_zero_measurable (c : SpeedOfLight) (a I : ℝ) :
    Measurable (fun x : SpaceTime => thickWireCurrent a I (toTimeAndSpace c x).2 0) := by
  simp only [thickWireCurrent_space_zero_eq]
  exact Measurable.ite (measurableSet_lt axisDistSqST_differentiable.continuous.measurable
    measurable_const) measurable_const measurable_const

lemma abs_thickWireCurrent_space_zero_le (c : SpeedOfLight) {a : ℝ} (ha : 0 < a) (I : ℝ)
    (x : SpaceTime) :
    |thickWireCurrent a I (toTimeAndSpace c x).2 0| ≤ |I| / (Real.pi * a ^ 2) := by
  rw [thickWireCurrent_space_zero_eq]
  split_ifs
  · rw [abs_div, abs_of_pos (show (0 : ℝ) < Real.pi * a ^ 2 by positivity)]
  · simp only [abs_zero]
    positivity

lemma thickWireVar₃_integrable (c : SpeedOfLight) {a : ℝ} (ha : 0 < a) (I : ℝ)
    {δA : SpaceTime → Lorentz.Vector} (hδA : IsTestFunction δA) :
    Integrable (thickWireVar₃ c a I δA) := by
  have h0 : Integrable (fun x => δA x (Sum.inr 0)) :=
    ((Lorentz.Vector.coordCLM (Sum.inr 0)).continuous.comp hδA.smooth.continuous)
      |>.integrable_of_hasCompactSupport (hδA.supp.comp_left (by simp))
  exact h0.bdd_mul (thickWireCurrent_space_zero_measurable c a I).aestronglyMeasurable
    (Eventually.of_forall fun x => (Real.norm_eq_abs _).trans_le
      (abs_thickWireCurrent_space_zero_le c ha I x))

lemma thickWireVar₃_section_integrable (c : SpeedOfLight) {a : ℝ} (ha : 0 < a) (I : ℝ)
    {δA : SpaceTime → Lorentz.Vector} (hδA : IsTestFunction δA) (t : Time) :
    Integrable (fun y : Space => thickWireVar₃ c a I δA ((toTimeAndSpace c).symm (t, y))) := by
  have h0 : Integrable (fun y : Space => δA ((toTimeAndSpace c).symm (t, y)) (Sum.inr 0)) := by
    refine Continuous.integrable_of_hasCompactSupport
      ((Lorentz.Vector.coordCLM (Sum.inr 0)).continuous.comp
        (hδA.smooth.continuous.comp (by fun_prop))) ?_
    exact (hδA.supp.comp_left (g := fun v : Lorentz.Vector => v (Sum.inr 0))
      (by simp)).comp_isClosedEmbedding (timeSection_isClosedEmbedding c t)
  exact h0.bdd_mul ((thickWireCurrent_space_zero_measurable c a I).comp
    (by fun_prop : Measurable fun y : Space => (toTimeAndSpace c).symm (t, y))).aestronglyMeasurable
    (Eventually.of_forall fun y => (Real.norm_eq_abs _).trans_le
      (abs_thickWireCurrent_space_zero_le c ha I _))

/-!

## J. The axial part integrates to zero

-/

lemma thickWireVar₂_axisPoint (c : SpeedOfLight) (a I : ℝ) {δA : SpaceTime → Lorentz.Vector}
    (hδA : IsTestFunction δA) (t : Time) (r : ℝ) (q : Space 2) :
    thickWireVar₂ a I δA (axisPoint c t r q) =
      - I / (2 * Real.pi) * (q 0 / max (‖q‖ ^ 2) (a ^ 2) *
          _root_.deriv (fun r => δA (axisPoint c t r q) (Sum.inr 1)) r +
        q 1 / max (‖q‖ ^ 2) (a ^ 2) *
          _root_.deriv (fun r => δA (axisPoint c t r q) (Sum.inr 2)) r) := by
  have hd : ∀ j : Fin 3, ∂_ (Sum.inr 0) δA (axisPoint c t r q) (Sum.inr j) =
      _root_.deriv (fun r => δA (axisPoint c t r q) (Sum.inr j)) r := fun j => by
    rw [SpaceTime.deriv_apply_eq _ _ _ hδA.differentiable, ← SpaceTime.deriv_eq,
      deriv_inr_zero_axisPoint c _
        ((SpaceTime.differentiable_vector δA).mpr hδA.differentiable (Sum.inr j))]
  simp only [thickWireVar₂, axisPoint_inr_one, axisPoint_inr_two, axisDistSqST_axisPoint, hd]

lemma axisPoint_left_contDiff (c : SpeedOfLight) (t : Time) (q : Space 2) :
    ContDiff ℝ ∞ (fun r : ℝ => axisPoint c t r q) := by
  unfold axisPoint
  fun_prop

lemma integral_thickWireVar₂_axisPoint (c : SpeedOfLight) (a I : ℝ)
    {δA : SpaceTime → Lorentz.Vector} (hδA : IsTestFunction δA) (t : Time) (q : Space 2) :
    ∫ r, thickWireVar₂ a I δA (axisPoint c t r q) = 0 := by
  simp only [thickWireVar₂_axisPoint c a I hδA t]
  have hg (j : Fin 3) : ContDiff ℝ 1 (fun r => δA (axisPoint c t r q) (Sum.inr j)) :=
    (Lorentz.Vector.coordCLM (Sum.inr j)).contDiff.comp
      ((hδA.smooth.of_le (WithTop.coe_le_coe.mpr le_top)).comp
        ((axisPoint_left_contDiff c t q).of_le (WithTop.coe_le_coe.mpr le_top)))
  have hcs (j : Fin 3) : HasCompactSupport (fun r => δA (axisPoint c t r q) (Sum.inr j)) :=
    (hδA.supp.comp_left (g := fun v : Lorentz.Vector => v (Sum.inr j))
      (by simp)).comp_isClosedEmbedding (axisPoint_left_isClosedEmbedding c t q)
  have hint (j : Fin 3) (k : ℝ) :
      Integrable (fun r => k * _root_.deriv (fun r => δA (axisPoint c t r q) (Sum.inr j)) r) :=
    (continuous_const.mul ((hg j).continuous_deriv le_rfl)).integrable_of_hasCompactSupport
      (hcs j).deriv.mul_left
  rw [integral_const_mul, integral_add (hint 1 _) (hint 2 _), integral_const_mul,
    integral_const_mul, integral_deriv_eq_zero_of_hasCompactSupport (hg 1) (hcs 1),
    integral_deriv_eq_zero_of_hasCompactSupport (hg 2) (hcs 2)]
  simp

lemma integral_thickWireVar₂ (𝓕 : FreeSpace) {a : ℝ} (ha : 0 < a) (I : ℝ)
    {δA : SpaceTime → Lorentz.Vector} (hδA : IsTestFunction δA) :
    ∫ x, thickWireVar₂ a I δA x = 0 := by
  have hcont := thickWireVar₂_continuous ha I hδA
  have hcs := thickWireVar₂_hasCompactSupport a I hδA
  rw [integral_eq_integral_axisPoint 𝓕.c _ (hcont.integrable_of_hasCompactSupport hcs)
    (fun t => (hcont.comp (by fun_prop)).integrable_of_hasCompactSupport
      (hcs.comp_isClosedEmbedding (timeSection_isClosedEmbedding 𝓕.c t)))]
  rw [show (∫ t : Time, ∫ r : ℝ, ∫ q : Space 2, thickWireVar₂ a I δA (axisPoint 𝓕.c t r q)) =
    ∫ t : Time, (0 : ℝ) from ?_]
  · simp
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  show ∫ r : ℝ, ∫ q : Space 2, thickWireVar₂ a I δA (axisPoint 𝓕.c t r q) = 0
  rw [integral_integral_swap ?_]
  · simp [integral_thickWireVar₂_axisPoint 𝓕.c a I hδA t]
  · refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact hcont.comp ((toTimeAndSpace 𝓕.c).symm.continuous.comp (continuous_const.prodMk
        ((slice 0).symm.continuous.comp (continuous_fst.prodMk continuous_snd))))
    · exact hcs.comp_isClosedEmbedding (axisPoint_prod_isClosedEmbedding 𝓕.c t)

/-!

## K. The radial profile of the transverse gradient

-/

/-- The radial function describing the transverse gradient of the potential: the gradient of
`thickWireRadialProfile a (‖q‖ ^ 2)` is `(thickWireRadial a ‖q‖ / ‖q‖ ^ 2) • q`. -/
noncomputable def thickWireRadial (a r : ℝ) : ℝ := r ^ 2 / max (r ^ 2) (a ^ 2)

/-- The derivative of `thickWireRadial`, away from `r = a`. -/
noncomputable def thickWireRadialDeriv (a r : ℝ) : ℝ :=
  (Ico 0 a).indicator (fun r => 2 * r / a ^ 2) r

lemma thickWireRadial_continuous {a : ℝ} (ha : 0 < a) : Continuous (thickWireRadial a) :=
  (continuous_pow 2).div ((continuous_pow 2).max continuous_const) fun r =>
    (lt_max_of_lt_right (by positivity)).ne'

lemma abs_thickWireRadial_le {a : ℝ} (ha : 0 < a) (r : ℝ) : |thickWireRadial a r| ≤ 1 := by
  have hpos : 0 < max (r ^ 2) (a ^ 2) := lt_max_of_lt_right (by positivity)
  rw [thickWireRadial, abs_of_nonneg (by positivity), div_le_one hpos]
  exact le_max_left _ _

lemma thickWireRadialDeriv_measurable (a : ℝ) : Measurable (thickWireRadialDeriv a) :=
  (by fun_prop : Measurable fun r : ℝ => 2 * r / a ^ 2).indicator measurableSet_Ico

lemma abs_thickWireRadialDeriv_le {a : ℝ} (ha : 0 < a) (r : ℝ) :
    |thickWireRadialDeriv a r| ≤ 2 / a := by
  rw [thickWireRadialDeriv]
  by_cases hr : r ∈ Ico 0 a
  · rw [indicator_of_mem hr, abs_of_nonneg (by have := hr.1; positivity),
      div_le_div_iff₀ (by positivity) ha]
    nlinarith [hr.1, hr.2]
  · rw [indicator_of_notMem hr, abs_zero]
    positivity

lemma hasDerivAt_thickWireRadial {a : ℝ} (ha : 0 < a) :
    ∀ r ∈ Ioi (0 : ℝ) \ {a}, HasDerivAt (thickWireRadial a) (thickWireRadialDeriv a r) r := by
  rintro r ⟨hr, hra⟩
  have hr : 0 < r := hr
  rcases lt_or_gt_of_ne (show r ≠ a from hra) with h | h
  · rw [thickWireRadialDeriv, indicator_of_mem (show r ∈ Ico 0 a from ⟨hr.le, h⟩)]
    have hd : HasDerivAt (fun r : ℝ => r ^ 2 / a ^ 2) (2 * r / a ^ 2) r := by
      simpa using (hasDerivAt_pow 2 r).div_const (a ^ 2)
    refine hd.congr_of_eventuallyEq (Filter.eventually_of_mem (Ioo_mem_nhds
      (show -a < r by linarith) h) fun t ht => ?_)
    rw [thickWireRadial, max_eq_right (by nlinarith [ht.1, ht.2])]
  · rw [thickWireRadialDeriv, indicator_of_notMem (fun h' => absurd h'.2 (not_lt.mpr h.le))]
    refine (hasDerivAt_const r (1 : ℝ)).congr_of_eventuallyEq (Filter.eventually_of_mem
      (Ioi_mem_nhds h) fun t ht => ?_)
    have ht : a < t := ht
    rw [thickWireRadial, max_eq_left (by nlinarith), div_self (by nlinarith)]

/-!

## L. The transverse and source parts cancel

-/

lemma thickWire_section_hasCompactSupport (c : SpeedOfLight) {δA : SpaceTime → Lorentz.Vector}
    (hδA : IsTestFunction δA) (t : Time) (r : ℝ) :
    HasCompactSupport (fun q : Space 2 => δA (axisPoint c t r q) (Sum.inr 0)) :=
  (hδA.supp.comp_left (g := fun v : Lorentz.Vector => v (Sum.inr 0))
    (by simp)).comp_isClosedEmbedding (axisPoint_isClosedEmbedding c t r)

lemma thickWire_section_contDiff (c : SpeedOfLight) {δA : SpaceTime → Lorentz.Vector}
    (hδA : IsTestFunction δA) (t : Time) (r : ℝ) :
    ContDiff ℝ ∞ (fun q : Space 2 => δA (axisPoint c t r q) (Sum.inr 0)) :=
  (Lorentz.Vector.coordCLM (Sum.inr 0)).contDiff.comp (hδA.smooth.comp (axisPoint_contDiff c t r))

/-- The transverse slice of the `x`-component of a test function, as a Schwartz function. -/
noncomputable def thickWireSection (c : SpeedOfLight) {δA : SpaceTime → Lorentz.Vector}
    (hδA : IsTestFunction δA) (t : Time) (r : ℝ) : 𝓢(Space 2, ℝ) :=
  (thickWire_section_hasCompactSupport c hδA t r).toSchwartzMap
    (thickWire_section_contDiff c hδA t r)

lemma thickWireSection_apply (c : SpeedOfLight) {δA : SpaceTime → Lorentz.Vector}
    (hδA : IsTestFunction δA) (t : Time) (r : ℝ) (q : Space 2) :
    thickWireSection c hδA t r q = δA (axisPoint c t r q) (Sum.inr 0) := rfl

lemma thickWireRadial_zero (a : ℝ) : thickWireRadial a 0 = 0 := by
  simp [thickWireRadial]

lemma thickWireRadial_mul_zpow_mul {a : ℝ} (ha : 0 < a) (q : Space 2) (j : Fin 2) :
    thickWireRadial a ‖q‖ * ‖q‖ ^ (-(2 : ℤ)) * q j = q j / max (‖q‖ ^ 2) (a ^ 2) := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  · have hn : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
    have hM : max (‖q‖ ^ 2) (a ^ 2) ≠ 0 := (lt_max_of_lt_right (by positivity)).ne'
    rw [thickWireRadial, zpow_neg, zpow_ofNat]
    field_simp

lemma thickWireVar₁_axisPoint (c : SpeedOfLight) {a : ℝ} (ha : 0 < a) (I : ℝ)
    {δA : SpaceTime → Lorentz.Vector} (hδA : IsTestFunction δA) (t : Time) (r : ℝ) (q : Space 2) :
    thickWireVar₁ a I δA (axisPoint c t r q) = I / (2 * Real.pi) *
      ⟪(thickWireRadial a ‖q‖ * ‖q‖ ^ (-(2 : ℤ))) • basis.repr q,
        ∇ (thickWireSection c hδA t r) q⟫_ℝ := by
  have hd (j : Fin 2) : ∂_ (Sum.inr (Fin.succAbove 0 j)) δA (axisPoint c t r q) (Sum.inr 0) =
      ∂[j] (thickWireSection c hδA t r) q := by
    rw [SpaceTime.deriv_apply_eq _ _ _ hδA.differentiable, ← SpaceTime.deriv_eq,
      deriv_inr_succAbove_axisPoint c _
        ((SpaceTime.differentiable_vector δA).mpr hδA.differentiable (Sum.inr 0))]
    rfl
  rw [inner_grad_eq, Fin.sum_univ_two]
  simp only [PiLp.smul_apply, Space.basis_repr_apply, smul_eq_mul,
    thickWireRadial_mul_zpow_mul ha]
  rw [thickWireVar₁, axisPoint_inr_one, axisPoint_inr_two, axisDistSqST_axisPoint,
    show (Sum.inr 1 : Fin 1 ⊕ Fin 3) = Sum.inr (Fin.succAbove 0 0) from rfl,
    show (Sum.inr 2 : Fin 1 ⊕ Fin 3) = Sum.inr (Fin.succAbove 0 1) from rfl, hd 0, hd 1]

lemma thickWireVar₃_axisPoint (c : SpeedOfLight) {a : ℝ} (ha : 0 < a) (I : ℝ)
    {δA : SpaceTime → Lorentz.Vector} (hδA : IsTestFunction δA) (t : Time) (r : ℝ) (q : Space 2) :
    thickWireVar₃ c a I δA (axisPoint c t r q) = I / (Real.pi * a ^ 2) *
      ((Metric.ball (0 : Space 2) a).indicator (fun _ => 1) q * thickWireSection c hδA t r q) := by
  rw [thickWireVar₃, thickWireCurrent_space_zero_eq, axisDistSqST_axisPoint,
    thickWireSection_apply]
  by_cases h : ‖q‖ < a
  · rw [ite_eq_left (pow_lt_pow_left₀ h (norm_nonneg q) two_ne_zero),
      indicator_of_mem (show q ∈ Metric.ball (0 : Space 2) a by simpa using h)]
    ring
  · rw [ite_eq_right (fun h' => h (lt_of_pow_lt_pow_left₀ 2 ha.le h')),
      indicator_of_notMem (show q ∉ Metric.ball (0 : Space 2) a by simpa using h)]
    ring

lemma thickWireRadialDeriv_mul_zpow_ae {a : ℝ} (ha : 0 < a) :
    ∀ᵐ q : Space 2, thickWireRadialDeriv a ‖q‖ * ‖q‖ ^ (1 - 2 : ℤ) =
      2 / a ^ 2 * (Metric.ball (0 : Space 2) a).indicator (fun _ => 1) q := by
  filter_upwards [Measure.ae_ne volume 0] with q hq
  have hn : 0 < ‖q‖ := norm_pos_iff.mpr hq
  by_cases h : ‖q‖ < a
  · rw [thickWireRadialDeriv, indicator_of_mem (show ‖q‖ ∈ Ico 0 a from ⟨hn.le, h⟩),
      indicator_of_mem (show q ∈ Metric.ball (0 : Space 2) a by simpa using h)]
    norm_num
    field_simp
  · rw [thickWireRadialDeriv, indicator_of_notMem (fun h' => h h'.2),
      indicator_of_notMem (show q ∉ Metric.ball (0 : Space 2) a by simpa using h)]
    simp

lemma integral_thickWireVar₁_add_thickWireVar₃_axisPoint (c : SpeedOfLight) {a : ℝ} (ha : 0 < a)
    (I : ℝ) {δA : SpaceTime → Lorentz.Vector} (hδA : IsTestFunction δA) (t : Time) (r : ℝ) :
    ∫ q, (thickWireVar₁ a I δA (axisPoint c t r q) + thickWireVar₃ c a I δA (axisPoint c t r q))
      = 0 := by
  set ψ := thickWireSection c hδA t r
  simp only [thickWireVar₁_axisPoint c ha I hδA t r, thickWireVar₃_axisPoint c ha I hδA t r]
  have hG : IsDistBounded (fun q : Space 2 =>
      (thickWireRadial a ‖q‖ * ‖q‖ ^ (-(2 : ℤ))) • basis.repr q) :=
    IsDistBounded.radial_smul_repr (d := 2) (thickWireRadial_continuous ha).measurable
      (abs_thickWireRadial_le ha)
  have hind : Integrable (fun q : Space 2 =>
      (Metric.ball (0 : Space 2) a).indicator (fun _ => (1 : ℝ)) q * ψ q) :=
    ψ.integrable.bdd_mul (c := 1) (measurable_const.indicator Metric.isOpen_ball.measurableSet
      |>.aestronglyMeasurable) (Eventually.of_forall fun q => by
        by_cases h : q ∈ Metric.ball (0 : Space 2) a <;> simp [h])
  rw [integral_add ((integrable_isDistBounded_inner_grad_schwartzMap hG ψ).const_mul _)
    (hind.const_mul _), integral_const_mul, integral_const_mul]
  have hrad := integral_inner_radial_grad (d := 2) (thickWireRadial_continuous ha)
    (abs_thickWireRadial_le ha) (thickWireRadialDeriv_measurable a)
    (abs_thickWireRadialDeriv_le ha) (countable_singleton a) (hasDerivAt_thickWireRadial ha) ψ
  simp only [Nat.cast_ofNat, thickWireRadial_zero, zero_mul, sub_zero] at hrad
  have hae : (fun q : Space 2 => ψ q * (thickWireRadialDeriv a ‖q‖ * ‖q‖ ^ (1 - 2 : ℤ))) =ᵐ[volume]
      fun q => 2 / a ^ 2 * ((Metric.ball (0 : Space 2) a).indicator (fun _ => (1 : ℝ)) q * ψ q) :=
    (thickWireRadialDeriv_mul_zpow_ae ha).mono fun q hq => by beta_reduce; rw [hq]; ring
  rw [hrad, integral_congr_ae hae, integral_const_mul]
  field_simp
  ring

lemma integral_thickWireVar₁_add_thickWireVar₃ (𝓕 : FreeSpace) {a : ℝ} (ha : 0 < a) (I : ℝ)
    {δA : SpaceTime → Lorentz.Vector} (hδA : IsTestFunction δA) :
    ∫ x, (thickWireVar₁ a I δA x + thickWireVar₃ 𝓕.c a I δA x) = 0 := by
  have h1c := thickWireVar₁_continuous ha I hδA
  have h1s := thickWireVar₁_hasCompactSupport a I hδA
  rw [integral_eq_integral_axisPoint 𝓕.c
    (fun x => thickWireVar₁ a I δA x + thickWireVar₃ 𝓕.c a I δA x)
    ((h1c.integrable_of_hasCompactSupport h1s).add (thickWireVar₃_integrable 𝓕.c ha I hδA))
    (fun t => ((h1c.comp (by fun_prop)).integrable_of_hasCompactSupport
      (h1s.comp_isClosedEmbedding (timeSection_isClosedEmbedding 𝓕.c t))).add
      (thickWireVar₃_section_integrable 𝓕.c ha I hδA t))]
  simp [integral_thickWireVar₁_add_thickWireVar₃_axisPoint 𝓕.c ha I hδA]

/-!

## M. The thick wire is a weak extremum

-/

/-- The potential of the thick wire is a weak extremum of the action with source the current of
the wire: the first variation of the action vanishes for every test-function variation. -/
theorem infiniteThickWire_isWeakExtrema (𝓕 : FreeSpace) {a : ℝ} (ha : 0 < a) (I : ℝ) :
    IsWeakExtrema 𝓕 (infiniteThickWire 𝓕 a I) (thickWireCurrentDensity 𝓕.c a I) := by
  intro δA hδA
  have h2c := thickWireVar₂_continuous ha I hδA
  have h2s := thickWireVar₂_hasCompactSupport a I hδA
  have h1c := thickWireVar₁_continuous ha I hδA
  have h1s := thickWireVar₁_hasCompactSupport a I hδA
  calc ∫ x, _root_.deriv (fun s : ℝ => lagrangian 𝓕
        ⟨fun x' => infiniteThickWire 𝓕 a I x' + s • δA x'⟩ (thickWireCurrentDensity 𝓕.c a I) x) 0
      = ∫ x, ((thickWireVar₁ a I δA x + thickWireVar₃ 𝓕.c a I δA x) +
          thickWireVar₂ a I δA x) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        beta_reduce
        rw [deriv_lagrangian_infiniteThickWire_eq 𝓕 ha I δA hδA.differentiable]
        ring
    _ = 0 := by
        rw [integral_add (μ := volume) (show Integrable (fun x => thickWireVar₁ a I δA x +
          thickWireVar₃ 𝓕.c a I δA x) volume from (h1c.integrable_of_hasCompactSupport h1s).add
          (thickWireVar₃_integrable 𝓕.c ha I hδA)) (h2c.integrable_of_hasCompactSupport h2s),
          integral_thickWireVar₁_add_thickWireVar₃ 𝓕 ha I hδA, integral_thickWireVar₂ 𝓕 ha I hδA,
          add_zero]

end ElectromagneticPotential
end Electromagnetism
