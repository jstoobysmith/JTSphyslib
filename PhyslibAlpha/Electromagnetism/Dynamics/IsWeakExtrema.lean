/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Electromagnetism.Dynamics.IsExtrema

/-!

# Weak extrema of the electromagnetic action

The variational gradient `gradLagrangian` is only defined for smooth potentials. For potentials
which are differentiable but not smooth, such as the potential of a current which jumps across a
surface, the extremality condition is instead expressed through the first variation of the
action: `A` is a weak extremum if the first variation of the action vanishes for every
test-function variation of the potential. For smooth data this is implied by `IsExtrema`.

## Main results

- `IsWeakExtrema` : the first variation of the action vanishes for every test-function
  variation of the potential.
- `IsExtrema.isWeakExtrema` : for smooth data, an extremum of the action is a weak extremum.

## Contents

- A. Weak extrema

-/

@[expose] public section

namespace Electromagnetism
open ContDiff InnerProductSpace

namespace ElectromagneticPotential

/-!

## A. Weak extrema

-/

/-- The potential `A` is a weak extremum of the action with source `J`: the first variation
of the action vanishes for every test-function variation `δA` of the potential. -/
def IsWeakExtrema {d} (𝓕 : FreeSpace) (A : ElectromagneticPotential d)
    (J : LorentzCurrentDensity d) : Prop :=
  ∀ δA : SpaceTime d → Lorentz.Vector d, IsTestFunction δA →
    ∫ x, _root_.deriv (fun s : ℝ => lagrangian 𝓕 ⟨fun x => A x + s • δA x⟩ J x) 0 = 0

/-- For smooth data, an extremum of the action is a weak extremum. -/
lemma IsExtrema.isWeakExtrema {𝓕 : FreeSpace} {A : ElectromagneticPotential d}
    {J : LorentzCurrentDensity d} (hA : ContDiff ℝ ∞ A) (hJ : ContDiff ℝ ∞ J)
    (h : IsExtrema 𝓕 A J) : IsWeakExtrema 𝓕 A J := by
  intro δA hδA
  obtain ⟨F', hF', hgrad⟩ := lagrangian_hasVarGradientAt_gradLagrangian A hA J hJ
  have hadj := hF'.adjoint
  set F : (SpaceTime d → Lorentz.Vector d) → SpaceTime d → ℝ := fun δu x =>
    _root_.deriv (fun s : ℝ => lagrangian 𝓕 ⟨fun x' => A x' + s • δu x'⟩ J x) 0 with hF
  have hFδ : IsTestFunction (F δA) := hadj.test_fun_preserving δA hδA
  obtain ⟨L, hL, hloc⟩ := hadj.ext' (tsupport δA) hδA.supp
  -- A bump function equal to `1` on `L` and on the support of `F δA`.
  obtain ⟨R, hR⟩ := (hL.union hFδ.supp).isBounded.subset_closedBall 0
  let b : ContDiffBump (0 : SpaceTime d) := ⟨max R 1, max R 1 + 1, by positivity, by linarith⟩
  have hψ : IsTestFunction (⇑b) := ⟨b.contDiff, b.hasCompactSupport⟩
  have hb1 : ∀ x ∈ L ∪ tsupport (F δA), b x = 1 := fun x hx =>
    b.one_of_mem_closedBall (Metric.closedBall_subset_closedBall (le_max_left R 1) (hR hx))
  have h0 : F' (fun _ => 1) = 0 := by rw [← hgrad]; exact h
  calc ∫ x, F δA x
      _ = ∫ x, ⟪F δA x, b x⟫_ℝ := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        by_cases hx : x ∈ tsupport (F δA)
        · simp [hb1 x (Set.mem_union_right _ hx)]
        · simp [image_eq_zero_of_notMem_tsupport hx]
      _ = ∫ x, ⟪δA x, F' (⇑b) x⟫_ℝ := hadj.adjoint δA (⇑b) hδA hψ
      _ = 0 := by
        refine MeasureTheory.integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
        show ⟪δA x, F' (⇑b) x⟫_ℝ = 0
        by_cases hx : x ∈ tsupport δA
        · rw [hloc (⇑b) (fun _ => 1) (fun y hy => hb1 y (Set.mem_union_left _ hy)) x hx, h0]
          simp
        · simp [image_eq_zero_of_notMem_tsupport hx]

end ElectromagneticPotential

end Electromagnetism
