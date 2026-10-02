/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.SpaceAndTime.Space.Derivatives.Curl
/-!

# Locality of derivatives on `Space`

## i. Overview

The spatial derivatives `∂[i]`, the divergence and the curl of a function at a point only
depend on the function in a neighbourhood of that point. This lets one compute them for
functions which are only smooth on part of space, by comparing with a function that agrees
with them locally.

## ii. Key results

- `Space.deriv_eventuallyEq` : functions agreeing near `x` have derivatives agreeing near `x`.
- `Space.div_congr_of_eventuallyEq` : functions agreeing near `x` have the same divergence at `x`.
- `Space.curl_eventuallyEq` : functions agreeing near `x` have curls agreeing near `x`.

## iii. Table of contents

- A. Derivatives
- B. The divergence
- C. The curl

## iv. References

* None.
-/

@[expose] public section

open Filter Topology

namespace Space

/-!

## A. Derivatives

-/

lemma deriv_congr_of_eventuallyEq {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {f g : Space d → M} {x : Space d} (h : f =ᶠ[𝓝 x] g) (μ : Fin d) :
    ∂[μ] f x = ∂[μ] g x := by
  rw [deriv_eq, deriv_eq, h.fderiv_eq]

lemma deriv_eventuallyEq {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {f g : Space d → M} {x : Space d} (h : f =ᶠ[𝓝 x] g) (μ : Fin d) :
    ∂[μ] f =ᶠ[𝓝 x] ∂[μ] g :=
  h.eventuallyEq_nhds.mono fun _ hy => deriv_congr_of_eventuallyEq hy μ

/-!

## B. The divergence

-/

lemma div_congr_of_eventuallyEq {d} {f g : Space d → EuclideanSpace ℝ (Fin d)} {x : Space d}
    (h : f =ᶠ[𝓝 x] g) : (∇ ⬝ f) x = (∇ ⬝ g) x := by
  refine Finset.sum_congr rfl fun i _ => deriv_congr_of_eventuallyEq ?_ i
  exact h.mono fun _ hy => by simp only [hy]

/-!

## C. The curl

-/

lemma curl_eventuallyEq {f g : Space → EuclideanSpace ℝ (Fin 3)} {x : Space}
    (h : f =ᶠ[𝓝 x] g) : (∇ ⨯ f) =ᶠ[𝓝 x] (∇ ⨯ g) := by
  have hc (i : Fin 3) : (fun y => f y i) =ᶠ[𝓝 x] fun y => g y i :=
    h.mono fun _ hy => by simp only [hy]
  filter_upwards [deriv_eventuallyEq (hc 0) 1, deriv_eventuallyEq (hc 0) 2,
    deriv_eventuallyEq (hc 1) 0, deriv_eventuallyEq (hc 1) 2, deriv_eventuallyEq (hc 2) 0,
    deriv_eventuallyEq (hc 2) 1] with y h01 h02 h10 h12 h20 h21
  ext i
  fin_cases i <;> simp [curl, h01, h02, h10, h12, h20, h21]

end Space
