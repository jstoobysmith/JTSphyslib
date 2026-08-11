/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.GaugeDoubleDeriv.BoostWeight
/-!
# The invariant second derivatives of the field strength

An invariant element of the span of the monomials `∂_ρ ∂_τ F_{μν}` is zero: the gauge sector has
no Lorentz invariant linear in the field strength. A scalar built from `∂_ρ ∂_τ F_{μν}` would
have to contract the symmetric derivative pair with the antisymmetric index pair of the field
strength, and that contraction vanishes.

Only one implication of `boostWeight_inter_fieldStrengthDeriv_pair_full` is used, and only
through the boosts: an invariant element has boost weight zero along each of the three axes
(`mem_boostWeightSubmodule_zero_of_isInvariant`), which is already enough to force it to vanish.

## Key results

- `JetAlgebra.eq_zero_of_isInvariant_of_mem_span_fieldStrengthDeriv_pair` : an invariant second
  derivative of the field strength is zero.

-/

@[expose] public section

namespace LeptonGaugeSector
open TensorProduct StandardModel

namespace JetAlgebra

/-!

## The key theorem

-/

/-- **There is no invariant second derivative of the field strength.** An invariant element of
  the span of the monomials `∂_ρ ∂_τ F_{μν}` is zero. -/
lemma eq_zero_of_isInvariant_of_mem_span_fieldStrengthDeriv_pair {x : JetAlgebra}
    (hx : IsInvariant x)
    (ht : x ∈ Submodule.span ℂ {y | ∃ ρ τ μ ν, y = fieldStrengthDeriv {ρ, τ} μ ν}) :
    x = 0 := by
  have hb : x ∈ (⊥ : Submodule ℂ JetAlgebra) := by
    rw [← boostWeight_inter_fieldStrengthDeriv_pair_full]
    exact ⟨⟨⟨mem_boostWeightSubmodule_zero_of_isInvariant hx,
      mem_boostWeightSubmodule_zero_of_isInvariant hx⟩,
      mem_boostWeightSubmodule_zero_of_isInvariant hx⟩, ht⟩
  simpa using hb

end JetAlgebra

end LeptonGaugeSector

end
