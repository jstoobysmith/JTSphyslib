/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.GaugeKineticTerm.BoostWeight
/-!
# The invariant photon pairs

An invariant element of the span of the products `F_{μν} F_{μ'ν'}` is a combination of the
Maxwell term `F_{μν} F^{μν}` and the theta term `ε^{μνρσ} F_{μν} F_{ρσ}`: the gauge sector has
no other Lorentz invariant quadratic in the field strength.

Only one implication of `boostWeight_inter_fieldStrength_full` is used, and only through the
boosts: an invariant element has boost weight zero along each of the three axes
(`mem_boostWeightSubmodule_zero_of_isInvariant`), which is already enough to pin it down. The
converse — that the two terms are invariant — is where the boost weight zero statement came
from in the first place.

## Key results

- `JetAlgebra.mem_gauge_kinetic_span_eq_maxwell_theta_of_isInvariant` : an invariant photon
  pair is a combination of the Maxwell and theta terms.

-/

@[expose] public section

namespace LeptonGaugeSector
open TensorProduct StandardModel

namespace JetAlgebra

/-!

## The key theorem

-/

/-- **The invariant photon pairs are the Maxwell and theta terms.** An invariant element of the
  span of the products `F_{μν} F_{μ'ν'}` lies in the span of `maxwellTerm` and `thetaTerm`. -/
lemma mem_gauge_kinetic_span_eq_maxwell_theta_of_isInvariant {x : JetAlgebra}
    (hx : IsInvariant x)
    (ht : x ∈ Submodule.span ℂ
      {y | ∃ μ ν μ' ν', y = fieldStrengthDeriv {} μ ν * fieldStrengthDeriv {} μ' ν'}) :
    x ∈ Submodule.span ℂ {maxwellTerm, thetaTerm} := by
  rw [← boostWeight_inter_fieldStrength_full]
  exact ⟨⟨⟨mem_boostWeightSubmodule_zero_of_isInvariant hx,
    mem_boostWeightSubmodule_zero_of_isInvariant hx⟩,
    mem_boostWeightSubmodule_zero_of_isInvariant hx⟩, ht⟩

end JetAlgebra

end LeptonGaugeSector

end
