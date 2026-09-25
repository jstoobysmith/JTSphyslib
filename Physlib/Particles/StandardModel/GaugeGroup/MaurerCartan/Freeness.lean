/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.LocalGaugeData
/-!
# Freeness of the Standard Model jets

## i. Overview

A local-gauge-data package is `Free` when its jets are honest formal power series in the
spacetime coordinates: every family of base-point Taylor data is realized by an element of
the jet Lie algebra (Taylor completeness), and every element vanishing at the base point
is the radial component `∑_μ x_μ ω_μ(U)` of the Maurer–Cartan form of some pure jet
(radial integrability). The general theory then makes the symmetrized Maurer–Cartan data
free coordinates on the pure jets, `LocalGaugeData.symmetrizedMaurerCartanCoeff_bijective`,
which is what the classification of gauge invariants uses. The Standard Model package is
free because each of its factors is and freeness passes to products.

## ii. Key results

- `StandardModel.instFreeLocalGaugeData` : the package is free.

-/

@[expose] public section

namespace StandardModel

/-- The Standard Model package is free. It is the local gauge data of the factors
  `SU(3)`, `SU(2)` and `U(1)`, each free, and freeness passes to products:
  `LocalGaugeData.instFreeOfFactors`. The symmetrized Maurer–Cartan data are therefore free
  coordinates on its pure jets, by `LocalGaugeData.symmetrizedMaurerCartanCoeff_bijective`. -/
instance instFreeLocalGaugeData : localGaugeData.Free := LocalGaugeData.instFreeOfFactors _

end StandardModel
