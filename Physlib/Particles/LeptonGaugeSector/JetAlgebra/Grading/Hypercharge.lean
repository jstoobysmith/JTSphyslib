/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.MassDim
public import Physlib.Relativity.LorentzGroup.FermionicParity
/-!
# Grading due to hypercharge

The JetAlgebra can be mapped into a `LaurentPolynomial` mapping generators
to exponents of the generator `T` corresponding to their hypercharge.
This map is an algebra map. For example `ψ ↦ T^(-6) • ψ`

In the same way which mass dimension is defined through `Polynomial`,
we define a grading on `JetAlgebra` through `LaurentPolynomial`.

This grading can be used to define a projection from `JetAlgebra` to itself
picking out only the subspace of terms which are charge singlets.

Every term which is invariant is stable under this projection.
This result trivially generalizes to any theory based on the SM gauge group.

-/

@[expose] public section

namespace LeptonGaugeSector
open TensorProduct StandardModel Matrix MatrixGroups LorentzGroup

namespace JetAlgebra

end JetAlgebra

end LeptonGaugeSector

end
