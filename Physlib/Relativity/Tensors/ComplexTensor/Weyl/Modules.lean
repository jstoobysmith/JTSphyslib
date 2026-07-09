/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Physlib.Meta.TODO.Basic
/-!

## Modules associated with Fermions

Weyl fermions live in the vector space `ℂ^2`, defined here as `Fin 2 → ℂ`.
However if we simply define the Module of Weyl fermions as `Fin 2 → ℂ` we get casting problems,
where e.g. left-handed fermions can be cast to right-handed fermions etc.
To overcome this, for each type of Weyl fermion we define a structure that wraps `Fin 2 → ℂ`,
and these structures we define the instance of a module. This prevents casting between different
types of fermions.


-/

@[expose] public section

namespace Fermion
noncomputable section

end
end Fermion
