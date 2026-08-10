/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.FermionicParity
public import Mathlib.Algebra.Polynomial.Laurent
/-!
# Grading by irreps

We can grade the *covariant algebra* by irreducible representations of the
global gauge group and the Lorentz group.

The irreps are determine the number of covariant derivatives acting on which field.

This grading is invariant under the action of both the gauge transformation
and the Lorentz group.

-/
