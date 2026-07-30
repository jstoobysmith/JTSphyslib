/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Jinzheng Li, Nathaneal Sajan
-/
module

public import Physlib.Particles.LagrangianTheory.Basic
/-!

# The Standard Model EFT Lagrangian without derivatives

## i. Overview

-/

@[expose] public section

namespace LagrangianTheory

open TensorProduct Matrix MatrixGroups

variable {G : Type} [Group G]


abbrev EFTLagrangianExclDeriv (L : LagrangianTheory G)  : Type :=
  -- bosonic part of the lagrangian
  L.ComplexScalarEFTExclDeriv ⊗[ℂ]
  -- fermionic part of the lagrangian
  L.FermionicEFTExclDeriv

namespace EFTLagrangianExclDeriv

variable {L : LagrangianTheory G}
/-!

## A. The invariance conditions

-/

/-!

### A.1. The representation

-/

noncomputable def repLorentzGroup : Representation ℂ SL(2,ℂ) L.EFTLagrangianExclDeriv :=
  (ComplexScalarEFTExclDeriv.repLorentzGroup).tprod (FermionicEFTExclDeriv.repLorentzGroup)


end EFTLagrangianExclDeriv

end LagrangianTheory
