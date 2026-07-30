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


variable {L : LagrangianTheory G}

abbrev EFTLagrangianExclDeriv (L : LagrangianTheory G)  : Type :=
  -- complex scalar part of the lagrangian
  L.ComplexScalarEFTExclDeriv ⊗[ℂ]
   L.RealBosonEFTExclDerivComplex ⊗[ℂ] L.FermionicEFTExclDeriv

namespace EFTLagrangianExclDeriv

variable {L : LagrangianTheory G}


set_option maxSynthPendingDepth 4 in
noncomputable instance : Ring (L.EFTLagrangianExclDeriv) := inferInstanceAs <|
  Ring (L.ComplexScalarEFTExclDeriv ⊗[ℂ]
   L.RealBosonEFTExclDerivComplex ⊗[ℂ] L.FermionicEFTExclDeriv)

set_option maxSynthPendingDepth 4 in
noncomputable instance : Algebra ℂ (L.EFTLagrangianExclDeriv) := inferInstanceAs <|
  Algebra ℂ (L.ComplexScalarEFTExclDeriv ⊗[ℂ]
   L.RealBosonEFTExclDerivComplex ⊗[ℂ] L.FermionicEFTExclDeriv)

/-!

## A. The invariance conditions

-/

/-!

### A.1. The representation

-/

noncomputable def repLorentzGroup :  Representation ℂ SL(2,ℂ) L.EFTLagrangianExclDeriv :=
  ((ComplexScalarEFTExclDeriv.repLorentzGroup (L := L)).tprod
    (RealBosonEFTExclDerivComplex.repLorentzGroup (L := L))).tprod
    (FermionicEFTExclDeriv.repLorentzGroup (L := L))


end EFTLagrangianExclDeriv

end LagrangianTheory
