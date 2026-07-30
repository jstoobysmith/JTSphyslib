/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Jinzheng Li, Nathaneal Sajan
-/
module

public import Physlib.Particles.LagrangianTheory.Basic

/-!

# The Standard Model EFT Lagrangian with derivatives

## i. Overview

-/

@[expose] public section

namespace LagrangianTheory

open TensorProduct Matrix MatrixGroups

variable {G : Type} [Group G]


variable {L : LagrangianTheory G}

abbrev EFTLagrangianFreeDeriv (L : LagrangianTheory G)  : Type :=
  -- complex scalar part of the lagrangian
  L.ComplexScalarEFTFreeDeriv ⊗[ℂ]
   L.RealBosonEFTFreeDerivComplex ⊗[ℂ] L.FermionicEFTFreeDeriv


#synth Ring L.EFTLagrangianFreeDeriv
namespace EFTLagrangianExclDeriv

variable {L : LagrangianTheory G}
/-!

## A. The invariance conditions

-/

/-!

### A.1. The representation

We define the representation of the Lorentz group on the full algebra.

-/

noncomputable def repLorentzGroup :  Representation ℂ SL(2,ℂ) L.EFTLagrangianFreeDeriv :=
  ((ComplexScalarEFTFreeDeriv.repLorentzGroup (L := L)).tprod
    (RealBosonEFTFreeDerivComplex.repLorentzGroup (L := L))).tprod
    (FermionicEFTFreeDeriv.repLorentzGroup (L := L))

lemma repLorentzGroup_mul (Λ : SL(2,ℂ)) (V W : L.EFTLagrangianFreeDeriv) :
    repLorentzGroup Λ (V * W) = repLorentzGroup Λ V * repLorentzGroup Λ W :=
  map_mul (Algebra.TensorProduct.map
    (SymmetricAlgebra.lift
      (SymmetricAlgebra.ι ℂ _ ∘ₗ ComplexScalarComponentSpace.repLorentzGroup Λ))
    (ExteriorAlgebra.map (FermionicComponentSpace.repLorentzGroup Λ))) V W

@[simp]
lemma repLorentzGroup_one (Λ : SL(2,ℂ)) :
    repLorentzGroup Λ 1 = 1 :=
  map_one (Algebra.TensorProduct.map
    (SymmetricAlgebra.lift
      (SymmetricAlgebra.ι ℂ _ ∘ₗ ComplexScalarComponentSpace.repLorentzGroup Λ))
    (ExteriorAlgebra.map (FermionicComponentSpace.repLorentzGroup Λ)))


noncomputable def repGaugeGroup :  Representation ℂ G L.EFTLagrangianFreeDeriv :=
  ((ComplexScalarEFTFreeDeriv.repGaugeGroup (L := L)).tprod
    (RealBosonEFTFreeDerivComplex.repGaugeGroup (L := L))).tprod
    (FermionicEFTFreeDeriv.repGaugeGroup (L := L))

/-!

### A.2. The IsInvariant condition

-/



end EFTLagrangianExclDeriv

end LagrangianTheory
