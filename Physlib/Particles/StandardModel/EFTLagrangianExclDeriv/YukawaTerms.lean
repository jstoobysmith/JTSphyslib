/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Jinzheng Li, Nathaneal Sajan
-/
module

public import Physlib.Particles.StandardModel.EFTLagrangianExclDeriv.Basic
/-!

# The Yukawa terms in the EFT lagrangian

-/

@[expose] public section

namespace StandardModel
namespace EFTLagrangianExclDeriv
noncomputable section

open Module Matrix
open MatrixGroups
open Complex
open TensorProduct
open CategoryTheory.MonoidalCategory
open Fermion

def yukawaTermLeH : EFTLagrangianExclDeriv := sorry

lemma yukawaTermLeH_invariant : IsInvariant yukawaTermLeH := by
  sorry

end
