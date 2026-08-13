/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Boosts.WeightGrading
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
/-!
# Class IsLorentzDeriv

-/

@[expose] public section

namespace Lorentz

open Matrix MatrixGroups TensorProduct

variable {A : Type} [Ring A] [Algebra ℂ A]

class IsLorentzDeriv (rep : Representation ℂ SL(2,ℂ) A) (D : (Fin 1 ⊕ Fin 3) → A →ₗ[ℂ] A) where
  rep_deriv {Λ μ x} : rep Λ (D μ  x) = ∑ a, (SL2C.toLorentzGroup Λ).1 a μ • D a (rep Λ x)

namespace IsLorentzDeriv

/-!

## Light cone derivatives

-/

def lightConePlus (D : (Fin 1 ⊕ Fin 3) → A →ₗ[ℂ] A) (i : Fin 3) : A →ₗ[ℂ] A :=
  D (Sum.inl 0) - D (Sum.inr i)

def lightConeMinus (D : (Fin 1 ⊕ Fin 3) → A →ₗ[ℂ] A) (i : Fin 3) : A →ₗ[ℂ] A :=
  D (Sum.inl 0) + D (Sum.inr i)

/-!

## Relationship to boost weights

-/

end IsLorentzDeriv

end Lorentz

end
