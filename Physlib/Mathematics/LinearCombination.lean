/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Nathaneal Sajan
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.LinearMap.Defs
/-!
# Finite linear combinations under a linear map

A family `T : ι → B` of vectors of a module, indexed by a finite type, has the combinations
`∑ i, c i • T i` for coefficients `c : ι → R`. Two bookkeeping identities about them: contracting
against coefficients moved by a matrix regroups as the same combination of the matrix-moved
components, and a linear map given on the family by a matrix moves a combination by that matrix
acting on the coefficients.
-/

@[expose] public section

variable {ι κ R B B' : Type*} [Fintype ι] [Fintype κ] [CommSemiring R]
  [AddCommMonoid B] [Module R B] [AddCommMonoid B'] [Module R B']

/-- Contracting the components against coefficients moved by a matrix is the original
  combination of the matrix-moved components. -/
lemma Fintype.sum_sum_mul_smul (M : ι → κ → R) (c : κ → R) (T : ι → B) :
    ∑ a, (∑ d, c d * M a d) • T a = ∑ d, c d • ∑ a, M a d • T a := by
  simp only [Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

/-- A linear map that moves each component of a family by a matrix moves a combination of the
  components by that matrix acting on the coefficients, with the free index first. -/
lemma LinearMap.map_sum_smul_of_forall_eq (φ : B →ₗ[R] B') (T : ι → B) (T' : κ → B')
    (M : κ → ι → R) (hT : ∀ l, φ (T l) = ∑ a, M a l • T' a) (c : ι → R) :
    φ (∑ l, c l • T l) = ∑ a, (∑ l, c l * M a l) • T' a := by
  rw [map_sum, Fintype.sum_sum_mul_smul]
  exact Finset.sum_congr rfl fun l _ => by rw [map_smul, hT]
