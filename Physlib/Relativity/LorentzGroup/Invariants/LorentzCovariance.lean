/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Invariants.Basic
/-!
# Lorentz covariance of component families

A family `T` of vectors of a complex module `B`, indexed by `n` spacetime directions and moved
by a representation of `SL(2,ℂ)` with one factor of the Lorentz matrix per index, is what the
rank-specific files of this folder classify the invariants of. This file holds the predicate
saying so, at an arbitrary number of indices, together with the part of its interface that does
not depend on that number.

The transformation law is

`repLorentz g (T l) = ∑_a (∏ i, Λ(g)_{a i, l i}) • T a`,

with `l` free and `a` summed, and the summed index first in each factor of the Lorentz matrix
`Λ(g)` of `g`. That is how the basis vectors of a tensor power of the vector representation
move, and `Invariants.act` is the matching action on coefficients.

Nothing here assumes the components independent or `B` finite dimensional: the span of the
components, Mathlib's `Submodule.span ℂ (Set.range T)`, is taken as it is, and a vector of it is
written as a combination in a way that need not be unique. The rank-zero
case is admitted and says that every component is invariant.
-/

@[expose] public section

namespace Lorentz

open Matrix MatrixGroups SL2C Invariants

/-!

## A. Families transforming with one Lorentz matrix per index

-/

/-- A family `T` of vectors of `B`, one per index vector `l : Fin n → Fin 1 ⊕ Fin 3`, which
  `repLorentz` moves the way the components of a rank-`n` tensor `T^{μ₁ ⋯ μₙ}` transform: one
  factor of the Lorentz matrix per slot, the moved index second in each factor and the summed
  one first. -/
structure IsLorentzCovariant (n : ℕ) (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B)
    (T : (Fin n → (Fin 1 ⊕ Fin 3)) → B) : Prop where
  repLorentz_T : ∀ (g : SL(2,ℂ)) l,
    repLorentz g (T l) = ∑ (a : Fin n → Fin 1 ⊕ Fin 3),
    (∏ (i : Fin n), (((SL2C.toLorentzGroup g).1 (a i) (l i) : ℝ) : ℂ)) • T a

namespace IsLorentzCovariant

section Monoid

variable {n : ℕ} {B : Type*} [AddCommMonoid B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {T : (Fin n → (Fin 1 ⊕ Fin 3)) → B}

/-- The image of the family under a linear map intertwining the two representations is again
  such a family. The map is not assumed injective or surjective. -/
lemma map {B' : Type*} [AddCommMonoid B'] [Module ℂ B'] {rep' : Representation ℂ SL(2,ℂ) B'}
    (hT : IsLorentzCovariant n B repLorentz T) (f : B →ₗ[ℂ] B')
    (hf : ∀ (g : SL(2,ℂ)) (y : B), f (repLorentz g y) = rep' g (f y)) :
    IsLorentzCovariant n B' rep' fun l => f (T l) where
  repLorentz_T g l := by
    rw [← hf, hT.repLorentz_T g l, map_sum]
    exact Finset.sum_congr rfl fun a _ => map_smul _ _ _

/-- The span of the components is Lorentz stable: each component goes to a combination of the
  components. -/
lemma repLorentz_mem_span_range (hT : IsLorentzCovariant n B repLorentz T) (g : SL(2,ℂ))
    {x : B} (hx : x ∈ Submodule.span ℂ (Set.range T)) :
    repLorentz g x ∈ Submodule.span ℂ (Set.range T) := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hx
  exact (Submodule.mem_span_range_iff_exists_fun ℂ).2
    ⟨_, (repLorentz_sum_smul hT.repLorentz_T g c).symm⟩

end Monoid

section Group

variable {n : ℕ} {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {T : (Fin n → (Fin 1 ⊕ Fin 3)) → B}

/-- The classes of the components in the quotient by a Lorentz-stable submodule again form a
  Lorentz tensor family of the same rank, for Mathlib's quotient representation. -/
lemma quotient (hT : IsLorentzCovariant n B repLorentz T) (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) :
    IsLorentzCovariant n (B ⧸ S) (repLorentz.quotient S fun g y hy => hS g y hy)
      fun l => S.mkQ (T l) :=
  hT.map S.mkQ fun _ _ => rfl

/-- A Lorentz invariant lying in the span of the components is the contraction of a coefficient
  tensor that the Lorentz matrices themselves fix. -/
lemma exists_isInvariantCoeff_of_mem_span_range
    (hT : IsLorentzCovariant n B repLorentz T) {x : B} (hx : x ∈ Submodule.span ℂ (Set.range T))
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ, IsInvariantCoeff c ∧ x = ∑ d, c d • T d :=
  Invariants.exists_isInvariantCoeff_of_mem_span hT.repLorentz_T hx hinv

/-- Contracting the components with an invariant coefficient tensor gives a Lorentz
  invariant. -/
lemma isInvariant_sum_smul (hT : IsLorentzCovariant n B repLorentz T)
    {c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ} (hc : IsInvariantCoeff c) (g : SL(2,ℂ)) :
    repLorentz g (∑ d, c d • T d) = ∑ d, c d • T d :=
  repLorentz_sum_smul_of_isInvariantCoeff hT.repLorentz_T hc g

end Group

end IsLorentzCovariant

/-!

## B. The quotient representation on classes

Dividing out a Lorentz-stable submodule `S` uses Mathlib's `Representation.quotient`. The
stability hypothesis is kept in the membership form the rest of the library uses, and converted
where Mathlib asks for the `comap` form.

-/

/-- The quotient representation on `B ⧸ S` moves the class of `y` by moving `y`. -/
lemma quotient_apply_mkQ {B : Type*} [AddCommGroup B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B) (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (g : SL(2,ℂ)) (y : B) :
    repLorentz.quotient S (fun g y hy => hS g y hy) g (S.mkQ y) = S.mkQ (repLorentz g y) := rfl

end Lorentz
