/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
/-!
# Representations acting by algebra maps

## i. Overview

A representation of a monoid on an algebra need not respect the multiplication; the ones
that do are the ones a field theory uses, and this file collects the two constructions on
them that are otherwise missing.

Section A is about `Representation.tprod` on a tensor product of two algebras. The unit and
the product of `A ⊗[k] B` are given by those of the factors, so a pair of unit-preserving
or multiplicative representations gives one on the tensor product. The lemmas are stated at
abstract types with the factor laws as hypotheses, which is what lets them be applied at a
large concrete algebra without unfolding it: neither the unit nor the product of a free
algebra presented as a quotient can be reduced cheaply.

Section B restricts a representation to a subalgebra it preserves. The invariance
hypothesis is stated pointwise, in the form the ambient invariance lemmas produce.

## ii. Key results

- `Representation.tprod_apply_one`, `Representation.tprod_apply_one_tmul`,
  `Representation.tprod_apply_tmul_one` : the unit laws on a tensor product.
- `Representation.tprod_apply_mul` : multiplicativity on a tensor product.
- `Representation.restrictSubalgebra` : the restriction to an invariant subalgebra.

## iii. Table of contents

- A. Tensor products of multiplicative representations
- B. Restriction to an invariant subalgebra

-/

@[expose] public section

open TensorProduct

namespace Representation

/-!

## A. Tensor products of multiplicative representations

-/

/-- The tensor product of two unit-preserving representations preserves the unit. -/
lemma tprod_apply_one {k G A B : Type*} [CommSemiring k] [Monoid G]
    [Ring A] [Algebra k A] [Ring B] [Algebra k B]
    (ρ : Representation k G A) (σ : Representation k G B) (g : G)
    (hρ : ρ g 1 = 1) (hσ : σ g 1 = 1) : (ρ.tprod σ) g 1 = 1 := by
  rw [Algebra.TensorProduct.one_def, Representation.tprod_apply, TensorProduct.map_tmul,
    hρ, hσ, ← Algebra.TensorProduct.one_def]

/-- On a pure tensor whose left entry is the unit only the right factor moves. -/
lemma tprod_apply_one_tmul {k G A B : Type*} [CommSemiring k]
    [Monoid G] [Ring A] [Algebra k A] [Ring B] [Algebra k B]
    (ρ : Representation k G A) (σ : Representation k G B) (g : G)
    (hρ : ρ g 1 = 1) (y : B) :
    (ρ.tprod σ) g ((1 : A) ⊗ₜ[k] y) = (1 : A) ⊗ₜ[k] σ g y := by
  rw [Representation.tprod_apply, TensorProduct.map_tmul, hρ]

/-- On a pure tensor whose right entry is the unit only the left factor moves. -/
lemma tprod_apply_tmul_one {k G A B : Type*} [CommSemiring k]
    [Monoid G] [Ring A] [Algebra k A] [Ring B] [Algebra k B]
    (ρ : Representation k G A) (σ : Representation k G B) (g : G) (x : A)
    (hσ : σ g 1 = 1) :
    (ρ.tprod σ) g (x ⊗ₜ[k] (1 : B)) = ρ g x ⊗ₜ[k] (1 : B) := by
  rw [Representation.tprod_apply, TensorProduct.map_tmul, hσ]

/-- The tensor product of two multiplicative representations on algebras is
  multiplicative. -/
lemma tprod_apply_mul {k G A B : Type*} [CommSemiring k] [Monoid G]
    [Ring A] [Algebra k A] [Ring B] [Algebra k B]
    (ρ : Representation k G A) (σ : Representation k G B)
    (hρ : ∀ (g : G) (x y : A), ρ g (x * y) = ρ g x * ρ g y)
    (hσ : ∀ (g : G) (x y : B), σ g (x * y) = σ g x * σ g y)
    (g : G) (x y : A ⊗[k] B) :
    (ρ.tprod σ) g (x * y) = (ρ.tprod σ) g x * (ρ.tprod σ) g y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => rw [add_mul, map_add, map_add, h₁, h₂, add_mul]
  | tmul a₁ b₁ =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ => rw [mul_add, map_add, map_add, h₁, h₂, mul_add]
    | tmul a₂ b₂ =>
      rw [Algebra.TensorProduct.tmul_mul_tmul,
        show (ρ.tprod σ) g (a₁ ⊗ₜ[k] b₁) = ρ g a₁ ⊗ₜ[k] σ g b₁ from rfl,
        show (ρ.tprod σ) g (a₂ ⊗ₜ[k] b₂) = ρ g a₂ ⊗ₜ[k] σ g b₂ from rfl,
        show (ρ.tprod σ) g ((a₁ * a₂) ⊗ₜ[k] (b₁ * b₂))
          = ρ g (a₁ * a₂) ⊗ₜ[k] σ g (b₁ * b₂) from rfl,
        hρ, hσ, Algebra.TensorProduct.tmul_mul_tmul]

/-!

## B. Restriction to an invariant subalgebra

-/

/-- The restriction of a representation to a subalgebra each group element preserves. -/
noncomputable def restrictSubalgebra {k A G : Type*} [CommSemiring k]
    [Monoid G] [Semiring A] [Algebra k A] (ρ : Representation k G A) (S : Subalgebra k A)
    (hS : ∀ (g : G) {x : A}, x ∈ S → ρ g x ∈ S) : Representation k G S where
  toFun g :=
    { toFun := fun x => ⟨ρ g (x : A), hS g x.2⟩
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
      map_smul' := fun _ _ => Subtype.ext (map_smul _ _ _) }
  map_one' := LinearMap.ext fun x => Subtype.ext
    (LinearMap.congr_fun (map_one ρ) (x : A))
  map_mul' g₁ g₂ := LinearMap.ext fun x => Subtype.ext
    (LinearMap.congr_fun (map_mul ρ g₁ g₂) (x : A))

@[simp]
lemma coe_restrictSubalgebra {k A G : Type*} [CommSemiring k]
    [Monoid G] [Semiring A] [Algebra k A] (ρ : Representation k G A) (S : Subalgebra k A)
    (hS : ∀ (g : G) {x : A}, x ∈ S → ρ g x ∈ S) (g : G) (x : S) :
    (ρ.restrictSubalgebra S hS g x : A) = ρ g (x : A) := rfl

end Representation
