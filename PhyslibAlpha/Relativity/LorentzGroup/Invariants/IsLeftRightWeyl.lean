/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Relativity.LorentzGroup.Invariants.IsBiLeftWeyl
/-!
# Lorentz invariants of a left-handed and a right-handed Weyl index

## i. Overview

A bispinor `T^{α α'}`, carrying one left-handed and one right-handed Weyl index, has no Lorentz
invariant but `0`: the pair carries the `(1/2, 1/2)` representation, a single four-vector index,
which has nothing to contract with. The same holds for the dual pair `T_{α α'}`. The families are
equivariant linear maps out of `ℂT[.upL, .upR]` and `ℂT[.downL, .downR]`, `IsLeftRightWeyl` and
`IsDualLeftRightWeyl` (A).

By `TensorSpecies.IsEquivariant.reducesInvariantsTo_bot` it is enough that the only invariant
tensor is zero (B). A tensor with two indices is `fromPairT` of an element of the tensor product
of the two Weyl representations, and two Weyl indices of opposite chirality have no invariants,
`Fermion.LeftHandedWeyl.invariants_tprod_rightHandedWeyl_eq_bot` and
`Fermion.DualLeftHandedWeyl.invariants_tprod_dualRightHandedWeyl_eq_bot`. The classification of
the invariants of a family follows (C).

## ii. Key results

- `Lorentz.eq_zero_of_invariant_leftRight` : an invariant tensor with a left- and a
  right-handed Weyl index is zero.
- `Lorentz.IsLeftRightWeyl.reducesInvariantsTo_bot` : the invariants of the range of a
  left-right family reduce to `⊥`.
- `Lorentz.IsDualLeftRightWeyl.reducesInvariantsTo_bot` : the same for the dual indices.

## iii. Table of contents

- A. Left-right families as equivariant maps
- B. The invariant tensors vanish
- C. The classification of the invariants

## iv. References

* None.

-/

@[expose] public section

namespace Lorentz

open Matrix MatrixGroups SL2C Invariants TensorSpecies Tensor complexLorentzTensor

/-!

## A. Left-right families as equivariant maps

-/

/-- A family with a left- and a right-handed Weyl index `T^{α α'}`: an equivariant linear map
  out of `ℂT[.upL, .upR]`. -/
abbrev IsLeftRightWeyl (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B) (f : ℂT[.upL, .upR] →ₗ[ℂ] B) : Prop :=
  complexLorentzTensor.IsEquivariant ![.upL, .upR] repLorentz f

/-- A family with a dual left- and a dual right-handed Weyl index `T_{α α'}`: an equivariant
  linear map out of `ℂT[.downL, .downR]`. -/
abbrev IsDualLeftRightWeyl (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B) (f : ℂT[.downL, .downR] →ₗ[ℂ] B) : Prop :=
  complexLorentzTensor.IsEquivariant ![.downL, .downR] repLorentz f

/-!

## B. The invariant tensors vanish

-/

/-- An invariant tensor with a left- and a right-handed Weyl index, or with their duals, is
  zero: it comes from the tensor product of the two Weyl representations, which has no
  invariants but zero. -/
lemma eq_zero_of_invariant_leftRight {k k' : complexLorentzTensor.Color}
    (hk : (k = .upL ∧ k' = .upR) ∨ (k = .downL ∧ k' = .downR)) {t : ℂT[k, k']}
    (ht : ∀ g : SL(2,ℂ), g • t = t) : t = 0 := by
  rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Tensor.eq_zero_of_invariant_of_invariants_eq_bot (S := complexLorentzTensor)
      (c1 := .upL) (c2 := .upR) Fermion.LeftHandedWeyl.invariants_tprod_rightHandedWeyl_eq_bot ht
  · exact Tensor.eq_zero_of_invariant_of_invariants_eq_bot (S := complexLorentzTensor)
      (c1 := .downL) (c2 := .downR)
      Fermion.DualLeftHandedWeyl.invariants_tprod_dualRightHandedWeyl_eq_bot ht

/-!

## C. The classification of the invariants

-/

variable {B : Type*} [AddCommGroup B] [Module ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B}

/-- The invariants of the range of a left-right family reduce to `⊥`: a Lorentz invariant of
  `LinearMap.range f ⊔ S`, for `S` a Lorentz-stable submodule, lies in `S`. -/
lemma IsLeftRightWeyl.reducesInvariantsTo_bot {f : ℂT[.upL, .upR] →ₗ[ℂ] B}
    (hf : IsLeftRightWeyl B repLorentz f) :
    ReducesInvariantsTo (fun g : SL(2,ℂ) => repLorentz g) (LinearMap.range f) ⊥ :=
  TensorSpecies.IsEquivariant.reducesInvariantsTo_bot hf (complexLorentzTensor.isAdjointClosed _)
    fun _ ht => eq_zero_of_invariant_leftRight (Or.inl ⟨rfl, rfl⟩) ht

/-- Every Lorentz invariant in the range of a left-right family is zero. -/
lemma IsLeftRightWeyl.eq_zero_of_invariant {f : ℂT[.upL, .upR] →ₗ[ℂ] B}
    (hf : IsLeftRightWeyl B repLorentz f) {x : B} (hx : x ∈ LinearMap.range f)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x = 0 :=
  TensorSpecies.IsEquivariant.eq_zero_of_invariant hf (complexLorentzTensor.isAdjointClosed _)
    (fun _ ht => eq_zero_of_invariant_leftRight (Or.inl ⟨rfl, rfl⟩) ht) hx hinv

/-- The invariants of the range of a dual left-right family reduce to `⊥`: a Lorentz invariant
  of `LinearMap.range f ⊔ S`, for `S` a Lorentz-stable submodule, lies in `S`. -/
lemma IsDualLeftRightWeyl.reducesInvariantsTo_bot {f : ℂT[.downL, .downR] →ₗ[ℂ] B}
    (hf : IsDualLeftRightWeyl B repLorentz f) :
    ReducesInvariantsTo (fun g : SL(2,ℂ) => repLorentz g) (LinearMap.range f) ⊥ :=
  TensorSpecies.IsEquivariant.reducesInvariantsTo_bot hf (complexLorentzTensor.isAdjointClosed _)
    fun _ ht => eq_zero_of_invariant_leftRight (Or.inr ⟨rfl, rfl⟩) ht

/-- Every Lorentz invariant in the range of a dual left-right family is zero. -/
lemma IsDualLeftRightWeyl.eq_zero_of_invariant {f : ℂT[.downL, .downR] →ₗ[ℂ] B}
    (hf : IsDualLeftRightWeyl B repLorentz f) {x : B} (hx : x ∈ LinearMap.range f)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x = 0 :=
  TensorSpecies.IsEquivariant.eq_zero_of_invariant hf (complexLorentzTensor.isAdjointClosed _)
    (fun _ ht => eq_zero_of_invariant_leftRight (Or.inr ⟨rfl, rfl⟩) ht) hx hinv

end Lorentz
