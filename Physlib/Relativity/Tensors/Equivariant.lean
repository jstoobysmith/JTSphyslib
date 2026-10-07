/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.Basic
/-!
# Equivariant maps out of the tensors of a species

## i. Overview

A family of vectors in a representation `ρ` of the group `G` of a tensor species `S`, carrying
indices of colors `c`, is packaged as a linear map `f : S.Tensor c →ₗ[k] B`, and
`S.IsEquivariant c ρ f` says that `f` intertwines the action of `G` on tensors with `ρ` (A).

A map is specified by its values on the basis tensors with `Basis.constr`, and
`isEquivariant_constr` turns a transformation law of those values into equivariance (B).

## ii. Key results

- `TensorSpecies.IsEquivariant` : equivariant linear maps out of `S.Tensor c`.
- `TensorSpecies.smul_basis_eq_sum` : the action on the basis tensors.
- `TensorSpecies.isEquivariant_constr` : a map defined on basis tensors is equivariant when its
  values obey the transformation law of the basis tensors.

## iii. Table of contents

- A. Equivariant maps and the action on basis tensors
- B. Building equivariant maps

## iv. References

* None.

-/

@[expose] public section

namespace TensorSpecies

open Module Matrix Tensor

/-!

## A. Equivariant maps and the action on basis tensors

-/

section General

variable {k : Type} [CommRing k] {C G : Type} [Group G]
  {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
  {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
  {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Basis (basisIdx c) k (V c)}

/-- A linear map `f` from the tensors of the species `S` with index colors `c` to a
  representation `ρ` of the group of the species, which is equivariant: it intertwines the action
  of the group on tensors with `ρ`. -/
structure IsEquivariant (S : TensorSpecies k C G V basisIdx rep b) {n : ℕ} (c : Fin n → C)
    {B : Type*} [AddCommMonoid B] [Module k B] (ρ : Representation k G B)
    (f : S.Tensor c →ₗ[k] B) : Prop where
  equivariant : ∀ (g : G) (t : S.Tensor c), f (g • t) = ρ g (f t)

variable {S : TensorSpecies k C G V basisIdx rep b}

/-- The action of `g` on a basis tensor: the coefficient of `e_ψ` in `g • e_φ` is the product over
  the indices of the matrix entries of `g` in the color of that index. -/
lemma smul_basis_eq_sum {n : ℕ} (c : Fin n → C) (g : G) (φ : ComponentIdx (S := S) c) :
    g • Tensor.basis (S := S) c φ
      = ∑ ψ : ComponentIdx (S := S) c,
        (∏ i, LinearMap.toMatrix (b (c i)) (b (c i)) (rep (c i) g) (ψ i) (φ i)) •
        Tensor.basis (S := S) c ψ := by
  simp only [Tensor.basis_apply, LinearMap.toMatrix_apply]
  rw [actionT_pure]
  have h : g • Pure.basisVector (S := S) c φ
      = (fun i => ∑ j, (b (c i)).repr (rep (c i) g (b (c i) (φ i))) j • b (c i) j :
        Pure S c) := by
    funext i
    exact ((b (c i)).sum_repr _).symm
  rw [h]
  unfold Pure.toTensor
  rw [MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [← MultilinearMap.map_smul_univ]
  rfl

/-- The components of `g • t`: the matrix of products of the matrix entries of `g`, one factor
  per index, applied to the components of `t`. -/
lemma basis_repr_smul {n : ℕ} (c : Fin n → C) (g : G) (t : S.Tensor c)
    (φ : ComponentIdx (S := S) c) :
    (Tensor.basis c).repr (g • t) φ
      = ∑ ψ, (∏ i, LinearMap.toMatrix (b (c i)) (b (c i)) (rep (c i) g) (φ i) (ψ i)) *
        (Tensor.basis c).repr t ψ := by
  conv_lhs => rw [← (Tensor.basis (S := S) c).sum_repr t]
  rw [actionT_eq, map_sum, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  congr 1
  have h := smul_basis_eq_sum c g ψ
  rw [actionT_eq] at h
  rw [h, map_sum]
  simp [Finsupp.single_apply]

namespace IsEquivariant

variable {n : ℕ} {c : Fin n → C} {B : Type*} [AddCommGroup B] [Module k B]
  {ρ : Representation k G B} {f : S.Tensor c →ₗ[k] B} (hf : S.IsEquivariant c ρ f)

include hf in
/-- The image of an invariant tensor under an equivariant map is invariant. -/
lemma rep_map_of_invariant {t : S.Tensor c} (ht : ∀ g : G, g • t = t) (g : G) :
    ρ g (f t) = f t := by
  rw [← hf.equivariant, ht]

/-- A sum of equivariant maps is equivariant. -/
lemma sum {ι : Type*} (s : Finset ι) {F : ι → S.Tensor c →ₗ[k] B}
    (hF : ∀ i ∈ s, S.IsEquivariant c ρ (F i)) : S.IsEquivariant c ρ (∑ i ∈ s, F i) where
  equivariant g t := by
    rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
    exact Finset.sum_congr rfl fun i hi => (hF i hi).equivariant g t

include hf in
/-- Composing with a linear map that intertwines `ρ` with `ρ'` keeps a map equivariant. -/
lemma comp {B' : Type*} [AddCommGroup B'] [Module k B'] {ρ' : Representation k G B'}
    (σ : B →ₗ[k] B') (hσ : ∀ (g : G) (y : B), σ (ρ g y) = ρ' g (σ y)) :
    S.IsEquivariant c ρ' (σ ∘ₗ f) where
  equivariant g t := by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hf.equivariant, hσ]

include hf in
/-- A difference of equivariant maps is equivariant. -/
lemma sub {f' : S.Tensor c →ₗ[k] B} (hf' : S.IsEquivariant c ρ f') :
    S.IsEquivariant c ρ (f - f') where
  equivariant g t := by
    rw [LinearMap.sub_apply, LinearMap.sub_apply, map_sub, hf.equivariant, hf'.equivariant]

end IsEquivariant

end General

/-!

## B. Building equivariant maps

-/

section Constr

variable {k : Type} [CommRing k] {C G : Type} [Group G]
  {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
  {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
  {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Basis (basisIdx c) k (V c)}
  {S : TensorSpecies k C G V basisIdx rep b}

/-- The linear map with prescribed values `T ψ` on the basis tensors is equivariant when the
  values are moved by `ρ` as the basis tensors are moved by the group. -/
lemma isEquivariant_constr {n : ℕ} {c : Fin n → C} {B : Type*} [AddCommGroup B] [Module k B]
    {ρ : Representation k G B} (T : ComponentIdx (S := S) c → B)
    (hT : ∀ (g : G) φ, ρ g (T φ)
      = ∑ ψ, (∏ i, LinearMap.toMatrix (b (c i)) (b (c i)) (rep (c i) g) (ψ i) (φ i)) • T ψ) :
    S.IsEquivariant c ρ ((Tensor.basis c).constr k T) where
  equivariant g t := by
    have h : (Tensor.basis c).constr k T ∘ₗ PiTensorProduct.map (fun i => rep (c i) g)
        = ρ g ∘ₗ (Tensor.basis c).constr k T := by
      refine (Tensor.basis (S := S) c).ext fun φ => ?_
      have h1 := smul_basis_eq_sum (S := S) c g φ
      rw [actionT_eq] at h1
      simp only [LinearMap.comp_apply, h1, map_sum, map_smul, Module.Basis.constr_basis, hT]
    exact LinearMap.congr_fun h t

end Constr

end TensorSpecies
