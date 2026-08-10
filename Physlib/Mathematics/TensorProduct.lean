/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Simultaneous fixed submodules under tensor extension

Let `F : ι → Module.End R M` be a family of linear endomorphisms. Its simultaneous fixed
submodule is the intersection `⋂ i, LinearMap.eqLocus (F i) LinearMap.id`.

If `C` is a free `R`-module and every `F i` acts on `M ⊗[R] C` through the `M` factor, then the
simultaneous fixed submodule of the extended family is the tensor extension of the original fixed
submodule. The corresponding result also holds for `C ⊗[R] M`, with the endomorphisms acting on
the right factor.

The proof chooses a basis of `C`, the tensor factor on which the extended endomorphisms act by the
identity. An element of the tensor product then has a unique finite expansion in this basis,
and it is fixed exactly when each coefficient in `M` is fixed. This only requires `C` to be free
as an `R`-module.

This allows a fixed-point calculation on one module to be reused after tensoring with a free module
on which the endomorphisms act as the identity. For example, the added factor may be an exterior
algebra over a field, even though it contains nilpotent elements.

-/

@[expose] public section

open scoped TensorProduct

namespace TensorProduct

/-!

## A. Coefficient decompositions and tensor maps

Mathlib's `equivFinsuppOfBasisRight` and `equivFinsuppOfBasisLeft` express a tensor as a finitely
supported family of coefficients after choosing a basis of one tensor factor. The following
lemmas show that applying a linear map to the other factor applies that map independently to every
coefficient.

-/

/-- Let `𝒞` be a basis of the right tensor factor. The `i`-th coefficient of
`f.rTensor C x` is `f` applied to the `i`-th coefficient of `x`. -/
lemma equivFinsuppOfBasisRight_rTensor_apply
    {R M N C κ : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [AddCommMonoid C] [Module R C] [DecidableEq κ]
    (𝒞 : Module.Basis κ R C) (f : M →ₗ[R] N) (x : M ⊗[R] C) (i : κ) :
    equivFinsuppOfBasisRight 𝒞 (f.rTensor C x) i =
      f (equivFinsuppOfBasisRight 𝒞 x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m c =>
      rw [LinearMap.rTensor_tmul, equivFinsuppOfBasisRight_apply_tmul_apply,
        equivFinsuppOfBasisRight_apply_tmul_apply, map_smul]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

/-- Let `𝒞` be a basis of the left tensor factor. The `i`-th coefficient of
`f.lTensor C x` is `f` applied to the `i`-th coefficient of `x`. -/
lemma equivFinsuppOfBasisLeft_lTensor_apply
    {R M N C κ : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [AddCommMonoid C] [Module R C] [DecidableEq κ]
    (𝒞 : Module.Basis κ R C) (f : M →ₗ[R] N) (x : C ⊗[R] M) (i : κ) :
    equivFinsuppOfBasisLeft 𝒞 (f.lTensor C x) i =
      f (equivFinsuppOfBasisLeft 𝒞 x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c m =>
      rw [LinearMap.lTensor_tmul, equivFinsuppOfBasisLeft_apply_tmul_apply,
        equivFinsuppOfBasisLeft_apply_tmul_apply, map_smul]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

end TensorProduct

namespace LinearMap

/-!

## B. Simultaneous fixed submodules

The simultaneous fixed submodule of `F` is the intersection of the equalizers of `F i` and the
identity. For a submodule `P ≤ M`, its extension inside `M ⊗[R] C` is
`Submodule.map₂ (TensorProduct.mk R M C) P ⊤`. This is the submodule spanned by the elementary
tensors `m ⊗ₜ c` with `m ∈ P`. When `C` is free, a tensor is fixed by every extended
endomorphism exactly when each of its coefficients belongs to the simultaneous fixed
submodule of `F`.

-/

/-- Simultaneous fixed submodules after tensoring on the right by a free module. -/
lemma iInf_eqLocus_rTensor
    {R M C ι : Type*} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup C] [Module R C] [Module.Free R C]
    (F : ι → Module.End R M) :
    (⨅ i, eqLocus ((F i).rTensor C) LinearMap.id) =
      Submodule.map₂ (TensorProduct.mk R M C) (⨅ i, eqLocus (F i) LinearMap.id) ⊤ := by
  classical
  apply le_antisymm
  · intro x hx
    simp only [Submodule.mem_iInf, LinearMap.mem_eqLocus, LinearMap.id_apply] at hx
    let 𝒞 := Module.Free.chooseBasis R C
    have hcoeff : ∀ k, TensorProduct.equivFinsuppOfBasisRight 𝒞 x k ∈
        (⨅ i, eqLocus (F i) LinearMap.id) := by
      intro k
      simp only [Submodule.mem_iInf, LinearMap.mem_eqLocus, LinearMap.id_apply]
      intro i
      have h := TensorProduct.equivFinsuppOfBasisRight_rTensor_apply 𝒞 (F i) x k
      rw [hx i] at h
      exact h.symm
    have hxrepr := (TensorProduct.equivFinsuppOfBasisRight 𝒞).symm_apply_apply x
    rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply] at hxrepr
    rw [← hxrepr, Finsupp.sum]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.apply_mem_map₂ _ (hcoeff k) (Submodule.mem_top)
  · rw [Submodule.map₂_le]
    intro m hm c _
    simp only [Submodule.mem_iInf, LinearMap.mem_eqLocus, LinearMap.id_apply] at hm ⊢
    intro i
    change (F i).rTensor C (m ⊗ₜ[R] c) = m ⊗ₜ[R] c
    rw [LinearMap.rTensor_tmul, hm i]

/-- Simultaneous fixed submodules after tensoring on the left by a free module. -/
lemma iInf_eqLocus_lTensor
    {R M C ι : Type*} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup C] [Module R C] [Module.Free R C]
    (F : ι → Module.End R M) :
    (⨅ i, eqLocus ((F i).lTensor C) LinearMap.id) =
      Submodule.map₂ (TensorProduct.mk R C M) ⊤ (⨅ i, eqLocus (F i) LinearMap.id) := by
  classical
  apply le_antisymm
  · intro x hx
    simp only [Submodule.mem_iInf, LinearMap.mem_eqLocus, LinearMap.id_apply] at hx
    let 𝒞 := Module.Free.chooseBasis R C
    have hcoeff : ∀ k, TensorProduct.equivFinsuppOfBasisLeft 𝒞 x k ∈
        (⨅ i, eqLocus (F i) LinearMap.id) := by
      intro k
      simp only [Submodule.mem_iInf, LinearMap.mem_eqLocus, LinearMap.id_apply]
      intro i
      have h := TensorProduct.equivFinsuppOfBasisLeft_lTensor_apply 𝒞 (F i) x k
      rw [hx i] at h
      exact h.symm
    have hxrepr := (TensorProduct.equivFinsuppOfBasisLeft 𝒞).symm_apply_apply x
    rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply] at hxrepr
    rw [← hxrepr, Finsupp.sum]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.apply_mem_map₂ _ (Submodule.mem_top) (hcoeff k)
  · rw [Submodule.map₂_le]
    intro c _ m hm
    simp only [Submodule.mem_iInf, LinearMap.mem_eqLocus, LinearMap.id_apply] at hm ⊢
    intro i
    change (F i).lTensor C (c ⊗ₜ[R] m) = c ⊗ₜ[R] m
    rw [LinearMap.lTensor_tmul, hm i]

end LinearMap
