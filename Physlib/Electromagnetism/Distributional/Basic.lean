/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.SpaceAndTime.SpaceTime.Derivatives
public import Physlib.SpaceAndTime.Space.Derivatives.Curl
public import Physlib.Mathematics.VariationalCalculus.HasVarAdjDeriv
public import Physlib.Relativity.Tensors.Elab
public import Physlib.SpaceAndTime.SpaceTime.TimeSlice

/-!

# The Electromagnetic Potential

## i. Overview

The electromagnetic potential `A^μ` is the fundamental objects in
electromagnetism. Mathematically it is related to a connection
on a `U(1)`-bundle.

We define the electromagnetic potential as a distribution from
spacetime to contravariant Lorentz vectors.

## ii. Key results

- `DistElectromagneticPotential` : the type of electromagnetic potentials as distributions.

## iii. Table of contents

- A. The electromagnetic potential as a distribution
  - A.1. The derivative of the electromagnetic potential as a distribution
  - A.2. The derivative in terms of the basis
  - A.3. Equivariance of the derivative distribution

## iv. References

- https://quantummechanics.ucsd.edu/ph130a/130_notes/node452.html
- https://ph.qmul.ac.uk/sites/default/files/EMT10new.pdf

-/

@[expose] public section

namespace Electromagnetism
open Module realLorentzTensor
open IndexNotation
open TensorSpecies
open Tensor

/-!

## A. The electromagnetic potential as a distribution

-/

/-- The electromagnetic potential as a distribution and as a tensor `A^μ`. -/
noncomputable abbrev DistElectromagneticPotential (d : ℕ := 3) :=
  (SpaceTime d) →d[ℝ] Lorentz.Vector d

namespace DistElectromagneticPotential
open TensorSpecies
open Tensor
open SpaceTime
open TensorProduct
open minkowskiMatrix SchwartzMap
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one

/-!

### A.1. The derivative of the electromagnetic potential as a distribution

-/

set_option backward.isDefEq.respectTransparency false in
/-- The derivative of a electromagnetic potential, which is a distribution. -/
noncomputable def deriv {d} : DistElectromagneticPotential d →ₗ[ℝ]
    (SpaceTime d) →d[ℝ] Lorentz.CoVector d ⊗[ℝ] Lorentz.Vector d := distTensorDeriv

set_option backward.isDefEq.respectTransparency false in
lemma deriv_eq_sum_sum {d} (A : DistElectromagneticPotential d)
    (ε : 𝓢(SpaceTime d, ℝ)) :
    deriv A ε =∑ μ, ∑ ν, (SpaceTime.distDeriv μ A ε ν) •
      Lorentz.CoVector.basis μ ⊗ₜ[ℝ] Lorentz.Vector.basis ν := by
  simp [deriv, distTensorDeriv_apply]
  congr
  funext μ
  conv_lhs => rw [← Lorentz.Vector.basis.sum_repr (SpaceTime.distDeriv μ A ε)]
  rw [tmul_sum]
  congr
  funext ν
  simp
  rfl
/-!

### A.2. The derivative in terms of the basis

-/

@[simp]
lemma deriv_basis_repr_apply {d} {μν : (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)}
    (A : DistElectromagneticPotential d)
    (ε : 𝓢(SpaceTime d, ℝ)) :
    (Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr (deriv A ε) μν =
    distDeriv μν.1 A ε μν.2 := by
  match μν with
  | (μ, ν) =>
  rw [deriv_eq_sum_sum]
  simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul, Finset.sum_apply,
    Pi.smul_apply, Basis.tensorProduct_repr_tmul_apply, Basis.repr_self, smul_eq_mul]
  rw [Finset.sum_eq_single μ, Finset.sum_eq_single ν]
  · simp
  · intro μ' _ h
    simp [h]
  · simp
  · intro ν' _ h
    simp [h]
  · simp

lemma toTensor_deriv_basis_repr_apply {d} (A : DistElectromagneticPotential d)
    (ε : 𝓢(SpaceTime d, ℝ)) (b : ComponentIdx (S := realLorentzTensor d)
      (Fin.append ![Color.down] ![Color.up])) :
    (Tensor.basis _).repr (Tensorial.toTensor (deriv A ε)) b =
    distDeriv (b 0) A ε (b 1) := by
  rw [Tensorial.basis_toTensor_apply]
  rw [Tensorial.basis_map_prod]
  simp only [Nat.reduceSucc, Nat.reduceAdd, Basis.repr_reindex, Finsupp.mapDomain_equiv_apply,
    Equiv.symm_symm, Fin.isValue]
  rw [Lorentz.Vector.tensor_basis_map_eq_basis_reindex,
    Lorentz.CoVector.tensor_basis_map_eq_basis_reindex]
  have hb : (((Lorentz.CoVector.basis (d := d)).reindex
      Lorentz.CoVector.indexEquiv.symm).tensorProduct
      (Lorentz.Vector.basis.reindex Lorentz.Vector.indexEquiv.symm)) =
      ((Lorentz.CoVector.basis (d := d)).tensorProduct (Lorentz.Vector.basis (d := d))).reindex
      (Lorentz.CoVector.indexEquiv.symm.prodCongr Lorentz.Vector.indexEquiv.symm) := by
    ext b
    match b with
    | ⟨i, j⟩ =>
    simp
  rw [hb]
  rw [Module.Basis.repr_reindex_apply, deriv_basis_repr_apply]
  rfl

/-!

### A.3. Equivariance of the derivative distribution

-/

set_option backward.isDefEq.respectTransparency false in
lemma deriv_equivariant {d} {A : DistElectromagneticPotential d}
    (Λ : LorentzGroup d) : deriv (Λ • A) = Λ • deriv A := by
  rw [deriv, distTensorDeriv_equivariant]

end DistElectromagneticPotential

end Electromagnetism
