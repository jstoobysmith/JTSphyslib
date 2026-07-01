/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Vector.Representation
public import Physlib.Relativity.Tensors.RealTensor.CoVector.Representation
public import Mathlib.RepresentationTheory.Intertwining
/-!

# Contraction of Real Lorentz Vectors and Covectors

We define the intertwining maps which define the contraction of a contravariant Lorentz vector with
a covariant Lorentz vector, and vice versa.

Note: This file will eventually replace `./Pre/Contraction.lean` when we move
  `realLorentzTensor` over to `Vector` and `CoVector`.

-/

@[expose] public section

noncomputable section

open Matrix MatrixGroups Complex TensorProduct minkowskiMatrix

namespace Lorentz
attribute [-simp] Fintype.sum_sum_type
variable {d : ℕ}

/-!

## A. The definitions

-/

TODO "In a similar way to `Vector.contract` and `CoVector.contract`,
  we want to define metrics and units as intertwining maps of representations.
  This should copy (and eventually replace) the definitions e.g. `./Units/Pre.lean`."

/-- The intertwining map defining the contraction of a contravariant Lorentz vector with a
  covariant Lorentz vector. -/
def Vector.contract : (Vector.rep.tprod CoVector.rep).IntertwiningMap
    (Representation.trivial ℝ (LorentzGroup d) ℝ) where
  toLinearMap := by
    refine TensorProduct.lift (LinearMap.mk₂ ℝ (fun φ ψ => ∑ i, φ i * ψ i) ?_ ?_ ?_ ?_)
    · intro m1 m2 n
      simp [add_mul, Finset.sum_add_distrib]
    · intro r m n
      simp only [apply_smul, smul_eq_mul, Finset.mul_sum]
      grind
    · intro m n1 n2
      simp [mul_add, Finset.sum_add_distrib]
    · intro r m n
      simp only [CoVector.apply_smul, smul_eq_mul, Finset.mul_sum]
      grind
  isIntertwining' Λ := by
    ext φ ψ
    simp only [Representation.tprod_apply, AlgebraTensorModule.curry_apply,
      LinearMap.restrictScalars_self, curry_apply, LinearMap.coe_comp, Function.comp_apply,
      map_tmul, lift.tmul, LinearMap.mk₂_apply, Representation.isTrivial_def, LinearMap.id_comp]
    trans (Λ.1 *ᵥ φ) ⬝ᵥ ((LorentzGroup.transpose Λ⁻¹).1 *ᵥ ψ); swap
    · rw [dotProduct_mulVec, LorentzGroup.transpose_val,
        vecMul_transpose, mulVec_mulVec, LorentzGroup.coe_inv, inv_mul_of_invertible Λ.1]
      simp only [one_mulVec]
      rfl
    · simp [dotProduct, Vector.rep_apply_eq_mulVec, CoVector.rep_apply_eq_mulVec]

/-- The intertwining map defining the contraction of a covariant Lorentz vector with a
  contravariant Lorentz vector. -/
def CoVector.contract : (CoVector.rep.tprod Vector.rep).IntertwiningMap
    (Representation.trivial ℝ (LorentzGroup d) ℝ) where
  toLinearMap := by
    refine TensorProduct.lift (LinearMap.mk₂ ℝ (fun φ ψ => ∑ i, φ i * ψ i) ?_ ?_ ?_ ?_)
    · intro m1 m2 n
      simp [add_mul, Finset.sum_add_distrib]
    · intro r m n
      simp only [apply_smul, smul_eq_mul, Finset.mul_sum]
      grind
    · intro m n1 n2
      simp [mul_add, Finset.sum_add_distrib]
    · intro r m n
      simp only [Vector.apply_smul, smul_eq_mul, Finset.mul_sum]
      grind
  isIntertwining' Λ := by
    ext φ ψ
    simp only [Representation.tprod_apply, AlgebraTensorModule.curry_apply,
      LinearMap.restrictScalars_self, curry_apply, LinearMap.coe_comp, Function.comp_apply,
      map_tmul, lift.tmul, LinearMap.mk₂_apply, Representation.isTrivial_def, LinearMap.id_comp]
    trans ((LorentzGroup.transpose Λ⁻¹).1 *ᵥ φ) ⬝ᵥ (Λ.1 *ᵥ ψ); swap
    · rw [dotProduct_mulVec, LorentzGroup.transpose_val,
        mulVec_transpose, vecMul_vecMul, LorentzGroup.coe_inv, inv_mul_of_invertible Λ.1]
      simp only [vecMul_one]
      rfl
    · simp [dotProduct, Vector.rep_apply_eq_mulVec, CoVector.rep_apply_eq_mulVec]

/-!

## B. Properties of the contractions

-/

lemma Vector.contract_tmul (φ : Vector d) (ψ : CoVector d) :
    Vector.contract (φ ⊗ₜ ψ) = ∑ i, φ i * ψ i := rfl

lemma CoVector.contract_tmul (φ : CoVector d) (ψ : Vector d) :
    CoVector.contract (φ ⊗ₜ ψ) = ∑ i, φ i * ψ i := rfl

lemma Vector.contract_basis_left (μ : Fin 1 ⊕ Fin d) (ψ : CoVector d) :
    Vector.contract (basis μ ⊗ₜ ψ) = ψ μ := by simp [Vector.contract_tmul, basis_apply]

lemma CoVector.contract_basis_left (μ : Fin 1 ⊕ Fin d) (φ : Vector d) :
    CoVector.contract (basis μ ⊗ₜ φ) = φ μ := by simp [CoVector.contract_tmul, basis_apply]

lemma Vector.contract_basis_right (φ : Vector d) (μ : Fin 1 ⊕ Fin d) :
    Vector.contract (φ ⊗ₜ basis μ) = φ μ := by simp [Vector.contract_tmul, basis_apply]

lemma CoVector.contract_basis_right (ψ : CoVector d) (μ : Fin 1 ⊕ Fin d) :
    CoVector.contract (ψ ⊗ₜ basis μ) = ψ μ := by simp [CoVector.contract_tmul, basis_apply]

lemma Vector.contract_eq_coVector_contract (φ : Vector d) (ψ : CoVector d) :
    Vector.contract (φ ⊗ₜ ψ) = CoVector.contract (ψ ⊗ₜ φ) := by
  simp only [Vector.contract_tmul, CoVector.contract_tmul]
  grind

lemma Vector.contract_rep (Λ : LorentzGroup d) (φ : Vector d) (ψ : CoVector d) :
    Vector.contract ((Vector.rep Λ φ) ⊗ₜ (CoVector.rep Λ ψ)) = Vector.contract (φ ⊗ₜ ψ) := by
  change Vector.contract ((Vector.rep.tprod CoVector.rep) Λ (φ ⊗ₜ ψ)) = _
  rw [Vector.contract.isIntertwining]
  simp

lemma CoVector.contract_rep (Λ : LorentzGroup d) (φ : CoVector d) (ψ : Vector d) :
    CoVector.contract ((CoVector.rep Λ φ) ⊗ₜ (Vector.rep Λ ψ)) = CoVector.contract (φ ⊗ₜ ψ) := by
  change CoVector.contract ((CoVector.rep.tprod Vector.rep) Λ (φ ⊗ₜ ψ)) = _
  rw [CoVector.contract.isIntertwining]
  simp

end Lorentz
end
