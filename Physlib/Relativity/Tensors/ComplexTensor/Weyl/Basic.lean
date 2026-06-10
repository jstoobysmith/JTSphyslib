/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Weyl.Modules
public import Physlib.Relativity.SL2C.Basic
public import Physlib.Meta.Informal.Basic
/-!

# Weyl fermions

A good reference for the material in this file is:
https://particle.physics.ucdavis.edu/modernsusy/slides/slideimages/spinorfeynrules.pdf

-/

@[expose] public section

namespace Fermion
noncomputable section

open Module Matrix
open MatrixGroups
open Complex
open TensorProduct

/-- The vector space ℂ^2 carrying the fundamental representation of SL(2,C).
  In index notation corresponds to a Weyl fermion with indices ψ^a. -/
def leftHandedRep : Representation ℂ SL(2,ℂ) LeftHandedWeyl where
  toFun := fun M => {
    toFun := fun (ψ : LeftHandedWeyl) =>
      LeftHandedWeyl.toFin2ℂEquiv.symm (M.1 *ᵥ ψ.toFin2ℂ),
    map_add' := by
      intro ψ ψ'
      simp [mulVec_add]
    map_smul' := by
      intro r ψ
      simp [mulVec_smul]}
  map_one' := by
    ext i
    simp
  map_mul' := fun M N => by
    simp only [SpecialLinearGroup.coe_mul]
    ext1 x
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply, LinearEquiv.apply_symm_apply,
      mulVec_mulVec]

/-- The standard basis on left-handed Weyl fermions. -/
def leftBasis : Basis (Fin 2) ℂ LeftHandedWeyl := Basis.ofEquivFun
  (Equiv.linearEquiv ℂ LeftHandedWeyl.toFin2ℂFun)

@[simp]
lemma leftBasis_ρ_apply (M : SL(2,ℂ)) (i j : Fin 2) :
    (LinearMap.toMatrix leftBasis leftBasis) (leftHandedRep M) i j = M.1 i j := by
  rw [LinearMap.toMatrix_apply]
  simp only [leftBasis, Basis.coe_ofEquivFun, Basis.ofEquivFun_repr_apply]
  change (M.1 *ᵥ (Pi.single j 1)) i = _
  simp

@[simp]
lemma leftBasis_toFin2ℂ (i : Fin 2) : (leftBasis i).toFin2ℂ = Pi.single i 1 := by
  simp only [leftBasis, Basis.coe_ofEquivFun]
  rfl

/-- The vector space ℂ^2 carrying the representation of SL(2,C) given by
    M → (M⁻¹)ᵀ. In index notation corresponds to a Weyl fermion with indices ψ_a. -/
def altLeftHandedRep : Representation ℂ SL(2,ℂ) DualLeftHandedWeyl where
  toFun := fun M => {
    toFun := fun (ψ : DualLeftHandedWeyl) =>
      DualLeftHandedWeyl.toFin2ℂEquiv.symm ((M.1⁻¹)ᵀ *ᵥ ψ.toFin2ℂ),
    map_add' := by
      intro ψ ψ'
      simp [mulVec_add]
    map_smul' := by
      intro r ψ
      simp [mulVec_smul]}
  map_one' := by
    ext i
    simp
  map_mul' := fun M N => by
    ext1 x
    simp only [SpecialLinearGroup.coe_mul, LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply,
      LinearEquiv.apply_symm_apply, mulVec_mulVec, EmbeddingLike.apply_eq_iff_eq]
    refine (congrFun (congrArg _ ?_) _)
    rw [Matrix.mul_inv_rev]
    exact transpose_mul _ _

/-- The standard basis on alt-left-handed Weyl fermions. -/
def altLeftBasis : Basis (Fin 2) ℂ DualLeftHandedWeyl := Basis.ofEquivFun
  (Equiv.linearEquiv ℂ DualLeftHandedWeyl.toFin2ℂFun)

@[simp]
lemma altLeftBasis_toFin2ℂ (i : Fin 2) : (altLeftBasis i).toFin2ℂ = Pi.single i 1 := by
  simp only [altLeftBasis, Basis.coe_ofEquivFun]
  rfl

@[simp]
lemma altLeftBasis_ρ_apply (M : SL(2,ℂ)) (i j : Fin 2) :
    (LinearMap.toMatrix altLeftBasis altLeftBasis) (altLeftHandedRep M) i j = (M.1⁻¹)ᵀ i j := by
  rw [LinearMap.toMatrix_apply]
  simp only [altLeftBasis, Basis.coe_ofEquivFun, Basis.ofEquivFun_repr_apply, transpose_apply]
  change ((M.1⁻¹)ᵀ *ᵥ (Pi.single j 1)) i = _
  simp

/-- The vector space ℂ^2 carrying the conjugate representation of SL(2,C).
  In index notation corresponds to a Weyl fermion with indices ψ^{dot a}. -/
def rightHandedRep : Representation ℂ SL(2,ℂ) RightHandedWeyl where
  toFun := fun M => {
    toFun := fun (ψ : RightHandedWeyl) =>
      RightHandedWeyl.toFin2ℂEquiv.symm (M.1.map star *ᵥ ψ.toFin2ℂ),
    map_add' := by
      intro ψ ψ'
      simp [mulVec_add]
    map_smul' := by
      intro r ψ
      simp [mulVec_smul]}
  map_one' := by
    ext i
    simp
  map_mul' := fun M N => by
    ext1 x
    simp only [SpecialLinearGroup.coe_mul, RCLike.star_def, Matrix.map_mul, LinearMap.coe_mk,
      AddHom.coe_mk, Module.End.mul_apply, LinearEquiv.apply_symm_apply, mulVec_mulVec]

/-- The standard basis on right-handed Weyl fermions. -/
def rightBasis : Basis (Fin 2) ℂ RightHandedWeyl := Basis.ofEquivFun
  (Equiv.linearEquiv ℂ RightHandedWeyl.toFin2ℂFun)

@[simp]
lemma rightBasis_toFin2ℂ (i : Fin 2) : (rightBasis i).toFin2ℂ = Pi.single i 1 := by
  simp only [rightBasis, Basis.coe_ofEquivFun]
  rfl

@[simp]
lemma rightBasis_ρ_apply (M : SL(2,ℂ)) (i j : Fin 2) :
    (LinearMap.toMatrix rightBasis rightBasis) (rightHandedRep M) i j = (M.1.map star) i j := by
  rw [LinearMap.toMatrix_apply]
  simp only [rightBasis, Basis.coe_ofEquivFun, Basis.ofEquivFun_repr_apply]
  change (M.1.map star *ᵥ (Pi.single j 1)) i = _
  simp [mulVec_single]

/-- The vector space ℂ^2 carrying the representation of SL(2,C) given by
    M → (M⁻¹)^†.
    In index notation this corresponds to a Weyl fermion with index `ψ_{dot a}`. -/
def altRightHandedRep : Representation ℂ SL(2,ℂ) DualRightHandedWeyl where
  toFun := fun M => {
    toFun := fun (ψ : DualRightHandedWeyl) =>
      DualRightHandedWeyl.toFin2ℂEquiv.symm ((M.1⁻¹).conjTranspose *ᵥ ψ.toFin2ℂ),
    map_add' := by
      intro ψ ψ'
      simp [mulVec_add]
    map_smul' := by
      intro r ψ
      simp [mulVec_smul]}
  map_one' := by
    ext i
    simp
  map_mul' := fun M N => by
    ext1 x
    simp only [SpecialLinearGroup.coe_mul, LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply,
      LinearEquiv.apply_symm_apply, mulVec_mulVec, EmbeddingLike.apply_eq_iff_eq]
    refine (congrFun (congrArg _ ?_) _)
    rw [Matrix.mul_inv_rev]
    exact conjTranspose_mul _ _

/-- The standard basis on alt-right-handed Weyl fermions. -/
def altRightBasis : Basis (Fin 2) ℂ DualRightHandedWeyl := Basis.ofEquivFun
  (Equiv.linearEquiv ℂ DualRightHandedWeyl.toFin2ℂFun)

@[simp]
lemma altRightBasis_toFin2ℂ (i : Fin 2) : (altRightBasis i).toFin2ℂ = Pi.single i 1 := by
  simp only [altRightBasis, Basis.coe_ofEquivFun]
  rfl

@[simp]
lemma altRightBasis_ρ_apply (M : SL(2,ℂ)) (i j : Fin 2) :
    (LinearMap.toMatrix altRightBasis altRightBasis) (altRightHandedRep M) i j =
    ((M.1⁻¹).conjTranspose) i j := by
  rw [LinearMap.toMatrix_apply]
  simp only [altRightBasis, Basis.coe_ofEquivFun, Basis.ofEquivFun_repr_apply]
  change ((M.1⁻¹).conjTranspose *ᵥ (Pi.single j 1)) i = _
  simp [mulVec_single]

/-!

## Equivalences between Weyl fermion vector spaces.

-/

/-- The morphism between the representation `leftHanded` and the representation
  `altLeftHanded` defined by multiplying an element of
  `leftHanded` by the matrix `εᵃ⁰ᵃ¹ = !![0, 1; -1, 0]]`. -/
def leftHandedToAlt : leftHandedRep.IntertwiningMap altLeftHandedRep where
  toFun := fun ψ => DualLeftHandedWeyl.toFin2ℂEquiv.symm (!![0, 1; -1, 0] *ᵥ ψ.toFin2ℂ)
  map_add' := by
    intro ψ ψ'
    simp only [mulVec_add, LinearEquiv.map_add]
  map_smul' := by
    intro a ψ
    simp only [mulVec_smul, LinearEquiv.map_smul]
    rfl
  isIntertwining' := by
    intro M
    refine LinearMap.ext (fun ψ => ?_)
    change DualLeftHandedWeyl.toFin2ℂEquiv.symm (!![0, 1; -1, 0] *ᵥ M.1 *ᵥ ψ.val) =
      DualLeftHandedWeyl.toFin2ℂEquiv.symm ((M.1⁻¹)ᵀ *ᵥ !![0, 1; -1, 0] *ᵥ ψ.val)
    apply congrArg
    rw [mulVec_mulVec, mulVec_mulVec, Lorentz.SL2C.inverse_coe, eta_fin_two M.1]
    refine congrFun (congrArg _ ?_) _
    rw [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_fin_two, eta_fin_two !![M.1 1 1, -M.1 0 1; -M.1 1 0, M.1 0 0]ᵀ]
    simp

lemma leftHandedToAlt_hom_apply (ψ : LeftHandedWeyl) :
    leftHandedToAlt ψ =
    DualLeftHandedWeyl.toFin2ℂEquiv.symm (!![0, 1; -1, 0] *ᵥ ψ.toFin2ℂ) := rfl

/-- The morphism from `altLeftHanded` to
  `leftHanded` defined by multiplying an element of
  DualLeftHandedWeyl by the matrix `εₐ₁ₐ₂ = !![0, -1; 1, 0]`. -/
def leftHandedAltTo : altLeftHandedRep.IntertwiningMap leftHandedRep where
  toFun := fun ψ =>
      LeftHandedWeyl.toFin2ℂEquiv.symm (!![0, -1; 1, 0] *ᵥ ψ.toFin2ℂ)
  map_add' := by
    intro ψ ψ'
    simp only [map_add]
    rw [mulVec_add, LinearEquiv.map_add]
  map_smul' := by
    intro a ψ
    simp only [LinearEquiv.map_smul]
    rw [mulVec_smul, LinearEquiv.map_smul]
    rfl
  isIntertwining' := by
    intro M
    refine LinearMap.ext (fun ψ => ?_)
    change LeftHandedWeyl.toFin2ℂEquiv.symm (!![0, -1; 1, 0] *ᵥ (M.1⁻¹)ᵀ *ᵥ ψ.val) =
      LeftHandedWeyl.toFin2ℂEquiv.symm (M.1 *ᵥ !![0, -1; 1, 0] *ᵥ ψ.val)
    rw [EquivLike.apply_eq_iff_eq, mulVec_mulVec, mulVec_mulVec, Lorentz.SL2C.inverse_coe,
      eta_fin_two M.1]
    refine congrFun (congrArg _ ?_) _
    rw [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_fin_two, eta_fin_two !![M.1 1 1, -M.1 0 1; -M.1 1 0, M.1 0 0]ᵀ]
    simp

lemma leftHandedAltTo_hom_apply (ψ : DualLeftHandedWeyl) :
    leftHandedAltTo ψ =
    LeftHandedWeyl.toFin2ℂEquiv.symm (!![0, -1; 1, 0] *ᵥ ψ.toFin2ℂ) := rfl

/-- The equivalence between the representation `leftHanded` and the representation
  `altLeftHanded` defined by multiplying an element of
  `leftHanded` by the matrix `εᵃ⁰ᵃ¹ = !![0, 1; -1, 0]]`. -/
def leftHandedAltEquiv : leftHandedRep.Equiv altLeftHandedRep := by
  refine Representation.Equiv.mk' leftHandedToAlt leftHandedAltTo ?_ ?_
  · intro x
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
      Representation.IntertwiningMap.coe_toLinearMap]
    rw [leftHandedAltTo_hom_apply, leftHandedToAlt_hom_apply]
    rw [DualLeftHandedWeyl.toFin2ℂ, LinearEquiv.apply_symm_apply, mulVec_mulVec]
    rw [show (!![0, -1; (1 : ℂ), 0] * !![0, 1; -1, 0]) = 1 by simpa using Eq.symm one_fin_two]
    rw [one_mulVec]
    rfl
  · intro ψ
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
      Representation.IntertwiningMap.coe_toLinearMap]
    rw [leftHandedAltTo_hom_apply, leftHandedToAlt_hom_apply, LeftHandedWeyl.toFin2ℂ,
      LinearEquiv.apply_symm_apply, mulVec_mulVec]
    rw [show (!![0, (1 : ℂ); -1, 0] * !![0, -1; 1, 0]) = 1 by simpa using Eq.symm one_fin_two]
    rw [one_mulVec]
    rfl

/-- `leftHandedAltEquiv` acting on an element `ψ : leftHanded` corresponds
  to multiplying `ψ` by the matrix `!![0, 1; -1, 0]`. -/
lemma leftHandedAltEquiv_hom_hom_apply (ψ : LeftHandedWeyl) :
    leftHandedAltEquiv ψ =
    DualLeftHandedWeyl.toFin2ℂEquiv.symm (!![0, 1; -1, 0] *ᵥ ψ.toFin2ℂ) := rfl

/-- The inverse of `leftHandedAltEquiv` acting on an element`ψ : altLeftHanded` corresponds
  to multiplying `ψ` by the matrix `!![0, -1; 1, 0]`. -/
lemma leftHandedAltEquiv_inv_hom_apply (ψ : DualLeftHandedWeyl) :
    leftHandedAltEquiv.symm ψ =
    LeftHandedWeyl.toFin2ℂEquiv.symm (!![0, -1; 1, 0] *ᵥ ψ.toFin2ℂ) := rfl

/-- The linear equivalence between `rightHandedWeyl` and `DualRightHandedWeyl` given by multiplying
an element of `rightHandedWeyl` by the matrix `εᵃ⁰ᵃ¹ = !![0, 1; -1, 0]]`.
-/
informal_definition rightHandedWeylAltEquiv where
  deps := [``rightHandedRep, ``altRightHandedRep]
  tag := "6VZR4"

/-- The linear equivalence `rightHandedWeylAltEquiv` is equivariant with respect to the action of
`SL(2,C)` on `rightHandedWeyl` and `DualRightHandedWeyl`.
-/
informal_lemma rightHandedWeylAltEquiv_equivariant where
  deps := [``rightHandedWeylAltEquiv]
  tag := "6VZSG"

end

end Fermion
