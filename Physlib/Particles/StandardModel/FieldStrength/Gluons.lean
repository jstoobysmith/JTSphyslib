/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Relativity.Tensors.ComplexTensor.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Representation
public import Physlib.Relativity.SL2C.Basic
/-!
# Field strength of gluons

## i. Overview

-/

@[expose] public section

namespace StandardModel

open TensorProduct

/-!

## A. The gluon field strength
-/

/-- The target vector space of the gluon field strength `G_{μν}`. It carries two
  Lorentz indices, and is valued in the real vector space of `3 × 3` hermitian
  matrices, corresponding to the adjoint of `SU(3)`. -/
@[ext]
structure GluonFieldStrength where
  /-- The two Lorentz indices together with the adjoint (hermitian-matrix) colour
    factor. -/
  val : Lorentz.Vector ⊗[ℝ] Lorentz.Vector ⊗[ℝ] selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ)

namespace GluonFieldStrength

/-!

## B. Linear structure
-/

def valEquiv : GluonFieldStrength ≃ Lorentz.Vector ⊗[ℝ] Lorentz.Vector ⊗[ℝ] selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ) where
  toFun := val
  invFun := fun m => ⟨m⟩

noncomputable instance : AddCommGroup GluonFieldStrength := Equiv.addCommGroup valEquiv

noncomputable instance : Module ℝ GluonFieldStrength := Equiv.module ℝ valEquiv

/-- The linear identification with the underlying tensor product. -/
def valLinEquiv : GluonFieldStrength ≃ₗ[ℝ]
    Lorentz.Vector ⊗[ℝ] Lorentz.Vector ⊗[ℝ] selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ) where
  toFun := val
  invFun := fun m => ⟨m⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp]
lemma valLinEquiv_apply (d : GluonFieldStrength) : valLinEquiv d = d.val := rfl

lemma valLinEquiv_symm_apply
    (m : Lorentz.Vector ⊗[ℝ] Lorentz.Vector ⊗[ℝ] selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ)) :
    valLinEquiv.symm m = ⟨m⟩ := rfl

@[simp]
lemma val_add (d₁ d₂ : GluonFieldStrength) : (d₁ + d₂).val = d₁.val + d₂.val := rfl

@[simp]
lemma val_smul (r : ℝ) (d : GluonFieldStrength) : (r • d).val = r • d.val := rfl


/-!

## C. Lorentz action

The Lorentz group acts on the right-handed Weyl factor and leaves the colour index fixed.
-/

open Matrix MatrixGroups

/-- The action of an element of `SL(2,ℂ)` on the gluon field strength: the vector
  action, through the covering map `SL(2,ℂ) →* LorentzGroup 3`, on the two Lorentz
  indices, and the trivial action on the colour (adjoint) factor. -/
noncomputable def repLorentzGroupAux (Λ : SL(2,ℂ)) :
    GluonFieldStrength →ₗ[ℝ] GluonFieldStrength :=
  valLinEquiv.symm.toLinearMap ∘ₗ
    TensorProduct.map
      (TensorProduct.map (Lorentz.Vector.rep (Lorentz.SL2C.toLorentzGroup Λ))
        (Lorentz.Vector.rep (Lorentz.SL2C.toLorentzGroup Λ)))
      (Representation.trivial ℝ (SL(2,ℂ)) (selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ)) Λ) ∘ₗ
    valLinEquiv.toLinearMap

/-- The Lorentz representation on the gluon field strength: the action on the two
  Lorentz indices, trivial on the colour (adjoint) factor. -/
noncomputable def repLorentzGroup : Representation ℝ (SL(2,ℂ)) GluonFieldStrength where
  toFun := repLorentzGroupAux
  map_one' := by
    ext F
    simp [repLorentzGroupAux, Module.End.one_eq_id]
  map_mul' Λ₁ Λ₂ := by
    ext1 F
    simp [repLorentzGroupAux, TensorProduct.map_map, TensorProduct.map_comp,
      Module.End.mul_eq_comp, map_mul]

/-!

## D. Gauge action

The gluon field strength transforms in the adjoint representation of the gauge group:
the `SU(3)` component acts on the colour factor by conjugation `A ↦ u * A * uᴴ`, while
the `SU(2)` and `U(1)` components act trivially, as do the two Lorentz indices.
-/

/-- The adjoint action of an element of `SU(3)` on the real vector space of `3 × 3`
  hermitian matrices, `A ↦ u * A * uᴴ`. -/
@[simps!]
noncomputable def adjointAction (u : specialUnitaryGroup (Fin 3) ℂ) :
    selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ) →ₗ[ℝ] selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ) where
  toFun A := ⟨u.1 * A.1 * (u.1)ᴴ,
    by
      noncomm_ring [selfAdjoint.mem_iff, star_eq_conjTranspose,
        conjTranspose_mul, conjTranspose_conjTranspose,
        (star_eq_conjTranspose A.1).symm.trans <| selfAdjoint.mem_iff.mp A.2]⟩
  map_add' A B := by
    simp only [AddSubgroup.coe_add, AddMemClass.mk_add_mk, Subtype.mk.injEq]
    noncomm_ring
  map_smul' r A := by
    noncomm_ring [selfAdjoint.val_smul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
      RingHom.id_apply]

@[simp]
lemma adjointAction_one : adjointAction 1 = LinearMap.id := by
  refine LinearMap.ext fun A => Subtype.ext ?_
  simp [adjointAction]

lemma adjointAction_mul (u₁ u₂ : specialUnitaryGroup (Fin 3) ℂ) :
    adjointAction (u₁ * u₂) = adjointAction u₁ ∘ₗ adjointAction u₂ := by
  refine LinearMap.ext fun A => Subtype.ext ?_
  simp [adjointAction, conjTranspose_mul, mul_assoc]

/-- The action of an element of the gauge group on the gluon field strength: the
  adjoint action of the `SU(3)` component on the colour factor, trivial on the two
  Lorentz indices. -/
noncomputable def repGaugeGroupIAux (g : GaugeGroupI) :
    GluonFieldStrength →ₗ[ℝ] GluonFieldStrength :=
  valLinEquiv.symm.toLinearMap ∘ₗ
    TensorProduct.map LinearMap.id (adjointAction g.toSU3) ∘ₗ
    valLinEquiv.toLinearMap

/-- The adjoint action of the unquotiented Standard Model gauge group on the gluon
  field strength. -/
noncomputable def repGaugeGroupI : Representation ℝ GaugeGroupI GluonFieldStrength where
  toFun := repGaugeGroupIAux
  map_one' := by
    ext F
    simp [repGaugeGroupIAux]
  map_mul' g₁ g₂ := by
    ext1 F
    simp [repGaugeGroupIAux, map_mul, adjointAction_mul, TensorProduct.map_map,
      Module.End.mul_eq_comp]

end GluonFieldStrength

end StandardModel
