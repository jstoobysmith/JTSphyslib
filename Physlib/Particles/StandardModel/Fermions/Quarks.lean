/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Relativity.Tensors.ComplexTensor.Weyl.Basic/-!
# The type of quarks

In this module we define the type corresponding to
the target vector space of a quark field in the Standard Model.

On this type we define a representation of the Lorentz group, and a
representation of the Standard Model gauge group.

-/

@[expose] public section

namespace StandardModel

open TensorProduct

/-- The vector space of a quark field in the Standard Model.
  These live in the (3, 2)_{1} representation of the gauge group. -/
@[ext]
structure Quark where
  /-- The underlying value of the quark field in the tensor product space. -/
  val : Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3) ⊗[ℂ] EuclideanSpace ℂ (Fin 2)

namespace Quark

/-!

## The structure of a module

-/

instance : Add Quark where
  add q1 q2 := ⟨q1.val + q2.val⟩

@[simp]
lemma add_val (q1 q2 : Quark) : (q1 + q2).val = q1.val + q2.val := rfl

instance : Zero Quark where
  zero := ⟨0⟩

@[simp]
lemma zero_val : (0 : Quark).val = 0 := rfl

instance : Neg Quark where
  neg q := ⟨-q.val⟩

@[simp]
lemma neg_val (q : Quark) : (-q).val = -q.val := rfl

instance : SMul ℂ Quark where
  smul c q := ⟨c • q.val⟩

@[simp]
lemma smul_val (c : ℂ) (q : Quark) : (c • q).val = c • q.val := rfl

instance : AddCommGroup Quark where
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := by intros; ext; simp [add_assoc]
  zero_add := by intros; ext; simp [zero_add]
  add_zero := by intros; ext; simp [add_zero]
  neg_add_cancel := by intros; ext; simp; grind
  add_comm := by intros; ext; simp [add_comm]

instance : Module ℂ Quark where
  smul_add := by intros; ext; simp [smul_add]
  add_smul := by intros; ext; simp [add_smul]
  mul_smul := by intros; ext; simp [mul_smul]
  one_smul := by intros; ext; simp [one_smul]
  smul_zero := by intros; ext; simp [smul_zero]
  zero_smul := by intros; ext; simp [zero_smul]

def valLinEquiv : Quark ≃ₗ[ℂ]
    Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3) ⊗[ℂ] EuclideanSpace ℂ (Fin 2) where
  toFun := val
  invFun := fun m => ⟨m⟩
  map_add' := by intros; simp
  map_smul' := by intros; simp


/-!

## Lorentz group representation

-/
open Matrix MatrixGroups

open Representation in
/-- The representation of the Lorentz group on the space of quark fields. -/
noncomputable def repLorentzGroup : Representation ℂ (SL(2,ℂ)) Quark where
  toFun Λ := {
    toFun q := ⟨((Fermion.leftHandedRep).tprod (trivial ℂ (SL(2,ℂ)) _)).tprod
        (trivial ℂ (SL(2,ℂ)) _) Λ q.val⟩
    map_add' := by intros; simp [map_add]; rfl
    map_smul' := by intros; simp [map_smul]; rfl}
  map_one' := by simp [map_one]; rfl
  map_mul' := by intros; simp [map_mul]; rfl

/-!

## The representation of the Standard Model gauge group

-/

/-- The action of the Standard Model gauge group on quark fields. -/
noncomputable def repGaugeGroup : Representation ℂ GaugeGroupI Quark where
  toFun g := valLinEquiv.symm ∘ₗ
      TensorProduct.map
        (TensorProduct.map
        (LinearMap.id (M := Fermion.LeftHandedWeyl)) -- action on the Lorentz indices
        g.toSU3.1.toEuclideanLin) -- SU(3) action
        g.toSU2.1.toEuclideanLin  -- SU(2) action
      ∘ₗ LinearMap.lsmul ℂ _ (g.toU1 : ℂ) -- U(1) action
      ∘ₗ valLinEquiv
  map_one' := by
    ext q
    simp
  map_mul' g1 g2 := by
    ext q
    simp [smul_smul, mul_comm, TensorProduct.map_map, ← TensorProduct.map_comp]

end Quark
end StandardModel
