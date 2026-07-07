/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Relativity.Tensors.ComplexTensor.Weyl.Basic
/-!
# The type corresponding to quark doublets

In this module we define the type corresponding to
the target vector space of a quark field in the Standard Model.

On this type we define a representation of the Lorentz group, and a
representation of the Standard Model gauge group.

-/

@[expose] public section

namespace StandardModel

open TensorProduct

TODO "Add other fermions similar to this file with the names:
 - UpSinglet (3, 1)_{4} (right-handed)
 - DownSinglet (3, 1)_{-2} (right-handed)
 - LeptonDoublet (1, 2)_{-3} (left-handed)
 - LeptonSinglet (1, 1)_{-6} (right-handed)"

/-- The vector space of a quark field in the Standard Model.
  These live in the (3, 2)_{1} representation of the gauge group. -/
@[ext]
structure QuarkDoublet where
  /-- The underlying value of the quark field in the tensor product space. -/
  val : Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3) ⊗[ℂ] EuclideanSpace ℂ (Fin 2)

namespace QuarkDoublet

/-!

## Equivalence with the underlying tensor product space

-/

/-- The linear equivalence between `QuarkDoublet` and its underlying tensor product space. -/
def valEquiv : QuarkDoublet ≃
    Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3) ⊗[ℂ] EuclideanSpace ℂ (Fin 2) where
  toFun := val
  invFun := fun m => ⟨m⟩

/-!

## The structure of a module

The AddCommGroup and module instances are inherited from the underlying tensor product space.
-/

instance : AddCommGroup QuarkDoublet := Equiv.addCommGroup valEquiv

instance : Module ℂ QuarkDoublet := Equiv.module ℂ valEquiv

/-- The linear equivalence between `QuarkDoublet` and its underlying tensor product space. -/
def valLinEquiv : QuarkDoublet ≃ₗ[ℂ]
    Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3) ⊗[ℂ] EuclideanSpace ℂ (Fin 2) where
  toFun := val
  invFun := fun m => ⟨m⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp]
lemma valLinEquiv_apply (q : QuarkDoublet) : valLinEquiv q = q.val := rfl

lemma valLinEquiv_symm_apply
    (m : Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3) ⊗[ℂ] EuclideanSpace ℂ (Fin 2)) :
    valLinEquiv.symm m = ⟨m⟩ := rfl

/-!

## Lorentz group representation

-/
open Matrix MatrixGroups

open Representation in
/-- The representation of the Lorentz group on the space of quark fields. -/
noncomputable def repLorentzGroup : Representation ℂ (SL(2,ℂ)) QuarkDoublet where
  toFun Λ :=  valLinEquiv.symm ∘ₗ
      TensorProduct.map
      (TensorProduct.map (Fermion.leftHandedRep Λ)
        (trivial ℂ (SL(2,ℂ)) (EuclideanSpace ℂ (Fin 3)) Λ))
        (trivial ℂ (SL(2,ℂ)) (EuclideanSpace ℂ (Fin 2)) Λ)
      ∘ₗ valLinEquiv
  map_one' := by
    ext q
    simp [Module.End.one_eq_id]
  map_mul' Λ1 Λ2 := by
    ext1 q
    simp [TensorProduct.map_map, ← TensorProduct.map_comp, Module.End.mul_eq_comp]

/-!

## The representation of the Standard Model gauge group

-/

/-- The action of the full Standard Model gauge group on quark fields. -/
noncomputable def repGaugeGroupI : Representation ℂ GaugeGroupI QuarkDoublet where
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
    simp [valLinEquiv_symm_apply]
  map_mul' g1 g2 := by
    ext q
    simp [smul_smul, mul_comm, TensorProduct.map_map, ← TensorProduct.map_comp,
      valLinEquiv_symm_apply]

lemma repGaugeGroupI_tmul (g : GaugeGroupI) (ψ : Fermion.LeftHandedWeyl)
    (v : EuclideanSpace ℂ (Fin 3)) (w : EuclideanSpace ℂ (Fin 2)) :
    repGaugeGroupI g ⟨ψ ⊗ₜ v ⊗ₜ w⟩ = ⟨g.toU1 • ψ ⊗ₜ (g.toSU3.1.toEuclideanLin v) ⊗ₜ
      (g.toSU2.1.toEuclideanLin w)⟩ := rfl

@[simp]
lemma repGaugeGroupI_gaugeGroupℤ₆OfRoot_apply (α : rootsOfUnity 6 ℂ) (q : QuarkDoublet) :
    repGaugeGroupI (gaugeGroupℤ₆OfRoot α) q = q := by
  obtain ⟨c, rfl⟩ := valLinEquiv.symm.surjective q
  induction' c using TensorProduct.induction_on with ψ w v1 v2 h1 h2
  · simp
  · induction' ψ using TensorProduct.induction_on with ψ v v1 v2 h1 h2
    · simp
    · simp [valLinEquiv_symm_apply, repGaugeGroupI_tmul, gaugeGroupℤ₆SU2OfRoot_toEuclideanLin_apply,
        gaugeGroupℤ₆SU3OfRoot_toEuclideanLin_apply, smul_smul, tmul_smul, smul_tmul,
        gaugeGroupℤ₆UnitaryOfRoot,]
      suffices h : (α.1 * ((starRingEnd ℂ) α.1 ^ 3 *  α.1 ^ 2)) = 1 by simp [h]
      simp only [Complex.conj_rootsOfUnity α.2, Units.val_inv_eq_inv_val, inv_pow]
      field_simp
    · simp_all [add_tmul]
  · simp_all

/-- The action of the Standard Model gauge group, potentially quotiented by
  a discrete factor on quark fields. -/
noncomputable def repGaugeGroup : (Q : GaugeGroupQuot) →
    Representation ℂ (GaugeGroup Q) QuarkDoublet
  | .I => repGaugeGroupI
  | .ℤ₆ => QuotientGroup.lift _ repGaugeGroupI <| by
      simp only [gaugeGroupℤ₆SubGroup, SetLike.le_def, MonoidHom.mem_range, gaugeGroupℤ₆Hom_apply,
        Subtype.exists, mem_rootsOfUnity, MonoidHom.mem_ker, forall_exists_index]
      rintro g x hx ⟨rfl⟩
      ext q
      simp
  | .ℤ₂ => QuotientGroup.lift _ repGaugeGroupI <| by
      simp only [SetLike.le_def, gaugeGroupℤ₂SubGroup, MonoidHom.mem_range, gaugeGroupℤ₂Hom_apply,
        gaugeGroupℤ₂OfRoot, Subtype.exists, mem_rootsOfUnity, MonoidHom.mem_ker,
        forall_exists_index]
      rintro g x hx ⟨rfl⟩
      ext q
      simp
  | .ℤ₃ => QuotientGroup.lift _ repGaugeGroupI <| by
      simp only [SetLike.le_def, gaugeGroupℤ₃SubGroup, MonoidHom.mem_range, gaugeGroupℤ₃Hom_apply,
        gaugeGroupℤ₃OfRoot, Subtype.exists, mem_rootsOfUnity, MonoidHom.mem_ker,
        forall_exists_index]
      rintro g x hx ⟨rfl⟩
      ext q
      simp

TODO "Find the subgroup of the Standard Model gauge group which acts trivially on the
  quark doublet."

end QuarkDoublet

end StandardModel
