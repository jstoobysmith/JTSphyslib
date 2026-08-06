/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.Jet
public import Physlib.Particles.StandardModel.GaugeBosons.BBoson
public import Mathlib.RingTheory.TensorProduct.Basic
public import Physlib.Relativity.Tensors.ComplexTensor.Basic
public import Physlib.Mathematics.ConjModule
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Physlib.Particles.LagrangianTheory.Basic
public import Mathlib.Algebra.TrivSqZeroExt.Basic
/-!
# Charged-lepton singlets

## i. Overview

The Standard Model charged-lepton singlet is a right-handed Weyl spinor in the `(1, 1)_{-6}`
representation. Here charges are normalized as `6Y`, so `-6` is the usual hypercharge
`Y = -1`.

`LeptonSinglet` is the target vector space of one charged-lepton singlet. Its only index is
the Lorentz index carried by the Weyl spinor.

The Lorentz and gauge actions are first defined separately. The gauge action is then computed
on an arbitrary spinor, used to identify its kernel, and descended to each supported global
form of the Standard Model gauge group.

## ii. Key results

- `LeptonSinglet` : the target space of the `(1, 1)_{-6}` multiplet.
- `repLorentzGroup` : the right-handed Lorentz action.
- `repGaugeGroupI` : the action of the unquotiented gauge group.
- `repGaugeGroupI_apply` : the gauge action on a spinor.
- `mem_repGaugeGroupI_ker_iff_eq` : the kernel of the full-group action.
- `gaugeGroup_subgroup_ℤ₆_le_ker_repGaugeGroupI` : triviality of the central `ℤ₆`.
- `repGaugeGroup` : the action descended to every supported gauge-group quotient.

## iii. Table of contents

- A. The charged-lepton-singlet space
- B. Linear structure
- C. Lorentz action
- D. Gauge action
- E. Kernel of the gauge action
- F. Descent to quotient gauge groups
- G. Jet gauge action

-/

@[expose] public section

namespace StandardModel

/-!

## A. The charged-lepton-singlet space

The Weyl spinor carries the right-handed Lorentz index, and it is the whole of the multiplet:
a charged-lepton singlet has no colour index and no weak-isospin index.
-/

/-- The target vector space of one Standard Model charged-lepton singlet.
  It carries the `(1, 1)_{-6}` representation of the gauge group. -/
@[ext]
structure LeptonSinglet where
  /-- The right-handed Weyl spinor. -/
  val : Fermion.RightHandedWeyl

namespace LeptonSinglet

/-!

## B. Linear structure

The wrapper distinguishes charged-lepton singlets from other isomorphic vector spaces.
The following equivalences transfer the linear structure of the Weyl-spinor space and expose
that model when defining representations.
-/

/-- Identifies a charged-lepton singlet with its underlying Weyl spinor. -/
def valEquiv : LeptonSinglet ≃ Fermion.RightHandedWeyl where
  toFun := val
  invFun := fun m => ⟨m⟩

instance : AddCommGroup LeptonSinglet := Equiv.addCommGroup valEquiv

instance : Module ℂ LeptonSinglet := Equiv.module ℂ valEquiv

/-- The linear identification with the underlying Weyl-spinor space. -/
def valLinEquiv : LeptonSinglet ≃ₗ[ℂ] Fermion.RightHandedWeyl where
  toFun := val
  invFun := fun m => ⟨m⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp]
lemma valLinEquiv_apply (l : LeptonSinglet) : valLinEquiv l = l.val := rfl

lemma valLinEquiv_symm_apply (m : Fermion.RightHandedWeyl) :
    valLinEquiv.symm m = ⟨m⟩ := rfl

@[simp]
lemma val_add (l₁ l₂ : LeptonSinglet) : (l₁ + l₂).val = l₁.val + l₂.val := rfl

@[simp]
lemma val_smul (r : ℂ) (l : LeptonSinglet) : (r • l).val = r • l.val := rfl

/-!

## The basis of the charged-lepton-singlet space

-/

/-- A basis on the charged-lepton singlets. -/
noncomputable def basis : Module.Basis (Fin 2) ℂ LeptonSinglet :=
  Fermion.RightHandedWeyl.basis.map valLinEquiv.symm

/-!

## C. Lorentz action

The Lorentz group acts through the right-handed Weyl representation, transported along the
identification of a charged-lepton singlet with its spinor.
-/

open Matrix MatrixGroups

/-- The right-handed Lorentz representation on charged-lepton singlets. -/
noncomputable def repLorentzGroup : Representation ℂ (SL(2,ℂ)) LeptonSinglet where
  toFun Λ := valLinEquiv.symm ∘ₗ Fermion.RightHandedWeyl.rep Λ ∘ₗ valLinEquiv
  map_one' := by
    ext l
    simp [Module.End.one_eq_id]
  map_mul' Λ₁ Λ₂ := by
    ext1 l
    simp [Module.End.mul_eq_comp]

/-- The Lorentz action on the lepton-singlet basis: the right-handed Weyl
  action by the entrywise conjugate matrix. -/
lemma repLorentzGroup_apply_basis (Λ : SL(2,ℂ)) (α : Fin 2) :
    repLorentzGroup Λ (basis α) = ∑ β, star (Λ.1 β α) • basis β := by
  simp only [basis, Module.Basis.map_apply, repLorentzGroup, MonoidHom.coe_mk,
    OneHom.coe_mk, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.apply_symm_apply, Fermion.RightHandedWeyl.rep_apply_basis,
    Matrix.map_apply, map_sum, map_smul]

/-- The lepton jet coordinates transform contragrediently, by the entrywise
  conjugate of the inverse matrix. -/
lemma repLorentzGroup_dual_dualBasis (Λ : SL(2,ℂ)) (α : Fin 2) :
    repLorentzGroup.dual Λ (basis.dualBasis α) =
      ∑ β, star ((Λ⁻¹).1 α β) • basis.dualBasis β :=
  Representation.dual_apply_dualBasis _ _ _ _
    (Matrix.of fun l j => star ((Λ⁻¹).1 l j))
    (fun j => repLorentzGroup_apply_basis Λ⁻¹ j)

/-- The Lorentz action on the conjugate lepton basis: the coefficients are the
  conjugates of those of the lepton action, that is, the matrix itself. -/
lemma repLorentzGroup_conj_apply_basis (Λ : SL(2,ℂ)) (α : Fin 2) :
    repLorentzGroup.conj Λ (basis.conj α) = ∑ β, Λ.1 β α • basis.conj β := by
  rw [Representation.conj_apply, Module.Basis.conj_apply,
    LinearEquiv.symm_apply_apply, repLorentzGroup_apply_basis, map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [LinearEquiv.map_smulₛₗ, starRingEnd_apply, star_star, Module.Basis.conj_apply]

/-- The conjugate lepton jet coordinates transform by the inverse matrix. -/
lemma repLorentzGroup_conj_dual_dualBasis (Λ : SL(2,ℂ)) (α : Fin 2) :
    repLorentzGroup.conj.dual Λ (basis.conj.dualBasis α) =
      ∑ β, (Λ⁻¹).1 α β • basis.conj.dualBasis β :=
  Representation.dual_apply_dualBasis _ _ _ _
    (Matrix.of fun l j => (Λ⁻¹).1 l j)
    (fun j => repLorentzGroup_conj_apply_basis Λ⁻¹ j)

/-!

## D. Global Gauge action

The colour and weak factors act trivially, so the gauge group acts only through hypercharge.
The `U(1)` action is `star z ^ 6`; since `z` is unitary, `star z = z⁻¹`, so this represents
charge `-6`.

The formulas below expose the scalar used to compare actions and compute the kernel.
-/

/-- The `(1, 1)_{-6}` action of the unquotiented Standard Model gauge group. -/
noncomputable def repGaugeGroupI : Representation ℂ GaugeGroupI LeptonSinglet where
  toFun g := valLinEquiv.symm ∘ₗ
      LinearMap.lsmul ℂ Fermion.RightHandedWeyl (star g.toU1.1 ^ 6 : ℂ)
      ∘ₗ valLinEquiv
  map_one' := by
    ext l
    simp [valLinEquiv_symm_apply]
  map_mul' g₁ g₂ := by
    ext l
    simp [smul_smul, mul_comm, valLinEquiv_symm_apply]
    ring_nf

/-- The gauge group acts on a charged-lepton singlet by the hypercharge scalar alone. -/
lemma repGaugeGroupI_apply (g : GaugeGroupI) (ψ : Fermion.RightHandedWeyl) :
    repGaugeGroupI g ⟨ψ⟩ = ⟨(star g.toU1.1 ^ 6) • ψ⟩ := rfl

open Fermion in
/-- The gauge action is diagonal in the standard Weyl basis. -/
lemma repGaugeGroupI_basis (g : GaugeGroupI) (k : Fin 2) :
    repGaugeGroupI g ⟨RightHandedWeyl.basis k⟩ =
      (star g.toU1.1 ^ 6) • (⟨RightHandedWeyl.basis k⟩ : LeptonSinglet) := rfl

open Fermion in
/-- Two gauge elements induce the same action exactly when their hypercharge scalars agree. -/
lemma repGaugeGroupI_eq_iff {g₁ g₂ : GaugeGroupI} :
    repGaugeGroupI g₁ = repGaugeGroupI g₂ ↔
      star g₁.toU1.1 ^ 6 = star g₂.toU1.1 ^ 6 := by
  constructor
  · intro h
    have h' := congrFun (congrArg (fun f => f.1) h)
      (⟨RightHandedWeyl.basis 0⟩ : LeptonSinglet)
    simp only [LinearMap.coe_toAddHom, repGaugeGroupI_apply] at h'
    have h'' := congrArg (fun v => RightHandedWeyl.basis.repr (LeptonSinglet.val v) 0) h'
    simpa using h''
  · intro h
    have h' : (starRingEnd ℂ) g₁.toU1.1 ^ 6 = (starRingEnd ℂ) g₂.toU1.1 ^ 6 := h
    ext l
    simp [repGaugeGroupI, h']

/-!

## E. Kernel of the gauge action

An element acts trivially exactly when its hypercharge scalar is one. Its colour and weak
components are unrestricted, since neither appears in the action.
-/

/-- Characterizes the full-group elements acting trivially on the charged-lepton singlet. -/
lemma mem_repGaugeGroupI_ker_iff_eq {g : GaugeGroupI} :
    g ∈ repGaugeGroupI.ker ↔ star g.toU1.1 ^ 6 = 1 := by
  rw [MonoidHom.mem_ker, ← MonoidHom.map_one repGaugeGroupI, repGaugeGroupI_eq_iff]
  simp

/-!

## F. Descent to quotient gauge groups

A representation descends through a quotient when the quotient subgroup lies in its kernel.
The `U(1)` component of a central element is a sixth root of unity, so conjugating and raising
to the sixth power gives one, and charge `-6` therefore acts trivially.
-/

/-- The central `ℤ₆` subgroup acts trivially on `(1, 1)_{-6}`. -/
lemma gaugeGroup_subgroup_ℤ₆_le_ker_repGaugeGroupI :
    GaugeGroupQuot.subgroup .ℤ₆ ≤ repGaugeGroupI.ker := by
  simp only [GaugeGroupQuot.subgroup, gaugeGroupℤ₆SubGroup, SetLike.le_def,
    MonoidHom.mem_range, gaugeGroupℤ₆Hom_apply, Subtype.exists,
    mem_repGaugeGroupI_ker_iff_eq, forall_exists_index]
  rintro g x hx ⟨rfl⟩
  simp only [gaugeGroupℤ₆OfRoot_toU1, gaugeGroupℤ₆UnitaryOfRoot_coe]
  have hx6 : (((x : ℂˣ) : ℂ)) ^ 6 = 1 := (mem_rootsOfUnity' 6 x).mp hx
  simpa [map_pow] using congrArg (starRingEnd ℂ) hx6

/-- Every supported quotient subgroup acts trivially on the charged-lepton singlet. -/
lemma gaugeGroup_subgroup_le_ker_repGaugeGroupI (Q : GaugeGroupQuot) :
    Q.subgroup ≤ repGaugeGroupI.ker := Q.subgroup_le_subgroup_ℤ₆.trans
  gaugeGroup_subgroup_ℤ₆_le_ker_repGaugeGroupI

/-- The `(1, 1)_{-6}` representation for every supported global form of the
  Standard Model gauge group. -/
noncomputable def repGaugeGroup : (Q : GaugeGroupQuot) →
    Representation ℂ (GaugeGroup Q) LeptonSinglet
  | .I => repGaugeGroupI
  | .ℤ₆ => QuotientGroup.lift _ repGaugeGroupI (gaugeGroup_subgroup_le_ker_repGaugeGroupI .ℤ₆)
  | .ℤ₂ => QuotientGroup.lift _ repGaugeGroupI (gaugeGroup_subgroup_le_ker_repGaugeGroupI .ℤ₂)
  | .ℤ₃ => QuotientGroup.lift _ repGaugeGroupI (gaugeGroup_subgroup_le_ker_repGaugeGroupI .ℤ₃)

/-!

## G. The jet component vector space

A Lagrangian containing a charged lepton singlet may have terms
of the form `∂_μ ∂_ν ψ`. These expressions should be considered as
component functions which takes in a section of the
bundle of charged lepton singlets and returns a complex number.

The space of all such component functions is what we call the jet component space.
The lagrangian is an element of the algebra over all such component
functions for all the fields in the theory.

For matter particles, the (jet) Gauge group acts on the
jet component space as a representation. This is not case for the gauge bosons.

-/

open TensorProduct LagrangianTheory

inductive JetGenerators where
  | dψ (s : Multiset (Fin 1 ⊕ Fin 3)) (α : Fin 2) : JetGenerators
  | dbarψ (s : Multiset (Fin 1 ⊕ Fin 3)) (α : Fin 2) : JetGenerators
deriving DecidableEq

def JetGenerators.equiv : JetGenerators ≃
    (Multiset (Fin 1 ⊕ Fin 3) × Fin 2 ⊕ Multiset (Fin 1 ⊕ Fin 3) × Fin 2) where
  toFun
    | JetGenerators.dψ s α => Sum.inl (s, α)
    | JetGenerators.dbarψ s α => Sum.inr (s, α)
  invFun
    | Sum.inl (s, α) => JetGenerators.dψ s α
    | Sum.inr (s, α) => JetGenerators.dbarψ s α
  left_inv := by
    intro x
    cases x <;> rfl
  right_inv := by
    intro x
    cases x <;> rfl

def JetGenerators.massWeight : JetGenerators → ℕ
  | JetGenerators.dψ s _ => 3 + 2 * s.card
  | JetGenerators.dbarψ s _ => 3 + 2 * s.card

abbrev JetComponentSpace :=
  (SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ]
    Module.Dual ℂ LeptonSinglet) ×
  (SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ]
    Module.Dual ℂ (ConjModule LeptonSinglet))

noncomputable def JetComponentSpace.basis : Module.Basis JetGenerators ℂ JetComponentSpace :=
  ((DerivAlgebraComplex.basis.tensorProduct
      LeptonSinglet.basis.dualBasis).prod
    (DerivAlgebraComplex.basis.tensorProduct
      (LeptonSinglet.basis.conj.dualBasis))).reindex JetGenerators.equiv.symm

/-- The basis vector of the jet component space at the zeroth-order singlet
  generator: the unit of the dual jet algebra tensored with the dual basis of the
  singlet, in the first (unconjugated) factor. -/
lemma JetComponentSpace.basis_dψ_nil (α : Fin 2) :
    JetComponentSpace.basis (.dψ {} α) =
      ((1 : SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule)) ⊗ₜ[ℂ]
        LeptonSinglet.basis.dualBasis α, 0) := by
  rw [JetComponentSpace.basis, Module.Basis.reindex_apply,
    show JetGenerators.equiv.symm.symm (.dψ {} α) = Sum.inl ({}, α) from rfl]
  refine Prod.ext ?_ ?_
  · rw [Module.Basis.prod_apply_inl_fst, Module.Basis.tensorProduct_apply',
      DerivAlgebraComplex.basis_nil]
  · rw [Module.Basis.prod_apply_inl_snd]

/-- The basis vector of the jet component space at a first-order singlet
  generator: the dual derivative symbol tensored with the dual basis of the
  singlet, in the first (unconjugated) factor. -/
lemma JetComponentSpace.basis_dψ_singleton (μ : Fin 1 ⊕ Fin 3) (α : Fin 2) :
    JetComponentSpace.basis (.dψ {μ} α) =
      (SymmetricAlgebra.ι ℂ (Module.Dual ℂ Lorentz.CoℂModule)
        (Lorentz.complexCoBasis.dualBasis μ) ⊗ₜ[ℂ]
        LeptonSinglet.basis.dualBasis α, 0) := by
  rw [JetComponentSpace.basis, Module.Basis.reindex_apply,
    show JetGenerators.equiv.symm.symm (.dψ {μ} α) = Sum.inl ({μ}, α) from rfl]
  refine Prod.ext ?_ ?_
  · rw [Module.Basis.prod_apply_inl_fst, Module.Basis.tensorProduct_apply',
      DerivAlgebraComplex.basis_singleton]
  · rw [Module.Basis.prod_apply_inl_snd]

/-- The basis vector of the jet component space at a general singlet generator:
  the dual jet algebra basis vector at its multiset of derivative indices,
  tensored with the dual basis of the singlet, in the first (unconjugated)
  factor. -/
lemma JetComponentSpace.basis_dψ (s : Multiset (Fin 1 ⊕ Fin 3)) (α : Fin 2) :
    JetComponentSpace.basis (.dψ s α) =
      (DerivAlgebraComplex.basis s ⊗ₜ[ℂ] LeptonSinglet.basis.dualBasis α, 0) := by
  rw [JetComponentSpace.basis, Module.Basis.reindex_apply,
    show JetGenerators.equiv.symm.symm (.dψ s α) = Sum.inl (s, α) from rfl]
  refine Prod.ext ?_ ?_
  · rw [Module.Basis.prod_apply_inl_fst, Module.Basis.tensorProduct_apply']
  · rw [Module.Basis.prod_apply_inl_snd]

/-- The basis vector of the jet component space at a general conjugate-singlet
  generator: the dual jet algebra basis vector at its multiset of derivative
  indices, tensored with the conjugate dual basis of the singlet, in the second
  (conjugated) factor. -/
lemma JetComponentSpace.basis_dbarψ (s : Multiset (Fin 1 ⊕ Fin 3)) (α : Fin 2) :
    JetComponentSpace.basis (.dbarψ s α) =
      (0, DerivAlgebraComplex.basis s ⊗ₜ[ℂ] LeptonSinglet.basis.conj.dualBasis α) := by
  rw [JetComponentSpace.basis, Module.Basis.reindex_apply,
    show JetGenerators.equiv.symm.symm (.dbarψ s α) = Sum.inr (s, α) from rfl]
  refine Prod.ext ?_ ?_
  · rw [Module.Basis.prod_apply_inr_fst]
  · rw [Module.Basis.prod_apply_inr_snd, Module.Basis.tensorProduct_apply']

noncomputable def JetComponentSpace.repLorentzGroup :
    Representation ℂ (SL(2,ℂ)) JetComponentSpace :=
  (DerivAlgebraComplex.repLorentzGroup.tprod LeptonSinglet.repLorentzGroup.dual).prod
  (DerivAlgebraComplex.repLorentzGroup.tprod LeptonSinglet.repLorentzGroup.conj.dual)

/-- The Lorentz action on the zeroth-order lepton jet coordinate: the
  contragredient conjugate spinor action. -/
lemma JetComponentSpace.repLorentzGroup_basis_dψ_nil (Λ : SL(2,ℂ)) (α : Fin 2) :
    JetComponentSpace.repLorentzGroup Λ (JetComponentSpace.basis (.dψ {} α)) =
      ∑ β, star ((Λ⁻¹).1 α β) • JetComponentSpace.basis (.dψ {} β) := by
  rw [basis_dψ_nil,
    show JetComponentSpace.repLorentzGroup Λ =
      LinearMap.prodMap
        (TensorProduct.map (DerivAlgebraComplex.repLorentzGroup Λ)
          (LeptonSinglet.repLorentzGroup.dual Λ))
        (TensorProduct.map (DerivAlgebraComplex.repLorentzGroup Λ)
          (LeptonSinglet.repLorentzGroup.conj.dual Λ)) from rfl,
    LinearMap.prodMap_apply, map_zero, TensorProduct.map_tmul,
    DerivAlgebraComplex.repLorentzGroup_apply_one,
    LeptonSinglet.repLorentzGroup_dual_dualBasis, TensorProduct.tmul_sum]
  have hb : ∀ β : Fin 2, JetComponentSpace.basis
      (.dψ (0 : Multiset (Fin 1 ⊕ Fin 3)) β) =
      ((1 : SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule)) ⊗ₜ[ℂ]
        LeptonSinglet.basis.dualBasis β, 0) := fun β => basis_dψ_nil β
  refine Prod.ext ?_ ?_
  · simp [Prod.fst_sum, hb, TensorProduct.tmul_smul]
  · simp [Prod.snd_sum, hb]

set_option maxHeartbeats 1000000 in
/-- The Lorentz action on the first-order lepton jet coordinate: the derivative
  slot transforms by the columns of the Lorentz matrix and the spinor slot
  contragrediently. -/
lemma JetComponentSpace.repLorentzGroup_basis_dψ_singleton (Λ : SL(2,ℂ))
    (μ : Fin 1 ⊕ Fin 3) (α : Fin 2) :
    JetComponentSpace.repLorentzGroup Λ (JetComponentSpace.basis (.dψ {μ} α)) =
      ∑ ν, ∑ β, ((((Lorentz.SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) *
        star ((Λ⁻¹).1 α β)) • JetComponentSpace.basis (.dψ {ν} β) := by
  rw [basis_dψ_singleton,
    show JetComponentSpace.repLorentzGroup Λ =
      LinearMap.prodMap
        (TensorProduct.map (DerivAlgebraComplex.repLorentzGroup Λ)
          (LeptonSinglet.repLorentzGroup.dual Λ))
        (TensorProduct.map (DerivAlgebraComplex.repLorentzGroup Λ)
          (LeptonSinglet.repLorentzGroup.conj.dual Λ)) from rfl,
    LinearMap.prodMap_apply, map_zero, TensorProduct.map_tmul,
    DerivAlgebraComplex.repLorentzGroup_apply_ι,
    Lorentz.CoℂModule.SL2CRep_dual_dualBasis,
    LeptonSinglet.repLorentzGroup_dual_dualBasis, map_sum, TensorProduct.sum_tmul]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_sum, Prod.smul_fst, basis_dψ_singleton, map_smul,
      TensorProduct.smul_tmul', TensorProduct.tmul_sum, TensorProduct.sum_tmul,
      Finset.smul_sum, TensorProduct.tmul_smul, smul_smul]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun β _ => ?_
    rw [mul_comm]
  · simp [Prod.snd_sum, basis_dψ_singleton, TensorProduct.tmul_sum,
      TensorProduct.sum_tmul, map_smul, TensorProduct.smul_tmul']

/-- The Lorentz action on the zeroth-order conjugate lepton jet coordinate. -/
lemma JetComponentSpace.repLorentzGroup_basis_dbarψ_nil (Λ : SL(2,ℂ)) (α : Fin 2) :
    JetComponentSpace.repLorentzGroup Λ (JetComponentSpace.basis (.dbarψ {} α)) =
      ∑ β, (Λ⁻¹).1 α β • JetComponentSpace.basis (.dbarψ {} β) := by
  rw [basis_dbarψ,
    show JetComponentSpace.repLorentzGroup Λ =
      LinearMap.prodMap
        (TensorProduct.map (DerivAlgebraComplex.repLorentzGroup Λ)
          (LeptonSinglet.repLorentzGroup.dual Λ))
        (TensorProduct.map (DerivAlgebraComplex.repLorentzGroup Λ)
          (LeptonSinglet.repLorentzGroup.conj.dual Λ)) from rfl,
    LinearMap.prodMap_apply, map_zero, TensorProduct.map_tmul,
    show DerivAlgebraComplex.basis ({} : Multiset (Fin 1 ⊕ Fin 3)) = 1 from
      DerivAlgebraComplex.basis_nil,
    DerivAlgebraComplex.repLorentzGroup_apply_one,
    LeptonSinglet.repLorentzGroup_conj_dual_dualBasis, TensorProduct.tmul_sum]
  have hb0 : DerivAlgebraComplex.basis (0 : Multiset (Fin 1 ⊕ Fin 3)) = 1 :=
    DerivAlgebraComplex.basis_nil
  refine Prod.ext ?_ ?_
  · simp [Prod.fst_sum, basis_dbarψ]
  · simp [Prod.snd_sum, basis_dbarψ, TensorProduct.tmul_smul, hb0]

set_option maxHeartbeats 1000000 in
/-- The Lorentz action on the first-order conjugate lepton jet coordinate. -/
lemma JetComponentSpace.repLorentzGroup_basis_dbarψ_singleton (Λ : SL(2,ℂ))
    (μ : Fin 1 ⊕ Fin 3) (α : Fin 2) :
    JetComponentSpace.repLorentzGroup Λ (JetComponentSpace.basis (.dbarψ {μ} α)) =
      ∑ ν, ∑ β, ((((Lorentz.SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) *
        (Λ⁻¹).1 α β) • JetComponentSpace.basis (.dbarψ {ν} β) := by
  rw [basis_dbarψ,
    show JetComponentSpace.repLorentzGroup Λ =
      LinearMap.prodMap
        (TensorProduct.map (DerivAlgebraComplex.repLorentzGroup Λ)
          (LeptonSinglet.repLorentzGroup.dual Λ))
        (TensorProduct.map (DerivAlgebraComplex.repLorentzGroup Λ)
          (LeptonSinglet.repLorentzGroup.conj.dual Λ)) from rfl,
    LinearMap.prodMap_apply, map_zero, TensorProduct.map_tmul,
    show DerivAlgebraComplex.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3)) =
        SymmetricAlgebra.ι ℂ (Module.Dual ℂ Lorentz.CoℂModule)
          (Lorentz.complexCoBasis.dualBasis μ) from
      DerivAlgebraComplex.basis_singleton μ,
    DerivAlgebraComplex.repLorentzGroup_apply_ι,
    Lorentz.CoℂModule.SL2CRep_dual_dualBasis,
    LeptonSinglet.repLorentzGroup_conj_dual_dualBasis, map_sum,
    TensorProduct.sum_tmul]
  refine Prod.ext ?_ ?_
  · simp [Prod.fst_sum, basis_dbarψ, TensorProduct.tmul_sum,
      TensorProduct.sum_tmul, map_smul, TensorProduct.smul_tmul']
  · simp only [Prod.snd_sum, Prod.smul_snd, basis_dbarψ,
      DerivAlgebraComplex.basis_singleton, map_smul, TensorProduct.smul_tmul',
      TensorProduct.tmul_sum, TensorProduct.sum_tmul, Finset.smul_sum,
      TensorProduct.tmul_smul, smul_smul]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun β _ => ?_
    rw [mul_comm]

/-- The action of the jet gauge group on the dual jet algebra of the
  charged-lepton singlet's component functions. Component functions transform
  contragrediently to the field, so the hypercharge power series is
  `u ^ 6 = (star u ^ 6)⁻¹`, acting through the Leibniz rule on the dual
  derivative symbols. -/
noncomputable def dualJetAlgebraRepJetGaugeGroupI :
    Representation ℂ JetGaugeGroupI
      (SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule)) where
  toFun U := DerivAlgebraComplex.jetRingAction (((U.2.2 : unitary JetRing) : JetRing) ^ 6)
  map_one' := by
    rw [show (((1 : JetGaugeGroupI).2.2 : unitary JetRing) : JetRing) ^ 6 =
        (1 : JetRing) by simp, DerivAlgebraComplex.jetRingAction_one]
    rfl
  map_mul' U₁ U₂ := by
    rw [show (((U₁ * U₂ : JetGaugeGroupI).2.2 : unitary JetRing) : JetRing) ^ 6 =
        ((U₁.2.2 : unitary JetRing) : JetRing) ^ 6 *
          ((U₂.2.2 : unitary JetRing) : JetRing) ^ 6 by
      rw [show (((U₁ * U₂ : JetGaugeGroupI).2.2 : unitary JetRing) : JetRing) =
          ((U₁.2.2 : unitary JetRing) : JetRing) * ((U₂.2.2 : unitary JetRing) : JetRing)
          from rfl, mul_pow],
      DerivAlgebraComplex.jetRingAction_mul, Module.End.mul_eq_comp]

/-- The action of the jet gauge group on the dual jet algebra of the conjugate
  charged-lepton singlet's component functions: the conjugate components
  transform with the conjugate-contragredient hypercharge power series
  `star u ^ 6`. -/
noncomputable def dualJetAlgebraRepJetGaugeGroupIConj :
    Representation ℂ JetGaugeGroupI
      (SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule)) where
  toFun U := DerivAlgebraComplex.jetRingAction ((star ((U.2.2 : unitary JetRing) : JetRing)) ^ 6)
  map_one' := by
    rw [show (star (((1 : JetGaugeGroupI).2.2 : unitary JetRing) : JetRing)) ^ 6 =
        (1 : JetRing) by simp, DerivAlgebraComplex.jetRingAction_one]
    rfl
  map_mul' U₁ U₂ := by
    rw [show (star (((U₁ * U₂ : JetGaugeGroupI).2.2 : unitary JetRing) : JetRing)) ^ 6 =
        (star ((U₁.2.2 : unitary JetRing) : JetRing)) ^ 6 *
          (star ((U₂.2.2 : unitary JetRing) : JetRing)) ^ 6 by
      rw [show (((U₁ * U₂ : JetGaugeGroupI).2.2 : unitary JetRing) : JetRing) =
          ((U₁.2.2 : unitary JetRing) : JetRing) * ((U₂.2.2 : unitary JetRing) : JetRing)
          from rfl, star_mul', mul_pow],
      DerivAlgebraComplex.jetRingAction_mul, Module.End.mul_eq_comp]

@[simp]
lemma dualJetAlgebraRepJetGaugeGroupI_apply (U : JetGaugeGroupI) :
    dualJetAlgebraRepJetGaugeGroupI U =
      DerivAlgebraComplex.jetRingAction (((U.2.2 : unitary JetRing) : JetRing) ^ 6) := rfl

@[simp]
lemma dualJetAlgebraRepJetGaugeGroupIConj_apply (U : JetGaugeGroupI) :
    dualJetAlgebraRepJetGaugeGroupIConj U =
      DerivAlgebraComplex.jetRingAction ((star ((U.2.2 : unitary JetRing) : JetRing)) ^ 6) := rfl

/-- The `(1, 1)_{-6}` action of the jet gauge group on the space of component
  functions of the charged-lepton singlet, its conjugate, and their derivative
  coordinates. The conventions are contragredient, matching the `.dual` and
  `.conj.dual` conventions of the global component-space representations: the
  singlet components transform through the derivative action of `u ^ 6`, the
  conjugate components through the derivative action of `star u ^ 6`, and the
  target factors are inert. On jets of constant gauge transformations the
  derivative symbols are inert and the action reduces to the dual global gauge
  action. -/
noncomputable def JetComponentSpace.repJetGaugeGroupI :
    Representation ℂ JetGaugeGroupI JetComponentSpace :=
  (dualJetAlgebraRepJetGaugeGroupI.tprod
      (Representation.trivial ℂ JetGaugeGroupI (Module.Dual ℂ LeptonSinglet))).prod
    (dualJetAlgebraRepJetGaugeGroupIConj.tprod
      (Representation.trivial ℂ JetGaugeGroupI (Module.Dual ℂ (ConjModule LeptonSinglet))))

/-- The jet gauge action preserves the unconjugated half of the component space,
  acting there by the dual derivative action of the contragredient hypercharge
  power series on the derivative symbols. -/
lemma JetComponentSpace.repJetGaugeGroupI_inl (U : JetGaugeGroupI)
    (a : SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule))
    (φ : Module.Dual ℂ LeptonSinglet) :
    JetComponentSpace.repJetGaugeGroupI U ((a ⊗ₜ[ℂ] φ, 0) : JetComponentSpace) =
      ((DerivAlgebraComplex.jetRingAction (((U.2.2 : unitary JetRing) : JetRing) ^ 6) a) ⊗ₜ[ℂ] φ, 0) := by
  refine Prod.ext ?_ ?_ <;>
    simp [JetComponentSpace.repJetGaugeGroupI, Representation.prod_apply_apply,
      Representation.tprod_apply, dualJetAlgebraRepJetGaugeGroupI_apply]

/-- The jet gauge action on a general element of the unconjugated half of the
  component space. -/
lemma JetComponentSpace.repJetGaugeGroupI_inl' (U : JetGaugeGroupI)
    (y : SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ]
      Module.Dual ℂ LeptonSinglet) :
    JetComponentSpace.repJetGaugeGroupI U ((y, 0) : JetComponentSpace) =
      ((TensorProduct.map (DerivAlgebraComplex.jetRingAction (((U.2.2 : unitary JetRing) : JetRing) ^ 6))
        LinearMap.id) y, 0) := by
  induction y using TensorProduct.induction_on with
  | zero =>
    rw [show ((0, 0) : JetComponentSpace) = 0 from rfl, map_zero, map_zero]
    rfl
  | add a b ha hb =>
    have hpair : ((a + b, 0) : JetComponentSpace) = (a, 0) + (b, 0) := by
      simp
    rw [hpair, map_add, ha, hb, map_add]
    simp
  | tmul a φ =>
    rw [JetComponentSpace.repJetGaugeGroupI_inl, TensorProduct.map_tmul]
    rfl

/-- The jet gauge action preserves the conjugated half of the component space,
  acting there by the dual derivative action of the conjugate-contragredient
  hypercharge power series on the derivative symbols. -/
lemma JetComponentSpace.repJetGaugeGroupI_inr (U : JetGaugeGroupI)
    (a : SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule))
    (φ : Module.Dual ℂ (ConjModule LeptonSinglet)) :
    JetComponentSpace.repJetGaugeGroupI U ((0, a ⊗ₜ[ℂ] φ) : JetComponentSpace) =
      (0, (DerivAlgebraComplex.jetRingAction
        ((star ((U.2.2 : unitary JetRing) : JetRing)) ^ 6) a) ⊗ₜ[ℂ] φ) := by
  refine Prod.ext ?_ ?_ <;>
    simp [JetComponentSpace.repJetGaugeGroupI, Representation.prod_apply_apply,
      Representation.tprod_apply, dualJetAlgebraRepJetGaugeGroupIConj_apply]

/-- The jet gauge action on a general element of the conjugated half of the
  component space. -/
lemma JetComponentSpace.repJetGaugeGroupI_inr' (U : JetGaugeGroupI)
    (y : SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ]
      Module.Dual ℂ (ConjModule LeptonSinglet)) :
    JetComponentSpace.repJetGaugeGroupI U ((0, y) : JetComponentSpace) =
      (0, (TensorProduct.map (DerivAlgebraComplex.jetRingAction
        ((star ((U.2.2 : unitary JetRing) : JetRing)) ^ 6)) LinearMap.id) y) := by
  induction y using TensorProduct.induction_on with
  | zero =>
    rw [show ((0, 0) : JetComponentSpace) = 0 from rfl, map_zero, map_zero]
    rfl
  | add a b ha hb =>
    have hpair : ((0, a + b) : JetComponentSpace) = (0, a) + (0, b) := by
      simp
    rw [hpair, map_add, ha, hb, map_add]
    simp
  | tmul a φ =>
    rw [JetComponentSpace.repJetGaugeGroupI_inr, TensorProduct.map_tmul]
    rfl

/-!

## The formal total derivative on the component functions

The formal total spacetime derivative `∂_μ` acts on the component functions of
the charged-lepton jet by appending the derivative index,
`∂_s ψ_α ↦ ∂_{s + {μ}} ψ_α`, and likewise on the conjugate components.

-/

namespace JetGenerators

/-- The jet generator with one further derivative in the direction `μ`. -/
def shift (μ : Fin 1 ⊕ Fin 3) : JetGenerators → JetGenerators
  | dψ s α => dψ (s + {μ}) α
  | dbarψ s α => dbarψ (s + {μ}) α

@[simp]
lemma shift_dψ (μ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) (α : Fin 2) :
    shift μ (dψ s α) = dψ (s + {μ}) α := rfl

@[simp]
lemma shift_dbarψ (μ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) (α : Fin 2) :
    shift μ (dbarψ s α) = dbarψ (s + {μ}) α := rfl

/-- Appending a derivative index raises the mass weight by two: a derivative has
  mass dimension one. -/
@[simp]
lemma massWeight_shift (μ : Fin 1 ⊕ Fin 3) (j : JetGenerators) :
    (shift μ j).massWeight = j.massWeight + 2 := by
  cases j <;> simp [shift, massWeight] <;> omega

end JetGenerators

/-- The formal total spacetime derivative on the space of component functions of
  the charged-lepton singlet in the direction `μ`: the shift
  `∂_s ψ_α ↦ ∂_{s + {μ}} ψ_α` of the derivative multi-index, and likewise on the
  conjugate components. -/
noncomputable def JetComponentSpace.jetDeriv (μ : Fin 1 ⊕ Fin 3) :
    JetComponentSpace →ₗ[ℂ] JetComponentSpace :=
  JetComponentSpace.basis.constr ℂ fun j =>
    JetComponentSpace.basis (JetGenerators.shift μ j)

@[simp]
lemma JetComponentSpace.jetDeriv_basis (μ : Fin 1 ⊕ Fin 3) (j : JetGenerators) :
    JetComponentSpace.jetDeriv μ (JetComponentSpace.basis j) =
      JetComponentSpace.basis (JetGenerators.shift μ j) := by
  rw [JetComponentSpace.jetDeriv, Module.Basis.constr_basis]

/-- The mass-dimension scaling on the space of component functions of the
  charged-lepton singlet: the diagonal map multiplying each component function
  `∂_s ψ_α` by `c ^ w`, where `w` is twice its mass dimension. -/
noncomputable def JetComponentSpace.massWeightScale (c : ℂ) :
    JetComponentSpace →ₗ[ℂ] JetComponentSpace :=
  JetComponentSpace.basis.constr ℂ fun j =>
    c ^ j.massWeight • JetComponentSpace.basis j

@[simp]
lemma JetComponentSpace.massWeightScale_basis (c : ℂ) (j : JetGenerators) :
    JetComponentSpace.massWeightScale c (JetComponentSpace.basis j) =
      c ^ j.massWeight • JetComponentSpace.basis j := by
  rw [JetComponentSpace.massWeightScale, Module.Basis.constr_basis]

/-- The total derivative raises the mass weight by two on the component space:
  the scaling and the derivative commute up to `c ^ 2`. -/
lemma JetComponentSpace.massWeightScale_jetDeriv (c : ℂ) (μ : Fin 1 ⊕ Fin 3)
    (v : JetComponentSpace) :
    JetComponentSpace.massWeightScale c (JetComponentSpace.jetDeriv μ v) =
      c ^ 2 • JetComponentSpace.jetDeriv μ (JetComponentSpace.massWeightScale c v) := by
  have h : JetComponentSpace.massWeightScale c ∘ₗ JetComponentSpace.jetDeriv μ =
      c ^ 2 • (JetComponentSpace.jetDeriv μ ∘ₗ JetComponentSpace.massWeightScale c) := by
    refine JetComponentSpace.basis.ext fun j => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
      JetComponentSpace.jetDeriv_basis, JetComponentSpace.massWeightScale_basis,
      map_smul, JetGenerators.massWeight_shift, smul_smul, ← pow_add]
    congr 1
    ring
  exact DFunLike.congr_fun h v

/-- The mass-dimension scaling commutes with the action of jets of constant
  gauge transformations on the component space: the constant action is diagonal
  on the generator basis, with no derivative mixing. For a non-constant jet the
  higher Taylor coefficients of `u ^ 6` strictly lower the derivative degree, so
  the action does not commute with the scaling. -/
lemma JetComponentSpace.massWeightScale_repJetGaugeGroupI_ofConstant (c : ℂ) (g : GaugeGroupI) :
    JetComponentSpace.massWeightScale c ∘ₗ
        JetComponentSpace.repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) =
      JetComponentSpace.repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) ∘ₗ
        JetComponentSpace.massWeightScale c := by
  have hu : ((((JetGaugeGroupI.ofConstant g).2.2 : unitary JetRing)) : JetRing) =
      MvPowerSeries.C ((g.2.2 : ℂ)) := rfl
  refine JetComponentSpace.basis.ext fun j => ?_
  cases j with
  | dψ s α =>
    have hrep : JetComponentSpace.repJetGaugeGroupI (JetGaugeGroupI.ofConstant g)
        (JetComponentSpace.basis (.dψ s α)) =
          ((g.2.2 : ℂ) ^ 6) • JetComponentSpace.basis (.dψ s α) := by
      simp only [JetComponentSpace.basis_dψ]
      rw [JetComponentSpace.repJetGaugeGroupI_inl, hu, ← map_pow,
        DerivAlgebraComplex.jetRingAction_C]
      simp [TensorProduct.smul_tmul', Prod.smul_mk]
    simp only [LinearMap.coe_comp, Function.comp_apply, hrep, map_smul,
      JetComponentSpace.massWeightScale_basis]
    exact smul_comm _ _ _
  | dbarψ s α =>
    have hrep : JetComponentSpace.repJetGaugeGroupI (JetGaugeGroupI.ofConstant g)
        (JetComponentSpace.basis (.dbarψ s α)) =
          ((star (g.2.2 : ℂ)) ^ 6) • JetComponentSpace.basis (.dbarψ s α) := by
      simp only [JetComponentSpace.basis_dbarψ]
      rw [JetComponentSpace.repJetGaugeGroupI_inr, hu, JetRing.star_C, ← map_pow,
        DerivAlgebraComplex.jetRingAction_C]
      simp [TensorProduct.smul_tmul', Prod.smul_mk]
    simp only [LinearMap.coe_comp, Function.comp_apply, hrep, map_smul,
      JetComponentSpace.massWeightScale_basis]
    exact smul_comm _ _ _

/-- The mass-dimension scaling commutes with the Lorentz action on the component
  space: the Lorentz action mixes derivative symbols and spinor components only
  within a fixed derivative degree, on which the scaling is a scalar. -/
lemma JetComponentSpace.massWeightScale_repLorentzGroup (c : ℂ) (g : SL(2,ℂ)) :
    JetComponentSpace.massWeightScale c ∘ₗ JetComponentSpace.repLorentzGroup g =
      JetComponentSpace.repLorentzGroup g ∘ₗ JetComponentSpace.massWeightScale c := by
  have hfact : JetComponentSpace.massWeightScale c =
      LinearMap.prodMap
        (TensorProduct.map (DerivAlgebraComplex.gradeScale (c ^ 2)).toLinearMap
          (c ^ 3 • LinearMap.id))
        (TensorProduct.map (DerivAlgebraComplex.gradeScale (c ^ 2)).toLinearMap
          (c ^ 3 • LinearMap.id)) := by
    refine JetComponentSpace.basis.ext fun j => ?_
    cases j with
    | dψ s α =>
      have hscal : (c : ℂ) ^ (JetGenerators.dψ s α).massWeight =
          c ^ 3 * (c ^ 2) ^ s.card := by
        show c ^ (3 + 2 * s.card) = _
        ring
      rw [JetComponentSpace.massWeightScale_basis, hscal]
      simp only [JetComponentSpace.basis_dψ, LinearMap.prodMap_apply, map_zero,
        TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.smul_apply,
        LinearMap.id_apply, DerivAlgebraComplex.gradeScale_basis,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul', Prod.smul_mk, smul_smul,
        smul_zero]
    | dbarψ s α =>
      have hscal : (c : ℂ) ^ (JetGenerators.dbarψ s α).massWeight =
          c ^ 3 * (c ^ 2) ^ s.card := by
        show c ^ (3 + 2 * s.card) = _
        ring
      rw [JetComponentSpace.massWeightScale_basis, hscal]
      simp only [JetComponentSpace.basis_dbarψ, LinearMap.prodMap_apply, map_zero,
        TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.smul_apply,
        LinearMap.id_apply, DerivAlgebraComplex.gradeScale_basis,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul', Prod.smul_mk, smul_smul,
        smul_zero]
  have hA : (DerivAlgebraComplex.gradeScale (c ^ 2)).toLinearMap ∘ₗ
      DerivAlgebraComplex.repLorentzGroup g =
      (DerivAlgebraComplex.repLorentzGroup g :
        DerivAlgebraComplex →ₗ[ℂ] DerivAlgebraComplex) ∘ₗ
        (DerivAlgebraComplex.gradeScale (c ^ 2)).toLinearMap :=
    LinearMap.ext fun a => DerivAlgebraComplex.gradeScale_repLorentzGroup (c ^ 2) g a
  have hB1 : (c ^ 3 • (LinearMap.id : Module.End ℂ (Module.Dual ℂ LeptonSinglet))) ∘ₗ
      LeptonSinglet.repLorentzGroup.dual g =
      LeptonSinglet.repLorentzGroup.dual g ∘ₗ (c ^ 3 • LinearMap.id) := by
    rw [LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.id_comp, LinearMap.comp_id]
  have hB2 : (c ^ 3 • (LinearMap.id :
      Module.End ℂ (Module.Dual ℂ (ConjModule LeptonSinglet)))) ∘ₗ
      LeptonSinglet.repLorentzGroup.conj.dual g =
      LeptonSinglet.repLorentzGroup.conj.dual g ∘ₗ (c ^ 3 • LinearMap.id) := by
    rw [LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.id_comp, LinearMap.comp_id]
  have hcomp1 : TensorProduct.map (DerivAlgebraComplex.gradeScale (c ^ 2)).toLinearMap
      (c ^ 3 • LinearMap.id) ∘ₗ
      TensorProduct.map (DerivAlgebraComplex.repLorentzGroup g)
        (LeptonSinglet.repLorentzGroup.dual g) =
      TensorProduct.map (DerivAlgebraComplex.repLorentzGroup g)
        (LeptonSinglet.repLorentzGroup.dual g) ∘ₗ
      TensorProduct.map (DerivAlgebraComplex.gradeScale (c ^ 2)).toLinearMap
        (c ^ 3 • LinearMap.id) := by
    rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, hA, hB1]
  have hcomp2 : TensorProduct.map (DerivAlgebraComplex.gradeScale (c ^ 2)).toLinearMap
      (c ^ 3 • LinearMap.id) ∘ₗ
      TensorProduct.map (DerivAlgebraComplex.repLorentzGroup g)
        (LeptonSinglet.repLorentzGroup.conj.dual g) =
      TensorProduct.map (DerivAlgebraComplex.repLorentzGroup g)
        (LeptonSinglet.repLorentzGroup.conj.dual g) ∘ₗ
      TensorProduct.map (DerivAlgebraComplex.gradeScale (c ^ 2)).toLinearMap
        (c ^ 3 • LinearMap.id) := by
    rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, hA, hB2]
  rw [hfact, show JetComponentSpace.repLorentzGroup g =
      LinearMap.prodMap
        (TensorProduct.map (DerivAlgebraComplex.repLorentzGroup g)
          (LeptonSinglet.repLorentzGroup.dual g))
        (TensorProduct.map (DerivAlgebraComplex.repLorentzGroup g)
          (LeptonSinglet.repLorentzGroup.conj.dual g)) from rfl]
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.prodMap_apply]
  exact Prod.ext (DFunLike.congr_fun hcomp1 x.1) (DFunLike.congr_fun hcomp2 x.2)

/-- The total derivative preserves the unconjugated half of the component space,
  acting there by the shift of dual derivative symbols. -/
lemma JetComponentSpace.jetDeriv_inl (μ : Fin 1 ⊕ Fin 3)
    (a : SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule))
    (φ : Module.Dual ℂ LeptonSinglet) :
    JetComponentSpace.jetDeriv μ ((a ⊗ₜ[ℂ] φ, 0) : JetComponentSpace) =
      ((DerivAlgebraComplex.deriv μ a) ⊗ₜ[ℂ] φ, 0) := by
  have h : (JetComponentSpace.jetDeriv μ) ∘ₗ (LinearMap.inl ℂ
        (SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ]
          Module.Dual ℂ LeptonSinglet)
        (SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ]
          Module.Dual ℂ (ConjModule LeptonSinglet))) =
      (LinearMap.inl ℂ _ _) ∘ₗ (TensorProduct.map (DerivAlgebraComplex.deriv μ) LinearMap.id) := by
    refine (DerivAlgebraComplex.basis.tensorProduct LeptonSinglet.basis.dualBasis).ext
      fun p => ?_
    obtain ⟨s, α⟩ := p
    rw [Module.Basis.tensorProduct_apply']
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.inl_apply,
      TensorProduct.map_tmul, LinearMap.id_coe, id_eq]
    rw [show ((DerivAlgebraComplex.basis s ⊗ₜ[ℂ] LeptonSinglet.basis.dualBasis α, 0) :
        JetComponentSpace) = JetComponentSpace.basis (.dψ s α) from
        (JetComponentSpace.basis_dψ s α).symm,
      JetComponentSpace.jetDeriv_basis, JetGenerators.shift_dψ,
      JetComponentSpace.basis_dψ, DerivAlgebraComplex.deriv_basis_multiset]
  have h1 := LinearMap.congr_fun h (a ⊗ₜ[ℂ] φ)
  simpa using h1

/-- The total derivative on a general element of the unconjugated half of the
  component space. -/
lemma JetComponentSpace.jetDeriv_inl' (μ : Fin 1 ⊕ Fin 3)
    (y : SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ]
      Module.Dual ℂ LeptonSinglet) :
    JetComponentSpace.jetDeriv μ ((y, 0) : JetComponentSpace) =
      ((TensorProduct.map (DerivAlgebraComplex.deriv μ) LinearMap.id) y, 0) := by
  induction y using TensorProduct.induction_on with
  | zero =>
    rw [show ((0, 0) : JetComponentSpace) = 0 from rfl, map_zero, map_zero]
    rfl
  | add a b ha hb =>
    have hpair : ((a + b, 0) : JetComponentSpace) = (a, 0) + (b, 0) := by
      simp
    rw [hpair, map_add, ha, hb, map_add]
    simp
  | tmul a φ =>
    rw [JetComponentSpace.jetDeriv_inl, TensorProduct.map_tmul]
    rfl

/-- The total derivative preserves the conjugated half of the component space,
  acting there by the shift of dual derivative symbols. -/
lemma JetComponentSpace.jetDeriv_inr (μ : Fin 1 ⊕ Fin 3)
    (a : SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule))
    (φ : Module.Dual ℂ (ConjModule LeptonSinglet)) :
    JetComponentSpace.jetDeriv μ ((0, a ⊗ₜ[ℂ] φ) : JetComponentSpace) =
      (0, (DerivAlgebraComplex.deriv μ a) ⊗ₜ[ℂ] φ) := by
  have h : (JetComponentSpace.jetDeriv μ) ∘ₗ (LinearMap.inr ℂ
        (SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ]
          Module.Dual ℂ LeptonSinglet)
        (SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ]
          Module.Dual ℂ (ConjModule LeptonSinglet))) =
      (LinearMap.inr ℂ _ _) ∘ₗ (TensorProduct.map (DerivAlgebraComplex.deriv μ)
        LinearMap.id) := by
    refine (DerivAlgebraComplex.basis.tensorProduct
      (LeptonSinglet.basis.conj.dualBasis)).ext fun p => ?_
    obtain ⟨s, α⟩ := p
    rw [Module.Basis.tensorProduct_apply']
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.inr_apply,
      TensorProduct.map_tmul, LinearMap.id_coe, id_eq]
    rw [show ((0, DerivAlgebraComplex.basis s ⊗ₜ[ℂ]
        LeptonSinglet.basis.conj.dualBasis α) : JetComponentSpace) =
        JetComponentSpace.basis (.dbarψ s α) from
        (JetComponentSpace.basis_dbarψ s α).symm,
      JetComponentSpace.jetDeriv_basis, JetGenerators.shift_dbarψ,
      JetComponentSpace.basis_dbarψ, DerivAlgebraComplex.deriv_basis_multiset]
  have h1 := LinearMap.congr_fun h (a ⊗ₜ[ℂ] φ)
  simpa using h1

/-- The total derivative on a general element of the conjugated half of the
  component space. -/
lemma JetComponentSpace.jetDeriv_inr' (μ : Fin 1 ⊕ Fin 3)
    (y : SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ]
      Module.Dual ℂ (ConjModule LeptonSinglet)) :
    JetComponentSpace.jetDeriv μ ((0, y) : JetComponentSpace) =
      (0, (TensorProduct.map (DerivAlgebraComplex.deriv μ) LinearMap.id) y) := by
  induction y using TensorProduct.induction_on with
  | zero =>
    rw [show ((0, 0) : JetComponentSpace) = 0 from rfl, map_zero, map_zero]
    rfl
  | add a b ha hb =>
    have hpair : ((0, a + b) : JetComponentSpace) = (0, a) + (0, b) := by
      simp
    rw [hpair, map_add, ha, hb, map_add]
    simp
  | tmul a φ =>
    rw [JetComponentSpace.jetDeriv_inr, TensorProduct.map_tmul]
    rfl

/-!

## A. The jet algebra

-/


abbrev JetAlgebra : Type := ExteriorAlgebra ℂ JetComponentSpace

namespace JetAlgebra


/-!

### A.1. The generators of the jet algebra

-/

noncomputable def ofGenerator (j : JetGenerators) : JetAlgebra :=
  ExteriorAlgebra.ι ℂ (JetComponentSpace.basis j)


/-!

### A.2. The action of the jet gauge group.

-/

/-- The action of the (jet) gauge group on the jet algebra of the lepton singlets. -/
noncomputable def repJetGaugeGroupI : Representation ℂ JetGaugeGroupI JetAlgebra where
  toFun g := (ExteriorAlgebra.map (JetComponentSpace.repJetGaugeGroupI g)).toLinearMap
  map_one' := by
    simp only [map_one, Module.End.one_eq_id, ExteriorAlgebra.map_id,
      AlgHom.toLinearMap_id]
  map_mul' g1 g2 := by
    simp only [map_mul, Module.End.mul_eq_comp, ← ExteriorAlgebra.map_comp_map,
      AlgHom.comp_toLinearMap]

lemma repJetGaugeGroupI_apply (g : JetGaugeGroupI) (x : JetAlgebra) :
    repJetGaugeGroupI g x =
      ExteriorAlgebra.map (JetComponentSpace.repJetGaugeGroupI g) x := rfl

/-- The value of the jet of gauge transformations at the base point acts by the
  contragredient hypercharge scalar on the zeroth-order singlet generator, with
  no derivative contributions. -/
lemma repJetGaugeGroupI_ofGenerator_ψ_nil (g : JetGaugeGroupI) (α : Fin 2) :
    repJetGaugeGroupI g (ofGenerator (.dψ {} α)) =  g.eval.2.2 ^ 6 • ofGenerator (.dψ {} α) := by
  rw [ofGenerator, repJetGaugeGroupI_apply, ExteriorAlgebra.map_apply_ι,
    JetComponentSpace.basis_dψ_nil, Submonoid.smul_def]
  simp only [JetComponentSpace.repJetGaugeGroupI, Representation.prod_apply_apply,
    Representation.tprod_apply, dualJetAlgebraRepJetGaugeGroupI_apply,
    Representation.trivial_apply, map_zero, TensorProduct.map_tmul,
    DerivAlgebraComplex.jetRingAction_apply_one, map_pow, ← TensorProduct.smul_tmul',
    SubmonoidClass.coe_pow, ← map_smul, Prod.smul_mk, smul_zero]
  rfl


/-- The action of the gauge group on ∂_μ ψ takes it to
  g • (∂_μ ψ + 6 i (maurerCartanU1Coeff g μ 0) • ψ)-/
lemma repJetGaugeGroupI_ofGenerator_ψ_singleton (g : JetGaugeGroupI)
      (μ : (Fin 1 ⊕ Fin 3)) (α : Fin 2) :
    repJetGaugeGroupI g (ofGenerator (.dψ {μ} α)) =
      g.eval.2.2 ^ 6 • ofGenerator (.dψ {μ} α) -
        ((6 : ℂ) * Complex.I * (maurerCartanU1Coeff g μ 0 : ℂ) * (g.eval.2.2 : ℂ) ^ 6) •
          ofGenerator (.dψ {} α) := by
  have hval : ((g.eval.2.2 : unitary ℂ) : ℂ) =
      MvPowerSeries.constantCoeff ((g.2.2 : unitary JetRing) : JetRing) := rfl
  have hcoeff : MvPowerSeries.coeff (Finsupp.single μ 1)
      (((g.2.2 : unitary JetRing) : JetRing) ^ 6) =
      -((6 : ℂ) * Complex.I * (maurerCartanU1Coeff g μ 0 : ℂ) *
        MvPowerSeries.constantCoeff ((g.2.2 : unitary JetRing) : JetRing) ^ 6) := by
    have h := congrArg (MvPowerSeries.coeff (0 : (Fin 1 ⊕ Fin 3) →₀ ℕ))
      (BBoson.pderiv_pow_unitary g μ 6)
    rw [MvPowerSeries.coeff_pderiv] at h
    simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, map_pow,
      MvPowerSeries.constantCoeff_C, Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero,
      zero_add, mul_one] at h
    rw [show ((maurerCartanU1Coeff g μ 0 : selfAdjoint ℂ) : ℂ) =
        MvPowerSeries.constantCoeff (maurerCartanU1 g μ) from
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply _, h]
    push_cast
    ring
  have hinl : ∀ x : SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ]
      Module.Dual ℂ LeptonSinglet,
      (x, (0 : SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ]
        Module.Dual ℂ (ConjModule LeptonSinglet))) =
      LinearMap.inl ℂ _ _ x := fun x => rfl
  simp only [ofGenerator, repJetGaugeGroupI_apply, ExteriorAlgebra.map_apply_ι,
    JetComponentSpace.basis_dψ_singleton, JetComponentSpace.basis_dψ_nil,
    JetComponentSpace.repJetGaugeGroupI, Representation.prod_apply_apply,
    Representation.tprod_apply, dualJetAlgebraRepJetGaugeGroupI_apply,
    Representation.trivial_apply, map_zero, TensorProduct.map_tmul,
    DerivAlgebraComplex.jetRingAction_apply_ι, hcoeff, TensorProduct.add_tmul,
    ← TensorProduct.smul_tmul', Submonoid.smul_def, SubmonoidClass.coe_pow,
    hval, map_pow, sub_eq_add_neg, neg_smul]
  simp only [hinl, TensorProduct.neg_tmul, ← TensorProduct.smul_tmul',
    map_add, map_neg, map_smul]

/-- The jet gauge action on a general singlet generator: the all-orders Leibniz
  rule. A jet of gauge transformations acts on the derivative generator
  `∂_s ψ_α` through the Taylor coefficients of its contragredient hypercharge
  power series `u ^ 6`: each splitting `s = p.1 + p.2` contributes the `p.1`-th
  Taylor coefficient, with the divided-power multiplicity, times the lower
  generator `∂_{p.2} ψ_α`. The zeroth- and first-order cases are
  `repJetGaugeGroupI_ofGenerator_ψ_nil` and
  `repJetGaugeGroupI_ofGenerator_ψ_singleton`. -/
lemma repJetGaugeGroupI_ofGenerator_ψ (g : JetGaugeGroupI)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (α : Fin 2) :
    repJetGaugeGroupI g (ofGenerator (.dψ s α)) =
      ∑ p ∈ Finset.antidiagonal (Multiset.toFinsupp s),
        ((∏ μ, (Multiset.toFinsupp s μ).descFactorial (p.1 μ) : ℕ) : ℂ) •
          MvPowerSeries.coeff p.1 (((g.2.2 : unitary JetRing) : JetRing) ^ 6) •
            ofGenerator (.dψ (Finsupp.toMultiset p.2) α) := by
  have hinl : ∀ x : SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ]
      Module.Dual ℂ LeptonSinglet,
      (x, (0 : SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ]
        Module.Dual ℂ (ConjModule LeptonSinglet))) =
      LinearMap.inl ℂ _ _ x := fun x => rfl
  simp only [ofGenerator, repJetGaugeGroupI_apply, ExteriorAlgebra.map_apply_ι,
    JetComponentSpace.basis_dψ, DerivAlgebraComplex.basis_apply, Finsupp.toMultiset_toFinsupp,
    JetComponentSpace.repJetGaugeGroupI, Representation.prod_apply_apply,
    Representation.tprod_apply, dualJetAlgebraRepJetGaugeGroupI_apply,
    Representation.trivial_apply, map_zero, TensorProduct.map_tmul,
    DerivAlgebraComplex.jetRingAction_basis]
  simp only [hinl, TensorProduct.sum_tmul, ← TensorProduct.smul_tmul', map_sum, map_smul]

/-!

### A.3. The action of the Lorentz group

-/

noncomputable def repLorentzGroup : Representation ℂ SL(2,ℂ) JetAlgebra where
  toFun g := (ExteriorAlgebra.map (JetComponentSpace.repLorentzGroup g)).toLinearMap
  map_one' := by
    simp only [map_one, Module.End.one_eq_id, ExteriorAlgebra.map_id,
      AlgHom.toLinearMap_id]
  map_mul' g1 g2 := by
    simp only [map_mul, Module.End.mul_eq_comp, ← ExteriorAlgebra.map_comp_map,
      AlgHom.comp_toLinearMap]

lemma repLorentzGroup_apply (g : SL(2,ℂ)) (x : JetAlgebra) :
    repLorentzGroup g x =
      ExteriorAlgebra.map (JetComponentSpace.repLorentzGroup g) x := rfl

lemma repLorentzGroup_apply_one (g : SL(2,ℂ)) :
    repLorentzGroup g 1 = 1 := by simp [repLorentzGroup_apply]

lemma repLorentzGroup_apply_mul (g : SL(2,ℂ)) (x y : JetAlgebra) :
    repLorentzGroup g (x * y) = repLorentzGroup g x * repLorentzGroup g y := by
  simp [repLorentzGroup_apply]

/-- The Lorentz action on a jet-algebra generator. -/
lemma repLorentzGroup_ofGenerator (Λ : SL(2,ℂ)) (j : JetGenerators) :
    repLorentzGroup Λ (ofGenerator j) =
      ExteriorAlgebra.ι ℂ
        (JetComponentSpace.repLorentzGroup Λ (JetComponentSpace.basis j)) := by
  rw [ofGenerator, repLorentzGroup_apply, ExteriorAlgebra.map_apply_ι]

/-- The Lorentz action on the zeroth-order lepton generator. -/
lemma repLorentzGroup_ofGenerator_ψ_nil (Λ : SL(2,ℂ)) (α : Fin 2) :
    repLorentzGroup Λ (ofGenerator (.dψ {} α)) =
      ∑ β, star ((Λ⁻¹).1 α β) • ofGenerator (.dψ {} β) := by
  rw [repLorentzGroup_ofGenerator,
    JetComponentSpace.repLorentzGroup_basis_dψ_nil, map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_smul, ofGenerator]

/-- The Lorentz action on the first-order lepton generator. -/
lemma repLorentzGroup_ofGenerator_ψ_singleton (Λ : SL(2,ℂ))
    (μ : Fin 1 ⊕ Fin 3) (α : Fin 2) :
    repLorentzGroup Λ (ofGenerator (.dψ {μ} α)) =
      ∑ ν, ∑ β, ((((Lorentz.SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) *
        star ((Λ⁻¹).1 α β)) • ofGenerator (.dψ {ν} β) := by
  rw [repLorentzGroup_ofGenerator,
    JetComponentSpace.repLorentzGroup_basis_dψ_singleton, map_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_smul, ofGenerator]

/-- The Lorentz action on the zeroth-order conjugate lepton generator. -/
lemma repLorentzGroup_ofGenerator_barψ_nil (Λ : SL(2,ℂ)) (α : Fin 2) :
    repLorentzGroup Λ (ofGenerator (.dbarψ {} α)) =
      ∑ β, (Λ⁻¹).1 α β • ofGenerator (.dbarψ {} β) := by
  rw [repLorentzGroup_ofGenerator,
    JetComponentSpace.repLorentzGroup_basis_dbarψ_nil, map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_smul, ofGenerator]

/-- The Lorentz action on the first-order conjugate lepton generator. -/
lemma repLorentzGroup_ofGenerator_barψ_singleton (Λ : SL(2,ℂ))
    (μ : Fin 1 ⊕ Fin 3) (α : Fin 2) :
    repLorentzGroup Λ (ofGenerator (.dbarψ {μ} α)) =
      ∑ ν, ∑ β, ((((Lorentz.SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) *
        (Λ⁻¹).1 α β) • ofGenerator (.dbarψ {ν} β) := by
  rw [repLorentzGroup_ofGenerator,
    JetComponentSpace.repLorentzGroup_basis_dbarψ_singleton, map_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_smul, ofGenerator]


noncomputable def repLorentzGroupAlgHom (Λ : SL(2,ℂ)) :
    AlgHom ℂ JetAlgebra JetAlgebra where
  toFun := repLorentzGroup Λ
  map_add' := LinearMap.map_add _
  map_zero' := LinearMap.map_zero _
  map_one' := repLorentzGroup_apply_one Λ
  map_mul' := repLorentzGroup_apply_mul Λ
  commutes' r := by simp [repLorentzGroup_apply]


/-!

### A.4. The formal total derivative on the jet algebra

The formal total spacetime derivative extends from the component functions to
the whole jet algebra as an even derivation:
`∂_μ (x y) = (∂_μ x) y + x (∂_μ y)`, with no Koszul signs. It is constructed by
lifting the generator map `ι x ↦ (ι x, ι (∂_μ x))` to an algebra homomorphism
into the trivial square-zero extension of the jet algebra; the square-zero
condition holds because degree-one elements of the exterior algebra
anticommute.

-/

/-- The generator map of the total derivative into the trivial square-zero
  extension of the jet algebra: `ι x ↦ (ι x, ι (∂_μ x))`. -/
noncomputable def jetDerivGen (μ : Fin 1 ⊕ Fin 3) :
    JetComponentSpace →ₗ[ℂ] TrivSqZeroExt JetAlgebra JetAlgebra where
  toFun x := (ExteriorAlgebra.ι ℂ x,
    ExteriorAlgebra.ι ℂ (JetComponentSpace.jetDeriv μ x))
  map_add' x y := by
    simp only [map_add]
    rfl
  map_smul' c x := by
    simp only [map_smul, RingHom.id_apply]
    rfl

@[simp]
lemma jetDerivGen_fst (μ : Fin 1 ⊕ Fin 3) (x : JetComponentSpace) :
    (jetDerivGen μ x).fst = ExteriorAlgebra.ι ℂ x := rfl

@[simp]
lemma jetDerivGen_snd (μ : Fin 1 ⊕ Fin 3) (x : JetComponentSpace) :
    (jetDerivGen μ x).snd = ExteriorAlgebra.ι ℂ (JetComponentSpace.jetDeriv μ x) := rfl

/-- The generator map squares to zero: degree-one elements of the exterior
  algebra anticommute. -/
lemma jetDerivGen_mul_self (μ : Fin 1 ⊕ Fin 3) (x : JetComponentSpace) :
    jetDerivGen μ x * jetDerivGen μ x = 0 := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [TrivSqZeroExt.fst_mul, jetDerivGen_fst, ExteriorAlgebra.ι_sq_zero,
      TrivSqZeroExt.fst_zero]
  · rw [TrivSqZeroExt.snd_mul, jetDerivGen_fst, jetDerivGen_snd, TrivSqZeroExt.snd_zero,
      smul_eq_mul, op_smul_eq_mul]
    exact ExteriorAlgebra.ι_add_mul_swap x (JetComponentSpace.jetDeriv μ x)

/-- The lift of the total derivative to the trivial square-zero extension of the
  jet algebra: the algebra homomorphism `x ↦ (x, ∂_μ x)`. -/
noncomputable def jetDerivHom (μ : Fin 1 ⊕ Fin 3) :
    JetAlgebra →ₐ[ℂ] TrivSqZeroExt JetAlgebra JetAlgebra :=
  ExteriorAlgebra.lift ℂ ⟨jetDerivGen μ, jetDerivGen_mul_self μ⟩

@[simp]
lemma jetDerivHom_ι (μ : Fin 1 ⊕ Fin 3) (x : JetComponentSpace) :
    jetDerivHom μ (ExteriorAlgebra.ι ℂ x) = jetDerivGen μ x := by
  rw [jetDerivHom, ExteriorAlgebra.lift_ι_apply]

/-- The first component of the square-zero lift is the identity. -/
@[simp]
lemma jetDerivHom_fst (μ : Fin 1 ⊕ Fin 3) (x : JetAlgebra) :
    (jetDerivHom μ x).fst = x := by
  have h : (TrivSqZeroExt.fstHom ℂ JetAlgebra JetAlgebra).comp (jetDerivHom μ) =
      AlgHom.id ℂ JetAlgebra := by
    refine ExteriorAlgebra.hom_ext (LinearMap.ext fun v => ?_)
    simp
  exact DFunLike.congr_fun h x

/-- The formal total spacetime derivative on the jet algebra of the
  charged-lepton singlet in the direction `μ`: the even derivation extending the
  shift `∂_s ψ_α ↦ ∂_{s + {μ}} ψ_α` of the component functions. -/
noncomputable def jetDeriv (μ : Fin 1 ⊕ Fin 3) : JetAlgebra →ₗ[ℂ] JetAlgebra where
  toFun x := (jetDerivHom μ x).snd
  map_add' x y := congrArg TrivSqZeroExt.snd (map_add (jetDerivHom μ) x y)
  map_smul' c x := congrArg TrivSqZeroExt.snd (map_smul (jetDerivHom μ) c x)

lemma jetDeriv_apply (μ : Fin 1 ⊕ Fin 3) (x : JetAlgebra) :
    jetDeriv μ x = (jetDerivHom μ x).snd := rfl

@[simp]
lemma jetDeriv_ι (μ : Fin 1 ⊕ Fin 3) (x : JetComponentSpace) :
    jetDeriv μ (ExteriorAlgebra.ι ℂ x) =
      ExteriorAlgebra.ι ℂ (JetComponentSpace.jetDeriv μ x) := by
  rw [jetDeriv_apply, jetDerivHom_ι, jetDerivGen_snd]

/-- The total derivative appends the derivative index to each component
  function. -/
@[simp]
lemma jetDeriv_ofGenerator (μ : Fin 1 ⊕ Fin 3) (j : JetGenerators) :
    jetDeriv μ (ofGenerator j) = ofGenerator (JetGenerators.shift μ j) := by
  rw [ofGenerator, jetDeriv_ι, JetComponentSpace.jetDeriv_basis]
  rfl

@[simp]
lemma jetDeriv_one (μ : Fin 1 ⊕ Fin 3) : jetDeriv μ (1 : JetAlgebra) = 0 :=
  congrArg TrivSqZeroExt.snd (map_one (jetDerivHom μ))

/-- The total derivative is an even derivation: the Leibniz rule holds on the
  jet algebra with no Koszul signs. -/
lemma jetDeriv_mul (μ : Fin 1 ⊕ Fin 3) (x y : JetAlgebra) :
    jetDeriv μ (x * y) = jetDeriv μ x * y + x * jetDeriv μ y := by
  have h : jetDeriv μ (x * y) =
      (jetDerivHom μ x).fst * jetDeriv μ y + jetDeriv μ x * (jetDerivHom μ y).fst :=
    congrArg TrivSqZeroExt.snd (map_mul (jetDerivHom μ) x y)
  rw [jetDerivHom_fst, jetDerivHom_fst] at h
  exact h.trans (add_comm _ _)

/-!

### A.5. The mass-weight scaling on the jet algebra

-/

/-- The mass-dimension scaling on the jet algebra of the charged-lepton singlet:
  the (linear map underlying the) algebra map multiplying each generator by
  `c ^ w`, where `w` is twice its mass dimension. -/
noncomputable def massWeightScale (c : ℂ) : JetAlgebra →ₐ[ℂ] JetAlgebra :=
  (ExteriorAlgebra.map (JetComponentSpace.massWeightScale c))

lemma massWeightScale_apply (c : ℂ) (x : JetAlgebra) :
    massWeightScale c x =
      ExteriorAlgebra.map (JetComponentSpace.massWeightScale c) x := rfl

/-- Each generator scales by `c` to the power of its mass weight. -/
@[simp]
lemma massWeightScale_ofGenerator (c : ℂ) (j : JetGenerators) :
    massWeightScale c (ofGenerator j) = c ^ j.massWeight • ofGenerator j := by
  rw [ofGenerator, massWeightScale_apply, ExteriorAlgebra.map_apply_ι,
    JetComponentSpace.massWeightScale_basis, map_smul]

@[simp]
lemma massWeightScale_ι (c : ℂ) (v : JetComponentSpace) :
    massWeightScale c (ExteriorAlgebra.ι ℂ v) =
      ExteriorAlgebra.ι ℂ (JetComponentSpace.massWeightScale c v) := by
  rw [massWeightScale_apply, ExteriorAlgebra.map_apply_ι]

set_option maxHeartbeats 1000000 in
/-- The total derivative raises the mass weight by two: the scaling and the
  derivative commute up to `c ^ 2`. -/
lemma massWeightScale_jetDeriv (c : ℂ) (μ : Fin 1 ⊕ Fin 3) (x : JetAlgebra) :
    massWeightScale c (jetDeriv μ x) = c ^ 2 • jetDeriv μ (massWeightScale c x) := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap r =>
    simp [Algebra.algebraMap_eq_smul_one]
  | ι v =>
    rw [jetDeriv_ι, massWeightScale_ι, JetComponentSpace.massWeightScale_jetDeriv,
      map_smul, massWeightScale_ι, jetDeriv_ι]
  | mul x y hx hy =>
    have hm : ∀ a b : JetAlgebra, massWeightScale c (a * b) =
        massWeightScale c a * massWeightScale c b := fun a b => map_mul _ a b
    rw [jetDeriv_mul, map_add, hm, hm, hm, hx, hy, smul_mul_assoc, mul_smul_comm,
      jetDeriv_mul, smul_add]
  | add x y hx hy =>
    simp only [map_add, hx, hy, smul_add]

/-- The mass-dimension scaling commutes with the gauge action of jets of
  constant gauge transformations. This fails for a general jet: the gauge action
  sends `∂ψ` to `u(0)⁶ ∂ψ + (∂u⁶)(0) ψ + …`, mixing derivative degrees
  downwards, while the scaling weights each degree differently, so the two
  compositions already differ on first-derivative generators. -/
lemma massWeightScale_repJetGaugeGroupI_ofConstant (c : ℂ) (g : GaugeGroupI) :
    massWeightScale c ∘ₗ JetAlgebra.repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) =
      JetAlgebra.repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) ∘ₗ massWeightScale c := by
  have h : (massWeightScale c).comp
      (ExteriorAlgebra.map (JetComponentSpace.repJetGaugeGroupI
        (JetGaugeGroupI.ofConstant g))) =
      (ExteriorAlgebra.map (JetComponentSpace.repJetGaugeGroupI
        (JetGaugeGroupI.ofConstant g))).comp (massWeightScale c) := by
    rw [massWeightScale, ExteriorAlgebra.map_comp_map, ExteriorAlgebra.map_comp_map,
      JetComponentSpace.massWeightScale_repJetGaugeGroupI_ofConstant]
  have h2 := congrArg AlgHom.toLinearMap h
  rw [AlgHom.comp_toLinearMap, AlgHom.comp_toLinearMap] at h2
  exact h2

lemma massWeightScale_repLorentzGroup (c : ℂ) (g : SL(2,ℂ)) :
    massWeightScale c ∘ₗ JetAlgebra.repLorentzGroup g =
      JetAlgebra.repLorentzGroup g ∘ₗ massWeightScale c := by
  have h : (massWeightScale c).comp
      (ExteriorAlgebra.map (JetComponentSpace.repLorentzGroup g)) =
      (ExteriorAlgebra.map (JetComponentSpace.repLorentzGroup g)).comp
        (massWeightScale c) := by
    rw [massWeightScale, ExteriorAlgebra.map_comp_map, ExteriorAlgebra.map_comp_map,
      JetComponentSpace.massWeightScale_repLorentzGroup]
  have h2 := congrArg AlgHom.toLinearMap h
  rw [AlgHom.comp_toLinearMap, AlgHom.comp_toLinearMap] at h2
  exact h2
end JetAlgebra

end LeptonSinglet

end StandardModel
