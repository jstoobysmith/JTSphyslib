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

noncomputable def JetComponentSpace.repLorentzGroup :
    Representation ℂ (SL(2,ℂ)) JetComponentSpace :=
  (DerivAlgebraComplex.repLorentzGroup.tprod LeptonSinglet.repLorentzGroup.dual).prod
  (DerivAlgebraComplex.repLorentzGroup.tprod LeptonSinglet.repLorentzGroup.conj.dual)

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

/-!

## The jet algebra

-/


abbrev JetAlgebra : Type := ExteriorAlgebra ℂ JetComponentSpace

namespace JetAlgebra

/-- The action of the (jet) gauge group on the jet algebra of the lepton singlets. -/
noncomputable def repJetGaugeGroupI : Representation ℂ JetGaugeGroupI JetAlgebra where
  toFun g := (ExteriorAlgebra.map (JetComponentSpace.repJetGaugeGroupI g)).toLinearMap
  map_one' := by
    simp only [map_one, Module.End.one_eq_id, ExteriorAlgebra.map_id,
      AlgHom.toLinearMap_id]
  map_mul' g1 g2 := by
    simp only [map_mul, Module.End.mul_eq_comp, ← ExteriorAlgebra.map_comp_map,
      AlgHom.comp_toLinearMap]

noncomputable def ofGenerator (j : JetGenerators) : JetAlgebra :=
  ExteriorAlgebra.ι ℂ (JetComponentSpace.basis j)

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

## The formal total derivative on the jet algebra

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

end JetAlgebra

end LeptonSinglet

end StandardModel
