/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Jinzheng Li, Nathaneal Sajan
-/
module

public import Physlib.Relativity.Fermions.Weyl.Metric
public import Physlib.Particles.StandardModel.Fermions.QuarkDoublet
public import Physlib.Particles.StandardModel.Fermions.DownSinglet
public import Physlib.Particles.StandardModel.Fermions.LeptonDoublet
public import Physlib.Particles.StandardModel.Fermions.LeptonSinglet
public import Physlib.Particles.StandardModel.Fermions.UpSinglet
public import Physlib.Particles.StandardModel.HiggsBoson.Basic
public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Physlib.Mathematics.ConjModule
public import Physlib.Mathematics.MultisetsOfMassDim
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.TensorAlgebra.Basis
public import Physlib.Relativity.Tensors.ComplexTensor.Vector.Pre.Basic
/-!

# The Standard Model EFT Lagrangian without derivatives

## i. Overview

-/

@[expose] public section

/-!

## The basic type for a lagrangian theory

-/
open Matrix MatrixGroups Module TensorProduct

structure LagrangianTheory (G : Type) [Group G] where
  -- The fermions
  FermionIrreps : Type
  [fermionIrreps_fintype : Fintype FermionIrreps]
  [fermionIrreps_decEq : DecidableEq FermionIrreps]
  FermionComponents : FermionIrreps → Type
  [fermionComponents_fintype : ∀ φ, Fintype (FermionComponents φ)]
  [fermionComponents_decEq : ∀ φ, DecidableEq (FermionComponents φ)]
  fermionModule : ∀ (_ : FermionIrreps), Type
  [fermionModule_addCommGroup : ∀ φ, AddCommGroup (fermionModule φ)]
  [fermionModule_module : ∀ φ, Module ℂ (fermionModule φ)]
  fermionBasis : ∀ φ, Basis (FermionComponents φ) ℂ (fermionModule φ)
  fermionRepLorentzGroup : ∀ φ, Representation ℂ SL(2,ℂ) (fermionModule φ)
  fermionRepGaugeGroup : ∀ φ, Representation ℂ G (fermionModule φ)
  -- The complex scalars
  ComplexScalarIrreps : Type
  [complexScalarIrreps_fintype : Fintype ComplexScalarIrreps]
  [complexScalarIrreps_decEq : DecidableEq ComplexScalarIrreps]
  ComplexScalarComponents : ComplexScalarIrreps → Type
  [complexScalarComponents_fintype : ∀ φ, Fintype (ComplexScalarComponents φ)]
  [complexScalarComponents_decEq : ∀ φ, DecidableEq (ComplexScalarComponents φ)]
  complexScalarModule : ∀ (_ : ComplexScalarIrreps), Type
  [complexScalarModule_addCommGroup : ∀ φ, AddCommGroup (complexScalarModule φ)]
  [complexScalarModule_module : ∀ φ, Module ℂ (complexScalarModule φ)]
  complexScalarBasis : ∀ φ, Basis (ComplexScalarComponents φ) ℂ (complexScalarModule φ)
  complexScalarRepLorentzGroup : ∀ φ, Representation ℂ SL(2,ℂ) (complexScalarModule φ)
  complexScalarRepGaugeGroup : ∀ φ, Representation ℂ G (complexScalarModule φ)
  -- The real bosonic fields (e.g. the field strengths of the gauge bosons)
  RealBosonIrreps : Type
  [realBosonIrreps_fintype : Fintype RealBosonIrreps]
  [realBosonIrreps_decEq : DecidableEq RealBosonIrreps]
  RealBosonComponents : RealBosonIrreps → Type
  [realBosonComponents_fintype : ∀ φ, Fintype (RealBosonComponents φ)]
  [realBosonComponents_decEq : ∀ φ, DecidableEq (RealBosonComponents φ)]
  realBosonModule : ∀ (_ : RealBosonIrreps), Type
  [realBosonModule_addCommGroup : ∀ φ, AddCommGroup (realBosonModule φ)]
  [realBosonModule_module : ∀ φ, Module ℂ (realBosonModule φ)]
  realBosonBasis : ∀ φ, Basis (RealBosonComponents φ) ℂ (realBosonModule φ)

namespace LagrangianTheory


attribute [instance] fermionIrreps_fintype fermionIrreps_decEq
  fermionComponents_fintype fermionComponents_decEq
  fermionModule_addCommGroup fermionModule_module
  complexScalarIrreps_fintype complexScalarIrreps_decEq
  complexScalarComponents_fintype complexScalarComponents_decEq
  complexScalarModule_addCommGroup complexScalarModule_module

variable {G : Type} [Group G]

/-!

## A. Definitions related to fermions

-/

inductive FermionicGenerator (L : LagrangianTheory G)
  | of (φ : L.FermionIrreps) (α : L.FermionComponents φ) : L.FermionicGenerator
  | bar (φ : L.FermionIrreps) (α : L.FermionComponents φ) : L.FermionicGenerator
deriving DecidableEq, Fintype

def FermionicGenerator.conjugate {L : LagrangianTheory G} :
    L.FermionicGenerator → L.FermionicGenerator
  | .of φ α => .bar φ α
  | .bar φ α => .of φ α

@[simp]
lemma FermionicGenerator.conjugate_conjugate {L : LagrangianTheory G} (g : L.FermionicGenerator) :
    g.conjugate.conjugate = g := by
  cases g <;> rfl

def fermionicGeneratorEquiv {L : LagrangianTheory G}  : L.FermionicGenerator ≃
  (Σ φ : L.FermionIrreps, L.FermionComponents φ) ⊕ (Σ φ : L.FermionIrreps, L.FermionComponents φ) where
  toFun g := match g with
    | .of φ α => Sum.inl ⟨φ, α⟩
    | .bar φ α => Sum.inr ⟨φ, α⟩
  invFun g := match g with
    | Sum.inl ⟨φ, α⟩ => .of φ α
    | Sum.inr ⟨φ, α⟩ => .bar φ α
  left_inv g := by cases g <;> rfl
  right_inv g := by cases g <;> rfl

/-!

### A.1. The vector spaces of the fermionic fields.

-/

/-- The target vector space of the fermionic fields.
  If fermions are consider in terms of an associated-bundle, this vector space
  would be the fiber of that bundle.

  This vector space includes all the fields appearing in the theory. -/
abbrev FermionicTargetSpace (L : LagrangianTheory G) := Π (φ : L.FermionIrreps),  L.fermionModule φ

/-- The target vector space of covariant derivatives of fermions e.g. ∇_μ ψ.
  This is similar to the Jet space associated with fermions, however, because covariant derivatives
  do not commute, the commutation is not taken account of here.

  This vector space includes all the fields in the theory + their covariant derivatives. -/
abbrev FermionicDerivSpace (L : LagrangianTheory G) :=
  TensorAlgebra ℂ Lorentz.CoℂModule ⊗[ℂ] L.FermionicTargetSpace

/-- The fermionic target space linearly embeds into the fermionic target space with derivatives. -/
def FermionicTargetSpace.toFermionicDerivSpace {L : LagrangianTheory G} :
    L.FermionicTargetSpace →ₗ[ℂ] L.FermionicDerivSpace :=
  TensorProduct.mk ℂ (TensorAlgebra ℂ Lorentz.CoℂModule) L.FermionicTargetSpace 1

/-- Since fermions are complex fields, we also need to consider the target space of their
  complex conjugate. The vector space `FermionicTargetSpaceWithComplex` is defined
  to contain both the target space of the fields, and their conjugates.

  This vector space includes all the fields appearing in the theory + their conjugates.  -/
abbrev FermionicTargetSpaceWithComplex (L : LagrangianTheory G) := L.FermionicTargetSpace ×
  ConjModule L.FermionicTargetSpace

/-- Similar to `FermionicTargetSpaceWithComplex` except including derivatives.

  This vector space includes all the fields present in the theory + their conjugates + all
  their covariant derivatives. -/
abbrev FermionicDerivSpaceWithComplex (L : LagrangianTheory G) :=
  (TensorAlgebra ℂ Lorentz.CoℂModule ⊗[ℂ] L.FermionicTargetSpace) ×
  (TensorAlgebra ℂ Lorentz.CoℂModule ⊗[ℂ] L.FermionicTargetSpaceWithComplex)

/-- The vector space dual to `FermionicTargetSpaceWithComplex` and spanned by the component
  functions of all the fields + their conjugates in the theory. -/
abbrev FermionicComponentSpace (L : LagrangianTheory G) :=
  Module.Dual ℂ L.FermionicTargetSpaceWithComplex

/-- The vector space dual to `FermionicDerivSpaceWithComplex` and spanned by the component
  functions of all the fields + their conjugates + all their covariant derivatives in the theory. -/
abbrev FermionicComponentSpaceWithDeriv (L : LagrangianTheory G) :=
  Module.Dual ℂ L.FermionicDerivSpaceWithComplex

noncomputable def fermionicComponentBasis {L : LagrangianTheory G}  :
    Basis L.FermionicGenerator ℂ L.FermionicComponentSpace :=
  ((Pi.basis (fun φ => L.fermionBasis φ)).prod
  ((Pi.basis (fun φ => L.fermionBasis φ)).conj)).dualBasis.reindex fermionicGeneratorEquiv.symm

/-!

## A.2. The fermionic algebras

-/

/-- The EFT algebra spanned by the fermions in the theory + their conjugate. -/
abbrev FermionicEFTExclDeriv (L : LagrangianTheory G) := ExteriorAlgebra ℂ L.FermionicComponentSpace

/-- The EFT algebra spanned by the fermions in the theory + their conjugate + all their
  covariant derivatives without taking account of commutation of derivatives, or
  total derivatives or equations of motion relations. -/
abbrev FermionicEFTFreeDeriv (L : LagrangianTheory G) :=
  ExteriorAlgebra ℂ L.FermionicComponentSpaceWithDeriv

/-!

## A.1. The derivative space of the fermionic fields

-/

/-- The basis of `FermionicDerivSpace` indexed by pairs of a list of spacetime
  indices `Fin 1 ⊕ Fin 3` (the derivative slots, ordered since covariant derivatives
  do not commute) and a basis index of the fermionic target space. -/
noncomputable def FermionicDerivSpace.basis {L : LagrangianTheory G} :
    Basis (List (Fin 1 ⊕ Fin 3) × Σ φ : L.FermionIrreps, L.FermionComponents φ) ℂ
      L.FermionicDerivSpace :=
  (Lorentz.complexCoBasis.tensorAlgebra).tensorProduct (Pi.basis fun φ => L.fermionBasis φ)

/-- The inclusion of single covariant derivatives of the fermionic fields into
  the space of all covariant derivatives, `v ⊗ₜ ψ ↦ TensorAlgebra.ι ℂ v ⊗ₜ ψ`. -/
noncomputable def FermionicDerivSpace.ofSingleDeriv {L : LagrangianTheory G} :
    Lorentz.CoℂModule ⊗[ℂ] L.FermionicTargetSpace →ₗ[ℂ] L.FermionicDerivSpace :=
  LinearMap.rTensor L.FermionicTargetSpace (TensorAlgebra.ι ℂ)

/-!

### A.1 The representation of the Lorentz group on the fermionic part

-/

variable {L : LagrangianTheory G}

def FermionicTargetSpace.repLorentzGroup : Representation ℂ SL(2,ℂ) L.FermionicTargetSpace where
  toFun Λ := LinearMap.piMap fun φ => L.fermionRepLorentzGroup φ Λ
  map_one' := by
    ext x i y
    simp only [map_one, LinearMap.coe_comp, LinearMap.coe_piMap, LinearMap.coe_single,
      Function.comp_apply, Pi.map_apply, End.one_apply]
  map_mul' Λ1 Λ2 := by
    ext x i y
    simp

/-- The representation of the Lorentz group on the tensor algebra of covariant
  derivative slots, acting through `CoℂModule.SL2CRep` on each factor. -/
noncomputable def derivSlotsRepLorentzGroup :
    Representation ℂ SL(2,ℂ) (TensorAlgebra ℂ Lorentz.CoℂModule) where
  toFun Λ := (TensorAlgebra.lift ℂ
    (TensorAlgebra.ι ℂ ∘ₗ Lorentz.CoℂModule.SL2CRep Λ)).toLinearMap
  map_one' := by
    suffices h : TensorAlgebra.lift ℂ
        (TensorAlgebra.ι ℂ ∘ₗ Lorentz.CoℂModule.SL2CRep 1) =
        AlgHom.id ℂ (TensorAlgebra ℂ Lorentz.CoℂModule) by
      rw [h]; rfl
    ext v
    simp
  map_mul' Λ1 Λ2 := by
    suffices h : TensorAlgebra.lift ℂ
        (TensorAlgebra.ι ℂ ∘ₗ Lorentz.CoℂModule.SL2CRep (Λ1 * Λ2)) =
        (TensorAlgebra.lift ℂ
          (TensorAlgebra.ι ℂ ∘ₗ Lorentz.CoℂModule.SL2CRep Λ1)).comp
        (TensorAlgebra.lift ℂ
          (TensorAlgebra.ι ℂ ∘ₗ Lorentz.CoℂModule.SL2CRep Λ2)) by
      rw [h]; rfl
    ext v
    simp

/-- The representation of the Lorentz group on the covariant-derivative space of the fermionic
  fields: the tensor product of the action on the derivative slots and the action
  on the fermionic target space. -/
noncomputable def FermionicDerivSpace.repLorentzGroup :
    Representation ℂ SL(2,ℂ) L.FermionicDerivSpace :=
  derivSlotsRepLorentzGroup.tprod FermionicTargetSpace.repLorentzGroup

noncomputable def FermionicTargetSpaceWithComplex.repLorentzGroup :
    Representation ℂ SL(2,ℂ) L.FermionicTargetSpaceWithComplex :=
  FermionicTargetSpace.repLorentzGroup.prod (FermionicTargetSpace.repLorentzGroup.conj)

noncomputable def FermionicComponentSpace.repLorentzGroup :
    Representation ℂ SL(2,ℂ) L.FermionicComponentSpace :=
  FermionicTargetSpaceWithComplex.repLorentzGroup.dual

noncomputable def FermionicEFTExclDeriv.repLorentzGroup : Representation ℂ SL(2,ℂ) L.FermionicEFTExclDeriv where
  toFun Λ := (ExteriorAlgebra.map (FermionicComponentSpace.repLorentzGroup Λ)).toLinearMap
  map_one' := by
    simp only [map_one, End.one_eq_id, ExteriorAlgebra.map_id,
      AlgHom.toLinearMap_id]
  map_mul' Λ1 Λ2 := by
    simp only [map_mul, End.mul_eq_comp, ← ExteriorAlgebra.map_comp_map,
      AlgHom.comp_toLinearMap]

/-!

### A.2. The representation of the Gauge group on the fermionic part

-/


def FermionicTargetSpace.repGaugeGroup : Representation ℂ G L.FermionicTargetSpace where
  toFun Λ := LinearMap.piMap fun φ => L.fermionRepGaugeGroup φ Λ
  map_one' := by
    ext x i y
    simp only [map_one, LinearMap.coe_comp, LinearMap.coe_piMap, LinearMap.coe_single,
      Function.comp_apply, Pi.map_apply, End.one_apply]
  map_mul' Λ1 Λ2 := by
    ext x i y
    simp

noncomputable def FermionicTargetSpaceWithComplex.repGaugeGroup :
    Representation ℂ G L.FermionicTargetSpaceWithComplex :=
  FermionicTargetSpace.repGaugeGroup.prod (FermionicTargetSpace.repGaugeGroup.conj)

noncomputable def FermionicComponentSpace.repGaugeGroup : Representation ℂ G L.FermionicComponentSpace :=
  FermionicTargetSpaceWithComplex.repGaugeGroup.dual

noncomputable def FermionicEFTExclDeriv.repGaugeGroup : Representation ℂ G L.FermionicEFTExclDeriv where
  toFun Λ := (ExteriorAlgebra.map (FermionicComponentSpace.repGaugeGroup Λ)).toLinearMap
  map_one' := by
    simp only [map_one, End.one_eq_id, ExteriorAlgebra.map_id,
      AlgHom.toLinearMap_id]
  map_mul' Λ1 Λ2 := by
    simp only [map_mul, End.mul_eq_comp, ← ExteriorAlgebra.map_comp_map,
      AlgHom.comp_toLinearMap]

/-!

## B. Definitions related to the complex scalars

-/

inductive ComplexScalarGenerator (L : LagrangianTheory G)
  | of (φ : L.ComplexScalarIrreps) (α : L.ComplexScalarComponents φ) : L.ComplexScalarGenerator
  | bar (φ : L.ComplexScalarIrreps) (α : L.ComplexScalarComponents φ) : L.ComplexScalarGenerator
deriving DecidableEq, Fintype

def ComplexScalarGenerator.conjugate : L.ComplexScalarGenerator → L.ComplexScalarGenerator
  | .of φ α => .bar φ α
  | .bar φ α => .of φ α

@[simp]
lemma ComplexScalarGenerator.conjugate_conjugate (g : L.ComplexScalarGenerator) :
    g.conjugate.conjugate = g := by
  cases g <;> rfl

def complexScalarGeneratorEquiv : L.ComplexScalarGenerator ≃
    (Σ φ : L.ComplexScalarIrreps, L.ComplexScalarComponents φ) ⊕
    (Σ φ : L.ComplexScalarIrreps, L.ComplexScalarComponents φ) where
  toFun g := match g with
    | .of φ α => Sum.inl ⟨φ, α⟩
    | .bar φ α => Sum.inr ⟨φ, α⟩
  invFun g := match g with
    | Sum.inl ⟨φ, α⟩ => .of φ α
    | Sum.inr ⟨φ, α⟩ => .bar φ α
  left_inv g := by cases g <;> rfl
  right_inv g := by cases g <;> rfl

abbrev ComplexScalarTargetSpace (L : LagrangianTheory G) :=
  Π (φ : L.ComplexScalarIrreps), L.complexScalarModule φ

/-- The target space of the complex scalar fields, including their conjugates. -/
abbrev ComplexScalarTargetSpaceWithComplex (L : LagrangianTheory G) :=
  L.ComplexScalarTargetSpace × ConjModule L.ComplexScalarTargetSpace

abbrev ComplexScalarComponentSpace (L : LagrangianTheory G) :=
  Module.Dual ℂ L.ComplexScalarTargetSpaceWithComplex

noncomputable def complexScalarComponentBasis :
    Basis L.ComplexScalarGenerator ℂ L.ComplexScalarComponentSpace :=
  ((Pi.basis (fun φ => L.complexScalarBasis φ)).prod
  ((Pi.basis (fun φ => L.complexScalarBasis φ)).conj)).dualBasis.reindex
    complexScalarGeneratorEquiv.symm

abbrev ComplexScalarEFTExclDeriv (L : LagrangianTheory G) :=
  SymmetricAlgebra ℂ L.ComplexScalarComponentSpace

/-!

### B.1 The representation of the Lorentz group on the complex scalar part

-/

def ComplexScalarTargetSpace.repLorentzGroup :
    Representation ℂ SL(2,ℂ) L.ComplexScalarTargetSpace where
  toFun Λ := LinearMap.piMap fun φ => L.complexScalarRepLorentzGroup φ Λ
  map_one' := by
    ext x i y
    simp only [map_one, LinearMap.coe_comp, LinearMap.coe_piMap, LinearMap.coe_single,
      Function.comp_apply, Pi.map_apply, End.one_apply]
  map_mul' Λ1 Λ2 := by
    ext x i y
    simp

noncomputable def ComplexScalarTargetSpaceWithComplex.repLorentzGroup :
    Representation ℂ SL(2,ℂ) L.ComplexScalarTargetSpaceWithComplex :=
  ComplexScalarTargetSpace.repLorentzGroup.prod (ComplexScalarTargetSpace.repLorentzGroup.conj)

noncomputable def ComplexScalarComponentSpace.repLorentzGroup :
    Representation ℂ SL(2,ℂ) L.ComplexScalarComponentSpace :=
  ComplexScalarTargetSpaceWithComplex.repLorentzGroup.dual

noncomputable def ComplexScalarEFTExclDeriv.repLorentzGroup :
    Representation ℂ SL(2,ℂ) L.ComplexScalarEFTExclDeriv where
  toFun Λ := (SymmetricAlgebra.lift
    (SymmetricAlgebra.ι ℂ _ ∘ₗ ComplexScalarComponentSpace.repLorentzGroup Λ)).toLinearMap
  map_one' := by
    simp [End.one_eq_id]
  map_mul' Λ1 Λ2 := by
    suffices h : SymmetricAlgebra.lift
        (SymmetricAlgebra.ι ℂ _ ∘ₗ ComplexScalarComponentSpace.repLorentzGroup (Λ1 * Λ2)) =
        (SymmetricAlgebra.lift
          (SymmetricAlgebra.ι ℂ _ ∘ₗ ComplexScalarComponentSpace.repLorentzGroup Λ1)).comp
        (SymmetricAlgebra.lift
          (SymmetricAlgebra.ι ℂ _ ∘ₗ ComplexScalarComponentSpace.repLorentzGroup Λ2)) by
      rw [h]; rfl
    ext v
    simp

/-!

### B.2. The representation of the Gauge group on the complex scalar part

-/

def ComplexScalarTargetSpace.repGaugeGroup :
    Representation ℂ G L.ComplexScalarTargetSpace where
  toFun g := LinearMap.piMap fun φ => L.complexScalarRepGaugeGroup φ g
  map_one' := by
    ext x i y
    simp only [map_one, LinearMap.coe_comp, LinearMap.coe_piMap, LinearMap.coe_single,
      Function.comp_apply, Pi.map_apply, End.one_apply]
  map_mul' g1 g2 := by
    ext x i y
    simp

noncomputable def ComplexScalarTargetSpaceWithComplex.repGaugeGroup :
    Representation ℂ G L.ComplexScalarTargetSpaceWithComplex :=
  ComplexScalarTargetSpace.repGaugeGroup.prod (ComplexScalarTargetSpace.repGaugeGroup.conj)

noncomputable def ComplexScalarComponentSpace.repGaugeGroup :
    Representation ℂ G L.ComplexScalarComponentSpace :=
  ComplexScalarTargetSpaceWithComplex.repGaugeGroup.dual

noncomputable def ComplexScalarEFTExclDeriv.repGaugeGroup :
    Representation ℂ G L.ComplexScalarEFTExclDeriv where
  toFun g := (SymmetricAlgebra.lift
    (SymmetricAlgebra.ι ℂ _ ∘ₗ ComplexScalarComponentSpace.repGaugeGroup g)).toLinearMap
  map_one' := by
    simp [End.one_eq_id]
  map_mul' g1 g2 := by
    suffices h : SymmetricAlgebra.lift
        (SymmetricAlgebra.ι ℂ _ ∘ₗ ComplexScalarComponentSpace.repGaugeGroup (g1 * g2)) =
        (SymmetricAlgebra.lift
          (SymmetricAlgebra.ι ℂ _ ∘ₗ ComplexScalarComponentSpace.repGaugeGroup g1)).comp
        (SymmetricAlgebra.lift
          (SymmetricAlgebra.ι ℂ _ ∘ₗ ComplexScalarComponentSpace.repGaugeGroup g2)) by
      rw [h]; rfl
    ext v
    simp

/-!

## C. General field generators

-/


inductive FieldGenerators (L : LagrangianTheory G)
  | cScalar (_ : L.ComplexScalarGenerator) : FieldGenerators L
  | fermion (_ : L.FermionicGenerator) : FieldGenerators L
deriving DecidableEq, Fintype

def FieldGenerators.IsFermion : L.FieldGenerators → Bool
  | .cScalar _ => False
  | .fermion _ => True

def FieldGenerators.IsBoson : L.FieldGenerators → Bool
  | .cScalar _ => True
  | .fermion _ => False

def FieldGenerators.conjugate : L.FieldGenerators → L.FieldGenerators
  | .cScalar g => .cScalar g.conjugate
  | .fermion g => .fermion g.conjugate

@[simp]
lemma FieldGenerators.conjugate_conjugate (ϕ : L.FieldGenerators) :
    ϕ.conjugate.conjugate = ϕ := by
  cases ϕ <;> simp [conjugate]

def fieldGeneratorsEquiv : L.FieldGenerators ≃
    L.ComplexScalarGenerator ⊕ L.FermionicGenerator where
  toFun g := match g with
    | .cScalar g => Sum.inl g
    | .fermion g => Sum.inr g
  invFun g := match g with
    | Sum.inl g => .cScalar g
    | Sum.inr g => .fermion g
  left_inv g := by cases g <;> rfl
  right_inv g := by cases g <;> rfl

@[simp]
lemma FieldGenerators.cScalar_isFermion (ϕ : L.ComplexScalarGenerator) :
     (cScalar ϕ).IsFermion = False := by simp [IsFermion]

@[simp]
lemma FieldGenerators.fermion_isFermion (ϕ : L.FermionicGenerator) :
     (fermion ϕ).IsFermion = True := by simp [IsFermion]

@[simp]
lemma FieldGenerators.cScalar_isBoson (ϕ : L.ComplexScalarGenerator) :
     (cScalar ϕ).IsBoson = True := by simp [IsBoson]

@[simp]
lemma FieldGenerators.fermion_isBoson (ϕ : L.FermionicGenerator) :
     (fermion ϕ).IsBoson = False := by simp [IsBoson]


end LagrangianTheory
