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
/-!

# The Standard Model EFT Lagrangian without derivatives

## i. Overview

-/

@[expose] public section

/-!

## The basic type for a lagrangian theory

-/
open Matrix MatrixGroups Module

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

namespace LagrangianTheory

/-!

## A. Definitions related to fermions

-/

attribute [instance] fermionIrreps_fintype fermionIrreps_decEq
  fermionComponents_fintype fermionComponents_decEq
  fermionModule_addCommGroup fermionModule_module
  complexScalarIrreps_fintype complexScalarIrreps_decEq
  complexScalarComponents_fintype complexScalarComponents_decEq
  complexScalarModule_addCommGroup complexScalarModule_module

variable {G : Type} [Group G]

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

abbrev FermionicTargetSpace (L : LagrangianTheory G) := Π (φ : L.FermionIrreps),  L.fermionModule φ

/-- The target space of the fermionic fields, including their conjugates. -/
abbrev FermionicTargetSpaceWithComplex (L : LagrangianTheory G) := L.FermionicTargetSpace ×
  ConjModule L.FermionicTargetSpace


abbrev FermionicComponentSpace (L : LagrangianTheory G) :=
  Module.Dual ℂ L.FermionicTargetSpaceWithComplex

noncomputable def fermionicComponentBasis {L : LagrangianTheory G}  :
    Basis L.FermionicGenerator ℂ L.FermionicComponentSpace :=
  ((Pi.basis (fun φ => L.fermionBasis φ)).prod
  ((Pi.basis (fun φ => L.fermionBasis φ)).conj)).dualBasis.reindex fermionicGeneratorEquiv.symm

abbrev FermionicEFTExclDeriv (L : LagrangianTheory G) := ExteriorAlgebra ℂ L.FermionicComponentSpace

end LagrangianTheory
