/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Jinzheng Li, Nathaneal Sajan
-/
module

public import Physlib.Particles.LagrangianTheory.Basic
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

namespace StandardModel
noncomputable section

open Module Matrix
open MatrixGroups
open Complex
open TensorProduct
open CategoryTheory.MonoidalCategory
open Fermion

/-!

## Field specification

-/

/-!

## Specific block: The input data for Fermions

For the Wess-Zumino theory there is a single left-handed Weyl fermion.

-/

/-- The irreducible representations of the fermion field
  under the Lorentz group. -/
inductive FermionIrrep
  | Q (i : Fin 3) : FermionIrrep
  | u (i : Fin 3) : FermionIrrep
  | d (i : Fin 3) : FermionIrrep
  | L (i : Fin 3) : FermionIrrep
  | e (i : Fin 3) : FermionIrrep
deriving DecidableEq, Fintype

/-- The components of each of the irreducible Fermionic representations
  appearing in the Standard model. The components are ordered by
  `Lorentz - SU(3) - SU(2)`. -/
def FermionIrrep.components : FermionIrrep → Type
  | .Q _ => Fin 2 × Fin 3 × Fin 2
  | .u _ => Fin 2 × Fin 3
  | .d _ => Fin 2 × Fin 3
  | .L _ => Fin 2 × Fin 2
  | .e _ => Fin 2

instance : (φ : FermionIrrep) → Fintype (FermionIrrep.components φ)
  | .Q _ => inferInstanceAs (Fintype (Fin 2 × Fin 3 × Fin 2))
  | .u _ => inferInstanceAs (Fintype (Fin 2 × Fin 3))
  | .d _ => inferInstanceAs (Fintype (Fin 2 × Fin 3))
  | .L _ => inferInstanceAs (Fintype (Fin 2 × Fin 2))
  | .e _ => inferInstanceAs (Fintype (Fin 2))

instance : (φ : FermionIrrep) → DecidableEq (FermionIrrep.components φ)
  | .Q _ => inferInstanceAs (DecidableEq (Fin 2 × Fin 3 × Fin 2))
  | .u _ => inferInstanceAs (DecidableEq (Fin 2 × Fin 3))
  | .d _ => inferInstanceAs (DecidableEq (Fin 2 × Fin 3))
  | .L _ => inferInstanceAs (DecidableEq (Fin 2 × Fin 2))
  | .e _ => inferInstanceAs (DecidableEq (Fin 2))

def FermionIrrep.module : FermionIrrep → Type
  | .Q _ => QuarkDoublet
  | .u _ => UpSinglet
  | .d _ => DownSinglet
  | .L _ => LeptonDoublet
  | .e _ => LeptonSinglet

instance : (φ : FermionIrrep) →  AddCommGroup (FermionIrrep.module φ)
  | .Q _ => inferInstanceAs (AddCommGroup QuarkDoublet)
  | .u _ => inferInstanceAs (AddCommGroup UpSinglet)
  | .d _ => inferInstanceAs (AddCommGroup DownSinglet)
  | .L _ => inferInstanceAs (AddCommGroup LeptonDoublet)
  | .e _ => inferInstanceAs (AddCommGroup LeptonSinglet)

instance : (φ : FermionIrrep) →  Module ℂ (FermionIrrep.module φ)
  | .Q _ => inferInstanceAs (Module ℂ QuarkDoublet)
  | .u _ => inferInstanceAs (Module ℂ UpSinglet)
  | .d _ => inferInstanceAs (Module ℂ DownSinglet)
  | .L _ => inferInstanceAs (Module ℂ LeptonDoublet)
  | .e _ => inferInstanceAs (Module ℂ LeptonSinglet)

def FermionIrrep.basis  : (φ : FermionIrrep) →
    Basis (FermionIrrep.components φ) ℂ (FermionIrrep.module φ)
  | .Q _ => QuarkDoublet.basis
  | .u _ => UpSinglet.basis
  | .d _ => DownSinglet.basis
  | .L _ => LeptonDoublet.basis
  | .e _ => LeptonSinglet.basis

def FermionIrrep.repLorentzGroup :
    (φ : FermionIrrep) → Representation ℂ SL(2,ℂ) (FermionIrrep.module φ)
  | .Q _ => QuarkDoublet.repLorentzGroup
  | .u _ => UpSinglet.repLorentzGroup
  | .d _ => DownSinglet.repLorentzGroup
  | .L _ => LeptonDoublet.repLorentzGroup
  | .e _ => LeptonSinglet.repLorentzGroup

def FermionIrrep.repGaugeGroupI :
    (φ : FermionIrrep) → Representation ℂ GaugeGroupI (FermionIrrep.module φ)
  | .Q _ => QuarkDoublet.repGaugeGroupI
  | .u _ => UpSinglet.repGaugeGroupI
  | .d _ => DownSinglet.repGaugeGroupI
  | .L _ => LeptonDoublet.repGaugeGroupI
  | .e _ => LeptonSinglet.repGaugeGroupI

/-!

## Repetable Derived Fermionic quantities

This are quantities whose form is independent of the specific theory
we are constructing.

-/

inductive FermionicGenerator
  | of (φ : FermionIrrep) (α : FermionIrrep.components φ) : FermionicGenerator
  | bar (φ : FermionIrrep) (α : FermionIrrep.components φ) : FermionicGenerator
deriving DecidableEq, Fintype

def FermionicGenerator.conjugate : FermionicGenerator → FermionicGenerator
  | .of φ α => .bar φ α
  | .bar φ α => .of φ α

@[simp]
lemma FermionicGenerator.conjugate_conjugate (g : FermionicGenerator) :
    g.conjugate.conjugate = g := by
  cases g <;> rfl

def fermionicGeneratorEquiv : FermionicGenerator ≃
  (Σ φ : FermionIrrep, FermionIrrep.components φ) ⊕ (Σ φ : FermionIrrep, FermionIrrep.components φ) where
  toFun g := match g with
    | .of φ α => Sum.inl ⟨φ, α⟩
    | .bar φ α => Sum.inr ⟨φ, α⟩
  invFun g := match g with
    | Sum.inl ⟨φ, α⟩ => .of φ α
    | Sum.inr ⟨φ, α⟩ => .bar φ α
  left_inv g := by cases g <;> rfl
  right_inv g := by cases g <;> rfl

abbrev FermionicTargetSpace := Π (φ : FermionIrrep), FermionIrrep.module φ

/-- The target space of the fermionic fields, including their conjugates. -/
abbrev FermionicTargetSpaceWithComplex := FermionicTargetSpace ×
  ConjModule FermionicTargetSpace


abbrev FermionicComponentSpace := Module.Dual ℂ FermionicTargetSpaceWithComplex

def fermionicComponentBasis : Basis FermionicGenerator ℂ FermionicComponentSpace :=
  ((Pi.basis (fun φ => FermionIrrep.basis φ)).prod
  ((Pi.basis (fun φ => FermionIrrep.basis φ)).conj)).dualBasis.reindex fermionicGeneratorEquiv.symm

abbrev FermionicEFTExclDeriv := ExteriorAlgebra ℂ FermionicComponentSpace

/-!

### The representation of the Lorentz group on the fermionic part

-/

def FermionicTargetSpace.repLorentzGroup : Representation ℂ SL(2,ℂ) FermionicTargetSpace where
  toFun Λ := LinearMap.piMap fun φ => FermionIrrep.repLorentzGroup φ Λ
  map_one' := by
    ext x i y
    simp only [map_one, LinearMap.coe_comp, LinearMap.coe_piMap, LinearMap.coe_single,
      Function.comp_apply, Pi.map_apply, End.one_apply]
  map_mul' Λ1 Λ2 := by
    ext x i y
    simp

def FermionicTargetSpaceWithComplex.repLorentzGroup :
    Representation ℂ SL(2,ℂ) FermionicTargetSpaceWithComplex :=
  FermionicTargetSpace.repLorentzGroup.prod (FermionicTargetSpace.repLorentzGroup.conj)

def FermionicComponentSpace.repLorentzGroup : Representation ℂ SL(2,ℂ) FermionicComponentSpace :=
  FermionicTargetSpaceWithComplex.repLorentzGroup.dual

def FermionicEFTExclDeriv.repLorentzGroup : Representation ℂ SL(2,ℂ) FermionicEFTExclDeriv where
  toFun Λ := (ExteriorAlgebra.map (FermionicComponentSpace.repLorentzGroup Λ)).toLinearMap
  map_one' := by
    simp only [map_one, End.one_eq_id, ExteriorAlgebra.map_id,
      AlgHom.toLinearMap_id]
  map_mul' Λ1 Λ2 := by
    simp only [map_mul, End.mul_eq_comp, ← ExteriorAlgebra.map_comp_map,
      AlgHom.comp_toLinearMap]

/-!

### The representation of the Gauge group on the fermionic part

-/


def FermionicTargetSpace.repGaugeGroupI : Representation ℂ GaugeGroupI FermionicTargetSpace where
  toFun Λ := LinearMap.piMap fun φ => FermionIrrep.repGaugeGroupI φ Λ
  map_one' := by
    ext x i y
    simp only [map_one, LinearMap.coe_comp, LinearMap.coe_piMap, LinearMap.coe_single,
      Function.comp_apply, Pi.map_apply, End.one_apply]
  map_mul' Λ1 Λ2 := by
    ext x i y
    simp

def FermionicTargetSpaceWithComplex.repGaugeGroupI :
    Representation ℂ GaugeGroupI FermionicTargetSpaceWithComplex :=
  FermionicTargetSpace.repGaugeGroupI.prod (FermionicTargetSpace.repGaugeGroupI.conj)

def FermionicComponentSpace.repGaugeGroupI : Representation ℂ GaugeGroupI FermionicComponentSpace :=
  FermionicTargetSpaceWithComplex.repGaugeGroupI.dual

def FermionicEFTExclDeriv.repGaugeGroupI : Representation ℂ GaugeGroupI FermionicEFTExclDeriv where
  toFun Λ := (ExteriorAlgebra.map (FermionicComponentSpace.repGaugeGroupI Λ)).toLinearMap
  map_one' := by
    simp only [map_one, End.one_eq_id, ExteriorAlgebra.map_id,
      AlgHom.toLinearMap_id]
  map_mul' Λ1 Λ2 := by
    simp only [map_mul, End.mul_eq_comp, ← ExteriorAlgebra.map_comp_map,
      AlgHom.comp_toLinearMap]



/-!

## The input data for the complex scalar fields

-/


set_option linter.constructorNameAsVariable false

inductive ComplexScalarIrrep
  | H : ComplexScalarIrrep
deriving DecidableEq, Fintype

def ComplexScalarIrrep.components : ComplexScalarIrrep → Type
  | .H => Fin 2

instance : (φ : ComplexScalarIrrep) → Fintype (ComplexScalarIrrep.components φ)
  | .H => inferInstanceAs (Fintype (Fin 2))

instance : (φ : ComplexScalarIrrep) → DecidableEq (ComplexScalarIrrep.components φ)
  | .H => inferInstanceAs (DecidableEq (Fin 2))

def ComplexScalarIrrep.module : ComplexScalarIrrep → Type
  | .H => HiggsVec

instance : (φ : ComplexScalarIrrep) →  AddCommGroup (ComplexScalarIrrep.module φ)
  | .H => inferInstanceAs (AddCommGroup HiggsVec)

instance : (φ : ComplexScalarIrrep) →  Module ℂ (ComplexScalarIrrep.module φ)
  | .H => inferInstanceAs (Module ℂ HiggsVec)

def ComplexScalarIrrep.basis  : (φ : ComplexScalarIrrep) →
    Basis (ComplexScalarIrrep.components φ) ℂ (ComplexScalarIrrep.module φ)
  | .H => HiggsVec.orthonormBasis.toBasis

def ComplexScalarIrrep.repLorentzGroup : (φ : ComplexScalarIrrep) → Representation ℂ SL(2,ℂ) (ComplexScalarIrrep.module φ)
  | .H => Representation.trivial ℂ SL(2,ℂ) HiggsVec

def ComplexScalarIrrep.repGaugeGroupI :
    (φ : ComplexScalarIrrep) → Representation ℂ GaugeGroupI (ComplexScalarIrrep.module φ)
  | .H => HiggsVec.repGaugeGroupI

@[reducible]
def StandardModelLT : LagrangianTheory GaugeGroupI where
  FermionIrreps := FermionIrrep
  FermionComponents := FermionIrrep.components
  fermionModule := FermionIrrep.module
  fermionBasis := FermionIrrep.basis
  fermionRepLorentzGroup := FermionIrrep.repLorentzGroup
  fermionRepGaugeGroup := FermionIrrep.repGaugeGroupI
  ComplexScalarIrreps := ComplexScalarIrrep
  ComplexScalarComponents := ComplexScalarIrrep.components
  complexScalarModule := ComplexScalarIrrep.module
  complexScalarBasis := ComplexScalarIrrep.basis
  complexScalarRepLorentzGroup := ComplexScalarIrrep.repLorentzGroup
  complexScalarRepGaugeGroup := ComplexScalarIrrep.repGaugeGroupI
  -- The Standard Model has no real bosonic fields at the no-derivative level
  -- (the field strengths only enter the free-derivative layer).
  RealBosonIrreps := Empty
  RealBosonComponents := fun x => x.elim
  realBosonComponents_fintype := fun x => x.elim
  realBosonComponents_decEq := fun x => x.elim
  realBosonModule := fun x => x.elim
  realBosonModule_addCommGroup := fun x => x.elim
  realBosonModule_module := fun x => x.elim
  realBosonBasis := fun x => x.elim
  realBosonRepLorentzGroup := fun x => x.elim
  realBosonRepGaugeGroup := fun x => x.elim

/-!

## Derived Complex Scalar quantities

-/

inductive ComplexScalarGenerator
  | of (ϕ : ComplexScalarIrrep) (α : ComplexScalarIrrep.components ϕ) : ComplexScalarGenerator
  | bar (ϕ : ComplexScalarIrrep) (α : ComplexScalarIrrep.components ϕ) : ComplexScalarGenerator
deriving DecidableEq, Fintype

def ComplexScalarGenerator.conjugate : ComplexScalarGenerator → ComplexScalarGenerator
  | .of φ α => .bar φ α
  | .bar φ α => .of φ α

@[simp]
lemma ComplexScalarGenerator.conjugate_conjugate (g : ComplexScalarGenerator) :
    g.conjugate.conjugate = g := by
  cases g <;> rfl

def complexScalarGeneratorEquiv : ComplexScalarGenerator ≃
    (Σ φ : ComplexScalarIrrep, ComplexScalarIrrep.components φ) ⊕
    (Σ φ : ComplexScalarIrrep, ComplexScalarIrrep.components φ) where
  toFun g := match g with
    | .of φ α => Sum.inl ⟨φ, α⟩
    | .bar φ α => Sum.inr ⟨φ, α⟩
  invFun g := match g with
    | Sum.inl ⟨φ, α⟩ => .of φ α
    | Sum.inr ⟨φ, α⟩ => .bar φ α
  left_inv g := by cases g <;> rfl
  right_inv g := by cases g <;> rfl

abbrev ComplexScalarTargetSpace := Π (φ : ComplexScalarIrrep), ComplexScalarIrrep.module φ


/-- The target space of the fermionic fields, including their conjugates. -/
abbrev ComplexScalarTargetSpaceWithComplex := ComplexScalarTargetSpace ×
  ConjModule ComplexScalarTargetSpace


abbrev ComplexScalarComponentSpace := Module.Dual ℂ ComplexScalarTargetSpaceWithComplex

def complexScalarComponentBasis : Basis ComplexScalarGenerator ℂ ComplexScalarComponentSpace :=
  ((Pi.basis (fun φ => ComplexScalarIrrep.basis φ)).prod
  ((Pi.basis (fun φ => ComplexScalarIrrep.basis φ)).conj)).dualBasis.reindex complexScalarGeneratorEquiv.symm

abbrev ComplexScalarEFTExclDeriv := SymmetricAlgebra ℂ ComplexScalarComponentSpace


/-!

### The representation of the Lorentz group on the complex scalar part

-/

def ComplexScalarTargetSpace.repLorentzGroup : Representation ℂ SL(2,ℂ) ComplexScalarTargetSpace where
  toFun Λ := LinearMap.piMap fun φ => ComplexScalarIrrep.repLorentzGroup φ Λ
  map_one' := by
    ext1 x
    apply LinearMap.ext
    intro i
    ext y
    simp
  map_mul' Λ1 Λ2 := by
    ext1 x
    apply LinearMap.ext
    intro i
    ext y
    simp

/-- The representation of the Lorentz group on the fermionic target space:
  the irreps act componentwise on the product of their modules, and by the
  conjugate action on the conjugate factor. -/
def ComplexScalarTargetSpaceWithComplex.repLorentzGroup :
    Representation ℂ SL(2,ℂ) ComplexScalarTargetSpaceWithComplex :=
  (ComplexScalarTargetSpace.repLorentzGroup).prod (ComplexScalarTargetSpace.repLorentzGroup.conj)

def ComplexScalarComponentSpace.repLorentzGroup : Representation ℂ SL(2,ℂ) ComplexScalarComponentSpace :=
  (ComplexScalarTargetSpaceWithComplex.repLorentzGroup).dual

def ComplexScalarEFTExclDeriv.repLorentzGroup : Representation ℂ SL(2,ℂ) ComplexScalarEFTExclDeriv where
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

## The representation of the Gauge group on the complex scalar part

-/

def ComplexScalarTargetSpace.repGaugeGroupI :
    Representation ℂ GaugeGroupI ComplexScalarTargetSpace where
  toFun g := LinearMap.piMap fun φ => ComplexScalarIrrep.repGaugeGroupI φ g
  map_one' := by
    ext1 x
    apply LinearMap.ext
    intro i
    ext y
    simp
  map_mul' g1 g2 := by
    ext1 x
    apply LinearMap.ext
    intro i
    ext y
    simp

/-- The representation of the gauge group on the complex scalar target space:
  the irreps act componentwise on the product of their modules, and by the
  conjugate action on the conjugate factor. -/
def ComplexScalarTargetSpaceWithComplex.repGaugeGroupI :
    Representation ℂ GaugeGroupI ComplexScalarTargetSpaceWithComplex :=
  (ComplexScalarTargetSpace.repGaugeGroupI).prod (ComplexScalarTargetSpace.repGaugeGroupI.conj)

def ComplexScalarComponentSpace.repGaugeGroupI :
    Representation ℂ GaugeGroupI ComplexScalarComponentSpace :=
  (ComplexScalarTargetSpaceWithComplex.repGaugeGroupI).dual

def ComplexScalarEFTExclDeriv.repGaugeGroupI :
    Representation ℂ GaugeGroupI ComplexScalarEFTExclDeriv where
  toFun g := (SymmetricAlgebra.lift
    (SymmetricAlgebra.ι ℂ _ ∘ₗ ComplexScalarComponentSpace.repGaugeGroupI g)).toLinearMap
  map_one' := by
    simp [End.one_eq_id]
  map_mul' g1 g2 := by
    suffices h : SymmetricAlgebra.lift
        (SymmetricAlgebra.ι ℂ _ ∘ₗ ComplexScalarComponentSpace.repGaugeGroupI (g1 * g2)) =
        (SymmetricAlgebra.lift
          (SymmetricAlgebra.ι ℂ _ ∘ₗ ComplexScalarComponentSpace.repGaugeGroupI g1)).comp
        (SymmetricAlgebra.lift
          (SymmetricAlgebra.ι ℂ _ ∘ₗ ComplexScalarComponentSpace.repGaugeGroupI g2)) by
      rw [h]; rfl
    ext v
    simp

/-!

## The field generators

-/

inductive FieldGenerators
  | cScalar (_ : ComplexScalarGenerator) : FieldGenerators
  | fermion (_ : FermionicGenerator) : FieldGenerators
deriving DecidableEq, Fintype

def FieldGenerators.IsFermion : FieldGenerators → Bool
  | .cScalar _ => False
  | .fermion _ => True

def FieldGenerators.IsBoson : FieldGenerators → Bool
  | .cScalar _ => True
  | .fermion _ => False

def FieldGenerators.conjugate : FieldGenerators → FieldGenerators
  | .cScalar g => .cScalar g.conjugate
  | .fermion g => .fermion g.conjugate

@[simp]
lemma FieldGenerators.conjugate_conjugate (ϕ : FieldGenerators) :
    ϕ.conjugate.conjugate = ϕ := by
  cases ϕ <;> simp [conjugate]

def fieldGeneratorsEquiv : FieldGenerators ≃
    ComplexScalarGenerator ⊕ FermionicGenerator where
  toFun g := match g with
    | .cScalar g => Sum.inl g
    | .fermion g => Sum.inr g
  invFun g := match g with
    | Sum.inl g => .cScalar g
    | Sum.inr g => .fermion g
  left_inv g := by cases g <;> rfl
  right_inv g := by cases g <;> rfl

@[simp]
lemma FieldGenerators.cScalar_isFermion (ϕ : ComplexScalarGenerator) :
     (cScalar ϕ).IsFermion = False := by simp [IsFermion]

@[simp]
lemma FieldGenerators.fermion_isFermion (ϕ : FermionicGenerator) :
     (fermion ϕ).IsFermion = True := by simp [IsFermion]

@[simp]
lemma FieldGenerators.cScalar_isBoson (ϕ : ComplexScalarGenerator) :
     (cScalar ϕ).IsBoson = True := by simp [IsBoson]

@[simp]
lemma FieldGenerators.fermion_isBoson (ϕ : FermionicGenerator) :
     (fermion ϕ).IsBoson = False := by simp [IsBoson]


/-!

## Irreps

-/

inductive Irrep
  | cScalar (_ : ComplexScalarIrrep) : Irrep
  | barCScalar (_ : ComplexScalarIrrep) : Irrep
  | fermion (_ : FermionIrrep) : Irrep
  | barFermion (_ : FermionIrrep) : Irrep

def FieldGenerators.toIrrep : FieldGenerators → Irrep
  | .cScalar (.of φ _) => .cScalar φ
  | .cScalar (.bar φ _) => .barCScalar φ
  | .fermion (.of φ _) => .fermion φ
  | .fermion (.bar φ _) => .barFermion φ

/-!

## A. The EFT lagrangian without derivatives

-/

/-- The algebra corresponding to the EFT lagrangian excluding
  derivative terms for the Wess-Zumino theory: the free supercommutative algebra
  on the bosonic and fermionic generators, i.e. the tensor product of the symmetric
  algebra on the bosonic duals with the exterior algebra on the fermionic duals. -/
abbrev EFTLagrangianExclDeriv : Type :=
  -- bosonic part of the lagrangian
  ComplexScalarEFTExclDeriv ⊗[ℂ]
  -- fermionic part of the lagrangian
  FermionicEFTExclDeriv

namespace EFTLagrangianExclDeriv

/-!

## B. Invariance under the group actions

-/
/-!

### B.1 The representation of the Lorentz group on the EFT lagrangian

-/

/-- The representation of the Lorentz group on `EFTLagrangianExclDeriv`. -/
def repLorentzGroup : Representation ℂ SL(2,ℂ) EFTLagrangianExclDeriv :=
  (ComplexScalarEFTExclDeriv.repLorentzGroup).tprod (FermionicEFTExclDeriv.repLorentzGroup)

lemma repLorentzGroup_mul (Λ : SL(2,ℂ)) (V W : EFTLagrangianExclDeriv) :
    repLorentzGroup Λ (V * W) = repLorentzGroup Λ V * repLorentzGroup Λ W :=
  map_mul (Algebra.TensorProduct.map
    (SymmetricAlgebra.lift
      (SymmetricAlgebra.ι ℂ _ ∘ₗ ComplexScalarComponentSpace.repLorentzGroup Λ))
    (ExteriorAlgebra.map (FermionicComponentSpace.repLorentzGroup Λ))) V W

@[simp]
lemma repLorentzGroup_one (Λ : SL(2,ℂ)) :
    repLorentzGroup Λ 1 = 1 :=
  map_one (Algebra.TensorProduct.map
    (SymmetricAlgebra.lift
      (SymmetricAlgebra.ι ℂ _ ∘ₗ ComplexScalarComponentSpace.repLorentzGroup Λ))
    (ExteriorAlgebra.map (FermionicComponentSpace.repLorentzGroup Λ)))

/-!

### B.2 The representation of the gauge group on the EFT lagrangian

-/

/-- The representation of the gauge group on `EFTLagrangianExclDeriv`. -/
def repGaugeGroupI : Representation ℂ GaugeGroupI EFTLagrangianExclDeriv :=
  (ComplexScalarEFTExclDeriv.repGaugeGroupI).tprod (FermionicEFTExclDeriv.repGaugeGroupI)

lemma repGaugeGroupI_mul (g : GaugeGroupI) (V W : EFTLagrangianExclDeriv) :
    repGaugeGroupI g (V * W) = repGaugeGroupI g V * repGaugeGroupI g W :=
  map_mul (Algebra.TensorProduct.map
    (SymmetricAlgebra.lift
      (SymmetricAlgebra.ι ℂ _ ∘ₗ ComplexScalarComponentSpace.repGaugeGroupI g))
    (ExteriorAlgebra.map (FermionicComponentSpace.repGaugeGroupI g))) V W

@[simp]
lemma repGaugeGroupI_one (g : GaugeGroupI) :
    repGaugeGroupI g 1 = 1 :=
  map_one (Algebra.TensorProduct.map
    (SymmetricAlgebra.lift
      (SymmetricAlgebra.ι ℂ _ ∘ₗ ComplexScalarComponentSpace.repGaugeGroupI g))
    (ExteriorAlgebra.map (FermionicComponentSpace.repGaugeGroupI g)))

/-!

### B.3. The condition for invariance

-/

def IsInvariant (V : EFTLagrangianExclDeriv) : Prop :=
  (∀ (Λ : SL(2,ℂ)), repLorentzGroup Λ V = V) ∧ ∀ (g : GaugeGroupI), repGaugeGroupI g V = V

@[simp]
lemma IsInvariant.zero : IsInvariant 0 := by
  simp [IsInvariant]

lemma IsInvariant.add {V W : EFTLagrangianExclDeriv} (hV : IsInvariant V) (hW : IsInvariant W) :
    IsInvariant (V + W) := by
  simp_all [IsInvariant]

lemma IsInvariant.smul {V : EFTLagrangianExclDeriv} (c : ℂ) (hV : IsInvariant V) :
    IsInvariant (c • V) := by
  simp_all [IsInvariant]

lemma IsInvariant.mul {V W : EFTLagrangianExclDeriv} (hV : IsInvariant V) (hW : IsInvariant W) :
    IsInvariant (V * W) := by
  simp_all [IsInvariant, repLorentzGroup_mul, repGaugeGroupI_mul]

@[simp]
lemma IsInvariant.one : IsInvariant 1 := by
  simp [IsInvariant]

lemma IsInvariant.sum {ι : Type} [Fintype ι] {V : ι → EFTLagrangianExclDeriv}
    (hV : ∀ i, IsInvariant (V i)) : IsInvariant (∑ i, V i) := by
  simp_all [IsInvariant]

lemma IsInvariant.of_mem_span {V : EFTLagrangianExclDeriv} {S : Set EFTLagrangianExclDeriv}
    (hS : ∀ W ∈ S, IsInvariant W) (hV : V ∈ Submodule.span ℂ S)  :
    IsInvariant V := by
  induction' hV using Submodule.span_induction with W hW W1 W2 h1 h2 hI1 hI2 a W hW hIW
  · exact hS W hW
  · exact zero
  · exact add hI1 hI2
  · exact smul a hIW

/-!

## The elements of the EFT generated by the field generators

Every element of the Field generators gives an element in the
type of EFT lagragians.

-/
/-- The elements of `EFTLagrangianExclDeriv` associated with
  the `FieldGenerators`. -/
def ofFieldGenerators : FieldGenerators → EFTLagrangianExclDeriv
  | .cScalar φ => SymmetricAlgebra.ι ℂ _ (complexScalarComponentBasis φ) ⊗ₜ 1
  | .fermion ψ => 1 ⊗ₜ ExteriorAlgebra.ι ℂ (fermionicComponentBasis ψ)

scoped notation "[" v "]ₐ" => ofFieldGenerators v
scoped notation "[" v "]ₛ" => ofFieldGenerators (FieldGenerators.cScalar v)
scoped notation "[" v "]ₑ" => ofFieldGenerators (FieldGenerators.fermion v)

lemma ofFieldGenerators_cScalar_exists (ϕ : ComplexScalarGenerator) :
    ∃ x, [ϕ]ₛ = SymmetricAlgebra.ι ℂ _ x ⊗ₜ 1 :=
  ⟨complexScalarComponentBasis ϕ, rfl⟩

lemma ofFieldGenerators_fermion_exists (ψ : FermionicGenerator) :
    ∃ x, [ψ]ₑ = 1 ⊗ₜ ExteriorAlgebra.ι ℂ x :=
  ⟨fermionicComponentBasis ψ, rfl⟩

lemma cScalar_comm_cScalar (φ₁ φ₂ : ComplexScalarGenerator) :
    [φ₁]ₛ * [φ₂]ₛ = [φ₂]ₛ * [φ₁]ₛ := by
  obtain ⟨x₁, h1⟩ := ofFieldGenerators_cScalar_exists φ₁
  obtain ⟨x₂, h2⟩ := ofFieldGenerators_cScalar_exists φ₂
  simp [h1, h2, mul_comm]

lemma cScalar_comm_fermion (ϕ : ComplexScalarGenerator) (ψ : FermionicGenerator) :
    [ϕ]ₛ * [ψ]ₑ = [ψ]ₑ * [ϕ]ₛ := by
  obtain ⟨x₁, h1⟩ := ofFieldGenerators_cScalar_exists ϕ
  obtain ⟨x₂, h2⟩ := ofFieldGenerators_fermion_exists ψ
  simp [h1, h2, mul_comm]

lemma cScalar_comm (V : EFTLagrangianExclDeriv) (ϕ : ComplexScalarGenerator) :
    [ϕ]ₛ * V = V * [ϕ]ₛ := by
  obtain ⟨x, h⟩ := ofFieldGenerators_cScalar_exists ϕ
  induction V using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [h, mul_comm]
  | add x y hx hy => simp [mul_add, add_mul, hx, hy]

lemma fermion_comm_cScalar (ψ : FermionicGenerator) (ϕ : ComplexScalarGenerator) :
    [ψ]ₑ * [ϕ]ₛ = [ϕ]ₛ * [ψ]ₑ := by
  obtain ⟨x₁, h1⟩ := ofFieldGenerators_fermion_exists ψ
  obtain ⟨x₂, h2⟩ := ofFieldGenerators_cScalar_exists ϕ
  simp [h1, h2]

lemma fermion_anticomm_fermion (ψ₁ ψ₂ : FermionicGenerator) :
    [ψ₁]ₑ * [ψ₂]ₑ = - [ψ₂]ₑ * [ψ₁]ₑ := by
  obtain ⟨x₁, h1⟩ := ofFieldGenerators_fermion_exists ψ₁
  obtain ⟨x₂, h2⟩ := ofFieldGenerators_fermion_exists ψ₂
  rw [h1, h2, ← TensorProduct.tmul_neg, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul]
  congr 1
  rw [neg_mul, eq_neg_iff_add_eq_zero]
  exact ExteriorAlgebra.ι_add_mul_swap x₁ x₂

@[simp]
lemma fermion_mul_self (ψ : FermionicGenerator) : [ψ]ₑ * [ψ]ₑ = 0 := by
  obtain ⟨x, h⟩ := ofFieldGenerators_fermion_exists ψ
  simp [h]

lemma ofFieldGenerators_comm (ϕ₁ ϕ₂ : FieldGenerators) :
    ∃ c : ℂ, [ϕ₁]ₐ * [ϕ₂]ₐ = c • [ϕ₂]ₐ * [ϕ₁]ₐ ∧ (c = 1 ∨ c = -1) := by
  match ϕ₁, ϕ₂ with
  | .cScalar φ₁, .cScalar φ₂ => exact ⟨1, by simp [cScalar_comm_cScalar]⟩
  | .cScalar _, .fermion ψ => exact ⟨1, by simp [cScalar_comm_fermion]⟩
  | .fermion ψ, .cScalar _ => exact ⟨1, by simp [fermion_comm_cScalar]⟩
  |.fermion ψ₁, .fermion ψ₂ =>
    exact ⟨-1, by rw [fermion_anticomm_fermion]; abel, by simp⟩

/-!

## The lift of a map from the field generators to an algebra homomorphism

-/

open scoped IsMulCommutative in
set_option maxRecDepth 2000 in
/-- The algebra map `EFTLagrangianExclDeriv →ₐ[ℂ] A` determined by the images `F g` of
  the field generators: the images of the bosonic generators pairwise commute and
  commute with the images of the fermionic generators, which pairwise anticommute.
  The bosonic factor lifts through the commutative subalgebra generated by the
  bosonic images. -/
def lift {A : Type} [Ring A] [Algebra ℂ A] (F : FieldGenerators → A)
    (hBB : ∀ g g', Commute (F (.cScalar g)) (F (.cScalar g')))
    (hBF : ∀ g g', Commute (F (.cScalar g)) (F (.fermion g')))
    (hFF : ∀ g g', F (.fermion g) * F (.fermion g') = - (F (.fermion g') * F (.fermion g))) :
    EFTLagrangianExclDeriv →ₐ[ℂ] A :=
  let FB : ComplexScalarGenerator → A := fun g => F (.cScalar g)
  let FF : FermionicGenerator → A := fun g => F (.fermion g)
  have hFF : ∀ g g', FF g * FF g' = - (FF g' * FF g) := hFF
  haveI : IsMulCommutative (Algebra.adjoin ℂ (Set.range FB)) :=
    Algebra.isMulCommutative_adjoin ℂ (by rintro _ ⟨g, rfl⟩ _ ⟨g', rfl⟩; exact hBB g g')
  let fS : ComplexScalarEFTExclDeriv →ₐ[ℂ] Algebra.adjoin ℂ (Set.range FB) :=
    SymmetricAlgebra.lift (complexScalarComponentBasis.constr ℂ fun g =>
      ⟨FB g, Algebra.subset_adjoin ⟨g, rfl⟩⟩)
  Algebra.TensorProduct.lift
    ((Algebra.adjoin ℂ (Set.range FB)).val.comp fS)
    (ExteriorAlgebra.lift ℂ
      ⟨fermionicComponentBasis.constr ℂ FF, fun v => by
        have hdiag : ∀ g, FF g * FF g = 0 := fun g => by
          simpa [← two_smul ℂ] using eq_neg_iff_add_eq_zero.mp (hFF g g)
        rw [Basis.constr_apply_fintype, Finset.sum_mul_sum, ← Fintype.sum_prod_type']
        exact Finset.sum_involution (fun p _ => (p.2, p.1))
          (fun p _ => by rw [smul_mul_smul_comm, smul_mul_smul_comm, hFF p.1 p.2]; module)
          (fun p _ hf hswap => hf (by rw [show p.2 = p.1 from (Prod.ext_iff.mp hswap).1,
            smul_mul_smul_comm, hdiag, smul_zero]))
          (fun p _ => Finset.mem_univ _) (fun p _ => rfl)⟩)
    (fun x y => by
      refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute (fS x).2 ?_).symm
      rintro _ ⟨g, rfl⟩
      induction y using ExteriorAlgebra.induction with
      | algebraMap r => rw [AlgHom.commutes]; exact Algebra.commutes r _
      | ι v =>
        rw [ExteriorAlgebra.lift_ι_apply, Basis.constr_apply_fintype]
        exact Commute.sum_left _ _ _ fun g' _ => (hBF g g').symm.smul_left _
      | mul u w hu hw => rw [map_mul]; exact hu.mul_left hw
      | add u w hu hw => rw [map_add]; exact hu.add_left hw)

/-!

## The elements generated by lists of field generators

-/

/-- The element of `EFTLagrangianExclDeriv` generated from a list of field generators. -/
def termOfList (l : List FieldGenerators) : EFTLagrangianExclDeriv :=
  (l.map ofFieldGenerators).prod

lemma termOfList_cons (ψ : FieldGenerators) (l : List FieldGenerators) :
    termOfList (ψ :: l) = [ψ]ₐ * termOfList l := by simp [termOfList]

lemma termOfList_nil : termOfList [] = 1 := by simp [termOfList]

lemma termOfList_append (l1 l2 : List FieldGenerators) :
    termOfList (l1 ++ l2) = termOfList l1 * termOfList l2 := by
  simp [termOfList]

lemma termOfList_perm {l1 l2 : List FieldGenerators} (h : l1.Perm l2) :
    ∃ c : ℂ, termOfList l1 = c • termOfList l2 ∧ (c = 1 ∨ c = -1) := by
  induction h with
  | nil => exact ⟨1, by simp⟩
  | cons x _ ih =>
    obtain ⟨c, hc1, hc2⟩ := ih
    exact ⟨c, by rw [termOfList_cons, termOfList_cons, hc1, mul_smul_comm], hc2⟩
  | swap x y l =>
    obtain ⟨c, hc1, hc2⟩ := ofFieldGenerators_comm y x
    refine ⟨c, ?_⟩
    rw [termOfList_cons, termOfList_cons, termOfList_cons, termOfList_cons, ← mul_assoc]
    simp [hc1, mul_assoc, smul_mul_assoc]
    exact hc2
  | trans _ _ ih1 ih2 =>
    obtain ⟨c1, hc1, hc1'⟩ := ih1
    obtain ⟨c2, hc2, hc2'⟩ := ih2
    exact ⟨c1 * c2, by rw [hc1, hc2, smul_smul], by grind⟩

lemma fermion_mul_termOfList_of_mem (ψ : FermionicGenerator) (l : List FieldGenerators)
    (hψ : .fermion ψ ∈ l) : [ψ]ₑ * termOfList l = 0 := by
  induction l with
  | nil => simp at hψ
  | cons β t ih =>
    rcases List.mem_cons.mp hψ with rfl | ha
    · simp [termOfList_cons, ← mul_assoc]
    · obtain ⟨c, hc1, hc2⟩ := ofFieldGenerators_comm (.fermion ψ) β
      simp [termOfList_cons, ← mul_assoc, hc1]
      simp [mul_assoc, ih ha]

lemma termOfList_filter_isBoson_comm (l : List FieldGenerators) (V : EFTLagrangianExclDeriv) :
    termOfList (l.filter FieldGenerators.IsBoson) * V =
    V * termOfList (l.filter FieldGenerators.IsBoson) := by
  induction l with
  | nil => simp [termOfList]
  | cons ψ t ih =>
    match ψ with
    | .cScalar ϕ =>
      simp [termOfList_cons, cScalar_comm, mul_assoc]
      simp [← mul_assoc, ih]
    | .fermion ψ => simpa using ih

lemma termOfList_eq_isBoson_mul_isFermion (l : List FieldGenerators) :
    termOfList l = termOfList (l.filter FieldGenerators.IsBoson) *
      termOfList (l.filter FieldGenerators.IsFermion) := by
  induction l with
  | nil => simp [termOfList]
  | cons ψ t ih =>
    match ψ with
    | .cScalar ϕ => simp [termOfList_cons, ih, mul_assoc]
    | .fermion ψ =>
      simp [termOfList_cons, ih, ← mul_assoc, termOfList_filter_isBoson_comm]
      simp [mul_assoc, termOfList_filter_isBoson_comm]

lemma termOfList_reverse_eq_of_eq {l1 l2 : List FieldGenerators} {c : ℂ}
    (h : termOfList l1 = c • termOfList l2) :
    termOfList l1.reverse = c • termOfList l2.reverse := by
  let r : EFTLagrangianExclDeriv →ₗ[ℂ] EFTLagrangianExclDeriv :=
    TensorProduct.map LinearMap.id CliffordAlgebra.reverse
  have hmul : ∀ x y : EFTLagrangianExclDeriv, r (x * y) = r y * r x := by
    intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a' b' =>
        simp [r, CliffordAlgebra.reverse.map_mul, mul_comm]
      | add y₁ y₂ h₁ h₂ => simp [mul_add, add_mul, h₁, h₂]
    | add x₁ x₂ h₁ h₂ => simp [mul_add, add_mul, h₁, h₂]
  have hgen : ∀ ψ : FieldGenerators, r [ψ]ₐ = [ψ]ₐ := by
    rintro (ϕ | ψ) <;> simp [r, ofFieldGenerators, CliffordAlgebra.reverse_ι]
  have hf : ∀ l : List FieldGenerators, r (termOfList l) = termOfList l.reverse := by
    intro l
    induction l with
    | nil => simp [r, termOfList_nil, Algebra.TensorProduct.one_def]
    | cons ψ t ih =>
      rw [termOfList_cons, hmul, ih, hgen, List.reverse_cons, termOfList_append]
      simp [termOfList]
  rw [← hf, ← hf, h, map_smul]

lemma termOfList_conjugate_eq_of_eq {l1 l2 : List FieldGenerators} {c : ℂ}
    (h : termOfList l1 = c • termOfList l2) :
    termOfList (l1.map FieldGenerators.conjugate) =
      c • termOfList (l2.map FieldGenerators.conjugate) := by
  -- Conjugation of generators induces an algebra endomorphism, acting on each
  -- tensor factor by the basis permutation `g ↦ g.conjugate`.
  let f : EFTLagrangianExclDeriv →ₐ[ℂ] EFTLagrangianExclDeriv :=
    Algebra.TensorProduct.map
      (SymmetricAlgebra.lift (SymmetricAlgebra.ι ℂ _ ∘ₗ
        complexScalarComponentBasis.constr ℂ fun g => complexScalarComponentBasis g.conjugate))
      (ExteriorAlgebra.map (fermionicComponentBasis.constr ℂ fun g =>
        fermionicComponentBasis g.conjugate))
  have hgen : ∀ g : FieldGenerators, f [g]ₐ = [g.conjugate]ₐ := by
    rintro (g | g) <;>
      simp [f, ofFieldGenerators, FieldGenerators.conjugate, ExteriorAlgebra.map_apply_ι]
  have hf : ∀ l : List FieldGenerators,
      f (termOfList l) = termOfList (l.map FieldGenerators.conjugate) := by
    intro l
    induction l with
    | nil => simp [termOfList_nil]
    | cons g t ih => rw [termOfList_cons, map_mul, ih, hgen, List.map_cons, termOfList_cons]
  rw [← hf, ← hf, h, map_smul]

/-- The elements of type `termOfList` span `EFTLagrangianExclDeriv`. -/
lemma mem_termOfList_span (V : EFTLagrangianExclDeriv) :
    V ∈ Submodule.span ℂ (Set.range termOfList) := by
  have hmul_mem : ∀ x y : EFTLagrangianExclDeriv,
      x ∈ Submodule.span ℂ (Set.range termOfList) →
      y ∈ Submodule.span ℂ (Set.range termOfList) →
      x * y ∈ Submodule.span ℂ (Set.range termOfList) := fun x y hx hy => by
    have h := Submodule.mul_mem_mul hx hy
    rw [Submodule.span_mul_span] at h
    refine Submodule.span_mono ?_ h
    rintro _ ⟨_, ⟨l1, rfl⟩, _, ⟨l2, rfl⟩, rfl⟩
    exact ⟨l1 ++ l2, termOfList_append l1 l2⟩
  have hgen : ∀ g : FieldGenerators, [g]ₐ ∈ Submodule.span ℂ (Set.range termOfList) :=
    fun g => Submodule.subset_span ⟨[g], by simp [termOfList]⟩
  induction V using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul a b =>
    -- The bosonic factor: `a ⊗ₜ 1` lies in the span.
    have h1 : (a ⊗ₜ[ℂ] 1 : EFTLagrangianExclDeriv) ∈
        Submodule.span ℂ (Set.range termOfList) := by
      induction a using SymmetricAlgebra.induction with
      | algebraMap c =>
        simpa [termOfList, Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def,
          TensorProduct.smul_tmul'] using
          Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_range_self (f := termOfList) []))
      | ι x =>
        rw [← Basis.sum_repr complexScalarComponentBasis x, map_sum, TensorProduct.sum_tmul]
        refine Submodule.sum_mem _ fun i _ => ?_
        rw [map_smul, ← TensorProduct.smul_tmul']
        exact Submodule.smul_mem _ _ (hgen (.cScalar i))
      | mul a₁ a₂ h₁ h₂ => simpa using hmul_mem _ _ h₁ h₂
      | add a₁ a₂ h₁ h₂ => rw [TensorProduct.add_tmul]; exact Submodule.add_mem _ h₁ h₂
    -- The fermionic factor: `1 ⊗ₜ b` lies in the span.
    have h2 : (1 ⊗ₜ[ℂ] b : EFTLagrangianExclDeriv) ∈
        Submodule.span ℂ (Set.range termOfList) := by
      induction b using ExteriorAlgebra.induction with
      | algebraMap c =>
        simpa [termOfList, Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def,
          TensorProduct.tmul_smul] using
          Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_range_self (f := termOfList) []))
      | ι x =>
        rw [← Basis.sum_repr fermionicComponentBasis x, map_sum, TensorProduct.tmul_sum]
        refine Submodule.sum_mem _ fun i _ => ?_
        rw [map_smul, TensorProduct.tmul_smul]
        exact Submodule.smul_mem _ _ (hgen (.fermion i))
      | mul b₁ b₂ h₁ h₂ => simpa using hmul_mem _ _ h₁ h₂
      | add b₁ b₂ h₁ h₂ => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ h₁ h₂
    simpa using hmul_mem _ _ h1 h2

/-- The linear map `EFTLagrangianExclDeriv →ₗ[ℂ] A` determined by the values `F l` on
  the spanning terms `termOfList l`, provided `F` respects the scaling relations that
  hold among the terms. -/
noncomputable def liftLinear {A : Type} [Ring A] [Algebra ℂ A] (F : List FieldGenerators → A)
    (hscale : ∀ (l1 l2 : List FieldGenerators) (c : ℂ),
      termOfList l1 = c • termOfList l2 → F l1 = c • F l2) :
    EFTLagrangianExclDeriv →ₗ[ℂ] A :=
  let π : (List FieldGenerators →₀ ℂ) →ₗ[ℂ] EFTLagrangianExclDeriv :=
    Finsupp.linearCombination ℂ termOfList
  let φ : (List FieldGenerators →₀ ℂ) →ₗ[ℂ] A :=
    Finsupp.linearCombination ℂ F
  have hπ : Function.Surjective π :=
    LinearMap.range_eq_top.mp (by
      rw [Finsupp.range_linearCombination, eq_top_iff]
      exact fun V _ => mem_termOfList_span V)
  have hker : LinearMap.ker π ≤ LinearMap.ker φ := by

    sorry
  ((LinearMap.ker π).liftQ φ hker).comp (π.quotKerEquivOfSurjective hπ).symm.toLinearMap

lemma liftLinear_of_eq (A : Type) [Ring A] [Algebra ℂ A] (F : List FieldGenerators → A)
    (hscale : ∀ (l1 l2 : List FieldGenerators) (c : ℂ),
      termOfList l1 = c • termOfList l2 → F l1 = c • F l2) (l : List FieldGenerators) :
    liftLinear F hscale (termOfList l) = F l := by
  have h : termOfList l =
      Finsupp.linearCombination ℂ termOfList (Finsupp.single l 1) := by
    simp
  simp only [liftLinear, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [h, LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
  simp

end EFTLagrangianExclDeriv
