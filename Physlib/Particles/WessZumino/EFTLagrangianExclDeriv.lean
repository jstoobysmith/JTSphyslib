/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Jinzheng Li, Nathaneal Sajan
-/
module

public import Physlib.Relativity.Fermions.Weyl.Metric
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

# The Wess-Zumino EFT Lagrangian without derivatives

## i. Overview

The Wess-Zumino theory is a simple field theory consisting
of a single left-handed Weyl fermion and a single complex scalar field.
Sometimes the complex scalar field is replaced by a pair of real scalar fields.

The theory is of physical interest, because it simple example of a theory
permitting a supersymmetry. In this file we don't consider the supersymmetric nature
of the theory.

-/

@[expose] public section

namespace WessZumino
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

## The input data for Fermions

For the Wess-Zumino theory there is a single left-handed Weyl fermion.

-/

/-- The irreducible representations of the fermion field
  under the Lorentz group. -/
inductive FermionIrrep
  | ψ : FermionIrrep
deriving DecidableEq, Fintype

def FermionIrrep.components : FermionIrrep → Type
  | .ψ => Fin 2

instance : (φ : FermionIrrep) → Fintype (FermionIrrep.components φ)
  | .ψ => inferInstanceAs (Fintype (Fin 2))

instance : (φ : FermionIrrep) → DecidableEq (FermionIrrep.components φ)
  | .ψ => inferInstanceAs (DecidableEq (Fin 2))

def FermionIrrep.module : FermionIrrep → Type
  | .ψ => LeftHandedWeyl

instance : (φ : FermionIrrep) →  AddCommGroup (FermionIrrep.module φ)
  | .ψ => inferInstanceAs (AddCommGroup LeftHandedWeyl)

instance : (φ : FermionIrrep) →  Module ℂ (FermionIrrep.module φ)
  | .ψ => inferInstanceAs (Module ℂ LeftHandedWeyl)

def FermionIrrep.basis  : (φ : FermionIrrep) →
    Basis (FermionIrrep.components φ) ℂ (FermionIrrep.module φ)
  | .ψ => LeftHandedWeyl.basis

def FermionIrrep.rep : (φ : FermionIrrep) → Representation ℂ SL(2,ℂ) (FermionIrrep.module φ)
  | .ψ => LeftHandedWeyl.rep

/-!

## Derived Fermionic quantities

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

def FermionicTargetSpace.rep : Representation ℂ SL(2,ℂ) FermionicTargetSpace where
  toFun Λ := LinearMap.piMap fun φ => FermionIrrep.rep φ Λ
  map_one' := by
    ext x i y
    simp only [map_one, LinearMap.coe_comp, LinearMap.coe_piMap, LinearMap.coe_single,
      Function.comp_apply, Pi.map_apply, Pi.single_eq_same, End.one_apply]
  map_mul' Λ1 Λ2 := by
    ext x i y
    simp

/-- The target space of the fermionic fields, including their conjugates. -/
abbrev FermionicTargetSpaceWithComplex := FermionicTargetSpace ×
  ConjModule FermionicTargetSpace

/-- The representation of the Lorentz group on the fermionic target space:
  the irreps act componentwise on the product of their modules, and by the
  conjugate action on the conjugate factor. -/
def FermionicTargetSpaceWithComplex.rep :
    Representation ℂ SL(2,ℂ) FermionicTargetSpaceWithComplex :=
  (FermionicTargetSpace.rep).prod (FermionicTargetSpace.rep.conj)

abbrev FermionicComponentSpace := Module.Dual ℂ FermionicTargetSpaceWithComplex

def FermionicComponentSpace.rep : Representation ℂ SL(2,ℂ) FermionicComponentSpace :=
  (FermionicTargetSpaceWithComplex.rep).dual

def fermionicComponentBasis : Basis FermionicGenerator ℂ FermionicComponentSpace :=
  ((Pi.basis (fun φ => FermionIrrep.basis φ)).prod
  ((Pi.basis (fun φ => FermionIrrep.basis φ)).conj)).dualBasis.reindex fermionicGeneratorEquiv.symm

abbrev FermionicEFTExclDeriv := ExteriorAlgebra ℂ FermionicComponentSpace

def FermionicEFTExclDeriv.rep : Representation ℂ SL(2,ℂ) FermionicEFTExclDeriv where
  toFun Λ := (ExteriorAlgebra.map (FermionicComponentSpace.rep Λ)).toLinearMap
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
  | φ : ComplexScalarIrrep
deriving DecidableEq, Fintype

def ComplexScalarIrrep.components : ComplexScalarIrrep → Type
  | .φ => Fin 1

instance : (φ : ComplexScalarIrrep) → Fintype (ComplexScalarIrrep.components φ)
  | .φ => inferInstanceAs (Fintype (Fin 1))

instance : (φ : ComplexScalarIrrep) → DecidableEq (ComplexScalarIrrep.components φ)
  | .φ => inferInstanceAs (DecidableEq (Fin 1))

def ComplexScalarIrrep.module : ComplexScalarIrrep → Type
  | .φ => ℂ

instance : (φ : ComplexScalarIrrep) →  AddCommGroup (ComplexScalarIrrep.module φ)
  | .φ => inferInstanceAs (AddCommGroup ℂ)

instance : (φ : ComplexScalarIrrep) →  Module ℂ (ComplexScalarIrrep.module φ)
  | .φ => inferInstanceAs (Module ℂ ℂ)

def ComplexScalarIrrep.basis  : (φ : ComplexScalarIrrep) →
    Basis (ComplexScalarIrrep.components φ) ℂ (ComplexScalarIrrep.module φ)
  | .φ => Basis.singleton (Fin 1) ℂ

def ComplexScalarIrrep.rep : (φ : ComplexScalarIrrep) → Representation ℂ SL(2,ℂ) (ComplexScalarIrrep.module φ)
  | .φ => Representation.trivial ℂ SL(2,ℂ) ℂ

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

def ComplexScalarTargetSpace.rep : Representation ℂ SL(2,ℂ) ComplexScalarTargetSpace where
  toFun Λ := LinearMap.piMap fun φ => ComplexScalarIrrep.rep φ Λ
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

/-- The target space of the fermionic fields, including their conjugates. -/
abbrev ComplexScalarTargetSpaceWithComplex := ComplexScalarTargetSpace ×
  ConjModule ComplexScalarTargetSpace

/-- The representation of the Lorentz group on the fermionic target space:
  the irreps act componentwise on the product of their modules, and by the
  conjugate action on the conjugate factor. -/
def ComplexScalarTargetSpaceWithComplex.rep :
    Representation ℂ SL(2,ℂ) ComplexScalarTargetSpaceWithComplex :=
  (ComplexScalarTargetSpace.rep).prod (ComplexScalarTargetSpace.rep.conj)

abbrev ComplexScalarComponentSpace := Module.Dual ℂ ComplexScalarTargetSpaceWithComplex

def ComplexScalarComponentSpace.rep : Representation ℂ SL(2,ℂ) ComplexScalarComponentSpace :=
  (ComplexScalarTargetSpaceWithComplex.rep).dual

def complexScalarComponentBasis : Basis ComplexScalarGenerator ℂ ComplexScalarComponentSpace :=
  ((Pi.basis (fun φ => ComplexScalarIrrep.basis φ)).prod
  ((Pi.basis (fun φ => ComplexScalarIrrep.basis φ)).conj)).dualBasis.reindex complexScalarGeneratorEquiv.symm

abbrev ComplexScalarEFTExclDeriv := SymmetricAlgebra ℂ ComplexScalarComponentSpace

TODO "Define ComplexScalarEFTExclDeriv.rep"

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

/-- The square-zero condition needed to lift to the exterior algebra holds for every
  vector as soon as the images of the fermionic generators pairwise anticommute:
  expanding in the basis, the diagonal terms vanish (over `ℂ`, `x = -x` forces `x = 0`)
  and the off-diagonal terms cancel in swapped pairs. -/
lemma fermionic_constr_mul_self_eq_zero {A : Type} [Ring A] [Algebra ℂ A]
    (FF : FermionicGenerator → A)
    (hFF : ∀ g g', FF g * FF g' = -(FF g' * FF g)) (v : FermionicComponentSpace) :
    fermionicComponentBasis.constr ℂ FF v * fermionicComponentBasis.constr ℂ FF v = 0 := by
  have hdiag : ∀ g, FF g * FF g = 0 := fun g => by
    have h2 : (2 : ℂ) • (FF g * FF g) = 0 := by
      rw [two_smul]
      exact eq_neg_iff_add_eq_zero.mp (hFF g g)
    calc FF g * FF g = ((2 : ℂ)⁻¹ * 2) • (FF g * FF g) := by norm_num
      _ = (2 : ℂ)⁻¹ • ((2 : ℂ) • (FF g * FF g)) := by rw [mul_smul]
      _ = 0 := by rw [h2, smul_zero]
  rw [← fermionicComponentBasis.sum_repr v, map_sum]
  simp only [map_smul, Basis.constr_basis]
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_involution (fun p _ => (p.2, p.1)) ?_ ?_ (fun p _ => Finset.mem_univ _)
    (fun p _ => rfl)
  · intro p _
    rw [smul_mul_smul_comm, smul_mul_smul_comm, hFF p.1 p.2]
    module
  · intro p _ hf hswap
    apply hf
    have h1 : p.2 = p.1 := (Prod.ext_iff.mp hswap).1
    rw [h1, smul_mul_smul_comm, hdiag, smul_zero]

/-- The algebra map `EFTLagrangianExclDeriv →ₐ[ℂ] A` determined by the images of the
  field generators: the bosonic generators are sent to central elements `FB g` and the
  fermionic generators to pairwise-anticommuting elements `FF g`. -/
def lift {A : Type} [Ring A] [Algebra ℂ A]
    (FB : ComplexScalarGenerator → Subalgebra.center ℂ A)
    (FF : FermionicGenerator → A)
    (hFF : ∀ g g', FF g * FF g' = -(FF g' * FF g)) :
    EFTLagrangianExclDeriv →ₐ[ℂ] A :=
  Algebra.TensorProduct.lift
    ((Subalgebra.center ℂ A).val.comp
      (SymmetricAlgebra.lift (complexScalarComponentBasis.constr ℂ FB)))
    (ExteriorAlgebra.lift ℂ
      ⟨fermionicComponentBasis.constr ℂ FF, fermionic_constr_mul_self_eq_zero FF hFF⟩)
    (fun x y => Subalgebra.mem_center_iff.mp
      (SymmetricAlgebra.lift (complexScalarComponentBasis.constr ℂ FB) x).2 _ |>.symm)


lemma ofFieldGenerators_cScalar_exists (ϕ : ComplexScalarGenerator) :
    ∃ x, [ϕ]ₛ = SymmetricAlgebra.ι ℂ _ x ⊗ₜ 1 := by
  match ϕ with
  | .of φ => exact
    ⟨((Basis.singleton (Fin 1) ℂ).prod (Basis.singleton (Fin 1) ℂ).conj).dualBasis (Sum.inl 0), rfl⟩
  | .barφ => exact
    ⟨((Basis.singleton (Fin 1) ℂ).prod (Basis.singleton (Fin 1) ℂ).conj).dualBasis (Sum.inr 0), rfl⟩

lemma ofFieldGenerators_fermion_exists (ψ : Fermions) :
    ∃ x, [ψ]ₑ = 1 ⊗ₜ ExteriorAlgebra.ι ℂ x := by
  match ψ with
  | .ψ α => exact
    ⟨((LeftHandedWeyl.basis.prod LeftHandedWeyl.basis.conj).dualBasis (Sum.inl α)), rfl⟩
  | .barψ α => exact
    ⟨((LeftHandedWeyl.basis.prod LeftHandedWeyl.basis.conj).dualBasis (Sum.inr α)), rfl⟩

lemma cScalar_comm_cScalar (φ₁ φ₂ : ComplexScalars) :
    [φ₁]ₛ * [φ₂]ₛ = [φ₂]ₛ * [φ₁]ₛ := by
  obtain ⟨x₁, h1⟩ := ofFieldGenerators_cScalar_exists φ₁
  obtain ⟨x₂, h2⟩ := ofFieldGenerators_cScalar_exists φ₂
  simp [h1, h2, mul_comm]

lemma cScalar_comm_fermion (ϕ : ComplexScalars) (ψ : Fermions) :
    [ϕ]ₛ * [ψ]ₑ = [ψ]ₑ * [ϕ]ₛ := by
  obtain ⟨x₁, h1⟩ := ofFieldGenerators_cScalar_exists ϕ
  obtain ⟨x₂, h2⟩ := ofFieldGenerators_fermion_exists ψ
  simp [h1, h2, mul_comm]

lemma cScalar_comm (V : EFTLagrangianExclDeriv) (ϕ : ComplexScalars) :
    [ϕ]ₛ * V = V * [ϕ]ₛ := by
  obtain ⟨x, h⟩ := ofFieldGenerators_cScalar_exists ϕ
  induction V using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [h, mul_comm]
  | add x y hx hy => simp [mul_add, add_mul, hx, hy]

lemma fermion_comm_cScalar (ψ : Fermions) (ϕ : ComplexScalars) :
    [ψ]ₑ * [ϕ]ₛ = [ϕ]ₛ * [ψ]ₑ := by
  obtain ⟨x₁, h1⟩ := ofFieldGenerators_fermion_exists ψ
  obtain ⟨x₂, h2⟩ := ofFieldGenerators_cScalar_exists ϕ
  simp [h1, h2]

lemma fermion_anticomm_fermion (ψ₁ ψ₂ : Fermions) :
    [ψ₁]ₑ * [ψ₂]ₑ = - [ψ₂]ₑ * [ψ₁]ₑ := by
  obtain ⟨x₁, h1⟩ := ofFieldGenerators_fermion_exists ψ₁
  obtain ⟨x₂, h2⟩ := ofFieldGenerators_fermion_exists ψ₂
  rw [h1, h2, ← TensorProduct.tmul_neg, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul]
  congr 1
  rw [neg_mul, eq_neg_iff_add_eq_zero]
  exact ExteriorAlgebra.ι_add_mul_swap x₁ x₂

@[simp]
lemma fermion_mul_self (ψ : Fermions) : [ψ]ₑ * [ψ]ₑ = 0 := by
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

lemma fermion_mul_termOfList_of_mem (ψ : Fermions) (l : List FieldGenerators)
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
    intro ψ
    match ψ with
    | .cScalar ϕ =>
      obtain ⟨x, hx⟩ := ofFieldGenerators_cScalar_exists ϕ
      simp [r, hx]
    | .fermion ψ =>
      obtain ⟨x, hx⟩ := ofFieldGenerators_fermion_exists ψ
      simp [r, hx, CliffordAlgebra.reverse_ι]
  have hf : ∀ l : List FieldGenerators, r (termOfList l) = termOfList l.reverse := by
    intro l
    induction l with
    | nil => simp [r, termOfList_nil, Algebra.TensorProduct.one_def]
    | cons ψ t ih =>
      rw [termOfList_cons, hmul, ih, hgen, List.reverse_cons, termOfList_append]
      simp [termOfList]
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
        have : (algebraMap ℂ _ c ⊗ₜ[ℂ] 1 : EFTLagrangianExclDeriv) = c • termOfList [] := by
          simp [termOfList, Algebra.TensorProduct.one_def, Algebra.algebraMap_eq_smul_one,
            TensorProduct.smul_tmul']
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[], rfl⟩)
      | ι x =>
        rw [← Basis.sum_repr
          (((Basis.singleton (Fin 1) ℂ).prod (Basis.singleton (Fin 1) ℂ).conj).dualBasis) x,
          map_sum, TensorProduct.sum_tmul]
        refine Submodule.sum_mem _ fun i _ => ?_
        rw [map_smul, ← TensorProduct.smul_tmul']
        refine Submodule.smul_mem _ _ ?_
        obtain (i | i) := i <;> fin_cases i
        · exact hgen (.cScalar .φ)
        · exact hgen (.cScalar .barφ)
      | mul a₁ a₂ h₁ h₂ => simpa using hmul_mem _ _ h₁ h₂
      | add a₁ a₂ h₁ h₂ => rw [TensorProduct.add_tmul]; exact Submodule.add_mem _ h₁ h₂
    -- The fermionic factor: `1 ⊗ₜ b` lies in the span.
    have h2 : (1 ⊗ₜ[ℂ] b : EFTLagrangianExclDeriv) ∈
        Submodule.span ℂ (Set.range termOfList) := by
      induction b using ExteriorAlgebra.induction with
      | algebraMap c =>
        have : (1 ⊗ₜ[ℂ] algebraMap ℂ _ c : EFTLagrangianExclDeriv) = c • termOfList [] := by
          simp [termOfList, Algebra.TensorProduct.one_def, Algebra.algebraMap_eq_smul_one,
            TensorProduct.tmul_smul]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[], rfl⟩)
      | ι x =>
        rw [← Basis.sum_repr ((LeftHandedWeyl.basis.prod LeftHandedWeyl.basis.conj).dualBasis) x,
          map_sum, TensorProduct.tmul_sum]
        refine Submodule.sum_mem _ fun i _ => ?_
        rw [map_smul, TensorProduct.tmul_smul]
        refine Submodule.smul_mem _ _ ?_
        obtain (α | α) := i
        · exact hgen (.fermion (.ψ α))
        · exact hgen (.fermion (.barψ α))
      | mul b₁ b₂ h₁ h₂ => simpa using hmul_mem _ _ h₁ h₂
      | add b₁ b₂ h₁ h₂ => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ h₁ h₂
    simpa using hmul_mem _ _ h1 h2

/-!

## The coefficent associated with a multiset of field generators



The below is AI slop, but it shows a useful way od defining the coefficent.

-/

def CoeffSubmodule (s : Multiset FieldGenerators) : Submodule ℂ EFTLagrangianExclDeriv :=
  Submodule.span ℂ (termOfList '' {l | Multiset.ofList l = s})

instance : SetLike.GradedMonoid CoeffSubmodule where
  one_mem := by simp [CoeffSubmodule, termOfList_nil]
  mul_mem s1 s2 V1 V2 hV1 hV2 := by
    have h := Submodule.mul_mem_mul hV1 hV2
    rw [CoeffSubmodule, CoeffSubmodule, Submodule.span_mul_span] at h
    refine Submodule.span_mono ?_ h
    rintro _ ⟨_, ⟨l1, hl1, rfl⟩, _, ⟨l2, hl2, rfl⟩, rfl⟩
    exact ⟨l1 ++ l2, by subst hl1; subst hl2; rfl, termOfList_append l1 l2⟩

open DirectSum

namespace CoeffSubmodule


/-- Transport `DirectSum.of` along an equality of degrees: two homogeneous components with
  equal degrees and equal underlying values are equal. -/
lemma of_eq {s t : Multiset FieldGenerators} (h : s = t)
    {x : CoeffSubmodule s} {y : CoeffSubmodule t}
    (hxy : (x : EFTLagrangianExclDeriv) = y) :
    DirectSum.of (fun u => CoeffSubmodule u) s x = DirectSum.of (fun u => CoeffSubmodule u) t y := by
  subst h
  exact congrArg _ (Subtype.ext hxy)

/-- The class of `termOfList l` in the direct sum of the coefficient submodules, placed
  in degree `↑l`. Note that the membership proof is definitional. -/
def ofList (l : List FieldGenerators) : ⨁ s, CoeffSubmodule s :=
  DirectSum.of (fun s => CoeffSubmodule s) ↑l
    ⟨termOfList l, Submodule.subset_span ⟨l, rfl, rfl⟩⟩

lemma ofList_nil : ofList [] = 1 := by
  simp [ofList, termOfList_nil]
  rfl

lemma ofList_append (l₁ l₂ : List FieldGenerators) :
     ofList (l₁ ++ l₂) = ofList l₁ * ofList l₂ := by
  rw [ofList, ofList, ofList, DirectSum.of_mul_of]
  exact of_eq rfl (by rw [SetLike.coe_gMul]; exact termOfList_append l₁ l₂)


/-- The image of a generator in the direct sum of the coefficient submodules,
  placed in degree `{g}`. -/
def ofGenerator (g : FieldGenerators) : ⨁ s, CoeffSubmodule s := ofList [g]

lemma ofGenerator_comm {g₁ g₂ : FieldGenerators} (h : [g₁]ₐ * [g₂]ₐ = [g₂]ₐ * [g₁]ₐ) :
    ofGenerator g₁ * ofGenerator g₂ = ofGenerator g₂ * ofGenerator g₁ := by
  rw [ofGenerator, ofGenerator, ← ofList_append, ← ofList_append]
  exact of_eq (Multiset.cons_swap g₁ g₂ 0) (by simp [termOfList, h])

lemma fermion_mul_fermion_add_swap (ψ₁ ψ₂ : Fermions) :
    [ψ₁]ₑ * [ψ₂]ₑ + [ψ₂]ₑ * [ψ₁]ₑ = 0 := by
  obtain ⟨x₁, h1⟩ := ofFieldGenerators_fermion_exists ψ₁
  obtain ⟨x₂, h2⟩ := ofFieldGenerators_fermion_exists ψ₂
  rw [h1, h2, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    ← TensorProduct.tmul_add]
  simp

lemma ofList_eq_zero {l : List FieldGenerators} (h : termOfList l = 0) : ofList l = 0 := by
  have hx : (⟨termOfList l, Submodule.subset_span ⟨l, rfl, rfl⟩⟩ : CoeffSubmodule ↑l) = 0 :=
    Subtype.ext h
  rw [ofList, hx, map_zero]

/-- Two `termOfList` classes with the same field content sum to zero as soon as the
  underlying terms do. -/
lemma ofList_add_ofList {l₁ l₂ : List FieldGenerators}
    (hp : (↑l₂ : Multiset FieldGenerators) = ↑l₁)
    (h : termOfList l₁ + termOfList l₂ = 0) : ofList l₁ + ofList l₂ = 0 := by
  have h2 : ofList l₂ = DirectSum.of (fun u => CoeffSubmodule u) ↑l₁
      ⟨termOfList l₂, Submodule.subset_span ⟨l₂, hp, rfl⟩⟩ := of_eq hp rfl
  have hsum : (⟨termOfList l₁, Submodule.subset_span ⟨l₁, rfl, rfl⟩⟩ +
      ⟨termOfList l₂, Submodule.subset_span ⟨l₂, hp, rfl⟩⟩ : CoeffSubmodule ↑l₁) = 0 :=
    Subtype.ext h
  rw [ofList, h2, ← map_add, hsum, map_zero]

lemma ofGenerator_fermion_sq (ψf : Fermions) :
    ofGenerator (.fermion ψf) * ofGenerator (.fermion ψf) = 0 := by
  rw [ofGenerator, ← ofList_append]
  exact ofList_eq_zero (by simp [termOfList])

lemma ofGenerator_fermion_add_swap (ψ₁ ψ₂ : Fermions) :
    ofGenerator (.fermion ψ₁) * ofGenerator (.fermion ψ₂) +
      ofGenerator (.fermion ψ₂) * ofGenerator (.fermion ψ₁) = 0 := by
  rw [ofGenerator, ofGenerator, ← ofList_append, ← ofList_append]
  exact ofList_add_ofList
    (by simpa using List.Perm.swap (FieldGenerators.fermion ψ₁) (.fermion ψ₂) [])
    (by simpa [termOfList] using fermion_mul_fermion_add_swap ψ₁ ψ₂)

/-- The decomposition map on the fermionic factor, sending each fermionic generator to
  its class in degree `{ψ}`. -/
noncomputable def decomposeExt :
    ExteriorAlgebra ℂ (Module.Dual ℂ (LeftHandedWeyl × ConjModule LeftHandedWeyl)) →ₐ[ℂ]
      ⨁ s, CoeffSubmodule s :=
  ExteriorAlgebra.lift ℂ
    ⟨(LeftHandedWeyl.basis.prod LeftHandedWeyl.basis.conj).dualBasis.constr ℂ
        (fun i => ofGenerator (.fermion (Sum.elim Fermions.ψ Fermions.barψ i))), by
      intro m
      -- Generic ring/module lemmas restated locally so that their statements carry the
      -- direct sum's own instances; `rw` can then match where the library patterns cannot.
      have hexpand : ∀ f g : Fin 2 ⊕ Fin 2 → ⨁ s, CoeffSubmodule s,
          (∑ i, f i) * ∑ j, g j = ∑ i, ∑ j, f i * g j := fun f g => Fintype.sum_mul_sum f g
      have hsmul : ∀ (a b : ℂ) (x y : ⨁ s, CoeffSubmodule s),
          (a • x) * (b • y) = (a * b) • (x * y) := fun a b x y => smul_mul_smul_comm a x b y
      have hcollect : ∀ (a : ℂ) (x y : ⨁ s, CoeffSubmodule s),
          a • x + a • y = a • (x + y) := fun a x y => (smul_add a x y).symm
      have hzero : ∀ a : ℂ, a • (0 : ⨁ s, CoeffSubmodule s) = 0 := fun a => smul_zero a
      rw [Basis.constr_apply_fintype, hexpand, ← Finset.sum_product']
      refine Finset.sum_involution (fun p _ => (p.2, p.1)) ?_ ?_
        (fun p _ => Finset.mem_univ _) (fun p _ => rfl)
      · intro p _
        rw [hsmul, hsmul, mul_comm
          ((LeftHandedWeyl.basis.prod LeftHandedWeyl.basis.conj).dualBasis.equivFun m p.2)
          ((LeftHandedWeyl.basis.prod LeftHandedWeyl.basis.conj).dualBasis.equivFun m p.1),
          hcollect, ofGenerator_fermion_add_swap, hzero]
      · intro p _ hne heq
        refine hne ?_
        have h1 : p.2 = p.1 := congrArg Prod.fst heq
        rw [hsmul, h1, ofGenerator_fermion_sq, hzero]⟩

/-- The subalgebra of the graded direct sum generated by the bosonic generator classes.
  It is commutative, which lets `SymmetricAlgebra.lift` target it. -/
noncomputable def bosonicAdjoin : Subalgebra ℂ (⨁ s, CoeffSubmodule s) :=
  Algebra.adjoin ℂ {ofGenerator (.cScalar .φ), ofGenerator (.cScalar .barφ)}

instance : IsMulCommutative bosonicAdjoin :=
  Algebra.isMulCommutative_adjoin ℂ (by
    rintro a (rfl | rfl) b (rfl | rfl)
    · rfl
    · exact ofGenerator_comm (cScalar_comm_cScalar .φ .barφ)
    · exact ofGenerator_comm (cScalar_comm_cScalar .barφ .φ)
    · rfl)

open scoped IsMulCommutative in
/-- The decomposition map on the bosonic factor. Since `SymmetricAlgebra.lift` requires a
  commutative target, we factor through `bosonicAdjoin`. -/
noncomputable def decomposeSym :
    SymmetricAlgebra ℂ (Module.Dual ℂ (ℂ × ConjModule ℂ)) →ₐ[ℂ] ⨁ s, CoeffSubmodule s :=
  bosonicAdjoin.val.comp <| SymmetricAlgebra.lift <|
    ((Basis.singleton (Fin 1) ℂ).prod (Basis.singleton (Fin 1) ℂ).conj).dualBasis.constr ℂ
      (Sum.elim
        (fun _ => ⟨ofGenerator (.cScalar .φ), Algebra.subset_adjoin (Set.mem_insert _ _)⟩)
        (fun _ => ⟨ofGenerator (.cScalar .barφ),
          Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)⟩))

lemma decomposeSym_mem_bosonicAdjoin (x : SymmetricAlgebra ℂ (Module.Dual ℂ (ℂ × ConjModule ℂ))) :
    decomposeSym x ∈ bosonicAdjoin := by
  simp only [decomposeSym, AlgHom.coe_comp, Function.comp_apply, Subalgebra.coe_val]
  exact SetLike.coe_mem _

lemma decomposeExt_ι (v : Module.Dual ℂ (LeftHandedWeyl × ConjModule LeftHandedWeyl)) :
    decomposeExt (ExteriorAlgebra.ι ℂ v) =
      ∑ j, (LeftHandedWeyl.basis.prod LeftHandedWeyl.basis.conj).dualBasis.equivFun v j •
        ofGenerator (.fermion (Sum.elim Fermions.ψ Fermions.barψ j)) := by
  rw [decomposeExt, ExteriorAlgebra.lift_ι_apply, Basis.constr_apply_fintype]

lemma commute_decomposeSym_decomposeExt
    (x : SymmetricAlgebra ℂ (Module.Dual ℂ (ℂ × ConjModule ℂ)))
    (y : ExteriorAlgebra ℂ (Module.Dual ℂ (LeftHandedWeyl × ConjModule LeftHandedWeyl))) :
    Commute (decomposeSym x) (decomposeExt y) := by
  -- Every element of `bosonicAdjoin` commutes with the image of the fermionic factor;
  -- this avoids ever unfolding `decomposeSym`.
  have hgen : ∀ g ∈ ({ofGenerator (.cScalar .φ), ofGenerator (.cScalar .barφ)} :
      Set (⨁ s, CoeffSubmodule s)), Commute g (decomposeExt y) := by
    intro g hg
    induction y using ExteriorAlgebra.induction with
    | algebraMap c => rw [AlgHom.commutes]; exact (Algebra.commutes c g).symm
    | mul y₁ y₂ h₁ h₂ =>
      rw [map_mul]
      exact Commute.mul_right (a := g) (b := decomposeExt y₁) h₁ h₂
    | add y₁ y₂ h₁ h₂ => rw [map_add]; exact h₁.add_right h₂
    | ι v =>
      rw [decomposeExt_ι]
      refine Commute.sum_right (b := g) _ _ fun j _ => ?_
      refine Commute.smul_right (a := g) ?_ _
      rcases hg with rfl | rfl
      · exact ofGenerator_comm (cScalar_comm_fermion _ _)
      · exact ofGenerator_comm (cScalar_comm_fermion _ _)
  have hx := decomposeSym_mem_bosonicAdjoin x
  generalize decomposeSym x = a at hx ⊢
  induction hx using Algebra.adjoin_induction with
  | mem a ha => exact hgen a ha
  | algebraMap c => exact Algebra.commutes c _
  | add a b _ _ h₁ h₂ => exact h₁.add_left h₂
  | mul a b _ _ h₁ h₂ => exact Commute.mul_left (c := decomposeExt y) h₁ h₂

noncomputable def decompose' : EFTLagrangianExclDeriv →ₐ[ℂ] ⨁ s, CoeffSubmodule s :=
  Algebra.TensorProduct.lift decomposeSym decomposeExt commute_decomposeSym_decomposeExt

lemma decomposeSym_ι_basis (j : Fin 1 ⊕ Fin 1) :
    decomposeSym (SymmetricAlgebra.ι ℂ _
      (((Basis.singleton (Fin 1) ℂ).prod (Basis.singleton (Fin 1) ℂ).conj).dualBasis j)) =
      Sum.elim (fun _ => ofGenerator (.cScalar .φ)) (fun _ => ofGenerator (.cScalar .barφ)) j := by
  simp only [decomposeSym, AlgHom.coe_comp, Function.comp_apply, SymmetricAlgebra.lift_ι_apply,
    Basis.constr_basis]
  obtain (j | j) := j <;> rfl

lemma decomposeExt_ι_basis (j : Fin 2 ⊕ Fin 2) :
    decomposeExt (ExteriorAlgebra.ι ℂ
      ((LeftHandedWeyl.basis.prod LeftHandedWeyl.basis.conj).dualBasis j)) =
      ofGenerator (.fermion (Sum.elim Fermions.ψ Fermions.barψ j)) := by
  rw [decomposeExt, ExteriorAlgebra.lift_ι_apply, Basis.constr_basis]

lemma decompose'_ofFieldGenerators (g : FieldGenerators) :
    decompose' [g]ₐ = ofGenerator g := by
  -- Local restatements of `mul_one`/`one_mul` carrying the direct sum's own instances.
  have hmul_one : ∀ x : ⨁ s, CoeffSubmodule s, x * 1 = x := fun x => mul_one x
  have hone_mul : ∀ x : ⨁ s, CoeffSubmodule s, 1 * x = x := fun x => one_mul x
  match g with
  | .cScalar .φ =>
    rw [decompose', show ([ComplexScalars.φ]ₛ : EFTLagrangianExclDeriv) =
        SymmetricAlgebra.ι ℂ _ (((Basis.singleton (Fin 1) ℂ).prod
          (Basis.singleton (Fin 1) ℂ).conj).dualBasis (Sum.inl 0)) ⊗ₜ 1 from rfl,
      Algebra.TensorProduct.lift_tmul, map_one, hmul_one, decomposeSym_ι_basis]
    rfl
  | .cScalar .barφ =>
    rw [decompose', show ([ComplexScalars.barφ]ₛ : EFTLagrangianExclDeriv) =
        SymmetricAlgebra.ι ℂ _ (((Basis.singleton (Fin 1) ℂ).prod
          (Basis.singleton (Fin 1) ℂ).conj).dualBasis (Sum.inr 0)) ⊗ₜ 1 from rfl,
      Algebra.TensorProduct.lift_tmul, map_one, hmul_one, decomposeSym_ι_basis]
    rfl
  | .fermion (.ψ α) =>
    rw [decompose', show ([Fermions.ψ α]ₑ : EFTLagrangianExclDeriv) =
        1 ⊗ₜ ExteriorAlgebra.ι ℂ ((LeftHandedWeyl.basis.prod
          LeftHandedWeyl.basis.conj).dualBasis (Sum.inl α)) from rfl,
      Algebra.TensorProduct.lift_tmul, map_one, hone_mul, decomposeExt_ι_basis]
    rfl
  | .fermion (.barψ α) =>
    rw [decompose', show ([Fermions.barψ α]ₑ : EFTLagrangianExclDeriv) =
        1 ⊗ₜ ExteriorAlgebra.ι ℂ ((LeftHandedWeyl.basis.prod
          LeftHandedWeyl.basis.conj).dualBasis (Sum.inr α)) from rfl,
      Algebra.TensorProduct.lift_tmul, map_one, hone_mul, decomposeExt_ι_basis]
    rfl

lemma decompose'_termOfList (l : List FieldGenerators) :
    decompose' (termOfList l) = ofList l := by
  induction l with
  | nil => rw [termOfList_nil, map_one, ofList_nil]
  | cons g t ih =>
    rw [termOfList_cons, map_mul, ih, decompose'_ofFieldGenerators, ofGenerator,
      ← ofList_append, List.singleton_append]

lemma coeAlgHom_ofList (l : List FieldGenerators) :
    DirectSum.coeAlgHom CoeffSubmodule (ofList l) = termOfList l := by
  rw [ofList]
  exact DirectSum.coeAlgHom_of _ _ _

instance : GradedAlgebra CoeffSubmodule := by
  refine GradedAlgebra.ofAlgHom CoeffSubmodule decompose' ?_ ?_
  · refine AlgHom.ext fun x => ?_
    rw [AlgHom.comp_apply, AlgHom.id_apply]
    induction mem_termOfList_span x using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨l, rfl⟩ := ha
      rw [decompose'_termOfList]
      exact coeAlgHom_ofList l
    | zero => simp
    | add a b _ _ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
    | smul c a _ h₁ => rw [map_smul, map_smul, h₁]
  · intro s x
    obtain ⟨x, hx⟩ := x
    induction hx using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨l, hl, rfl⟩ := ha
      subst hl
      rw [decompose'_termOfList]
      rfl
    | zero => exact (map_zero (DirectSum.of (fun i => CoeffSubmodule i) s)).symm ▸ map_zero _
    | add a b ha hb h₁ h₂ => rw [map_add, h₁, h₂, ← map_add]; rfl
    | smul c a ha h₁ =>
      rw [map_smul, h₁, ← DirectSum.lof_eq_of ℂ, ← map_smul]; rfl


def coeff (s : Multiset FieldGenerators) : EFTLagrangianExclDeriv →ₗ[ℂ] EFTLagrangianExclDeriv:=
  GradedAlgebra.proj CoeffSubmodule s

end CoeffSubmodule


end EFTLagrangianExclDeriv
