/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.MatrixRep.Factors
public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeFieldData.Basic
public import Physlib.Relativity.Fermions.Weyl.LeftHanded
public import Physlib.Relativity.Fermions.Weyl.RightHanded
/-!
# Model tables

## i. Overview

A gauge-theory model is written down, as in a model-building tool, as a *table*: the gauge
group as a list of factors, and one row per field recording its number of generations,
its Lorentz character and one charge per factor — an integer charge under a `U(1)` factor,
a representation label under an `SU(n)` factor.

This file defines the tables over any local gauge data and compiles them into the general
theory. A gauge group is a list of `Factor`s, each a `U1Factor` or an `SUFactor` of the
local gauge data; the charges of a row form the tuple `Charges Γ` over the list, so that a
row reads `(1, .fund, .fund)`; the charges name a matrix representation `Charges.rep`,
assembled from the factors by the hypercharge twist and the Kronecker product; a row
compiles to a `MatterField` and a table to a `GaugeFieldData`.

## ii. Key results

- `LocalGaugeData.Factor`, `Factors` : a gauge group presented as a list of factors.
- `SURep`, `Charges` : the charge labels of a row and the charge tuple.
- `Charges.rep` : the matrix representation named by a charge tuple.
- `FermionRow`, `ScalarRow`, `Table` : the rows and the table.
- `FermionRow.matterField`, `ScalarRow.matterField`, `Table.fieldData` : the compilation.

## iii. Table of contents

- A. Factors and charge labels
- B. Charge tuples and their internal index
- C. The representation named by a charge tuple
- D. The rows and their matter fields
- E. The table and its field content

-/

@[expose] public section

open Matrix MatrixGroups TensorProduct

namespace LocalGaugeData

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]

/-!

## A. Factors and charge labels

-/

/-- **A factor of the gauge group**, presented in the local gauge data: a `U(1)` factor or
  an `SU(n)` factor. -/
inductive Factor (jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J)
  /-- A `U(1)` factor. -/
  | U1 (F : U1Factor jets)
  /-- An `SU(n)` factor. -/
  | SU {n : ℕ} (F : SUFactor jets (Fin n))

/-- **A gauge group presented by its factors.** -/
abbrev Factors (jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J) : Type := List (Factor jets)

/-- **A representation label under `SU(n)`.** -/
inductive SURep
  /-- The singlet `1`. -/
  | singlet
  /-- The fundamental `n`. -/
  | fund
  /-- The antifundamental `n̄`. -/
  | antifund
  deriving DecidableEq, Repr

/-- The dimension of the representation of `SU(n)` a label names. -/
abbrev SURep.dim (n : ℕ) : SURep → ℕ
  | .singlet => 1
  | .fund => n
  | .antifund => n

variable {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J}

/-- The matrix representation of an `SU(n)` factor named by a label. -/
noncomputable def SURep.rep {n : ℕ} (F : SUFactor jets (Fin n)) :
    (r : SURep) → MatrixRep jets (Fin (r.dim n))
  | .singlet => MatrixRep.trivial
  | .fund => F.fund
  | .antifund => F.fund.conj

/-- The charge a field carries under a factor: an integer under `U(1)`, a representation
  label under `SU(n)`. -/
abbrev Factor.Charge : Factor jets → Type
  | .U1 _ => ℤ
  | .SU _ => SURep

/-!

## B. Charge tuples and their internal index

-/

/-- **The charge tuple** of a row: one charge per factor, as a nested pair so that a row
  reads `(1, .fund, .fund)`. -/
abbrev Charges : Factors jets → Type
  | [] => Unit
  | [f] => f.Charge
  | f :: g :: gs => f.Charge × Charges (g :: gs)

/-- **The internal index** of a field with the given charges: the product of the
  `SU(n)`-representation indices; `U(1)` factors contribute no index. (A definition rather
  than an abbreviation, so that instance search on `Idx Γ c` finds the instances below
  instead of unfolding into a stuck match on `Γ`.) -/
def Idx : (Γ : Factors jets) → Charges Γ → Type
  | [], _ => Fin 1
  | [.U1 _], _ => Fin 1
  | [.SU (n := n) _], r => Fin (r.dim n)
  | .U1 _ :: g :: gs, c => Idx (g :: gs) c.2
  | .SU (n := n) _ :: g :: gs, c => Fin (c.1.dim n) × Idx (g :: gs) c.2

/-- The index of a charge tuple is finite. -/
@[instance_reducible]
def Idx.fintype : (Γ : Factors jets) → (c : Charges Γ) → Fintype (Idx Γ c)
  | [], _ => inferInstanceAs (Fintype (Fin 1))
  | [.U1 _], _ => inferInstanceAs (Fintype (Fin 1))
  | [.SU (n := n) _], r => inferInstanceAs (Fintype (Fin (r.dim n)))
  | .U1 _ :: g :: gs, c => Idx.fintype (g :: gs) c.2
  | .SU (n := n) _ :: g :: gs, c =>
    letI := Idx.fintype (g :: gs) c.2
    inferInstanceAs (Fintype (Fin (c.1.dim n) × Idx (g :: gs) c.2))

/-- The index of a charge tuple has decidable equality. -/
@[instance_reducible]
def Idx.decidableEq : (Γ : Factors jets) → (c : Charges Γ) → DecidableEq (Idx Γ c)
  | [], _ => inferInstanceAs (DecidableEq (Fin 1))
  | [.U1 _], _ => inferInstanceAs (DecidableEq (Fin 1))
  | [.SU (n := n) _], r => inferInstanceAs (DecidableEq (Fin (r.dim n)))
  | .U1 _ :: g :: gs, c => Idx.decidableEq (g :: gs) c.2
  | .SU (n := n) _ :: g :: gs, c =>
    letI := Idx.decidableEq (g :: gs) c.2
    inferInstanceAs (DecidableEq (Fin (c.1.dim n) × Idx (g :: gs) c.2))

instance (Γ : Factors jets) (c : Charges Γ) : Fintype (Idx Γ c) := Idx.fintype Γ c

instance (Γ : Factors jets) (c : Charges Γ) : DecidableEq (Idx Γ c) := Idx.decidableEq Γ c

/-!

## C. The representation named by a charge tuple

-/

/-- **The matrix representation named by a charge tuple**: the Kronecker product of the
  `SU(n)` representations the labels name, twisted by the charge powers of the `U(1)`
  jets. -/
noncomputable def Charges.rep : (Γ : Factors jets) → (c : Charges Γ) → MatrixRep jets (Idx Γ c)
  | [], _ => MatrixRep.trivial
  | [.U1 F], q => F.charge q MatrixRep.trivial
  | [.SU F], r => SURep.rep F r
  | .U1 F :: g :: gs, c => F.charge c.1 (Charges.rep (g :: gs) c.2)
  | .SU F :: g :: gs, c => (SURep.rep F c.1).kron (Charges.rep (g :: gs) c.2)

/-!

## D. The rows and their matter fields

-/

/-- The chirality of a fermion row: a left- or right-handed Weyl spinor. -/
inductive Chirality
  /-- A left-handed Weyl spinor. -/
  | L
  /-- A right-handed Weyl spinor. -/
  | R
  deriving DecidableEq, Repr

/-- **A fermion row** of a table: the name of the field, its number of generations, its
  chirality and its charges. -/
structure FermionRow (Γ : Factors jets) where
  /-- The name of the field. -/
  name : String
  /-- The number of generations. -/
  generations : ℕ
  /-- The chirality. -/
  chirality : Chirality
  /-- The charges, one per factor. -/
  charges : Charges Γ

/-- **A scalar row** of a table: the name of the field, its number of generations and its
  charges. -/
structure ScalarRow (Γ : Factors jets) where
  /-- The name of the field. -/
  name : String
  /-- The number of generations. -/
  generations : ℕ
  /-- The charges, one per factor. -/
  charges : Charges Γ

instance : Module.Finite ℂ Fermion.LeftHandedWeyl :=
  Module.Finite.of_basis Fermion.LeftHandedWeyl.basis

instance : Module.Finite ℂ Fermion.RightHandedWeyl :=
  Module.Finite.of_basis Fermion.RightHandedWeyl.basis

/-- The mass weight of a fermion, in the units in which a derivative has weight `2`. -/
def fermionMassWeight : ℕ := 3

/-- The mass weight of a scalar, in the units in which a derivative has weight `2`. -/
def scalarMassWeight : ℕ := 2

variable {Γ : Factors jets}

/-- **The matter field of a fermion row**: a Weyl spinor of the row's chirality tensored
  with the internal index of its charges, transforming in the representation the charges
  name, of mass weight `3`. -/
noncomputable def FermionRow.matterField (r : FermionRow Γ) : MatterField jets :=
  match r.chirality with
  | .L => (Charges.rep Γ r.charges).matterField (LinearEquiv.refl ℂ _)
      Fermion.LeftHandedWeyl.rep fermionMassWeight
  | .R => (Charges.rep Γ r.charges).matterField (LinearEquiv.refl ℂ _)
      Fermion.RightHandedWeyl.rep fermionMassWeight

/-- **The matter field of a scalar row**: a Lorentz scalar with the internal index of its
  charges, transforming in the representation the charges name, of mass weight `2`. -/
noncomputable def ScalarRow.matterField (r : ScalarRow Γ) : MatterField jets :=
  (Charges.rep Γ r.charges).matterField (LinearEquiv.refl ℂ _)
    (Representation.trivial ℂ SL(2,ℂ) ℂ) scalarMassWeight

@[simp]
lemma FermionRow.matterField_massWeight (r : FermionRow Γ) :
    r.matterField.massWeight = fermionMassWeight := by
  cases h : r.chirality <;> simp [FermionRow.matterField, h]

@[simp]
lemma ScalarRow.matterField_massWeight (r : ScalarRow Γ) :
    r.matterField.massWeight = scalarMassWeight := rfl

/-!

## E. The table and its field content

-/

/-- **A model table**: the gauge group as a list of factors, the fermion rows and the
  scalar rows. -/
structure Table (jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J) where
  /-- The gauge group. -/
  gauge : Factors jets
  /-- The fermion rows. -/
  fermions : List (FermionRow gauge)
  /-- The scalar rows. -/
  scalars : List (ScalarRow gauge)

namespace Table

variable [Module.Finite ℝ 𝔤] (T : Table jets)

/-- The fermionic species of a table: a fermion row together with a generation. -/
abbrev FermionSpecies : Type :=
  Σ i : Fin T.fermions.length, Fin (T.fermions.get i).generations

/-- The bosonic species of a table: a scalar row together with a generation. -/
abbrev BosonSpecies : Type :=
  Σ i : Fin T.scalars.length, Fin (T.scalars.get i).generations

/-- **The field content of a table**: one matter field per species. -/
noncomputable def fieldData : GaugeFieldData jets where
  FermionSpecies := T.FermionSpecies
  fermion s := (T.fermions.get s.1).matterField
  BosonSpecies := T.BosonSpecies
  boson s := (T.scalars.get s.1).matterField

@[simp]
lemma fieldData_FermionSpecies : T.fieldData.FermionSpecies = T.FermionSpecies := rfl

@[simp]
lemma fieldData_fermion (s : T.FermionSpecies) :
    T.fieldData.fermion s = (T.fermions.get s.1).matterField := rfl

@[simp]
lemma fieldData_BosonSpecies : T.fieldData.BosonSpecies = T.BosonSpecies := rfl

@[simp]
lemma fieldData_boson (s : T.BosonSpecies) :
    T.fieldData.boson s = (T.scalars.get s.1).matterField := rfl

/-- Every fermionic species of a table has mass weight `3`. -/
lemma fieldData_fermion_massWeight (s : T.FermionSpecies) :
    (T.fieldData.fermion s).massWeight = fermionMassWeight := by simp

/-- Every bosonic species of a table has mass weight `2`. -/
lemma fieldData_boson_massWeight (s : T.BosonSpecies) :
    (T.fieldData.boson s).massWeight = scalarMassWeight := by simp

end Table

end LocalGaugeData
