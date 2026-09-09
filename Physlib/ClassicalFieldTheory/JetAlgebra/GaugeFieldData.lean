/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeBoson.GaugeJetAlgebra.Basic
public import Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.Basic
public import Physlib.ClassicalFieldTheory.JetAlgebra.SpeciesGenerators
/-!
# The field data of a gauge theory and its generator spaces

## i. Overview

A gauge theory is fixed, before any Lagrangian is chosen, by a gauge context and a matter
content. The gauge context is the existing jet data of the gauge group, namely a global
group `G₀` with finite-dimensional real Lie algebra `𝔤`, a jet group `G` with jet Lie
algebra `𝔤J`, and a local-gauge-data package `jets : LocalGaugeData G 𝔤 G₀ 𝔤J` relating them. The
matter content is a finite family of
fermionic species and a finite family of bosonic species, each given by an existing
`MatterField jets`.

`GaugeFieldData jets` bundles the matter content over such a context. From it this file
derives, with no further data,

* the fermionic and bosonic generator spaces, as `SpeciesComponentSpace` of the families
  of value spaces;
* the connection generator space, as the existing `GaugeBoson.JetComponentSpace 𝔤`;
* the Lorentz and jet gauge actions and the mass-weight scaling on those spaces,
  assembled species by species.

The algebra built on the three generator spaces, `GaugeFieldData.LocalFieldAlgebra`, and
its mapping-out universal property are in
`Physlib.ClassicalFieldTheory.JetAlgebra.LocalFieldAlgebra`, which imports this file. The
split is one of subject matter: here the datum and the spaces it determines, there the
algebra of local expressions on them.

It is field and transformation data before a Lagrangian, so packaging the species'
representations separately certifies no physical compatibility between them, and no
invariance is claimed here.

The generator spaces carry derivative symbols of every order and are infinite-dimensional
however few species there are. Finiteness of the species types and of the value spaces is
not inherited by them.

## ii. Key results

- `GaugeFieldData` : the matter content of a gauge theory over a gauge context.
- `GaugeFieldData.FermionGenerators`, `GaugeFieldData.BosonGenerators` : the species
  generator spaces.
- `GaugeFieldData.inclFermion`, `GaugeFieldData.inclBoson` : the inclusion of the
  component space of one species.
- `GaugeFieldData.repLorentzFermion`, `GaugeFieldData.repJetFermion` : the Lorentz and jet
  gauge actions assembled on the generator spaces.
- `GaugeFieldData.massWeightScaleFermion` : the mass-weight scaling carrying the weight of
  each species.

## iii. Table of contents

- A. The gauge context and the field datum
- B. The generator spaces
  - B.1. The species generator spaces
  - B.2. The connection generator space
- C. The transformation data on the generator spaces
  - C.1. The Lorentz action
  - C.2. The jet gauge action
  - C.3. The mass weights

-/

@[expose] public section

open Matrix MatrixGroups TensorProduct

/-!

## A. The gauge context and the field datum

The gauge context is the parameter list of the structure below, namely the two groups, the
two Lie algebras, the supplied local-gauge-data package `jets` and its Taylor–Leibniz law. It is
`jets` that makes `𝔤` the gauge algebra of `G` rather than an unrelated Lie algebra, and
it is supplied rather than inferred, so a second package over the same carriers is a
different context. `GaugeFieldData` adds only the matter content on top of it.

-/

/-- The field data of a gauge theory. Over a gauge context, given by a jet gauge group `G`
  with global group `G₀`, a finite-dimensional real gauge algebra `𝔤` with jet algebra
  `𝔤J` and a local-gauge-data package `jets` over them, it records a finite family of fermionic
  species and a finite family of bosonic species, each given by an existing
  `MatterField jets`.

  Nothing is repeated from `MatterField`, whose fields already carry the value space, the
  Lorentz representation, the local-gauge-data action and the mass weight of a species. Nothing is
  repeated from the gauge context either, and the gauge bosons are not a species, since
  their generator space is determined by `𝔤` alone.

  This is data before a Lagrangian. Collecting representations of the several species does
  not assert that they are jointly consistent. Gauge-Lorentz compatibility, factorization
  of the jet action through its global value, and richness of the jet group are separate
  conditions, none of them imposed here. -/
structure GaugeFieldData {G : Type} [Group G] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [Module.Finite ℝ 𝔤] {G₀ : Type} [Group G₀] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
    (jets : LocalGaugeData G 𝔤 G₀ 𝔤J) where
  /-- The index type of the fermionic species. -/
  FermionSpecies : Type
  [decidableEqFermionSpecies : DecidableEq FermionSpecies]
  [finiteFermionSpecies : Finite FermionSpecies]
  /-- The matter field of each fermionic species. -/
  fermion : FermionSpecies → MatterField jets
  /-- The index type of the bosonic species. -/
  BosonSpecies : Type
  [decidableEqBosonSpecies : DecidableEq BosonSpecies]
  [finiteBosonSpecies : Finite BosonSpecies]
  /-- The matter field of each bosonic species. -/
  boson : BosonSpecies → MatterField jets

attribute [instance] GaugeFieldData.decidableEqFermionSpecies
  GaugeFieldData.finiteFermionSpecies GaugeFieldData.decidableEqBosonSpecies
  GaugeFieldData.finiteBosonSpecies

namespace GaugeFieldData

variable {G : Type} [Group G] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Finite ℝ 𝔤]
  {G₀ : Type} [Group G₀] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {jets : LocalGaugeData G 𝔤 G₀ 𝔤J} (T : GaugeFieldData jets)

/-!

## B. The generator spaces

### B.1. The species generator spaces

-/

/-- The value space of a fermionic species. -/
abbrev FermionValue (i : T.FermionSpecies) : Type := (T.fermion i).V

/-- The value space of a bosonic species. -/
abbrev BosonValue (j : T.BosonSpecies) : Type := (T.boson j).V

/-- The fermionic generator space of the datum, holding the component functions `∂_s ψ_α`
  and their conjugates of every fermionic species at once, as a direct sum over the
  species. The direct sum, rather than a single component space on the product of the
  value spaces, is what lets the species carry different mass weights. -/
abbrev FermionGenerators : Type := SpeciesComponentSpace T.FermionValue

/-- The bosonic generator space of the datum, assembled from the bosonic species in
  the same way. -/
abbrev BosonGenerators : Type := SpeciesComponentSpace T.BosonValue

/-- The inclusion of the component space of one fermionic species into the fermionic
  generator space. -/
abbrev inclFermion (i : T.FermionSpecies) :
    JetComponentSpace (T.FermionValue i) →ₗ[ℂ] T.FermionGenerators :=
  SpeciesComponentSpace.incl T.FermionValue i

/-- The inclusion of the component space of one bosonic species into the bosonic generator
  space. -/
abbrev inclBoson (j : T.BosonSpecies) :
    JetComponentSpace (T.BosonValue j) →ₗ[ℂ] T.BosonGenerators :=
  SpeciesComponentSpace.incl T.BosonValue j

/-!

### B.2. The connection generator space

The connection is not a species. It is fixed by the gauge context alone, and its component
functions `∂_s A_μ^φ` are the existing `GaugeBoson.JetComponentSpace 𝔤`, used below
without a new name. They are real, a connection being a real object, which is why the
third generator family of the local field algebra is a real vector space, complexified
once inside the algebra. Finite dimensionality of `𝔤` is what makes `Module.Dual ℝ 𝔤` the
span of the adjoint components, so that these generators really are the `A_μ^a`.

## C. The transformation data on the generator spaces

The datum supplies, per species, a Lorentz representation and a fibrewise action of the
gauge jets. Both land on the generator spaces species by species, so both are assembled by
`SpeciesComponentSpace.rep`. Nothing here asserts that the two actions commute, since
Lorentz transformations act on nonconstant gauge jets, and nothing extends them to the
algebra `J(T)`.

### C.1. The Lorentz action

-/

/-- The Lorentz action on the fermionic generator space, acting on each species through
  the Lorentz representation of its matter field. -/
noncomputable def repLorentzFermion : Representation ℂ SL(2,ℂ) T.FermionGenerators :=
  SpeciesComponentSpace.rep T.FermionValue fun i =>
    JetComponentSpace.repLorentzGroup (T.fermion i).repLorentz

/-- The Lorentz action on the bosonic generator space. -/
noncomputable def repLorentzBoson : Representation ℂ SL(2,ℂ) T.BosonGenerators :=
  SpeciesComponentSpace.rep T.BosonValue fun j =>
    JetComponentSpace.repLorentzGroup (T.boson j).repLorentz

variable {T}

@[simp]
lemma repLorentzFermion_inclFermion (Λ : SL(2,ℂ)) (i : T.FermionSpecies)
    (x : JetComponentSpace (T.FermionValue i)) :
    T.repLorentzFermion Λ (T.inclFermion i x)
      = T.inclFermion i (JetComponentSpace.repLorentzGroup (T.fermion i).repLorentz Λ x) :=
  SpeciesComponentSpace.rep_incl _ Λ i x

@[simp]
lemma repLorentzBoson_inclBoson (Λ : SL(2,ℂ)) (j : T.BosonSpecies)
    (y : JetComponentSpace (T.BosonValue j)) :
    T.repLorentzBoson Λ (T.inclBoson j y)
      = T.inclBoson j (JetComponentSpace.repLorentzGroup (T.boson j).repLorentz Λ y) :=
  SpeciesComponentSpace.rep_incl _ Λ j y

variable (T)

/-!

### C.2. The jet gauge action

-/

/-- The action of the jet gauge group on the fermionic generator space, acting on each
  species through the fibrewise jet action of its matter field. Both the fibrewise
  hypothesis and the finite dimensionality of the value space that
  `JetComponentSpace.repJet` needs are already fields of `MatterField`. -/
noncomputable def repJetFermion : Representation ℂ G T.FermionGenerators :=
  SpeciesComponentSpace.rep T.FermionValue fun i =>
    JetComponentSpace.repJet (T.fermion i).repJet (T.fermion i).repJet_smul

/-- The action of the jet gauge group on the bosonic generator space. -/
noncomputable def repJetBoson : Representation ℂ G T.BosonGenerators :=
  SpeciesComponentSpace.rep T.BosonValue fun j =>
    JetComponentSpace.repJet (T.boson j).repJet (T.boson j).repJet_smul

variable {T}

@[simp]
lemma repJetFermion_inclFermion (U : G) (i : T.FermionSpecies)
    (x : JetComponentSpace (T.FermionValue i)) :
    T.repJetFermion U (T.inclFermion i x)
      = T.inclFermion i
        (JetComponentSpace.repJet (T.fermion i).repJet (T.fermion i).repJet_smul U x) :=
  SpeciesComponentSpace.rep_incl _ U i x

@[simp]
lemma repJetBoson_inclBoson (U : G) (j : T.BosonSpecies)
    (y : JetComponentSpace (T.BosonValue j)) :
    T.repJetBoson U (T.inclBoson j y)
      = T.inclBoson j
        (JetComponentSpace.repJet (T.boson j).repJet (T.boson j).repJet_smul U y) :=
  SpeciesComponentSpace.rep_incl _ U j y

variable (T)

/-!

### C.3. The mass weights

-/

/-- The mass-weight scaling on the fermionic generator space, with the weight of each
  species taken from its matter field. Species of different weight scale differently,
  which is the property the direct-sum generator space was chosen to have. -/
noncomputable def massWeightScaleFermion (c : ℂ) :
    T.FermionGenerators →ₗ[ℂ] T.FermionGenerators :=
  SpeciesComponentSpace.massWeightScale T.FermionValue
    (fun i => (T.fermion i).massWeight) c

/-- The mass-weight scaling on the bosonic generator space. -/
noncomputable def massWeightScaleBoson (c : ℂ) :
    T.BosonGenerators →ₗ[ℂ] T.BosonGenerators :=
  SpeciesComponentSpace.massWeightScale T.BosonValue (fun j => (T.boson j).massWeight) c

variable {T}

/-- On the summand of a fermionic species the scaling is that species' own mass-weight
  scaling, with the weight recorded in its matter field. -/
@[simp]
lemma massWeightScaleFermion_inclFermion (c : ℂ) (i : T.FermionSpecies)
    (x : JetComponentSpace (T.FermionValue i)) :
    T.massWeightScaleFermion c (T.inclFermion i x)
      = T.inclFermion i
        (JetComponentSpace.massWeightScale (T.fermion i).massWeight c x) :=
  SpeciesComponentSpace.massWeightScale_incl _ c i x

/-- On the summand of a bosonic species the scaling is that species' own mass-weight
  scaling. -/
@[simp]
lemma massWeightScaleBoson_inclBoson (c : ℂ) (j : T.BosonSpecies)
    (y : JetComponentSpace (T.BosonValue j)) :
    T.massWeightScaleBoson c (T.inclBoson j y)
      = T.inclBoson j (JetComponentSpace.massWeightScale (T.boson j).massWeight c y) :=
  SpeciesComponentSpace.massWeightScale_incl _ c j y

/-- A component function `∂_s ψ_α` of a fermionic species scales by `c ^ (w + 2 |s|)`,
  where `w` is the mass weight of that species. There is one factor of `c` per unit of
  mass dimension of the field and two per derivative. -/
lemma massWeightScaleFermion_inclFermion_basis_tmul (c : ℂ) (i : T.FermionSpecies)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (T.FermionValue i)) :
    T.massWeightScaleFermion c (T.inclFermion i
        ((DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ, 0) : JetComponentSpace (T.FermionValue i)))
      = c ^ ((T.fermion i).massWeight + 2 * Multiset.card s) • T.inclFermion i
          ((DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ, 0) : JetComponentSpace (T.FermionValue i)) :=
  SpeciesComponentSpace.massWeightScale_incl_basis_tmul _ c i s φ

/-- A component function `∂_s φ_α` of a bosonic species scales by `c ^ (w + 2 |s|)`
  with that species' own weight `w`. -/
lemma massWeightScaleBoson_inclBoson_basis_tmul (c : ℂ) (j : T.BosonSpecies)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (T.BosonValue j)) :
    T.massWeightScaleBoson c (T.inclBoson j
        ((DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ, 0) : JetComponentSpace (T.BosonValue j)))
      = c ^ ((T.boson j).massWeight + 2 * Multiset.card s) • T.inclBoson j
          ((DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ, 0) : JetComponentSpace (T.BosonValue j)) :=
  SpeciesComponentSpace.massWeightScale_incl_basis_tmul _ c j s φ

end GaugeFieldData
