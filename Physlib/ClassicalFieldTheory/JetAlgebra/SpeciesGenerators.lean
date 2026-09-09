/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.JetComponentSpace.Basic
public import Mathlib.Algebra.DirectSum.Module
/-!
# The generator spaces of a family of species

## i. Overview

A field theory carries several species of field, each with its own value space, its own
Lorentz representation and its own mass weight. The local field algebra built in
`Physlib.ClassicalFieldTheory.JetAlgebra.LocalFieldAlgebra` is an exterior algebra on one
complex space of fermionic generators tensored with a symmetric algebra on one complex
space of bosonic generators, so a multi-species theory has to present its species as a
single generator space.

This file does that with a direct sum of component spaces. For a family `V : ι → Type` of
value spaces the total generator space is

`SpeciesComponentSpace V = ⨁ i, JetComponentSpace (V i)`,

one `JetComponentSpace` per species, each with its conjugate summand. The alternative, a
single `JetComponentSpace (∀ i, V i)` on the product of the value spaces, is available but
carries only one mass weight, since its scaling commutes with `JetComponentSpace.comap`
and so cannot distinguish the species. The direct sum records one weight per species.

Nothing here is finite. Neither the index type `ι` nor any of the value spaces `V i` is
assumed finite, and the component spaces are infinite-dimensional in any case, since a
derivative label ranges over all multisets of directions. Only `DecidableEq ι` is used,
and only to have the summand inclusions.

The subtle point, settled in `Physlib.Mathematics.AlgebraGeneration` rather than here, is
Fermi statistics. A square-zero condition on the total space is strictly stronger than the
same condition on each species: by `DirectSum.mul_self_iff_lof` it is equivalent to
square-zero on each species together with anticommutation between the images of any two
species. The generator space assembled here is what makes that distinction expressible.

## ii. Key results

- `SpeciesComponentSpace` : the total component space of a family of species.
- `SpeciesComponentSpace.incl`, `SpeciesComponentSpace.assemble`,
  `SpeciesComponentSpace.hom_ext`, `SpeciesComponentSpace.existsUnique_linearMap` : the
  species inclusions and the mapping-out property of the total component space.
- `SpeciesComponentSpace.comap` : functoriality, contravariant in the family of value
  spaces.
- `SpeciesComponentSpace.rep` : the species-diagonal assembly of a family of
  representations on the individual component spaces.
- `SpeciesComponentSpace.massWeightScale` : the mass-weight scaling of a family with one
  weight per species.
- `JetComponentSpace.comap_comp_massWeightScale` : the scaling of a single component
  space is natural in the value space, hence species-blind, which is the reason for the
  direct sum.

## iii. Table of contents

- A. The component space of a family of species
  - A.1. The species inclusions and the assembly of linear maps
  - A.2. Functoriality in the family of value spaces
  - A.3. The species-diagonal representation
  - A.4. Unequal mass weights
  - A.5. Why the weights are recorded per species

-/

@[expose] public section

open TensorProduct DirectSum

/-!

## A. The component space of a family of species

-/

section ComponentSpace

variable {ι : Type*} [DecidableEq ι] (V : ι → Type*)
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- The component space of a family of species, with one `JetComponentSpace` per species,
  each carrying its own conjugate summand, combined by a direct sum. A component function
  of the theory is a finitely supported family of component functions of the species. -/
abbrev SpeciesComponentSpace : Type _ := ⨁ i, JetComponentSpace (V i)

namespace SpeciesComponentSpace

/-!

### A.1. The species inclusions and the assembly of linear maps

-/

/-- The inclusion of a species into the total component space. -/
abbrev incl (i : ι) : JetComponentSpace (V i) →ₗ[ℂ] SpeciesComponentSpace V :=
  DirectSum.lof ℂ ι (fun i => JetComponentSpace (V i)) i

variable {N : Type*} [AddCommMonoid N] [Module ℂ N]

/-- The assembly of a species-wise family of linear maps into a common target. -/
abbrev assemble (f : ∀ i, JetComponentSpace (V i) →ₗ[ℂ] N) :
    SpeciesComponentSpace V →ₗ[ℂ] N :=
  DirectSum.toModule ℂ ι N f

variable {V}

@[simp]
lemma assemble_incl (f : ∀ i, JetComponentSpace (V i) →ₗ[ℂ] N) (i : ι)
    (x : JetComponentSpace (V i)) : assemble V f (incl V i x) = f i x :=
  DirectSum.toModule_lof (M := fun i => JetComponentSpace (V i)) ℂ i x

/-- Two linear maps out of the total component space agreeing on every species are
  equal. -/
lemma hom_ext {F G : SpeciesComponentSpace V →ₗ[ℂ] N}
    (h : ∀ i x, F (incl V i x) = G (incl V i x)) : F = G :=
  DirectSum.linearMap_ext ℂ fun i => LinearMap.ext (h i)

variable (V)

/-- The mapping-out property of the total component space. A species-wise family of linear
  maps into a common target extends to one and only one linear map out of the total
  component space. -/
lemma existsUnique_linearMap (f : ∀ i, JetComponentSpace (V i) →ₗ[ℂ] N) :
    ∃! F : SpeciesComponentSpace V →ₗ[ℂ] N, ∀ i x, F (incl V i x) = f i x :=
  ⟨assemble V f, assemble_incl f, fun _ hF =>
    hom_ext fun i x => (hF i x).trans (assemble_incl f i x).symm⟩

/-!

### A.2. Functoriality in the family of value spaces

Component functions are covectors on the value space, so the total component space is
contravariant in the family of value spaces, exactly as a single one is. The species-wise
pullbacks are the existing `JetComponentSpace.comap`; only the assembly is new.

-/

variable (W : ι → Type*) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- The total component space is contravariant in the family of value spaces. Applied
  to the projections out of a larger family, this is the inclusion of a subfamily of
  species. -/
noncomputable def comap (f : ∀ i, V i →ₗ[ℂ] W i) :
    SpeciesComponentSpace W →ₗ[ℂ] SpeciesComponentSpace V :=
  assemble W fun i => (incl V i).comp (JetComponentSpace.comap (f i))

variable {V W}

@[simp]
lemma comap_incl (f : ∀ i, V i →ₗ[ℂ] W i) (i : ι) (x : JetComponentSpace (W i)) :
    comap V W f (incl W i x) = incl V i (JetComponentSpace.comap (f i) x) :=
  assemble_incl _ i x

@[simp]
lemma comap_id : comap V V (fun _ => LinearMap.id) = LinearMap.id :=
  hom_ext fun i x => by
    rw [comap_incl, JetComponentSpace.comap_id, LinearMap.id_apply, LinearMap.id_apply]

/-- Functoriality, with the order reversing as a contravariant construction demands. -/
lemma comap_comp (U : ι → Type*) [∀ i, AddCommGroup (U i)] [∀ i, Module ℂ (U i)]
    (f : ∀ i, V i →ₗ[ℂ] W i) (g : ∀ i, W i →ₗ[ℂ] U i) :
    comap V U (fun i => (g i).comp (f i)) = (comap V W f).comp (comap W U g) :=
  hom_ext fun i x => by
    rw [comap_incl, JetComponentSpace.comap_comp, LinearMap.comp_apply,
      LinearMap.comp_apply, comap_incl, comap_incl]

/-!

### A.3. The species-diagonal representation

A symmetry of a field theory acts on each species separately, a Lorentz transformation
through that species' Lorentz representation and a gauge jet through that species' jet
action. On the total component space the action is therefore the direct sum of the
species-wise actions, and the representation laws follow from the mapping-out property of
the direct sum alone, with no relation between the species used.

-/

variable (V)

/-- The species-diagonal representation on the total component space assembled from a
  representation on each species' component space. The summands are preserved, so `map_one`
  and `map_mul` reduce by `hom_ext` to the corresponding laws of the species-wise
  representations.

  Both transformation laws a matter species carries are of this form, namely the Lorentz
  action `JetComponentSpace.repLorentzGroup` and the jet gauge action
  `JetComponentSpace.repJet`. Nothing here asks the two to commute, and nothing asks the
  monoid `H` to be related to the species. -/
noncomputable def rep {H : Type*} [Monoid H]
    (ρ : ∀ i, Representation ℂ H (JetComponentSpace (V i))) :
    Representation ℂ H (SpeciesComponentSpace V) where
  toFun g := assemble V fun i => (incl V i).comp (ρ i g)
  map_one' := hom_ext fun i x => by simp
  map_mul' g h := hom_ext fun i x => by simp

variable {V}

/-- The species-diagonal representation acts on the summand of a species through that
  species' representation. -/
@[simp]
lemma rep_incl {H : Type*} [Monoid H] (ρ : ∀ i, Representation ℂ H (JetComponentSpace (V i)))
    (g : H) (i : ι) (x : JetComponentSpace (V i)) :
    rep V ρ g (incl V i x) = incl V i (ρ i g x) :=
  assemble_incl _ i x

/-!

### A.4. Unequal mass weights

The mass weight is a property of a species, not of the theory, a fermion carrying weight
`3` and a scalar weight `2`. The total component space records one weight per species,
and the scaling acts on the summand of a species through that species' weight alone.

-/

variable (V)

/-- The mass-weight scaling of a family of species, with the weight `w i` of each
  species acting on that species' component functions. -/
noncomputable def massWeightScale (w : ι → ℕ) (c : ℂ) :
    SpeciesComponentSpace V →ₗ[ℂ] SpeciesComponentSpace V :=
  assemble V fun i => (incl V i).comp (JetComponentSpace.massWeightScale (w i) c)

variable {V}

@[simp]
lemma massWeightScale_incl (w : ι → ℕ) (c : ℂ) (i : ι) (x : JetComponentSpace (V i)) :
    massWeightScale V w c (incl V i x)
      = incl V i (JetComponentSpace.massWeightScale (w i) c x) :=
  assemble_incl _ i x

/-- On a homogeneous component function `∂_s φ_α` of the species `i` the scaling is
  multiplication by `c ^ (w i + 2 |s|)`, the weight being the weight of that species. -/
lemma massWeightScale_incl_basis_tmul (w : ι → ℕ) (c : ℂ) (i : ι)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (V i)) :
    massWeightScale V w c
        (incl V i ((DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ, 0) : JetComponentSpace (V i)))
      = c ^ (w i + 2 * Multiset.card s) •
        incl V i ((DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ, 0) : JetComponentSpace (V i)) := by
  rw [massWeightScale_incl, ← LinearMap.map_smul]
  refine congrArg _ (Prod.ext ?_ ?_)
  · exact JetComponentSpace.massWeightScale_fst_basis_tmul (w i) c s φ 0
  · simp

/-- The conjugate component functions of a species scale with the same weight as its
  unconjugated ones. -/
lemma massWeightScale_incl_basis_tmul_conj (w : ι → ℕ) (c : ℂ) (i : ι)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule (V i))) :
    massWeightScale V w c
        (incl V i ((0, DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ) : JetComponentSpace (V i)))
      = c ^ (w i + 2 * Multiset.card s) •
        incl V i ((0, DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ) : JetComponentSpace (V i)) := by
  rw [massWeightScale_incl, ← LinearMap.map_smul]
  refine congrArg _ (Prod.ext ?_ ?_)
  · simp
  · simp only [JetComponentSpace.massWeightScale_snd, Prod.smul_snd,
      TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
      DerivAlgebraComplex.gradeScale_basis, LinearMap.id_apply, TensorProduct.smul_tmul',
      ← pow_mul, ← smul_assoc, smul_eq_mul, ← pow_add, mul_comm 2 (Multiset.card s)]

end SpeciesComponentSpace

end ComponentSpace

/-!

### A.5. Why the weights are recorded per species

-/

/-- The mass-weight scaling of a single component space is natural in the value space. It
  therefore cannot see which species a component function came from, so in the alternative
  encoding `JetComponentSpace (∀ i, V i)`, where a species enters through
  `JetComponentSpace.comap (LinearMap.proj i)`, every species is scaled by the same weight.
  That is why the total generator space of this file is a direct sum, with one weight per
  summand.

  The statement is about a single `JetComponentSpace` and would sit more naturally with the
  rest of that API in
  `Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.JetComponentSpace.Basic`; it
  is here because it justifies the choice this file makes. -/
lemma JetComponentSpace.comap_comp_massWeightScale {V W : Type*} [AddCommGroup V]
    [Module ℂ V] [AddCommGroup W] [Module ℂ W] (f : V →ₗ[ℂ] W) (w : ℕ) (c : ℂ) :
    (JetComponentSpace.comap f).comp (JetComponentSpace.massWeightScale w c)
      = (JetComponentSpace.massWeightScale w c).comp (JetComponentSpace.comap f) := by
  simp only [JetComponentSpace.comap, JetComponentSpace.massWeightScale,
    LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.prodMap_comp,
    ← TensorProduct.map_comp, LinearMap.comp_id, LinearMap.id_comp]
