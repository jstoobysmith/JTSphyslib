/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeFieldData.BosonMatterField
/-!
# The bosonic generators as the components of one scalar field

## i. Overview

`GaugeFieldData.BosonGenerators` is built species by species, as the direct sum
`⨁ i, JetComponentSpace (T.boson i).V` of the component spaces of the several scalar
multiplets. A physicist writing a theory down does not do this. They write one scalar
field `φ`, valued in the whole bosonic module, and take its component functions
`∂_s φ_α` — a single `JetComponentSpace`, indexed by a target index `α` that runs over all
the multiplets at once. For the Standard Model, with its one Higgs doublet, the two
descriptions are trivially the same; for a two-Higgs-doublet model or any theory with
several scalars they are not, and the content below is what identifies them.

This file shows that the two agree. When the bosonic species share a mass weight — the
condition under which `GaugeFieldData.bosonMatterField` exists, and the condition a theory
whose scalars all have the same mass dimension satisfies — there is an isomorphism

`T.BosonGenerators ≃ₗ[ℂ] JetComponentSpace T.BosonModule`,

and under it the summand of a species is the pullback along the projection onto that
species, `bosonGeneratorsEquiv_inclBoson`. So the generators of one multiplet sit
inside the generators of the whole scalar field exactly as its target components sit
inside the bosonic module, which is what a physicist means by writing `φ_α` with `α`
ranging over everything.

The isomorphism is not merely one of vector spaces: it intertwines the Lorentz action and
the mass-weight scaling with those of the single matter field
`T.bosonMatterField w h`. The mass weight is where the shared weight `w` is needed and
where the species-by-species construction earns its keep — a family of *unequal* weights
has no single `JetComponentSpace.massWeightScale` to be compared with, which is precisely
the reason `SpeciesComponentSpace` was built as a direct sum in the first place. With one
weight that obstruction is gone and the two descriptions coincide.

The underlying identification is `JetComponentSpace.piEquiv`, composed with the
identification of a direct sum over a finite index with the product.

## ii. Key results

- `GaugeFieldData.bosonGeneratorsEquiv` : the bosonic generator space is the component
  space of the bosonic matter field.
- `GaugeFieldData.bosonGeneratorsEquiv_inclBoson` : a species sits inside it as the
  pullback along the projection onto that species.
- `GaugeFieldData.bosonGeneratorsEquiv_repLorentzBoson` : the identification is
  Lorentz-equivariant.
- `GaugeFieldData.bosonGeneratorsEquiv_massWeightScaleBoson` : it carries the
  species-wise mass-weight scaling to the single scaling of weight `w`.

## iii. Table of contents

- A. The bosonic generators as one component space
  - A.1. The species as pullbacks
  - A.2. The transformation data

-/

@[expose] public section

open Matrix MatrixGroups TensorProduct

namespace GaugeFieldData

variable {G : Type} [Group G] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Finite ℝ 𝔤]
  {G₀ : Type} [Group G₀] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {jets : LocalGaugeData G 𝔤 G₀ 𝔤J} (T : GaugeFieldData jets)

/-!

## A. The bosonic generators as one component space

-/

/-- **The bosonic generator space is the component space of the bosonic module.** The
  direct sum over the species of their component spaces is, the species type being finite,
  the same thing as the space of component functions `∂_s φ_α` of a single field valued in
  the whole bosonic module — the presentation of the boson content used in writing a
  theory down. -/
noncomputable def bosonGeneratorsEquiv :
    T.BosonGenerators ≃ₗ[ℂ] JetComponentSpace T.BosonModule :=
  (DirectSum.linearEquivFunOnFintype ℂ T.BosonSpecies
      fun i => JetComponentSpace (T.BosonValue i)).trans
    (JetComponentSpace.piEquiv T.BosonValue).symm

/-!

### A.1. The species as pullbacks

-/

variable {T}

/-- **A species sits inside the bosonic generators as the pullback along the projection
  onto it.** A component function `∂_s φ_α` of the multiplet `i` becomes the component
  function of the whole scalar field whose target covector is supported on that
  multiplet. -/
@[simp]
lemma bosonGeneratorsEquiv_inclBoson (i : T.BosonSpecies)
    (x : JetComponentSpace (T.BosonValue i)) :
    T.bosonGeneratorsEquiv (T.inclBoson i x)
      = JetComponentSpace.comap (T.projBosonValue i) x := by
  rw [bosonGeneratorsEquiv, LinearEquiv.trans_apply,
    show (DirectSum.linearEquivFunOnFintype ℂ T.BosonSpecies
        fun i => JetComponentSpace (T.BosonValue i)) (T.inclBoson i x)
      = Pi.single i x from DirectSum.linearEquivFunOnFintype_lof
      (M := fun i => JetComponentSpace (T.BosonValue i)) ℂ i x,
    JetComponentSpace.piEquiv_symm_single]

/-- Two linear maps out of the component space of the bosonic module agree as soon as
  they agree on every species, the species pullbacks spanning it. -/
lemma bosonGenerators_hom_ext {N : Type} [AddCommGroup N] [Module ℂ N]
    {F F' : JetComponentSpace T.BosonModule →ₗ[ℂ] N}
    (h : ∀ i x, F (JetComponentSpace.comap (T.projBosonValue i) x)
      = F' (JetComponentSpace.comap (T.projBosonValue i) x)) : F = F' := by
  have key : F.comp T.bosonGeneratorsEquiv.toLinearMap
      = F'.comp T.bosonGeneratorsEquiv.toLinearMap :=
    SpeciesComponentSpace.hom_ext fun i x => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        bosonGeneratorsEquiv_inclBoson]
      exact h i x
  refine LinearMap.ext fun z => ?_
  simpa using LinearMap.congr_fun key (T.bosonGeneratorsEquiv.symm z)

/-!

### A.2. The transformation data

-/

/-- **The identification is Lorentz-equivariant.** The species-diagonal Lorentz action on
  the generator space is the Lorentz action on the component functions of the single
  scalar field: each species is a subrepresentation of the bosonic module, so pulling
  back along the projection onto it commutes with the two actions. No common mass weight
  is needed here — the Lorentz action does not see it. -/
lemma bosonGeneratorsEquiv_repLorentzBoson (Λ : SL(2,ℂ)) (y : T.BosonGenerators) :
    T.bosonGeneratorsEquiv (T.repLorentzBoson Λ y)
      = JetComponentSpace.repLorentzGroup T.repLorentzBosonModule Λ
        (T.bosonGeneratorsEquiv y) := by
  have key : T.bosonGeneratorsEquiv.toLinearMap.comp (T.repLorentzBoson Λ)
      = (JetComponentSpace.repLorentzGroup T.repLorentzBosonModule Λ).comp
        T.bosonGeneratorsEquiv.toLinearMap := by
    refine SpeciesComponentSpace.hom_ext fun i x => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      repLorentzBoson_inclBoson, bosonGeneratorsEquiv_inclBoson,
      bosonGeneratorsEquiv_inclBoson]
    exact LinearMap.congr_fun (JetComponentSpace.comap_comp_repLorentzGroup
      T.repLorentzBosonModule (T.boson i).repLorentz
      (T.projBosonValue i) (fun _ => LinearMap.ext fun _ => rfl) Λ) x
  exact LinearMap.congr_fun key y

/-- **The identification carries the species-wise mass-weight scaling to a single
  scaling.** With one weight `w` shared by every bosonic species, the scaling that acts
  on each species through its own weight is the scaling of weight `w` on the component
  functions of the one scalar field: `comap` is natural in the value space, so it does
  not see which species a generator came from. -/
lemma bosonGeneratorsEquiv_massWeightScaleBoson (w : ℕ)
    (h : ∀ i, (T.boson i).massWeight = w) (c : ℂ) (y : T.BosonGenerators) :
    T.bosonGeneratorsEquiv (T.massWeightScaleBoson c y)
      = JetComponentSpace.massWeightScale w c (T.bosonGeneratorsEquiv y) := by
  have key : T.bosonGeneratorsEquiv.toLinearMap.comp (T.massWeightScaleBoson c)
      = (JetComponentSpace.massWeightScale w c).comp
        T.bosonGeneratorsEquiv.toLinearMap := by
    refine SpeciesComponentSpace.hom_ext fun i x => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      massWeightScaleBoson_inclBoson, bosonGeneratorsEquiv_inclBoson,
      bosonGeneratorsEquiv_inclBoson, h i]
    exact LinearMap.congr_fun (JetComponentSpace.comap_comp_massWeightScale
      (T.projBosonValue i) w c) x
  exact LinearMap.congr_fun key y

end GaugeFieldData
