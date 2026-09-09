/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeFieldData.FermionMatterField
/-!
# The fermionic generators as the components of one fermion field

## i. Overview

`GaugeFieldData.FermionGenerators` is built species by species, as the direct sum
`⨁ i, JetComponentSpace (T.fermion i).V` of the component spaces of the several fermionic
multiplets. A physicist writing the Standard Model does not do this. They write one fermion
field `ψ`, valued in the whole fermionic module, and take its component functions
`∂_s ψ_α` — a single `JetComponentSpace`, indexed by a target index `α` that runs over all
the multiplets at once.

This file shows that the two agree. When the fermionic species share a mass weight — the
condition under which `GaugeFieldData.fermionMatterField` exists, and the condition every
theory of Weyl fermions satisfies — there is an isomorphism

`T.FermionGenerators ≃ₗ[ℂ] JetComponentSpace T.FermionModule`,

and under it the summand of a species is the pullback along the projection onto that
species, `fermionGeneratorsEquiv_inclFermion`. So the generators of one multiplet sit
inside the generators of the whole fermion field exactly as its target components sit
inside the fermionic module, which is what a physicist means by writing `ψ_α` with `α`
ranging over everything.

The isomorphism is not merely one of vector spaces: it intertwines the Lorentz action and
the mass-weight scaling with those of the single matter field
`T.fermionMatterField w h`. The mass weight is where the shared weight `w` is needed and
where the species-by-species construction earns its keep — a family of *unequal* weights
has no single `JetComponentSpace.massWeightScale` to be compared with, which is precisely
the reason `SpeciesComponentSpace` was built as a direct sum in the first place. With one
weight that obstruction is gone and the two descriptions coincide.

The underlying identification is `JetComponentSpace.piEquiv`, composed with the
identification of a direct sum over a finite index with the product.

## ii. Key results

- `GaugeFieldData.fermionGeneratorsEquiv` : the fermionic generator space is the component
  space of the fermionic matter field.
- `GaugeFieldData.fermionGeneratorsEquiv_inclFermion` : a species sits inside it as the
  pullback along the projection onto that species.
- `GaugeFieldData.fermionGeneratorsEquiv_repLorentzFermion` : the identification is
  Lorentz-equivariant.
- `GaugeFieldData.fermionGeneratorsEquiv_massWeightScaleFermion` : it carries the
  species-wise mass-weight scaling to the single scaling of weight `w`.

## iii. Table of contents

- A. The fermionic generators as one component space
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

## A. The fermionic generators as one component space

-/

/-- **The fermionic generator space is the component space of the fermionic module.** The
  direct sum over the species of their component spaces is, the species type being finite,
  the same thing as the space of component functions `∂_s ψ_α` of a single field valued in
  the whole fermionic module — the presentation of the fermion content used in writing a
  theory down. -/
noncomputable def fermionGeneratorsEquiv :
    T.FermionGenerators ≃ₗ[ℂ] JetComponentSpace T.FermionModule :=
  (DirectSum.linearEquivFunOnFintype ℂ T.FermionSpecies
      fun i => JetComponentSpace (T.FermionValue i)).trans
    (JetComponentSpace.piEquiv T.FermionValue).symm

/-!

### A.1. The species as pullbacks

-/

variable {T}

/-- **A species sits inside the fermionic generators as the pullback along the projection
  onto it.** A component function `∂_s ψ_α` of the multiplet `i` becomes the component
  function of the whole fermion field whose target covector is supported on that
  multiplet. -/
@[simp]
lemma fermionGeneratorsEquiv_inclFermion (i : T.FermionSpecies)
    (x : JetComponentSpace (T.FermionValue i)) :
    T.fermionGeneratorsEquiv (T.inclFermion i x)
      = JetComponentSpace.comap (T.projFermionValue i) x := by
  rw [fermionGeneratorsEquiv, LinearEquiv.trans_apply,
    show (DirectSum.linearEquivFunOnFintype ℂ T.FermionSpecies
        fun i => JetComponentSpace (T.FermionValue i)) (T.inclFermion i x)
      = Pi.single i x from DirectSum.linearEquivFunOnFintype_lof
      (M := fun i => JetComponentSpace (T.FermionValue i)) ℂ i x,
    JetComponentSpace.piEquiv_symm_single]

/-- Two linear maps out of the component space of the fermionic module agree as soon as
  they agree on every species, the species pullbacks spanning it. -/
lemma fermionGenerators_hom_ext {N : Type} [AddCommGroup N] [Module ℂ N]
    {F F' : JetComponentSpace T.FermionModule →ₗ[ℂ] N}
    (h : ∀ i x, F (JetComponentSpace.comap (T.projFermionValue i) x)
      = F' (JetComponentSpace.comap (T.projFermionValue i) x)) : F = F' := by
  have key : F.comp T.fermionGeneratorsEquiv.toLinearMap
      = F'.comp T.fermionGeneratorsEquiv.toLinearMap :=
    SpeciesComponentSpace.hom_ext fun i x => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        fermionGeneratorsEquiv_inclFermion]
      exact h i x
  refine LinearMap.ext fun z => ?_
  simpa using LinearMap.congr_fun key (T.fermionGeneratorsEquiv.symm z)

/-!

### A.2. The transformation data

-/

/-- **The identification is Lorentz-equivariant.** The species-diagonal Lorentz action on
  the generator space is the Lorentz action on the component functions of the single
  fermion field: each species is a subrepresentation of the fermionic module, so pulling
  back along the projection onto it commutes with the two actions. No common mass weight
  is needed here — the Lorentz action does not see it. -/
lemma fermionGeneratorsEquiv_repLorentzFermion (Λ : SL(2,ℂ)) (y : T.FermionGenerators) :
    T.fermionGeneratorsEquiv (T.repLorentzFermion Λ y)
      = JetComponentSpace.repLorentzGroup T.repLorentzFermionModule Λ
        (T.fermionGeneratorsEquiv y) := by
  have key : T.fermionGeneratorsEquiv.toLinearMap.comp (T.repLorentzFermion Λ)
      = (JetComponentSpace.repLorentzGroup T.repLorentzFermionModule Λ).comp
        T.fermionGeneratorsEquiv.toLinearMap := by
    refine SpeciesComponentSpace.hom_ext fun i x => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      repLorentzFermion_inclFermion, fermionGeneratorsEquiv_inclFermion,
      fermionGeneratorsEquiv_inclFermion]
    exact LinearMap.congr_fun (JetComponentSpace.comap_comp_repLorentzGroup
      T.repLorentzFermionModule (T.fermion i).repLorentz
      (T.projFermionValue i) (fun _ => LinearMap.ext fun _ => rfl) Λ) x
  exact LinearMap.congr_fun key y

/-- **The identification carries the species-wise mass-weight scaling to a single
  scaling.** With one weight `w` shared by every fermionic species, the scaling that acts
  on each species through its own weight is the scaling of weight `w` on the component
  functions of the one fermion field: `comap` is natural in the value space, so it does
  not see which species a generator came from. -/
lemma fermionGeneratorsEquiv_massWeightScaleFermion (w : ℕ)
    (h : ∀ i, (T.fermion i).massWeight = w) (c : ℂ) (y : T.FermionGenerators) :
    T.fermionGeneratorsEquiv (T.massWeightScaleFermion c y)
      = JetComponentSpace.massWeightScale w c (T.fermionGeneratorsEquiv y) := by
  have key : T.fermionGeneratorsEquiv.toLinearMap.comp (T.massWeightScaleFermion c)
      = (JetComponentSpace.massWeightScale w c).comp
        T.fermionGeneratorsEquiv.toLinearMap := by
    refine SpeciesComponentSpace.hom_ext fun i x => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      massWeightScaleFermion_inclFermion, fermionGeneratorsEquiv_inclFermion,
      fermionGeneratorsEquiv_inclFermion, h i]
    exact LinearMap.congr_fun (JetComponentSpace.comap_comp_massWeightScale
      (T.projFermionValue i) w c) x
  exact LinearMap.congr_fun key y

end GaugeFieldData
