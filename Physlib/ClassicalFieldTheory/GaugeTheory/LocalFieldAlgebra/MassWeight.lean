/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.GaugeAction
public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.LorentzAction
public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.TransformsIn
public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeBoson.LocalGaugeFieldAlgebra.MassDim
/-!

# The mass-weight filtration and the invariants of a local field algebra

## i. Overview

The local field algebra of a field datum is graded by mass weight: a generator `∂_s φ_α`
of a field of mass weight `w` has weight `w + 2 |s|`, a connection generator `∂_s A_μ` has
weight `2 + 2 |s|`. The grading is recorded by the algebra endomorphisms scaling each
generator by `c` to its weight, for real `c`; the weight-`n` piece is the common
eigenspace of eigenvalue `c ^ n`, and the filtration is the join of the pieces of weight
at most `w`.

Together with the actions of the jet gauge group and of the Lorentz group this gives the
submodule of gauge and Lorentz invariants of mass weight at most `w`, which is what a
Lagrangian classification describes. Everything here is generic: a model contributes only
its datum.

## ii. Key results

- `GaugeFieldData.massWeightScale` : the scaling of the local field algebra by `c` to the
  mass weight of each generator.
- `GaugeFieldData.massWeightSubmodule`, `massWeightSubmoduleLE` : the graded pieces and
  the filtration.
- `GaugeFieldData.gaugeInvariants`, `lorentzInvariants`, `invariantsLE` : the invariants,
  and the invariants of mass weight at most `w`.
- `GaugeFieldData.bosonNormSq` : the contraction `φ† φ` of a bosonic species with its
  conjugate through a basis of its value space, the simplest invariant.

## iii. Table of contents

- A. The mass-weight scaling
- B. The graded pieces and the filtration
- C. The invariants
- D. The contraction of a boson with its conjugate

-/

@[expose] public section

open TensorProduct Matrix MatrixGroups

namespace GaugeFieldData

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Finite ℝ 𝔤]
  {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J} (T : GaugeFieldData jets)

/-!

## A. The mass-weight scaling

-/

/-- The assignment scaling each generator by `c` to its mass weight: a component function
  `∂_s φ_α` of a species of mass weight `w` by `c ^ (w + 2 |s|)`, a connection generator
  `∂_s A_μ` by `c ^ (2 + 2 |s|)`. The relations hold because the images are generators of
  the same kind. -/
noncomputable def massWeightAssignment (c : ℝ) : T.Assignment T.LocalFieldAlgebra where
  fermion i := T.ιFermion i ∘ₗ JetComponentSpace.massWeightScale (T.fermion i).massWeight (c : ℂ)
  boson j := T.ιBoson j ∘ₗ JetComponentSpace.massWeightScale (T.boson j).massWeight (c : ℂ)
  connection := T.ιConnection ∘ₗ GaugeBoson.JetComponentSpace.massWeightScale 𝔤 c
  fermion_mul_self i _ := ιFermion_mul_self i _
  fermion_mul_swap i j _ _ := ιFermion_mul_swap i j _ _
  boson_commute i j _ _ := ιBoson_commute i j _ _
  connection_commute _ _ := ιConnection_commute _ _
  boson_commute_connection _ _ _ := ιBoson_commute_ιConnection _ _ _
  boson_commute_fermion j i _ _ := ιBoson_commute_ιFermion j i _ _
  connection_commute_fermion _ _ _ := ιConnection_commute_ιFermion _ _ _

/-- **The mass-weight scaling of the local field algebra**: the algebra endomorphism
  scaling each generator by `c` to its mass weight. -/
noncomputable def massWeightScale (c : ℝ) : T.LocalFieldAlgebra →ₐ[ℂ] T.LocalFieldAlgebra :=
  (T.massWeightAssignment c).lift

@[simp]
lemma massWeightScale_ιFermion (c : ℝ) (i : T.FermionSpecies)
    (x : JetComponentSpace (T.fermion i)) :
    T.massWeightScale c (T.ιFermion i x)
      = T.ιFermion i (JetComponentSpace.massWeightScale (T.fermion i).massWeight (c : ℂ) x) :=
  (T.massWeightAssignment c).lift_ιFermion i x

@[simp]
lemma massWeightScale_ιBoson (c : ℝ) (j : T.BosonSpecies)
    (y : JetComponentSpace (T.boson j)) :
    T.massWeightScale c (T.ιBoson j y)
      = T.ιBoson j (JetComponentSpace.massWeightScale (T.boson j).massWeight (c : ℂ) y) :=
  (T.massWeightAssignment c).lift_ιBoson j y

@[simp]
lemma massWeightScale_ιConnection (c : ℝ) (v : GaugeBoson.JetComponentSpace 𝔤) :
    T.massWeightScale c (T.ιConnection v)
      = T.ιConnection (GaugeBoson.JetComponentSpace.massWeightScale 𝔤 c v) :=
  (T.massWeightAssignment c).lift_ιConnection v

/-!

## B. The graded pieces and the filtration

-/

/-- **The weight-`n` piece** of the local field algebra: the elements scaled by `c ^ n`
  under every mass-weight scaling: the equaliser of the scalings and the scalars. -/
noncomputable def massWeightSubmodule (n : ℕ) : Submodule ℂ T.LocalFieldAlgebra :=
  ⨅ c : ℝ, LinearMap.eqLocus (T.massWeightScale c).toLinearMap
    (((c : ℂ) ^ n) • (LinearMap.id : T.LocalFieldAlgebra →ₗ[ℂ] T.LocalFieldAlgebra))

lemma mem_massWeightSubmodule_iff {n : ℕ} {x : T.LocalFieldAlgebra} :
    x ∈ T.massWeightSubmodule n ↔ ∀ c : ℝ, T.massWeightScale c x = ((c : ℂ) ^ n) • x := by
  simp only [massWeightSubmodule, Submodule.mem_iInf, LinearMap.mem_eqLocus,
    AlgHom.toLinearMap_apply, LinearMap.smul_apply, LinearMap.id_apply]

/-- **The mass-weight filtration**: the join of the pieces of weight at most `w`. -/
noncomputable def massWeightSubmoduleLE (w : ℕ) : Submodule ℂ T.LocalFieldAlgebra :=
  ⨆ k ∈ Finset.range (w + 1), T.massWeightSubmodule k

lemma massWeightSubmodule_le_massWeightSubmoduleLE {k w : ℕ} (h : k ≤ w) :
    T.massWeightSubmodule k ≤ T.massWeightSubmoduleLE w :=
  le_iSup₂ (f := fun k _ => T.massWeightSubmodule k) k (Finset.mem_range.mpr (Nat.lt_succ_of_le h))

/-!

## C. The invariants

-/

/-- **The gauge invariants**: the elements fixed by every jet of gauge transformations. -/
noncomputable def gaugeInvariants : Submodule ℂ T.LocalFieldAlgebra :=
  ⨅ U : GJ, LinearMap.eqLocus (T.repJet U)
    (LinearMap.id : T.LocalFieldAlgebra →ₗ[ℂ] T.LocalFieldAlgebra)

lemma mem_gaugeInvariants_iff {x : T.LocalFieldAlgebra} :
    x ∈ T.gaugeInvariants ↔ ∀ U : GJ, T.repJet U x = x := by
  simp only [gaugeInvariants, Submodule.mem_iInf, LinearMap.mem_eqLocus, LinearMap.id_apply]

/-- **The Lorentz invariants**: the elements fixed by every Lorentz transformation. -/
noncomputable def lorentzInvariants : Submodule ℂ T.LocalFieldAlgebra :=
  ⨅ Λ : SL(2,ℂ), LinearMap.eqLocus (T.repLorentzGroup Λ)
    (LinearMap.id : T.LocalFieldAlgebra →ₗ[ℂ] T.LocalFieldAlgebra)

lemma mem_lorentzInvariants_iff {x : T.LocalFieldAlgebra} :
    x ∈ T.lorentzInvariants ↔ ∀ Λ : SL(2,ℂ), T.repLorentzGroup Λ x = x := by
  simp only [lorentzInvariants, Submodule.mem_iInf, LinearMap.mem_eqLocus, LinearMap.id_apply]

/-- **The invariants of mass weight at most `w`**: the gauge and Lorentz invariants in the
  filtration. A Lagrangian of mass dimension at most `w / 2` is an element of it. -/
noncomputable def invariantsLE (w : ℕ) : Submodule ℂ T.LocalFieldAlgebra :=
  T.massWeightSubmoduleLE w ⊓ (T.gaugeInvariants ⊓ T.lorentzInvariants)

lemma mem_invariantsLE_iff {w : ℕ} {x : T.LocalFieldAlgebra} :
    x ∈ T.invariantsLE w ↔ x ∈ T.massWeightSubmoduleLE w
      ∧ (∀ U : GJ, T.repJet U x = x) ∧ ∀ Λ : SL(2,ℂ), T.repLorentzGroup Λ x = x := by
  simp only [invariantsLE, Submodule.mem_inf, mem_gaugeInvariants_iff, mem_lorentzInvariants_iff]

/-!

## D. The contraction of a boson with its conjugate

-/

/-- **The contraction `φ† φ`** of a bosonic species with its conjugate, through a basis of
  its value space: the sum over the basis of the conjugate coordinate times the coordinate.
  For a scalar in a unitary representation it is the mass term. -/
noncomputable def bosonNormSq (j : T.BosonSpecies) {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ (T.BosonValue j)) : T.LocalFieldAlgebra :=
  ∑ i, T.conjBosonSymbol j 0 (b.conj.dualBasis i) * T.bosonSymbol j 0 (b.dualBasis i)

end GaugeFieldData
