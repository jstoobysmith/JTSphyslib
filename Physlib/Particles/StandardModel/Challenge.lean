/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.MassWeight
public import Physlib.Meta.Linters.Sorry
/-!

# The Standard Model challenge

## i. Overview

The classification of the Standard Model Lagrangian, stated so that every notion in it is
either the card `Physlib.Particles.StandardModel.Basic` or generic: the left side is the
submodule of gauge and Lorentz invariants of mass weight at most a bound, in the local
field algebra of the card's field datum (`GaugeFieldData.invariantsLE`), and the right
side is the span of the Lagrangian terms, each built by a generic constructor from the
card's fields. The challenge is to prove the statements in this form, with no
Standard-Model-specific definition entering the statement and, eventually, none entering
the proof beyond theorems about the card.

The classification is currently proved in `AlgebraRealization/MassWeight/Filtration.lean`
in a form whose statement uses the hand-built realization, sector and span definitions of
this folder. Bridging the two forms is the remaining work; the statements below are its
target.

What can be stated today is the classification up to mass weight four: the constant term
and the Higgs mass term `H† H`, the latter by the generic contraction `bosonNormSq` through
the Higgs basis. The classification up to mass weight eight needs generic constructors
that do not exist yet: the kinetic term of a fermion species, the field strength squared
of each gauge factor, the covariant-derivative and box terms of a scalar, the quartic
potential, and the Yukawa term of a fermion–fermion–scalar triple. Each is a contraction
of the species' indices, one delta or epsilon per gauge factor and a Lorentz contraction,
read off the charges.

## ii. Key results

- `StandardModel.Model.higgsMass_mem_massWeightSubmodule` : the Higgs mass term has mass
  weight four, from the card and the generic filtration alone.
- `StandardModel.Model.invariantsLE_four` : the challenge at mass weight four.

-/

@[expose] public section

open LocalGaugeData GaugeFieldData

namespace StandardModel

namespace Model

/-- **The Higgs mass term `H† H` has mass weight four**: a first check that the generic
  filtration computes on a term built from the card. -/
lemma higgsMass_mem_massWeightSubmodule :
    fieldData.bosonNormSq ⟨⟨.H, by decide⟩, ⟨0, by decide⟩⟩ higgs.basis
      ∈ fieldData.massWeightSubmodule 4 := by
  rw [mem_massWeightSubmodule_iff]
  intro c
  simp only [bosonNormSq, map_sum, map_mul, conjBosonSymbol, bosonSymbol, conjBosonSymbolMap,
    bosonSymbolMap, LinearMap.comp_apply, TensorProduct.mk_apply, LinearMap.inl_apply,
    LinearMap.inr_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hw : (fieldData.boson ⟨⟨.H, by decide⟩, ⟨0, by decide⟩⟩).massWeight = 2 := rfl
  rw [massWeightScale_ιBoson, massWeightScale_ιBoson, hw]
  simp only [JetComponentSpace.massWeightScale, LinearMap.smul_apply, LinearMap.prodMap_apply,
    TensorProduct.map_tmul, AlgHom.toLinearMap_apply, DerivAlgebraComplex.gradeScale_basis,
    Multiset.card_zero, pow_zero, one_smul, LinearMap.id_apply, map_zero, map_smul,
    smul_mul_smul_comm, ← pow_add]

/-- **The challenge at mass weight four**: the gauge and Lorentz invariants of mass weight
  at most four in the local field algebra of the Standard Model are spanned by the constant
  term and the Higgs mass term `H† H`. -/
@[sorryful]
theorem invariantsLE_four :
    fieldData.invariantsLE 4
      = ℂ ∙ (1 : fieldData.LocalFieldAlgebra)
        ⊔ ℂ ∙ fieldData.bosonNormSq ⟨⟨.H, by decide⟩, ⟨0, by decide⟩⟩ higgs.basis := by
  sorry

end Model

end StandardModel
