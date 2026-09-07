/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeField.Basic
public import Physlib.ClassicalFieldTheory.GaugeTheory.Matter.CovariantDeriv
public import Physlib.Particles.StandardModel.GaugeBosons.AlgebraValued.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.MaurerCartan.Basic
public import Physlib.Particles.StandardModel.Matter.JetComponentSpace.CovariantDeriv
/-!
# The Standard Model gauge group as jets of a gauge group

## i. Overview

The generic transformation laws of gauge and matter fields are stated against the class
`GaugeJet G 𝔤 G₀ 𝔤J`. The Standard Model already carries all of its data, for the jet
gauge group `JetGaugeGroupI` of `SU(3) × SU(2) × U(1)` with jet Lie algebra
`JetGaugeAlgebra`, global group `GaugeGroupI` and gauge algebra `GaugeAlgebra`.

This file installs those existing constructions as the instance
`StandardModel.instGaugeJet`, and records the rules that compute the generic interface
back to the Standard Model definition it came from, so the existing Standard Model lemmas
apply to it unchanged. `GaugeJetLeibniz` is not instantiated here.

## ii. Key results

- `StandardModel.instGaugeJet` : the Standard Model gauge group as jets of a gauge group.
- `StandardModel.gaugeJet_eval`, `StandardModel.gaugeJet_deriv`,
  `StandardModel.gaugeJet_mc`, … : the generic interface computed back to the Standard
  Model definitions.
- `StandardModel.gaugeJet_iteratedDeriv` : the generic iterated derivative is the Standard
  Model iterated derivative.
- `StandardModel.gaugeJet_adjointCoeff`, `StandardModel.gaugeJet_adjointDualCoeff` : the
  generic base-point adjoint transport at the instance is the existing Standard Model one.

## iii. Table of contents

- A. The gauge-jet instance
- B. The generic interface in Standard Model terms
  - B.1. The group and Lie algebra data
  - B.2. The derivative, the adjoint action and the Maurer–Cartan form
- C. The generic adjoint transport is the Standard Model adjoint transport

-/

@[expose] public section

namespace StandardModel

open JetGaugeAlgebra

/-!

## A. The gauge-jet instance

It is registered as a global instance because `G₀` and `𝔤J` are output parameters of the
class, so the pair `(JetGaugeGroupI, GaugeAlgebra)` determines it, and the library holds
no other `GaugeJet` instance.

-/

/-- The Standard Model gauge group as jets of a gauge group, for the jet gauge group
  `JetGaugeGroupI` and its Lie algebra `JetGaugeAlgebra` over the global group
  `GaugeGroupI` and gauge algebra `GaugeAlgebra`. Nothing is redefined. Every data field
  is an existing Standard Model construction and every proof field an existing Standard
  Model lemma. -/
noncomputable instance instGaugeJet :
    GaugeJet JetGaugeGroupI GaugeAlgebra GaugeGroupI JetGaugeAlgebra where
  eval := JetGaugeGroupI.eval
  ofConstant := JetGaugeGroupI.ofConstant
  eval_ofConstant := JetGaugeGroupI.eval_ofConstant
  evalLie := JetGaugeAlgebra.eval
  ofConstantLie := JetGaugeAlgebra.ofConstant
  ofConstantLie_lie := JetGaugeAlgebra.ofConstant_lie
  deriv := JetGaugeAlgebra.deriv
  deriv_comm := JetGaugeAlgebra.deriv_comm
  deriv_bracket := JetGaugeAlgebra.deriv_bracket
  deriv_ofConstantLie := JetGaugeAlgebra.deriv_ofConstant
  adjoint := JetGaugeAlgebra.adjoint
  adjoint_lie := JetGaugeAlgebra.adjointMap_lie
  mc := maurerCartanForm
  mc_one := fun μ => congrFun maurerCartanForm_one μ
  mc_cocycle := maurerCartanForm_cocycle
  mc_structure := maurerCartanForm_structure
  deriv_adjoint := deriv_adjointMap
  adjointValue := GaugeAlgebra.adjoint
  evalLie_adjoint_ofConstantLie := JetGaugeAlgebra.eval_adjointMap_ofConstant

/-!

## B. The generic interface in Standard Model terms

These rules point from the generic interface to the Standard Model definitions, which is
the direction in which the existing Standard Model lemmas become applicable.

### B.1. The group and Lie algebra data

-/

@[simp]
lemma gaugeJet_eval : GaugeJet.eval GaugeAlgebra (G := JetGaugeGroupI) =
    JetGaugeGroupI.eval := rfl

@[simp]
lemma gaugeJet_ofConstant : GaugeJet.ofConstant GaugeAlgebra (G := JetGaugeGroupI) =
    JetGaugeGroupI.ofConstant := rfl

@[simp]
lemma gaugeJet_evalLie : GaugeJet.evalLie JetGaugeGroupI (𝔤 := GaugeAlgebra) =
    JetGaugeAlgebra.eval := rfl

@[simp]
lemma gaugeJet_ofConstantLie : GaugeJet.ofConstantLie JetGaugeGroupI (𝔤 := GaugeAlgebra) =
    JetGaugeAlgebra.ofConstant := rfl

@[simp]
lemma gaugeJet_adjointValue : GaugeJet.adjointValue JetGaugeGroupI (𝔤 := GaugeAlgebra) =
    GaugeAlgebra.adjoint := rfl

/-!

### B.2. The derivative, the adjoint action and the Maurer–Cartan form

-/

@[simp]
lemma gaugeJet_deriv (μ : Fin 1 ⊕ Fin 3) :
    GaugeJet.deriv JetGaugeGroupI GaugeAlgebra μ = JetGaugeAlgebra.deriv μ := rfl

/-- The generic iterated derivative is the Standard Model iterated derivative, both being
  the same fold of `JetGaugeAlgebra.deriv` over the multiset of directions. -/
@[simp]
lemma gaugeJet_iteratedDeriv (s : Multiset (Fin 1 ⊕ Fin 3)) :
    GaugeJet.iteratedDeriv JetGaugeGroupI GaugeAlgebra s = JetGaugeAlgebra.iteratedDeriv s :=
  rfl

@[simp]
lemma gaugeJet_adjoint : GaugeJet.adjoint GaugeAlgebra (G := JetGaugeGroupI) =
    JetGaugeAlgebra.adjoint := rfl

@[simp]
lemma gaugeJet_mc : GaugeJet.mc GaugeAlgebra (G := JetGaugeGroupI) = maurerCartanForm := rfl

/-!

## C. The generic adjoint transport is the Standard Model adjoint transport

The composite `evalLie ∘ ∂_x ∘ Ad_U ∘ ofConstantLie`, by which the generic theory
transports the gauge algebra to the base point, is the map the Standard Model
covariant-derivative development already uses under the same name.

-/

@[simp]
lemma gaugeJet_adjointCoeff (U : JetGaugeGroupI) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    _root_.IsGaugeField.adjointCoeff (𝔤 := GaugeAlgebra) U x = IsGaugeField.adjointCoeff U x :=
  rfl

@[simp]
lemma gaugeJet_adjointDualCoeff (U : JetGaugeGroupI) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    _root_.adjointDualCoeff (𝔤 := GaugeAlgebra) U x = adjointDualCoeff U x := rfl

end StandardModel
