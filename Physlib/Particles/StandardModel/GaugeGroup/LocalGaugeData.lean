/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeField.Basic
public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.InfinitesimalAction
public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.MaurerCartan
public import Physlib.ClassicalFieldTheory.GaugeTheory.Matter.CovariantDeriv
public import Physlib.Particles.StandardModel.GaugeBosons.AlgebraValued.Basic
public import Physlib.Particles.StandardModel.GaugeBosons.GaugeJetAlgebra.GaugeAction
public import Physlib.Particles.StandardModel.GaugeGroup.MaurerCartan.Basic
public import Physlib.Particles.StandardModel.Matter.JetComponentSpace.CovariantDeriv
/-!
# The Standard Model gauge group as jets of a gauge group

## i. Overview

The generic transformation laws of gauge and matter fields are stated against a supplied
local-gauge-data package `jets : LocalGaugeData G 𝔤 G₀ 𝔤J`. The Standard Model already
carries all of its data, for the jet gauge group `JetGaugeGroupI` of `SU(3) × SU(2) × U(1)`
with jet Lie algebra `JetGaugeAlgebra`, global group `GaugeGroupI` and gauge algebra
`GaugeAlgebra`.

This file packages those existing constructions as the named term
`StandardModel.localGaugeData`, and records the rules that compute the generic interface back to
the Standard Model definition it came from, so the existing Standard Model lemmas apply to
it unchanged. It is a term, not an instance: every generic construction receives it as an
argument. Its extra law `LocalGaugeDataLeibniz` is a property of that package rather than a
choice, so it is an instance, discharged by the existing Taylor–Leibniz theorem.

## ii. Key results

- `StandardModel.localGaugeData` : the Standard Model gauge group as jets of a gauge group.
- `StandardModel.localGaugeData_eval`, `StandardModel.localGaugeData_deriv`,
  `StandardModel.localGaugeData_maurerCartan`, … : the generic interface computed back to
  the Standard Model definitions.
- `StandardModel.localGaugeData_iteratedDeriv` : the generic iterated derivative is the Standard
  Model iterated derivative.
- `StandardModel.localGaugeData_adjointCoeff`, `StandardModel.localGaugeData_adjointDualCoeff` : the
  generic base-point adjoint transport at this package is the existing Standard Model one.
- `StandardModel.localGaugeData_repCoeff` : the generic base-point Taylor coefficient of a
  representation is the Standard Model one.
- `StandardModel.IsGaugeField.toLocalGaugeData` : a Standard Model gauge field is a gauge
  field of the package.
- `StandardModel.TransformsIn.repGauge_zero`,
  `StandardModel.TransformsIn.covDerivAction`, `StandardModel.TransformsIn.covDerivIter`,
  `StandardModel.TransformsIn.repGauge_eq_of_mem_truncationKer_zero` : the generic
  covariance theorems of the covariant derivative, read at this package.
- `StandardModel.instLocalGaugeDataLeibniz` : the package obeys the Taylor–Leibniz rule for the
  adjoint action.

## iii. Table of contents

- A. The local-gauge-data package
- B. The generic interface in Standard Model terms
  - B.1. The group and Lie algebra data
  - B.2. The derivative, the adjoint action and the Maurer–Cartan form
- C. The generic adjoint transport is the Standard Model adjoint transport
  - C.1. Gauge fields
  - C.2. The generic covariance theorems in Standard Model terms
- D. The Taylor–Leibniz rule

-/

@[expose] public section

namespace StandardModel

open JetGaugeAlgebra TensorProduct Matrix MatrixGroups

/-!

## A. The local-gauge-data package

`LocalGaugeData` is an ordinary structure, so this is a named term supplied at each use site,
not an instance found by search. The four carriers do not determine it — a truncated jet
group over the same gauge group would be a second, equally canonical package — so nothing
is registered globally.

-/

/-- The Standard Model gauge group as jets of a gauge group, for the jet gauge group
  `JetGaugeGroupI` and its Lie algebra `JetGaugeAlgebra` over the global group
  `GaugeGroupI` and gauge algebra `GaugeAlgebra`. Nothing is redefined. Every data field
  is an existing Standard Model construction and every proof field an existing Standard
  Model lemma. -/
noncomputable def localGaugeData :
    LocalGaugeData JetGaugeGroupI GaugeAlgebra GaugeGroupI JetGaugeAlgebra where
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
  maurerCartan := maurerCartanForm
  maurerCartan_one := fun μ => congrFun maurerCartanForm_one μ
  maurerCartan_ofConstant := fun g μ => congrFun (maurerCartanForm_ofConstant g) μ
  maurerCartan_cocycle := maurerCartanForm_cocycle
  maurerCartan_structure := maurerCartanForm_structure
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
lemma localGaugeData_eval : localGaugeData.eval = JetGaugeGroupI.eval := rfl

@[simp]
lemma localGaugeData_ofConstant : localGaugeData.ofConstant = JetGaugeGroupI.ofConstant := rfl

@[simp]
lemma localGaugeData_evalLie : localGaugeData.evalLie = JetGaugeAlgebra.eval := rfl

@[simp]
lemma localGaugeData_ofConstantLie :
    localGaugeData.ofConstantLie = JetGaugeAlgebra.ofConstant := rfl

@[simp]
lemma localGaugeData_adjointValue : localGaugeData.adjointValue = GaugeAlgebra.adjoint := rfl

/-!

### B.2. The derivative, the adjoint action and the Maurer–Cartan form

-/

@[simp]
lemma localGaugeData_deriv (μ : Fin 1 ⊕ Fin 3) :
    localGaugeData.deriv μ = JetGaugeAlgebra.deriv μ := rfl

/-- The generic iterated derivative is the Standard Model iterated derivative, both being
  the same fold of `JetGaugeAlgebra.deriv` over the multiset of directions. -/
@[simp]
lemma localGaugeData_iteratedDeriv (s : Multiset (Fin 1 ⊕ Fin 3)) :
    localGaugeData.iteratedDeriv s = JetGaugeAlgebra.iteratedDeriv s := rfl

@[simp]
lemma localGaugeData_adjoint : localGaugeData.adjoint = JetGaugeAlgebra.adjoint := rfl

@[simp]
lemma localGaugeData_maurerCartan : localGaugeData.maurerCartan = maurerCartanForm := rfl

/-- The symmetrized Maurer–Cartan form of the package, written out in Standard Model
  terms: the generic iterated derivative and Maurer–Cartan form are the Standard Model
  ones, so the average is the one the component computations use. -/
lemma localGaugeData_symmetrizedMaurerCartanForm_eq (U : JetGaugeGroupI)
    (r : Multiset (Fin 1 ⊕ Fin 3)) :
    localGaugeData.symmetrizedMaurerCartanForm U r =
      (1/(r.card : ℝ) : ℝ) • (r.map fun μ =>
        JetGaugeAlgebra.iteratedDeriv (r - {μ}) (maurerCartanForm U μ)).sum := rfl

/-- The symmetrization defect of the Maurer–Cartan form in Standard Model terms: the
  generic `LocalGaugeData.iteratedDeriv_maurerCartan_eq_symmetrized_add` read at this package. -/
lemma iteratedDeriv_maurerCartanForm_eq_symmetrized_add (U : JetGaugeGroupI)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) :
    JetGaugeAlgebra.iteratedDeriv s (maurerCartanForm U μ) =
      localGaugeData.symmetrizedMaurerCartanForm U (μ ::ₘ s) +
      (1/(s.card + 1 : ℝ)) • (s.map fun ν =>
        JetGaugeAlgebra.iteratedDeriv (s.erase ν)
          ⁅maurerCartanForm U μ, maurerCartanForm U ν⁆).sum :=
  localGaugeData.iteratedDeriv_maurerCartan_eq_symmetrized_add U s μ

/-- **The Maurer–Cartan form of an inverse**: the generic `LocalGaugeData.maurerCartan_inv` read at
  this package. -/
lemma maurerCartanForm_inv (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3) :
    maurerCartanForm U⁻¹ μ = - JetGaugeAlgebra.adjoint U⁻¹ (maurerCartanForm U μ) :=
  localGaugeData.maurerCartan_inv U μ

/-!

## C. The generic adjoint transport is the Standard Model adjoint transport

The composite `evalLie ∘ ∂_x ∘ Ad_U ∘ ofConstantLie`, by which the generic theory
transports the gauge algebra to the base point, is the map the Standard Model
covariant-derivative development already uses under the same name.

-/

@[simp]
lemma localGaugeData_adjointCoeff (U : JetGaugeGroupI) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    _root_.IsGaugeField.adjointCoeff localGaugeData U x = IsGaugeField.adjointCoeff U x := rfl

@[simp]
lemma localGaugeData_adjointDualCoeff (U : JetGaugeGroupI) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    _root_.adjointDualCoeff localGaugeData U x = adjointDualCoeff U x := rfl

/-- The generic base-point Taylor coefficient of a representation is the Standard Model
  one. Neither side mentions the package — both are `jetEval ∘ ∂_x ∘ rep U ∘ jetOfConstant`
  — but the two `jet`-level operations are defined in different namespaces, and this rule
  points from the generic one to the Standard Model one. -/
@[simp]
lemma localGaugeData_repCoeff {V : Type} [AddCommGroup V] [Module ℂ V]
    (rep : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V)) (U : JetGaugeGroupI)
    (x : Multiset (Fin 1 ⊕ Fin 3)) :
    _root_.IsGaugeField.repCoeff rep U x = IsGaugeField.repCoeff rep U x := rfl

@[simp]
lemma localGaugeData_repDualCoeff {V : Type} [AddCommGroup V] [Module ℂ V]
    (rep : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V)) (U : JetGaugeGroupI)
    (x : Multiset (Fin 1 ⊕ Fin 3)) :
    _root_.IsGaugeField.repDualCoeff rep U x = IsGaugeField.repDualCoeff rep U x := rfl

/-!

### C.1. Gauge fields

-/

/-- **A Standard Model gauge field is a gauge field of the package.** The two structures
  have the same three fields: the generic `adjointDualCoeff` and Maurer–Cartan form at
  `localGaugeData` are the Standard Model ones, so each law transfers unchanged. This is
  the bridge along which the generic covariance theorems apply to the Standard Model. -/
lemma IsGaugeField.toLocalGaugeData {B : Type} [Ring B] [Algebra ℂ B]
    {repLorentz : Representation ℂ SL(2,ℂ) B} {repGauge : Representation ℂ JetGaugeGroupI B}
    {A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B}
    (hA : IsGaugeField repLorentz repGauge A) :
    _root_.IsGaugeField localGaugeData repLorentz repGauge A where
  lorentz_apply := hA.lorentz_apply
  gauge_apply_deriv := hA.gauge_apply_deriv
  gauge_mul := hA.gauge_mul

/-!

### C.2. The generic covariance theorems in Standard Model terms

The covariance of the covariant derivative is proved once, generically, in
`Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.InfinitesimalAction`. The
Standard Model `TransformsIn`, `covDerivAction` and `covDerivIter` are the generic ones
at `localGaugeData`, so those theorems specialize; only the gauge-field hypothesis needs
the bridge `IsGaugeField.toLocalGaugeData`.

-/

section Covariance

variable {B : Type} [Ring B] [Algebra ℂ B] {V : Type} [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V]
  {repLorentz : Representation ℂ SL(2,ℂ) B} {repGauge : Representation ℂ JetGaugeGroupI B}
  {A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B}
  {rep : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V)}
  {act : GaugeAlgebra →ₗ[ℝ] V →ₗ[ℂ] V}
  {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B}

omit [FiniteDimensional ℂ V] in
/-- A matter gauge tensor transforms at the base point through the dual coefficient of the
  base-point value of the gauge jet alone: the generic
  `LocalGaugeData.TransformsIn.repGauge_zero`. -/
lemma TransformsIn.repGauge_zero (hF : TransformsIn repGauge rep F) (U : JetGaugeGroupI)
    (φ : Module.Dual ℂ V) :
    repGauge U (F 0 φ) = F 0 (IsGaugeField.repDualCoeff rep U⁻¹ 0 φ) :=
  _root_.LocalGaugeData.TransformsIn.repGauge_zero hF U φ

/-- **The covariant derivative preserves `TransformsIn`**, for the Standard Model: the
  generic `LocalGaugeData.TransformsIn.covDerivAction` read at `localGaugeData`. -/
theorem TransformsIn.covDerivAction (hA : IsGaugeField repLorentz repGauge A)
    (hF : TransformsIn repGauge rep F)
    (hact : localGaugeData.IsInfinitesimalActionOf act rep)
    (ρ : Fin 1 ⊕ Fin 3) :
    TransformsIn repGauge rep (IsGaugeField.covDerivAction A act F ρ) :=
  _root_.LocalGaugeData.TransformsIn.covDerivAction hA.toLocalGaugeData hF hact ρ

/-- **Every iterated covariant derivative preserves `TransformsIn`**, for the Standard
  Model: the recursion of `TransformsIn.covDerivAction` over the tuple of directions. -/
theorem TransformsIn.covDerivIter (hA : IsGaugeField repLorentz repGauge A)
    (hF : TransformsIn repGauge rep F)
    (hact : localGaugeData.IsInfinitesimalActionOf act rep)
    (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    TransformsIn repGauge rep (IsGaugeField.covDerivIter A act F n l) := by
  induction n with
  | zero => exact hF
  | succ n ih => exact TransformsIn.covDerivAction hA (ih fun i => l i.succ) hact (l 0)

omit [FiniteDimensional ℂ V] in
/-- **Matter gauge tensors are fixed by pure jets**, for the Standard Model: the generic
  `LocalGaugeData.TransformsIn.repGauge_eq_of_eval_eq_one`, with membership in the zeroth truncation
  kernel read as triviality of the base-point value. -/
lemma TransformsIn.repGauge_eq_of_mem_truncationKer_zero
    (hF : TransformsIn repGauge rep F)
    (hrep : ∀ {W : JetGaugeGroupI}, W.eval = 1 → IsGaugeField.repCoeff rep W 0 = LinearMap.id)
    (U : JetGaugeGroupI.truncationKer 0) (φ : Module.Dual ℂ V) :
    repGauge U.1 (F 0 φ) = F 0 φ :=
  _root_.LocalGaugeData.TransformsIn.repGauge_eq_of_eval_eq_one (jets := localGaugeData) hF hrep
    (JetGaugeGroupI.mem_truncationKer_zero_iff.mp U.2) φ

end Covariance

/-!

## D. The Taylor–Leibniz rule

-/

/-- The Standard Model package obeys the Taylor–Leibniz rule for the adjoint action. The
  class field is the existing theorem `JetGaugeAlgebra.eval_iteratedDeriv_adjointMap`: the
  `IsGaugeField.adjointCoeff U p.1` appearing there is by definition the composite
  `evalLie ∘ ∂_{p.1} ∘ Ad_U ∘ ofConstantLie` that the field writes out.

  Unlike the package itself this is a property of it and not a choice, so it is an
  instance. -/
instance instLocalGaugeDataLeibniz : LocalGaugeDataLeibniz localGaugeData where
  evalLie_iteratedDeriv_adjoint := JetGaugeAlgebra.eval_iteratedDeriv_adjointMap

end StandardModel
