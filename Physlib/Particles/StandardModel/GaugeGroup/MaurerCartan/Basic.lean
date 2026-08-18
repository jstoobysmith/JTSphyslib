/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.Jet
public import Physlib.Particles.StandardModel.GaugeAlgebra.JetGaugeAlgebra
public import Physlib.Relativity.Tensors.ComplexTensor.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Representation
public import Physlib.Relativity.SL2C.Basic
public import Physlib.Mathematics.ConjModule
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Physlib.Particles.LagrangianTheory.Basic
public import Physlib.Mathematics.MvPowerSeriesDerivative
public import Physlib.Mathematics.MvPolynomialTranslation
public import Mathlib.Algebra.MvPolynomial.Derivation
/-!
# The Maurer–Cartan forms of the jet gauge group

The Maurer-Cartan form is a map
`ω : JetGaugeGroupI → (Fin 1 ⊕ Fin 3) → JetGaugeAlgebra`
defined as `ω_μ(U) := i (∂_μ U) U†`.

We will use `ω^a_ν` to denote the `a`-th component of the Maurer–Cartan form in the
basis of the jet Lie algebra, and `f^a_{b c}` to denote the structure constants of the
jet Lie algebra in that basis.

It satisfies the following properties:
- *Cocycle law*: `ω_μ(UV) = ω_μ(U) + U ω_μ(V) U†`
- *Value on the identity*: `ω_μ(1) = 0`
- *Value on constant gauge transformations*: `ω_μ(U₀) = 0`
- *Value on the inverse*: `ω_μ(U⁻¹) = -U⁻¹ ω_μ(U) U`
- *Structural equation*: `∂_μ ω^a_ν(U) − ∂_ν ω^a_μ(U) = ∑_{b c} f^a_{b c} · ω^b_μ(U) · ω^c_ν(U)`

-/

@[expose] public section
namespace StandardModel
open MvPowerSeries JetGaugeAlgebra

/-!

## The Maurer–Cartan form of the jet gauge group

-/

/-- The Maurer–Cartan form `ω_μ(U) := i (∂_μ U) U⁻¹` of the jet gauge group, valued
  in the jet gauge algebra. -/
noncomputable def maurerCartanForm (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3) : JetGaugeAlgebra :=
  JetGaugeAlgebra.ofMatrixProd (Complex.I • (JetGaugeGroupI.deriv μ U * (U⁻¹).toVal))
    ⟨JetGaugeGroupI.star_deriv_mul_inv_toVal_SU3 μ U,
      JetGaugeGroupI.deriv_mul_inv_toVal_SU3_traceless μ U⟩
    ⟨JetGaugeGroupI.star_deriv_mul_inv_toVal_SU2 μ U,
      JetGaugeGroupI.deriv_mul_inv_toVal_SU2_traceless μ U⟩
    (JetGaugeGroupI.star_deriv_mul_inv_toVal_U1 μ U)

@[simp]
lemma maurerCartanForm_toSU3Matrix (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3) :
    (maurerCartanForm U μ).toSU3Matrix =
      Complex.I • (U.1.1.map (pderiv ℂ μ) * star U.1.1) := rfl

@[simp]
lemma maurerCartanForm_toSU2Matrix (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3) :
    (maurerCartanForm U μ).toSU2Matrix =
      Complex.I • (U.2.1.1.map (pderiv ℂ μ) * star U.2.1.1) := rfl

@[simp]
lemma maurerCartanForm_toU1Value (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3) :
    (maurerCartanForm U μ).toU1Value =
      Complex.I • (pderiv ℂ μ U.2.2.1 * star U.2.2.1) := rfl

@[simp]
lemma maurerCartanForm_one : maurerCartanForm (1 : JetGaugeGroupI) = 0 := by
  ext <;> simp [maurerCartanForm,JetGaugeGroupI.deriv_one]

lemma maurerCartanForm_ofConstant (U₀ : GaugeGroupI) :
    maurerCartanForm (JetGaugeGroupI.ofConstant U₀) = 0 := by
  ext <;> simp [maurerCartanForm,JetGaugeGroupI.deriv_ofConstant]

lemma maurerCartanForm_cocycle (U V : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3) :
    maurerCartanForm (U * V) μ = maurerCartanForm U μ + adjoint U (maurerCartanForm V μ) := by
  have h1 : V.toVal * (V⁻¹).toVal = 1 := by
    rw [show V.toVal * (V⁻¹).toVal = (V * V⁻¹).toVal from rfl, mul_inv_cancel]; rfl
  have key : Complex.I • (JetGaugeGroupI.deriv μ (U * V) * ((U * V)⁻¹).toVal) =
      Complex.I • (JetGaugeGroupI.deriv μ U * (U⁻¹).toVal) +
        U.toVal * (Complex.I • (JetGaugeGroupI.deriv μ V * (V⁻¹).toVal)) * (U⁻¹).toVal := by
    rw [show ((U * V)⁻¹).toVal = (V⁻¹).toVal * (U⁻¹).toVal from by rw [mul_inv_rev]; rfl,
      JetGaugeGroupI.deriv_mul, add_mul, smul_add, mul_smul_comm, smul_mul_assoc]
    congr 1
    · rw [mul_assoc (JetGaugeGroupI.deriv μ U), ← mul_assoc V.toVal, h1, one_mul]
    · simp [mul_assoc]
  refine ext_of_matrix (congrArg (fun p => p.1) key) (congrArg (fun p => p.2.1) key) ?_
  have h22 : (maurerCartanForm (U * V) μ).toU1Value =
      (maurerCartanForm U μ).toU1Value +
        U.2.2.1 * (maurerCartanForm V μ).toU1Value * star U.2.2.1 :=
    congrArg (fun p => p.2.2) key
  rw [h22, mul_comm (U.2.2.1 : JetRing) ((maurerCartanForm V μ).toU1Value), mul_assoc,
    (Unitary.mem_iff.mp U.2.2.2).2, mul_one]
  rfl

lemma maurerCartanForm_inv (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3) :
    maurerCartanForm (U⁻¹) μ = - adjoint U⁻¹ (maurerCartanForm U μ) := by
  linear_combination (norm := simp) -(maurerCartanForm_cocycle  U⁻¹ U μ)

lemma deriv_zero_of_maurerCartanForm_zero (U : JetGaugeGroupI) (h : maurerCartanForm U = 0) :
    ∀ μ, U.deriv μ = 0 := by
  intro μ
  have h1 : maurerCartanForm U μ = 0 := congrFun h μ
  -- extract the underlying value triple of the vanishing algebra element
  have h2 : Complex.I • (JetGaugeGroupI.deriv μ U * (U⁻¹).toVal) = 0 :=
    Prod.ext (congrArg (fun a => a.1.1) h1)
      (Prod.ext (congrArg (fun a => a.2.1.1) h1) (congrArg (fun a => a.2.2.1) h1))
  -- cancel the scalar `i`
  have hml : (-Complex.I) * Complex.I = 1 := by simp [neg_mul, Complex.I_mul_I]
  have h3 : JetGaugeGroupI.deriv μ U * (U⁻¹).toVal = 0 := by
    have h4 := congrArg (fun X => (-Complex.I) • X) h2
    simpa [smul_smul, hml] using h4
  -- cancel `U⁻¹` on the right
  have h5 : (U⁻¹).toVal * U.toVal = 1 := by
    rw [show (U⁻¹).toVal * U.toVal = (U⁻¹ * U).toVal from rfl, inv_mul_cancel]
    rfl
  calc JetGaugeGroupI.deriv μ U
      = JetGaugeGroupI.deriv μ U * ((U⁻¹).toVal * U.toVal) := by rw [h5, mul_one]
    _ = JetGaugeGroupI.deriv μ U * (U⁻¹).toVal * U.toVal := by rw [mul_assoc]
    _ = 0 := by rw [h3, zero_mul]

lemma maurerCartanForm_eq_zero_iff_ofConstant (U : JetGaugeGroupI) :
    maurerCartanForm U = 0 ↔ ∃ c, U = JetGaugeGroupI.ofConstant c := by
  constructor
  · intro h
    -- Step 1: all first derivatives of `U` vanish.
    have hderiv := deriv_zero_of_maurerCartanForm_zero U h
    -- Step 2: a jet with vanishing first derivatives is the constant jet of its value.
    have hconst : ∀ f : JetRing, (∀ μ, pderiv ℂ μ f = 0) → f = C (constantCoeff f) := by
      intro f hf
      refine pderiv.ext (fun i => ?_) ?_
      · rw [hf i, pderiv_C]
      · rw [constantCoeff_C]
    refine ⟨U.eval, Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))⟩
    · show U.1.1 = ((JetGaugeGroupI.ofConstant U.eval).1 : Matrix (Fin 3) (Fin 3) JetRing)
      ext i j : 1
      exact hconst (U.1.1 i j) fun μ => by
        simpa [JetGaugeGroupI.deriv, Matrix.map_apply] using
          congrArg (fun p => (p.1 : Matrix (Fin 3) (Fin 3) JetRing) i j) (hderiv μ)
    · show U.2.1.1 = ((JetGaugeGroupI.ofConstant U.eval).2.1 : Matrix (Fin 2) (Fin 2) JetRing)
      ext i j : 1
      exact hconst (U.2.1.1 i j) fun μ => by
        simpa [JetGaugeGroupI.deriv, Matrix.map_apply] using
          congrArg (fun p => (p.2.1 : Matrix (Fin 2) (Fin 2) JetRing) i j) (hderiv μ)
    · show U.2.2.1 = ((JetGaugeGroupI.ofConstant U.eval).2.2 : JetRing)
      exact hconst U.2.2.1 fun μ => congrArg (fun p => (p.2.2 : JetRing)) (hderiv μ)
  · rintro ⟨c, rfl⟩
    exact maurerCartanForm_ofConstant c

/-!

## The symmeterized Maurer–Cartan form

-/

TODO "The symmetrizedMaurerCartanForm should actually land in the normal gauge algebra."
noncomputable def symmetrizedMaurerCartanForm (U : JetGaugeGroupI)
    (r :  Multiset (Fin 1 ⊕ Fin 3)) : JetGaugeAlgebra :=
  (1/(r.card : ℝ) : ℝ) • (r.map fun μ => (iteratedDeriv (r - {μ})  (maurerCartanForm U μ))).sum

@[simp]
lemma symmetrizedMaurerCartanForm_zero (U : JetGaugeGroupI) :
    symmetrizedMaurerCartanForm U 0 = 0 := by
  simp [symmetrizedMaurerCartanForm]

@[simp]
lemma symmetrizedMaurerCartanForm_ofConstant (U₀ : GaugeGroupI) :
    symmetrizedMaurerCartanForm (JetGaugeGroupI.ofConstant U₀) = 0 := by
  ext <;> simp [symmetrizedMaurerCartanForm, maurerCartanForm_ofConstant]

@[simp]
lemma symmetrizedMaurerCartanForm_singleton (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3) :
    symmetrizedMaurerCartanForm U {μ} = maurerCartanForm U μ := by
  simp [symmetrizedMaurerCartanForm, iteratedDeriv_zero]

end StandardModel
