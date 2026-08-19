/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.Jet.Basic
public import Physlib.Particles.StandardModel.GaugeAlgebra.JetGaugeAlgebra
public import Physlib.Particles.StandardModel.GaugeGroup.MaurerCartan.Basic
public import Physlib.Relativity.IsLorentzDeriv
public import Physlib.Relativity.Tensors.ComplexTensor.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Representation
public import Physlib.Relativity.SL2C.Basic
/-!
# Algebra valued gauge bosons

An algebra `B` (for instance a jet algebra of Lagrangian terms) may contain a family of
elements playing the role of the gauge-field symbols `[∂_s A_μ^a]`. This file defines
what it means for such a family to *be* a set of gauge bosons: the structure
`IsGaugeField` records the transformation laws that the physicists' gauge field
satisfies, with nothing postulated beyond them.

## The physics

Let `A_μ^a` be a gauge field for the gauge group `G`, with `μ` a spacetime (covector)
index and `a` an adjoint index. Under a gauge transformation `g` the field transforms as

  `A_μ ↦ Ad_g A_μ + mc(g)_μ`,

where `mc(g)_μ = i (∂_μ g) g⁻¹` is the Maurer–Cartan form. The symbols `[∂_s A_μ^a]`
are coordinate functions on the space of field configurations, so the induced (left)
action is the pullback along `g⁻¹`: one substitutes `g⁻¹` into the field law and
differentiates `s` times with the Leibniz rule:

  `g • [∂_s A_μ^a] = ∑_{x+y=s} C(x,y) (∂_x (Ad_{g⁻¹})^a_b)| [∂_y A_μ^b]`
  `                  + (∂_s mc(g⁻¹)_μ^a)|`,

where `C(x,y)` is the multinomial coefficient of the splitting and `|` denotes
evaluation at the base point. All the data on the right is carried by the *jet* of the
gauge transformation, which is why the gauge representation below is a representation
of `JetGaugeGroupI` and not merely of `GaugeGroupI`.

## The formalization dictionary

* `A μ φ` is the symbol `A_μ^a` contracted with a dual adjoint vector `φ`; the
  derivative symbols `[∂_s A_μ^a]` are its images `iteratedD D deriv_comm s (A μ φ)` under the
  total derivative `D`.
* `∂_x (Ad_{g⁻¹})^a_b|` acting on the dual index is `adjointDualCoeff g⁻¹ x φ`:
  include the constant algebra element into jets, act by the adjoint of `g⁻¹`,
  differentiate `x` times, evaluate at the base point, and pair with `φ`.
* The sum `∑_{x+y=s} C(x,y)` is the sum over `s.antidiagonal`: a splitting `(x, y)`
  occurs in the antidiagonal of the multiset `s` with multiplicity exactly `C(x,y)`.
* `(∂_s mc(g⁻¹)_μ)|` is `JetGaugeAlgebra.eval (iteratedDeriv s (maurerCartanForm g⁻¹ μ))`,
  a constant algebra element, paired with `φ` and embedded in `B` as a scalar.

-/

@[expose] public section

namespace StandardModel
open Matrix MatrixGroups
variable {B : Type} [Ring B] [Algebra ℂ B]

/-- The physicists' `∂_x (Ad_{U})^a_b|` acting on the dual adjoint index of a
  gauge-field symbol: precomposition of `φ` with the constant inclusion into jets,
  followed by the adjoint action of `U`, `x` formal derivatives, and evaluation at
  the base point. For `x = 0` this is the dual (contragredient) adjoint action of
  the value `U₀`; for `x ≠ 0` it sees the derivatives of the gauge transformation. -/
noncomputable def adjointDualCoeff (U : JetGaugeGroupI) (x : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℝ GaugeAlgebra) : Module.Dual ℝ GaugeAlgebra :=
  φ ∘ₗ JetGaugeAlgebra.eval.toLinearMap ∘ₗ JetGaugeAlgebra.iteratedDeriv x ∘ₗ
    JetGaugeAlgebra.adjointMap U ∘ₗ JetGaugeAlgebra.ofConstant

/-- The family `A` of symbols in the algebra `B` is a gauge field for the total
  derivative `D`, the Lorentz representation `repLorentz` and the gauge representation
  `repGauge`, when it satisfies the transformation laws of the physicists' gauge field:

  * it presupposes (as arguments, not fields) that `D` is a Lorentz derivative — the
    instance `Lorentz.IsLorentzDeriv repLorentz D` — and that its components commute
    (`deriv_comm`), as total derivatives do;
  * the symbol `A_μ^a` carries one covector index, transforming through the columns of
    the Lorentz matrix (`lorentz_A`);
  * under a gauge jet `U` the derivative symbols `[∂_s A_μ^a]` transform by the
    Leibniz expansion of `A_μ ↦ Ad_{U⁻¹} A_μ + mc(U⁻¹)_μ` (`gauge_A`) — the adjoint
    convolution plus the inhomogeneous Maurer–Cartan shift. The inverse makes the
    action a left action, exactly as in `φ'(x) = φ(Λ⁻¹ x)`. -/
structure IsGaugeField (repLorentz : Representation ℂ SL(2,ℂ) B)
    (repGauge : Representation ℂ JetGaugeGroupI B)
    (A : (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (D : (Fin 1 ⊕ Fin 3) → B →ₗ[ℂ] B)
    [Lorentz.IsLorentzDeriv repLorentz D]
    (deriv_comm : ∀ μ ν, (D μ).comp (D ν) = (D ν).comp (D μ)) : Prop where
  /-- The gauge-field symbol carries one covector Lorentz index. -/
  lorentz_apply : ∀ (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra),
    repLorentz Λ (A μ φ) =
      ∑ a, (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) • A a φ
  /-- The gauge transformation of the derivative symbols `[∂_s A_μ^a]`: the Leibniz
    convolution of the dual adjoint action of `U⁻¹` against lower derivative symbols
    (the multiset antidiagonal carries the multinomial coefficients), plus the
    base-point value of the `s`-th derivative of the Maurer–Cartan form of `U⁻¹`. -/
  gauge_apply_deriv : ∀ (U : JetGaugeGroupI) (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℝ GaugeAlgebra),
    repGauge U (Lorentz.iteratedD D deriv_comm s (A μ φ)) =
      (s.antidiagonal.map fun p =>
        Lorentz.iteratedD D deriv_comm p.2 (A μ (adjointDualCoeff U⁻¹ p.1 φ))).sum
      + algebraMap ℂ B
          (φ (JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv s (maurerCartanForm U⁻¹ μ))))

namespace IsGaugeField

variable {repLorentz : Representation ℂ SL(2,ℂ) B}
variable {repGauge : Representation ℂ JetGaugeGroupI B}
variable {A : (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B}
variable {D : (Fin 1 ⊕ Fin 3) → B →ₗ[ℂ] B}
variable [Lorentz.IsLorentzDeriv repLorentz D]
variable {D_comm : ∀ μ ν, (D μ).comp (D ν) = (D ν).comp (D μ)}

/-- The gauge transformation of the underived symbol `A_μ^φ`: the special case `s = 0`
  of `gauge_apply_deriv`, with no Leibniz convolution left over — the dual adjoint
  action of the value of `U⁻¹` plus the Maurer–Cartan shift. -/
lemma gauge_apply (hA : IsGaugeField repLorentz repGauge A D D_comm) (U : JetGaugeGroupI)
    (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra) :
    repGauge U (A μ φ) = A μ (adjointDualCoeff U⁻¹ ∅ φ) +
      algebraMap ℂ B (φ (JetGaugeAlgebra.eval (maurerCartanForm U⁻¹ μ))) := by
  simpa [Lorentz.iteratedD, show (∅ : Multiset (Fin 1 ⊕ Fin 3)) = 0 from rfl] using
    hA.gauge_apply_deriv U 0 μ φ

end IsGaugeField

end StandardModel
