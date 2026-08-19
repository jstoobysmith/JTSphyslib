/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeBosons.AlgebraValued.Basic
/-!

# Adjoint gauge tensors and the covariant derivative

A component family is an *adjoint gauge tensor* when all its derivative symbols
transform by the pure Leibniz convolution of the dual adjoint action, with no
inhomogeneous term. The convolution is forced: the gauge group acts on the
derivative symbols by substitution and the chain rule, so `U • [∂_s F^φ]` produces
every splitting `s = x + y` — `x` derivatives hitting the adjoint, `y` remaining on
`F`; the naive law `U • [∂_s F^φ] = F^{(∂_s Ad)^* φ}` holds only at `s = 0`.

The two theorems of this section: the field strength is an adjoint gauge tensor
(`transformsInAdjoint_fieldStrength`), and adjoint gauge tensors are closed under
the covariant derivative `∇_ρ = D_ρ + ⁅A_ρ, ·⁆`
(`TransformsInAdjoint.covDerivAdjoint`) — so by recursion every iterated covariant
derivative of the field strength is an adjoint gauge tensor.

-/

@[expose] public section

namespace StandardModel
open Matrix MatrixGroups TensorProduct
variable {B : Type} [Ring B] [Algebra ℂ B]

namespace IsGaugeField

variable {repLorentz : Representation ℂ SL(2,ℂ) B}
variable {repGauge : Representation ℂ JetGaugeGroupI B}
variable {A : (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B}
variable {D : (Fin 1 ⊕ Fin 3) → B →ₗ[ℂ] B}
variable [Lorentz.IsLorentzDeriv repLorentz D]
variable {D_comm : ∀ μ ν, (D μ).comp (D ν) = (D ν).comp (D μ)}

/-- A component family `F` *transforms in the adjoint* (is an adjoint gauge tensor)
  for the gauge field `hA` when each derivative symbol `[∂_s F^φ]` transforms by the
  Leibniz convolution of the dual adjoint coefficients against lower derivative
  symbols — the shape of `gauge_apply_deriv` with no Maurer–Cartan shift. At `s = 0`
  this is the homogeneous law `U • F^φ = F^{Ad₀^* φ}`. The `hA` argument pins the
  representations and derivative to the gauge-field setting. -/
def TransformsInAdjoint (_hA : IsGaugeField repLorentz repGauge A D D_comm)
    (F : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B) : Prop :=
  ∀ (U : JetGaugeGroupI) (φ : Module.Dual ℝ GaugeAlgebra) (s : Multiset (Fin 1 ⊕ Fin 3)),
    repGauge U (Lorentz.iteratedD D D_comm s (F φ)) =
      (s.antidiagonal.map fun p =>
        Lorentz.iteratedD D D_comm p.2 (F (adjointDualCoeff U⁻¹ p.1 φ))).sum

/-- The covariant derivative `∇_ρ F = D_ρ F + ⁅A_ρ, F⁆` of an adjoint-valued
  component family: the total derivative plus the bracket against the gauge field.
  The gauge-algebra bracket carries the physicists' `i`, so in matrix terms this is
  `∂_ρ F + i [A_ρ, F]` — the adjoint-representation covariant derivative in the same
  `D = ∂ + i A` convention as the field strength. It preserves `TransformsInAdjoint`
  (`TransformsInAdjoint.covDerivAdjoint`). -/
noncomputable def covDerivAdjoint
    (A : (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (F : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (D : (Fin 1 ⊕ Fin 3) → B →ₗ[ℂ] B) (ρ : Fin 1 ⊕ Fin 3) :
    Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B :=
  (D ρ).restrictScalars ℝ ∘ₗ F + bracketFam (A ρ) F

@[simp]
lemma covDerivAdjoint_apply (A : (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (F : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (D : (Fin 1 ⊕ Fin 3) → B →ₗ[ℂ] B) (ρ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ GaugeAlgebra) :
    covDerivAdjoint A F D ρ φ = D ρ (F φ) + bracketFam (A ρ) F φ := rfl

/-!

## The iterated covariance of the covariant derivative

-/

/-- If `F` transforms in the adjoint, so do its `κ ::ₘ s`-derived symbols with the
  extra derivative traced through `adjointDualCoeff_cons`: the Leibniz splittings
  where `κ` stays a derivative, minus the convolution where `κ` hits the adjoint —
  an `ad` of the derived Maurer–Cartan form. -/
lemma TransformsInAdjoint.repGauge_iteratedD_cons
    {hA : IsGaugeField repLorentz repGauge A D D_comm}
    {F : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B} (hF : hA.TransformsInAdjoint F)
    (U : JetGaugeGroupI) (κ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℝ GaugeAlgebra) :
    repGauge U (Lorentz.iteratedD D D_comm (κ ::ₘ s) (F φ)) =
      (s.antidiagonal.map fun p =>
        Lorentz.iteratedD D D_comm (κ ::ₘ p.2) (F (adjointDualCoeff U⁻¹ p.1 φ))).sum
      - (s.antidiagonal.map fun p =>
          (p.1.antidiagonal.map fun q =>
            Lorentz.iteratedD D D_comm p.2 (F (adjointDualCoeff U⁻¹ q.2
              (φ ∘ₗ LieAlgebra.ad ℝ GaugeAlgebra (JetGaugeAlgebra.eval
                (JetGaugeAlgebra.iteratedDeriv q.1
                  (maurerCartanForm U⁻¹ κ))))))).sum).sum := by
  rw [hF U φ (κ ::ₘ s)]
  simp only [Multiset.antidiagonal_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
  have hsec : (Multiset.map (fun p => Lorentz.iteratedD D D_comm p.2
        (F (adjointDualCoeff U⁻¹ (κ ::ₘ p.1) φ))) s.antidiagonal).sum =
      -(s.antidiagonal.map fun p =>
          (p.1.antidiagonal.map fun q =>
            Lorentz.iteratedD D D_comm p.2 (F (adjointDualCoeff U⁻¹ q.2
              (φ ∘ₗ LieAlgebra.ad ℝ GaugeAlgebra (JetGaugeAlgebra.eval
                (JetGaugeAlgebra.iteratedDeriv q.1
                  (maurerCartanForm U⁻¹ κ))))))).sum).sum := by
    rw [← Multiset.sum_map_neg'']
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [adjointDualCoeff_cons U⁻¹ κ p.1 φ, map_neg, map_neg, map_multiset_sum,
      Multiset.map_map, map_multiset_sum, Multiset.map_map]
    exact congrArg Neg.neg (congrArg Multiset.sum (Multiset.map_congr rfl fun q hq => rfl))
  rw [hsec, sub_eq_add_neg]

set_option maxHeartbeats 2000000 in
/-- The all-orders gauge transformation of the derived bracket `⁅A_ρ, F⁆` against an
  adjoint gauge tensor `F`: since `F` transforms homogeneously, only one `ad`
  cross-term convolution survives — the analogue of `repGauge_iteratedD_commutator`
  with a gauge tensor in the second slot. -/
lemma TransformsInAdjoint.repGauge_iteratedD_bracket
    {hA : IsGaugeField repLorentz repGauge A D D_comm}
    (hD : ∀ (κ : Fin 1 ⊕ Fin 3) (b₁ b₂ : B), D κ (b₁ * b₂) = D κ b₁ * b₂ + b₁ * D κ b₂)
    {F : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B} (hF : hA.TransformsInAdjoint F)
    (U : JetGaugeGroupI) (s : Multiset (Fin 1 ⊕ Fin 3)) (ρ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ GaugeAlgebra) :
    repGauge U (Lorentz.iteratedD D D_comm s (bracketFam (A ρ) F φ)) =
      (s.antidiagonal.map fun p =>
        Lorentz.iteratedD D D_comm p.2 (bracketFam (A ρ) F
          (adjointDualCoeff U⁻¹ p.1 φ))).sum
      + (s.antidiagonal.map fun p =>
          (p.2.antidiagonal.map fun r =>
            Lorentz.iteratedD D D_comm r.2 (F (adjointDualCoeff U⁻¹ r.1
              (φ ∘ₗ LieAlgebra.ad ℝ GaugeAlgebra (JetGaugeAlgebra.eval
                (JetGaugeAlgebra.iteratedDeriv p.1
                  (maurerCartanForm U⁻¹ ρ))))))).sum).sum := by
  have hAlaw : ∀ (u : Multiset (Fin 1 ⊕ Fin 3)) (ψ : Module.Dual ℝ GaugeAlgebra),
      repGauge U (((Lorentz.iteratedD D D_comm u).restrictScalars ℝ ∘ₗ A ρ) ψ) =
        ((u.antidiagonal.map fun q =>
          (Lorentz.iteratedD D D_comm q.2).restrictScalars ℝ ∘ₗ A ρ ∘ₗ
            adjointDualCoeff U⁻¹ q.1).sum) ψ
        + algebraMap ℂ B (ψ (JetGaugeAlgebra.eval
            (JetGaugeAlgebra.iteratedDeriv u (maurerCartanForm U⁻¹ ρ)))) := by
    intro u ψ
    show repGauge U (Lorentz.iteratedD D D_comm u (A ρ ψ)) = _
    rw [hA.gauge_apply_deriv U u ρ ψ, Multiset.sum_linearMap_apply, Multiset.map_map]
    congr 1
  have hFlaw : ∀ (u : Multiset (Fin 1 ⊕ Fin 3)) (ψ : Module.Dual ℝ GaugeAlgebra),
      repGauge U (((Lorentz.iteratedD D D_comm u).restrictScalars ℝ ∘ₗ F) ψ) =
        ((u.antidiagonal.map fun r =>
          (Lorentz.iteratedD D D_comm r.2).restrictScalars ℝ ∘ₗ F ∘ₗ
            adjointDualCoeff U⁻¹ r.1).sum) ψ
        + algebraMap ℂ B (ψ (0 : GaugeAlgebra)) := by
    intro u ψ
    show repGauge U (Lorentz.iteratedD D D_comm u (F ψ)) = _
    rw [hF U ψ u, Multiset.sum_linearMap_apply, Multiset.map_map]
    simp only [map_zero, Complex.ofReal_zero, add_zero]
    congr 1
  have hMa : (s.antidiagonal.map fun p =>
      bracketFam ((p.1.antidiagonal.map fun q =>
          (Lorentz.iteratedD D D_comm q.2).restrictScalars ℝ ∘ₗ A ρ ∘ₗ
            adjointDualCoeff U⁻¹ q.1).sum)
        ((p.2.antidiagonal.map fun r =>
          (Lorentz.iteratedD D D_comm r.2).restrictScalars ℝ ∘ₗ F ∘ₗ
            adjointDualCoeff U⁻¹ r.1).sum) φ).sum =
      (s.antidiagonal.map fun p =>
        (p.1.antidiagonal.map fun q =>
          (p.2.antidiagonal.map fun r =>
            bracketFam ((Lorentz.iteratedD D D_comm q.2).restrictScalars ℝ ∘ₗ A ρ ∘ₗ
                adjointDualCoeff U⁻¹ q.1)
              ((Lorentz.iteratedD D D_comm r.2).restrictScalars ℝ ∘ₗ F ∘ₗ
                adjointDualCoeff U⁻¹ r.1) φ).sum).sum).sum := by
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [bracketFam_sum_left, Multiset.sum_linearMap_apply, Multiset.map_map,
      Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun q hq => ?_)
    simp only [Function.comp_apply]
    rw [bracketFam_sum_right, Multiset.sum_linearMap_apply, Multiset.map_map,
      Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun r hr => ?_)
    simp only [Function.comp_apply]
  have hMc : (s.antidiagonal.map fun p =>
      Lorentz.iteratedD D D_comm p.2 (bracketFam (A ρ) F
        (adjointDualCoeff U⁻¹ p.1 φ))).sum =
      (s.antidiagonal.map fun p =>
        (p.1.antidiagonal.map fun q =>
          (p.2.antidiagonal.map fun r =>
            bracketFam ((Lorentz.iteratedD D D_comm r.1).restrictScalars ℝ ∘ₗ A ρ ∘ₗ
                adjointDualCoeff U⁻¹ q.1)
              ((Lorentz.iteratedD D D_comm r.2).restrictScalars ℝ ∘ₗ F ∘ₗ
                adjointDualCoeff U⁻¹ q.2) φ).sum).sum).sum := by
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [bracketFam_adjointDualCoeff U⁻¹ p.1 (A ρ) F φ,
      map_multiset_sum, Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun q hq => ?_)
    simp only [Function.comp_apply]
    rw [iteratedD_bracketFam hD p.2 (A ρ ∘ₗ adjointDualCoeff U⁻¹ q.1)
      (F ∘ₗ adjointDualCoeff U⁻¹ q.2) φ]
  have hM := hMa.trans ((Multiset.sum_antidiagonal_exchange s fun a b c d =>
      bracketFam ((Lorentz.iteratedD D D_comm b).restrictScalars ℝ ∘ₗ A ρ ∘ₗ
          adjointDualCoeff U⁻¹ a)
        ((Lorentz.iteratedD D D_comm d).restrictScalars ℝ ∘ₗ F ∘ₗ
          adjointDualCoeff U⁻¹ c) φ).trans hMc.symm)
  have hCg : ∀ p : Multiset (Fin 1 ⊕ Fin 3) × Multiset (Fin 1 ⊕ Fin 3),
      ((p.2.antidiagonal.map fun r =>
        (Lorentz.iteratedD D D_comm r.2).restrictScalars ℝ ∘ₗ F ∘ₗ
          adjointDualCoeff U⁻¹ r.1).sum)
        (φ ∘ₗ LieAlgebra.ad ℝ GaugeAlgebra (JetGaugeAlgebra.eval
          (JetGaugeAlgebra.iteratedDeriv p.1 (maurerCartanForm U⁻¹ ρ)))) =
      (p.2.antidiagonal.map fun r =>
        Lorentz.iteratedD D D_comm r.2 (F (adjointDualCoeff U⁻¹ r.1
          (φ ∘ₗ LieAlgebra.ad ℝ GaugeAlgebra (JetGaugeAlgebra.eval
            (JetGaugeAlgebra.iteratedDeriv p.1 (maurerCartanForm U⁻¹ ρ))))))).sum := by
    intro p
    rw [Multiset.sum_linearMap_apply, Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun r hr => ?_)
    simp only [Function.comp_apply, LinearMap.coe_comp, LinearMap.restrictScalars_apply]
  rw [iteratedD_bracketFam hD s (A ρ) F φ, map_multiset_sum, Multiset.map_map,
    Multiset.map_congr rfl (fun p hp => by
      rw [Function.comp_apply, hA.repGauge_bracketFam U (hAlaw p.1) (hFlaw p.2) φ,
        hCg p, map_zero, LinearMap.comp_zero, map_zero, sub_zero, lie_zero, map_zero,
        Complex.ofReal_zero, map_zero, add_zero]),
    Multiset.sum_map_add, hM]

set_option maxHeartbeats 2000000 in
/-- **Adjoint gauge tensors are closed under the covariant derivative**: if `F`
  transforms in the adjoint, so does `∇_ρ F = D_ρ F + ⁅A_ρ, F⁆`. The single
  inhomogeneous convolution of `∂_{ρ ::ₘ s} F`
  (`TransformsInAdjoint.repGauge_iteratedD_cons`) cancels the single `ad` cross-term
  convolution of `⁅A_ρ, F⁆` (`TransformsInAdjoint.repGauge_iteratedD_bracket`)
  through the coassociativity of the antidiagonal; no structural equation is needed.
  Together with `transformsInAdjoint_fieldStrength` this makes every iterated
  covariant derivative of the field strength an adjoint gauge tensor, by recursion. -/
theorem TransformsInAdjoint.covDerivAdjoint
    {hA : IsGaugeField repLorentz repGauge A D D_comm}
    (hD : ∀ (κ : Fin 1 ⊕ Fin 3) (b₁ b₂ : B), D κ (b₁ * b₂) = D κ b₁ * b₂ + b₁ * D κ b₂)
    {F : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B} (hF : hA.TransformsInAdjoint F)
    (ρ : Fin 1 ⊕ Fin 3) :
    hA.TransformsInAdjoint (covDerivAdjoint A F D ρ) := by
  intro U φ s
  have hDcomp : ∀ (κ : Fin 1 ⊕ Fin 3) (t : Multiset (Fin 1 ⊕ Fin 3)) (b : B),
      Lorentz.iteratedD D D_comm t (D κ b) = Lorentz.iteratedD D D_comm (κ ::ₘ t) b := by
    intro κ t b
    rw [show (κ ::ₘ t : Multiset (Fin 1 ⊕ Fin 3)) = t + {κ} from by
        rw [add_comm, Multiset.singleton_add],
      Lorentz.iteratedD_add, LinearMap.comp_apply]
    congr 1
  have hL : repGauge U (Lorentz.iteratedD D D_comm s
      (IsGaugeField.covDerivAdjoint A F D ρ φ)) =
      repGauge U (Lorentz.iteratedD D D_comm (ρ ::ₘ s) (F φ))
      + repGauge U (Lorentz.iteratedD D D_comm s (bracketFam (A ρ) F φ)) := by
    rw [covDerivAdjoint_apply, map_add, hDcomp ρ s, map_add]
  have hR : (s.antidiagonal.map fun p =>
      Lorentz.iteratedD D D_comm p.2 (IsGaugeField.covDerivAdjoint A F D ρ
        (adjointDualCoeff U⁻¹ p.1 φ))).sum =
      (s.antidiagonal.map fun p =>
        Lorentz.iteratedD D D_comm (ρ ::ₘ p.2) (F (adjointDualCoeff U⁻¹ p.1 φ))).sum
      + (s.antidiagonal.map fun p =>
        Lorentz.iteratedD D D_comm p.2 (bracketFam (A ρ) F
          (adjointDualCoeff U⁻¹ p.1 φ))).sum := by
    rw [← Multiset.sum_map_add]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [covDerivAdjoint_apply, map_add, hDcomp ρ p.2]
  have hcancel : (s.antidiagonal.map fun p =>
      (p.1.antidiagonal.map fun q =>
        Lorentz.iteratedD D D_comm p.2 (F (adjointDualCoeff U⁻¹ q.2
          (φ ∘ₗ LieAlgebra.ad ℝ GaugeAlgebra (JetGaugeAlgebra.eval
            (JetGaugeAlgebra.iteratedDeriv q.1
              (maurerCartanForm U⁻¹ ρ))))))).sum).sum =
    (s.antidiagonal.map fun p =>
      (p.2.antidiagonal.map fun r =>
        Lorentz.iteratedD D D_comm r.2 (F (adjointDualCoeff U⁻¹ r.1
          (φ ∘ₗ LieAlgebra.ad ℝ GaugeAlgebra (JetGaugeAlgebra.eval
            (JetGaugeAlgebra.iteratedDeriv p.1
              (maurerCartanForm U⁻¹ ρ))))))).sum).sum :=
    Multiset.sum_antidiagonal_assoc s (fun a b c =>
      Lorentz.iteratedD D D_comm c (F (adjointDualCoeff U⁻¹ b
        (φ ∘ₗ LieAlgebra.ad ℝ GaugeAlgebra (JetGaugeAlgebra.eval
          (JetGaugeAlgebra.iteratedDeriv a (maurerCartanForm U⁻¹ ρ)))))))
  rw [hL, hF.repGauge_iteratedD_cons U ρ s φ, hF.repGauge_iteratedD_bracket hD U s ρ φ,
    hR, hcancel]
  abel

end IsGaugeField

end StandardModel
