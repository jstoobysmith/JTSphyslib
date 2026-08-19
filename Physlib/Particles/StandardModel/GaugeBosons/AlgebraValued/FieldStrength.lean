/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeBosons.AlgebraValued.Basic
public import Physlib.Particles.StandardModel.GaugeBosons.AlgebraValued.TransformsInAdjoint
/-!

# The field strength

The field strength is defined as
```
  F_{μν} = D_μ A_ν − D_ν A_μ + ⁅A_μ, A_ν⁆
```
with `⁅·,·⁆` the gauge-algebra bracket, which already carries the physicists' factor
of `i` (on the matrix factors `⁅a, b⁆ = i(ab − ba)`). In terms of the plain matrix
commutator this is `F_{μν} = D_μ A_ν − D_ν A_μ + i [A_μ, A_ν]`, the sign forced by
the convention `ω_μ(g) = i (∂_μ g) g⁻¹` for the Maurer–Cartan form (equivalently, by
its structural equation `∂_μ ω_ν − ∂_ν ω_μ + ⁅ω_μ, ω_ν⁆ = 0`): only with this
coefficient do the inhomogeneous terms cancel. It transforms under the gauge
transformation covariantly via the adjoint action (`repGauge_fieldStrength`).

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

/-- The field strength `F_μν = D_μ A_ν − D_ν A_μ + ⁅A_μ, A_ν⁆` of a family of
  gauge-field symbols, as a component family: the derivative terms through the total
  derivative `D`, the commutator term through `commutator`. This is the physicists'
  `F_μν^a = ∂_μ A_ν^a − ∂_ν A_μ^a + f^a_{bc} A_μ^b A_ν^c`: the gauge-algebra bracket
  already carries the physicists' factor of `i`, so no explicit factor appears — the
  same normalization as in the structural equation of the Maurer–Cartan form, which
  is exactly what makes the field strength transform without inhomogeneous terms
  (`repGauge_fieldStrength`). -/
noncomputable def fieldStrength (A : (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (D : (Fin 1 ⊕ Fin 3) → B →ₗ[ℂ] B) (μ ν : Fin 1 ⊕ Fin 3) :
    Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B :=
  (D μ).restrictScalars ℝ ∘ₗ A ν - (D ν).restrictScalars ℝ ∘ₗ A μ + commutator A μ ν

@[simp]
lemma fieldStrength_apply (A : (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (D : (Fin 1 ⊕ Fin 3) → B →ₗ[ℂ] B) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ GaugeAlgebra) :
    fieldStrength A D μ ν φ = D μ (A ν φ) - D ν (A μ φ) + commutator A μ ν φ := rfl


set_option maxHeartbeats 400000 in
/-- **The field strength transforms in the adjoint.** Under a gauge jet `U` all
  inhomogeneous terms in the transformation of `F_μν = D_μ A_ν − D_ν A_μ + ⁅A_μ, A_ν⁆`
  cancel: the Leibniz cross terms of the derivatives against the commutator cross
  terms (`adjointDualCoeff_singleton`), and the derived Maurer–Cartan shifts against
  the bracket of the two shifts (the structural equation of the Maurer–Cartan form).
  What remains is the base-point dual adjoint action of `U⁻¹` on the adjoint index. -/
lemma repGauge_fieldStrength (hA : IsGaugeField repLorentz repGauge A D D_comm)
    (U : JetGaugeGroupI) (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra) :
    repGauge U (fieldStrength A D μ ν φ) = fieldStrength A D μ ν (adjointDualCoeff U⁻¹ 0 φ) := by
  -- the structural equation of the Maurer–Cartan form, under `φ ∘ eval`
  have hstruct :
      φ (JetGaugeAlgebra.eval (JetGaugeAlgebra.deriv μ (maurerCartanForm U⁻¹ ν))) =
      φ (JetGaugeAlgebra.eval (JetGaugeAlgebra.deriv ν (maurerCartanForm U⁻¹ μ)))
      - φ ⁅JetGaugeAlgebra.eval (maurerCartanForm U⁻¹ μ),
          JetGaugeAlgebra.eval (maurerCartanForm U⁻¹ ν)⁆ := by
    have h0 := congrArg (fun z => φ (JetGaugeAlgebra.eval z))
      (maurerCartanForm_structure U⁻¹ μ ν)
    simp only [map_add, map_sub, map_zero, LieHom.map_lie] at h0
    linarith
  rw [fieldStrength_apply, fieldStrength_apply, map_add, map_sub,
    hA.repGauge_deriv_apply U μ ν φ, hA.repGauge_deriv_apply U ν μ φ,
    hA.repGauge_commutator U μ ν φ, adjointDualCoeff_singleton U⁻¹ μ φ,
    adjointDualCoeff_singleton U⁻¹ ν φ, map_neg, map_neg, hstruct,
    Complex.ofReal_sub, map_sub]
  abel

set_option maxHeartbeats 1000000 in
/-- **The transformation law of the derived field strength**: for `D` a derivation
  (Leibniz rule, taken as the hypothesis `hD` since `IsGaugeField` does not postulate
  it), the once-derived field strength transforms by the Leibniz convolution of the
  dual adjoint action against the underived field strength — with *no* Maurer–Cartan
  shift, since the field strength itself transforms homogeneously:

  `U • ∂_ρ F_μν^φ = ∂_ρ (F_μν^{Ad₀* φ}) + F_μν^{(∂_ρ Ad)* φ}`.

  All inhomogeneous terms cancel: the two-derivative Leibniz terms of the fields
  against the cross terms of the derived commutator (`adjointDualCoeff_pair` and
  `adjointDualCoeff_singleton`), and the twice-derived Maurer–Cartan shifts against
  the brackets of shifts (the `∂_ρ`-derivative of the structural equation). -/
theorem repGauge_deriv_fieldStrength (hA : IsGaugeField repLorentz repGauge A D D_comm)
    (hD : ∀ (κ : Fin 1 ⊕ Fin 3) (b₁ b₂ : B), D κ (b₁ * b₂) = D κ b₁ * b₂ + b₁ * D κ b₂)
    (U : JetGaugeGroupI) (ρ μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra) :
    repGauge U (D ρ (fieldStrength A D μ ν φ)) =
      D ρ (fieldStrength A D μ ν (adjointDualCoeff U⁻¹ 0 φ))
      + fieldStrength A D μ ν (adjointDualCoeff U⁻¹ {ρ} φ) := by
  -- the base-point and once-derived adjoint transports, as maps on the gauge algebra
  set T₀ : GaugeAlgebra →ₗ[ℝ] GaugeAlgebra :=
    JetGaugeAlgebra.eval.toLinearMap ∘ₗ JetGaugeAlgebra.iteratedDeriv 0 ∘ₗ
      JetGaugeAlgebra.adjointMap U⁻¹ ∘ₗ JetGaugeAlgebra.ofConstant with hT₀def
  set T₁ : GaugeAlgebra →ₗ[ℝ] GaugeAlgebra :=
    JetGaugeAlgebra.eval.toLinearMap ∘ₗ JetGaugeAlgebra.iteratedDeriv {ρ} ∘ₗ
      JetGaugeAlgebra.adjointMap U⁻¹ ∘ₗ JetGaugeAlgebra.ofConstant with hT₁def
  have hcoeff0 : adjointDualCoeff U⁻¹ 0 = T₀.dualMap := by rw [hT₀def]; rfl
  have hcoeff1 : adjointDualCoeff U⁻¹ ({ρ} : Multiset (Fin 1 ⊕ Fin 3)) = T₁.dualMap := by
    rw [hT₁def]; rfl
  have hT₀lie : ∀ a b : GaugeAlgebra, T₀ ⁅a, b⁆ = ⁅T₀ a, T₀ b⁆ := by
    intro a b
    simp [hT₀def, JetGaugeAlgebra.ofConstant_lie, JetGaugeAlgebra.adjointMap_lie,
      LieHom.map_lie]
  have hT₁rel : ∀ a b : GaugeAlgebra, T₁ ⁅a, b⁆ = ⁅T₁ a, T₀ b⁆ + ⁅T₀ a, T₁ b⁆ := by
    intro a b
    simp only [hT₁def, hT₀def, LinearMap.coe_comp, Function.comp_apply,
      LieHom.coe_toLinearMap, JetGaugeAlgebra.iteratedDeriv_singleton,
      JetGaugeAlgebra.iteratedDeriv_zero, LinearMap.id_coe, id_eq]
    rw [JetGaugeAlgebra.ofConstant_lie, JetGaugeAlgebra.adjointMap_lie,
      JetGaugeAlgebra.deriv_bracket, map_add, LieHom.map_lie, LieHom.map_lie]
  -- brackets against the transported families
  have hbr0 : ∀ f g : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B,
      bracketFam (f ∘ₗ adjointDualCoeff U⁻¹ 0) (g ∘ₗ adjointDualCoeff U⁻¹ 0) φ =
        bracketFam f g (adjointDualCoeff U⁻¹ 0 φ) := by
    intro f g
    rw [hcoeff0, bracketFam_comp_dualMap T₀ hT₀lie f g]
    rfl
  have hbrρ : ∀ f g : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B,
      bracketFam (f ∘ₗ adjointDualCoeff U⁻¹ {ρ}) (g ∘ₗ adjointDualCoeff U⁻¹ 0) φ +
        bracketFam (f ∘ₗ adjointDualCoeff U⁻¹ 0) (g ∘ₗ adjointDualCoeff U⁻¹ {ρ}) φ =
        bracketFam f g (adjointDualCoeff U⁻¹ {ρ} φ) := by
    intro f g
    rw [hcoeff0, hcoeff1, ← LinearMap.add_apply,
      bracketFam_dualMap_derivation T₀ T₁ hT₁rel f g]
    rfl
  -- the affine transformation laws of the four families entering the bracket terms
  have hAμ0 : ∀ ψ : Module.Dual ℝ GaugeAlgebra,
      repGauge U (A μ ψ) = (A μ ∘ₗ adjointDualCoeff U⁻¹ 0) ψ
        + algebraMap ℂ B (ψ (JetGaugeAlgebra.eval (maurerCartanForm U⁻¹ μ))) :=
    fun ψ => hA.repGauge_apply U μ ψ
  have hAν0 : ∀ ψ : Module.Dual ℝ GaugeAlgebra,
      repGauge U (A ν ψ) = (A ν ∘ₗ adjointDualCoeff U⁻¹ 0) ψ
        + algebraMap ℂ B (ψ (JetGaugeAlgebra.eval (maurerCartanForm U⁻¹ ν))) :=
    fun ψ => hA.repGauge_apply U ν ψ
  have hDμ : ∀ ψ : Module.Dual ℝ GaugeAlgebra,
      repGauge U (((D ρ).restrictScalars ℝ ∘ₗ A μ) ψ) =
        (((D ρ).restrictScalars ℝ ∘ₗ A μ) ∘ₗ adjointDualCoeff U⁻¹ 0
          + A μ ∘ₗ adjointDualCoeff U⁻¹ {ρ}) ψ
        + algebraMap ℂ B (ψ (JetGaugeAlgebra.eval
            (JetGaugeAlgebra.deriv ρ (maurerCartanForm U⁻¹ μ)))) :=
    fun ψ => hA.repGauge_deriv_apply U ρ μ ψ
  have hDν : ∀ ψ : Module.Dual ℝ GaugeAlgebra,
      repGauge U (((D ρ).restrictScalars ℝ ∘ₗ A ν) ψ) =
        (((D ρ).restrictScalars ℝ ∘ₗ A ν) ∘ₗ adjointDualCoeff U⁻¹ 0
          + A ν ∘ₗ adjointDualCoeff U⁻¹ {ρ}) ψ
        + algebraMap ℂ B (ψ (JetGaugeAlgebra.eval
            (JetGaugeAlgebra.deriv ρ (maurerCartanForm U⁻¹ ν)))) :=
    fun ψ => hA.repGauge_deriv_apply U ρ ν ψ
  -- the transformed pieces
  have h1 := hA.repGauge_deriv_deriv_apply U ρ μ ν φ
  have h2 := hA.repGauge_deriv_deriv_apply U ρ ν μ φ
  have h3 := hA.repGauge_bracketFam U hDμ hAν0 φ
  have h4 := hA.repGauge_bracketFam U hAμ0 hDν φ
  -- the split of both sides through the Leibniz rule
  have hL : repGauge U (D ρ (fieldStrength A D μ ν φ)) =
      repGauge U (D ρ (D μ (A ν φ))) - repGauge U (D ρ (D ν (A μ φ)))
      + (repGauge U (bracketFam ((D ρ).restrictScalars ℝ ∘ₗ A μ) (A ν) φ)
        + repGauge U (bracketFam (A μ) ((D ρ).restrictScalars ℝ ∘ₗ A ν) φ)) := by
    rw [fieldStrength_apply, map_add, map_sub, deriv_commutator hD ρ μ ν φ,
      map_add, map_sub, map_add]
  have hR : D ρ (fieldStrength A D μ ν (adjointDualCoeff U⁻¹ 0 φ))
      + fieldStrength A D μ ν (adjointDualCoeff U⁻¹ {ρ} φ) =
      (D ρ (D μ (A ν (adjointDualCoeff U⁻¹ 0 φ)))
        - D ρ (D ν (A μ (adjointDualCoeff U⁻¹ 0 φ)))
        + (bracketFam ((D ρ).restrictScalars ℝ ∘ₗ A μ) (A ν) (adjointDualCoeff U⁻¹ 0 φ)
          + bracketFam (A μ) ((D ρ).restrictScalars ℝ ∘ₗ A ν)
              (adjointDualCoeff U⁻¹ 0 φ)))
      + (D μ (A ν (adjointDualCoeff U⁻¹ {ρ} φ))
        - D ν (A μ (adjointDualCoeff U⁻¹ {ρ} φ))
        + commutator A μ ν (adjointDualCoeff U⁻¹ {ρ} φ)) := by
    rw [fieldStrength_apply, map_add, map_sub,
      deriv_commutator hD ρ μ ν (adjointDualCoeff U⁻¹ 0 φ), fieldStrength_apply]
  -- the `∂_ρ`-derivative of the structural equation, under `φ ∘ eval`
  have hstruct2 :
      φ (JetGaugeAlgebra.eval (JetGaugeAlgebra.deriv ρ
        (JetGaugeAlgebra.deriv μ (maurerCartanForm U⁻¹ ν)))) =
      φ (JetGaugeAlgebra.eval (JetGaugeAlgebra.deriv ρ
        (JetGaugeAlgebra.deriv ν (maurerCartanForm U⁻¹ μ))))
      - φ ⁅JetGaugeAlgebra.eval (JetGaugeAlgebra.deriv ρ (maurerCartanForm U⁻¹ μ)),
          JetGaugeAlgebra.eval (maurerCartanForm U⁻¹ ν)⁆
      - φ ⁅JetGaugeAlgebra.eval (maurerCartanForm U⁻¹ μ),
          JetGaugeAlgebra.eval (JetGaugeAlgebra.deriv ρ (maurerCartanForm U⁻¹ ν))⁆ := by
    have h0 := congrArg (fun z => φ (JetGaugeAlgebra.eval (JetGaugeAlgebra.deriv ρ z)))
      (maurerCartanForm_structure U⁻¹ μ ν)
    simp only [map_add, map_sub, map_zero, JetGaugeAlgebra.deriv_bracket,
      LieHom.map_lie] at h0
    linarith
  -- assemble
  rw [hL, h1, h2, h3, h4, hR, commutator_eq_bracketFam, ← hbrρ (A μ) (A ν)]
  simp only [bracketFam_add_left, bracketFam_add_right, LinearMap.add_apply,
    LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  rw [hbr0 ((D ρ).restrictScalars ℝ ∘ₗ A μ) (A ν),
    hbr0 (A μ) ((D ρ).restrictScalars ℝ ∘ₗ A ν),
    adjointDualCoeff_singleton U⁻¹ μ φ, adjointDualCoeff_singleton U⁻¹ ν φ,
    adjointDualCoeff_pair U⁻¹ ρ μ φ, adjointDualCoeff_pair U⁻¹ ρ ν φ]
  simp only [map_sub, map_neg]
  rw [hstruct2, Complex.ofReal_sub, Complex.ofReal_sub, map_sub, map_sub]
  abel

set_option maxHeartbeats 2000000 in
/-- **The general transformation law of iterated derivatives of the field strength**:
  for `D` a derivation, every derivative symbol of `F_μν` transforms by the pure
  Leibniz convolution of the dual adjoint action over the multiset antidiagonal —
  the exact analogue of `gauge_apply_deriv` with *no* Maurer–Cartan shift, since the
  field strength transforms homogeneously. The `κ`-into-the-adjoint splittings of the
  derivative terms (`repGauge_iteratedD_cons_apply`) cancel the `ad` cross-term
  convolutions of the commutator (`repGauge_iteratedD_commutator`) through the
  coassociativity and swap of the antidiagonal, and the derived Maurer–Cartan shifts
  cancel the bracket-shift convolution through the all-orders structural equation. -/
lemma repGauge_iteratedD_fieldStrength (hA : IsGaugeField repLorentz repGauge A D D_comm)
    (hD : ∀ (κ : Fin 1 ⊕ Fin 3) (b₁ b₂ : B), D κ (b₁ * b₂) = D κ b₁ * b₂ + b₁ * D κ b₂)
    (U : JetGaugeGroupI) (s : Multiset (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ GaugeAlgebra) :
    repGauge U (Lorentz.iteratedD D D_comm s (fieldStrength A D μ ν φ)) =
      (s.antidiagonal.map fun p => Lorentz.iteratedD D D_comm p.2 (fieldStrength A D μ ν
          (adjointDualCoeff U⁻¹ p.1 φ))).sum := by
  have hDcomp : ∀ (κ : Fin 1 ⊕ Fin 3) (t : Multiset (Fin 1 ⊕ Fin 3)) (b : B),
      Lorentz.iteratedD D D_comm t (D κ b) = Lorentz.iteratedD D D_comm (κ ::ₘ t) b := by
    intro κ t b
    rw [show (κ ::ₘ t : Multiset (Fin 1 ⊕ Fin 3)) = t + {κ} from by
        rw [add_comm, Multiset.singleton_add],
      Lorentz.iteratedD_add, LinearMap.comp_apply]
    congr 1
  have hL : repGauge U (Lorentz.iteratedD D D_comm s (fieldStrength A D μ ν φ)) =
      repGauge U (Lorentz.iteratedD D D_comm (μ ::ₘ s) (A ν φ))
      - repGauge U (Lorentz.iteratedD D D_comm (ν ::ₘ s) (A μ φ))
      + repGauge U (Lorentz.iteratedD D D_comm s (commutator A μ ν φ)) := by
    rw [fieldStrength_apply, map_add, map_sub, hDcomp μ s, hDcomp ν s, map_add, map_sub]
  have hR : (s.antidiagonal.map fun p =>
      Lorentz.iteratedD D D_comm p.2 (fieldStrength A D μ ν
        (adjointDualCoeff U⁻¹ p.1 φ))).sum =
      (s.antidiagonal.map fun p =>
        Lorentz.iteratedD D D_comm (μ ::ₘ p.2) (A ν (adjointDualCoeff U⁻¹ p.1 φ))).sum
      - (s.antidiagonal.map fun p =>
        Lorentz.iteratedD D D_comm (ν ::ₘ p.2) (A μ (adjointDualCoeff U⁻¹ p.1 φ))).sum
      + (s.antidiagonal.map fun p =>
        Lorentz.iteratedD D D_comm p.2 (commutator A μ ν
          (adjointDualCoeff U⁻¹ p.1 φ))).sum := by
    rw [← Multiset.sum_map_sub, ← Multiset.sum_map_add]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [fieldStrength_apply, map_add, map_sub, hDcomp μ p.2, hDcomp ν p.2]
  have hcancel₁ : (s.antidiagonal.map fun p =>
      (p.1.antidiagonal.map fun q =>
        Lorentz.iteratedD D D_comm p.2 (A ν (adjointDualCoeff U⁻¹ q.2
          (φ ∘ₗ LieAlgebra.ad ℝ GaugeAlgebra (JetGaugeAlgebra.eval
            (JetGaugeAlgebra.iteratedDeriv q.1 (maurerCartanForm U⁻¹ μ))))))).sum).sum =
    (s.antidiagonal.map fun p =>
      (p.2.antidiagonal.map fun r =>
        Lorentz.iteratedD D D_comm r.2 (A ν (adjointDualCoeff U⁻¹ r.1
          (φ ∘ₗ LieAlgebra.ad ℝ GaugeAlgebra (JetGaugeAlgebra.eval
            (JetGaugeAlgebra.iteratedDeriv p.1 (maurerCartanForm U⁻¹ μ))))))).sum).sum :=
    Multiset.sum_antidiagonal_assoc s (fun a b c =>
      Lorentz.iteratedD D D_comm c (A ν (adjointDualCoeff U⁻¹ b
        (φ ∘ₗ LieAlgebra.ad ℝ GaugeAlgebra (JetGaugeAlgebra.eval
          (JetGaugeAlgebra.iteratedDeriv a (maurerCartanForm U⁻¹ μ)))))))
  have hcancel₂ : (s.antidiagonal.map fun p =>
      (p.1.antidiagonal.map fun q =>
        Lorentz.iteratedD D D_comm p.2 (A μ (adjointDualCoeff U⁻¹ q.2
          (φ ∘ₗ LieAlgebra.ad ℝ GaugeAlgebra (JetGaugeAlgebra.eval
            (JetGaugeAlgebra.iteratedDeriv q.1 (maurerCartanForm U⁻¹ ν))))))).sum).sum =
    (s.antidiagonal.map fun p =>
      (p.1.antidiagonal.map fun q =>
        Lorentz.iteratedD D D_comm q.2 (A μ (adjointDualCoeff U⁻¹ q.1
          (φ ∘ₗ LieAlgebra.ad ℝ GaugeAlgebra (JetGaugeAlgebra.eval
            (JetGaugeAlgebra.iteratedDeriv p.2 (maurerCartanForm U⁻¹ ν))))))).sum).sum := by
    refine (Multiset.sum_antidiagonal_assoc s (fun a b c =>
      Lorentz.iteratedD D D_comm c (A μ (adjointDualCoeff U⁻¹ b
        (φ ∘ₗ LieAlgebra.ad ℝ GaugeAlgebra (JetGaugeAlgebra.eval
          (JetGaugeAlgebra.iteratedDeriv a (maurerCartanForm U⁻¹ ν)))))))).trans ?_
    exact Multiset.sum_antidiagonal_swap s (fun a b =>
      (b.antidiagonal.map fun q =>
        Lorentz.iteratedD D D_comm q.2 (A μ (adjointDualCoeff U⁻¹ q.1
          (φ ∘ₗ LieAlgebra.ad ℝ GaugeAlgebra (JetGaugeAlgebra.eval
            (JetGaugeAlgebra.iteratedDeriv a (maurerCartanForm U⁻¹ ν))))))).sum)
  set Θ : GaugeAlgebra →+ B := ((algebraMap ℂ B).toAddMonoidHom.comp
    ((Complex.ofRealHom : ℝ →+* ℂ).toAddMonoidHom.comp φ.toAddMonoidHom)) with hΘdef
  have hΘ : ∀ z : GaugeAlgebra, algebraMap ℂ B ((φ z : ℝ) : ℂ) = Θ z := fun z => rfl
  have hconst : Θ (JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv (μ ::ₘ s)
      (maurerCartanForm U⁻¹ ν))) =
    Θ (JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv (ν ::ₘ s)
      (maurerCartanForm U⁻¹ μ)))
    - (s.antidiagonal.map fun p =>
        Θ ⁅JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv p.1
            (maurerCartanForm U⁻¹ μ)),
          JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv p.2
            (maurerCartanForm U⁻¹ ν))⁆).sum := by
    rw [eval_iteratedDeriv_maurerCartan_structure U⁻¹ s μ ν, map_sub, map_multiset_sum,
      Multiset.map_map]
    congr 1
  rw [hL, repGauge_iteratedD_cons_apply hA U μ s ν φ,
    repGauge_iteratedD_cons_apply hA U ν s μ φ,
    hA.repGauge_iteratedD_commutator hD U s μ ν φ, hR]
  simp only [hΘ]
  rw [hconst, hcancel₁, hcancel₂]
  abel

/-- **The field strength is an adjoint gauge tensor**: the packaging of
  `repGauge_iteratedD_fieldStrength` as `TransformsInAdjoint` — the base case of the
  covariant-derivative recursion `TransformsInAdjoint.covDerivAdjoint`. -/
theorem transformsInAdjoint_fieldStrength (hA : IsGaugeField repLorentz repGauge A D D_comm)
    (hD : ∀ (κ : Fin 1 ⊕ Fin 3) (b₁ b₂ : B), D κ (b₁ * b₂) = D κ b₁ * b₂ + b₁ * D κ b₂)
    (μ ν : Fin 1 ⊕ Fin 3) : hA.TransformsInAdjoint (fieldStrength A D μ ν) :=
  fun U φ s => hA.repGauge_iteratedD_fieldStrength hD U s μ ν φ

end IsGaugeField

end StandardModel
