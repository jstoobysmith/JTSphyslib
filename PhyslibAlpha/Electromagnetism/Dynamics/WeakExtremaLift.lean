/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Electromagnetism.Dynamics.IsWeakExtrema
public import PhyslibAlpha.Electromagnetism.Dynamics.FirstVariation
public import PhyslibAlpha.SpaceAndTime.SpaceTime.Lift
public import Physlib.Electromagnetism.Distributional.Dynamics.IsExtrema

/-!

# The bridge between weak extrema and extrema of distributions

Maxwell's equations have two formulations in Physlib-Alpha. In the functional one, a potential
`A` with source `J` is a weak extremum of the action (`IsWeakExtrema`): the first variation of the
action vanishes along every test-function variation. In the distributional one, the lifts of
`A` and `J` to distributions (`SpaceTime.lift`) are an extremum of the distributional action
(`DistElectromagneticPotential.IsExtrema`). This file proves that the two agree for every
potential and current which are regular enough to be lifted: `A` differentiable, and `A`, its
derivatives and `J` tempered integrable (`LiftRegular`).

The first variation of the lagrangian density in a coordinate direction `ε • eᵥ` is an explicit
expression `firstVariation` in the derivatives of `A` and of `ε`. Integrating it by parts once
against a Schwartz function `ε` gives `c` times the `ν`-component of the distributional
variational gradient of the lifts, paired with `ε`
(`LiftRegular.integral_firstVariation_eq_gradLagrangian`). The two notions are then compared:
- an extremum of the lifts is a weak extremum, since every test-function variation decomposes
  into coordinate directions, each a Schwartz function;
- a weak extremum makes the integrated first variation vanish against compactly supported test
  functions only, and this is extended to all Schwartz functions by cutting them off with
  stretched bumps `cutoff n` and passing to the limit by dominated convergence.

## Main results

- `LiftRegular` : the regularity under which a potential and a current can be lifted.
- `firstVariation` : the first variation of the lagrangian density in a coordinate direction.
- `LiftRegular.integral_firstVariation_eq_gradLagrangian` : the integrated first variation is the
  distributional variational gradient of the lifts.
- `LiftRegular.isWeakExtrema_iff_isExtrema_lift` : the bridge between the functional and the
  distributional formulations of Maxwell's equations.

## Contents

- A. Tempered integrable functions on spacetime
- B. The first variation in a coordinate direction
- C. The integrated first variation
- D. The first variation as a sum over coordinate directions
- E. Extrema of the lifts are weak extrema
- F. Cutting test functions off
- G. Limits of cut-off pairings
- H. Weak extrema are extrema of the lifts
- I. The bridge

-/

@[expose] public section

open MeasureTheory SchwartzMap Physlib Physlib.Distribution Filter Topology
open SpaceTime minkowskiMatrix ContDiff
open scoped SchwartzMap

namespace Electromagnetism

/-!

## A. Tempered integrable functions on spacetime

-/

namespace SpaceTime

variable {d : ℕ}

lemma _root_.Physlib.Distribution.IsTemperedIntegrable.apply {f : SpaceTime d → Lorentz.Vector d}
    (hf : IsTemperedIntegrable f) (ν : Fin 1 ⊕ Fin d) :
    IsTemperedIntegrable (fun x => f x ν) := by
  obtain ⟨k, hk⟩ := hf
  exact ⟨k, ((Lorentz.Vector.coordCLM ν).integrable_comp hk).congr
    (Eventually.of_forall fun x => by simp [Lorentz.Vector.coordCLM_apply])⟩

lemma _root_.Physlib.Distribution.IsTemperedIntegrable.integrable_mul {f : SpaceTime d → ℝ}
    (hf : IsTemperedIntegrable f) (ψ : 𝓢(SpaceTime d, ℝ)) :
    Integrable (fun x => ψ x * f x) :=
  hf.integrable_smul ψ

/-- The coordinate derivative of a test function on spacetime, as a test function. -/
noncomputable def schwartzDeriv (μ : Fin 1 ⊕ Fin d) (ε : 𝓢(SpaceTime d, ℝ)) :
    𝓢(SpaceTime d, ℝ) :=
  SchwartzMap.evalCLM ℝ (SpaceTime d) ℝ (Lorentz.Vector.basis μ) (fderivCLM ℝ (SpaceTime d) ℝ ε)

@[simp]
lemma schwartzDeriv_apply (μ : Fin 1 ⊕ Fin d) (ε : 𝓢(SpaceTime d, ℝ)) (x : SpaceTime d) :
    schwartzDeriv μ ε x = ∂_ μ ε x := rfl

/-- Integration by parts on spacetime against a test function. -/
lemma integral_deriv_mul_eq_neg {g : SpaceTime d → ℝ} (hg : Differentiable ℝ g)
    (hgi : IsTemperedIntegrable g) (hdg : IsTemperedIntegrable (∂_ μ g))
    (ψ : 𝓢(SpaceTime d, ℝ)) :
    ∫ x, ∂_ μ g x * ψ x = - ∫ x, g x * ∂_ μ ψ x := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := ψ) (g := g) (v := Lorentz.Vector.basis μ)
    ((hgi.integrable_mul (schwartzDeriv μ ψ)).congr (Eventually.of_forall fun x => rfl))
    ((hdg.integrable_mul ψ).congr (Eventually.of_forall fun x => rfl))
    (hgi.integrable_mul ψ) (fun x _ => ψ.differentiableAt) (fun x _ => hg x)
  simp only [← SpaceTime.deriv_eq] at h
  rw [show (∫ x, ∂_ μ g x * ψ x) = ∫ x, ψ x * ∂_ μ g x from
    integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _), h]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)

end SpaceTime

namespace ElectromagneticPotential

open SpaceTime

variable {d : ℕ}

/-!

## B. The first variation in a coordinate direction

-/

lemma deriv_smul_basis_apply (φ : SpaceTime d → ℝ) (hφ : Differentiable ℝ φ)
    (μ ν ν' : Fin 1 ⊕ Fin d) (x : SpaceTime d) :
    ∂_ μ (fun x => φ x • Lorentz.Vector.basis ν) x ν' =
      ∂_ μ φ x * Lorentz.Vector.basis ν ν' := by
  rw [SpaceTime.deriv_eq, SpaceTime.deriv_eq, fderiv_smul_const (hφ x)]
  simp

/-- The first variation of the lagrangian density in the direction `φ • eᵥ`. -/
lemma deriv_lagrangian_smul_basis {𝓕 : FreeSpace} (A : ElectromagneticPotential d)
    (J : LorentzCurrentDensity d) (hA : Differentiable ℝ A) (φ : SpaceTime d → ℝ)
    (hφ : Differentiable ℝ φ) (ν : Fin 1 ⊕ Fin d) (x : SpaceTime d) :
    _root_.deriv (fun s : ℝ => lagrangian 𝓕
        ⟨fun x' => A x' + s • (φ x' • Lorentz.Vector.basis ν)⟩ J x) 0 =
      - 1 / 𝓕.μ₀ * ∑ μ, (η μ μ * η ν ν * ∂_ μ A x ν * ∂_ μ φ x - ∂_ ν A x μ * ∂_ μ φ x)
        - η ν ν * φ x * J x ν := by
  have hδ : Differentiable ℝ (fun x => φ x • Lorentz.Vector.basis ν) := hφ.smul_const _
  rw [deriv_lagrangian_add_smul A J _ hA hδ x]
  simp only [deriv_smul_basis_apply φ hφ, Lorentz.Vector.basis_apply,
    Lorentz.Vector.minkowskiProduct_toCoord_minkowskiMatrix, Lorentz.Vector.apply_smul]
  have h1 : ∑ μ, ∑ ν', η μ μ * η ν' ν' * ∂_ μ A x ν' * (∂_ μ φ x * if ν = ν' then 1 else 0) =
      ∑ μ, η μ μ * η ν ν * ∂_ μ A x ν * ∂_ μ φ x := by
    simp [mul_ite, Finset.sum_ite_eq]
  have h2 : ∑ μ, ∑ ν', ∂_ μ A x ν' * (∂_ ν' φ x * if ν = μ then 1 else 0) =
      ∑ μ, ∂_ ν A x μ * ∂_ μ φ x := by
    rw [Finset.sum_comm]
    simp [mul_ite, Finset.sum_ite_eq]
  have h3 : ∑ μ, η μ μ * (φ x * if ν = μ then 1 else 0) * J x μ = η ν ν * φ x * J x ν := by
    simp [mul_ite, Finset.sum_ite_eq]
  simp only [Finset.sum_sub_distrib]
  rw [h1, h2, h3]

/-!

## C. The integrated first variation

-/

/-- The first variation of the lagrangian density in the direction `φ • eᵥ`, as an explicit
expression in the derivatives of the potential. -/
noncomputable def firstVariation (𝓕 : FreeSpace) (A : ElectromagneticPotential d)
    (J : LorentzCurrentDensity d) (ν : Fin 1 ⊕ Fin d) (φ : SpaceTime d → ℝ) (x : SpaceTime d) :
    ℝ :=
  - 1 / 𝓕.μ₀ * ∑ μ, (η μ μ * η ν ν * ∂_ μ A x ν * ∂_ μ φ x - ∂_ ν A x μ * ∂_ μ φ x)
    - η ν ν * φ x * J x ν

/-- The regularity under which the lift of a potential and a current to distributions is
compatible with the first variation of the action. -/
structure LiftRegular (A : ElectromagneticPotential d) (J : LorentzCurrentDensity d) : Prop where
  differentiable : Differentiable ℝ A
  temperedIntegrable : IsTemperedIntegrable A.val
  deriv_temperedIntegrable : ∀ μ, IsTemperedIntegrable (∂_ μ A.val)
  current_temperedIntegrable : IsTemperedIntegrable J

variable {A : ElectromagneticPotential d} {J : LorentzCurrentDensity d}

lemma LiftRegular.deriv_apply_temperedIntegrable (h : LiftRegular A J) (μ ν : Fin 1 ⊕ Fin d) :
    IsTemperedIntegrable (fun x => ∂_ μ A x ν) :=
  (h.deriv_temperedIntegrable μ).apply ν

lemma LiftRegular.deriv_component_eq (h : LiftRegular A J) (μ ν : Fin 1 ⊕ Fin d) :
    ∂_ μ (fun x => A x ν) = fun x => ∂_ μ A x ν := by
  funext x
  rw [SpaceTime.deriv_apply_eq μ ν _ h.differentiable, SpaceTime.deriv_eq]

/-- The integrated first variation, split into its terms. -/
lemma LiftRegular.integral_firstVariation (h : LiftRegular A J) (𝓕 : FreeSpace)
    (ν : Fin 1 ⊕ Fin d) (ψ : 𝓢(SpaceTime d, ℝ)) :
    ∫ x, firstVariation 𝓕 A J ν ψ x =
      - 1 / 𝓕.μ₀ * ∑ μ, (η μ μ * η ν ν * (∫ x, ∂_ μ A x ν * ∂_ μ ψ x)
        - ∫ x, ∂_ ν A x μ * ∂_ μ ψ x) - η ν ν * ∫ x, ψ x * J x ν := by
  have hi (μ ν' ν'' : Fin 1 ⊕ Fin d) : Integrable (fun x => ∂_ μ A x ν' * ∂_ ν'' ψ x) :=
    ((h.deriv_apply_temperedIntegrable μ ν').integrable_mul (schwartzDeriv ν'' ψ)).congr
      (Eventually.of_forall fun x => mul_comm _ _)
  have hJ : Integrable (fun x => ψ x * J x ν) :=
    (h.current_temperedIntegrable.apply ν).integrable_mul ψ
  unfold firstVariation
  rw [integral_sub ((integrable_finsetSum _ fun μ _ =>
      (((hi μ ν μ).const_mul (η μ μ * η ν ν)).sub (hi ν μ μ)).congr
        (Eventually.of_forall fun x => by simp only [Pi.sub_apply]; ring)).const_mul _)
      ((hJ.const_mul (η ν ν)).congr (Eventually.of_forall fun x => by ring)),
    integral_const_mul, integral_finsetSum _ fun μ _ =>
      (((hi μ ν μ).const_mul (η μ μ * η ν ν)).sub (hi ν μ μ)).congr
        (Eventually.of_forall fun x => by simp only [Pi.sub_apply]; ring)]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← integral_const_mul, ← integral_sub ((hi μ ν μ).const_mul _) (hi ν μ μ)]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  · rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)

lemma lift_apply_apply (c : SpeedOfLight) {f : SpaceTime d → Lorentz.Vector d}
    (hf : IsTemperedIntegrable f) (ψ : 𝓢(SpaceTime d, ℝ)) (ν : Fin 1 ⊕ Fin d) :
    SpaceTime.lift c f ψ ν = (c.val)⁻¹ * ∫ x, ψ x * f x ν := by
  rw [SpaceTime.lift_apply c hf, Lorentz.Vector.apply_smul]
  congr 1
  change Lorentz.Vector.coordCLM ν (∫ x, ψ x • f x) = _
  rw [← ContinuousLinearMap.integral_comp_comm _ (hf.integrable_smul ψ)]
  simp [Lorentz.Vector.coordCLM_apply]

/-- The `ν`-component of the variational gradient of the lagrangian of the lifted potential and
current, written as integrals against the potential and the current. -/
lemma LiftRegular.gradLagrangian_lift_apply (h : LiftRegular A J) (𝓕 : FreeSpace)
    (ε : 𝓢(SpaceTime d, ℝ)) (ν : Fin 1 ⊕ Fin d) :
    DistElectromagneticPotential.gradLagrangian 𝓕 (SpaceTime.lift 𝓕.c A.val)
      (SpaceTime.lift 𝓕.c J) ε ν =
    (𝓕.c.val)⁻¹ * (1 / 𝓕.μ₀ * ∑ μ,
      (η μ μ * η ν ν * (∫ x, schwartzDeriv μ (schwartzDeriv μ ε) x * A x ν)
        - ∫ x, schwartzDeriv ν (schwartzDeriv μ ε) x * A x μ)
      - η ν ν * ∫ x, ε x * J x ν) := by
  rw [DistElectromagneticPotential.gradLagrangian, _root_.sub_apply,
    DistElectromagneticPotential.gradKineticTerm_eq_sum_sum,
    DistElectromagneticPotential.gradFreeCurrentPotential_eq_sum_basis]
  simp only [Lorentz.Vector.apply_sub, Lorentz.Vector.apply_sum, Lorentz.Vector.apply_smul,
    Lorentz.Vector.basis_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [SpaceTime.distDeriv_apply', neg_neg, Lorentz.Vector.neg_apply]
  simp only [lift_apply_apply 𝓕.c h.temperedIntegrable,
    lift_apply_apply 𝓕.c h.current_temperedIntegrable]
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun μ _ => ?_
    ring_nf
    rfl
  · ring

lemma LiftRegular.integral_deriv_mul_schwartzDeriv (h : LiftRegular A J)
    (μ ν' ν'' : Fin 1 ⊕ Fin d) (ε : 𝓢(SpaceTime d, ℝ)) :
    ∫ x, ∂_ μ A x ν' * ∂_ ν'' ε x =
      - ∫ x, schwartzDeriv μ (schwartzDeriv ν'' ε) x * A x ν' := by
  have hg : Differentiable ℝ (fun x => A x ν') :=
    (SpaceTime.differentiable_vector _).mpr h.differentiable ν'
  have hdg : IsTemperedIntegrable (∂_ μ (fun x => A x ν')) := by
    rw [h.deriv_component_eq]
    exact h.deriv_apply_temperedIntegrable μ ν'
  have hibp := SpaceTime.integral_deriv_mul_eq_neg (μ := μ) hg
    (h.temperedIntegrable.apply ν') hdg (schwartzDeriv ν'' ε)
  rw [h.deriv_component_eq] at hibp
  simp only [schwartzDeriv_apply] at hibp
  rw [hibp]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)

/-- The integrated first variation of the action in the direction `ε • eᵥ` is `c` times the
`ν`-component of the variational gradient of the lagrangian of the lifted potential and
current, paired with `ε`. -/
lemma LiftRegular.integral_firstVariation_eq_gradLagrangian (h : LiftRegular A J)
    (𝓕 : FreeSpace) (ε : 𝓢(SpaceTime d, ℝ)) (ν : Fin 1 ⊕ Fin d) :
    ∫ x, firstVariation 𝓕 A J ν ε x =
      𝓕.c.val * DistElectromagneticPotential.gradLagrangian 𝓕 (SpaceTime.lift 𝓕.c A.val)
        (SpaceTime.lift 𝓕.c J) ε ν := by
  rw [h.integral_firstVariation, h.gradLagrangian_lift_apply, ← mul_assoc,
    mul_inv_cancel₀ 𝓕.c.val_ne_zero, one_mul]
  simp only [h.integral_deriv_mul_schwartzDeriv]
  congr 1
  rw [neg_div, neg_mul, ← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  ring

lemma LiftRegular.integrable_firstVariation (h : LiftRegular A J) (𝓕 : FreeSpace)
    (ν : Fin 1 ⊕ Fin d) (ψ : 𝓢(SpaceTime d, ℝ)) :
    Integrable (firstVariation 𝓕 A J ν ψ) := by
  have hi (μ ν' ν'' : Fin 1 ⊕ Fin d) : Integrable (fun x => ∂_ μ A x ν' * ∂_ ν'' ψ x) :=
    ((h.deriv_apply_temperedIntegrable μ ν').integrable_mul (schwartzDeriv ν'' ψ)).congr
      (Eventually.of_forall fun x => mul_comm _ _)
  have hJ : Integrable (fun x => ψ x * J x ν) :=
    (h.current_temperedIntegrable.apply ν).integrable_mul ψ
  unfold firstVariation
  refine (((integrable_finsetSum Finset.univ fun μ _ =>
      (((hi μ ν μ).const_mul (η μ μ * η ν ν)).sub (hi ν μ μ))).const_mul (- 1 / 𝓕.μ₀)).sub
      (hJ.const_mul (η ν ν))).congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.sub_apply]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun μ _ => ?_
    ring
  · ring

/-!

## D. The first variation as a sum over coordinate directions

-/

lemma deriv_lagrangian_eq_sum_firstVariation {𝓕 : FreeSpace} (A : ElectromagneticPotential d)
    (J : LorentzCurrentDensity d) (hA : Differentiable ℝ A)
    (δA : SpaceTime d → Lorentz.Vector d) (hδA : Differentiable ℝ δA) (x : SpaceTime d) :
    _root_.deriv (fun s : ℝ => lagrangian 𝓕 ⟨fun x' => A x' + s • δA x'⟩ J x) 0 =
      ∑ ν, firstVariation 𝓕 A J ν (fun x => δA x ν) x := by
  have hd (μ ν : Fin 1 ⊕ Fin d) : ∂_ μ δA x ν = ∂_ μ (fun x => δA x ν) x := by
    rw [SpaceTime.deriv_apply_eq μ ν _ hδA, SpaceTime.deriv_eq]
  rw [deriv_lagrangian_add_smul A J δA hA hδA x,
    Lorentz.Vector.minkowskiProduct_toCoord_minkowskiMatrix]
  unfold firstVariation
  simp only [hd, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [Finset.sum_comm (f := fun μ ν => η μ μ * η ν ν * ∂_ μ A x ν * ∂_ μ (fun x => δA x ν) x)]

/-!

## E. Extrema of the lifts are weak extrema

-/

/-- The component of a test function along a coordinate direction, as a Schwartz function. -/
noncomputable def _root_.IsTestFunction.componentSchwartz {δA : SpaceTime d → Lorentz.Vector d}
    (hδA : IsTestFunction δA) (ν : Fin 1 ⊕ Fin d) : 𝓢(SpaceTime d, ℝ) :=
  (hδA.supp.comp_left (g := fun v : Lorentz.Vector d => v ν) (by simp)).toSchwartzMap
    ((Lorentz.Vector.coordCLM ν).contDiff.comp hδA.smooth)

@[simp]
lemma _root_.IsTestFunction.componentSchwartz_apply {δA : SpaceTime d → Lorentz.Vector d}
    (hδA : IsTestFunction δA) (ν : Fin 1 ⊕ Fin d) (x : SpaceTime d) :
    hδA.componentSchwartz ν x = δA x ν := rfl

lemma LiftRegular.isWeakExtrema_of_isExtrema (h : LiftRegular A J) {𝓕 : FreeSpace}
    (hE : DistElectromagneticPotential.IsExtrema 𝓕 (SpaceTime.lift 𝓕.c A.val)
      (SpaceTime.lift 𝓕.c J)) :
    IsWeakExtrema 𝓕 A J := by
  intro δA hδA
  have hcomp (ν : Fin 1 ⊕ Fin d) : (fun x => δA x ν) = ⇑(hδA.componentSchwartz ν) := rfl
  calc ∫ x, _root_.deriv (fun s : ℝ => lagrangian 𝓕 ⟨fun x' => A x' + s • δA x'⟩ J x) 0
      = ∫ x, ∑ ν, firstVariation 𝓕 A J ν (hδA.componentSchwartz ν) x := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        beta_reduce
        rw [deriv_lagrangian_eq_sum_firstVariation A J h.differentiable δA
          hδA.differentiable x]
        rfl
    _ = ∑ ν, ∫ x, firstVariation 𝓕 A J ν (hδA.componentSchwartz ν) x :=
        integral_finsetSum _ fun ν _ => h.integrable_firstVariation 𝓕 ν _
    _ = 0 := by
        refine Finset.sum_eq_zero fun ν _ => ?_
        rw [h.integral_firstVariation_eq_gradLagrangian 𝓕, hE]
        simp

/-!

## F. Cutting test functions off

-/

/-- A smooth bump on spacetime equal to `1` on the unit ball and supported in the ball of
radius `2`. -/
noncomputable def cutoffBump : ContDiffBump (0 : SpaceTime d) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The bump `cutoffBump` stretched by a factor `n + 1`. -/
noncomputable def cutoff (n : ℕ) (x : SpaceTime d) : ℝ :=
  cutoffBump (((n : ℝ) + 1)⁻¹ • x)

lemma cutoff_scale_ne_zero (n : ℕ) : ((n : ℝ) + 1)⁻¹ ≠ 0 := by positivity

lemma cutoff_contDiff (n : ℕ) : ContDiff ℝ ∞ (cutoff (d := d) n) :=
  (cutoffBump (d := d)).contDiff.comp (contDiff_const_smul _)

lemma cutoff_hasCompactSupport (n : ℕ) : HasCompactSupport (cutoff (d := d) n) :=
  (cutoffBump (d := d)).hasCompactSupport.comp_homeomorph
    (Homeomorph.smulOfNeZero _ (cutoff_scale_ne_zero n))

lemma abs_cutoff_le (n : ℕ) (x : SpaceTime d) : |cutoff n x| ≤ 1 := by
  unfold cutoff
  rw [abs_of_nonneg (cutoffBump.nonneg)]
  exact cutoffBump.le_one

lemma tendsto_cutoff (x : SpaceTime d) : Tendsto (fun n => cutoff n x) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop ⌈‖x‖⌉₊] with n hn
  symm
  refine cutoffBump.one_of_mem_closedBall ?_
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity), inv_mul_le_iff₀ (by positivity)]
  show ‖x‖ ≤ ((n : ℝ) + 1) * 1
  have := Nat.le_ceil ‖x‖
  have h2 : (⌈‖x‖⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
  linarith

lemma deriv_cutoff (n : ℕ) (μ : Fin 1 ⊕ Fin d) (x : SpaceTime d) :
    ∂_ μ (cutoff n) x = ((n : ℝ) + 1)⁻¹ *
      fderiv ℝ (cutoffBump (d := d)) (((n : ℝ) + 1)⁻¹ • x) (Lorentz.Vector.basis μ) := by
  have h := ((((cutoffBump (d := d)).contDiff (n := 1)).differentiable one_ne_zero)
    (((n : ℝ) + 1)⁻¹ • x)).hasFDerivAt.comp x
    ((ContinuousLinearMap.id ℝ (SpaceTime d)).hasFDerivAt.const_smul ((n : ℝ) + 1)⁻¹)
  rw [SpaceTime.deriv_eq]
  change fderiv ℝ (cutoffBump ∘ HSMul.hSMul ((n : ℝ) + 1)⁻¹) x (Lorentz.Vector.basis μ) = _
  rw [h.fderiv]
  simp

lemma exists_abs_deriv_cutoff_le (μ : Fin 1 ⊕ Fin d) :
    ∃ K, 0 ≤ K ∧ ∀ n x, |∂_ μ (cutoff n) x| ≤ K := by
  obtain ⟨C, hC⟩ := Continuous.bounded_above_of_compact_support
    (((cutoffBump (d := d)).contDiff (n := 1)).continuous_fderiv one_ne_zero)
    ((cutoffBump (d := d)).hasCompactSupport.fderiv (𝕜 := ℝ))
  refine ⟨max C 0 * ‖Lorentz.Vector.basis (d := d) μ‖, by positivity, fun n x => ?_⟩
  rw [deriv_cutoff, abs_mul, abs_of_pos (by positivity)]
  calc ((n : ℝ) + 1)⁻¹ * |fderiv ℝ cutoffBump (((n : ℝ) + 1)⁻¹ • x) (Lorentz.Vector.basis μ)|
      ≤ 1 * (max C 0 * ‖Lorentz.Vector.basis (d := d) μ‖) := by
        refine mul_le_mul (inv_le_one_of_one_le₀ (by simp)) ?_ (abs_nonneg _) zero_le_one
        rw [← Real.norm_eq_abs]
        exact ((fderiv ℝ cutoffBump _).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right ((hC _).trans (le_max_left _ _)) (norm_nonneg _))
    _ = max C 0 * ‖Lorentz.Vector.basis (d := d) μ‖ := one_mul _

lemma tendsto_deriv_cutoff (μ : Fin 1 ⊕ Fin d) (x : SpaceTime d) :
    Tendsto (fun n => ∂_ μ (cutoff n) x) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := Continuous.bounded_above_of_compact_support
    (((cutoffBump (d := d)).contDiff (n := 1)).continuous_fderiv one_ne_zero)
    ((cutoffBump (d := d)).hasCompactSupport.fderiv (𝕜 := ℝ))
  set K := max C 0 * ‖Lorentz.Vector.basis (d := d) μ‖
  have hlim : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ * K) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).mul_const K
  refine squeeze_zero_norm (fun n => ?_) hlim
  rw [deriv_cutoff, norm_mul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact ((fderiv ℝ cutoffBump _).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right ((hC _).trans (le_max_left _ _)) (norm_nonneg _))

/-- A test function cut off by `cutoff n`, as a compactly supported Schwartz function. -/
noncomputable def cutoffSchwartz (n : ℕ) (ε : 𝓢(SpaceTime d, ℝ)) : 𝓢(SpaceTime d, ℝ) :=
  ((cutoff_hasCompactSupport (d := d) n).mul_right (f' := ⇑ε)).toSchwartzMap
    ((cutoff_contDiff n).mul (ε.smooth ⊤))

@[simp]
lemma cutoffSchwartz_apply (n : ℕ) (ε : 𝓢(SpaceTime d, ℝ)) (x : SpaceTime d) :
    cutoffSchwartz n ε x = cutoff n x * ε x := rfl

lemma cutoffSchwartz_hasCompactSupport (n : ℕ) (ε : 𝓢(SpaceTime d, ℝ)) :
    HasCompactSupport (cutoffSchwartz n ε) :=
  (cutoff_hasCompactSupport (d := d) n).mul_right

lemma deriv_cutoffSchwartz (n : ℕ) (ε : 𝓢(SpaceTime d, ℝ)) (μ : Fin 1 ⊕ Fin d)
    (x : SpaceTime d) :
    ∂_ μ (cutoffSchwartz n ε) x = cutoff n x * ∂_ μ ε x + ∂_ μ (cutoff n) x * ε x := by
  have hc := ((cutoff_contDiff (d := d) n).differentiable (by simp)) x
  rw [SpaceTime.deriv_eq, SpaceTime.deriv_eq, SpaceTime.deriv_eq]
  change fderiv ℝ (fun y => cutoff n y * ε y) x (Lorentz.Vector.basis μ) = _
  rw [fderiv_fun_mul hc ε.differentiableAt]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

/-!

## G. Limits of cut-off pairings

-/

lemma tendsto_integral_cutoffSchwartz_mul {g : SpaceTime d → ℝ} (hg : IsTemperedIntegrable g)
    (ε : 𝓢(SpaceTime d, ℝ)) :
    Tendsto (fun n => ∫ x, cutoffSchwartz n ε x * g x) atTop (𝓝 (∫ x, ε x * g x)) := by
  refine tendsto_integral_of_dominated_convergence (fun x => ‖ε x * g x‖)
    (fun n => (hg.integrable_mul (cutoffSchwartz n ε)).aestronglyMeasurable)
    (hg.integrable_mul ε).norm (fun n => Eventually.of_forall fun x => ?_)
    (Eventually.of_forall fun x => ?_)
  · rw [cutoffSchwartz_apply, mul_assoc, norm_mul, Real.norm_eq_abs (cutoff n x)]
    exact mul_le_of_le_one_left (norm_nonneg _) (abs_cutoff_le n x)
  · simp only [cutoffSchwartz_apply, mul_assoc]
    simpa using (tendsto_cutoff x).mul_const (ε x * g x)

lemma tendsto_integral_mul_deriv_cutoffSchwartz {g : SpaceTime d → ℝ}
    (hg : IsTemperedIntegrable g) (ε : 𝓢(SpaceTime d, ℝ)) (μ : Fin 1 ⊕ Fin d) :
    Tendsto (fun n => ∫ x, g x * ∂_ μ (cutoffSchwartz n ε) x) atTop
      (𝓝 (∫ x, g x * ∂_ μ ε x)) := by
  obtain ⟨K, hK, hKb⟩ := exists_abs_deriv_cutoff_le (d := d) μ
  have h1 : Integrable (fun x => ‖schwartzDeriv μ ε x * g x‖) :=
    (hg.integrable_mul (schwartzDeriv μ ε)).norm
  have h2 : Integrable (fun x => ‖ε x * g x‖) := (hg.integrable_mul ε).norm
  refine tendsto_integral_of_dominated_convergence
    (fun x => ‖schwartzDeriv μ ε x * g x‖ + K * ‖ε x * g x‖)
    (fun n => ((hg.integrable_mul (schwartzDeriv μ (cutoffSchwartz n ε))).aestronglyMeasurable
      ).congr (Eventually.of_forall fun x => mul_comm _ _))
    (h1.add (h2.const_mul K)) (fun n => Eventually.of_forall fun x => ?_)
    (Eventually.of_forall fun x => ?_)
  · rw [deriv_cutoffSchwartz, mul_add, Real.norm_eq_abs]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [schwartzDeriv_apply, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
      nlinarith [mul_le_mul_of_nonneg_right (abs_cutoff_le n x)
        (mul_nonneg (abs_nonneg (∂_ μ ε x)) (abs_nonneg (g x)))]
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
      nlinarith [mul_le_mul_of_nonneg_right (hKb n x)
        (mul_nonneg (abs_nonneg (ε x)) (abs_nonneg (g x)))]
  · simp only [deriv_cutoffSchwartz]
    have := (((tendsto_cutoff x).mul_const (∂_ μ ε x)).add
      ((tendsto_deriv_cutoff μ x).mul_const (ε x))).const_mul (g x)
    simpa using this

/-!

## H. Weak extrema are extrema of the lifts

-/

/-- For a weak extremum, the integrated first variation vanishes in every coordinate direction
against every Schwartz function, not only against test functions of compact support. -/
lemma LiftRegular.integral_firstVariation_eq_zero (h : LiftRegular A J) {𝓕 : FreeSpace}
    (hW : IsWeakExtrema 𝓕 A J) (ε : 𝓢(SpaceTime d, ℝ)) (ν : Fin 1 ⊕ Fin d) :
    ∫ x, firstVariation 𝓕 A J ν ε x = 0 := by
  have hn (n : ℕ) : ∫ x, firstVariation 𝓕 A J ν (cutoffSchwartz n ε) x = 0 := by
    have ht : IsTestFunction (fun x => cutoffSchwartz n ε x • Lorentz.Vector.basis ν) :=
      ⟨((cutoffSchwartz n ε).smooth ⊤).smul contDiff_const,
        (cutoffSchwartz_hasCompactSupport n ε).smul_right⟩
    rw [← hW _ ht]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    exact (deriv_lagrangian_smul_basis A J h.differentiable _
      (cutoffSchwartz n ε).differentiable ν x).symm
  have hlim : Tendsto (fun n => ∫ x, firstVariation 𝓕 A J ν (cutoffSchwartz n ε) x) atTop
      (𝓝 (∫ x, firstVariation 𝓕 A J ν ε x)) := by
    simp only [h.integral_firstVariation]
    refine Tendsto.sub (Tendsto.const_mul _ (tendsto_finsetSum _ fun μ _ =>
      Tendsto.sub (Tendsto.const_mul _ ?_) ?_)) (Tendsto.const_mul _ ?_)
    · exact tendsto_integral_mul_deriv_cutoffSchwartz (h.deriv_apply_temperedIntegrable μ ν) ε μ
    · exact tendsto_integral_mul_deriv_cutoffSchwartz (h.deriv_apply_temperedIntegrable ν μ) ε μ
    · exact tendsto_integral_cutoffSchwartz_mul (h.current_temperedIntegrable.apply ν) ε
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr fun n => (hn n).symm)

lemma LiftRegular.isExtrema_of_isWeakExtrema (h : LiftRegular A J) {𝓕 : FreeSpace}
    (hW : IsWeakExtrema 𝓕 A J) :
    DistElectromagneticPotential.IsExtrema 𝓕 (SpaceTime.lift 𝓕.c A.val)
      (SpaceTime.lift 𝓕.c J) := by
  ext ε ν
  have hε := h.integral_firstVariation_eq_gradLagrangian 𝓕 ε ν
  rw [h.integral_firstVariation_eq_zero hW] at hε
  exact (mul_eq_zero.mp hε.symm).resolve_left 𝓕.c.val_ne_zero

/-!

## I. The bridge

-/

/-- The bridge between the functional and the distributional formulations of Maxwell's
equations: a potential `A` and a current `J` which are regular enough to be lifted to
distributions satisfy the weak extremum condition exactly when their lifts satisfy the
distributional extremum condition. -/
theorem LiftRegular.isWeakExtrema_iff_isExtrema_lift (h : LiftRegular A J) (𝓕 : FreeSpace) :
    IsWeakExtrema 𝓕 A J ↔
      DistElectromagneticPotential.IsExtrema 𝓕 (SpaceTime.lift 𝓕.c A.val)
        (SpaceTime.lift 𝓕.c J) :=
  ⟨h.isExtrema_of_isWeakExtrema, h.isWeakExtrema_of_isExtrema⟩

end ElectromagneticPotential
end Electromagnetism
