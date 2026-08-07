/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.Particles.StandardModel.GaugeBosons.Gluons.JetCompleteness.HookBianchi
/-!
# The full-series gauge action and Maurer--Cartan coefficients

## i. Overview

This file proves the group-action laws for `GaugeAction`'s power-series-valued `actPot`, the
full-series Maurer--Cartan cocycle, and an arbitrary-coefficient API in the physical traceless
hermitian colour carrier.  It does not construct an all-orders polynomial carrier.

The multiplication convention is the left action

```text
actPot (U * V) A = actPot U (actPot V A),
```

and the corresponding hermitian Maurer--Cartan cocycle is

```text
mcH (U * V) μ = mcH U μ + U * mcH V μ * star U.
```
-/

@[expose] public section

namespace StandardModel

open Matrix Module MvPowerSeries

namespace SU3Jet

/-!

## A. Full-series Maurer--Cartan and action laws

-/

/-- The Lie-algebra Maurer--Cartan series vanishes on the identity gauge jet. -/
lemma mcP_one (μ : Lor) : mcP (1 : specialUnitaryGroup (Fin 3) JetRing) μ = 0 := by
  rw [mcP]
  change dMat μ (1 : Matrix (Fin 3) (Fin 3) JetRing) * star
      (1 : Matrix (Fin 3) (Fin 3) JetRing) = 0
  rw [dMat_one, Matrix.zero_mul]

/-- The hermitian Maurer--Cartan series vanishes on the identity gauge jet. -/
lemma mcH_one (μ : Lor) : mcH (1 : specialUnitaryGroup (Fin 3) JetRing) μ = 0 := by
  rw [mcH, mcP_one, smul_zero]

/-- The full-series Lie-algebra Maurer--Cartan cocycle. -/
lemma mcP_mul (U V : specialUnitaryGroup (Fin 3) JetRing) (μ : Lor) :
    mcP (U * V) μ = mcP U μ + U.1 * mcP V μ * star U.1 := by
  rw [mcP, mcP, mcP]
  change dMat μ (U.1 * V.1) * star (U.1 * V.1) = _
  rw [dMat_mul, star_mul, Matrix.add_mul]
  have hV : V.1 * star V.1 = 1 := Gluon.coe_mul_star_self V
  calc
    dMat μ U.1 * V.1 * (star V.1 * star U.1) +
          U.1 * dMat μ V.1 * (star V.1 * star U.1) =
        dMat μ U.1 * (V.1 * star V.1) * star U.1 +
          U.1 * (dMat μ V.1 * star V.1) * star U.1 := by
            noncomm_ring
    _ = dMat μ U.1 * star U.1 + U.1 * (dMat μ V.1 * star V.1) * star U.1 := by
      rw [hV, Matrix.mul_one]

/-- The full-series hermitian Maurer--Cartan cocycle, with the orientation forced by `actPot`. -/
lemma mcH_mul (U V : specialUnitaryGroup (Fin 3) JetRing) (μ : Lor) :
    mcH (U * V) μ = mcH U μ + U.1 * mcH V μ * star U.1 := by
  rw [mcH, mcH, mcH, mcP_mul, smul_add]
  simp only [Matrix.smul_mul, Matrix.mul_smul]

/-- The identity gauge jet acts trivially on a full power-series potential. -/
lemma actPot_one (A : Potential) : actPot (1 : specialUnitaryGroup (Fin 3) JetRing) A = A := by
  funext μ
  rw [actPot, mcH_one]
  change (1 : Matrix (Fin 3) (Fin 3) JetRing) * A μ * star
      (1 : Matrix (Fin 3) (Fin 3) JetRing) + 0 = A μ
  simp

/-- The full power-series potential transformation is a left group action. -/
lemma actPot_mul (U V : specialUnitaryGroup (Fin 3) JetRing) (A : Potential) :
    actPot (U * V) A = actPot U (actPot V A) := by
  funext μ
  rw [actPot, actPot, actPot, mcH_mul]
  change (U.1 * V.1) * A μ * star (U.1 * V.1) +
      (mcH U μ + U.1 * mcH V μ * star U.1) =
    U.1 * (V.1 * A μ * star V.1 + mcH V μ) * star U.1 + mcH U μ
  rw [star_mul]
  noncomm_ring

/-!

## B. Arbitrary traceless-hermitian coefficients

-/

/-- The hermitian Maurer--Cartan series is self-adjoint. -/
lemma star_mcH (U : specialUnitaryGroup (Fin 3) JetRing) (μ : Lor) :
    star (mcH U μ) = mcH U μ := by
  have hp := star_mcP U μ
  apply Matrix.ext
  intro i j
  have hpij := congrFun (congrFun hp i) j
  change star ((MvPowerSeries.C Complex.I : JetRing) * (mcP U μ) j i) =
    (MvPowerSeries.C Complex.I : JetRing) * (mcP U μ) i j
  rw [star_mul', JetRing.star_C, Complex.star_def, Complex.conj_I,
    show star ((mcP U μ) j i) = -(mcP U μ) i j from hpij]
  simp

/-- The hermitian Maurer--Cartan series is traceless. -/
lemma trace_mcH (U : specialUnitaryGroup (Fin 3) JetRing) (μ : Lor) : trace (mcH U μ) = 0 := by
  rw [mcH, trace_smul, trace_mcP, smul_zero]

/-- The matrix coefficient of the hermitian Maurer--Cartan series at an arbitrary Lorentz
multi-index. -/
noncomputable def mcCoeffM (U : specialUnitaryGroup (Fin 3) JetRing) (μ : Lor)
    (k : Lor →₀ ℕ) : Matrix (Fin 3) (Fin 3) ℂ := coeffMat k (mcH U μ)

lemma trace_coeffMat (k : Lor →₀ ℕ) (M : Matrix (Fin 3) (Fin 3) JetRing) :
    trace (coeffMat k M) = MvPowerSeries.coeff k (trace M) := by
  rw [Matrix.trace, Matrix.trace, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ rfl

/-- Every arbitrary coefficient of `mcH` is hermitian. -/
lemma star_mcCoeffM (U : specialUnitaryGroup (Fin 3) JetRing) (μ : Lor) (k : Lor →₀ ℕ) :
    star (mcCoeffM U μ k) = mcCoeffM U μ k := by
  have hs := star_mcH U μ
  ext i j
  have hsij := congrFun (congrFun hs i) j
  change star (MvPowerSeries.coeff k ((mcH U μ) j i)) =
    MvPowerSeries.coeff k ((mcH U μ) i j)
  rw [← JetRing.coeff_star]
  exact congrArg (MvPowerSeries.coeff k) hsij

/-- Every arbitrary coefficient of `mcH` is traceless. -/
lemma trace_mcCoeffM (U : specialUnitaryGroup (Fin 3) JetRing) (μ : Lor) (k : Lor →₀ ℕ) :
    trace (mcCoeffM U μ k) = 0 := by
  rw [mcCoeffM, trace_coeffMat, trace_mcH, map_zero]

/-- The arbitrary coefficient of `mcH`, packaged in the physical traceless-hermitian colour
carrier. -/
noncomputable def mcCoeffCAt (U : specialUnitaryGroup (Fin 3) JetRing) (μ : Lor)
    (k : Lor →₀ ℕ) : ColourSpace :=
  mkCM (mcCoeffM U μ k) (star_mcCoeffM U μ k) (trace_mcCoeffM U μ k)

@[simp]
lemma cmat_mcCoeffCAt (U : specialUnitaryGroup (Fin 3) JetRing) (μ : Lor) (k : Lor →₀ ℕ) :
    cmat (mcCoeffCAt U μ k) = mcCoeffM U μ k := rfl

/-!

## C. Coefficient consequences of the cocycle

-/

/-- Coefficient extraction from the series Maurer--Cartan cocycle.  The conjugated term remains
at series level, avoiding an unnecessary general three-fold convolution formula. -/
lemma mcCoeffM_mul (U V : specialUnitaryGroup (Fin 3) JetRing) (μ : Lor) (k : Lor →₀ ℕ) :
    mcCoeffM (U * V) μ k = mcCoeffM U μ k +
      coeffMat k (U.1 * mcH V μ * star U.1) := by
  rw [mcCoeffM, mcCoeffM, mcH_mul]
  ext i j
  simp [coeffMat, Matrix.add_apply]

/-- Every arbitrary Maurer--Cartan coefficient of a constant gauge jet vanishes. -/
lemma mcCoeffM_ofConstantSU (v : specialUnitaryGroup (Fin 3) ℂ) (μ : Lor) (k : Lor →₀ ℕ) :
    mcCoeffM (JetGaugeGroupI.ofConstantSU (Fin 3) v) μ k = 0 := by
  rw [mcCoeffM, mcH, mcP_ofConstantSU, smul_zero]
  ext i j
  simp [coeffMat]

/-- Constant gauge jets have zero arbitrary colour coefficient. -/
lemma mcCoeffCAt_ofConstantSU (v : specialUnitaryGroup (Fin 3) ℂ) (μ : Lor) (k : Lor →₀ ℕ) :
    mcCoeffCAt (JetGaugeGroupI.ofConstantSU (Fin 3) v) μ k = 0 := by
  apply cmat_injective
  rw [cmat_mcCoeffCAt, mcCoeffM_ofConstantSU, cmat_zero]

/-- The full hermitian Maurer--Cartan series of a constant gauge jet vanishes. -/
lemma mcH_ofConstantSU (v : specialUnitaryGroup (Fin 3) ℂ) (μ : Lor) :
    mcH (JetGaugeGroupI.ofConstantSU (Fin 3) v) μ = 0 := by
  rw [mcH, mcP_ofConstantSU, smul_zero]

/-- Conjugation of an arbitrary gauge jet by a constant colour rotation, at series level. -/
lemma mcH_conjBy (v : specialUnitaryGroup (Fin 3) ℂ)
    (V : specialUnitaryGroup (Fin 3) JetRing) (μ : Lor) :
    mcH (conjBy v V) μ =
      (v : Matrix (Fin 3) (Fin 3) ℂ).map (MvPowerSeries.C : ℂ →+* JetRing) * mcH V μ *
        ((v : Matrix (Fin 3) (Fin 3) ℂ))ᴴ.map (MvPowerSeries.C : ℂ →+* JetRing) := by
  have hinv : (JetGaugeGroupI.ofConstantSU (Fin 3) v)⁻¹ =
      JetGaugeGroupI.ofConstantSU (Fin 3) v⁻¹ := (map_inv _ v).symm
  rw [conjBy, hinv, mcH_mul, mcH_mul, mcH_ofConstantSU, mcH_ofConstantSU]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, ofConstantSU_coe]
  congr 1
  ext i j
  simp [Matrix.star_apply, JetRing.star_C]

/-- Arbitrary coefficients commute with multiplication on both sides by constant matrices. -/
lemma coeffMat_conj_const (P R : Matrix (Fin 3) (Fin 3) ℂ)
    (M : Matrix (Fin 3) (Fin 3) JetRing) (k : Lor →₀ ℕ) :
    coeffMat k (P.map (MvPowerSeries.C : ℂ →+* JetRing) * M *
      R.map (MvPowerSeries.C : ℂ →+* JetRing)) = P * coeffMat k M * R := by
  ext i j
  simp only [coeffMat, Matrix.mul_apply, map_sum, MvPowerSeries.coeff_mul_C,
    MvPowerSeries.coeff_C_mul, Matrix.map_apply]

/-- Conjugation by a constant `SU(3)` element conjugates every arbitrary matrix coefficient. -/
lemma mcCoeffM_conjBy (v : specialUnitaryGroup (Fin 3) ℂ)
    (V : specialUnitaryGroup (Fin 3) JetRing) (μ : Lor) (k : Lor →₀ ℕ) :
    mcCoeffM (conjBy v V) μ k =
      (v : Matrix (Fin 3) (Fin 3) ℂ) * mcCoeffM V μ k *
        ((v : Matrix (Fin 3) (Fin 3) ℂ))ᴴ := by
  rw [mcCoeffM, mcH_conjBy, coeffMat_conj_const]
  rfl

/-- Conjugation by a constant `SU(3)` element acts on every arbitrary colour coefficient by
`adC`. -/
lemma mcCoeffCAt_conjBy (v : specialUnitaryGroup (Fin 3) ℂ)
    (V : specialUnitaryGroup (Fin 3) JetRing) (μ : Lor) (k : Lor →₀ ℕ) :
    mcCoeffCAt (conjBy v V) μ k = adC v (mcCoeffCAt V μ k) := by
  apply cmat_injective
  rw [cmat_mcCoeffCAt, cmat_adC, cmat_mcCoeffCAt, mcCoeffM_conjBy]

/-!

## D. Leading coefficients under lower-coefficient vanishing

-/

/-- All coefficients strictly below `k` in the componentwise multi-index order vanish. -/
def LowerCoeffZero (M : Matrix (Fin 3) (Fin 3) JetRing) (k : Lor →₀ ℕ) : Prop :=
  ∀ q, q ≤ k → q ≠ k → coeffMat q M = 0

private lemma finsupp_left_le_of_add_eq {p q k : Lor →₀ ℕ} (h : p + q = k) : p ≤ k := by
  intro i
  have hi := DFunLike.congr_fun h i
  rw [Finsupp.add_apply] at hi
  omega

private lemma finsupp_right_le_of_add_eq {p q k : Lor →₀ ℕ} (h : p + q = k) : q ≤ k := by
  intro i
  have hi := DFunLike.congr_fun h i
  rw [Finsupp.add_apply] at hi
  omega

private lemma coeff_mul_of_right_lower_zero (f g : JetRing) (k : Lor →₀ ℕ)
    (hg : ∀ q, q ≤ k → q ≠ k → MvPowerSeries.coeff q g = 0) :
    MvPowerSeries.coeff k (f * g) =
      MvPowerSeries.constantCoeff f * MvPowerSeries.coeff k g := by
  classical
  rw [MvPowerSeries.coeff_mul, Finset.sum_eq_single (0, k),
    MvPowerSeries.coeff_zero_eq_constantCoeff]
  · rintro ⟨p, q⟩ hp hpair
    have hpq : p + q = k := Finset.mem_antidiagonal.mp hp
    by_cases hq : q = k
    · subst q
      have hp0 : p = 0 := by
        ext i
        have hi : p i + k i = k i := by
          simpa only [Finsupp.add_apply] using DFunLike.congr_fun hpq i
        change p i = 0
        omega
      exact (hpair (Prod.ext hp0 rfl)).elim
    · rw [hg q (finsupp_right_le_of_add_eq hpq) hq, mul_zero]
  · simp

private lemma coeff_mul_of_left_lower_zero (f g : JetRing) (k : Lor →₀ ℕ)
    (hf : ∀ p, p ≤ k → p ≠ k → MvPowerSeries.coeff p f = 0) :
    MvPowerSeries.coeff k (f * g) =
      MvPowerSeries.coeff k f * MvPowerSeries.constantCoeff g := by
  classical
  rw [MvPowerSeries.coeff_mul, Finset.sum_eq_single (k, 0),
    MvPowerSeries.coeff_zero_eq_constantCoeff]
  · rintro ⟨p, q⟩ hp hpair
    have hpq : p + q = k := Finset.mem_antidiagonal.mp hp
    by_cases hp' : p = k
    · subst p
      have hq0 : q = 0 := by
        ext i
        have hi : k i + q i = k i := by
          simpa only [Finsupp.add_apply] using DFunLike.congr_fun hpq i
        change q i = 0
        omega
      exact (hpair (Prod.ext rfl hq0)).elim
    · rw [hf p (finsupp_left_le_of_add_eq hpq) hp', zero_mul]
  · simp

private lemma coeffMat_mul_of_right_lower_zero (P M : Matrix (Fin 3) (Fin 3) JetRing)
    (k : Lor →₀ ℕ) (hM : LowerCoeffZero M k) :
    coeffMat k (P * M) = Gluon.jetValue P * coeffMat k M := by
  apply Matrix.ext
  intro i j
  simp only [coeffMat, Matrix.map_apply, Matrix.mul_apply, Gluon.jetValue]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  apply coeff_mul_of_right_lower_zero
  intro q hq hqk
  have hMq := hM q hq hqk
  exact congrFun (congrFun hMq a) j

private lemma coeffMat_mul_of_left_lower_zero (M R : Matrix (Fin 3) (Fin 3) JetRing)
    (k : Lor →₀ ℕ) (hM : LowerCoeffZero M k) :
    coeffMat k (M * R) = coeffMat k M * Gluon.jetValue R := by
  apply Matrix.ext
  intro i j
  simp only [coeffMat, Matrix.map_apply, Matrix.mul_apply, Gluon.jetValue]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  apply coeff_mul_of_left_lower_zero
  intro q hq hqk
  have hMq := hM q hq hqk
  exact congrFun (congrFun hMq i) a

private lemma lowerCoeffZero_mul_left (P M : Matrix (Fin 3) (Fin 3) JetRing)
    (k : Lor →₀ ℕ) (hM : LowerCoeffZero M k) : LowerCoeffZero (P * M) k := by
  intro q hq hqk
  have hMq : LowerCoeffZero M q := by
    intro r hr hrq
    apply hM r (hr.trans hq)
    intro hrk
    subst r
    exact hqk (le_antisymm hq hr)
  rw [coeffMat_mul_of_right_lower_zero P M q hMq, hM q hq hqk, Matrix.mul_zero]

/-- **Leading coefficient of a conjugated series.** If all coefficients of the middle series
strictly below `k` vanish, then the `k`-coefficient of `P M R` only sees the constant coefficients
of the two outer series. -/
lemma coeffMat_conj_leading (P M R : Matrix (Fin 3) (Fin 3) JetRing) (k : Lor →₀ ℕ)
    (hM : LowerCoeffZero M k) :
    coeffMat k (P * M * R) = Gluon.jetValue P * coeffMat k M * Gluon.jetValue R := by
  rw [coeffMat_mul_of_left_lower_zero (P * M) R k (lowerCoeffZero_mul_left P M k hM),
    coeffMat_mul_of_right_lower_zero P M k hM]

/-- **Leading-order coefficient form of the Maurer--Cartan cocycle.** Under explicit vanishing of
all lower coefficients of `mcH V μ`, the conjugated contribution at `k` is conjugation of the
`k`-coefficient by the base-point value of `U`. -/
lemma mcCoeffM_mul_leading (U V : specialUnitaryGroup (Fin 3) JetRing) (μ : Lor)
    (k : Lor →₀ ℕ) (hV : LowerCoeffZero (mcH V μ) k) :
    mcCoeffM (U * V) μ k = mcCoeffM U μ k +
      Gluon.jetValue U.1 * mcCoeffM V μ k * star (Gluon.jetValue U.1) := by
  rw [mcCoeffM_mul, coeffMat_conj_leading U.1 (mcH V μ) (star U.1) k hV,
    Gluon.jetValue_star]
  rfl

/-- The leading-order cocycle in the physical colour carrier: the second summand is acted on only
by the constant `SU(3)` value of the first jet. -/
lemma mcCoeffCAt_mul_leading (U V : specialUnitaryGroup (Fin 3) JetRing) (μ : Lor)
    (k : Lor →₀ ℕ) (hV : LowerCoeffZero (mcH V μ) k) :
    mcCoeffCAt (U * V) μ k = mcCoeffCAt U μ k +
      adC (JetGaugeGroupI.evalSU (Fin 3) U) (mcCoeffCAt V μ k) := by
  apply cmat_injective
  rw [cmat_mcCoeffCAt, cmat_add, cmat_mcCoeffCAt, cmat_adC, cmat_mcCoeffCAt,
    mcCoeffM_mul_leading U V μ k hV, jetValue_coe_eq, star_eq_conjTranspose]

/-!

## E. Compatibility with the degree-one and degree-two coefficients

-/

/-- The zero multi-index coefficient of `mcH` is `GaugeAction`'s first Maurer--Cartan colour
  coefficient. -/
lemma mcCoeffCAt_zero (U : specialUnitaryGroup (Fin 3) JetRing) (μ : Lor) :
    mcCoeffCAt U μ 0 = mcC U μ := by
  apply cmat_injective
  rw [cmat_mcCoeffCAt, cmat_mcC, mcCoeffM, ← jetValue_mcH]
  ext i j
  simp [coeffMat, Gluon.jetValue]

/-- A degree-one coefficient of `mcH` is `GaugeAction`'s second Maurer--Cartan colour coefficient.
  -/
lemma mcCoeffCAt_single (U : specialUnitaryGroup (Fin 3) JetRing) (ν μ : Lor) :
    mcCoeffCAt U μ (Finsupp.single ν 1) = mc2C U ν μ := by
  apply cmat_injective
  rw [cmat_mcCoeffCAt, cmat_mc2C, mcCoeffM, ← jetDeriv_mcH]
  exact (jetDeriv_eq_coeffMat ν (mcH U μ)).symm

end SU3Jet

end StandardModel
