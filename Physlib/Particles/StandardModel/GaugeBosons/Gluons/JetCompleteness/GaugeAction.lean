/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Physlib.Particles.StandardModel.GaugeBosons.Gluons.JetCompleteness.CoordinateChange
/-!
# The first-order gauge action in covariant coordinates

## i. Overview

This file defines the action of a gauge jet on the first-order gluon jet algebra `A₁` of
`CoordinateChange` and proves
the transformation law of every generator.

The action is not asserted: it is *derived*. A gluon potential together with all of its
derivatives at a point is modelled, as in the underlying matrix-valued jet model, by a
matrix of formal power series for each spacetime direction, and the local gauge action is the
honest affine one

```text
A_μ ↦ U A_μ U† + i (∂_μ U) U†.
```

`jetValue_actPot` and `jetDeriv_actPot` compute the base-point value and the first Taylor
coefficient of the transformed potential, and those two identities are exactly the substitution
`gaugeSubst` used on the polynomial coordinates.

## ii. Conventions

Hermitian throughout, matching the Physlib gluon convention. The Maurer–Cartan series carries the
`+i` of
`Gluon.mcMatrix`, and the colour bracket is `brMat M N = i (M N - N M)` as in `CoordinateChange`.
The
Lie-algebra (anti-hermitian) formulas of the underlying matrix-valued jet calculation are converted,
never adopted.

## iii. The three transformation laws

With `u = U(0)`, `m_ν = Gluon.mcCoeff U ν` and `t_{νμ} = mc2C U ν μ` the second Maurer–Cartan
coefficient:

```text
A_μ      ↦ Ad_u A_μ + m_μ
∂_ν A_μ  ↦ Ad_u (∂_ν A_μ) - i [m_ν, Ad_u A_μ] + t_{νμ}
F_{νμ}   ↦ Ad_u F_{νμ}
```

The third is `curvC_actPt`/`gaugeAct_curvPoly`: the field strength is *covariant*, not invariant.
The antisymmetric part of `t` is exactly what makes the cancellation work:
`t_{νμ} - t_{μν} = -i [m_ν, m_μ]` (`mc2C_sub`).

## iv. Results

* `mcP`, `mc2M`, `mc2C` — the Maurer–Cartan series and its first derivative;
* `trace_mcP` — the Maurer–Cartan series is traceless, because `det U = 1`;
* `actPot`, `jetValue_actPot`, `jetDeriv_actPot` — the derived coordinate transformation;
* `gaugeSubst`, `gaugeAct` — the induced substitution on `A₁`;
* `gaugeAct_curvPoly` — **curvature transforms by conjugation by the base-point value**.

-/

@[expose] public section

namespace StandardModel

open Matrix Module MvPolynomial

namespace SU3Jet

/-!

## A. The entrywise formal derivative on matrices of jets

These entrywise derivative lemmas support the power-series gauge-action calculation.

-/

/-- The entrywise formal partial derivative of a matrix of jets. -/
noncomputable def dMat (ν : Lor) (M : Matrix (Fin 3) (Fin 3) JetRing) :
    Matrix (Fin 3) (Fin 3) JetRing :=
  M.map (fun f => MvPowerSeries.pderiv ℂ ν f)

@[simp]
lemma dMat_apply (ν : Lor) (M : Matrix (Fin 3) (Fin 3) JetRing) (i j : Fin 3) :
    dMat ν M i j = MvPowerSeries.pderiv ℂ ν (M i j) := rfl

lemma dMat_mul (ν : Lor) (M N : Matrix (Fin 3) (Fin 3) JetRing) :
    dMat ν (M * N) = dMat ν M * N + M * dMat ν N := by
  refine Matrix.ext fun i j => ?_
  rw [dMat_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply,
    map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Derivation.leibniz]
  simp only [dMat_apply, smul_eq_mul]
  ring

@[simp]
lemma dMat_one (ν : Lor) : dMat ν (1 : Matrix (Fin 3) (Fin 3) JetRing) = 0 := by
  refine Matrix.ext fun i j => ?_
  by_cases h : i = j <;> simp [h]

lemma dMat_star (ν : Lor) (M : Matrix (Fin 3) (Fin 3) JetRing) :
    dMat ν (star M) = star (dMat ν M) := by
  refine Matrix.ext fun i j => ?_
  exact JetRing.pderiv_star ν (M j i)

lemma dMat_comm (μ ν : Lor) (M : Matrix (Fin 3) (Fin 3) JetRing) :
    dMat μ (dMat ν M) = dMat ν (dMat μ M) :=
  Matrix.ext fun i j => JetRing.pderiv_comm μ ν (M i j)

/-- The base-point value of the entrywise derivative is the first Taylor coefficient. -/
lemma jetValue_dMat (ν : Lor) (M : Matrix (Fin 3) (Fin 3) JetRing) :
    Gluon.jetValue (dMat ν M) = Gluon.jetDeriv ν M := by
  ext i j
  show MvPowerSeries.constantCoeff (MvPowerSeries.pderiv ℂ ν (M i j)) =
    MvPowerSeries.coeff (Finsupp.single ν 1) (M i j)
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
  simp

lemma jetDeriv_add (ν : Lor) (M N : Matrix (Fin 3) (Fin 3) JetRing) :
    Gluon.jetDeriv ν (M + N) = Gluon.jetDeriv ν M + Gluon.jetDeriv ν N := by
  ext i j
  simp [Gluon.jetDeriv, Matrix.add_apply]

lemma jetValue_add (M N : Matrix (Fin 3) (Fin 3) JetRing) :
    Gluon.jetValue (M + N) = Gluon.jetValue M + Gluon.jetValue N := by
  ext i j
  simp [Gluon.jetValue, Matrix.add_apply]

lemma jetValue_sub (M N : Matrix (Fin 3) (Fin 3) JetRing) :
    Gluon.jetValue (M - N) = Gluon.jetValue M - Gluon.jetValue N := by
  ext i j
  simp [Gluon.jetValue, Matrix.sub_apply]

lemma trace_jetValue (M : Matrix (Fin 3) (Fin 3) JetRing) :
    trace (Gluon.jetValue M) = MvPowerSeries.constantCoeff (trace M) := by
  rw [Matrix.trace, Matrix.trace, map_sum]
  exact Finset.sum_congr rfl fun i _ => rfl

lemma trace_jetDeriv (ν : Lor) (M : Matrix (Fin 3) (Fin 3) JetRing) :
    trace (Gluon.jetDeriv ν M) = MvPowerSeries.coeff (Finsupp.single ν 1) (trace M) := by
  rw [Matrix.trace, Matrix.trace, map_sum]
  exact Finset.sum_congr rfl fun i _ => rfl

/-!

## B. The Maurer–Cartan series

`mcP` is the Lie-algebra (anti-hermitian) Maurer–Cartan series `(∂_μ U) U†` of the underlying
matrix-valued jet calculation.
The hermitian series is `i` times it; the factor of `i` is inserted only after passing to complex
matrices, so no star-module structure on the jet ring is needed.

-/

variable (U : specialUnitaryGroup (Fin 3) JetRing)

lemma coe_star_mul_self : star (U : Matrix (Fin 3) (Fin 3) JetRing) * U.1 = 1 :=
  mem_unitaryGroup_iff'.mp (mem_specialUnitaryGroup_iff.mp U.2).1

/-- The Maurer–Cartan series of a gauge jet, in the Lie-algebra convention: `(∂_μ U) U†`. -/
noncomputable def mcP (μ : Lor) : Matrix (Fin 3) (Fin 3) JetRing :=
  dMat μ U.1 * star U.1

lemma dMat_star_coe (μ : Lor) : dMat μ (star U.1) = -(star U.1 * mcP U μ) := by
  have h := congrArg (dMat μ) (Gluon.coe_mul_star_self U)
  rw [dMat_mul, dMat_one] at h
  have h2 : U.1 * dMat μ (star U.1) = -(dMat μ U.1 * star U.1) :=
    eq_neg_of_add_eq_zero_right h
  calc dMat μ (star U.1)
      = star U.1 * U.1 * dMat μ (star U.1) := by rw [coe_star_mul_self, Matrix.one_mul]
    _ = star U.1 * (U.1 * dMat μ (star U.1)) := by rw [Matrix.mul_assoc]
    _ = -(star U.1 * mcP U μ) := by rw [h2, mcP, Matrix.mul_neg]

/-- The Maurer–Cartan series is anti-self-adjoint; the hermitian series is `i` times it. -/
lemma star_mcP (μ : Lor) : star (mcP U μ) = -mcP U μ := by
  have h := congrArg (dMat μ) (Gluon.coe_mul_star_self U)
  rw [dMat_mul, dMat_one] at h
  rw [mcP, star_mul, star_star, ← dMat_star]
  exact eq_neg_of_add_eq_zero_right h

/-- The derivative of the Maurer–Cartan series: a symmetric second-derivative term together with
  a quadratic term. This is `dMat_mcP`, converted. -/
lemma dMat_mcP (ν μ : Lor) :
    dMat ν (mcP U μ) = dMat ν (dMat μ U.1) * star U.1 - mcP U μ * mcP U ν := by
  rw [mcP, dMat_mul, dMat_star_coe]
  rw [show dMat μ U.1 * -(star U.1 * mcP U ν) = -(dMat μ U.1 * star U.1 * mcP U ν) by
    rw [Matrix.mul_neg, Matrix.mul_assoc]]
  rw [← mcP]
  abel

lemma jetValue_mcP (μ : Lor) :
    Gluon.jetValue (mcP U μ) = Gluon.jetDeriv μ U.1 * star (Gluon.jetValue U.1) := by
  rw [mcP, Gluon.jetValue_mul, Gluon.jetValue_star, jetValue_dMat]

lemma mcMatrix_eq (μ : Lor) :
    Gluon.mcMatrix μ U.1 = Complex.I • Gluon.jetValue (mcP U μ) := by
  rw [Gluon.mcMatrix, jetValue_mcP]

/-!

### B.1. The Maurer–Cartan series is traceless

Unitarity alone makes the series anti-self-adjoint; it is the determinant-one condition that makes
it traceless, i.e. `su(3)`-valued rather than `u(3)`-valued. This is the all-orders tracelessness
statement needed below.

-/

/-- Jacobi's formula for `3 × 3` matrices of jets: a direct expansion, not a general
  determinant-derivative development. -/
lemma pderiv_det (ν : Lor) (M : Matrix (Fin 3) (Fin 3) JetRing) :
    MvPowerSeries.pderiv ℂ ν M.det = trace (dMat ν M * adjugate M) := by
  simp only [Matrix.det_fin_three, Matrix.adjugate_fin_three, map_add, map_sub,
    Derivation.leibniz, smul_eq_mul, Matrix.trace_fin_three, Matrix.mul_apply,
    Fin.sum_univ_three, dMat_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_fin_const]
  ring

/-- For a gauge jet the adjugate is the conjugate transpose. -/
lemma adjugate_coe : adjugate (U : Matrix (Fin 3) (Fin 3) JetRing) = star U.1 := by
  have h3 : (U : Matrix (Fin 3) (Fin 3) JetRing) * adjugate U.1 = 1 := by
    rw [Matrix.mul_adjugate, (mem_specialUnitaryGroup_iff.mp U.2).2, one_smul]
  calc adjugate (U : Matrix (Fin 3) (Fin 3) JetRing)
      = 1 * adjugate U.1 := by rw [Matrix.one_mul]
    _ = star U.1 * U.1 * adjugate U.1 := by rw [coe_star_mul_self]
    _ = star U.1 * (U.1 * adjugate U.1) := by rw [Matrix.mul_assoc]
    _ = star U.1 := by rw [h3, Matrix.mul_one]

/-- **The Maurer–Cartan series is traceless.** -/
lemma trace_mcP (μ : Lor) : trace (mcP U μ) = 0 := by
  have h := pderiv_det μ (U : Matrix (Fin 3) (Fin 3) JetRing)
  rw [(mem_specialUnitaryGroup_iff.mp U.2).2, Derivation.map_one_eq_zero, adjugate_coe] at h
  rw [mcP, ← h]

/-!

## C. The colour data of a gauge jet

-/

/-- The base-point Maurer–Cartan coefficient, as a colour vector. -/
noncomputable def mcC (μ : Lor) : ColourSpace :=
  ⟨Gluon.mcCoeff U μ, by
    show trace (Gluon.mcMatrix μ U.1) = 0
    rw [mcMatrix_eq U, trace_smul, trace_jetValue, trace_mcP, map_zero, smul_zero]⟩

@[simp]
lemma cmat_mcC (μ : Lor) : cmat (mcC U μ) = Gluon.mcMatrix μ U.1 := rfl

/-- The first derivative of the hermitian Maurer–Cartan series, as a complex matrix. -/
noncomputable def mc2M (ν μ : Lor) : Matrix (Fin 3) (Fin 3) ℂ :=
  Complex.I • Gluon.jetDeriv ν (mcP U μ)

lemma star_mc2M (ν μ : Lor) : star (mc2M U ν μ) = mc2M U ν μ := by
  have h : star (Gluon.jetDeriv ν (mcP U μ)) = -Gluon.jetDeriv ν (mcP U μ) := by
    rw [← Gluon.jetDeriv_star, star_mcP]
    ext i j
    simp [Gluon.jetDeriv, Matrix.neg_apply]
  rw [mc2M, star_smul, h, Complex.star_def, Complex.conj_I, neg_smul, ← smul_neg, neg_neg]

lemma trace_mc2M (ν μ : Lor) : trace (mc2M U ν μ) = 0 := by
  rw [mc2M, trace_smul, trace_jetDeriv, trace_mcP, map_zero, smul_zero]

/-- The second Maurer–Cartan coefficient, as a colour vector: the constant by which an order-two
  based jet translates the derivative coordinates. -/
noncomputable def mc2C (ν μ : Lor) : ColourSpace :=
  mkCM (mc2M U ν μ) (star_mc2M U ν μ) (trace_mc2M U ν μ)

@[simp]
lemma cmat_mc2C (ν μ : Lor) : cmat (mc2C U ν μ) = mc2M U ν μ := rfl

/-- **The antisymmetric part of the second Maurer–Cartan coefficient.** It is exactly minus the
  colour bracket of the first coefficients; this identity is what makes the field strength
  covariant, and it is why the order-two translation is symmetric on based jets. -/
lemma mc2C_sub (ν μ : Lor) :
    mc2C U ν μ - mc2C U μ ν = -br (mcC U ν) (mcC U μ) := by
  apply cmat_injective
  have hd : ∀ ρ σ : Lor, Gluon.jetDeriv ρ (mcP U σ) =
      Gluon.jetValue (dMat ρ (dMat σ U.1) * star U.1) -
        Gluon.jetValue (mcP U σ) * Gluon.jetValue (mcP U ρ) := by
    intro ρ σ
    rw [← jetValue_dMat, dMat_mcP, jetValue_sub, Gluon.jetValue_mul (mcP U σ) (mcP U ρ)]
  have key : Gluon.jetDeriv ν (mcP U μ) - Gluon.jetDeriv μ (mcP U ν) =
      Gluon.jetValue (mcP U ν) * Gluon.jetValue (mcP U μ) -
        Gluon.jetValue (mcP U μ) * Gluon.jetValue (mcP U ν) := by
    rw [hd ν μ, hd μ ν, dMat_comm ν μ U.1]
    abel
  have hI : ∀ Z : Matrix (Fin 3) (Fin 3) ℂ, Complex.I • (Complex.I • Z) = -Z := by
    intro Z
    rw [smul_smul, Complex.I_mul_I, neg_smul, one_smul]
  show mc2M U ν μ - mc2M U μ ν = -brMat (cmat (mcC U ν)) (cmat (mcC U μ))
  rw [mc2M, mc2M, ← smul_sub, key, brMat, cmat_mcC, cmat_mcC, mcMatrix_eq, mcMatrix_eq]
  simp only [Matrix.smul_mul, Matrix.mul_smul, hI]
  module

/-!

## D. The gauge action on potentials

-/

/-- A gluon potential together with all of its derivatives at a point: for each spacetime
  direction a matrix of formal power series in the spacetime coordinates. -/
abbrev Potential : Type := Lor → Matrix (Fin 3) (Fin 3) JetRing

/-- The hermitian Maurer–Cartan series `i (∂_μ U) U†`, written without a star-module structure on
  the jet ring. -/
noncomputable def mcH (μ : Lor) : Matrix (Fin 3) (Fin 3) JetRing :=
  (MvPowerSeries.C Complex.I : JetRing) • mcP U μ

lemma jetValue_mcH (μ : Lor) : Gluon.jetValue (mcH U μ) = Gluon.mcMatrix μ U.1 := by
  rw [mcMatrix_eq U]
  ext i j
  show MvPowerSeries.constantCoeff ((MvPowerSeries.C Complex.I : JetRing) * (mcP U μ) i j) =
    Complex.I * MvPowerSeries.constantCoeff ((mcP U μ) i j)
  simp

lemma jetDeriv_mcH (ν μ : Lor) : Gluon.jetDeriv ν (mcH U μ) = mc2M U ν μ := by
  rw [mc2M]
  ext i j
  show MvPowerSeries.coeff (Finsupp.single ν 1)
      ((MvPowerSeries.C Complex.I : JetRing) * (mcP U μ) i j) =
    Complex.I * MvPowerSeries.coeff (Finsupp.single ν 1) ((mcP U μ) i j)
  simp

/-- **The local gauge action on potentials**, in the hermitian convention:
  `A_μ ↦ U A_μ U† + i (∂_μ U) U†`. -/
noncomputable def actPot (A : Potential) : Potential :=
  fun μ => U.1 * A μ * star U.1 + mcH U μ

/-- **The transformation of the connection coordinate.** -/
lemma jetValue_actPot (A : Potential) (μ : Lor) :
    Gluon.jetValue (actPot U A μ) =
      Gluon.jetValue U.1 * Gluon.jetValue (A μ) * star (Gluon.jetValue U.1) +
        Gluon.mcMatrix μ U.1 := by
  rw [actPot, jetValue_add, jetValue_mcH, Gluon.jetValue_mul, Gluon.jetValue_mul,
    Gluon.jetValue_star]

lemma jetDeriv_coe (ν : Lor) :
    Gluon.jetDeriv ν U.1 = (-Complex.I) • (Gluon.mcMatrix ν U.1 * Gluon.jetValue U.1) := by
  have hu : star (Gluon.jetValue U.1) * Gluon.jetValue U.1 = 1 :=
    mul_eq_one_comm.mp (Gluon.jetValue_mul_star_self U)
  rw [Gluon.mcMatrix, Matrix.smul_mul, smul_smul, Matrix.mul_assoc, hu, Matrix.mul_one,
    show (-Complex.I) * Complex.I = 1 by rw [neg_mul, Complex.I_mul_I, neg_neg], one_smul]

lemma jetDeriv_star_coe (ν : Lor) :
    Gluon.jetDeriv ν (star U.1) =
      Complex.I • (star (Gluon.jetValue U.1) * Gluon.mcMatrix ν U.1) := by
  have hh : star (Gluon.mcMatrix ν U.1) = Gluon.mcMatrix ν U.1 :=
    selfAdjoint.mem_iff.mp (Gluon.mcMatrix_mem_selfAdjoint (Gluon.coe_mul_star_self U) ν)
  rw [Gluon.jetDeriv_star, jetDeriv_coe, star_smul, star_mul, hh, Complex.star_def, map_neg,
    Complex.conj_I, neg_neg]

/-- **The transformation of the derivative coordinate.** Conjugation by the base-point value,
  a commutator with the Maurer–Cartan coefficient, and a translation by the second Maurer–Cartan
  coefficient. -/
lemma jetDeriv_actPot (A : Potential) (ν μ : Lor) :
    Gluon.jetDeriv ν (actPot U A μ) =
      Gluon.jetValue U.1 * Gluon.jetDeriv ν (A μ) * star (Gluon.jetValue U.1) -
        brMat (Gluon.mcMatrix ν U.1)
          (Gluon.jetValue U.1 * Gluon.jetValue (A μ) * star (Gluon.jetValue U.1)) +
        mc2M U ν μ := by
  rw [actPot, jetDeriv_add, jetDeriv_mcH, Gluon.jetDeriv_mul, Gluon.jetDeriv_mul,
    Gluon.jetValue_mul, Gluon.jetValue_star, jetDeriv_coe, jetDeriv_star_coe]
  congr 1
  rw [brMat]
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul, smul_sub, Matrix.mul_assoc]
  module

/-!

## E. The adjoint action on the colour carrier

-/

lemma adjointAction_mem_ColourSpace (u : specialUnitaryGroup (Fin 3) ℂ)
    {A : selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ)} (hA : A ∈ ColourSpace) :
    Gluon.adjointAction u A ∈ ColourSpace := by
  have hu : ((u : Matrix (Fin 3) (Fin 3) ℂ))ᴴ * (u : Matrix (Fin 3) (Fin 3) ℂ) = 1 := by
    have h := mem_unitaryGroup_iff'.mp (mem_specialUnitaryGroup_iff.mp u.2).1
    rwa [star_eq_conjTranspose] at h
  rw [mem_ColourSpace, Gluon.adjointAction_apply_coe, trace_mul_cycle, hu, Matrix.one_mul]
  exact hA

/-- The adjoint action of a constant colour rotation on the traceless hermitian carrier. -/
noncomputable def adC (u : specialUnitaryGroup (Fin 3) ℂ) : ColourSpace →ₗ[ℝ] ColourSpace :=
  LinearMap.restrict (Gluon.adjointAction u) (fun _ hX => adjointAction_mem_ColourSpace u hX)

@[simp]
lemma cmat_adC (u : specialUnitaryGroup (Fin 3) ℂ) (X : ColourSpace) :
    cmat (adC u X) = (u : Matrix (Fin 3) (Fin 3) ℂ) * cmat X *
      ((u : Matrix (Fin 3) (Fin 3) ℂ))ᴴ := rfl

@[simp]
lemma adC_one (X : ColourSpace) : adC 1 X = X := by
  apply cmat_injective
  rw [cmat_adC]
  show (1 : Matrix (Fin 3) (Fin 3) ℂ) * cmat X * (1 : Matrix (Fin 3) (Fin 3) ℂ)ᴴ = cmat X
  rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

/-- The adjoint action is a homomorphism for the colour bracket. -/
lemma br_adC (u : specialUnitaryGroup (Fin 3) ℂ) (X Y : ColourSpace) :
    br (adC u X) (adC u Y) = adC u (br X Y) := by
  apply cmat_injective
  have hu : ((u : Matrix (Fin 3) (Fin 3) ℂ))ᴴ * (u : Matrix (Fin 3) (Fin 3) ℂ) = 1 := by
    have h := mem_unitaryGroup_iff'.mp (mem_specialUnitaryGroup_iff.mp u.2).1
    rwa [star_eq_conjTranspose] at h
  rw [cmat_br, cmat_adC, cmat_adC, cmat_adC, cmat_br, brMat, brMat]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  rw [show ((u : Matrix (Fin 3) (Fin 3) ℂ))ᴴ * ((u : Matrix (Fin 3) (Fin 3) ℂ) *
      (cmat Y * ((u : Matrix (Fin 3) (Fin 3) ℂ))ᴴ)) =
      cmat Y * ((u : Matrix (Fin 3) (Fin 3) ℂ))ᴴ by
    rw [← Matrix.mul_assoc, hu, Matrix.one_mul]]
  rw [show ((u : Matrix (Fin 3) (Fin 3) ℂ))ᴴ * ((u : Matrix (Fin 3) (Fin 3) ℂ) *
      (cmat X * ((u : Matrix (Fin 3) (Fin 3) ℂ))ᴴ)) =
      cmat X * ((u : Matrix (Fin 3) (Fin 3) ℂ))ᴴ by
    rw [← Matrix.mul_assoc, hu, Matrix.one_mul]]

/-- The matrix of the adjoint action in the colour basis. -/
noncomputable def adCoef (u : specialUnitaryGroup (Fin 3) ℂ) (c c' : Col) : ℝ :=
  coordC c (adC u (colourBasis c'))

lemma adCoef_one (c c' : Col) : adCoef 1 c c' = if c = c' then 1 else 0 := by
  rw [adCoef, adC_one, coordC_apply]
  by_cases h : c = c'
  · subst h
    simp
  · rw [if_neg h, Basis.repr_self_apply, if_neg fun hc => h hc.symm]

lemma coordC_adC (u : specialUnitaryGroup (Fin 3) ℂ) (X : ColourSpace) (c : Col) :
    coordC c (adC u X) = ∑ c', adCoef u c c' * coordC c' X := by
  conv_lhs => rw [← colourBasis.sum_repr X]
  simp only [map_sum, map_smul, smul_eq_mul, coordC_apply, adCoef]
  exact Finset.sum_congr rfl fun c' _ => by ring

/-!

## F. The substitution on the polynomial algebra

-/

section Poly

variable {ι σ τ : Type*}

/-- The adjoint action on a colour vector of polynomials. -/
noncomputable def adP (u : specialUnitaryGroup (Fin 3) ℂ) (p : Col → MvPolynomial ι ℝ) :
    Col → MvPolynomial ι ℝ :=
  fun c => ∑ c', C (adCoef u c c') * p c'

/-- A constant colour vector of polynomials. -/
noncomputable def constP (Y : ColourSpace) : Col → MvPolynomial ι ℝ := fun c => C (coordC c Y)

lemma adP_one (p : Col → MvPolynomial ι ℝ) (c : Col) : adP 1 p c = p c := by
  rw [adP]
  have h : ∀ c' : Col, (C (adCoef 1 c c') : MvPolynomial ι ℝ) * p c' =
      if c = c' then p c' else 0 := by
    intro c'
    rw [adCoef_one]
    by_cases hc : c = c' <;> simp [hc]
  rw [Finset.sum_congr rfl fun c' (_ : c' ∈ Finset.univ) => h c']
  simp

@[simp]
lemma constP_zero : constP (0 : ColourSpace) = (fun _ => 0 : Col → MvPolynomial ι ℝ) := by
  funext c
  rw [constP, map_zero, map_zero]

lemma brP_zero_left (q : Col → MvPolynomial ι ℝ) (c : Col) :
    brP (fun _ => 0) q c = 0 := by
  rw [brP]
  exact Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => by simp

lemma eval_adP (x : ι → ℝ) (u : specialUnitaryGroup (Fin 3) ℂ) (p : Col → MvPolynomial ι ℝ)
    (c : Col) :
    eval x (adP u p c) = coordC c (adC u (mkC fun a => eval x (p a))) := by
  rw [coordC_adC]
  simp only [coordC_mkC]
  rw [adP, map_sum]
  exact Finset.sum_congr rfl fun c' _ => by rw [map_mul, eval_C]

@[simp]
lemma eval_constP (x : ι → ℝ) (Y : ColourSpace) (c : Col) :
    eval x (constP Y c : MvPolynomial ι ℝ) = coordC c Y := eval_C _

lemma mkC_eval_constP (x : ι → ℝ) (Y : ColourSpace) :
    (mkC fun a => eval x (constP Y a : MvPolynomial ι ℝ)) = Y := by
  rw [show (fun a => eval x (constP Y a : MvPolynomial ι ℝ)) = fun a => coordC a Y from
    funext fun a => eval_constP x Y a]
  exact mkC_coordC Y

lemma algHom_adP (φ : MvPolynomial σ ℝ →ₐ[ℝ] MvPolynomial τ ℝ)
    (u : specialUnitaryGroup (Fin 3) ℂ) (p : Col → MvPolynomial σ ℝ) (c : Col) :
    φ (adP u p c) = adP u (fun a => φ (p a)) c := by
  rw [adP, adP, map_sum]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [map_mul, ← algebraMap_eq, AlgHom.commutes, algebraMap_eq]

lemma algHom_constP (φ : MvPolynomial σ ℝ →ₐ[ℝ] MvPolynomial τ ℝ) (Y : ColourSpace) (c : Col) :
    φ (constP Y c) = constP Y c := by
  show φ (C (coordC c Y)) = C (coordC c Y)
  rw [← algebraMap_eq, AlgHom.commutes, algebraMap_eq]

end Poly

/-- The derivative colour vector in ordinary coordinates. -/
noncomputable def derOld (ν μ : Lor) : Col → A₁ := fun c => X (Coord.der ν μ c)

/-- **The gauge substitution**: the coordinate transcription of `jetValue_actPot` and
  `jetDeriv_actPot`. -/
noncomputable def gaugeSubst : Coord → A₁
  | Coord.conn μ c =>
      adP (JetGaugeGroupI.evalSU (Fin 3) U) (connOld μ) c + constP (mcC U μ) c
  | Coord.der ν μ c =>
      adP (JetGaugeGroupI.evalSU (Fin 3) U) (derOld ν μ) c -
        brP (constP (mcC U ν)) (adP (JetGaugeGroupI.evalSU (Fin 3) U) (connOld μ)) c +
        constP (mc2C U ν μ) c

/-- The pullback of the local gauge action to the first-order gluon jet algebra. -/
noncomputable def gaugeAct : A₁ →ₐ[ℝ] A₁ := aeval (gaugeSubst U)

@[simp]
lemma gaugeAct_conn (μ : Lor) (c : Col) :
    gaugeAct U (X (Coord.conn μ c)) =
      adP (JetGaugeGroupI.evalSU (Fin 3) U) (connOld μ) c + constP (mcC U μ) c := aeval_X _ _

@[simp]
lemma gaugeAct_der (ν μ : Lor) (c : Col) :
    gaugeAct U (X (Coord.der ν μ c)) =
      adP (JetGaugeGroupI.evalSU (Fin 3) U) (derOld ν μ) c -
        brP (constP (mcC U ν)) (adP (JetGaugeGroupI.evalSU (Fin 3) U) (connOld μ)) c +
        constP (mc2C U ν μ) c := aeval_X _ _

/-!

## G. Points of the coordinate space

Polynomial identities are proved by evaluating at every point, which turns them into identities in
the colour carrier. `MvPolynomial.funext` applies because `ℝ` is an infinite integral domain.

-/

/-- The connection of the configuration described by a point of the coordinate space. -/
noncomputable def cfgA (x : Coord → ℝ) (μ : Lor) : ColourSpace := mkC fun c => x (Coord.conn μ c)

/-- The connection derivative of the configuration described by a point. -/
noncomputable def cfgD (x : Coord → ℝ) (ν μ : Lor) : ColourSpace :=
  mkC fun c => x (Coord.der ν μ c)

/-- The field strength of the configuration described by a point. -/
noncomputable def curvC (x : Coord → ℝ) (ν μ : Lor) : ColourSpace :=
  cfgD x ν μ - cfgD x μ ν + br (cfgA x ν) (cfgA x μ)

/-- The transformed connection. -/
noncomputable def actA (x : Coord → ℝ) (μ : Lor) : ColourSpace :=
  adC (JetGaugeGroupI.evalSU (Fin 3) U) (cfgA x μ) + mcC U μ

/-- The transformed connection derivative. -/
noncomputable def actD (x : Coord → ℝ) (ν μ : Lor) : ColourSpace :=
  adC (JetGaugeGroupI.evalSU (Fin 3) U) (cfgD x ν μ) -
    br (mcC U ν) (adC (JetGaugeGroupI.evalSU (Fin 3) U) (cfgA x μ)) + mc2C U ν μ

/-- The transformed point of the coordinate space. -/
noncomputable def actPt (x : Coord → ℝ) : Coord → ℝ
  | Coord.conn μ c => coordC c (actA U x μ)
  | Coord.der ν μ c => coordC c (actD U x ν μ)

lemma mkC_eval_connOld (x : Coord → ℝ) (μ : Lor) :
    (mkC fun a => eval x (connOld μ a)) = cfgA x μ := by
  rw [cfgA]
  congr 1
  funext a
  exact eval_X _

lemma mkC_eval_derOld (x : Coord → ℝ) (ν μ : Lor) :
    (mkC fun a => eval x (derOld ν μ a)) = cfgD x ν μ := by
  rw [cfgD]
  congr 1
  funext a
  exact eval_X _

lemma mkC_eval_adP_connOld (x : Coord → ℝ) (u : specialUnitaryGroup (Fin 3) ℂ) (μ : Lor) :
    (mkC fun b => eval x (adP u (connOld μ) b)) = adC u (cfgA x μ) := by
  rw [show (fun b => eval x (adP u (connOld μ) b)) = fun b => coordC b (adC u (cfgA x μ)) from
    funext fun b => by rw [eval_adP, mkC_eval_connOld]]
  exact mkC_coordC _

lemma eval_gaugeSubst (x : Coord → ℝ) (i : Coord) :
    eval x (gaugeSubst U i) = actPt U x i := by
  cases i with
  | conn μ c =>
      rw [gaugeSubst, map_add, eval_adP, eval_constP, mkC_eval_connOld, actPt, actA, map_add]
  | der ν μ c =>
      rw [gaugeSubst, map_add, map_sub, eval_adP, eval_constP, eval_brP, mkC_eval_derOld,
        mkC_eval_constP, mkC_eval_adP_connOld, actPt, actD, map_add, map_sub]

lemma eval_gaugeAct (x : Coord → ℝ) (P : A₁) :
    eval x (gaugeAct U P) = eval (actPt U x) P := by
  have h : (fun i => eval x (gaugeSubst U i)) = actPt U x :=
    funext fun i => eval_gaugeSubst U x i
  rw [gaugeAct, MvPolynomial.eval_aeval, h]

@[simp]
lemma cfgA_actPt (x : Coord → ℝ) (μ : Lor) : cfgA (actPt U x) μ = actA U x μ := mkC_coordC _

@[simp]
lemma cfgD_actPt (x : Coord → ℝ) (ν μ : Lor) : cfgD (actPt U x) ν μ = actD U x ν μ :=
  mkC_coordC _

lemma eval_curvPoly (x : Coord → ℝ) (ν μ : Lor) (c : Col) :
    eval x (curvPoly ν μ c) = coordC c (curvC x ν μ) := by
  simp only [curvPoly, curvC, cfgD, map_add, map_sub, eval_X, coordC_mkC]
  rw [eval_brP, mkC_eval_connOld, mkC_eval_connOld]

/-!

## H. Covariance of the field strength

-/

private lemma curv_shift (Av Am Dvm Dmv mv mm tvm tmv : ColourSpace)
    (ht : tvm - tmv = -br mv mm) :
    (Dvm - br mv Am + tvm) - (Dmv - br mm Av + tmv) + br (Av + mv) (Am + mm)
      = Dvm - Dmv + br Av Am := by
  have h1 : br (Av + mv) (Am + mm) = br Av Am + br Av mm + br mv Am + br mv mm := by
    rw [show br (Av + mv) = br Av + br mv from map_add br Av mv, LinearMap.add_apply,
      map_add, map_add]
    abel
  have h2 : br Av mm = -br mm Av := br_swap Av mm
  have ht' : tvm = tmv - br mv mm := by
    rw [sub_eq_iff_eq_add.mp ht]
    abel
  rw [h1, h2, ht']
  abel

/-- **Covariance of the field strength.** Under any gauge jet the field strength of the
  transformed configuration is the conjugate, by the base-point value of the jet, of the field
  strength of the original configuration. -/
lemma curvC_actPt (x : Coord → ℝ) (ν μ : Lor) :
    curvC (actPt U x) ν μ = adC (JetGaugeGroupI.evalSU (Fin 3) U) (curvC x ν μ) := by
  rw [curvC, cfgA_actPt, cfgA_actPt, cfgD_actPt, cfgD_actPt, actA, actA, actD, actD,
    curv_shift _ _ _ _ _ _ _ _ (mc2C_sub U ν μ), curvC, map_add, map_sub, br_adC]

/-- **Covariance of the field strength, in coordinates.** This is the transformation law the
  completeness theorem consumes: the curvature generators span a subspace on which the whole jet
  gauge group acts through its evaluation at the base point. -/
lemma gaugeAct_curvPoly (ν μ : Lor) (c : Col) :
    gaugeAct U (curvPoly ν μ c) =
      ∑ c', C (adCoef (JetGaugeGroupI.evalSU (Fin 3) U) c c') * curvPoly ν μ c' := by
  refine MvPolynomial.funext fun x => ?_
  rw [eval_gaugeAct, eval_curvPoly, curvC_actPt, coordC_adC, map_sum]
  exact Finset.sum_congr rfl fun c' _ => by rw [map_mul, eval_C, eval_curvPoly]

/-!

## I. Constant jets

-/

lemma pderiv_C_jet (ν : Lor) (a : ℂ) :
    MvPowerSeries.pderiv ℂ ν (MvPowerSeries.C a : JetRing) = 0 := by
  ext k
  have hne : k + Finsupp.single ν 1 ≠ 0 := by
    intro h
    have h' := DFunLike.congr_fun h ν
    rw [Finsupp.add_apply, Finsupp.single_eq_same] at h'
    simp at h'
  rw [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_C, if_neg hne, zero_mul, map_zero]

lemma dMat_map_C (ν : Lor) (M : Matrix (Fin 3) (Fin 3) ℂ) :
    dMat ν (M.map (MvPowerSeries.C : ℂ →+* JetRing)) = 0 :=
  Matrix.ext fun i j => pderiv_C_jet ν (M i j)

lemma jetValue_map_C (M : Matrix (Fin 3) (Fin 3) ℂ) :
    Gluon.jetValue (M.map (MvPowerSeries.C : ℂ →+* JetRing)) = M := by
  refine Matrix.ext fun i j => ?_
  show MvPowerSeries.constantCoeff (MvPowerSeries.C (M i j) : JetRing) = M i j
  simp

@[simp]
lemma jetDeriv_zero (ν : Lor) :
    Gluon.jetDeriv ν (0 : Matrix (Fin 3) (Fin 3) JetRing) = 0 := by
  refine Matrix.ext fun i j => ?_
  show MvPowerSeries.coeff (Finsupp.single ν 1) (0 : JetRing) = 0
  exact map_zero _

lemma ofConstantSU_coe (u : specialUnitaryGroup (Fin 3) ℂ) :
    ((JetGaugeGroupI.ofConstantSU (Fin 3) u : specialUnitaryGroup (Fin 3) JetRing) :
      Matrix (Fin 3) (Fin 3) JetRing) =
      (u : Matrix (Fin 3) (Fin 3) ℂ).map (MvPowerSeries.C : ℂ →+* JetRing) := rfl

lemma mcP_ofConstantSU (u : specialUnitaryGroup (Fin 3) ℂ) (μ : Lor) :
    mcP (JetGaugeGroupI.ofConstantSU (Fin 3) u) μ = 0 := by
  rw [mcP, ofConstantSU_coe, dMat_map_C, Matrix.zero_mul]

lemma mcC_ofConstantSU (u : specialUnitaryGroup (Fin 3) ℂ) (μ : Lor) :
    mcC (JetGaugeGroupI.ofConstantSU (Fin 3) u) μ = 0 :=
  Subtype.ext (SU3Jet.mcCoeff_ofConstantSU u μ)

lemma mc2C_ofConstantSU (u : specialUnitaryGroup (Fin 3) ℂ) (ν μ : Lor) :
    mc2C (JetGaugeGroupI.ofConstantSU (Fin 3) u) ν μ = 0 := by
  apply cmat_injective
  show mc2M _ ν μ = cmat 0
  rw [mc2M, mcP_ofConstantSU, jetDeriv_zero, smul_zero, cmat_zero]

/-!

## J. Jets based to order one

-/

lemma jetValue_eq_one (hU : JetGaugeGroupI.evalSU (Fin 3) U = 1) : Gluon.jetValue U.1 = 1 := by
  rw [← Gluon.evalSU_coe, hU]
  rfl

lemma mcMatrix_eq_zero (hm : ∀ ρ, mcC U ρ = 0) (ν : Lor) : Gluon.mcMatrix ν U.1 = 0 := by
  have h := congrArg cmat (hm ν)
  rwa [cmat_mcC, cmat_zero] at h

lemma jetDeriv_eq_zero (hm : ∀ ρ, mcC U ρ = 0) (ν : Lor) : Gluon.jetDeriv ν U.1 = 0 := by
  rw [jetDeriv_coe, mcMatrix_eq_zero U hm, Matrix.zero_mul, smul_zero]

/-- On a jet based to order one the second Maurer–Cartan coefficient is just the second Taylor
  coefficient of the jet: no lower-order corrections survive. -/
lemma mc2M_of_based_one (hU : JetGaugeGroupI.evalSU (Fin 3) U = 1) (hm : ∀ ρ, mcC U ρ = 0)
    (ν μ : Lor) : mc2M U ν μ = Complex.I • Gluon.jetDeriv ν (dMat μ U.1) := by
  have h1 : Gluon.jetValue U.1 = 1 := jetValue_eq_one U hU
  have h2 : Gluon.jetValue (dMat μ U.1) = 0 := by
    rw [jetValue_dMat]
    exact jetDeriv_eq_zero U hm μ
  rw [mc2M, mcP, Gluon.jetDeriv_mul, Gluon.jetValue_star, h1, star_one, Matrix.mul_one, h2,
    Matrix.zero_mul, add_zero]

lemma jetDeriv_dMat_eq (ν μ : Lor) (M : Matrix (Fin 3) (Fin 3) JetRing) :
    Gluon.jetDeriv ν (dMat μ M) =
      ((((Finsupp.single ν 1 : Lor →₀ ℕ) μ : ℕ) : ℂ) + 1) •
        coeffMat (Finsupp.single ν 1 + Finsupp.single μ 1) M := by
  refine Matrix.ext fun i j => ?_
  show MvPowerSeries.coeff (Finsupp.single ν 1) (MvPowerSeries.pderiv ℂ μ (M i j)) =
    ((((Finsupp.single ν 1 : Lor →₀ ℕ) μ : ℕ) : ℂ) + 1) *
      MvPowerSeries.coeff (Finsupp.single ν 1 + Finsupp.single μ 1) (M i j)
  rw [MvPowerSeries.coeff_pderiv]
  ring

/-!

### J.1. Conjugation by a constant colour rotation

-/

lemma coe_inv_su3 (v : specialUnitaryGroup (Fin 3) ℂ) :
    ((v⁻¹ : specialUnitaryGroup (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) =
      ((v : Matrix (Fin 3) (Fin 3) ℂ))ᴴ := by
  have h1 : ((v : Matrix (Fin 3) (Fin 3) ℂ))ᴴ * (v : Matrix (Fin 3) (Fin 3) ℂ) = 1 := by
    have h := mem_unitaryGroup_iff'.mp (mem_specialUnitaryGroup_iff.mp v.2).1
    rwa [star_eq_conjTranspose] at h
  have h2 : (v : Matrix (Fin 3) (Fin 3) ℂ) *
      ((v⁻¹ : specialUnitaryGroup (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) = 1 := by
    have h : ((v * v⁻¹ : specialUnitaryGroup (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) = 1 := by
      rw [mul_inv_cancel]
      rfl
    rw [← h]
    rfl
  calc ((v⁻¹ : specialUnitaryGroup (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ)
      = 1 * ((v⁻¹ : specialUnitaryGroup (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) := by
        rw [Matrix.one_mul]
    _ = ((v : Matrix (Fin 3) (Fin 3) ℂ))ᴴ * (v : Matrix (Fin 3) (Fin 3) ℂ) *
        ((v⁻¹ : specialUnitaryGroup (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) := by rw [h1]
    _ = ((v : Matrix (Fin 3) (Fin 3) ℂ))ᴴ * ((v : Matrix (Fin 3) (Fin 3) ℂ) *
        ((v⁻¹ : specialUnitaryGroup (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ)) := by
          rw [Matrix.mul_assoc]
    _ = ((v : Matrix (Fin 3) (Fin 3) ℂ))ᴴ := by rw [h2, Matrix.mul_one]

/-- A based gauge jet conjugated by a constant colour rotation. -/
noncomputable def conjBy (v : specialUnitaryGroup (Fin 3) ℂ)
    (V : specialUnitaryGroup (Fin 3) JetRing) : specialUnitaryGroup (Fin 3) JetRing :=
  JetGaugeGroupI.ofConstantSU (Fin 3) v * V * (JetGaugeGroupI.ofConstantSU (Fin 3) v)⁻¹

lemma coe_conjBy (v : specialUnitaryGroup (Fin 3) ℂ) (V : specialUnitaryGroup (Fin 3) JetRing) :
    ((conjBy v V : specialUnitaryGroup (Fin 3) JetRing) : Matrix (Fin 3) (Fin 3) JetRing) =
      (v : Matrix (Fin 3) (Fin 3) ℂ).map (MvPowerSeries.C : ℂ →+* JetRing) * V.1 *
        ((v : Matrix (Fin 3) (Fin 3) ℂ))ᴴ.map (MvPowerSeries.C : ℂ →+* JetRing) := by
  rw [conjBy, show ((JetGaugeGroupI.ofConstantSU (Fin 3) v)⁻¹ :
      specialUnitaryGroup (Fin 3) JetRing) = JetGaugeGroupI.ofConstantSU (Fin 3) v⁻¹ from
    (map_inv _ v).symm, ← coe_inv_su3 v]
  rfl

lemma evalSU_conjBy (v : specialUnitaryGroup (Fin 3) ℂ)
    {V : specialUnitaryGroup (Fin 3) JetRing} (hV : JetGaugeGroupI.evalSU (Fin 3) V = 1) :
    JetGaugeGroupI.evalSU (Fin 3) (conjBy v V) = 1 := by
  rw [conjBy, map_mul, map_mul, map_inv, SU3Jet.evalSU_ofConstantSU, hV, mul_one, mul_inv_cancel]

lemma mcCoeff_conjBy (v : specialUnitaryGroup (Fin 3) ℂ)
    (V : specialUnitaryGroup (Fin 3) JetRing) (ρ : Lor) :
    Gluon.mcCoeff (conjBy v V) ρ = Gluon.adjointAction v (Gluon.mcCoeff V ρ) := by
  have hinv : (JetGaugeGroupI.ofConstantSU (Fin 3) v)⁻¹ =
      JetGaugeGroupI.ofConstantSU (Fin 3) v⁻¹ := (map_inv _ v).symm
  simp only [conjBy, hinv, Gluon.mcCoeff_mul, SU3Jet.mcCoeff_ofConstantSU, zero_add,
    SU3Jet.evalSU_ofConstantSU, map_zero, add_zero]

lemma mcC_conjBy (v : specialUnitaryGroup (Fin 3) ℂ) {V : specialUnitaryGroup (Fin 3) JetRing}
    (hm : ∀ ρ, mcC V ρ = 0) (ρ : Lor) : mcC (conjBy v V) ρ = 0 := by
  apply Subtype.ext
  show Gluon.mcCoeff (conjBy v V) ρ = 0
  rw [mcCoeff_conjBy, show Gluon.mcCoeff V ρ = 0 from congrArg Subtype.val (hm ρ), map_zero]

lemma dMat_conj_const (P R : Matrix (Fin 3) (Fin 3) ℂ) (M : Matrix (Fin 3) (Fin 3) JetRing)
    (μ : Lor) :
    dMat μ (P.map (MvPowerSeries.C : ℂ →+* JetRing) * M *
        R.map (MvPowerSeries.C : ℂ →+* JetRing)) =
      P.map (MvPowerSeries.C : ℂ →+* JetRing) * dMat μ M *
        R.map (MvPowerSeries.C : ℂ →+* JetRing) := by
  rw [dMat_mul, dMat_mul, dMat_map_C, dMat_map_C]
  simp

lemma jetDeriv_conj_const (P R : Matrix (Fin 3) (Fin 3) ℂ) (M : Matrix (Fin 3) (Fin 3) JetRing)
    (ν : Lor) :
    Gluon.jetDeriv ν (P.map (MvPowerSeries.C : ℂ →+* JetRing) * M *
        R.map (MvPowerSeries.C : ℂ →+* JetRing)) = P * Gluon.jetDeriv ν M * R := by
  rw [Gluon.jetDeriv_mul, Gluon.jetDeriv_mul, Gluon.jetDeriv_map_C, Gluon.jetDeriv_map_C,
    jetValue_map_C, jetValue_map_C]
  simp

/-- Conjugating a based gauge jet by a constant colour rotation conjugates its second
  Maurer–Cartan coefficient. -/
lemma mc2C_conjBy (v : specialUnitaryGroup (Fin 3) ℂ) {V : specialUnitaryGroup (Fin 3) JetRing}
    (hV : JetGaugeGroupI.evalSU (Fin 3) V = 1) (hm : ∀ ρ, mcC V ρ = 0) (ν μ : Lor) :
    mc2C (conjBy v V) ν μ = adC v (mc2C V ν μ) := by
  apply cmat_injective
  rw [cmat_adC, cmat_mc2C, cmat_mc2C,
    mc2M_of_based_one _ (evalSU_conjBy v hV) (mcC_conjBy v hm),
    mc2M_of_based_one _ hV hm, coe_conjBy, dMat_conj_const, jetDeriv_conj_const]
  simp only [Matrix.smul_mul, Matrix.mul_smul]

/-!

## K. The order-two diagonal jet

-/

/-- The total degree of a spacetime multi-index. -/
noncomputable def lorDeg (k : Lor →₀ ℕ) : ℕ := ∑ i, k i

lemma lorDeg_add (k l : Lor →₀ ℕ) : lorDeg (k + l) = lorDeg k + lorDeg l := by
  rw [lorDeg, lorDeg, lorDeg, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => rfl

lemma lorDeg_nsmul (n : ℕ) (k : Lor →₀ ℕ) : lorDeg (n • k) = n * lorDeg k := by
  rw [lorDeg, lorDeg, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by simp

lemma lorDeg_single (ν : Lor) : lorDeg (Finsupp.single ν 1) = 1 := by
  classical
  rw [lorDeg]
  simp [Finsupp.single_apply]

lemma single_ne_nsmul_two {ν μ ν₀ μ₀ : Lor}
    (hk : (Finsupp.single ν 1 + Finsupp.single μ 1 : Lor →₀ ℕ) ≠
      Finsupp.single ν₀ 1 + Finsupp.single μ₀ 1) (n : ℕ) :
    (Finsupp.single ν 1 + Finsupp.single μ 1 : Lor →₀ ℕ) ≠
      n • (Finsupp.single ν₀ 1 + Finsupp.single μ₀ 1) := by
  intro h
  have hdeg := congrArg lorDeg h
  rw [lorDeg_add, lorDeg_single, lorDeg_single, lorDeg_nsmul, lorDeg_add, lorDeg_single,
    lorDeg_single] at hdeg
  have hn : n = 1 := by omega
  rw [hn, one_smul] at h
  exact hk h

/-- Two degree-two spacetime exponents agree exactly when the unordered pairs agree. -/
lemma single_add_single_inj {ν μ ν' μ' : Lor}
    (h : (Finsupp.single ν 1 + Finsupp.single μ 1 : Lor →₀ ℕ) =
      Finsupp.single ν' 1 + Finsupp.single μ' 1) : s(ν, μ) = s(ν', μ') := by
  have hm : ({ν, μ} : Multiset Lor) = {ν', μ'} := by
    have hc := congrArg Finsupp.toMultiset h
    simpa [Finsupp.toMultiset_single] using hc
  rcases Multiset.cons_eq_cons.mp hm with ⟨h1, h2⟩ | ⟨_, cs, h2, h3⟩
  · rw [Sym2.eq_iff]
    exact Or.inl ⟨h1, Multiset.singleton_inj.mp h2⟩
  · have hcs : cs = 0 := by
      have hcard := congrArg Multiset.card h2
      simp at hcard
      omega
    subst hcs
    rw [Sym2.eq_iff]
    refine Or.inr ⟨?_, ?_⟩
    · exact (Multiset.singleton_inj.mp (by simpa using h3)).symm
    · exact Multiset.singleton_inj.mp (by simpa using h2)

lemma sym2_eq_iff_exp {ν μ ν₀ μ₀ : Lor} :
    s(ν, μ) = s(ν₀, μ₀) ↔
      (Finsupp.single ν 1 + Finsupp.single μ 1 : Lor →₀ ℕ) =
        Finsupp.single ν₀ 1 + Finsupp.single μ₀ 1 := by
  refine ⟨fun h => ?_, single_add_single_inj⟩
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, add_comm]

/-- The multiplicity factor of a symmetric pair: `2` on the diagonal, `1` off it. -/
noncomputable def dfac (ν μ : Lor) : ℝ := (((Finsupp.single ν 1 : Lor →₀ ℕ) μ : ℕ) : ℝ) + 1

lemma dfac_ne_zero (ν μ : Lor) : dfac ν μ ≠ 0 := by
  have h : (0 : ℝ) < dfac ν μ := by rw [dfac]; positivity
  exact ne_of_gt h

lemma dfac_symm (ν μ : Lor) : dfac ν μ = dfac μ ν := by
  classical
  rw [dfac, dfac, Finsupp.single_apply, Finsupp.single_apply]
  by_cases h : ν = μ
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg fun hc => h hc.symm]

/-- The `DiagonalJet` colour direction `diag(1, -1, 0)` as an element of the colour carrier. -/
noncomputable def colourC : ColourSpace := ⟨colourH, trace_colourMat⟩

@[simp]
lemma cmat_colourC : cmat colourC = colourMat := rfl

/-- **The order-two translation realized by the `DiagonalJet` diagonal jet.** For a degree-two
  spacetime
  exponent the diagonal jet is based to order one, and it translates exactly the symmetric
  derivative coordinates belonging to the unordered pair `{ν₀, μ₀}`. -/
lemma mc2C_diagSU_two (a : ℝ) (ν₀ μ₀ ν μ : Lor) :
    mc2C (diagSU a (Finsupp.single ν₀ 1 + Finsupp.single μ₀ 1) (add_single_ne_zero ν₀ μ₀)) ν μ =
      if s(ν, μ) = s(ν₀, μ₀) then (dfac ν₀ μ₀ * a) • colourC else 0 := by
  classical
  have hbased : JetGaugeGroupI.evalSU (Fin 3)
      (diagSU a (Finsupp.single ν₀ 1 + Finsupp.single μ₀ 1) (add_single_ne_zero ν₀ μ₀)) = 1 :=
    evalSU_diagSU a _ _
  have hm : ∀ ρ, mcC (diagSU a (Finsupp.single ν₀ 1 + Finsupp.single μ₀ 1)
      (add_single_ne_zero ν₀ μ₀)) ρ = 0 := fun ρ => Subtype.ext (mcCoeff_diagSU_two a ν₀ μ₀ ρ)
  apply cmat_injective
  rw [cmat_mc2C, mc2M_of_based_one _ hbased hm, jetDeriv_dMat_eq]
  by_cases hk : s(ν, μ) = s(ν₀, μ₀)
  · have hexp := sym2_eq_iff_exp.mp hk
    have hfac : dfac ν μ = dfac ν₀ μ₀ := by
      rcases Sym2.eq_iff.mp hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2, dfac_symm]
    rw [if_pos hk]
    show _ = ((dfac ν₀ μ₀ * a : ℝ) : ℂ) • colourMat
    rw [show (diagSU a (Finsupp.single ν₀ 1 + Finsupp.single μ₀ 1)
        (add_single_ne_zero ν₀ μ₀) : Matrix (Fin 3) (Fin 3) JetRing) =
        diagMat a (Finsupp.single ν₀ 1 + Finsupp.single μ₀ 1) (add_single_ne_zero ν₀ μ₀) from rfl,
      hexp, coeffMat_diagMat_self, smul_smul, smul_smul, ← hfac, dfac]
    congr 1
    push_cast
    linear_combination (-((((Finsupp.single ν 1 : Lor →₀ ℕ) μ : ℕ) : ℂ) + 1) * (a : ℂ)) *
      Complex.I_mul_I
  · rw [if_neg hk]
    have hexp : (Finsupp.single ν 1 + Finsupp.single μ 1 : Lor →₀ ℕ) ≠
        Finsupp.single ν₀ 1 + Finsupp.single μ₀ 1 := fun hc => hk (single_add_single_inj hc)
    rw [show (diagSU a (Finsupp.single ν₀ 1 + Finsupp.single μ₀ 1)
        (add_single_ne_zero ν₀ μ₀) : Matrix (Fin 3) (Fin 3) JetRing) =
        diagMat a (Finsupp.single ν₀ 1 + Finsupp.single μ₀ 1) (add_single_ne_zero ν₀ μ₀) from rfl,
      coeffMat_diagMat_eq_zero a _ (add_single_ne_zero ν₀ μ₀) (add_single_ne_zero ν μ)
        (single_ne_nsmul_two hexp), smul_zero, smul_zero, cmat_zero]

/-!

## L. Realizability of the two translations

-/

lemma adC_colourC (k : Col) : adC (colourConj k) colourC = colourBasis k :=
  Subtype.ext (colourBasis_eq_adjointAction k)

/-- **Order-two realizability.** For every unordered pair of spacetime directions, every colour
  basis direction and every real number there is a gauge jet, based to order one, which translates
  exactly the corresponding symmetric derivative coordinate. -/
lemma exists_based_two (s : Sym2 Lor) (c₀ : Col) (r : ℝ) :
    ∃ U : specialUnitaryGroup (Fin 3) JetRing,
      JetGaugeGroupI.evalSU (Fin 3) U = 1 ∧ (∀ ρ, mcC U ρ = 0) ∧
        ∀ ν μ, mc2C U ν μ = if s(ν, μ) = s then r • colourBasis c₀ else 0 := by
  classical
  induction s using Sym2.ind with
  | _ ν₀ μ₀ =>
    refine ⟨conjBy (colourConj c₀) (diagSU (r / dfac ν₀ μ₀)
      (Finsupp.single ν₀ 1 + Finsupp.single μ₀ 1) (add_single_ne_zero ν₀ μ₀)), ?_, ?_, ?_⟩
    · exact evalSU_conjBy _ (evalSU_diagSU _ _ _)
    · exact mcC_conjBy _ fun ρ => Subtype.ext (mcCoeff_diagSU_two _ ν₀ μ₀ ρ)
    · intro ν μ
      rw [mc2C_conjBy _ (evalSU_diagSU _ _ _)
        (fun ρ => Subtype.ext (mcCoeff_diagSU_two _ ν₀ μ₀ ρ)), mc2C_diagSU_two]
      by_cases hk : s(ν, μ) = s(ν₀, μ₀)
      · rw [if_pos hk, if_pos hk, map_smul, adC_colourC,
          mul_div_cancel₀ r (dfac_ne_zero ν₀ μ₀)]
      · rw [if_neg hk, if_neg hk, map_zero]

/-!

## M. Faithfulness of the substitution

`gaugeSubst` was written to match `jetValue_actPot` and `jetDeriv_actPot`. This section closes the
loop rather than leaving the match to inspection: for a potential whose base-point value and first
Taylor coefficients are traceless hermitian in every direction — the physical colour carrier —
reading off the coordinates and then substituting is the same as acting and then reading off the
coordinates.

-/

/-- A potential is a *colour potential* when its base-point value and its first Taylor coefficients
  are traceless hermitian in every spacetime direction. -/
structure IsColourPot (A : Potential) : Prop where
  /-- The base-point value is hermitian. -/
  star_val : ∀ μ, star (Gluon.jetValue (A μ)) = Gluon.jetValue (A μ)
  /-- The base-point value is traceless. -/
  trace_val : ∀ μ, trace (Gluon.jetValue (A μ)) = 0
  /-- The first Taylor coefficients are hermitian. -/
  star_der : ∀ ν μ, star (Gluon.jetDeriv ν (A μ)) = Gluon.jetDeriv ν (A μ)
  /-- The first Taylor coefficients are traceless. -/
  trace_der : ∀ ν μ, trace (Gluon.jetDeriv ν (A μ)) = 0

/-- The point of the coordinate space described by a colour potential. -/
noncomputable def potCoord {A : Potential} (h : IsColourPot A) : Coord → ℝ
  | Coord.conn μ c => coordC c (mkCM (Gluon.jetValue (A μ)) (h.star_val μ) (h.trace_val μ))
  | Coord.der ν μ c =>
      coordC c (mkCM (Gluon.jetDeriv ν (A μ)) (h.star_der ν μ) (h.trace_der ν μ))

lemma cfgA_potCoord {A : Potential} (h : IsColourPot A) (μ : Lor) :
    cfgA (potCoord h) μ = mkCM (Gluon.jetValue (A μ)) (h.star_val μ) (h.trace_val μ) :=
  mkC_coordC _

lemma cfgD_potCoord {A : Potential} (h : IsColourPot A) (ν μ : Lor) :
    cfgD (potCoord h) ν μ = mkCM (Gluon.jetDeriv ν (A μ)) (h.star_der ν μ) (h.trace_der ν μ) :=
  mkC_coordC _

private lemma star_conj_u (u : specialUnitaryGroup (Fin 3) ℂ) {M : Matrix (Fin 3) (Fin 3) ℂ}
    (hM : star M = M) :
    star ((u : Matrix (Fin 3) (Fin 3) ℂ) * M * ((u : Matrix (Fin 3) (Fin 3) ℂ))ᴴ) =
      (u : Matrix (Fin 3) (Fin 3) ℂ) * M * ((u : Matrix (Fin 3) (Fin 3) ℂ))ᴴ := by
  have h1 : star ((u : Matrix (Fin 3) (Fin 3) ℂ))ᴴ = (u : Matrix (Fin 3) (Fin 3) ℂ) := by
    rw [star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  have h2 : star (u : Matrix (Fin 3) (Fin 3) ℂ) = ((u : Matrix (Fin 3) (Fin 3) ℂ))ᴴ :=
    star_eq_conjTranspose _
  rw [star_mul, star_mul, h1, h2, hM, Matrix.mul_assoc]

private lemma trace_conj_u (u : specialUnitaryGroup (Fin 3) ℂ) (M : Matrix (Fin 3) (Fin 3) ℂ) :
    trace ((u : Matrix (Fin 3) (Fin 3) ℂ) * M * ((u : Matrix (Fin 3) (Fin 3) ℂ))ᴴ) = trace M := by
  have hu : ((u : Matrix (Fin 3) (Fin 3) ℂ))ᴴ * (u : Matrix (Fin 3) (Fin 3) ℂ) = 1 := by
    have h := mem_unitaryGroup_iff'.mp (mem_specialUnitaryGroup_iff.mp u.2).1
    rwa [star_eq_conjTranspose] at h
  rw [trace_mul_cycle, hu, Matrix.one_mul]

lemma jetValue_coe_eq (U : specialUnitaryGroup (Fin 3) JetRing) :
    Gluon.jetValue U.1 =
      ((JetGaugeGroupI.evalSU (Fin 3) U : specialUnitaryGroup (Fin 3) ℂ) :
        Matrix (Fin 3) (Fin 3) ℂ) := (Gluon.evalSU_coe U).symm

/-- The local gauge action preserves the physical colour carrier: this is where tracelessness of
  the Maurer–Cartan series is used. -/
lemma isColourPot_actPot {A : Potential} (h : IsColourPot A)
    (U : specialUnitaryGroup (Fin 3) JetRing) : IsColourPot (actPot U A) := by
  set u := JetGaugeGroupI.evalSU (Fin 3) U with hu
  have hcoe : Gluon.jetValue U.1 = ((u : specialUnitaryGroup (Fin 3) ℂ) :
      Matrix (Fin 3) (Fin 3) ℂ) := jetValue_coe_eq U
  have hstar : star ((u : specialUnitaryGroup (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) =
      ((u : specialUnitaryGroup (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ)ᴴ :=
    star_eq_conjTranspose _
  have hm : ∀ ν, star (Gluon.mcMatrix ν U.1) = Gluon.mcMatrix ν U.1 := fun ν =>
    selfAdjoint.mem_iff.mp (Gluon.mcMatrix_mem_selfAdjoint (Gluon.coe_mul_star_self U) ν)
  have hmt : ∀ ν, trace (Gluon.mcMatrix ν U.1) = 0 := fun ν => (mcC U ν).2
  refine ⟨fun μ => ?_, fun μ => ?_, fun ν μ => ?_, fun ν μ => ?_⟩
  · rw [jetValue_actPot, star_add, hm, hcoe, hstar, star_conj_u u (h.star_val μ)]
  · rw [jetValue_actPot, trace_add, hcoe, hstar, trace_conj_u, h.trace_val, hmt, add_zero]
  · rw [jetDeriv_actPot, star_add, star_sub, star_mc2M, hcoe, hstar,
      star_conj_u u (h.star_der ν μ), brMat_star (hm ν) (star_conj_u u (h.star_val μ))]
  · rw [jetDeriv_actPot, trace_add, trace_sub, trace_mc2M, hcoe, hstar, trace_conj_u,
      h.trace_der, brMat_trace, sub_zero, add_zero]

/-- **The substitution really is the coordinate form of the action.** Acting on a colour potential
  and then reading off its coordinates is the same as reading off its coordinates and then applying
  the transformed-point map that `gaugeSubst` evaluates to. -/
lemma potCoord_actPot {A : Potential} (h : IsColourPot A)
    (U : specialUnitaryGroup (Fin 3) JetRing) :
    potCoord (isColourPot_actPot h U) = actPt U (potCoord h) := by
  have hcoe : Gluon.jetValue U.1 =
      ((JetGaugeGroupI.evalSU (Fin 3) U : specialUnitaryGroup (Fin 3) ℂ) :
        Matrix (Fin 3) (Fin 3) ℂ) := jetValue_coe_eq U
  have hstar : star ((JetGaugeGroupI.evalSU (Fin 3) U : specialUnitaryGroup (Fin 3) ℂ) :
        Matrix (Fin 3) (Fin 3) ℂ) =
      ((JetGaugeGroupI.evalSU (Fin 3) U : specialUnitaryGroup (Fin 3) ℂ) :
        Matrix (Fin 3) (Fin 3) ℂ)ᴴ := star_eq_conjTranspose _
  funext i
  cases i with
  | conn μ c =>
      show coordC c (mkCM (Gluon.jetValue (actPot U A μ)) _ _) = coordC c (actA U (potCoord h) μ)
      congr 1
      apply cmat_injective
      rw [cmat_mkCM, jetValue_actPot, actA, cmat_add, cmat_adC, cfgA_potCoord, cmat_mkCM,
        cmat_mcC, hcoe, hstar]
  | der ν μ c =>
      show coordC c (mkCM (Gluon.jetDeriv ν (actPot U A μ)) _ _) =
        coordC c (actD U (potCoord h) ν μ)
      congr 1
      apply cmat_injective
      rw [cmat_mkCM, jetDeriv_actPot, actD, cmat_add, cmat_sub, cmat_adC, cmat_br, cmat_adC,
        cfgD_potCoord, cfgA_potCoord, cmat_mkCM, cmat_mkCM, cmat_mcC, cmat_mc2C, hcoe, hstar]

end SU3Jet

end StandardModel
