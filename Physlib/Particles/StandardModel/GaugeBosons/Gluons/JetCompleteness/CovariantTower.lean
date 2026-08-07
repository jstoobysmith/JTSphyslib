/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.Particles.StandardModel.GaugeBosons.Gluons.JetCompleteness.OrdinaryJets
/-!
# The covariant curvature tower and its residual action

## i. Overview

This file builds, **inside** `OrdinaryJets`'s ordinary jet algebra, the field strength, the
covariant derivative and
the genuinely symmetrized covariant derivatives `D^r F` at arbitrary order, and proves that the
whole tower transforms under a jet gauge transformation only through the base-point value of the
jet.  The covariant tower consists of honest elements of the ordinary algebra: it satisfies
antisymmetry, Bianchi and commutator relations, and no new carrier variables are introduced.

## ii. Conventions

The `HookBianchi` hermitian conventions, unchanged:

```text
br(M,N)  = i (M N - N M)
F_νμ     = ∂_ν A_μ - ∂_μ A_ν + br(A_ν, A_μ)
D_ρ X    = ∂_ρ X + br(A_ρ, X).
```

## iii. Method

The covariance proof runs through a *series* evaluation dictionary rather than through a
generator-by-generator commutation rule for `gaugePull` and `jetDeriv` (which is not clean, because
the substitution freezes the Taylor coefficients of the gauge jet at the base point).  Concretely:

* `evalS A : JetAlgebra →ₐ[ℝ] MvPowerSeries Lor ℝ` substitutes a colour potential and its
  derivatives *at a varying point*, and intertwines `jetDeriv` with `MvPowerSeries.pderiv`;
* `cser` turns a colour vector of real series into a matrix of jets, intertwining `brR` with the
  matrix bracket;
* at the level of matrices of jets the covariance of `F` and of `D_ρ` is the classical
  computation, whose only nontrivial input is the Maurer–Cartan structure equation
  `∂_ν m_μ - ∂_μ m_ν = m_ν m_μ - m_μ m_ν` (`dMat_mcP_sub`, from `GaugeAction`'s `dMat_mcP`);
* taking base-point values turns conjugation by the series `U` into `Ad` by `evalSU U`.

## iv. Symmetrization

`covIter t` is the *ordered* iterated covariant derivative along a tuple `t : Fin r → Lor`.
Covariant derivatives do **not** commute, so the published tower is the genuine symmetrization

```text
covCurv t ν μ = (r !)⁻¹ • ∑_{σ : Equiv.Perm (Fin r)} covIter (t ∘ σ) (curvVec ν μ),
```

and `covCurv_perm` proves it is unchanged by any permutation of the derivative slots.  No claim is
made that the unsymmetrized `covIter` depends only on the multiset of directions.

## v. Results

* `evalS`, `evalS_jetDeriv`, `constantCoeff_evalS` — the series evaluation dictionary;
* `curvVec`, `covD`, `covIter`, `covCurv`, `covCurv_perm` — the covariant tower;
* `gaugePull_covCurv` — the arbitrary-order covariance theorem;
* `covAlgebra`, `gaugePull_covAlgebra_le`, `gaugePull_eq_self_of_based`,
  `gaugePull_eq_of_evalSU_eq`, `gaugePull_eq_ofConstantSU` — the generated subalgebra results.

-/

@[expose] public section

namespace StandardModel

open Matrix Module MvPolynomial

namespace SU3Jet

/-!

## A. The series evaluation dictionary

Substituting a colour potential into a jet polynomial gives a *function of spacetime*, i.e. a
formal power series with real coefficients.  Under this substitution the formal total derivative
of `OrdinaryJets` becomes the formal partial derivative of the power series.

-/

/-- Real formal power series in the spacetime coordinates: the values of jet polynomials on a
  fixed field configuration. -/
abbrev RSeries : Type := MvPowerSeries Lor ℝ

/-- A real series with prescribed Taylor coefficients. -/
def mkRSeries (f : DIdx → ℝ) : RSeries := f

@[simp]
lemma coeff_mkRSeries (f : DIdx → ℝ) (k : DIdx) :
    MvPowerSeries.coeff k (mkRSeries f) = f k := rfl

/-- The colour component of the `s`-th ordinary derivative of a colour potential, as a function of
  the spacetime point.  Its `k`-th Taylor coefficient is `(k+s)!/k!` times the `(k+s)`-th
  coefficient of the potential. -/
noncomputable def sCoordS (A : ColourPot) (s : DIdx) (μ : Lor) (c : Col) : RSeries :=
  mkRSeries fun k => facI (k + s) / facI k * coordC c (A.coeffC (k + s) μ)

lemma constantCoeff_sCoordS (A : ColourPot) (s : DIdx) (μ : Lor) (c : Col) :
    MvPowerSeries.constantCoeff (sCoordS A s μ c) = potPt A (JetGenerators.dA s μ c) := by
  show facI (0 + s) / facI 0 * coordC c (A.coeffC (0 + s) μ) = _
  rw [zero_add, facI_zero, div_one]
  rfl

/-- **The derivative rule for the series dictionary.**  Differentiating the component function of
  `∂_s A_μ` gives the component function of `∂_{s+ρ} A_μ`. -/
lemma pderiv_sCoordS (A : ColourPot) (s : DIdx) (μ : Lor) (c : Col) (ρ : Lor) :
    MvPowerSeries.pderiv ℝ ρ (sCoordS A s μ c) = sCoordS A (s + Finsupp.single ρ 1) μ c := by
  refine MvPowerSeries.ext fun k => ?_
  have hidx : k + Finsupp.single ρ 1 + s = k + (s + Finsupp.single ρ 1) := by
    rw [add_assoc, add_comm (Finsupp.single ρ 1) s]
  have hk : facI k ≠ 0 := facI_ne_zero k
  have hr : ((k ρ : ℝ) + 1) ≠ 0 := by positivity
  rw [MvPowerSeries.coeff_pderiv, sCoordS, sCoordS, coeff_mkRSeries, coeff_mkRSeries, hidx,
    facI_add_single]
  field_simp

/-- The series dictionary on the ordinary generators. -/
noncomputable def sCoordGen (A : ColourPot) : JetGenerators → RSeries
  | .dA s μ c => sCoordS A s μ c

@[simp]
lemma sCoordGen_dA (A : ColourPot) (s : DIdx) (μ : Lor) (c : Col) :
    sCoordGen A (JetGenerators.dA s μ c) = sCoordS A s μ c := rfl

/-- **Evaluation of a jet polynomial on a colour potential**, as a function of the spacetime
  point. -/
noncomputable def evalS (A : ColourPot) : JetAlgebra →ₐ[ℝ] RSeries :=
  (MvPolynomial.aeval (sCoordGen A)).comp toPoly.toAlgHom

@[simp]
lemma evalS_ofGen (A : ColourPot) (g : JetGenerators) : evalS A (ofGen g) = sCoordGen A g := by
  show MvPolynomial.aeval (sCoordGen A) (toPoly (ofGen g)) = _
  rw [toPoly_ofGen, aeval_X]

private lemma aeval_polyDeriv (A : ColourPot) (ρ : Lor) (p : MvPolynomial JetGenerators ℝ) :
    MvPolynomial.aeval (sCoordGen A) (polyDeriv ρ p) =
      MvPowerSeries.pderiv ℝ ρ (MvPolynomial.aeval (sCoordGen A) p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      rw [← algebraMap_eq, Derivation.map_algebraMap, map_zero, AlgHom.commutes,
        Derivation.map_algebraMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p g hp =>
      cases g with
      | dA s μ c =>
        simp only [Derivation.leibniz, polyDeriv_X, smul_eq_mul, map_add, map_mul, aeval_X,
          JetGenerators.shift_dA, sCoordGen_dA, hp, pderiv_sCoordS]

/-- **The total derivative is the spacetime derivative of the substituted function.** -/
lemma evalS_jetDeriv (A : ColourPot) (ρ : Lor) (P : JetAlgebra) :
    evalS A (jetDeriv ρ P) = MvPowerSeries.pderiv ℝ ρ (evalS A P) := by
  show MvPolynomial.aeval (sCoordGen A) (toPoly (jetDeriv ρ P)) = _
  rw [toPoly_jetDeriv, aeval_polyDeriv]
  rfl

/-- The base-point value of a real series, as an algebra map. -/
noncomputable def constCoeffHom : RSeries →ₐ[ℝ] ℝ :=
  { (MvPowerSeries.constantCoeff : RSeries →+* ℝ) with
    commutes' := fun r => by
      show MvPowerSeries.constantCoeff (algebraMap ℝ RSeries r) = r
      simp [MvPowerSeries.algebraMap_apply] }

/-- Reading off the base-point value of a substituted jet polynomial is evaluating it at the
  coordinate point of the potential. -/
lemma constantCoeff_evalS (A : ColourPot) (P : JetAlgebra) :
    MvPowerSeries.constantCoeff (evalS A P) = evalA (potPt A) P := by
  have h : constCoeffHom.comp (evalS A) = evalA (potPt A) :=
    jetAlgHom_ext fun g => by
      cases g with
      | dA s μ c =>
        rw [AlgHom.comp_apply, evalS_ofGen, evalA_ofGen]
        exact constantCoeff_sCoordS A s μ c
  exact DFunLike.congr_fun h P

/-!

## B. Colour vectors of series as matrices of jets

-/

lemma jetMat_ext {M N : Matrix (Fin 3) (Fin 3) JetRing} (h : ∀ k, coeffMat k M = coeffMat k N) :
    M = N := by
  refine Matrix.ext fun i j => MvPowerSeries.ext fun k => ?_
  exact congrFun (congrFun (h k) i) j

lemma coeffMat_mul (k : DIdx) (M N : Matrix (Fin 3) (Fin 3) JetRing) :
    coeffMat k (M * N) = ∑ p ∈ Finset.antidiagonal k, coeffMat p.1 M * coeffMat p.2 N := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.sum_apply]
  show MvPowerSeries.coeff k (∑ l, M i l * N l j) =
    ∑ p ∈ Finset.antidiagonal k, ∑ l, coeffMat p.1 M i l * coeffMat p.2 N l j
  rw [map_sum, Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => MvPowerSeries.coeff_mul _ _ _

lemma coeffMat_sub (k : DIdx) (M N : Matrix (Fin 3) (Fin 3) JetRing) :
    coeffMat k (M - N) = coeffMat k M - coeffMat k N :=
  Matrix.ext fun i j => by
    show MvPowerSeries.coeff k (M i j - N i j) = _
    rw [map_sub]
    rfl

lemma coeffMat_dMat (k : DIdx) (ρ : Lor) (M : Matrix (Fin 3) (Fin 3) JetRing) :
    coeffMat k (dMat ρ M) = ((k ρ : ℂ) + 1) • coeffMat (k + Finsupp.single ρ 1) M := by
  refine Matrix.ext fun i j => ?_
  show MvPowerSeries.coeff k (MvPowerSeries.pderiv ℂ ρ (M i j)) =
    ((k ρ : ℂ) + 1) * MvPowerSeries.coeff (k + Finsupp.single ρ 1) (M i j)
  rw [MvPowerSeries.coeff_pderiv]
  ring

/-- The hermitian colour bracket on matrices of jets. -/
noncomputable def brJ (M N : Matrix (Fin 3) (Fin 3) JetRing) : Matrix (Fin 3) (Fin 3) JetRing :=
  (MvPowerSeries.C Complex.I : JetRing) • (M * N - N * M)

lemma coeffMat_brJ (k : DIdx) (M N : Matrix (Fin 3) (Fin 3) JetRing) :
    coeffMat k (brJ M N) =
      ∑ p ∈ Finset.antidiagonal k, brMat (coeffMat p.1 M) (coeffMat p.2 N) := by
  have hsm : ∀ (X : Matrix (Fin 3) (Fin 3) JetRing),
      coeffMat k ((MvPowerSeries.C Complex.I : JetRing) • X) = Complex.I • coeffMat k X := by
    intro X
    refine Matrix.ext fun i j => ?_
    show MvPowerSeries.coeff k ((MvPowerSeries.C Complex.I : JetRing) * X i j) =
      Complex.I * MvPowerSeries.coeff k (X i j)
    rw [MvPowerSeries.coeff_C_mul]
  rw [brJ, hsm, coeffMat_sub, coeffMat_mul, coeffMat_mul,
    Finsupp.sum_antidiagonal_swap k fun a b => coeffMat a N * coeffMat b M,
    ← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [brMat, smul_sub]

/-- A colour vector of real series, as a matrix of jets. -/
noncomputable def cser (f : Col → RSeries) : Matrix (Fin 3) (Fin 3) JetRing :=
  Matrix.of fun i j => ∑ c, MvPowerSeries.map (algebraMap ℝ ℂ) (f c) *
    (MvPowerSeries.C (cmat (colourBasis c) i j) : JetRing)

lemma coeffMat_cser (k : DIdx) (f : Col → RSeries) :
    coeffMat k (cser f) = cmat (mkC fun c => MvPowerSeries.coeff k (f c)) := by
  refine Matrix.ext fun i j => ?_
  rw [mkC_eq_sum, cmat_sum]
  show MvPowerSeries.coeff k (∑ c, MvPowerSeries.map (algebraMap ℝ ℂ) (f c) *
      (MvPowerSeries.C (cmat (colourBasis c) i j) : JetRing)) = _
  rw [map_sum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [MvPowerSeries.coeff_mul_C, MvPowerSeries.coeff_map]
  rfl

lemma cser_injective : Function.Injective cser := by
  intro f g h
  funext c
  refine MvPowerSeries.ext fun k => ?_
  have hk : cmat (mkC fun c => MvPowerSeries.coeff k (f c)) =
      cmat (mkC fun c => MvPowerSeries.coeff k (g c)) := by
    rw [← coeffMat_cser, ← coeffMat_cser, h]
  have := congrArg (coordC c) (cmat_injective hk)
  rwa [coordC_mkC, coordC_mkC] at this

lemma mkC_add (f g : Col → ℝ) : mkC (fun c => f c + g c) = mkC f + mkC g := by
  rw [mkC, mkC, mkC, ← map_add]
  rfl

lemma mkC_sub (f g : Col → ℝ) : mkC (fun c => f c - g c) = mkC f - mkC g := by
  rw [mkC, mkC, mkC, ← map_sub]
  rfl

lemma cser_add (f g : Col → RSeries) : cser (f + g) = cser f + cser g := by
  refine jetMat_ext fun k => ?_
  rw [coeffMat_add, coeffMat_cser, coeffMat_cser, coeffMat_cser,
    show (fun c => MvPowerSeries.coeff k ((f + g) c)) =
      (fun c => MvPowerSeries.coeff k (f c) + MvPowerSeries.coeff k (g c)) from
        funext fun c => map_add _ _ _, mkC_add, cmat_add]

lemma cser_sub (f g : Col → RSeries) : cser (f - g) = cser f - cser g := by
  refine jetMat_ext fun k => ?_
  rw [coeffMat_sub, coeffMat_cser, coeffMat_cser, coeffMat_cser,
    show (fun c => MvPowerSeries.coeff k ((f - g) c)) =
      (fun c => MvPowerSeries.coeff k (f c) - MvPowerSeries.coeff k (g c)) from
        funext fun c => map_sub _ _ _, mkC_sub, cmat_sub]

/-- The matrix dictionary intertwines the spacetime derivative with the entrywise derivative. -/
lemma dMat_cser (ρ : Lor) (f : Col → RSeries) :
    dMat ρ (cser f) = cser fun c => MvPowerSeries.pderiv ℝ ρ (f c) := by
  refine jetMat_ext fun k => ?_
  rw [coeffMat_dMat, coeffMat_cser, coeffMat_cser]
  refine Matrix.ext fun i j => ?_
  rw [Matrix.smul_apply, mkC_eq_sum, mkC_eq_sum, cmat_sum, cmat_sum, Matrix.sum_apply,
    Matrix.sum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [cmat_smul, cmat_smul, Matrix.smul_apply, Matrix.smul_apply, MvPowerSeries.coeff_pderiv]
  show ((k ρ : ℂ) + 1) * ((MvPowerSeries.coeff (k + Finsupp.single ρ 1) (f c) : ℝ) *
      cmat (colourBasis c) i j) =
    ((MvPowerSeries.coeff (k + Finsupp.single ρ 1) (f c) * ((k ρ : ℝ) + 1) : ℝ) *
      cmat (colourBasis c) i j)
  push_cast
  ring

/-- The matrix dictionary intertwines the polynomial colour bracket with the matrix bracket. -/
lemma brJ_cser (f g : Col → RSeries) : brJ (cser f) (cser g) = cser (brR f g) := by
  refine jetMat_ext fun k => ?_
  have hL : ∀ p : DIdx × DIdx, brMat (coeffMat p.1 (cser f)) (coeffMat p.2 (cser g)) =
      cmat (br (mkC fun c => MvPowerSeries.coeff p.1 (f c))
        (mkC fun c => MvPowerSeries.coeff p.2 (g c))) := fun p => by
    rw [cmat_br, coeffMat_cser, coeffMat_cser]
  have hbr : ∀ p : DIdx × DIdx, ∀ c : Col,
      coordC c (br (mkC fun a => MvPowerSeries.coeff p.1 (f a))
        (mkC fun b => MvPowerSeries.coeff p.2 (g b))) =
      ∑ a, ∑ b, MvPowerSeries.coeff p.1 (f a) * MvPowerSeries.coeff p.2 (g b) *
        cstruct a b c := fun p c => by
    rw [coordC_br]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
      rw [coordC_mkC, coordC_mkC]
  rw [coeffMat_brJ, coeffMat_cser,
    Finset.sum_congr rfl fun p (_ : p ∈ Finset.antidiagonal k) => hL p, ← cmat_sum]
  congr 1
  rw [← mkC_coordC (∑ p ∈ Finset.antidiagonal k,
    br (mkC fun c => MvPowerSeries.coeff p.1 (f c)) (mkC fun c => MvPowerSeries.coeff p.2 (g c)))]
  congr 1
  funext c
  have hLHS : coordC c (∑ p ∈ Finset.antidiagonal k,
      br (mkC fun a => MvPowerSeries.coeff p.1 (f a))
        (mkC fun b => MvPowerSeries.coeff p.2 (g b))) =
      ∑ a, ∑ b, ∑ p ∈ Finset.antidiagonal k,
        MvPowerSeries.coeff p.1 (f a) * MvPowerSeries.coeff p.2 (g b) * cstruct a b c := by
    rw [map_sum, Finset.sum_congr rfl fun p (_ : p ∈ Finset.antidiagonal k) => hbr p c,
      Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
  have hRHS : MvPowerSeries.coeff k (brR f g c) =
      ∑ a, ∑ b, ∑ p ∈ Finset.antidiagonal k,
        MvPowerSeries.coeff p.1 (f a) * MvPowerSeries.coeff p.2 (g b) * cstruct a b c := by
    rw [brR, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    show MvPowerSeries.coeff k ((MvPowerSeries.C (cstruct a b c) : RSeries) * (f a * g b)) = _
    rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hLHS, hRHS]

lemma jetValue_cser (f : Col → RSeries) :
    Gluon.jetValue (cser f) = cmat (mkC fun c => MvPowerSeries.constantCoeff (f c)) := by
  rw [← coeffMat_zero_eq_jetValue, coeffMat_cser]
  rfl

/-!

## C. Covariance at the level of matrices of jets

At series level the field strength and the covariant derivative obey the classical covariance laws.
The only nontrivial input is the Maurer–Cartan structure equation.

-/

lemma dMat_add (ν : Lor) (M N : Matrix (Fin 3) (Fin 3) JetRing) :
    dMat ν (M + N) = dMat ν M + dMat ν N :=
  Matrix.ext fun i j => by
    show MvPowerSeries.pderiv ℂ ν (M i j + N i j) = _
    rw [map_add]
    rfl

lemma dMat_smul_CI (ν : Lor) (M : Matrix (Fin 3) (Fin 3) JetRing) :
    dMat ν ((MvPowerSeries.C Complex.I : JetRing) • M) =
      (MvPowerSeries.C Complex.I : JetRing) • dMat ν M :=
  Matrix.ext fun i j => by
    show MvPowerSeries.pderiv ℂ ν ((MvPowerSeries.C Complex.I : JetRing) * M i j) =
      (MvPowerSeries.C Complex.I : JetRing) * MvPowerSeries.pderiv ℂ ν (M i j)
    rw [Derivation.leibniz, pderiv_C_jet, smul_zero, add_zero, smul_eq_mul]

/-- The derivative of the gauge jet is the Maurer–Cartan series times the jet. -/
lemma dMat_coe (U : specialUnitaryGroup (Fin 3) JetRing) (ρ : Lor) :
    dMat ρ U.1 = mcP U ρ * U.1 := by
  rw [mcP, Matrix.mul_assoc, coe_star_mul_self, Matrix.mul_one]

/-- The derivative of a conjugate. -/
lemma dMat_conj (U : specialUnitaryGroup (Fin 3) JetRing) (ρ : Lor)
    (M : Matrix (Fin 3) (Fin 3) JetRing) :
    dMat ρ (U.1 * M * star U.1) =
      mcP U ρ * (U.1 * M * star U.1) + U.1 * dMat ρ M * star U.1 -
        (U.1 * M * star U.1) * mcP U ρ := by
  rw [dMat_mul, dMat_mul, dMat_coe, dMat_star_coe]
  noncomm_ring

lemma brJ_swap (M N : Matrix (Fin 3) (Fin 3) JetRing) : brJ M N = -brJ N M := by
  rw [brJ, brJ, ← smul_neg, neg_sub]

lemma brJ_add_left (M M' N : Matrix (Fin 3) (Fin 3) JetRing) :
    brJ (M + M') N = brJ M N + brJ M' N := by
  rw [brJ, brJ, brJ, ← smul_add]
  congr 1
  noncomm_ring

lemma brJ_add_right (M N N' : Matrix (Fin 3) (Fin 3) JetRing) :
    brJ M (N + N') = brJ M N + brJ M N' := by
  rw [brJ, brJ, brJ, ← smul_add]
  congr 1
  noncomm_ring

private lemma smul_CI_CI (X : Matrix (Fin 3) (Fin 3) JetRing) :
    (MvPowerSeries.C Complex.I : JetRing) • ((MvPowerSeries.C Complex.I : JetRing) • X) = -X := by
  rw [smul_smul, ← map_mul, Complex.I_mul_I, map_neg, map_one, neg_smul, one_smul]

/-- The bracket of two conjugates is the conjugate of the bracket. -/
lemma brJ_conj (U : specialUnitaryGroup (Fin 3) JetRing)
    (M N : Matrix (Fin 3) (Fin 3) JetRing) :
    brJ (U.1 * M * star U.1) (U.1 * N * star U.1) = U.1 * brJ M N * star U.1 := by
  have key : ∀ P Q : Matrix (Fin 3) (Fin 3) JetRing,
      U.1 * P * star U.1 * (U.1 * Q * star U.1) = U.1 * (P * Q) * star U.1 := by
    intro P Q
    calc U.1 * P * star U.1 * (U.1 * Q * star U.1)
        = U.1 * P * (star U.1 * U.1) * Q * star U.1 := by noncomm_ring
      _ = U.1 * (P * Q) * star U.1 := by rw [coe_star_mul_self]; noncomm_ring
  rw [brJ, brJ, key, key, ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.mul_smul, Matrix.smul_mul]

/-- The bracket with the hermitian Maurer–Cartan series, on the left. -/
lemma brJ_mcH_left (U : specialUnitaryGroup (Fin 3) JetRing) (ρ : Lor)
    (M : Matrix (Fin 3) (Fin 3) JetRing) :
    brJ (mcH U ρ) M = -(mcP U ρ * M - M * mcP U ρ) := by
  rw [brJ, mcH, Matrix.smul_mul, Matrix.mul_smul, ← smul_sub, smul_CI_CI]

/-- The bracket with the hermitian Maurer–Cartan series, on the right. -/
lemma brJ_mcH_right (U : specialUnitaryGroup (Fin 3) JetRing) (ρ : Lor)
    (M : Matrix (Fin 3) (Fin 3) JetRing) :
    brJ M (mcH U ρ) = mcP U ρ * M - M * mcP U ρ := by
  rw [brJ_swap, brJ_mcH_left, neg_neg]

lemma brJ_mcH_mcH (U : specialUnitaryGroup (Fin 3) JetRing) (ν μ : Lor) :
    brJ (mcH U ν) (mcH U μ) =
      -((MvPowerSeries.C Complex.I : JetRing) • (mcP U ν * mcP U μ) -
        (MvPowerSeries.C Complex.I : JetRing) • (mcP U μ * mcP U ν)) := by
  rw [brJ_mcH_left, mcH, Matrix.mul_smul, Matrix.smul_mul]

/-- **The Maurer–Cartan structure equation.** -/
lemma dMat_mcP_sub (U : specialUnitaryGroup (Fin 3) JetRing) (ν μ : Lor) :
    dMat ν (mcP U μ) - dMat μ (mcP U ν) = mcP U ν * mcP U μ - mcP U μ * mcP U ν := by
  rw [dMat_mcP, dMat_mcP, dMat_comm ν μ U.1]
  abel

/-- **The field strength** of a colour potential, as a matrix of jets. -/
noncomputable def curvJ (A : ColourPot) (ν μ : Lor) : Matrix (Fin 3) (Fin 3) JetRing :=
  dMat ν (A.pot μ) - dMat μ (A.pot ν) + brJ (A.pot ν) (A.pot μ)

/-- **The covariant derivative** on matrices of jets. -/
noncomputable def covDJ (A : ColourPot) (ρ : Lor) (M : Matrix (Fin 3) (Fin 3) JetRing) :
    Matrix (Fin 3) (Fin 3) JetRing := dMat ρ M + brJ (A.pot ρ) M

/-- **Covariance of the covariant derivative** at series level. -/
lemma covDJ_conj (U : specialUnitaryGroup (Fin 3) JetRing) (A : ColourPot) (ρ : Lor)
    (M : Matrix (Fin 3) (Fin 3) JetRing) :
    covDJ (actPotC U A) ρ (U.1 * M * star U.1) = U.1 * covDJ A ρ M * star U.1 := by
  rw [covDJ, covDJ, actPotC_pot, actPot, dMat_conj, brJ_add_left, brJ_conj, brJ_mcH_left,
    Matrix.mul_add, Matrix.add_mul]
  abel

/-- **Covariance of the field strength** at series level. -/
lemma curvJ_actPotC (U : specialUnitaryGroup (Fin 3) JetRing) (A : ColourPot) (ν μ : Lor) :
    curvJ (actPotC U A) ν μ = U.1 * curvJ A ν μ * star U.1 := by
  have h1 : ∀ σ τ : Lor, dMat σ (actPot U A.pot τ) =
      mcP U σ * (U.1 * A.pot τ * star U.1) + U.1 * dMat σ (A.pot τ) * star U.1 -
        (U.1 * A.pot τ * star U.1) * mcP U σ +
        ((MvPowerSeries.C Complex.I : JetRing) • (dMat σ (dMat τ U.1) * star U.1) -
          (MvPowerSeries.C Complex.I : JetRing) • (mcP U τ * mcP U σ)) := by
    intro σ τ
    rw [actPot, dMat_add, dMat_conj, mcH, dMat_smul_CI, dMat_mcP, smul_sub]
  have h2 : brJ (actPot U A.pot ν) (actPot U A.pot μ) =
      U.1 * brJ (A.pot ν) (A.pot μ) * star U.1 +
        (mcP U μ * (U.1 * A.pot ν * star U.1) - (U.1 * A.pot ν * star U.1) * mcP U μ) -
        (mcP U ν * (U.1 * A.pot μ * star U.1) - (U.1 * A.pot μ * star U.1) * mcP U ν) -
        ((MvPowerSeries.C Complex.I : JetRing) • (mcP U ν * mcP U μ) -
          (MvPowerSeries.C Complex.I : JetRing) • (mcP U μ * mcP U ν)) := by
    rw [actPot, actPot, brJ_add_left, brJ_add_right, brJ_add_right, brJ_conj, brJ_mcH_left,
      brJ_mcH_right, brJ_mcH_mcH]
    abel
  rw [curvJ, curvJ, actPotC_pot, h1 ν μ, h1 μ ν, h2, dMat_comm ν μ U.1,
    show U.1 * (dMat ν (A.pot μ) - dMat μ (A.pot ν) + brJ (A.pot ν) (A.pot μ)) * star U.1 =
      U.1 * dMat ν (A.pot μ) * star U.1 - U.1 * dMat μ (A.pot ν) * star U.1 +
        U.1 * brJ (A.pot ν) (A.pot μ) * star U.1 from by noncomm_ring]
  abel

/-!

## D. The covariant tower inside the ordinary jet algebra

-/

/-- The connection colour vector of the ordinary jet algebra. -/
noncomputable def connVec (μ : Lor) : Col → JetAlgebra := genVec 0 μ

/-- **The field strength inside the ordinary jet algebra**, in the `HookBianchi` hermitian
  convention
  `F_νμ = ∂_ν A_μ - ∂_μ A_ν + br(A_ν, A_μ)`. -/
noncomputable def curvVec (ν μ : Lor) : Col → JetAlgebra :=
  fun c => jetDeriv ν (connVec μ c) - jetDeriv μ (connVec ν c) + brR (connVec ν) (connVec μ) c

/-- **The covariant derivative** on colour vectors of the ordinary jet algebra:
  `D_ρ X = ∂_ρ X + br(A_ρ, X)`, the `HookBianchi` convention. -/
noncomputable def covD (ρ : Lor) (X : Col → JetAlgebra) : Col → JetAlgebra :=
  fun c => jetDeriv ρ (X c) + brR (connVec ρ) X c

/-- The field strength is antisymmetric.  Such relations are *allowed*: the tower consists of
  elements of the ordinary algebra, not of independent carrier variables. -/
lemma curvVec_swap (ν μ : Lor) (c : Col) : curvVec ν μ c = -curvVec μ ν c := by
  rw [curvVec, curvVec, brR_swap (connVec ν) (connVec μ) c]
  abel

lemma curvVec_self (ν : Lor) (c : Col) : curvVec ν ν c = 0 := by
  rw [curvVec, brR_self, sub_self, add_zero]

/-- The **ordered** iterated covariant derivative along a tuple of directions.  Covariant
  derivatives do not commute, so this genuinely depends on the ordering; the published tower
  symmetrizes it. -/
noncomputable def covIter : (r : ℕ) → (Fin r → Lor) → (Col → JetAlgebra) → (Col → JetAlgebra)
  | 0, _, X => X
  | (n + 1), t, X => covD (t 0) (covIter n (fun i => t i.succ) X)

@[simp]
lemma covIter_zero (t : Fin 0 → Lor) (X : Col → JetAlgebra) : covIter 0 t X = X := rfl

@[simp]
lemma covIter_succ (n : ℕ) (t : Fin (n + 1) → Lor) (X : Col → JetAlgebra) :
    covIter (n + 1) t X = covD (t 0) (covIter n (fun i => t i.succ) X) := rfl

/-- **The symmetrized covariant derivative tower `D^r F`**, parametric in the derivative order. -/
noncomputable def covCurv {r : ℕ} (t : Fin r → Lor) (ν μ : Lor) : Col → JetAlgebra :=
  fun c => (Nat.factorial r : ℝ)⁻¹ •
    ∑ σ : Equiv.Perm (Fin r), covIter r (t ∘ σ) (curvVec ν μ) c

/-- **The published tower is genuinely symmetric**: it is unchanged by any permutation of the
  derivative slots.  No such claim is made for the unsymmetrized `covIter`. -/
lemma covCurv_perm {r : ℕ} (t : Fin r → Lor) (π : Equiv.Perm (Fin r)) (ν μ : Lor) :
    covCurv (t ∘ π) ν μ = covCurv t ν μ := by
  funext c
  rw [covCurv, covCurv]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft π) _ _ fun σ => ?_
  rfl

/-- **Degree-one agreement with the `HookBianchi` pilot**: the first covariant derivative of the
  field
  strength is `D_ρ F_νμ = ∂_ρ F_νμ + br(A_ρ, F_νμ)`. -/
lemma covCurv_one (ρ ν μ : Lor) (c : Col) :
    covCurv (fun _ : Fin 1 => ρ) ν μ c =
      jetDeriv ρ (curvVec ν μ c) + brR (connVec ρ) (curvVec ν μ) c := by
  have hall : ∀ σ : Equiv.Perm (Fin 1),
      covIter 1 ((fun _ : Fin 1 => ρ) ∘ ⇑σ) (curvVec ν μ) c =
        jetDeriv ρ (curvVec ν μ c) + brR (connVec ρ) (curvVec ν μ) c := fun _ => rfl
  rw [covCurv, Finset.sum_congr rfl fun σ (_ : σ ∈ Finset.univ) => hall σ, Finset.sum_const,
    Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  simp

/-- The **ordered** iterated covariant derivative on matrices of jets. -/
noncomputable def covIterJ (A : ColourPot) : (r : ℕ) → (Fin r → Lor) →
    Matrix (Fin 3) (Fin 3) JetRing → Matrix (Fin 3) (Fin 3) JetRing
  | 0, _, M => M
  | (n + 1), t, M => covDJ A (t 0) (covIterJ A n (fun i => t i.succ) M)

@[simp]
lemma covIterJ_zero (A : ColourPot) (t : Fin 0 → Lor) (M : Matrix (Fin 3) (Fin 3) JetRing) :
    covIterJ A 0 t M = M := rfl

@[simp]
lemma covIterJ_succ (A : ColourPot) (n : ℕ) (t : Fin (n + 1) → Lor)
    (M : Matrix (Fin 3) (Fin 3) JetRing) :
    covIterJ A (n + 1) t M = covDJ A (t 0) (covIterJ A n (fun i => t i.succ) M) := rfl

/-- The image of a colour vector of the ordinary algebra under the series dictionary. -/
noncomputable def evalCS (A : ColourPot) (X : Col → JetAlgebra) :
    Matrix (Fin 3) (Fin 3) JetRing := cser fun c => evalS A (X c)

lemma evalCS_connVec (A : ColourPot) (μ : Lor) : evalCS A (connVec μ) = A.pot μ := by
  refine jetMat_ext fun k => ?_
  rw [evalCS, coeffMat_cser, ← ColourPot.cmat_coeffC]
  refine congrArg cmat (Eq.trans (congrArg mkC ?_) (mkC_coordC (A.coeffC k μ)))
  funext c
  show MvPowerSeries.coeff k (evalS A (connVec μ c)) = coordC c (A.coeffC k μ)
  rw [connVec, genVec, evalS_ofGen, sCoordGen_dA, sCoordS, coeff_mkRSeries, add_zero,
    div_self (facI_ne_zero k), one_mul]

lemma evalCS_curvVec (A : ColourPot) (ν μ : Lor) : evalCS A (curvVec ν μ) = curvJ A ν μ := by
  have h : (fun c => evalS A (curvVec ν μ c)) =
      (fun c => MvPowerSeries.pderiv ℝ ν (evalS A (connVec μ c))) -
        (fun c => MvPowerSeries.pderiv ℝ μ (evalS A (connVec ν c))) +
        brR (fun c => evalS A (connVec ν c)) (fun c => evalS A (connVec μ c)) := by
    funext c
    rw [curvVec, map_add, map_sub, evalS_jetDeriv, evalS_jetDeriv, algHom_brR]
    rfl
  rw [evalCS, h, cser_add, cser_sub, ← dMat_cser, ← dMat_cser, ← brJ_cser, curvJ,
    show (cser fun c => evalS A (connVec μ c)) = A.pot μ from evalCS_connVec A μ,
    show (cser fun c => evalS A (connVec ν c)) = A.pot ν from evalCS_connVec A ν]

lemma evalCS_covD (A : ColourPot) (ρ : Lor) (X : Col → JetAlgebra) :
    evalCS A (covD ρ X) = covDJ A ρ (evalCS A X) := by
  have h : (fun c => evalS A (covD ρ X c)) =
      (fun c => MvPowerSeries.pderiv ℝ ρ (evalS A (X c))) +
        brR (fun c => evalS A (connVec ρ c)) (fun c => evalS A (X c)) := by
    funext c
    rw [covD, map_add, evalS_jetDeriv, algHom_brR]
    rfl
  rw [evalCS, h, cser_add, ← dMat_cser, ← brJ_cser, covDJ,
    show (cser fun c => evalS A (connVec ρ c)) = A.pot ρ from evalCS_connVec A ρ]
  rfl

lemma evalCS_covIter (A : ColourPot) : ∀ (r : ℕ) (t : Fin r → Lor) (X : Col → JetAlgebra),
    evalCS A (covIter r t X) = covIterJ A r t (evalCS A X)
  | 0, _, _ => rfl
  | (n + 1), t, X => by
      rw [covIter_succ, covIterJ_succ, evalCS_covD, evalCS_covIter A n]

lemma covIterJ_conj (U : specialUnitaryGroup (Fin 3) JetRing) (A : ColourPot) :
    ∀ (r : ℕ) (t : Fin r → Lor) (M : Matrix (Fin 3) (Fin 3) JetRing),
      covIterJ (actPotC U A) r t (U.1 * M * star U.1) = U.1 * covIterJ A r t M * star U.1
  | 0, _, _ => rfl
  | (n + 1), t, M => by
      rw [covIterJ_succ, covIterJ_succ, covIterJ_conj U A n, covDJ_conj]

lemma evalCS_actPotC_covIter (U : specialUnitaryGroup (Fin 3) JetRing) (A : ColourPot)
    (r : ℕ) (t : Fin r → Lor) (ν μ : Lor) :
    evalCS (actPotC U A) (covIter r t (curvVec ν μ)) =
      U.1 * evalCS A (covIter r t (curvVec ν μ)) * star U.1 := by
  rw [evalCS_covIter, evalCS_covIter, evalCS_curvVec, evalCS_curvVec, curvJ_actPotC,
    covIterJ_conj]

/-!

## E. The residual constant-colour action

-/

/-- **Covariance of the ordered covariant tower**, uniformly in the derivative order. -/
lemma gaugePull_covIter (U : specialUnitaryGroup (Fin 3) JetRing) (r : ℕ) (t : Fin r → Lor)
    (ν μ : Lor) (c : Col) :
    gaugePull U (covIter r t (curvVec ν μ) c) =
      adR (JetGaugeGroupI.evalSU (Fin 3) U) (covIter r t (curvVec ν μ)) c := by
  refine jetAlgebra_funext fun x => ?_
  have hx : potPt (potOf x) = x := potPt_potOf x
  have hkey : (mkC fun c' => MvPowerSeries.constantCoeff
        (evalS (actPotC U (potOf x)) (covIter r t (curvVec ν μ) c'))) =
      adC (JetGaugeGroupI.evalSU (Fin 3) U)
        (mkC fun c' => MvPowerSeries.constantCoeff
          (evalS (potOf x) (covIter r t (curvVec ν μ) c'))) := by
    apply cmat_injective
    rw [cmat_adC, ← jetValue_cser, ← jetValue_cser]
    show Gluon.jetValue (evalCS (actPotC U (potOf x)) (covIter r t (curvVec ν μ))) = _
    rw [evalCS_actPotC_covIter, Gluon.jetValue_mul, Gluon.jetValue_mul, Gluon.jetValue_star,
      jetValue_coe_eq, star_eq_conjTranspose]
    rfl
  have hL : evalA x (gaugePull U (covIter r t (curvVec ν μ) c)) =
      MvPowerSeries.constantCoeff
        (evalS (actPotC U (potOf x)) (covIter r t (curvVec ν μ) c)) := by
    rw [evalA_gaugePull, constantCoeff_evalS]
    rfl
  have hR : evalA x (adR (JetGaugeGroupI.evalSU (Fin 3) U) (covIter r t (curvVec ν μ)) c) =
      ∑ c', adCoef (JetGaugeGroupI.evalSU (Fin 3) U) c c' *
        MvPowerSeries.constantCoeff (evalS (potOf x) (covIter r t (curvVec ν μ) c')) := by
    rw [adR, map_sum]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [map_mul, evalA_algebraMap, constantCoeff_evalS, hx]
  have hc := congrArg (coordC c) hkey
  rw [coordC_mkC, coordC_adC] at hc
  rw [hL, hR, hc]
  exact Finset.sum_congr rfl fun c' _ => by rw [coordC_mkC]

/-- **The arbitrary-order covariance theorem.**  Under any jet gauge substitution the symmetrized
  covariant curvature tower transforms by the adjoint action of the base-point value of the jet
  alone. -/
lemma gaugePull_covCurv (U : specialUnitaryGroup (Fin 3) JetRing) {r : ℕ} (t : Fin r → Lor)
    (ν μ : Lor) (c : Col) :
    gaugePull U (covCurv t ν μ c) =
      adR (JetGaugeGroupI.evalSU (Fin 3) U) (covCurv t ν μ) c := by
  have hL : gaugePull U (covCurv t ν μ c) =
      (Nat.factorial r : ℝ)⁻¹ • ∑ σ : Equiv.Perm (Fin r),
        adR (JetGaugeGroupI.evalSU (Fin 3) U) (covIter r (t ∘ σ) (curvVec ν μ)) c := by
    rw [covCurv, map_smul, map_sum]
    exact congrArg _ (Finset.sum_congr rfl fun σ _ => gaugePull_covIter U r (t ∘ σ) ν μ c)
  have hR : adR (JetGaugeGroupI.evalSU (Fin 3) U) (covCurv t ν μ) c =
      (Nat.factorial r : ℝ)⁻¹ • ∑ σ : Equiv.Perm (Fin r),
        adR (JetGaugeGroupI.evalSU (Fin 3) U) (covIter r (t ∘ σ) (curvVec ν μ)) c := by
    rw [adR, Finset.smul_sum,
      show (∑ σ : Equiv.Perm (Fin r), (Nat.factorial r : ℝ)⁻¹ •
          adR (JetGaugeGroupI.evalSU (Fin 3) U) (covIter r (t ∘ σ) (curvVec ν μ)) c) =
        ∑ σ : Equiv.Perm (Fin r), ∑ c', (Nat.factorial r : ℝ)⁻¹ •
          (algebraMap ℝ JetAlgebra (adCoef (JetGaugeGroupI.evalSU (Fin 3) U) c c') *
            covIter r (t ∘ σ) (curvVec ν μ) c') from
        Finset.sum_congr rfl fun σ _ => by rw [adR, Finset.smul_sum], Finset.sum_comm]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [covCurv, mul_smul_comm, Finset.mul_sum, Finset.smul_sum]
  rw [hL, hR]

/-- Every component of the complete covariant curvature tower. -/
def covTower : Set JetAlgebra :=
  {P | ∃ (r : ℕ) (t : Fin r → Lor) (ν μ : Lor) (c : Col), P = covCurv t ν μ c}

lemma covCurv_mem_covTower {r : ℕ} (t : Fin r → Lor) (ν μ : Lor) (c : Col) :
    covCurv t ν μ c ∈ covTower := ⟨r, t, ν, μ, c, rfl⟩

/-- **The subalgebra generated by the covariant curvature tower.** -/
noncomputable def covAlgebra : Subalgebra ℝ JetAlgebra := Algebra.adjoin ℝ covTower

lemma covCurv_mem_covAlgebra {r : ℕ} (t : Fin r → Lor) (ν μ : Lor) (c : Col) :
    covCurv t ν μ c ∈ covAlgebra := Algebra.subset_adjoin (covCurv_mem_covTower t ν μ c)

lemma gaugePull_covCurv_mem (U : specialUnitaryGroup (Fin 3) JetRing) {r : ℕ} (t : Fin r → Lor)
    (ν μ : Lor) (c : Col) : gaugePull U (covCurv t ν μ c) ∈ covAlgebra := by
  rw [gaugePull_covCurv, adR]
  exact Subalgebra.sum_mem _ fun c' _ =>
    Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (covCurv_mem_covAlgebra t ν μ c')

/-- **Stability.**  The covariant subalgebra is preserved by every jet gauge substitution. -/
lemma gaugePull_covAlgebra_le (U : specialUnitaryGroup (Fin 3) JetRing) :
    covAlgebra.map (gaugePull U) ≤ covAlgebra := by
  rw [Subalgebra.map_le]
  refine Algebra.adjoin_le ?_
  rintro P ⟨r, t, ν, μ, c, rfl⟩
  exact gaugePull_covCurv_mem U t ν μ c

/-- **Based jets fix the covariant subalgebra pointwise.** -/
lemma gaugePull_eq_self_of_based (U : specialUnitaryGroup (Fin 3) JetRing)
    (hU : JetGaugeGroupI.evalSU (Fin 3) U = 1) {P : JetAlgebra} (hP : P ∈ covAlgebra) :
    gaugePull U P = P := by
  have h : covAlgebra ≤ AlgHom.equalizer (gaugePull U) (AlgHom.id ℝ JetAlgebra) := by
    refine Algebra.adjoin_le ?_
    rintro Q ⟨r, t, ν, μ, c, rfl⟩
    show gaugePull U (covCurv t ν μ c) = AlgHom.id ℝ JetAlgebra (covCurv t ν μ c)
    rw [gaugePull_covCurv, hU, adR_one, AlgHom.id_apply]
  exact h hP

/-- **The action on the covariant subalgebra factors through evaluation at the base point.** -/
lemma gaugePull_eq_of_evalSU_eq (U V : specialUnitaryGroup (Fin 3) JetRing)
    (h : JetGaugeGroupI.evalSU (Fin 3) U = JetGaugeGroupI.evalSU (Fin 3) V)
    {P : JetAlgebra} (hP : P ∈ covAlgebra) : gaugePull U P = gaugePull V P := by
  have hle : covAlgebra ≤ AlgHom.equalizer (gaugePull U) (gaugePull V) := by
    refine Algebra.adjoin_le ?_
    rintro Q ⟨r, t, ν, μ, c, rfl⟩
    show gaugePull U (covCurv t ν μ c) = gaugePull V (covCurv t ν μ c)
    rw [gaugePull_covCurv, gaugePull_covCurv, h]
  exact hle hP

/-- **On the covariant subalgebra a jet acts as the constant jet of its base-point value.**  This
  is the easy direction of the eventual completeness theorem.  It does *not* say that a tower
  element is invariant: a constant colour rotation generally moves it. -/
lemma gaugePull_eq_ofConstantSU (U : specialUnitaryGroup (Fin 3) JetRing) {P : JetAlgebra}
    (hP : P ∈ covAlgebra) :
    gaugePull U P =
      gaugePull (JetGaugeGroupI.ofConstantSU (Fin 3) (JetGaugeGroupI.evalSU (Fin 3) U)) P :=
  gaugePull_eq_of_evalSU_eq U _ (SU3Jet.evalSU_ofConstantSU _).symm hP

end SU3Jet

end StandardModel
