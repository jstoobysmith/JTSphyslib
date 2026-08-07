/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.Particles.StandardModel.GaugeBosons.BBoson.Basic
public import Physlib.Particles.StandardModel.GaugeBosons.Gluons
/-!
# A diagonal based `SU(3)` monomial jet

## i. Overview

This file proves that the scalar monomial-exponential gauge jet already constructed for the B boson
can
be embedded diagonally into `specialUnitaryGroup (Fin 3) JetRing` with exact control of its
base-point value and its leading Taylor coefficient.

The construction is: extract the scalar unitary series `z = exp(-i a X^w)` underlying
`BBoson.JetAlgebra.expUnitary a w hw`, and form

```text
diagonal (z, star z, 1).
```

Unitarity is `z (star z) = 1` entrywise; the determinant is `z (star z) 1 = 1`, so no determinant
theory beyond `Matrix.det_diagonal` is needed.

## ii. Conventions

Physlib represents gluon potentials by hermitian matrices, with Maurer–Cartan matrix

```text
mcMatrix μ A = i (∂_μ A)(0) (A(0))†
```

(`Gluon.mcMatrix`), and `BBoson.JetAlgebra.expUnitary a w hw` is the jet of `exp(-i a X^w)`, whose
coefficient at `n • w` is `(-i a)^n / n!`.

Composing the two: for a degree-one exponent `w = single μ 1` the diagonal jet has

```text
(∂_μ diag)(0) = (-i a) • diag(1, -1, 0),  mcMatrix μ = i (-i a) • diag(1, -1, 0) = a • diag(1, -1,
0).
```

So the Maurer–Cartan coefficient is `+a • diag(1, -1, 0)`: the sign is positive in `a`, and the two
factors of `i` cancel. This is recorded in `mcCoeff_diagSU_single`; it is the sign later modules
must
use.

## iii. Results

* `diagMat_mem` — the diagonal matrix is special unitary over the jet ring;
* `jetValue_diagMat`, `evalSU_diagSU`, `eval_diagJet` — the jet is based;
* `coeffMat_diagMat_self` — the leading Taylor coefficient is `(-i a) • diag(1, -1, 0)`;
* `coeffMat_diagMat_eq_zero` — all other coefficients below the first multiple of `w` vanish;
* `mcCoeff_diagSU_single`, `mcCoeff_diagSU_single_of_ne` — first-order realizability of an
  arbitrary real multiple of `diag(1, -1, 0)` in one chosen Lorentz direction;
* `mcCoeff_diagSU_two`, `coeffMat_diagMat_two` — second-order readiness: for a degree-two exponent
  every first-order Maurer–Cartan coefficient vanishes while the coefficient at `w` is controlled.

-/

@[expose] public section

namespace StandardModel

open Matrix MvPowerSeries JetRing

namespace SU3Jet

/-!

## A. The scalar exponential series

`BBoson.JetAlgebra.expUnitary` packages the series in the `U(1)` slot of `JetGaugeGroupI`. The
series itself is reachable through that projection, so no reimplementation of the coefficientwise
exponential is needed.

-/

/-- The scalar unitary power series `exp(-i a X^w)` underlying `BBoson.JetAlgebra.expUnitary`. -/
noncomputable def expSeries (a : ℝ) (w : (Fin 1 ⊕ Fin 3) →₀ ℕ) (hw : w ≠ 0) : JetRing :=
  (((BBoson.JetAlgebra.expUnitary a w hw).2.2 : unitary JetRing) : JetRing)

lemma expSeries_mul_star (a : ℝ) (w : (Fin 1 ⊕ Fin 3) →₀ ℕ) (hw : w ≠ 0) :
    expSeries a w hw * star (expSeries a w hw) = 1 :=
  (Unitary.mem_iff.mp (BBoson.JetAlgebra.expUnitary a w hw).2.2.2).2

lemma star_mul_expSeries (a : ℝ) (w : (Fin 1 ⊕ Fin 3) →₀ ℕ) (hw : w ≠ 0) :
    star (expSeries a w hw) * expSeries a w hw = 1 :=
  (Unitary.mem_iff.mp (BBoson.JetAlgebra.expUnitary a w hw).2.2.2).1

/-- The leading Taylor coefficient of the scalar series. -/
lemma coeff_expSeries_self (a : ℝ) (w : (Fin 1 ⊕ Fin 3) →₀ ℕ) (hw : w ≠ 0) :
    coeff w (expSeries a w hw) = -(a : ℂ) * Complex.I := by
  have h := BBoson.JetAlgebra.coeff_expUnitary_nsmul a hw 1
  rw [one_smul] at h
  simpa [expSeries] using h

/-- The Taylor coefficients of the scalar series vanish away from the multiples of `w`. -/
lemma coeff_expSeries_of_forall_ne (a : ℝ) (w : (Fin 1 ⊕ Fin 3) →₀ ℕ) (hw : w ≠ 0)
    {k : (Fin 1 ⊕ Fin 3) →₀ ℕ} (hk : ∀ n : ℕ, k ≠ n • w) :
    coeff k (expSeries a w hw) = 0 :=
  BBoson.JetAlgebra.coeff_expUnitary_of_forall_ne a hw hk

lemma constantCoeff_expSeries (a : ℝ) (w : (Fin 1 ⊕ Fin 3) →₀ ℕ) (hw : w ≠ 0) :
    constantCoeff (expSeries a w hw) = 1 :=
  BBoson.JetAlgebra.constantCoeff_expUnitary a w hw

/-!

## B. The diagonal special-unitary jet

-/

/-- The diagonal of the ``DiagonalJet`` jet: `(z, star z, 1)`. -/
noncomputable def diagVec (a : ℝ) (w : (Fin 1 ⊕ Fin 3) →₀ ℕ) (hw : w ≠ 0) : Fin 3 → JetRing :=
  ![expSeries a w hw, star (expSeries a w hw), 1]

/-- The diagonal `SU(3)` monomial jet `diag(exp(-i a X^w), exp(i a X^w), 1)`, as a matrix. -/
noncomputable def diagMat (a : ℝ) (w : (Fin 1 ⊕ Fin 3) →₀ ℕ) (hw : w ≠ 0) :
    Matrix (Fin 3) (Fin 3) JetRing :=
  diagonal (diagVec a w hw)

lemma diagMat_mul_star (a : ℝ) (w : (Fin 1 ⊕ Fin 3) →₀ ℕ) (hw : w ≠ 0) :
    diagMat a w hw * star (diagMat a w hw) = 1 := by
  have h : (fun i => diagVec a w hw i * (star (diagVec a w hw)) i) =
      fun _ : Fin 3 => (1 : JetRing) := by
    funext i
    fin_cases i <;>
      simp [diagVec, expSeries_mul_star, star_mul_expSeries]
  rw [diagMat, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal, h,
    diagonal_one]

lemma det_diagMat (a : ℝ) (w : (Fin 1 ⊕ Fin 3) →₀ ℕ) (hw : w ≠ 0) :
    (diagMat a w hw).det = 1 := by
  rw [diagMat, det_diagonal, Fin.prod_univ_three]
  simp [diagVec, expSeries_mul_star]

/-- **Special-unitary membership.** The diagonal monomial jet lies in
  `specialUnitaryGroup (Fin 3) JetRing`: unitarity is entrywise `z (star z) = 1`, and the
  determinant is the product of the three diagonal entries. -/
lemma diagMat_mem (a : ℝ) (w : (Fin 1 ⊕ Fin 3) →₀ ℕ) (hw : w ≠ 0) :
    diagMat a w hw ∈ specialUnitaryGroup (Fin 3) JetRing :=
  mem_specialUnitaryGroup_iff.mpr
    ⟨mem_unitaryGroup_iff.mpr (diagMat_mul_star a w hw), det_diagMat a w hw⟩

/-- The diagonal `SU(3)` monomial jet, as an element of the colour jet group. -/
noncomputable def diagSU (a : ℝ) (w : (Fin 1 ⊕ Fin 3) →₀ ℕ) (hw : w ≠ 0) :
    specialUnitaryGroup (Fin 3) JetRing :=
  ⟨diagMat a w hw, diagMat_mem a w hw⟩

/-- The diagonal monomial jet as an element of the full jet gauge group, with trivial `SU(2)` and
  `U(1)` components. The gluon action depends only on the `SU(3)` component. -/
noncomputable def diagJet (a : ℝ) (w : (Fin 1 ⊕ Fin 3) →₀ ℕ) (hw : w ≠ 0) : JetGaugeGroupI :=
  (diagSU a w hw, 1, 1)

/-!

## C. Basedness

-/

/-- **Basedness.** The value of the diagonal monomial jet at the base point is the identity. -/
lemma jetValue_diagMat (a : ℝ) (w : (Fin 1 ⊕ Fin 3) →₀ ℕ) (hw : w ≠ 0) :
    Gluon.jetValue (diagMat a w hw) = 1 := by
  have h : (fun i => constantCoeff (diagVec a w hw i)) = fun _ : Fin 3 => (1 : ℂ) := by
    funext i
    fin_cases i <;>
      simp [diagVec, constantCoeff_expSeries]
  rw [Gluon.jetValue, diagMat, diagonal_map (map_zero _), h, diagonal_one]

lemma evalSU_diagSU (a : ℝ) (w : (Fin 1 ⊕ Fin 3) →₀ ℕ) (hw : w ≠ 0) :
    JetGaugeGroupI.evalSU (Fin 3) (diagSU a w hw) = 1 := by
  apply Subtype.ext
  rw [Gluon.evalSU_coe]
  simpa [diagSU] using jetValue_diagMat a w hw

/-- The diagonal monomial jet lies in the kernel of evaluation: it is a based gauge jet. -/
lemma eval_diagJet (a : ℝ) (w : (Fin 1 ⊕ Fin 3) →₀ ℕ) (hw : w ≠ 0) :
    JetGaugeGroupI.eval (diagJet a w hw) = 1 := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact evalSU_diagSU a w hw
  · exact map_one _
  · exact map_one _

/-!

## D. Taylor coefficients

-/

/-- The matrix of Taylor coefficients at a multi-index. At `k = single μ 1` this is
  `Gluon.jetDeriv μ`. -/
noncomputable def coeffMat (k : (Fin 1 ⊕ Fin 3) →₀ ℕ) (A : Matrix (Fin 3) (Fin 3) JetRing) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  A.map (coeff k)

lemma jetDeriv_eq_coeffMat (μ : Fin 1 ⊕ Fin 3) (A : Matrix (Fin 3) (Fin 3) JetRing) :
    Gluon.jetDeriv μ A = coeffMat (Finsupp.single μ 1) A := rfl

lemma coeffMat_diagMat (k : (Fin 1 ⊕ Fin 3) →₀ ℕ) (a : ℝ) (w : (Fin 1 ⊕ Fin 3) →₀ ℕ)
    (hw : w ≠ 0) :
    coeffMat k (diagMat a w hw) =
      diagonal ![coeff k (expSeries a w hw), star (coeff k (expSeries a w hw)),
        if k = 0 then 1 else 0] := by
  have h : (fun i => coeff k (diagVec a w hw i)) =
      ![coeff k (expSeries a w hw), star (coeff k (expSeries a w hw)),
        if k = 0 then 1 else 0] := by
    funext i
    fin_cases i <;> simp [diagVec, coeff_one]
  rw [coeffMat, diagMat, diagonal_map (map_zero _), h]

/-- The traceless hermitian colour direction `diag(1, -1, 0)`. -/
def colourMat : Matrix (Fin 3) (Fin 3) ℂ := diagonal ![1, -1, 0]

lemma colourMat_mem : colourMat ∈ selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ) := by
  rw [selfAdjoint.mem_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [colourMat, Matrix.star_apply]

/-- The colour direction `diag(1, -1, 0)` as a hermitian matrix. -/
noncomputable def colourH : selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ) :=
  ⟨colourMat, colourMat_mem⟩

@[simp]
lemma colourH_coe : (colourH : Matrix (Fin 3) (Fin 3) ℂ) = colourMat := rfl

lemma trace_colourMat : trace colourMat = 0 := by
  simp [colourMat, Matrix.trace_diagonal, Fin.sum_univ_three]

/-- **Leading coefficient.** The Taylor coefficient of the diagonal monomial jet at its own
  exponent is `(-i a) • diag(1, -1, 0)`. -/
lemma coeffMat_diagMat_self (a : ℝ) (w : (Fin 1 ⊕ Fin 3) →₀ ℕ) (hw : w ≠ 0) :
    coeffMat w (diagMat a w hw) = (-(a : ℂ) * Complex.I) • colourMat := by
  have hstar : star (-(a : ℂ) * Complex.I) = (a : ℂ) * Complex.I := by
    rw [star_mul', Complex.star_def, Complex.conj_I, map_neg, Complex.conj_ofReal]
    ring
  rw [coeffMat_diagMat, coeff_expSeries_self, hstar, if_neg hw, colourMat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply]

/-- **Vanishing of the lower coefficients.** Away from the nonzero multiples of the exponent the
  diagonal monomial jet has no Taylor coefficients: in particular every coefficient of positive
  order strictly below `w` vanishes. -/
lemma coeffMat_diagMat_eq_zero (a : ℝ) (w : (Fin 1 ⊕ Fin 3) →₀ ℕ) (hw : w ≠ 0)
    {k : (Fin 1 ⊕ Fin 3) →₀ ℕ} (hk0 : k ≠ 0) (hk : ∀ n : ℕ, k ≠ n • w) :
    coeffMat k (diagMat a w hw) = 0 := by
  rw [coeffMat_diagMat, coeff_expSeries_of_forall_ne a w hw hk, star_zero, if_neg hk0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-!

## E. The Maurer–Cartan coefficient

-/

lemma mcMatrix_diagMat (μ : Fin 1 ⊕ Fin 3) (a : ℝ) (w : (Fin 1 ⊕ Fin 3) →₀ ℕ) (hw : w ≠ 0) :
    Gluon.mcMatrix μ (diagMat a w hw) =
      Complex.I • coeffMat (Finsupp.single μ 1) (diagMat a w hw) := by
  rw [Gluon.mcMatrix, jetValue_diagMat, star_one, Matrix.mul_one, jetDeriv_eq_coeffMat]

/-- Real scalars act on the colour carrier through the complex scalars. -/
lemma real_smul_colourMat (r : ℝ) : (r : ℂ) • colourMat = r • colourMat := by
  rw [show ((r : ℂ)) = algebraMap ℝ ℂ r from rfl, algebraMap_smul]

/-- **First-order specialization.** For the degree-one exponent `single μ 1` the Maurer–Cartan
  coefficient in the direction `μ` is exactly `a • diag(1, -1, 0)`. The sign is positive: the
  factor `-i` in `exp(-i a X^w)` cancels the factor `i` in `Gluon.mcMatrix`. Since `a` ranges over
  all reals, every real multiple of the colour direction is realized. -/
lemma mcCoeff_diagSU_single (a : ℝ) (μ : Fin 1 ⊕ Fin 3)
    (hw : (Finsupp.single μ 1 : (Fin 1 ⊕ Fin 3) →₀ ℕ) ≠ 0) :
    Gluon.mcCoeff (diagSU a (Finsupp.single μ 1) hw) μ = a • colourH := by
  apply Subtype.ext
  show Gluon.mcMatrix μ (diagMat a (Finsupp.single μ 1) hw) = _
  rw [mcMatrix_diagMat, coeffMat_diagMat_self, smul_smul,
    show Complex.I * (-(a : ℂ) * Complex.I) = (a : ℂ) by
      rw [show Complex.I * (-(a : ℂ) * Complex.I) = -(Complex.I * Complex.I) * (a : ℂ) by ring,
        Complex.I_mul_I]
      ring,
    real_smul_colourMat]
  rfl

lemma single_ne_zero' (μ : Fin 1 ⊕ Fin 3) :
    (Finsupp.single μ 1 : (Fin 1 ⊕ Fin 3) →₀ ℕ) ≠ 0 := by
  simp [Finsupp.single_eq_zero]

/-- In the other Lorentz directions the Maurer–Cartan coefficient of the degree-one jet vanishes:
  the translation is concentrated in the single direction `μ`. -/
lemma mcCoeff_diagSU_single_of_ne (a : ℝ) (μ ν : Fin 1 ⊕ Fin 3) (hμν : ν ≠ μ)
    (hw : (Finsupp.single μ 1 : (Fin 1 ⊕ Fin 3) →₀ ℕ) ≠ 0) :
    Gluon.mcCoeff (diagSU a (Finsupp.single μ 1) hw) ν = 0 := by
  apply Subtype.ext
  show Gluon.mcMatrix ν (diagMat a (Finsupp.single μ 1) hw) = _
  have hμν' : μ ≠ ν := fun h => hμν h.symm
  have hk : ∀ n : ℕ, (Finsupp.single ν 1 : (Fin 1 ⊕ Fin 3) →₀ ℕ) ≠ n • Finsupp.single μ 1 := by
    intro n h
    have h' := DFunLike.congr_fun h ν
    rw [Finsupp.single_eq_same, Finsupp.smul_apply, Finsupp.single_eq_of_ne hμν,
      smul_eq_mul, Nat.mul_zero] at h'
    exact absurd h' one_ne_zero
  rw [mcMatrix_diagMat, coeffMat_diagMat_eq_zero a _ hw (single_ne_zero' ν) hk, smul_zero]
  rfl

/-!

## F. Second-order readiness

For a degree-two exponent the jet is based *to first order as well*: every first-order
Maurer–Cartan coefficient vanishes, while the Taylor coefficient at the exponent itself is still
`(-i a) • diag(1, -1, 0)`. This is the input a second-order gauge variation needs; the induced
action on a first-order jet algebra is not built here.

-/

/-- A degree-two spacetime exponent is nonzero. -/
lemma add_single_ne_zero (μ ν : Fin 1 ⊕ Fin 3) :
    (Finsupp.single μ 1 + Finsupp.single ν 1 : (Fin 1 ⊕ Fin 3) →₀ ℕ) ≠ 0 := by
  intro h
  have h' := DFunLike.congr_fun h μ
  rw [Finsupp.add_apply, Finsupp.single_eq_same] at h'
  simp at h'

/-- No degree-one multi-index is a multiple of a degree-two one. -/
lemma single_ne_nsmul_add (ρ μ ν : Fin 1 ⊕ Fin 3) (n : ℕ) :
    (Finsupp.single ρ 1 : (Fin 1 ⊕ Fin 3) →₀ ℕ) ≠
      n • (Finsupp.single μ 1 + Finsupp.single ν 1) := by
  intro h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [zero_smul] at h
    exact single_ne_zero' ρ h
  have key : ∀ σ : Fin 1 ⊕ Fin 3,
      (Finsupp.single ρ 1 : (Fin 1 ⊕ Fin 3) →₀ ℕ) σ =
        (Finsupp.single μ n : (Fin 1 ⊕ Fin 3) →₀ ℕ) σ
          + (Finsupp.single ν n : (Fin 1 ⊕ Fin 3) →₀ ℕ) σ := by
    intro σ
    have hσ := DFunLike.congr_fun h σ
    simpa [Finsupp.smul_apply, Finsupp.add_apply] using hσ
  have hb : ∀ σ : Fin 1 ⊕ Fin 3, (Finsupp.single ρ 1 : (Fin 1 ⊕ Fin 3) →₀ ℕ) σ ≤ 1 := by
    intro σ
    rw [Finsupp.single_apply]
    split <;> simp
  have e1 : (Finsupp.single μ n : (Fin 1 ⊕ Fin 3) →₀ ℕ) μ = n := Finsupp.single_eq_same
  have e2 : (Finsupp.single ν n : (Fin 1 ⊕ Fin 3) →₀ ℕ) ν = n := Finsupp.single_eq_same
  rcases eq_or_ne μ ν with rfl | hne
  · have h1 := key μ
    have h3 := hb μ
    rw [e1] at h1
    omega
  · have hne' : ν ≠ μ := fun hc => hne hc.symm
    have h1 := key μ
    have h2 := key ν
    rw [e1, Finsupp.single_eq_of_ne hne] at h1
    rw [e2, Finsupp.single_eq_of_ne hne'] at h2
    have hρμ : ρ = μ := by
      by_contra hc
      rw [Finsupp.single_eq_of_ne (Ne.symm hc)] at h1
      omega
    have hρν : ρ = ν := by
      by_contra hc
      rw [Finsupp.single_eq_of_ne (Ne.symm hc)] at h2
      omega
    exact hne (by rw [← hρμ, hρν])

/-- **Second-order readiness, part one.** For a degree-two exponent every first-order
  Maurer–Cartan coefficient of the diagonal monomial jet vanishes: the jet is based through first
  order, so it acts trivially on the undifferentiated connection. -/
lemma mcCoeff_diagSU_two (a : ℝ) (μ ν ρ : Fin 1 ⊕ Fin 3) :
    Gluon.mcCoeff (diagSU a (Finsupp.single μ 1 + Finsupp.single ν 1)
      (add_single_ne_zero μ ν)) ρ = 0 := by
  apply Subtype.ext
  show Gluon.mcMatrix ρ (diagMat a _ (add_single_ne_zero μ ν)) = _
  rw [mcMatrix_diagMat,
    coeffMat_diagMat_eq_zero a _ (add_single_ne_zero μ ν) (single_ne_zero' ρ)
      (single_ne_nsmul_add ρ μ ν),
    smul_zero]
  rfl

/-- **Second-order readiness, part two.** The selected second-order Taylor coefficient of the
  degree-two jet is exactly `(-i a) • diag(1, -1, 0)`, stated directly as a power-series
  coefficient. -/
lemma coeffMat_diagMat_two (a : ℝ) (μ ν : Fin 1 ⊕ Fin 3) :
    coeffMat (Finsupp.single μ 1 + Finsupp.single ν 1)
        (diagMat a (Finsupp.single μ 1 + Finsupp.single ν 1) (add_single_ne_zero μ ν)) =
      (-(a : ℂ) * Complex.I) • colourMat :=
  coeffMat_diagMat_self a _ (add_single_ne_zero μ ν)

end SU3Jet

end StandardModel
