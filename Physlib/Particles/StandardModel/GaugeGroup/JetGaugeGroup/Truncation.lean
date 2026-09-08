/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.LocalGaugeData
/-!
# Truncation of the jet gauge group

## i. Overview

Truncating a jet of gauge transformations at order `n` sets to zero, in every matrix
entry, the Taylor coefficients of total degree above `n`. This `truncation n` is a plain
function into the matrix data, not a homomorphism into `JetGaugeGroupI`: deleting the
coefficients above order `n` breaks unitarity and multiplicativity at the orders between
`n + 1` and `2n`.

The homomorphic notion of a jet *trivial to order `n`* is the truncation filtration of the
local-gauge-data package, `localGaugeData.truncationKer n`, defined in
`Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.Truncation` through the value and
the Maurer–Cartan form of the jet alone. This file compares the two notions: a jet trivial to
order `n` in that sense truncates to the identity, `truncation_eq_one_of_mem_truncationKer`.
The argument is the Euler identity `∑_ρ x_ρ ∂_ρ f = (degree) f` on power series, applied to
the radial relation `∂_ρ U = −i ω_ρ(U) U` between a jet and its Maurer–Cartan form.

## ii. Key results

- `JetGaugeGroupI.truncation` : the `n`-th truncation of a jet.
- `JetGaugeGroupI.truncation_eq_one_of_mem_truncationKer` : jets trivial to order `n`
  truncate to the identity.

## iii. Table of contents

- A. The truncation
- B. Aside: vanishing of coefficients from the Euler identity
- C. The comparison with the Maurer–Cartan filtration

-/

@[expose] public section

open MvPowerSeries

namespace StandardModel

namespace JetGaugeGroupI

open JetGaugeAlgebra JetRing

/-!

## A. The truncation

-/

/-- The `n`-th truncation of a jet of a gauge transformation: componentwise, all Taylor
  coefficients of total degree greater than `n` are set to zero. -/
noncomputable def truncation (n : ℕ) (U : JetGaugeGroupI) :
    Matrix (Fin 3) (Fin 3) JetRing × Matrix (Fin 2) (Fin 2) JetRing × JetRing :=
  (U.1.1.map (JetRing.truncation n), U.2.1.1.map (JetRing.truncation n),
    JetRing.truncation n U.2.2.1)

/-- Truncation of the identity jet is the identity value triple. -/
@[simp]
lemma truncation_one (n : ℕ) : truncation n (1 : JetGaugeGroupI) = 1 :=
  Prod.ext (Matrix.map_one _ (JetRing.truncation_zero n) (JetRing.truncation_one n))
    (Prod.ext (Matrix.map_one _ (JetRing.truncation_zero n) (JetRing.truncation_one n))
      (JetRing.truncation_one n))

/-!

## B. Aside: vanishing of coefficients from the Euler identity

-/

/-- A product with a factor whose coefficients vanish below degree `n` has coefficients
  vanishing below degree `n`. -/
lemma coeff_mul_eq_zero_of_lt {n : ℕ} {w : JetRing}
    (hw : ∀ q : (Fin 1 ⊕ Fin 3) →₀ ℕ, Finsupp.degree q < n → coeff q w = 0) (v : JetRing)
    {q : (Fin 1 ⊕ Fin 3) →₀ ℕ} (hq : Finsupp.degree q < n) : coeff q (w * v) = 0 := by
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hpq : p.1 + p.2 = q := Finset.mem_antidiagonal.mp hp
  have hdeg : Finsupp.degree p.1 ≤ Finsupp.degree q := by
    rw [← hpq, map_add]
    exact Nat.le_add_right _ _
  rw [hw p.1 (lt_of_le_of_lt hdeg hq), zero_mul]

/-- The Euler vanishing principle: a power series all of whose first derivatives have
  coefficients vanishing below degree `n` has vanishing coefficients in every nonzero degree
  up to `n`, since `∑_ρ x_ρ ∂_ρ f` has the coefficient of `f` at `p` scaled by the degree
  of `p`. -/
lemma coeff_eq_zero_of_coeff_pderiv_eq_zero {n : ℕ} {f : JetRing}
    (hf : ∀ (ρ : Fin 1 ⊕ Fin 3) (q : (Fin 1 ⊕ Fin 3) →₀ ℕ), Finsupp.degree q < n →
      coeff q (pderiv ℂ ρ f) = 0)
    {p : (Fin 1 ⊕ Fin 3) →₀ ℕ} (hp : p ≠ 0) (hpn : Finsupp.degree p ≤ n) : coeff p f = 0 := by
  have h1 := JetRing.coeff_sum_X_smul_pderiv f p
  have h2 : coeff p (∑ ρ, (X ρ : JetRing) • pderiv ℂ ρ f) = 0 := by
    rw [map_sum]
    refine Finset.sum_eq_zero fun ρ _ => ?_
    rw [JetRing.coeff_X_smul]
    split_ifs with hle
    · refine hf ρ _ ?_
      have hd := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
      rw [map_add, Finsupp.degree_single] at hd
      omega
    · rfl
  rw [h2] at h1
  have hne : ((Finsupp.degree p : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr fun hc => hp ((Finsupp.degree_eq_zero_iff p).mp hc)
  exact (mul_eq_zero.mp h1.symm).resolve_left hne

/-- A power series satisfying a radial relation `∂_ρ f = x_ρ f`, with the `x_ρ` vanishing
  below degree `n`, has no coefficients in nonzero degree up to `n`. -/
lemma coeff_eq_zero_of_pderiv_eq_mul {n : ℕ} {f : JetRing} {x : (Fin 1 ⊕ Fin 3) → JetRing}
    (hd : ∀ ρ, pderiv ℂ ρ f = x ρ * f)
    (hx : ∀ (ρ : Fin 1 ⊕ Fin 3) (q : (Fin 1 ⊕ Fin 3) →₀ ℕ), Finsupp.degree q < n →
      coeff q (x ρ) = 0)
    {p : (Fin 1 ⊕ Fin 3) →₀ ℕ} (hp : p ≠ 0) (hpn : Finsupp.degree p ≤ n) : coeff p f = 0 :=
  coeff_eq_zero_of_coeff_pderiv_eq_zero
    (fun ρ q hq => by rw [hd ρ]; exact coeff_mul_eq_zero_of_lt (hx ρ) f hq) hp hpn

/-- The matrix form of `coeff_eq_zero_of_pderiv_eq_mul`: the entries of a matrix of power
  series satisfying `∂_ρ A = X_ρ A`, with the `X_ρ` vanishing below degree `n`, have no
  coefficients in nonzero degree up to `n`. -/
lemma coeff_entry_eq_zero_of_map_pderiv_eq_mul {κ : Type} [Fintype κ] [DecidableEq κ] {n : ℕ}
    {A : Matrix κ κ JetRing} {X : (Fin 1 ⊕ Fin 3) → Matrix κ κ JetRing}
    (hd : ∀ ρ, A.map (pderiv ℂ ρ) = X ρ * A)
    (hX : ∀ (ρ : Fin 1 ⊕ Fin 3) (q : (Fin 1 ⊕ Fin 3) →₀ ℕ), Finsupp.degree q < n →
      ∀ i j, coeff q (X ρ i j) = 0)
    (i j : κ) {p : (Fin 1 ⊕ Fin 3) →₀ ℕ} (hp : p ≠ 0) (hpn : Finsupp.degree p ≤ n) :
    coeff p (A i j) = 0 := by
  refine coeff_eq_zero_of_coeff_pderiv_eq_zero (fun ρ q hq => ?_) hp hpn
  have h1 : pderiv ℂ ρ (A i j) = (X ρ * A) i j := by rw [← hd ρ, Matrix.map_apply]
  rw [h1, Matrix.mul_apply, map_sum]
  exact Finset.sum_eq_zero fun k _ => coeff_mul_eq_zero_of_lt (fun q' hq' => hX ρ q' hq' i k) _ hq

/-- A matrix of power series with identity value and no coefficients in nonzero degree up
  to `n` truncates to the identity. -/
lemma matrix_map_truncation_eq_one {κ : Type} [Fintype κ] [DecidableEq κ] {n : ℕ}
    {A : Matrix κ κ JetRing} (h0 : (constantCoeff : JetRing →+* ℂ).mapMatrix A = 1)
    (hA : ∀ (i j : κ) (p : (Fin 1 ⊕ Fin 3) →₀ ℕ), p ≠ 0 → Finsupp.degree p ≤ n →
      coeff p (A i j) = 0) :
    A.map (JetRing.truncation n) = (1 : Matrix κ κ JetRing).map (JetRing.truncation n) := by
  ext i j : 1
  simp only [Matrix.map_apply]
  ext m
  by_cases hm : Finsupp.degree m ≤ n
  · rw [JetRing.coeff_truncation_of_le hm, JetRing.coeff_truncation_of_le hm]
    rcases eq_or_ne m 0 with rfl | hm0
    · have h3 := congrArg (fun N => N i j) h0
      simpa [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply,
        apply_ite constantCoeff, coeff_zero_eq_constantCoeff] using h3
    · rw [hA i j m hm0 hm]
      rcases eq_or_ne i j with rfl | hij
      · rw [Matrix.one_apply_eq, coeff_one, if_neg hm0]
      · rw [Matrix.one_apply_ne hij, map_zero]
  · rw [JetRing.coeff_truncation_of_gt (not_le.mp hm),
      JetRing.coeff_truncation_of_gt (not_le.mp hm)]

/-- A power series with value `1` and no coefficients in nonzero degree up to `n`
  truncates to `1`. -/
lemma truncation_eq_one_of_coeff {n : ℕ} {f : JetRing} (h0 : constantCoeff f = 1)
    (hf : ∀ p : (Fin 1 ⊕ Fin 3) →₀ ℕ, p ≠ 0 → Finsupp.degree p ≤ n → coeff p f = 0) :
    JetRing.truncation n f = JetRing.truncation n (1 : JetRing) := by
  ext m
  by_cases hm : Finsupp.degree m ≤ n
  · rw [JetRing.coeff_truncation_of_le hm, JetRing.coeff_truncation_of_le hm]
    rcases eq_or_ne m 0 with rfl | hm0
    · simpa [coeff_zero_eq_constantCoeff] using h0
    · rw [hf m hm0 hm, coeff_one, if_neg hm0]
  · rw [JetRing.coeff_truncation_of_gt (not_le.mp hm),
      JetRing.coeff_truncation_of_gt (not_le.mp hm)]

/-!

## C. The comparison with the Maurer–Cartan filtration

-/

/-- The base-point Taylor data of the Maurer–Cartan form of a jet trivial to order `n`,
  read as power-series coefficients of its `su(3)` entries: they vanish below degree `n`. -/
lemma coeff_maurerCartanForm_toSU3Matrix_eq_zero_of_mem_truncationKer {U : JetGaugeGroupI}
    {n : ℕ} (hU : U ∈ localGaugeData.truncationKer n) (ρ : Fin 1 ⊕ Fin 3)
    {m : (Fin 1 ⊕ Fin 3) →₀ ℕ} (hm : Finsupp.degree m < n) (i j : Fin 3) :
    coeff m ((maurerCartanForm U ρ).toSU3Matrix i j) = 0 := by
  have h0 := hU.2 (Finsupp.toMultiset m) ρ (by
    rw [← degree_toFinsupp_eq_card, Finsupp.toMultiset_toFinsupp]; exact hm)
  have h1 := congrArg (fun a => GaugeAlgebra.toSU3Matrix a i j) h0
  simp only [localGaugeData_evalLie, localGaugeData_iteratedDeriv, localGaugeData_maurerCartan,
    GaugeAlgebra.zero_toSU3Matrix, Matrix.zero_apply] at h1
  rw [eval_toSU3Matrix_apply, iteratedDeriv_toSU3Matrix, Matrix.map_apply,
    constantCoeff_foldl_pderiv, Finsupp.toMultiset_toFinsupp] at h1
  exact (mul_eq_zero.mp h1).resolve_left (Nat.cast_ne_zero.mpr
    (Finset.prod_ne_zero_iff.mpr fun ν _ => Nat.factorial_ne_zero _))

/-- The `su(2)` entries of `coeff_maurerCartanForm_toSU3Matrix_eq_zero_of_mem_truncationKer`. -/
lemma coeff_maurerCartanForm_toSU2Matrix_eq_zero_of_mem_truncationKer {U : JetGaugeGroupI}
    {n : ℕ} (hU : U ∈ localGaugeData.truncationKer n) (ρ : Fin 1 ⊕ Fin 3)
    {m : (Fin 1 ⊕ Fin 3) →₀ ℕ} (hm : Finsupp.degree m < n) (i j : Fin 2) :
    coeff m ((maurerCartanForm U ρ).toSU2Matrix i j) = 0 := by
  have h0 := hU.2 (Finsupp.toMultiset m) ρ (by
    rw [← degree_toFinsupp_eq_card, Finsupp.toMultiset_toFinsupp]; exact hm)
  have h1 := congrArg (fun a => GaugeAlgebra.toSU2Matrix a i j) h0
  simp only [localGaugeData_evalLie, localGaugeData_iteratedDeriv, localGaugeData_maurerCartan,
    GaugeAlgebra.zero_toSU2Matrix, Matrix.zero_apply] at h1
  rw [eval_toSU2Matrix_apply, iteratedDeriv_toSU2Matrix, Matrix.map_apply,
    constantCoeff_foldl_pderiv, Finsupp.toMultiset_toFinsupp] at h1
  exact (mul_eq_zero.mp h1).resolve_left (Nat.cast_ne_zero.mpr
    (Finset.prod_ne_zero_iff.mpr fun ν _ => Nat.factorial_ne_zero _))

/-- The `u(1)` value of `coeff_maurerCartanForm_toSU3Matrix_eq_zero_of_mem_truncationKer`. -/
lemma coeff_maurerCartanForm_toU1Value_eq_zero_of_mem_truncationKer {U : JetGaugeGroupI}
    {n : ℕ} (hU : U ∈ localGaugeData.truncationKer n) (ρ : Fin 1 ⊕ Fin 3)
    {m : (Fin 1 ⊕ Fin 3) →₀ ℕ} (hm : Finsupp.degree m < n) :
    coeff m (maurerCartanForm U ρ).toU1Value = 0 := by
  have h0 := hU.2 (Finsupp.toMultiset m) ρ (by
    rw [← degree_toFinsupp_eq_card, Finsupp.toMultiset_toFinsupp]; exact hm)
  have h1 := congrArg GaugeAlgebra.toU1Value h0
  simp only [localGaugeData_evalLie, localGaugeData_iteratedDeriv, localGaugeData_maurerCartan,
    GaugeAlgebra.zero_toU1Value] at h1
  rw [eval_toU1Value_eq, iteratedDeriv_toU1Value, constantCoeff_foldl_pderiv,
    Finsupp.toMultiset_toFinsupp] at h1
  exact (mul_eq_zero.mp h1).resolve_left (Nat.cast_ne_zero.mpr
    (Finset.prod_ne_zero_iff.mpr fun ν _ => Nat.factorial_ne_zero _))

/-- Maurer–Cartan triangularity for the Standard Model: a jet trivial to order `n` in the
  sense of the Maurer–Cartan filtration truncates to the identity at order `n`. On each
  factor the radial relation `∂_ρ U = −i ω_ρ(U) U` and the Euler vanishing principle
  propagate the vanishing of the Maurer–Cartan coefficients below degree `n` to the
  vanishing of the coefficients of `U` in nonzero degree up to `n`. -/
theorem truncation_eq_one_of_mem_truncationKer {U : JetGaugeGroupI} {n : ℕ}
    (hU : U ∈ localGaugeData.truncationKer n) : truncation n U = 1 := by
  have hstar3 : star U.1.1 * U.1.1 = 1 := by
    have h1 := (Matrix.mem_specialUnitaryGroup_iff.mp U.1.2).1
    rwa [Matrix.mem_unitaryGroup_iff'] at h1
  have hstar2 : star U.2.1.1 * U.2.1.1 = 1 := by
    have h1 := (Matrix.mem_specialUnitaryGroup_iff.mp U.2.1.2).1
    rwa [Matrix.mem_unitaryGroup_iff'] at h1
  have hstar1 : star U.2.2.1 * U.2.2.1 = 1 := (Unitary.mem_iff.mp U.2.2.2).1
  -- the radial relation `∂_ρ U = (−i ω_ρ) U` on each factor
  have hd3 : ∀ ρ, U.1.1.map (pderiv ℂ ρ) =
      ((-Complex.I) • (maurerCartanForm U ρ).toSU3Matrix) * U.1.1 := fun ρ => by
    rw [maurerCartanForm_toSU3Matrix, smul_smul, neg_mul, Complex.I_mul_I, neg_neg,
      one_smul, mul_assoc, hstar3, mul_one]
  have hd2 : ∀ ρ, U.2.1.1.map (pderiv ℂ ρ) =
      ((-Complex.I) • (maurerCartanForm U ρ).toSU2Matrix) * U.2.1.1 := fun ρ => by
    rw [maurerCartanForm_toSU2Matrix, smul_smul, neg_mul, Complex.I_mul_I, neg_neg,
      one_smul, mul_assoc, hstar2, mul_one]
  have hd1 : ∀ ρ, pderiv ℂ ρ U.2.2.1 =
      ((-Complex.I) • (maurerCartanForm U ρ).toU1Value) * U.2.2.1 := fun ρ => by
    rw [maurerCartanForm_toU1Value, smul_smul, neg_mul, Complex.I_mul_I, neg_neg,
      one_smul, mul_assoc, hstar1, mul_one]
  have heval : U.eval = 1 := hU.1
  rw [← truncation_one n]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact matrix_map_truncation_eq_one (congrArg (fun p => (p.1 : Matrix (Fin 3) (Fin 3) ℂ)) heval)
      fun i j p hp hpn => coeff_entry_eq_zero_of_map_pderiv_eq_mul hd3
        (fun ρ q hq i j => by
          rw [Matrix.smul_apply, map_smul,
            coeff_maurerCartanForm_toSU3Matrix_eq_zero_of_mem_truncationKer hU ρ hq, smul_zero])
        i j hp hpn
  · exact matrix_map_truncation_eq_one
      (congrArg (fun p => (p.2.1 : Matrix (Fin 2) (Fin 2) ℂ)) heval)
      fun i j p hp hpn => coeff_entry_eq_zero_of_map_pderiv_eq_mul hd2
        (fun ρ q hq i j => by
          rw [Matrix.smul_apply, map_smul,
            coeff_maurerCartanForm_toSU2Matrix_eq_zero_of_mem_truncationKer hU ρ hq, smul_zero])
        i j hp hpn
  · exact truncation_eq_one_of_coeff (congrArg (fun p => (p.2.2 : ℂ)) heval)
      fun p hp hpn => coeff_eq_zero_of_pderiv_eq_mul hd1
        (fun ρ q hq => by
          rw [map_smul, coeff_maurerCartanForm_toU1Value_eq_zero_of_mem_truncationKer hU ρ hq,
            smul_zero])
        hp hpn

end JetGaugeGroupI

end StandardModel
