/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib
/-!
# The effective potential of the Higgs field — a self-contained tutorial

This file is a **stand-alone, Mathlib-only** version of the result
`StandardModel.HiggsField.EffectivePotential.apply_eq_sum_norm_pow` found in
`Physlib/Particles/StandardModel/HiggsBoson/EffectivePotential.lean`.

It depends on nothing but Mathlib, and is intended as a teaching example of the
following piece of mathematics:

> A real-valued function on a normed real vector space which is
> (a) a polynomial of bounded total degree in some fixed real coordinates and
> (b) invariant under changes that preserve the norm,
> is necessarily a polynomial in the *even* powers of the norm.

## The physics, and how it is abstracted

In the full development the Higgs field takes values in
`HiggsVec := EuclideanSpace ℂ (Fin 2)`, a `2`-dimensional complex (hence
`4`-dimensional real) vector space, and "invariance" means invariance under the
global action of the Standard-Model gauge group `SU(3) × SU(2) × U(1)`.

The only consequence of gauge invariance ever used to prove the final result is
that the potential takes the **same value on Higgs vectors of equal norm**
(gauge transformations are norm-preserving, and conversely any two vectors of
equal norm lie on the same gauge orbit). We therefore take *that* property as
the definition of `IsInvariant`, which removes every dependence on the gauge
group while keeping the statement and proof faithful.

To talk about polynomials we use the four real coordinates of a Higgs vector,
packaged as the `ℝ`-linear map `HiggsVec.toRealScalars`.

## Main result

* `EffectivePotential.apply_eq_sum_norm_pow` :
  a bounded-degree, norm-invariant potential `V` satisfies
  `V φ = ∑ m, c m • ‖φ‖ ^ (2 * m)` for some real coefficients `c`.

## Structure of the argument

1. **Decompose into homogeneous pieces.** Writing `V` as a polynomial `p` in the
   real coordinates and splitting `p` into its homogeneous components gives
   `V φ = ∑ₘ termₘ φ`, where each `termₘ` is homogeneous of degree `m`:
   `termₘ (t • φ) = tᵐ · termₘ φ`.
2. **Each piece is itself norm-invariant.** Comparing the polynomials in `t`
   given by `V (t • φ)` and `V (t • ψ)` for `‖φ‖ = ‖ψ‖` and matching
   coefficients shows `termₘ φ = termₘ ψ`.
3. **Norm-invariant + homogeneous ⇒ a constant times `‖φ‖ᵐ`.**
4. **Odd pieces vanish**, because `-φ` has the same norm as `φ`.
5. Collecting the surviving (even) pieces gives the result.
-/

noncomputable section

/-!
## The Higgs vector space and its real coordinates

`HiggsVec` is the target space of the Higgs field: complex Euclidean `2`-space.
As a real inner-product space it is `4`-dimensional, and `toRealScalars` records
those four real coordinates `(Re φ₀, Im φ₀, Re φ₁, Im φ₁)`.
-/

/-- The Higgs vector space: complex Euclidean space of dimension `2`. -/
abbrev HiggsVec : Type := EuclideanSpace ℂ (Fin 2)

namespace HiggsVec

/-- The four underlying real coordinates of a Higgs vector, as an `ℝ`-linear map. -/
def toRealScalars : HiggsVec →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun x := fun
    | 0 => (x 0).re
    | 1 => (x 0).im
    | 2 => (x 1).re
    | 3 => (x 1).im
  map_add' x y := by
    ext i
    fin_cases i <;> simp
  map_smul' a x := by
    ext i
    fin_cases i <;> simp

end HiggsVec

/-- A general (real-valued) potential of the Higgs field. -/
abbrev EffectivePotential : Type := HiggsVec → ℝ

namespace EffectivePotential

/-!
## A. Norm invariance

In the full development `V` is invariant under the gauge group; the single
consequence ever used is that `V` agrees on vectors of equal norm. We take this
as the definition.
-/

/-- A potential is *invariant* if it takes equal values on Higgs vectors of equal
norm. (In the Standard Model this is exactly invariance under the gauge group,
since gauge transformations preserve the norm and any two vectors of equal norm
share a gauge orbit.) -/
def IsInvariant (V : EffectivePotential) : Prop :=
  ∀ φ ψ : HiggsVec, ‖φ‖ = ‖ψ‖ → V φ = V ψ

namespace IsInvariant

/-- An invariant potential is equal on Higgs vectors with identical norms. -/
lemma eq_of_norm_eq {φ1 φ2 : HiggsVec} {V : EffectivePotential} (h : IsInvariant V)
    (hφ : ‖φ1‖ = ‖φ2‖) :
    V φ1 = V φ2 := h φ1 φ2 hφ

end IsInvariant

/-!
## B. Maximum mass dimension

`V` has maximum mass dimension `≤ n` when it is given, on the four real
coordinates, by a polynomial of total degree `≤ n`.
-/

/-- The proposition that the potential `V` has a maximum mass dimension
  less than or equal to `n` - also implying it is a polynomial. -/
def HasMaxMassDimLE (V : EffectivePotential) (n : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin 4) ℝ, (∀ φ : HiggsVec, V φ = p.eval φ.toRealScalars) ∧
    p.totalDegree ≤ n

/-- The polynomial associated to a potential `V` with a maximum mass dimension
  less than or equal to `n`. -/
def polynomial (V : EffectivePotential) {n : ℕ} (h : HasMaxMassDimLE V n) :
    MvPolynomial (Fin 4) ℝ := Classical.choose h

lemma polynomial_totalDegree {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n) :
    (polynomial V h).totalDegree ≤ n := (Classical.choose_spec h).2

lemma apply_eq_polynomial {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n)
    (φ : HiggsVec) : V φ = (polynomial V h).eval φ.toRealScalars := (Classical.choose_spec h).1 φ

/-!
## C. Terms of a given mass dimension

`termOfMassDim V h m` is the degree-`m` homogeneous part of the potential.
-/

/-- The part of a potential at a given mass-dimension. -/
def termOfMassDim (V : EffectivePotential) {n : ℕ} (h : HasMaxMassDimLE V n) (m : ℕ) :
    HiggsVec → ℝ := fun φ => ((polynomial V h).homogeneousComponent m).eval φ.toRealScalars

lemma termOfMassDim_eq_zero_of_max_lt {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n)
    {m : ℕ} (hm : n < m) (φ : HiggsVec) :
    termOfMassDim V h m φ = 0 := by
  simp only [termOfMassDim]
  rw [MvPolynomial.homogeneousComponent_eq_zero]
  simp only [map_zero]
  have h1 := polynomial_totalDegree h
  grind

lemma termOfMassDim_homogeneity {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n) (m : ℕ)
    (φ : HiggsVec) (t : ℝ) : termOfMassDim V h m (t • φ) = t ^ m * termOfMassDim V h m φ := by
  rw [termOfMassDim, termOfMassDim, map_smul, MvPolynomial.eval_eq', MvPolynomial.eval_eq',
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i, d i = m := by
    rw [MvPolynomial.support_homogeneousComponent, Finset.mem_filter] at hd
    rw [← Finsupp.degree_eq_sum]
    exact hd.2
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hdeg]
  ring

lemma apply_eq_sum_termOfMassDim {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n)
    (φ : HiggsVec) :
    V φ = ∑ m ∈ Finset.range (n + 1), termOfMassDim V h m φ := by
  rw [apply_eq_polynomial h, ← MvPolynomial.sum_homogeneousComponent (polynomial V h)]
  simp only [map_sum]
  change  ∑ x ∈ Finset.range ((V.polynomial h).totalDegree + 1), termOfMassDim V h x φ = _
  symm
  refine Finset.eventually_constant_sum ?_ ?_
  · intro m hm
    simp [termOfMassDim]
    rw [MvPolynomial.homogeneousComponent_eq_zero _ _ (by grind)]
    simp
  · have h1 := polynomial_totalDegree h
    grind

lemma apply_smul_eq_sum_termOfMassDim {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n)
    (φ : HiggsVec) (t : ℝ) :
    V (t • φ) = ∑ m ∈ Finset.range (n + 1), t ^ m * termOfMassDim V h m φ := by
  rw [apply_eq_sum_termOfMassDim h]
  congr
  funext m
  exact termOfMassDim_homogeneity h m φ t

/-- Each homogeneous part is itself norm-invariant.

The argument is purely about polynomials in one real variable `t`: for `φ`, `ψ`
of equal norm, `t • φ` and `t • ψ` again have equal norm, so invariance of `V`
makes the two polynomials `t ↦ V (t • φ)` and `t ↦ V (t • ψ)` agree everywhere;
matching their coefficients gives `termₘ φ = termₘ ψ`. This is the only place
that "invariance" is used in an essential way, and it needs nothing beyond
`‖t • φ‖ = ‖t • ψ‖`. -/
lemma termOfMassDim_isInvariant {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n)
    (m : ℕ) (hV : IsInvariant V) : IsInvariant (termOfMassDim V h m) := by
  intro φ ψ hnorm
  have hVeq (t : ℝ) : V (t • φ) = V (t • ψ) :=
    hV _ _ (by rw [norm_smul, norm_smul, hnorm])
  have h1 (t : ℝ) : ∑ k ∈ Finset.range (n + 1),
      t ^ k * (termOfMassDim V h k φ - termOfMassDim V h k ψ) = 0 := by
    have key : (∑ k ∈ Finset.range (n + 1), t ^ k * termOfMassDim V h k φ)
        - (∑ k ∈ Finset.range (n + 1), t ^ k * termOfMassDim V h k ψ) = 0 := by
      rw [← apply_smul_eq_sum_termOfMassDim h φ t,
        ← apply_smul_eq_sum_termOfMassDim h ψ t, hVeq t, sub_self]
    rw [← key, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [mul_sub]
  by_cases hmn : m ≤ n
  · have hp : (∑ k ∈ Finset.range (n + 1),
        Polynomial.C (termOfMassDim V h k φ - termOfMassDim V h k ψ) * Polynomial.X ^ k)
          = 0 := by
      apply Polynomial.funext
      intro x
      simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero]
      rw [← h1 x]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hcoeff := congrArg (fun p => p.coeff m) hp
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff, hmn,
      if_true, Polynomial.coeff_zero] at hcoeff
    exact sub_eq_zero.mp hcoeff
  · rw [termOfMassDim_eq_zero_of_max_lt h (not_le.mp hmn),
      termOfMassDim_eq_zero_of_max_lt h (not_le.mp hmn)]

lemma termOfMassDim_eq_mul_norm {V : EffectivePotential} {n : ℕ}
    (h : HasMaxMassDimLE V n) (m : ℕ) (hV : IsInvariant V) (φ : HiggsVec) :
    ∃ c, termOfMassDim V h m φ = c * ‖φ‖ ^ m := by
  use termOfMassDim V h m !₂[1, 0]
  rw [(termOfMassDim_isInvariant h m hV).eq_of_norm_eq (φ2 := ‖φ‖ • !₂[1, 0])
    (by simp [PiLp.norm_eq_of_L2]), termOfMassDim_homogeneity h m !₂[1, 0] ‖φ‖]
  ring

lemma termOfMassDim_zero_of_odd {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n) (m : ℕ)
    (hV : IsInvariant V) (φ : HiggsVec) (hodd : Odd m)  :
    termOfMassDim V h m φ = 0 := by
  have h1 : termOfMassDim V h m φ  = termOfMassDim V h m ((-1 : ℝ) • φ) := by
    apply (termOfMassDim_isInvariant h m hV).eq_of_norm_eq
    simp
  rw [termOfMassDim_homogeneity h m φ (-1 : ℝ), hodd.neg_one_pow] at h1
  simp only [neg_mul, one_mul] at h1
  grind

/-!
## D. Potential in terms of the norm of the Higgs field

Collecting the (surviving, even) homogeneous pieces.
-/

lemma apply_eq_sum_even_termOfMassDim {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n)
    (hV : IsInvariant V) (φ : HiggsVec) :
    V φ = ∑ m ∈ Finset.range (n / 2 + 1), termOfMassDim V h (2 * m) φ := by
  rw [apply_eq_sum_termOfMassDim h, ← Finset.sum_filter_add_sum_filter_not
    (Finset.range (n + 1)) Even]
  have hodd : ∑ m ∈ (Finset.range (n + 1)).filter (fun m => ¬ Even m),
      termOfMassDim V h m φ = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    simp only [Finset.mem_filter] at hm
    exact termOfMassDim_zero_of_odd h m hV φ (Nat.not_even_iff_odd.mp hm.2)
  rw [hodd, add_zero]
  have hinj : ∀ x ∈ Finset.range (n / 2 + 1), ∀ y ∈ Finset.range (n / 2 + 1),
      2 * x = 2 * y → x = y := fun x _ y _ hxy => by omega
  have hset : (Finset.range (n / 2 + 1)).image (fun k => 2 * k)
      = (Finset.range (n + 1)).filter Even := by
    ext a
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_filter, Nat.even_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨by omega, by omega⟩
    · rintro ⟨ha, hae⟩
      exact ⟨a / 2, by omega, by omega⟩
  rw [← hset, Finset.sum_image hinj]

lemma apply_eq_sum_even_termOfMassDim_fin {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n)
    (hV : IsInvariant V) (φ : HiggsVec) :
    V φ = ∑ m : Fin (n/2 + 1), termOfMassDim V h (2 * m) φ := by
  rw [apply_eq_sum_even_termOfMassDim h hV φ, Finset.sum_range]

/-- The potential is equal to the sum of norms to even powers. -/
lemma apply_eq_sum_norm_pow {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n)
    (hV : IsInvariant V) (φ : HiggsVec) :
    ∃ c : Fin (n/2 + 1) → ℝ, V φ = ∑ m, c m • ‖φ‖ ^ (2 * m.1) := by
  use fun m' => Classical.choose (termOfMassDim_eq_mul_norm h (2 * m'.1) hV φ)
  rw [apply_eq_sum_even_termOfMassDim_fin h hV φ]
  congr 1
  ext m
  simpa using Classical.choose_spec (termOfMassDim_eq_mul_norm h (2 * m.1) hV φ)

end EffectivePotential

end
