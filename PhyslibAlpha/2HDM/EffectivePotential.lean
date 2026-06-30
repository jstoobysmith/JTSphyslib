/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.BeyondTheStandardModel.TwoHDM.GramMatrix
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.RingTheory.MvPolynomial.Tower
public import Mathlib.Analysis.Real.Pi.Irrational
public import PhyslibAlpha.«2HDM».Determinant
public import PhyslibAlpha.«2HDM».OrbitRepresentative
public import PhyslibAlpha.«2HDM».GaugeSlice
public import PhyslibAlpha.«2HDM».ChargeBalance
/-!
# The effective potential of the two Higgs doublet model


-/

@[expose] public section

noncomputable section

namespace TwoHiggsDoublet
open InnerProductSpace
open StandardModel

open SpaceTime


/-- A general potential of the Higgs field. -/
abbrev EffectivePotential : Type := TwoHiggsDoublet → ℝ

namespace EffectivePotential

/-!

## A. The invariance of the general potential under the gauge group

-/

/-- The proposition that the general potential is invariant under
  the global action of the gauge group. -/
def IsInvariant (V : EffectivePotential) : Prop :=
  ∀ (g : GaugeGroupI), ∀ (φ : TwoHiggsDoublet), V (g • φ) = V φ

namespace IsInvariant

/-- An invariant potential is equal on gauge orbits. -/
lemma eq_on_orbits {φ1 φ2 : TwoHiggsDoublet} {V : EffectivePotential} (h : IsInvariant V)
    (hφ : φ1 ∈ MulAction.orbit GaugeGroupI  φ2) :
    V φ1 = V φ2 := by
  obtain ⟨g, hg⟩ := hφ
  rw [← hg]
  exact h g φ2

/-- An invariant potential is equal on Higgs vectors with identical Gram vectors. -/
lemma eq_of_gramVector_eq {φ1 φ2 : TwoHiggsDoublet} {V : EffectivePotential} (h : IsInvariant V)
    (hφ : φ1.gramVector = φ2.gramVector) :
    V φ1 = V φ2 := h.eq_on_orbits <| (mem_orbit_gaugeGroupI_iff_gramVector φ1 φ2).mpr hφ

end IsInvariant

/-!

## B. Maximum mass dimension

-/

/-- The proposition that the potential `V` has a maximum mass dimension
  less then or equal to `n` - also implying it is a polynomial. -/
def HasMaxMassDimLE (V : EffectivePotential) (n : ℕ) : Prop :=
  ∃ p : MvPolynomial (Module.Dual ℝ TwoHiggsDoublet) ℝ, (∀ φ : TwoHiggsDoublet, V φ = p.eval
   (fun i => i φ) ) ∧ p.totalDegree ≤ n

/-- A polynomial potential, restricted along any real-linear parametrisation `L` of field
  configurations, is a genuine polynomial in the parameters. This is the bookkeeping that lets the
  potential be evaluated on the field components of a gauge slice. -/
lemma HasMaxMassDimLE.exists_comp_linear_poly {V : EffectivePotential} {n : ℕ}
    (h : HasMaxMassDimLE V n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → ℝ) →ₗ[ℝ] TwoHiggsDoublet) :
    ∃ P : MvPolynomial ι ℝ, ∀ a : ι → ℝ, V (L a) = P.eval a := by
  obtain ⟨p, hp, -⟩ := h
  refine ⟨MvPolynomial.aeval
    (fun i => ∑ k : ι, MvPolynomial.C (i (L (Pi.single k 1))) * MvPolynomial.X k) p, fun a => ?_⟩
  have key : (fun i : Module.Dual ℝ TwoHiggsDoublet => i (L a))
      = fun i => MvPolynomial.eval a
        (∑ k : ι, MvPolynomial.C (i (L (Pi.single k 1))) * MvPolynomial.X k) := by
    funext i
    have ha : a = ∑ k : ι, a k • (Pi.single k 1 : ι → ℝ) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq]
    rw [map_sum]
    conv_lhs => rw [ha, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [map_smul, map_smul, MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      smul_eq_mul, mul_comm]
  rw [hp, key, MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq, ← MvPolynomial.eval_assoc]
  rfl

open MvPolynomial in
/-- The Cartan hypercharge rotation of the slice parameters, as a substitution of the polynomial
  variables. -/
noncomputable def rotSubst (u : unitary ℂ) : Fin 6 → MvPolynomial (Fin 6) ℝ :=
  ![C (u : ℂ).re * X 0 - C (u : ℂ).im * X 1, C (u : ℂ).im * X 0 + C (u : ℂ).re * X 1,
    C (u : ℂ).re * X 2 - C (u : ℂ).im * X 3, C (u : ℂ).im * X 2 + C (u : ℂ).re * X 3,
    C (u : ℂ).re * X 4 + C (u : ℂ).im * X 5, C (u : ℂ).re * X 5 - C (u : ℂ).im * X 4]

open MvPolynomial in
lemma eval_rotSubst (u : unitary ℂ) (a : Fin 6 → ℝ) :
    (fun k => MvPolynomial.eval a (rotSubst u k)) = cartanRotParam u a := by
  funext k
  fin_cases k <;>
    simp [rotSubst, cartanRotParam, Complex.mul_re, Complex.mul_im] <;> ring

open MvPolynomial in
/-- Gauge (Cartan) invariance of the potential forces the slice polynomial to be invariant under the
  hypercharge rotation of its variables. -/
lemma aeval_rotSubst_eq {V : EffectivePotential} (hI : IsInvariant V)
    {P : MvPolynomial (Fin 6) ℝ} (hP : ∀ a, V (sliceR a) = P.eval a) (u : unitary ℂ) :
    aeval (rotSubst u) P = P := by
  apply MvPolynomial.funext
  intro a
  have hcomp : eval a (aeval (rotSubst u) P) = P.eval (fun k => eval a (rotSubst u k)) := by
    rw [aeval_def, algebraMap_eq, ← MvPolynomial.eval_assoc]
    rfl
  rw [hcomp, eval_rotSubst, ← hP (cartanRotParam u a), ← gaugeCartan_smul_sliceR,
    hI (StandardModel.GaugeGroupI.gaugeCartan u), hP a]

open MvPolynomial in
/-- The residual `U(1)` rotation of the perpendicular parameter, as a substitution. -/
noncomputable def resSubst (c : unitary ℂ) : Fin 6 → MvPolynomial (Fin 6) ℝ :=
  ![X 0, X 1, X 2, X 3,
    C (((c : ℂ) ^ 6).re) * X 4 - C (((c : ℂ) ^ 6).im) * X 5,
    C (((c : ℂ) ^ 6).im) * X 4 + C (((c : ℂ) ^ 6).re) * X 5]

open MvPolynomial in
lemma eval_resSubst (c : unitary ℂ) (a : Fin 6 → ℝ) :
    (fun k => MvPolynomial.eval a (resSubst c k)) = resRotParam c a := by
  funext k
  fin_cases k <;> simp [resSubst, resRotParam, Complex.mul_re, Complex.mul_im] <;> ring

open MvPolynomial in
/-- Gauge (residual `U(1)`) invariance forces the slice polynomial to be invariant under the
  perpendicular rotation of its variables. -/
lemma aeval_resSubst_eq {V : EffectivePotential} (hI : IsInvariant V)
    {P : MvPolynomial (Fin 6) ℝ} (hP : ∀ a, V (sliceR a) = P.eval a) (c : unitary ℂ) :
    aeval (resSubst c) P = P := by
  apply MvPolynomial.funext
  intro a
  have hcomp : eval a (aeval (resSubst c) P) = P.eval (fun k => eval a (resSubst c k)) := by
    rw [aeval_def, algebraMap_eq, ← MvPolynomial.eval_assoc]; rfl
  rw [hcomp, eval_resSubst, ← hP (resRotParam c a), ← ofU1Subgroup_smul_sliceR,
    hI (StandardModel.GaugeGroupI.ofU1Subgroup c), hP a]

open MvPolynomial in
/-- Change to hypercharge eigen-coordinates: `aₖ` in terms of `z, z̄, w₀, w̄₀, w₁, w̄₁`
  (indices `0..5`). This diagonalises the gauge-torus rotation into a scaling. -/
noncomputable def cplxEigen : Fin 6 → MvPolynomial (Fin 6) ℂ :=
  ![(X 0 + X 1) * C (1 / 2), (X 0 - X 1) * C (-Complex.I / 2),
    (X 2 + X 3) * C (1 / 2), (X 2 - X 3) * C (-Complex.I / 2),
    (X 4 + X 5) * C (1 / 2), (X 4 - X 5) * C (-Complex.I / 2)]

open MvPolynomial in
/-- The Cartan hypercharge, diagonal in eigen-coordinates: charges `(1,-1,1,-1,-1,1)`. -/
noncomputable def diagCartan (u : unitary ℂ) : Fin 6 → MvPolynomial (Fin 6) ℂ :=
  ![C (u : ℂ) * X 0, C (star (u : ℂ)) * X 1, C (u : ℂ) * X 2, C (star (u : ℂ)) * X 3,
    C (star (u : ℂ)) * X 4, C (u : ℂ) * X 5]

open MvPolynomial in
/-- The residual `U(1)`, diagonal in eigen-coordinates: only the perpendicular pair is charged. -/
noncomputable def diagRes (c : unitary ℂ) : Fin 6 → MvPolynomial (Fin 6) ℂ :=
  ![X 0, X 1, X 2, X 3, C ((c : ℂ) ^ 6) * X 4, C (star ((c : ℂ) ^ 6)) * X 5]

open MvPolynomial in
/-- Conjugation identity: the diagonal Cartan scaling, pulled back through the eigen-coordinate
  change, is the (complexified) Cartan rotation substitution. -/
lemma bind₁_diagCartan_cplxEigen (u : unitary ℂ) (k : Fin 6) :
    bind₁ (diagCartan u) (cplxEigen k)
      = bind₁ cplxEigen (map (algebraMap ℝ ℂ) (rotSubst u k)) := by
  apply MvPolynomial.funext
  intro x
  fin_cases k <;>
    simp only [cplxEigen, diagCartan, rotSubst, Matrix.cons_val, Fin.isValue,
      map_add, map_sub, map_mul, MvPolynomial.bind₁_X_right,
      MvPolynomial.bind₁_C_right, MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.algebraMap_eq,
      MvPolynomial.eval_X, MvPolynomial.eval_C] <;>
    (apply Complex.ext <;>
      simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.star_def, Complex.conj_re, Complex.conj_im] <;> ring)

open MvPolynomial in
/-- Conjugation identity for the residual `U(1)`. -/
lemma bind₁_diagRes_cplxEigen (c : unitary ℂ) (k : Fin 6) :
    bind₁ (diagRes c) (cplxEigen k)
      = bind₁ cplxEigen (map (algebraMap ℝ ℂ) (resSubst c k)) := by
  apply MvPolynomial.funext
  intro x
  simp only [diagRes, resSubst]
  generalize (c : ℂ) ^ 6 = μ
  fin_cases k <;>
    simp only [cplxEigen, Matrix.cons_val, Fin.isValue,
      map_add, map_sub, map_mul, MvPolynomial.bind₁_X_right,
      MvPolynomial.bind₁_C_right, MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.algebraMap_eq,
      MvPolynomial.eval_X, MvPolynomial.eval_C] <;>
    (apply Complex.ext <;>
      simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.star_def, Complex.conj_re, Complex.conj_im] <;> ring)

/-- The Cartan hypercharges of `z, z̄, w₀, w̄₀, w₁, w̄₁`. -/
def chargeA : Fin 6 → ℤ := ![1, -1, 1, -1, -1, 1]

/-- The residual-`U(1)` hypercharges (only the perpendicular pair is charged). -/
def chargeB : Fin 6 → ℤ := ![0, 0, 0, 0, 1, -1]

open MvPolynomial in
/-- The slice potential, complexified and written in hypercharge eigen-coordinates. -/
noncomputable def Qslice (P : MvPolynomial (Fin 6) ℝ) : MvPolynomial (Fin 6) ℂ :=
  bind₁ cplxEigen (map (algebraMap ℝ ℂ) P)

open MvPolynomial in
/-- The Cartan diagonal in the charge form consumed by the charge-balancing engine. -/
lemma diagCartan_eq (u : unitary ℂ) :
    diagCartan u = fun i => C ((u : ℂ) ^ (chargeA i)) * X i := by
  have hinv : star (u : ℂ) = (u : ℂ) ^ (-1 : ℤ) := by
    rw [zpow_neg_one]; exact (inv_eq_of_mul_eq_one_right u.2.2).symm
  funext i
  fin_cases i <;> simp [diagCartan, chargeA, hinv]

open MvPolynomial in
/-- The residual diagonal in the charge form consumed by the engine. -/
lemma diagRes_eq (c : unitary ℂ) :
    diagRes c = fun i => C (((c : ℂ) ^ 6) ^ (chargeB i)) * X i := by
  have hinv : star ((c : ℂ) ^ 6) = ((c : ℂ) ^ 6) ^ (-1 : ℤ) := by
    rw [zpow_neg_one]
    refine (inv_eq_of_mul_eq_one_right ?_).symm
    rw [star_pow, ← mul_pow, c.2.2, one_pow]
  funext i
  fin_cases i <;> simp [diagRes, chargeB, hinv]

open MvPolynomial in
/-- In eigen-coordinates, the Cartan hypercharge acts by the diagonal scaling, and the slice
  potential is invariant under it. -/
lemma bind₁_diagCartan_Qslice {V : EffectivePotential} (hI : IsInvariant V)
    {P : MvPolynomial (Fin 6) ℝ} (hP : ∀ a, V (sliceR a) = P.eval a) (u : unitary ℂ) :
    bind₁ (diagCartan u) (Qslice P) = Qslice P := by
  simp only [Qslice]
  rw [bind₁_bind₁]
  simp only [bind₁_diagCartan_cplxEigen]
  rw [← bind₁_bind₁, ← map_bind₁]
  congr 2
  exact aeval_rotSubst_eq hI hP u

open MvPolynomial in
/-- Likewise for the residual `U(1)`. -/
lemma bind₁_diagRes_Qslice {V : EffectivePotential} (hI : IsInvariant V)
    {P : MvPolynomial (Fin 6) ℝ} (hP : ∀ a, V (sliceR a) = P.eval a) (c : unitary ℂ) :
    bind₁ (diagRes c) (Qslice P) = Qslice P := by
  simp only [Qslice]
  rw [bind₁_bind₁]
  simp only [bind₁_diagRes_cplxEigen]
  rw [← bind₁_bind₁, ← map_bind₁]
  congr 2
  exact aeval_resSubst_eq hI hP c

/-- There is a gauge phase of infinite order (`exp i`), needed to run charge balancing. -/
lemma exists_infiniteOrder_unitary :
    ∃ ω : unitary ℂ, ∀ n : ℤ, (ω : ℂ) ^ n = 1 → n = 0 := by
  have key : star (Complex.exp Complex.I) * Complex.exp Complex.I = 1 := by
    rw [Complex.star_def, ← Complex.exp_conj, Complex.conj_I, ← Complex.exp_add]; simp
  have key2 : Complex.exp Complex.I * star (Complex.exp Complex.I) = 1 := by
    rw [Complex.star_def, ← Complex.exp_conj, Complex.conj_I, ← Complex.exp_add]; simp
  refine ⟨⟨Complex.exp Complex.I, key, key2⟩, fun n hn => ?_⟩
  simp only at hn
  rw [← Complex.exp_int_mul, Complex.exp_eq_one_iff] at hn
  obtain ⟨k, hk⟩ := hn
  have hc : (n : ℂ) = (k : ℂ) * (2 * Real.pi) := by
    have hI : (Complex.I) ≠ 0 := Complex.I_ne_zero
    apply mul_right_cancel₀ hI
    rw [hk]; ring
  have hr : (n : ℝ) = (k : ℝ) * (2 * Real.pi) := by exact_mod_cast hc
  rcases eq_or_ne k 0 with hk0 | hk0
  · simp [hk0] at hr; exact_mod_cast hr
  · exfalso
    have h2k : (2 * (k : ℝ)) ≠ 0 := by
      simp only [mul_ne_zero_iff]; exact ⟨two_ne_zero, by exact_mod_cast hk0⟩
    have hpi : Real.pi = (n : ℝ) / (2 * (k : ℝ)) := by rw [eq_div_iff h2k, hr]; ring
    exact irrational_pi.ne_rat ((n : ℚ) / (2 * (k : ℚ))) (by rw [hpi]; push_cast; ring)

open MvPolynomial in
/-- **Hypercharge balancing.** Every monomial of the slice potential `Qslice P` (in eigen-
  coordinates) that carries nonzero Cartan or residual hypercharge has vanishing coefficient. -/
lemma coeff_Qslice_eq_zero {V : EffectivePotential} (hI : IsInvariant V)
    {P : MvPolynomial (Fin 6) ℝ} (hP : ∀ a, V (sliceR a) = P.eval a) (m : Fin 6 →₀ ℕ)
    (hm : (∑ i ∈ m.support, (m i : ℤ) * chargeA i ≠ 0) ∨
          (∑ i ∈ m.support, (m i : ℤ) * chargeB i ≠ 0)) :
    coeff m (Qslice P) = 0 := by
  obtain ⟨ω, hω⟩ := exists_infiniteOrder_unitary
  have hω0 : (ω : ℂ) ≠ 0 := by intro h; have := ω.2.1; rw [h] at this; simp at this
  rcases hm with hmA | hmB
  · refine coeff_eq_zero_of_charge_ne_zero chargeA (ω : ℂ) hω0 hω ?_ hmA
    have h := bind₁_diagCartan_Qslice hI hP ω
    rwa [diagCartan_eq] at h
  · have hω6 : ((ω : ℂ) ^ 6) ≠ 0 := pow_ne_zero 6 hω0
    have hroot6 : ∀ n : ℤ, ((ω : ℂ) ^ 6) ^ n = 1 → n = 0 := by
      intro n hn
      rw [← zpow_natCast (ω : ℂ) 6, ← zpow_mul] at hn
      have := hω _ hn; omega
    refine coeff_eq_zero_of_charge_ne_zero chargeB ((ω : ℂ) ^ 6) hω6 hroot6 ?_ hmB
    have h := bind₁_diagRes_Qslice hI hP ω
    rwa [diagRes_eq] at h

/-!

## C'. Generation of neutral monomials by the bilinears

The hypercharge-neutral monomials of `Qslice P` are exactly the products of the five neutral
quadratic bilinears `z z̄, w₀ w̄₀, z w̄₀, z̄ w₀, w₁ w̄₁`. This is the (abelian) generation step:
combined Cartan- and residual-neutrality of a monomial forces it to be a product of these five,
because every charged variable carries a unit Cartan charge and the residual charges come in an
exact `±1` pair.

-/

open MvPolynomial in
/-- The five hypercharge-neutral quadratic bilinears in eigen-coordinates:
  `z z̄`, `w₀ w̄₀`, `z w̄₀`, `z̄ w₀`, `w₁ w̄₁`. -/
noncomputable def bilin : Fin 5 → MvPolynomial (Fin 6) ℂ :=
  ![X 0 * X 1, X 2 * X 3, X 0 * X 3, X 1 * X 2, X 4 * X 5]

/-- The charge of a monomial, summed over the whole index set, equals the sum over its support. -/
lemma charge_univ_eq_support (w : Fin 6 → ℤ) (m : Fin 6 →₀ ℕ) :
    ∑ i, (m i : ℤ) * w i = ∑ i ∈ m.support, (m i : ℤ) * w i := by
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  rw [Finsupp.notMem_support_iff.mp hi]; simp

/-- A charge sum is additive in the monomial. -/
lemma chargeSum_add (w : Fin 6 → ℤ) (a b : Fin 6 →₀ ℕ) :
    ∑ k, ((a + b) k : ℤ) * w k = (∑ k, (a k : ℤ) * w k) + ∑ k, (b k : ℤ) * w k := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finsupp.add_apply]; push_cast; ring

/-- The charge sum of a single generator is the charge of that variable. -/
lemma chargeSum_single (w : Fin 6 → ℤ) (i : Fin 6) :
    ∑ k, ((Finsupp.single i (1 : ℕ)) k : ℤ) * w k = w i := by
  simp [Finsupp.single_apply, ite_mul, Finset.sum_ite_eq]

open MvPolynomial in
/-- **Generation.** Every hypercharge-neutral monomial is a product of the five bilinears. -/
lemma monomial_mem_adjoin_bilin (m : Fin 6 →₀ ℕ)
    (hA : ∑ i, (m i : ℤ) * chargeA i = 0) (hB : ∑ i, (m i : ℤ) * chargeB i = 0) :
    monomial m (1 : ℂ) ∈ Algebra.adjoin ℂ (Set.range bilin) := by
  suffices H : ∀ n : ℕ, ∀ m : Fin 6 →₀ ℕ, (∑ i, m i) = n →
      (∑ i, (m i : ℤ) * chargeA i = 0) → (∑ i, (m i : ℤ) * chargeB i = 0) →
      monomial m (1 : ℂ) ∈ Algebra.adjoin ℂ (Set.range bilin) by
    exact H (∑ i, m i) m rfl hA hB
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro m hsum hA hB
    -- The reduction step: pair up two variables whose bilinear is a generator.
    have reduce : ∀ i j : Fin 6, i ≠ j → m i ≠ 0 → m j ≠ 0 →
        X i * X j ∈ Algebra.adjoin ℂ (Set.range bilin) →
        chargeA i + chargeA j = 0 → chargeB i + chargeB j = 0 →
        monomial m (1 : ℂ) ∈ Algebra.adjoin ℂ (Set.range bilin) := by
      intro i j hij hmi hmj hgen hcA hcB
      have hle : Finsupp.single i 1 + Finsupp.single j 1 ≤ m := by
        intro k
        rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
        by_cases h1 : i = k
        · by_cases h2 : j = k
          · exact absurd (h1.trans h2.symm) hij
          · rw [if_pos h1, if_neg h2]; subst h1; simpa using Nat.one_le_iff_ne_zero.mpr hmi
        · by_cases h2 : j = k
          · rw [if_neg h1, if_pos h2]; subst h2; simpa using Nat.one_le_iff_ne_zero.mpr hmj
          · rw [if_neg h1, if_neg h2]; simp
      set m' := m - (Finsupp.single i 1 + Finsupp.single j 1) with hm'def
      have hdecomp : m = (Finsupp.single i 1 + Finsupp.single j 1) + m' := by
        rw [hm'def, add_tsub_cancel_of_le hle]
      -- m' is still neutral
      have hA' : ∑ k, (m' k : ℤ) * chargeA k = 0 := by
        have h := hA
        rw [hdecomp, chargeSum_add, chargeSum_add, chargeSum_single, chargeSum_single] at h
        omega
      have hB' : ∑ k, (m' k : ℤ) * chargeB k = 0 := by
        have h := hB
        rw [hdecomp, chargeSum_add, chargeSum_add, chargeSum_single, chargeSum_single] at h
        omega
      -- the degree drops by 2
      have hsum' : ∑ k, m' k < n := by
        have e : (∑ k, m k) = (∑ k, (Finsupp.single i 1) k) + (∑ k, (Finsupp.single j 1) k)
            + ∑ k, m' k := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro k _
          rw [← Finsupp.add_apply, ← Finsupp.add_apply, ← hdecomp]
        have e1 : ∑ k, (Finsupp.single i 1) k = 1 := by
          simp [Finsupp.single_apply, Finset.sum_ite_eq]
        have e2 : ∑ k, (Finsupp.single j 1) k = 1 := by
          simp [Finsupp.single_apply, Finset.sum_ite_eq]
        rw [hsum, e1, e2] at e
        omega
      -- factor and recurse
      have hfact : monomial m (1 : ℂ) = (X i * X j) * monomial m' 1 := by
        rw [hdecomp,
          show (X i : MvPolynomial (Fin 6) ℂ) = monomial (Finsupp.single i 1) 1 from
            by rw [← X_pow_eq_monomial, pow_one],
          show (X j : MvPolynomial (Fin 6) ℂ) = monomial (Finsupp.single j 1) 1 from
            by rw [← X_pow_eq_monomial, pow_one],
          monomial_mul, monomial_mul, one_mul, one_mul, add_assoc]
      rw [hfact]
      exact Subalgebra.mul_mem _ hgen (ih (∑ k, m' k) hsum' m' rfl hA' hB')
    -- main case split
    rcases eq_or_ne n 0 with hn0 | hn0
    · -- degree zero: m = 0, monomial is 1
      have hm0 : m = 0 := by
        ext k
        have hk : m k ≤ ∑ i, m i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
        rw [hsum, hn0] at hk
        simpa using Nat.le_zero.mp hk
      rw [hm0]
      have h1 : monomial (0 : Fin 6 →₀ ℕ) (1 : ℂ) = 1 := by simp
      rw [h1]; exact Subalgebra.one_mem _
    · -- positive degree: find a neutral pair
      rcases eq_or_ne (m 4) 0 with h4 | h4
      · -- m 4 = 0; then m 5 = 0 by residual neutrality
        have h5 : m 5 = 0 := by
          have h := hB
          simp [chargeB, Fin.sum_univ_six] at h
          omega
        -- Cartan neutrality on {0,1,2,3}: m0 + m2 = m1 + m3
        have hcart : (m 0 : ℤ) + (m 2 : ℤ) = (m 1 : ℤ) + (m 3 : ℤ) := by
          have h := hA
          simp [chargeA, Fin.sum_univ_six] at h
          omega
        -- total degree on {0,1,2,3} is n > 0
        have hposL : 0 < m 0 + m 2 := by
          rcases Nat.eq_zero_or_pos (m 0 + m 2) with hc | hc
          · exfalso
            have h02 : m 0 = 0 ∧ m 2 = 0 := by omega
            have h13 : m 1 = 0 ∧ m 3 = 0 := by omega
            have hz : ∑ i, m i = 0 := by
              simp [Fin.sum_univ_six, h02.1, h02.2, h13.1, h13.2, h4, h5]
            rw [hsum] at hz; exact hn0 hz
          · exact hc
        have hposR : 0 < m 1 + m 3 := by omega
        -- choose a positive index in {0,2} and one in {1,3}
        rcases Nat.eq_zero_or_pos (m 0) with hm0 | hm0
        · -- m 0 = 0, so m 2 > 0
          have hm2 : m 2 ≠ 0 := by omega
          rcases Nat.eq_zero_or_pos (m 1) with hm1 | hm1
          · -- m 1 = 0, so m 3 > 0 : pair (2,3) -> bilin 1
            have hm3 : m 3 ≠ 0 := by omega
            refine reduce 2 3 (by decide) hm2 hm3 ?_ (by decide) (by decide)
            exact Algebra.subset_adjoin ⟨1, rfl⟩
          · -- m 1 > 0 : pair (1,2) -> bilin 3
            refine reduce 1 2 (by decide) (by omega) hm2 ?_ (by decide) (by decide)
            exact Algebra.subset_adjoin ⟨3, rfl⟩
        · -- m 0 > 0
          rcases Nat.eq_zero_or_pos (m 1) with hm1 | hm1
          · -- m 1 = 0, so m 3 > 0 : pair (0,3) -> bilin 2
            have hm3 : m 3 ≠ 0 := by omega
            refine reduce 0 3 (by decide) (by omega) hm3 ?_ (by decide) (by decide)
            exact Algebra.subset_adjoin ⟨2, rfl⟩
          · -- m 1 > 0 : pair (0,1) -> bilin 0
            refine reduce 0 1 (by decide) (by omega) (by omega) ?_ (by decide) (by decide)
            exact Algebra.subset_adjoin ⟨0, rfl⟩
      · -- m 4 > 0; then m 5 > 0 : pair (4,5) -> bilin 4
        have h5 : m 5 ≠ 0 := by
          have h := hB
          simp [chargeB, Fin.sum_univ_six] at h
          omega
        refine reduce 4 5 (by decide) h4 h5 ?_ (by decide) (by decide)
        exact Algebra.subset_adjoin ⟨4, rfl⟩

open MvPolynomial in
/-- The slice potential lies in the subalgebra generated by the five bilinears: every monomial that
  survives is hypercharge-neutral, hence a product of the bilinears. -/
lemma Qslice_mem_adjoin_bilin {V : EffectivePotential} (hI : IsInvariant V)
    {P : MvPolynomial (Fin 6) ℝ} (hP : ∀ a, V (sliceR a) = P.eval a) :
    Qslice P ∈ Algebra.adjoin ℂ (Set.range bilin) := by
  rw [(Qslice P).as_sum]
  apply Subalgebra.sum_mem
  intro m hm
  have hcoeff : coeff m (Qslice P) ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  have hsuppA : ∑ i ∈ m.support, (m i : ℤ) * chargeA i = 0 := by
    by_contra h0
    exact hcoeff (coeff_Qslice_eq_zero hI hP m (Or.inl h0))
  have hsuppB : ∑ i ∈ m.support, (m i : ℤ) * chargeB i = 0 := by
    by_contra h0
    exact hcoeff (coeff_Qslice_eq_zero hI hP m (Or.inr h0))
  have hmono : monomial m (1 : ℂ) ∈ Algebra.adjoin ℂ (Set.range bilin) :=
    monomial_mem_adjoin_bilin m
      ((charge_univ_eq_support chargeA m).trans hsuppA)
      ((charge_univ_eq_support chargeB m).trans hsuppB)
  have hrw : monomial m (coeff m (Qslice P)) = C (coeff m (Qslice P)) * monomial m 1 := by
    rw [C_mul_monomial, mul_one]
  rw [hrw]
  exact Subalgebra.mul_mem _
    (by rw [← MvPolynomial.algebraMap_eq]; exact Subalgebra.algebraMap_mem _ _) hmono

open MvPolynomial in
/-- Consequently the complexified slice potential is `aeval bilin G` for some polynomial `G` in the
  five bilinears. -/
lemma exists_aeval_bilin {V : EffectivePotential} (hI : IsInvariant V)
    {P : MvPolynomial (Fin 6) ℝ} (hP : ∀ a, V (sliceR a) = P.eval a) :
    ∃ G : MvPolynomial (Fin 5) ℂ, aeval bilin G = Qslice P := by
  have h := Qslice_mem_adjoin_bilin hI hP
  rw [Algebra.adjoin_range_eq_range_aeval ℂ bilin] at h
  obtain ⟨G, hG⟩ := h
  exact ⟨G, hG⟩

/-! ### Evaluating at the eigen-point of a representative -/

/-- The slice parameters realising `repHiggs X` as a point of the slice family. -/
def aRep (X : Fin 4 → ℝ) : Fin 6 → ℝ := ![X 0, 0, X 1, X 2, X 3, 0]

lemma repHiggs_eq_sliceR (X : Fin 4 → ℝ) : repHiggs X = sliceR (aRep X) := by
  rw [repHiggs_eq_sliceHiggs, sliceR_apply]
  simp [aRep]

/-- The hypercharge eigen-point `(z, z̄, w₀, w̄₀, w₁, w̄₁)` of `repHiggs X`: here `z = X₀` is real,
  `w₀ = X₁ + i X₂` and `w₁ = X₃` is real. -/
noncomputable def eigenPt (X : Fin 4 → ℝ) : Fin 6 → ℂ :=
  ![(X 0 : ℂ), (X 0 : ℂ), (X 1 : ℂ) + Complex.I * (X 2 : ℂ), (X 1 : ℂ) - Complex.I * (X 2 : ℂ),
    (X 3 : ℂ), (X 3 : ℂ)]

open MvPolynomial in
/-- The eigen-coordinate change sends the eigen-point of `repHiggs X` back to its slice parameters. -/
lemma aeval_cplxEigen_eigenPt (X : Fin 4 → ℝ) (k : Fin 6) :
    aeval (eigenPt X) (cplxEigen k) = algebraMap ℝ ℂ (aRep X k) := by
  fin_cases k <;>
    simp only [cplxEigen, eigenPt, aRep, Matrix.cons_val, Fin.isValue, map_add, map_sub, map_mul,
      aeval_X, aeval_C, MvPolynomial.algebraMap_eq] <;>
    (apply Complex.ext <;>
      simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring)

open MvPolynomial in
/-- The complexified slice potential, evaluated at the eigen-point of `repHiggs X`, returns the real
  value `V (repHiggs X)`. -/
lemma eval_Qslice_eigenPt (P : MvPolynomial (Fin 6) ℝ) (X : Fin 4 → ℝ) :
    eval (eigenPt X) (Qslice P) = algebraMap ℝ ℂ (P.eval (aRep X)) := by
  rw [Qslice, ← aeval_eq_eval, aeval_bind₁,
    show (fun i => aeval (eigenPt X) (cplxEigen i)) = (fun i => (Algebra.ofId ℝ ℂ) (aRep X i)) from
      funext (fun i => (aeval_cplxEigen_eigenPt X i).trans (Algebra.ofId_apply ℂ (aRep X i)).symm),
    MvPolynomial.aeval_map_algebraMap ℂ, ← MvPolynomial.comp_aeval]
  simp [aeval_eq_eval, Algebra.ofId_apply]

/-! ### Real-part descent: from a complex value back to a real polynomial -/

open MvPolynomial in
/-- The real part of a complex polynomial, taken coefficient-wise. -/
noncomputable def realPart (H : MvPolynomial (Fin 5) ℂ) : MvPolynomial (Fin 5) ℝ :=
  Finsupp.mapRange Complex.re Complex.zero_re H

open MvPolynomial in
@[simp] lemma realPart_coeff (H : MvPolynomial (Fin 5) ℂ) (m : Fin 5 →₀ ℕ) :
    coeff m (realPart H) = (coeff m H).re := Finsupp.mapRange_apply

open MvPolynomial in
lemma realPart_C (a : ℂ) : realPart (C a) = C a.re := by
  ext m; rw [realPart_coeff, coeff_C, coeff_C]; split_ifs <;> simp

open MvPolynomial in
lemma realPart_add (p q : MvPolynomial (Fin 5) ℂ) :
    realPart (p + q) = realPart p + realPart q := by
  ext m; simp [Complex.add_re]

open MvPolynomial in
lemma realPart_mul_X (p : MvPolynomial (Fin 5) ℂ) (i : Fin 5) :
    realPart (p * X i) = realPart p * X i := by
  ext m
  rw [realPart_coeff, coeff_mul_X', coeff_mul_X', realPart_coeff]
  split_ifs <;> simp

open MvPolynomial in
/-- Evaluating a complex polynomial at a real point and taking the real part is the same as
  evaluating its real part. -/
lemma realPart_eval (H : MvPolynomial (Fin 5) ℂ) (y : Fin 5 → ℝ) :
    (eval (fun j => (↑(y j) : ℂ)) H).re = (realPart H).eval y := by
  induction H using MvPolynomial.induction_on with
  | C a => rw [realPart_C]; simp
  | add p q hp hq => rw [realPart_add, map_add, map_add, Complex.add_re, hp, hq]
  | mul_X p i hp =>
    rw [realPart_mul_X, map_mul, map_mul, eval_X, eval_X, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, hp]

/-! ### Condition A: the value is a polynomial in the five bilinear generators -/

/-- The five real bilinear generators of `T'`, evaluated at `repHiggs X`:
  `‖Φ1‖², Re⟪⟫, Im⟪⟫, |Φ2₀|², |Φ2₁|²`. -/
def realGen (X : Fin 4 → ℝ) : Fin 5 → ℝ :=
  ![X 0 ^ 2, X 0 * X 1, X 0 * X 2, X 1 ^ 2 + X 2 ^ 2, X 3 ^ 2]

open MvPolynomial in
/-- The complex substitution expressing each bilinear, at the eigen-point, through the real
  generators (the off-diagonal pair `z w̄₀, z̄ w₀` mix `Re⟪⟫` and `Im⟪⟫`). -/
noncomputable def transf : Fin 5 → MvPolynomial (Fin 5) ℂ :=
  ![X 0, X 3, X 1 - C Complex.I * X 2, X 1 + C Complex.I * X 2, X 4]

open MvPolynomial in
/-- The bilinears at the eigen-point of `repHiggs X` are the real generators, read through `transf`. -/
lemma bilin_eval_eigenPt (X : Fin 4 → ℝ) (i : Fin 5) :
    eval (eigenPt X) (bilin i) = eval (fun j => (↑(realGen X j) : ℂ)) (transf i) := by
  fin_cases i <;>
    simp only [bilin, transf, eigenPt, realGen, Matrix.cons_val, Fin.isValue, map_mul, map_sub,
      map_add, eval_X, eval_C] <;>
    (apply Complex.ext <;>
      simp [pow_two, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring)

open MvPolynomial in
/-- Pushing an evaluation through an `aeval` substitution. -/
lemma eval_aeval_comp {R : Type*} [CommRing R] {κ ι : Type*} (x : ι → R)
    (f : κ → MvPolynomial ι R) (G : MvPolynomial κ R) :
    eval x (aeval f G) = eval (fun i => eval x (f i)) G := by
  rw [show (aeval f) G = bind₁ f G from rfl, ← aeval_eq_eval x, aeval_bind₁]
  simp [aeval_eq_eval]

open MvPolynomial in
/-- **Condition A.** A gauge-invariant polynomial potential, on the representative family, is a
  polynomial in the five real bilinear generators `‖Φ1‖², Re⟪⟫, Im⟪⟫, |Φ2₀|², |Φ2₁|²`. -/
lemma exists_polynomial_repHiggs_realGen {V : EffectivePotential} {n : ℕ}
    (hI : IsInvariant V) (h : HasMaxMassDimLE V n) :
    ∃ p : MvPolynomial (Fin 5) ℝ, ∀ X : Fin 4 → ℝ, V (repHiggs X) = p.eval (realGen X) := by
  obtain ⟨P, hP⟩ := h.exists_comp_linear_poly sliceR
  obtain ⟨G, hG⟩ := exists_aeval_bilin hI hP
  refine ⟨realPart (aeval transf G), fun X => ?_⟩
  have hval : (algebraMap ℝ ℂ) (V (repHiggs X))
      = eval (fun j => (↑(realGen X j) : ℂ)) (aeval transf G) := by
    rw [repHiggs_eq_sliceR, hP, ← eval_Qslice_eigenPt, ← hG]
    simp only [eval_aeval_comp]
    rw [show (fun i => eval (eigenPt X) (bilin i))
          = (fun i => eval (fun j => (↑(realGen X j) : ℂ)) (transf i)) from
        funext (bilin_eval_eigenPt X)]
  have hre : V (repHiggs X) = (eval (fun j => (↑(realGen X j) : ℂ)) (aeval transf G)).re := by
    rw [← hval]; simp
  rw [hre, realPart_eval]

/-! ### Clearing the `‖Φ1‖²` denominator: Condition A value times `‖Φ1‖²ᴺ` is a Gram polynomial -/

open MvPolynomial in
/-- The five bilinear generators, as polynomials in the four representative parameters. -/
noncomputable def realGenP : Fin 5 → MvPolynomial (Fin 4) ℝ :=
  ![X 0 ^ 2, X 0 * X 1, X 0 * X 2, X 1 ^ 2 + X 2 ^ 2, X 3 ^ 2]

open MvPolynomial in
/-- The four Gram components, as polynomials in the four representative parameters. -/
noncomputable def gramP : Fin 1 ⊕ Fin 3 → MvPolynomial (Fin 4) ℝ :=
  Sum.elim (fun _ => X 0 ^ 2 + (X 1 ^ 2 + X 2 ^ 2 + X 3 ^ 2))
    ![2 * (X 0 * X 1), 2 * (X 0 * X 2), X 0 ^ 2 - (X 1 ^ 2 + X 2 ^ 2 + X 3 ^ 2)]

open MvPolynomial in
@[simp] lemma realGenP_eval (X : Fin 4 → ℝ) (i : Fin 5) : (realGenP i).eval X = realGen X i := by
  fin_cases i <;> simp [realGenP, realGen]

open MvPolynomial in
@[simp] lemma gramP_eval (X : Fin 4 → ℝ) (μ : Fin 1 ⊕ Fin 3) :
    (gramP μ).eval X = (repHiggs X).gramVector μ := by
  match μ with
  | Sum.inl 0 => simp [gramP]
  | Sum.inr 0 => simp [gramP]; ring
  | Sum.inr 1 => simp [gramP]; ring
  | Sum.inr 2 => simp [gramP]

open MvPolynomial in
/-- Some power of `‖Φ1‖² = X₀²` times the Condition-A value polynomial lies in the Gram
  subalgebra: multiplying by `X₀²` pairs each `X₁²+X₂²` into `(X₀X₁)²+(X₀X₂)²` and each `X₃²` into
  the determinant `X₀²X₃²`, both of which are Gram polynomials. -/
lemma exists_clearing_mem (p : MvPolynomial (Fin 5) ℝ) :
    ∃ N : ℕ, (X 0) ^ (2 * N) * aeval realGenP p ∈ Algebra.adjoin ℝ (Set.range gramP) := by
  set S := Algebra.adjoin ℝ (Set.range gramP) with hS
  have hgmem : ∀ μ, gramP μ ∈ S := fun μ => Algebra.subset_adjoin ⟨μ, rfl⟩
  have hC : ∀ r : ℝ, (C r : MvPolynomial (Fin 4) ℝ) ∈ S := fun r => by
    rw [← MvPolynomial.algebraMap_eq]; exact Subalgebra.algebraMap_mem _ _
  have hX0sq : (X 0 ^ 2 : MvPolynomial (Fin 4) ℝ) ∈ S := by
    have e : (X 0 ^ 2 : MvPolynomial (Fin 4) ℝ)
        = C (1 / 2) * (gramP (Sum.inl 0) + gramP (Sum.inr 2)) := by
      apply MvPolynomial.funext; intro x; simp [gramP]; ring
    rw [e]; exact Subalgebra.mul_mem _ (hC _) (Subalgebra.add_mem _ (hgmem _) (hgmem _))
  have hX0X1 : (X 0 * X 1 : MvPolynomial (Fin 4) ℝ) ∈ S := by
    have e : (X 0 * X 1 : MvPolynomial (Fin 4) ℝ) = C (1 / 2) * gramP (Sum.inr 0) := by
      apply MvPolynomial.funext; intro x; simp [gramP]
    rw [e]; exact Subalgebra.mul_mem _ (hC _) (hgmem _)
  have hX0X2 : (X 0 * X 2 : MvPolynomial (Fin 4) ℝ) ∈ S := by
    have e : (X 0 * X 2 : MvPolynomial (Fin 4) ℝ) = C (1 / 2) * gramP (Sum.inr 1) := by
      apply MvPolynomial.funext; intro x; simp [gramP]
    rw [e]; exact Subalgebra.mul_mem _ (hC _) (hgmem _)
  have hmm : (X 1 ^ 2 + X 2 ^ 2 + X 3 ^ 2 : MvPolynomial (Fin 4) ℝ) ∈ S := by
    have e : (X 1 ^ 2 + X 2 ^ 2 + X 3 ^ 2 : MvPolynomial (Fin 4) ℝ)
        = C (1 / 2) * (gramP (Sum.inl 0) - gramP (Sum.inr 2)) := by
      apply MvPolynomial.funext; intro x; simp [gramP]; ring
    rw [e]; exact Subalgebra.mul_mem _ (hC _) (Subalgebra.sub_mem _ (hgmem _) (hgmem _))
  have her : (X 0 ^ 2 * (X 1 ^ 2 + X 2 ^ 2) : MvPolynomial (Fin 4) ℝ) ∈ S := by
    have e : (X 0 ^ 2 * (X 1 ^ 2 + X 2 ^ 2) : MvPolynomial (Fin 4) ℝ)
        = (X 0 * X 1) ^ 2 + (X 0 * X 2) ^ 2 := by ring
    rw [e]; exact Subalgebra.add_mem _ (pow_mem hX0X1 2) (pow_mem hX0X2 2)
  have hes : (X 0 ^ 2 * X 3 ^ 2 : MvPolynomial (Fin 4) ℝ) ∈ S := by
    have e : (X 0 ^ 2 * X 3 ^ 2 : MvPolynomial (Fin 4) ℝ)
        = X 0 ^ 2 * (X 1 ^ 2 + X 2 ^ 2 + X 3 ^ 2) - X 0 ^ 2 * (X 1 ^ 2 + X 2 ^ 2) := by ring
    rw [e]; exact Subalgebra.sub_mem _ (Subalgebra.mul_mem _ hX0sq hmm) her
  induction p using MvPolynomial.induction_on' with
  | monomial m c =>
    refine ⟨m 3 + m 4, ?_⟩
    have hmemRHS : C c * ((X 0 ^ 2) ^ m 0 * (X 0 * X 1) ^ m 1 * (X 0 * X 2) ^ m 2 *
        (X 0 ^ 2 * (X 1 ^ 2 + X 2 ^ 2)) ^ m 3 * (X 0 ^ 2 * X 3 ^ 2) ^ m 4) ∈ S :=
      Subalgebra.mul_mem _ (hC _) (Subalgebra.mul_mem _ (Subalgebra.mul_mem _
        (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (pow_mem hX0sq _) (pow_mem hX0X1 _))
          (pow_mem hX0X2 _)) (pow_mem her _)) (pow_mem hes _))
    rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun i => by simp), Fin.prod_univ_five]
    simp only [realGenP, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue,
      MvPolynomial.algebraMap_eq]
    convert hmemRHS using 1
    rw [pow_mul, pow_add]
    simp only [mul_pow]
    ring
  | add p q hp hq =>
    obtain ⟨Np, hp'⟩ := hp
    obtain ⟨Nq, hq'⟩ := hq
    refine ⟨max Np Nq, ?_⟩
    rw [map_add, mul_add]
    apply Subalgebra.add_mem
    · rw [show 2 * max Np Nq = 2 * (max Np Nq - Np) + 2 * Np from by omega, pow_add, mul_assoc]
      exact Subalgebra.mul_mem _ (by rw [pow_mul]; exact pow_mem hX0sq _) hp'
    · rw [show 2 * max Np Nq = 2 * (max Np Nq - Nq) + 2 * Nq from by omega, pow_add, mul_assoc]
      exact Subalgebra.mul_mem _ (by rw [pow_mul]; exact pow_mem hX0sq _) hq'

open MvPolynomial in
/-- **Denominator clearing.** For the Condition-A value polynomial `p`, some power of `‖Φ1‖² = X₀²`
  times `p ∘ realGen` is a polynomial in the Gram vector. -/
lemma exists_gram_clearing (p : MvPolynomial (Fin 5) ℝ) :
    ∃ (A : MvPolynomial (Fin 1 ⊕ Fin 3) ℝ) (N : ℕ), ∀ X : Fin 4 → ℝ,
      (X 0) ^ (2 * N) * p.eval (realGen X) = A.eval ((repHiggs X).gramVector) := by
  obtain ⟨N, hmem⟩ := exists_clearing_mem p
  rw [Algebra.adjoin_range_eq_range_aeval ℝ gramP] at hmem
  obtain ⟨A, hA⟩ := hmem
  change aeval gramP A = _ at hA
  refine ⟨A, N, fun X => ?_⟩
  have hL : eval X (aeval gramP A) = A.eval ((repHiggs X).gramVector) := by
    rw [eval_aeval_comp]; simp only [gramP_eval]
  have hR : eval X (MvPolynomial.X 0 ^ (2 * N) * aeval realGenP p)
      = (X 0) ^ (2 * N) * p.eval (realGen X) := by
    rw [map_mul, map_pow, eval_X, eval_aeval_comp]; simp only [realGenP_eval]
  rw [← hR, ← hL, hA]

/-!

## C. Reduction to the polynomial family of orbit representatives

The two structural ingredients of the proof live elsewhere:

* `TwoHiggsDoublet.exists_smul_eq_repHiggs` shows every configuration is gauge equivalent to a
  representative `repHiggs X` from the *polynomial* family of orbit representatives, and
* `TwoHiggsDoublet.gramVector_repHiggs_*` show the Gram vector of a representative is a polynomial
  in the four real parameters `X` (with no square roots).

Because the potential is gauge invariant, its value on any configuration equals its value on a
representative, and the Gram vector is likewise unchanged. Hence the whole statement reduces to the
question of whether `V ∘ repHiggs` is a polynomial in the (polynomial) Gram components of the
representative family — see `exists_polynomial_on_repHiggs`.

-/

/-- **The two Higgs doublet model first fundamental theorem (representative form).**

This is the irreducible invariant–theoretic core of the theorem: a gauge invariant polynomial
potential, restricted to the polynomial family of orbit representatives `repHiggs X`, is a
polynomial in the Gram components of that family.

This statement is square-root free (in contrast to the normalised representatives, whose
coordinates contain `√‖Φ1‖²`). It cannot follow from the parities of `V ∘ repHiggs` alone — e.g.
`X₁²` is parity invariant yet is `(Re ⟪Φ1,Φ2⟫)²/‖Φ1‖²`, which is not polynomial; it is excluded
precisely because it does not extend to a *global* polynomial invariant. The content is therefore
the non-abelian `SU(2)` first fundamental theorem specialised to two doublets in `ℂ²`, established
by the unipotent (shear group) reduction together with the Lagrange identity `norm_doubletDet_sq`
which folds the `SU(2)` determinant invariant back into the Gram data. -/
lemma exists_polynomial_on_repHiggs {V : EffectivePotential} {n : ℕ}
    (hI : IsInvariant V) (h : HasMaxMassDimLE V n) :
    ∃ p : MvPolynomial (Fin 1 ⊕ Fin 3) ℝ,
      ∀ X : Fin 4 → ℝ, V (repHiggs X) = p.eval (repHiggs X).gramVector := by
  sorry

/-- An invariant effective potential with maximum mass dimension n can be written as a
  polynomial in the entries of the Gram vector. -/
lemma effectivePotential_is_polynomial_gramVector {V : EffectivePotential} {n : ℕ}
    (hI: IsInvariant V) (h : HasMaxMassDimLE V n) :
    ∃ p : MvPolynomial (Fin 1 ⊕ Fin 3) ℝ, (∀ φ : TwoHiggsDoublet, V φ = p.eval φ.gramVector) := by
  obtain ⟨p, hp⟩ := exists_polynomial_on_repHiggs hI h
  refine ⟨p, fun φ => ?_⟩
  obtain ⟨X, g, hg⟩ := exists_smul_eq_repHiggs φ
  have hgram : φ.gramVector = (repHiggs X).gramVector := by
    rw [← hg]
    funext μ
    exact (gaugeGroupI_smul_fst_gramVector g φ μ).symm
  have hV : V φ = V (repHiggs X) := by
    rw [← hg]
    exact (hI g φ).symm
  rw [hV, hp X, hgram]

end EffectivePotential

end TwoHiggsDoublet
