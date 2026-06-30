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
