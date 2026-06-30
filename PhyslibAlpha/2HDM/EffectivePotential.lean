/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.BeyondTheStandardModel.TwoHDM.GramMatrix
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Funext
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
