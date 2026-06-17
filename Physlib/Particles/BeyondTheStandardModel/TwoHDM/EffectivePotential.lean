/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.BeyondTheStandardModel.TwoHDM.GramMatrix
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
/-!

# The potential of the Two Higgs doublet model

-/

@[expose] public section
namespace TwoHiggsDoublet
open InnerProductSpace
open StandardModel

abbrev EffectivePotential : Type := TwoHiggsDoublet → ℝ

namespace EffectivePotential

def IsInvariant (V : EffectivePotential) : Prop :=
  ∀ (g : GaugeGroupI), ∀ (φ : TwoHiggsDoublet), V (g • φ) = V φ

namespace IsInvariant

lemma eq_on_orbits {φ1 φ2 : TwoHiggsDoublet} {V : EffectivePotential} (hV : IsInvariant V)
    (h : φ1 ∈ MulAction.orbit GaugeGroupI φ2) : V φ1 = V φ2 := by
  rcases h with ⟨g, hg⟩
  rw [← hg]
  exact hV g φ2

lemma eq_of_gramMatrix_eq {φ1 φ2 : TwoHiggsDoublet} {V : EffectivePotential} (hV : IsInvariant V)
    (h : φ1.gramMatrix = φ2.gramMatrix) : V φ1 = V φ2 :=
  eq_on_orbits hV <| (mem_orbit_gaugeGroupI_iff_gramMatrix φ1 φ2).mpr h

end IsInvariant


/-!

## B. Maximum mass dimension

-/

/-- The proposition that the potential `V` has a maximum mass dimension
  less than or equal to `n` - also implying it is a polynomial. -/
def HasMaxMassDimLE (V : EffectivePotential) (n : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin 8) ℝ, (∀ φ : TwoHiggsDoublet, V φ = p.eval φ.toRealScalars) ∧
    p.totalDegree ≤ n

/-- The polynomial associated to a potential `V` with a maximum mass dimension
  less than or equal to `n`. -/
noncomputable def polynomial (V : EffectivePotential) {n : ℕ} (h : HasMaxMassDimLE V n) :
    MvPolynomial (Fin 8) ℝ := Classical.choose h

lemma polynomial_totalDegree {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n) :
    (polynomial V h).totalDegree ≤ n := (Classical.choose_spec h).2

lemma apply_eq_polynomial {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n)
    (φ : TwoHiggsDoublet) : V φ = (polynomial V h).eval φ.toRealScalars :=
  (Classical.choose_spec h).1 φ

/-!

## C. Terms of a given mass dimension

-/


/-- The part of a potential at a given mass-dimension. -/
noncomputable def termOfMassDim (V : EffectivePotential) {n : ℕ} (h : HasMaxMassDimLE V n) (m : ℕ) :
    TwoHiggsDoublet → ℝ := fun φ => ((polynomial V h).homogeneousComponent m).eval φ.toRealScalars

lemma termOfMassDim_eq_zero_of_max_lt {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n)
    {m : ℕ} (hm : n < m) (φ : TwoHiggsDoublet) :
    termOfMassDim V h m φ = 0 := by
  simp only [termOfMassDim]
  rw [MvPolynomial.homogeneousComponent_eq_zero]
  simp only [map_zero]
  have h1 := polynomial_totalDegree h
  grind

lemma termOfMassDim_homogeneity {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n) (m : ℕ)
    (φ : TwoHiggsDoublet) (t : ℝ) : termOfMassDim V h m (t • φ) = t ^ m *
      termOfMassDim V h m φ := by
  rw [termOfMassDim, termOfMassDim, MvPolynomial.eval_eq', MvPolynomial.eval_eq',
    Finset.mul_sum, toRealScalars_smul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i, d i = m := by
    rw [MvPolynomial.support_homogeneousComponent, Finset.mem_filter] at hd
    rw [← Finsupp.degree_eq_sum]
    exact hd.2
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hdeg]
  ring




open MvPolynomial in
noncomputable def partialGramTermOfMassDim (V : EffectivePotential) {n : ℕ}
    (h : HasMaxMassDimLE V n) (m : ℕ) :
    MvPolynomial (Fin 4) ℝ :=
  let p' := (polynomial V h).homogeneousComponent m
  let t : MvPolynomial (Fin 4) ℝ :=
    MvPolynomial.bind₁ ![X 0, 0, 0, 0, X 1, X 2, X 3, 0] p'
  ∑ d ∈ t.support.filter (fun d => Even (d 3)),
      MvPolynomial.monomial (Finsupp.update d 3 (d 3 / 2)) (t.coeff d)

/-!

The idea is now show that
- partialGramTermOfMassDim
-/
end EffectivePotential

end TwoHiggsDoublet
