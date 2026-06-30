/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.BeyondTheStandardModel.TwoHDM.GramMatrix
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
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
  ∃ p : MvPolynomial (Module.dual ℝ TwoHiggsDoublet) ℝ, (∀ φ : TwoHiggsDoublet, V φ = p.eval
   (fun i => φ.|)
  ) ∧
    p.totalDegree ≤ n

/-- The polynomial associated to a potential `V` with a maximum mass dimension
  less than or equal to `n`. -/
def polynomial (V : EffectivePotential) {n : ℕ} (h : HasMaxMassDimLE V n) :
    MvPolynomial (Fin 4) ℝ := Classical.choose h

lemma polynomial_totalDegree {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n) :
    (polynomial V h).totalDegree ≤ n := (Classical.choose_spec h).2

lemma apply_eq_polynomial {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n)
    (φ : TwoHiggsDoublet) : V φ = (polynomial V h).eval φ.toRealScalars := (Classical.choose_spec h).1 φ

end EffectivePotential

end TwoHiggsDoublet
