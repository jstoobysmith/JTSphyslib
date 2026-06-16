/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.BeyondTheStandardModel.TwoHDM.GramMatrix
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
end EffectivePotential

end TwoHiggsDoublet
