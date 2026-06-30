/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.«2HDM».GaugeTorus
public import PhyslibAlpha.«2HDM».OrbitRepresentative
/-!
# The gauge slice and the hypercharges of the doublet components

After using `SU(2)` to align the first doublet with the first axis, a configuration lies on the
*upper-triangular slice* `sliceHiggs z w₀ w₁ = ⟨(z, 0), (w₀, w₁)⟩`. The gauge torus acts on the
three surviving components `z = Φ1₀`, `w₀ = Φ2₀`, `w₁ = Φ2₁` by their hypercharges:

* the Cartan phase `a` multiplies the *first* components `z, w₀` (and conjugates the would-be second
  component of `Φ1`, which vanishes here), giving `(z, w₀, w₁) ↦ (a z, a w₀, ā w₁)`;
* the residual `U(1)` (`ofU1Subgroup c`) multiplies the *second* component `w₁` by `c⁶`, giving
  `(z, w₀, w₁) ↦ (z, w₀, c⁶ w₁)`.

These two phase rotations are the source of the charge balancing of the effective potential.
-/

@[expose] public section

noncomputable section

namespace TwoHiggsDoublet

open InnerProductSpace
open StandardModel
open ComplexConjugate

/-- The upper-triangular slice configuration `⟨(z, 0), (w₀, w₁)⟩`. It specialises to `repHiggs`
  when the components take their real "canonical frame" values. -/
def sliceHiggs (z w0 w1 : ℂ) : TwoHiggsDoublet where
  Φ1 := !₂[z, 0]
  Φ2 := !₂[w0, w1]

@[simp] lemma sliceHiggs_Φ1 (z w0 w1 : ℂ) : (sliceHiggs z w0 w1).Φ1 = !₂[z, 0] := rfl
@[simp] lemma sliceHiggs_Φ2 (z w0 w1 : ℂ) : (sliceHiggs z w0 w1).Φ2 = !₂[w0, w1] := rfl

/-- The representative family is the real slice. -/
lemma repHiggs_eq_sliceHiggs (X : Fin 4 → ℝ) :
    repHiggs X = sliceHiggs (X 0) ((X 1 : ℂ) + Complex.I * (X 2 : ℂ)) (X 3) := rfl

/-- Hypercharge action of the Cartan phase on the slice: it multiplies the first components by `a`
  and the perpendicular second component by `ā`. -/
lemma gaugeCartan_smul_sliceHiggs (a : unitary ℂ) (z w0 w1 : ℂ) :
    GaugeGroupI.gaugeCartan a • sliceHiggs z w0 w1
      = sliceHiggs ((a : ℂ) * z) ((a : ℂ) * w0) ((star a : ℂ) * w1) := by
  apply ext_of_fst_snd
  · rw [gaugeGroupI_smul_fst, GaugeGroupI.gaugeCartan_smul_eq]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · rw [gaugeGroupI_smul_snd, GaugeGroupI.gaugeCartan_smul_eq]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Hypercharge action of the residual `U(1)` on the slice: it multiplies the perpendicular second
  component by `c⁶` and leaves the first components fixed. -/
lemma ofU1Subgroup_smul_sliceHiggs (c : unitary ℂ) (z w0 w1 : ℂ) :
    GaugeGroupI.ofU1Subgroup c • sliceHiggs z w0 w1
      = sliceHiggs z w0 ((c : ℂ) ^ 6 * w1) := by
  apply ext_of_fst_snd
  · rw [gaugeGroupI_smul_fst, HiggsVec.ofU1Subgroup_smul_eq_smul]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · rw [gaugeGroupI_smul_snd, HiggsVec.ofU1Subgroup_smul_eq_smul]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

end TwoHiggsDoublet
