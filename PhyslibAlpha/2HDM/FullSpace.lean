/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.«2HDM».EffectivePotential
/-!
# The full configuration space of the two Higgs doublet model

The orbit-representative slice `repHiggs` captures the *abelian* (gauge-torus) content of the first
fundamental theorem (`Condition A`: the value is a polynomial in the five bilinears `‖Φ1‖²`,
`Re⟪⟫`, `Im⟪⟫`, `|Φ2₀|²`, `|Φ2₁|²`). It cannot, however, capture the non-abelian content: only the
diagonal torus preserves the slice `{Φ1₁ = 0}`, so the slice value polynomial is blind to the
component-mixing `SU(2)` rotations needed to fuse `|Φ2₀|²` and `|Φ2₁|²` into `‖Φ2‖²`.

To access that content we parametrise the *entire* eight–real–dimensional configuration space and
work with the two gauge tori (the standard diagonal one and a component-mixing one); their combined
invariance is the genuine `SU(2)` first fundamental theorem.
-/

@[expose] public section

noncomputable section

namespace TwoHiggsDoublet

open InnerProductSpace
open StandardModel
open scoped ComplexConjugate

/-- The full configuration space as a real-linear map of the eight real field components
  `(Re Φ1₀, Im Φ1₀, Re Φ1₁, Im Φ1₁, Re Φ2₀, Im Φ2₀, Re Φ2₁, Im Φ2₁)`. -/
def fullR : (Fin 8 → ℝ) →ₗ[ℝ] TwoHiggsDoublet where
  toFun a :=
    { Φ1 := !₂[(a 0 : ℂ) + Complex.I * (a 1 : ℂ), (a 2 : ℂ) + Complex.I * (a 3 : ℂ)]
      Φ2 := !₂[(a 4 : ℂ) + Complex.I * (a 5 : ℂ), (a 6 : ℂ) + Complex.I * (a 7 : ℂ)] }
  map_add' a b := by
    apply ext_of_fst_snd
    · ext i; fin_cases i <;> simp <;> ring
    · ext i; fin_cases i <;> simp <;> ring
  map_smul' c a := by
    apply ext_of_fst_snd
    · ext i; fin_cases i <;> simp [Complex.real_smul] <;> ring
    · ext i; fin_cases i <;> simp [Complex.real_smul] <;> ring

@[simp] lemma fullR_Φ1 (a : Fin 8 → ℝ) :
    (fullR a).Φ1 = !₂[(a 0 : ℂ) + Complex.I * (a 1 : ℂ), (a 2 : ℂ) + Complex.I * (a 3 : ℂ)] := rfl

@[simp] lemma fullR_Φ2 (a : Fin 8 → ℝ) :
    (fullR a).Φ2 = !₂[(a 4 : ℂ) + Complex.I * (a 5 : ℂ), (a 6 : ℂ) + Complex.I * (a 7 : ℂ)] := rfl

/-- Every configuration is `fullR` of its eight real components. -/
lemma exists_fullR (φ : TwoHiggsDoublet) : ∃ a : Fin 8 → ℝ, fullR a = φ := by
  refine ⟨![(φ.Φ1 0).re, (φ.Φ1 0).im, (φ.Φ1 1).re, (φ.Φ1 1).im,
      (φ.Φ2 0).re, (φ.Φ2 0).im, (φ.Φ2 1).re, (φ.Φ2 1).im], ?_⟩
  apply ext_of_fst_snd
  · ext i; fin_cases i <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one, mul_comm Complex.I, Complex.re_add_im]
  · ext i; fin_cases i <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one, mul_comm Complex.I, Complex.re_add_im]

end TwoHiggsDoublet
