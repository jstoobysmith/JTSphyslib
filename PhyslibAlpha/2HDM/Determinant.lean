/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.BeyondTheStandardModel.TwoHDM.GramMatrix
/-!
# The doublet determinant of the two Higgs doublet model

The two Higgs doublets `Φ1, Φ2 : ℂ²` form a `2 × 2` matrix whose determinant
`Φ1₀ Φ2₁ - Φ1₁ Φ2₀` is the basic `SU(2)`-invariant built out of the two doublets that is
*not* one of the entries of the Gram matrix.

Under the gauge group it carries hypercharge (it is rescaled by a phase under the `U(1)` factor
and is genuinely invariant under `SU(2)`), so it only contributes to gauge invariants through its
modulus squared. The central result of this file, `norm_doubletDet_sq`, is the Lagrange identity
which expresses this modulus squared in terms of the Gram data:
`‖doubletDet H‖² = ‖Φ1‖² ‖Φ2‖² - ‖⟪Φ1, Φ2⟫‖² = (gramMatrix H).det.re`.

-/

@[expose] public section

noncomputable section

namespace TwoHiggsDoublet

open InnerProductSpace
open StandardModel
open ComplexConjugate
open Matrix

/-- The determinant of the `2 × 2` matrix whose columns are the two Higgs doublets. This is the
  basic `SU(2)`-invariant of the two doublets which is not an entry of the Gram matrix. -/
def doubletDet (H : TwoHiggsDoublet) : ℂ :=
  H.Φ1 0 * H.Φ2 1 - H.Φ1 1 * H.Φ2 0

lemma doubletDet_eq (H : TwoHiggsDoublet) :
    H.doubletDet = H.Φ1 0 * H.Φ2 1 - H.Φ1 1 * H.Φ2 0 := rfl

/-- The Lagrange identity: the modulus squared of the doublet determinant equals the determinant
  of the Gram matrix. -/
lemma norm_doubletDet_sq (H : TwoHiggsDoublet) :
    ‖doubletDet H‖ ^ 2 = ‖H.Φ1‖ ^ 2 * ‖H.Φ2‖ ^ 2 - ‖⟪H.Φ1, H.Φ2⟫_ℂ‖ ^ 2 := by
  rw [doubletDet]
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, PiLp.inner_apply]
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.conj_re,
    Complex.conj_im, RCLike.inner_apply]
  ring

/-- The modulus squared of the doublet determinant equals the real part of the determinant of the
  Gram matrix. -/
lemma norm_doubletDet_sq_eq_det (H : TwoHiggsDoublet) :
    ‖doubletDet H‖ ^ 2 = H.gramMatrix.det.re := by
  rw [norm_doubletDet_sq, gramMatrix_det_eq_real]

/-- The modulus squared of the doublet determinant in terms of the Gram vector. -/
lemma norm_doubletDet_sq_eq_gramVector (H : TwoHiggsDoublet) :
    ‖doubletDet H‖ ^ 2 =
    (1 / 4 : ℝ) * (H.gramVector (Sum.inl 0) ^ 2 - ∑ μ : Fin 3, H.gramVector (Sum.inr μ) ^ 2) := by
  rw [norm_doubletDet_sq_eq_det, gramMatrix_det_eq_gramVector]

/-!

## Gauge covariance of the doublet determinant

The doublet determinant is genuinely invariant under `SU(2)` (whose determinant is `1`) and is
rescaled by the sixth power of the `U(1)` phase. In particular its modulus is gauge invariant,
consistent with `norm_doubletDet_sq_eq_det`.

-/

/-- The action of the gauge group on a single Higgs vector, written componentwise. -/
lemma gaugeGroupI_smul_apply (g : StandardModel.GaugeGroupI) (φ : HiggsVec) (i : Fin 2) :
    (g • φ) i = (g.toU1 ^ 3 : ℂ) * (g.toSU2.1 *ᵥ φ.ofLp) i := by
  rw [HiggsVec.gaugeGroupI_smul_eq]
  rfl

/-- The doublet determinant is a relative invariant: under a gauge transformation it picks up the
  sixth power of the `U(1)` phase (and is genuinely `SU(2)`-invariant). -/
lemma doubletDet_smul (g : StandardModel.GaugeGroupI) (H : TwoHiggsDoublet) :
    doubletDet (g • H) = (g.toU1 ^ 3 : ℂ) ^ 2 * doubletDet H := by
  rw [doubletDet, doubletDet, gaugeGroupI_smul_fst, gaugeGroupI_smul_snd,
    gaugeGroupI_smul_apply, gaugeGroupI_smul_apply, gaugeGroupI_smul_apply, gaugeGroupI_smul_apply]
  have hdet : (g.toSU2.1).det = 1 := g.toSU2.2.2
  rw [Matrix.det_fin_two] at hdet
  simp only [mulVec, dotProduct, Fin.sum_univ_two]
  linear_combination ((g.toU1 ^ 3 : ℂ) ^ 2 *
    (H.Φ1.ofLp 0 * H.Φ2.ofLp 1 - H.Φ1.ofLp 1 * H.Φ2.ofLp 0)) * hdet

/-- The modulus of the doublet determinant is gauge invariant. -/
@[simp]
lemma norm_doubletDet_smul (g : StandardModel.GaugeGroupI) (H : TwoHiggsDoublet) :
    ‖doubletDet (g • H)‖ = ‖doubletDet H‖ := by
  have h2 : ‖doubletDet (g • H)‖ ^ 2 = ‖doubletDet H‖ ^ 2 := by
    rw [norm_doubletDet_sq_eq_det, norm_doubletDet_sq_eq_det, gaugeGroupI_smul_gramMatrix]
  rw [← Real.sqrt_sq (norm_nonneg (doubletDet (g • H))), h2,
    Real.sqrt_sq (norm_nonneg (doubletDet H))]

end TwoHiggsDoublet
