/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.Particles.StandardModel.GaugeBosons.Gluons.JetCompleteness.CovariantTower
/-!
# Arbitrary-order highest-layer translations

## i. Overview

This file proves the programme-level highest-layer statement on `OrdinaryJets`'s ordinary
carrier.  A gauge jet based through order `r` fixes every ordinary generator below order `r` and
acts on order `r` by a constant translation.  The translation depends only on the total
multi-index obtained by adjoining the connection index, so it is totally symmetric in all
`r + 1` indices.

The factorial convention is essential: `facI_add_single` turns the derivative multiplicity in
`dMat` into the factorial of the total multi-index.  No hook coordinate or symmetric projection is
introduced here.
-/

@[expose] public section

namespace StandardModel

open Matrix Module MvPolynomial

namespace SU3Jet

/-!

## A. Jets based through a finite order

-/

/-- A gauge jet based through order `r`: its value is the identity and every positive Taylor
coefficient of total degree at most `r` vanishes. -/
def BasedTo (r : ℕ) (U : specialUnitaryGroup (Fin 3) JetRing) : Prop :=
  Gluon.jetValue U.1 = 1 ∧
    ∀ k, 0 < lorDeg k → lorDeg k ≤ r → coeffMat k U.1 = 0

lemma lorDeg_eq_zero_iff (k : DIdx) : lorDeg k = 0 ↔ k = 0 := by
  constructor
  · intro hk
    ext μ
    have hle : k μ ≤ lorDeg k := by
      rw [lorDeg]
      exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ μ)
    rw [hk] at hle
    exact Nat.eq_zero_of_le_zero hle
  · rintro rfl
    simp [lorDeg]

lemma lorDeg_pos_iff (k : DIdx) : 0 < lorDeg k ↔ k ≠ 0 := by
  rw [Nat.pos_iff_ne_zero, ne_eq, lorDeg_eq_zero_iff]

private lemma left_le_of_add_eq {p q k : DIdx} (h : p + q = k) : lorDeg p ≤ lorDeg k := by
  have hdeg := congrArg lorDeg h
  rw [lorDeg_add] at hdeg
  omega

private lemma right_le_of_add_eq {p q k : DIdx} (h : p + q = k) : lorDeg q ≤ lorDeg k := by
  have hdeg := congrArg lorDeg h
  rw [lorDeg_add] at hdeg
  omega

lemma basedTo_evalSU (hU : BasedTo r U) : JetGaugeGroupI.evalSU (Fin 3) U = 1 := by
  apply Subtype.ext
  rw [Gluon.evalSU_coe]
  exact hU.1

/-!

## B. Truncation of coefficient conjugation

-/

private lemma coeffMat_mul_constMat (k : DIdx) (P : Matrix (Fin 3) (Fin 3) JetRing)
    (M : Matrix (Fin 3) (Fin 3) ℂ) : coeffMat k (P * constMat M) = coeffMat k P * M := by
  ext i j
  simp only [coeffMat, Matrix.map_apply, Matrix.mul_apply, map_sum, constMat_apply,
    MvPowerSeries.coeff_mul_C]

/-- The coefficient of a conjugated constant matrix is the two-sided coefficient convolution. -/
lemma conjCoeffM_eq_sum (U : specialUnitaryGroup (Fin 3) JetRing) (t : DIdx)
    (M : Matrix (Fin 3) (Fin 3) ℂ) :
    conjCoeffM U t M =
      ∑ p ∈ Finset.antidiagonal t, coeffMat p.1 U.1 * M * star (coeffMat p.2 U.1) := by
  rw [conjCoeffM, coeffMat_mul]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [coeffMat_mul_constMat, star_coeffMat]

/-- Positive coefficient-conjugation orders through `r` vanish for a jet based through `r`. -/
lemma conjC_eq_zero_of_basedTo (hU : BasedTo r U) (ht0 : 0 < lorDeg t)
    (htr : lorDeg t ≤ r) : conjC U t = 0 := by
  apply LinearMap.ext
  intro X
  apply cmat_injective
  rw [cmat_conjC, LinearMap.zero_apply, cmat_zero, conjCoeffM_eq_sum]
  apply Finset.sum_eq_zero
  rintro ⟨p, q⟩ hpq
  have hpq' : p + q = t := Finset.mem_antidiagonal.mp hpq
  by_cases hp0 : p = 0
  · subst p
    have hqt : q = t := by simpa using hpq'
    subst q
    rw [hU.2 t ht0 htr, star_zero, Matrix.mul_zero]
  · have hpdeg : 0 < lorDeg p := (lorDeg_pos_iff p).2 hp0
    rw [hU.2 p hpdeg ((left_le_of_add_eq hpq').trans htr), Matrix.zero_mul,
      Matrix.zero_mul]

/-- At coefficient order zero, a based jet acts by the identity colour endomorphism. -/
lemma conjC_zero_of_basedTo (hU : BasedTo r U) : conjC U 0 = LinearMap.id := by
  apply LinearMap.ext
  intro X
  rw [conjC_zero, basedTo_evalSU hU, adC_one, LinearMap.id_apply]

/-!

## C. The canonical highest-layer shift

-/

/-- A canonical direction occurring in a nonzero total multi-index. -/
noncomputable def layerDir (w : DIdx) : Lor :=
  if hw : w = 0 then default else Classical.choose (Finsupp.ne_iff.mp hw)

lemma layerDir_coeff_ne_zero {w : DIdx} (hw : w ≠ 0) : w (layerDir w) ≠ 0 := by
  rw [layerDir, dif_neg hw]
  exact Classical.choose_spec (Finsupp.ne_iff.mp hw)

/-- The predecessor obtained by removing one occurrence of `layerDir w`. -/
noncomputable def layerPred (w : DIdx) : DIdx :=
  Finsupp.update w (layerDir w) (w (layerDir w) - 1)

lemma layerPred_add_single {w : DIdx} (hw : w ≠ 0) :
    layerPred w + Finsupp.single (layerDir w) 1 = w := by
  ext μ
  by_cases hμ : μ = layerDir w
  · subst μ
    simpa [layerPred, Finsupp.update] using
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (layerDir_coeff_ne_zero hw))
  · simp [layerPred, hμ]

lemma lorDeg_layerPred {w : DIdx} (hw : w ≠ 0) : lorDeg (layerPred w) + 1 = lorDeg w := by
  have h := congrArg lorDeg (layerPred_add_single hw)
  rwa [lorDeg_add, lorDeg_single] at h

/-- The constant colour shift attached to a total derivative multi-index.  It is packaged through
`mcCoeffCAt`, whose construction already proves hermiticity and tracelessness. -/
noncomputable def layerShift (U : specialUnitaryGroup (Fin 3) JetRing) (w : DIdx) : ColourSpace :=
  if _hw : w = 0 then 0 else
    facI (layerPred w) • mcCoeffCAt U (layerDir w) (layerPred w)

private lemma coeffMat_C_smul (z : ℂ) (k : DIdx)
    (M : Matrix (Fin 3) (Fin 3) JetRing) :
    coeffMat k ((MvPowerSeries.C z : JetRing) • M) = z • coeffMat k M := by
  ext i j
  show MvPowerSeries.coeff k ((MvPowerSeries.C z : JetRing) * M i j) =
    z * MvPowerSeries.coeff k (M i j)
  rw [MvPowerSeries.coeff_C_mul]

/-- Under basedness, the Maurer--Cartan coefficient has only its leading Taylor term. -/
lemma mcCoeffM_of_basedTo (hU : BasedTo r U) (hsr : lorDeg s ≤ r) (mu : Lor) :
    mcCoeffM U mu s =
      Complex.I • (((s mu : ℕ) : ℂ) + 1) •
        coeffMat (s + Finsupp.single mu 1) U.1 := by
  rw [mcCoeffM, mcH, mcP, coeffMat_C_smul, coeffMat_mul,
    Finset.sum_eq_single (s, 0)]
  · rw [coeffMat_dMat, coeffMat_zero_eq_jetValue, Gluon.jetValue_star, hU.1, star_one,
      Matrix.mul_one]
  · rintro ⟨p, q⟩ hpq hpair
    have hpq' : p + q = s := Finset.mem_antidiagonal.mp hpq
    have hq0 : q ≠ 0 := by
      intro hq
      subst q
      have hps : p = s := by simpa using hpq'
      exact hpair (Prod.ext hps rfl)
    have hqdeg : 0 < lorDeg q := (lorDeg_pos_iff q).2 hq0
    have hq : coeffMat q (star U.1) = 0 := by
      rw [← star_coeffMat, hU.2 q hqdeg ((right_le_of_add_eq hpq').trans hsr), star_zero]
    rw [hq, Matrix.mul_zero]
  · simp

private lemma cmat_normalized_mcCoeff (hU : BasedTo r U) (hsr : lorDeg s ≤ r) (mu : Lor) :
    cmat (facI s • mcCoeffCAt U mu s) =
      ((facI (s + Finsupp.single mu 1) : ℂ) * Complex.I) •
        coeffMat (s + Finsupp.single mu 1) U.1 := by
  rw [cmat_smul, cmat_mcCoeffCAt, mcCoeffM_of_basedTo hU hsr, smul_smul,
    facI_add_single]
  push_cast
  module

/-- **Total symmetry.**  The normalized coefficient depends only on the total index obtained by
adjoining the connection direction.  The proof is exactly `facI_add_single`. -/
lemma normalized_mcCoeff_eq_layerShift (hU : BasedTo r U) (hs : lorDeg s = r) (mu : Lor) :
    facI s • mcCoeffCAt U mu s = layerShift U (s + Finsupp.single mu 1) := by
  have hwdeg : lorDeg (s + Finsupp.single mu 1) = r + 1 := by
    rw [lorDeg_add, lorDeg_single, hs]
  have hw0 : s + Finsupp.single mu 1 ≠ 0 := by
    rw [← lorDeg_pos_iff, hwdeg]
    omega
  apply cmat_injective
  have hpred : lorDeg (layerPred (s + Finsupp.single mu 1)) ≤ r := by
    have h := lorDeg_layerPred hw0
    rw [hwdeg] at h
    omega
  rw [layerShift, dif_neg hw0, cmat_normalized_mcCoeff hU hs.le mu,
    cmat_normalized_mcCoeff hU hpred (layerDir (s + Finsupp.single mu 1)),
    layerPred_add_single hw0]

/-- The matrix of a highest-layer shift is `i` times the factorial-normalized leading Taylor
coefficient of the gauge jet. -/
lemma cmat_layerShift_of_basedTo (hU : BasedTo r U) (hw : lorDeg w = r + 1) :
    cmat (layerShift U w) =
      ((facI w : ℂ) * Complex.I) • coeffMat w U.1 := by
  have hw0 : w ≠ 0 := by
    rw [← lorDeg_pos_iff, hw]
    omega
  have hpred : lorDeg (layerPred w) ≤ r := by
    have h := lorDeg_layerPred hw0
    rw [hw] at h
    omega
  rw [layerShift, dif_neg hw0,
    cmat_normalized_mcCoeff hU hpred (layerDir w), layerPred_add_single hw0]

/-!

## D. Exact fixation below the top layer

-/

private lemma conjugation_part_eq_gen (hU : BasedTo r U) (hsr : lorDeg s ≤ r)
    (mu : Lor) (c : Col) :
    (∑ p ∈ Finset.antidiagonal s, ∑ c',
        algebraMap ℝ JetAlgebra
            (facI s * (facI p.1)⁻¹ * coordC c (conjC U p.2 (colourBasis c'))) *
          genVec p.1 mu c') = genVec s mu c := by
  rw [Finset.sum_eq_single (s, 0)]
  · rw [conjC_zero_of_basedTo hU]
    simp only [LinearMap.id_apply, mul_inv_cancel₀ (facI_ne_zero s),
      one_mul]
    calc
      (∑ c', algebraMap ℝ JetAlgebra (coordC c (colourBasis c')) * genVec s mu c') =
          adR (1 : specialUnitaryGroup (Fin 3) ℂ) (genVec s mu) c := by
            simpa only [adC_one] using
              (sum_coordC_adC (R := JetAlgebra) (1 : specialUnitaryGroup (Fin 3) ℂ)
                (genVec s mu) c)
      _ = genVec s mu c := adR_one _ _
  · rintro ⟨p, q⟩ hpq hpair
    have hpq' : p + q = s := Finset.mem_antidiagonal.mp hpq
    have hq0 : q ≠ 0 := by
      intro hq
      subst q
      have hps : p = s := by simpa using hpq'
      exact hpair (Prod.ext hps rfl)
    have hqdeg : 0 < lorDeg q := (lorDeg_pos_iff q).2 hq0
    rw [conjC_eq_zero_of_basedTo hU hqdeg ((right_le_of_add_eq hpq').trans hsr)]
    simp
  · simp

lemma mcCoeffCAt_eq_zero_of_lt (hU : BasedTo r U) (hsr : lorDeg s < r) (mu : Lor) :
    mcCoeffCAt U mu s = 0 := by
  have hwdeg : lorDeg (s + Finsupp.single mu 1) = lorDeg s + 1 := by
    rw [lorDeg_add, lorDeg_single]
  have hwpos : 0 < lorDeg (s + Finsupp.single mu 1) := by omega
  have hwle : lorDeg (s + Finsupp.single mu 1) ≤ r := by omega
  apply cmat_injective
  rw [cmat_mcCoeffCAt, cmat_zero, mcCoeffM_of_basedTo hU hsr.le,
    hU.2 _ hwpos hwle, smul_zero, smul_zero]

/-- **Lower layers are fixed exactly.**  Every ordinary generator of degree below `r` is fixed by
a jet based through order `r`. -/
lemma gaugeSubstGen_eq_ofGen_of_lt (hU : BasedTo r U) (hsr : lorDeg s < r)
    (mu : Lor) (c : Col) :
    gaugeSubstGen U (JetGenerators.dA s mu c) = ofGen (JetGenerators.dA s mu c) := by
  rw [gaugeSubstGen, conjugation_part_eq_gen hU hsr.le,
    mcCoeffCAt_eq_zero_of_lt hU hsr, smul_zero]
  simp [genVec, constR]

/-- The ordinary generators whose derivative degree is strictly below `r`. -/
def lowerLayer (r : ℕ) : Set JetAlgebra :=
  {P | ∃ (s : DIdx) (mu : Lor) (c : Col), lorDeg s < r ∧ P = ofGen (JetGenerators.dA s mu c)}

/-- The polynomial algebra supported on ordinary generators of derivative degree below `r`. -/
noncomputable def lowerAlgebra (r : ℕ) : Subalgebra ℝ JetAlgebra := Algebra.adjoin ℝ (lowerLayer r)

/-- A jet based through `r` fixes every polynomial supported below derivative degree `r`. -/
lemma gaugePull_eq_self_of_mem_lowerAlgebra (hU : BasedTo r U) {P : JetAlgebra}
    (hP : P ∈ lowerAlgebra r) : gaugePull U P = P := by
  have hle : lowerAlgebra r ≤ AlgHom.equalizer (gaugePull U) (AlgHom.id ℝ JetAlgebra) := by
    refine Algebra.adjoin_le ?_
    rintro Q ⟨s, mu, c, hsr, rfl⟩
    show gaugePull U (ofGen (JetGenerators.dA s mu c)) =
      AlgHom.id ℝ JetAlgebra (ofGen (JetGenerators.dA s mu c))
    rw [gaugePull_ofGen, gaugeSubstGen_eq_ofGen_of_lt hU hsr, AlgHom.id_apply]
  exact hle hP

/-- **The top layer is a pure translation.**  No field-dependent commutator survives at
derivative degree `r`. -/
lemma gaugeSubstGen_eq_add_layerShift (hU : BasedTo r U) (hs : lorDeg s = r)
    (mu : Lor) (c : Col) :
    gaugeSubstGen U (JetGenerators.dA s mu c) =
      ofGen (JetGenerators.dA s mu c) +
        constR (layerShift U (s + Finsupp.single mu 1)) c := by
  rw [gaugeSubstGen, conjugation_part_eq_gen hU hs.le,
    normalized_mcCoeff_eq_layerShift hU hs]
  rfl

/-- Two presentations of the same total multi-index give the same normalized shift. -/
lemma normalized_mcCoeff_eq_of_total_index (hU : BasedTo r U) (hs : lorDeg s = r)
    (hs' : lorDeg s' = r) (hidx : s + Finsupp.single mu 1 = s' + Finsupp.single mu' 1) :
    facI s • mcCoeffCAt U mu s = facI s' • mcCoeffCAt U mu' s' := by
  rw [normalized_mcCoeff_eq_layerShift hU hs,
    normalized_mcCoeff_eq_layerShift hU hs', hidx]

/-!

## E. Realizability by a single conjugated monomial jet

-/

/-- The single conjugated `DiagonalJet` monomial jet used to realize one highest-layer colour shift.
  -/
noncomputable def realizingJet (w : DIdx) (hw : w ≠ 0) (c₀ : Col) (a : ℝ) :
    specialUnitaryGroup (Fin 3) JetRing :=
  conjBy (colourConj c₀) (diagSU (a / facI w) w hw)

lemma realizingJet_basedTo (hw : lorDeg w = r + 1) (c₀ : Col) (a : ℝ) :
    BasedTo r (realizingJet w (by rw [← lorDeg_pos_iff, hw]; omega) c₀ a) := by
  let hw₀ : w ≠ 0 := by rw [← lorDeg_pos_iff, hw]; omega
  change BasedTo r (realizingJet w hw₀ c₀ a)
  constructor
  · exact jetValue_eq_one _
      (evalSU_conjBy _ (evalSU_diagSU (a / facI w) w hw₀))
  · intro k hkpos hkr
    have hk₀ : k ≠ 0 := (lorDeg_pos_iff k).1 hkpos
    have hmult : ∀ n : ℕ, k ≠ n • w := by
      intro n hkn
      have hdeg := congrArg lorDeg hkn
      rw [lorDeg_nsmul, hw] at hdeg
      by_cases hn : n = 0
      · subst n
        simp at hdeg
        omega
      have hlower := Nat.mul_le_mul_right (r + 1) (Nat.one_le_iff_ne_zero.mpr hn)
      simp only [one_mul] at hlower
      omega
    rw [realizingJet, coe_conjBy, coeffMat_conj_const,
      show ((diagSU (a / facI w) w hw₀ : specialUnitaryGroup (Fin 3) JetRing) :
          Matrix (Fin 3) (Fin 3) JetRing) = diagMat (a / facI w) w hw₀ from rfl,
      coeffMat_diagMat_eq_zero (a / facI w) w hw₀ hk₀ hmult,
      Matrix.mul_zero, Matrix.zero_mul]

private lemma realizing_scalar (w : DIdx) (a : ℝ) :
    ((facI w : ℂ) * Complex.I) * (-((a / facI w : ℝ) : ℂ) * Complex.I) = (a : ℂ) := by
  have hw : (facI w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (facI_ne_zero w)
  push_cast
  field_simp
  rw [pow_two, Complex.I_mul_I]
  ring

lemma layerShift_realizingJet_self (hw : lorDeg w = r + 1) (c₀ : Col) (a : ℝ) :
    layerShift (realizingJet w (by rw [← lorDeg_pos_iff, hw]; omega) c₀ a) w =
      a • colourBasis c₀ := by
  let hw₀ : w ≠ 0 := by rw [← lorDeg_pos_iff, hw]; omega
  change layerShift (realizingJet w hw₀ c₀ a) w = a • colourBasis c₀
  rw [← adC_colourC c₀]
  apply cmat_injective
  rw [cmat_layerShift_of_basedTo (realizingJet_basedTo hw c₀ a) hw, cmat_smul, cmat_adC,
    cmat_colourC, realizingJet, coe_conjBy, coeffMat_conj_const,
    show ((diagSU (a / facI w) w hw₀ : specialUnitaryGroup (Fin 3) JetRing) :
        Matrix (Fin 3) (Fin 3) JetRing) = diagMat (a / facI w) w hw₀ from rfl,
    coeffMat_diagMat_self]
  calc
    ((facI w : ℂ) * Complex.I) •
          ((colourConj c₀ : Matrix (Fin 3) (Fin 3) ℂ) *
            ((-((a / facI w : ℝ) : ℂ) * Complex.I) • colourMat) *
              ((colourConj c₀ : Matrix (Fin 3) (Fin 3) ℂ))ᴴ) =
        (((facI w : ℂ) * Complex.I) *
            (-((a / facI w : ℝ) : ℂ) * Complex.I)) •
          ((colourConj c₀ : Matrix (Fin 3) (Fin 3) ℂ) * colourMat *
            ((colourConj c₀ : Matrix (Fin 3) (Fin 3) ℂ))ᴴ) := by
              rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    _ = (a : ℂ) •
          ((colourConj c₀ : Matrix (Fin 3) (Fin 3) ℂ) * colourMat *
            ((colourConj c₀ : Matrix (Fin 3) (Fin 3) ℂ))ᴴ) := by rw [realizing_scalar]
    _ = a • ((colourConj c₀ : Matrix (Fin 3) (Fin 3) ℂ) * colourMat *
          ((colourConj c₀ : Matrix (Fin 3) (Fin 3) ℂ))ᴴ) := by
      rw [show ((a : ℂ)) = algebraMap ℝ ℂ a from rfl, algebraMap_smul]

lemma layerShift_realizingJet_of_ne (hw : lorDeg w = r + 1) (c₀ : Col) (a : ℝ)
    (hw' : lorDeg w' = r + 1) (hne : w' ≠ w) :
    layerShift (realizingJet w (by rw [← lorDeg_pos_iff, hw]; omega) c₀ a) w' = 0 := by
  let hw₀ : w ≠ 0 := by rw [← lorDeg_pos_iff, hw]; omega
  let hw₀' : w' ≠ 0 := by rw [← lorDeg_pos_iff, hw']; omega
  change layerShift (realizingJet w hw₀ c₀ a) w' = 0
  have hmult : ∀ n : ℕ, w' ≠ n • w := by
    intro n hn
    have hdeg := congrArg lorDeg hn
    rw [lorDeg_nsmul, hw, hw'] at hdeg
    have h₁n : 1 = n := Nat.mul_right_cancel (Nat.zero_lt_succ r)
      (by simpa only [one_mul] using hdeg)
    have hn₁ : n = 1 := h₁n.symm
    rw [hn₁, one_smul] at hn
    exact hne hn
  apply cmat_injective
  rw [cmat_layerShift_of_basedTo (realizingJet_basedTo hw c₀ a) hw', cmat_zero,
    realizingJet, coe_conjBy, coeffMat_conj_const,
    show ((diagSU (a / facI w) w hw₀ : specialUnitaryGroup (Fin 3) JetRing) :
        Matrix (Fin 3) (Fin 3) JetRing) = diagMat (a / facI w) w hw₀ from rfl,
    coeffMat_diagMat_eq_zero (a / facI w) w hw₀ hw₀' hmult,
    Matrix.mul_zero, Matrix.zero_mul, smul_zero]

/-- **Arbitrary-order realizability.**  One conjugated monomial jet realizes any chosen colour
basis shift at one degree-`r + 1` total index and vanishes at every other index in that layer. -/
lemma exists_basedTo_layerShift (hw : lorDeg w = r + 1) (c₀ : Col) (a : ℝ) :
    ∃ U : specialUnitaryGroup (Fin 3) JetRing,
      BasedTo r U ∧ layerShift U w = a • colourBasis c₀ ∧
        ∀ w', lorDeg w' = r + 1 → w' ≠ w → layerShift U w' = 0 := by
  let hw₀ : w ≠ 0 := by rw [← lorDeg_pos_iff, hw]; omega
  refine ⟨realizingJet w hw₀ c₀ a, realizingJet_basedTo hw c₀ a,
    layerShift_realizingJet_self hw c₀ a, ?_⟩
  intro w' hw' hne
  exact layerShift_realizingJet_of_ne hw c₀ a hw' hne

/-!

## F. Agreement with the degree-zero and degree-one pilots

-/

/-- At `r = 0`, the layer shift is `GaugeAction`'s first Maurer--Cartan colour coefficient. -/
lemma layerShift_single (hU : BasedTo 0 U) (mu : Lor) :
    layerShift U (Finsupp.single mu 1) = mcC U mu := by
  have h := normalized_mcCoeff_eq_layerShift hU (s := (0 : DIdx)) (by simp [lorDeg]) mu
  simpa only [facI_zero, one_smul, mcCoeffCAt_zero, zero_add] using h.symm

/-- At `r = 1`, the layer shift is `GaugeAction`'s second Maurer--Cartan colour coefficient. -/
lemma layerShift_pair (hU : BasedTo 1 U) (nu mu : Lor) :
    layerShift U (Finsupp.single nu 1 + Finsupp.single mu 1) = mc2C U nu mu := by
  have h := normalized_mcCoeff_eq_layerShift hU (s := Finsupp.single nu 1)
    (lorDeg_single nu) mu
  simpa only [facI_single, one_smul, mcCoeffCAt_single] using h.symm

end SU3Jet

end StandardModel
