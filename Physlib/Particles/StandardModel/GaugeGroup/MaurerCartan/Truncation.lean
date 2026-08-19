/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.MaurerCartan.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.Jet.Truncation
public import Physlib.Particles.StandardModel.GaugeAlgebra.JetGaugeAlgebra
public import Physlib.Relativity.Tensors.ComplexTensor.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Representation
public import Physlib.Relativity.SL2C.Basic
public import Physlib.Mathematics.ConjModule
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Physlib.Particles.LagrangianTheory.Basic
public import Physlib.Mathematics.MvPowerSeriesDerivative
public import Physlib.Mathematics.MvPolynomialTranslation
public import Mathlib.Algebra.MvPolynomial.Derivation
/-!
# The Maurer–Cartan forms and the truncation kernels
-/

@[expose] public section
namespace StandardModel
open MvPowerSeries JetGaugeAlgebra JetRing
/-- Projecting onto the zeroth truncation kernel does not change the Maurer–Cartan
  form: by the cocycle law, right-multiplication by a constant gauge transformation
  drops out. -/
lemma maurerCartanForm_truncationProjZero (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3) :
    maurerCartanForm (JetGaugeGroupI.truncationProjZero U : JetGaugeGroupI) μ =
      maurerCartanForm U μ := by
  rw [show (JetGaugeGroupI.truncationProjZero U : JetGaugeGroupI) =
      U * (JetGaugeGroupI.ofConstant U.eval)⁻¹ from rfl,
    ← map_inv, maurerCartanForm_cocycle, maurerCartanForm_ofConstant]
  simp

/-- A pure jet is determined by its Maurer–Cartan form: on the kernel of the zeroth
  truncation, `U ↦ ω(U)` is injective. By the cocycle and inverse laws
  `ω(V⁻¹ U) = Ad_{V⁻¹}(ω(U) − ω(V)) = 0`, so `V⁻¹ U` is a constant jet, and purity
  of `U` and `V` forces that constant to be the identity. -/
lemma maurerCartanForm_injOn_truncationKer_zero {U V : JetGaugeGroupI}
    (hU : U ∈ JetGaugeGroupI.truncationKer 0) (hV : V ∈ JetGaugeGroupI.truncationKer 0)
    (h : maurerCartanForm U = maurerCartanForm V) : U = V := by
  have h1 : maurerCartanForm (V⁻¹ * U) = 0 := by
    funext μ
    rw [maurerCartanForm_cocycle, maurerCartanForm_inv, congrFun h μ]
    simp
  obtain ⟨c, hc⟩ := (maurerCartanForm_eq_zero_iff_ofConstant _).mp h1
  have hc1 : c = 1 := by
    have he := congrArg JetGaugeGroupI.eval hc
    rw [map_mul, map_inv, JetGaugeGroupI.mem_truncationKer_zero_iff.mp hU,
      JetGaugeGroupI.mem_truncationKer_zero_iff.mp hV, JetGaugeGroupI.eval_ofConstant] at he
    simpa using he.symm
  rw [hc1, map_one] at hc
  exact (inv_mul_eq_one.mp hc).symm

lemma exists_maurerCartanForm_eq_of_structure
    (ω : (Fin 1 ⊕ Fin 3) → JetGaugeAlgebra)
    (hω : ∀ μ ν, deriv μ (ω ν) - deriv ν (ω μ) + ⁅ω μ, ω ν⁆ = 0) :
    ∃ U ∈ JetGaugeGroupI.truncationKer 0, maurerCartanForm U = ω := by
  obtain ⟨U, hU0, hU⟩ := exists_deriv_eq_of_maurerCartanForm_structure ω hω
  refine ⟨U, JetGaugeGroupI.mem_truncationKer_zero_iff.mpr hU0, funext fun μ => ?_⟩
  have hu3 : U.1.1 * star U.1.1 = 1 := by
    have h := (Matrix.mem_specialUnitaryGroup_iff.mp U.1.2).1
    rwa [Matrix.mem_unitaryGroup_iff] at h
  have hu2 : U.2.1.1 * star U.2.1.1 = 1 := by
    have h := (Matrix.mem_specialUnitaryGroup_iff.mp U.2.1.2).1
    rwa [Matrix.mem_unitaryGroup_iff] at h
  have hu1 : U.2.2.1 * star U.2.2.1 = 1 := (Unitary.mem_iff.mp U.2.2.2).2
  refine ext_of_matrix ?_ ?_ ?_
  · rw [maurerCartanForm_toSU3Matrix,
      show U.1.1.map (pderiv ℂ μ) = (-Complex.I) • (ω μ).toSU3Matrix * U.1.1 from
        congrArg (fun p => p.1) (hU μ),
      smul_mul_assoc, smul_mul_assoc, mul_assoc, hu3, mul_one, smul_smul]
    simp
  · rw [maurerCartanForm_toSU2Matrix,
      show U.2.1.1.map (pderiv ℂ μ) = (-Complex.I) • (ω μ).toSU2Matrix * U.2.1.1 from
        congrArg (fun p => p.2.1) (hU μ),
      smul_mul_assoc, smul_mul_assoc, mul_assoc, hu2, mul_one, smul_smul]
    simp
  · rw [maurerCartanForm_toU1Value,
      show pderiv ℂ μ U.2.2.1 = (-Complex.I) • (ω μ).toU1Value * U.2.2.1 from
        congrArg (fun p => p.2.2) (hU μ),
      smul_mul_assoc, smul_mul_assoc, mul_assoc, hu1, mul_one, smul_smul]
    simp


/-!

## Freeness: injectivity of the symmetrized Maurer–Cartan data

-/

/-- The symmetrized Maurer–Cartan data of a pure jet: the base-point values of its
  symmetrized Maurer–Cartan forms, indexed by nonempty multisets of directions.
  Total symmetry is automatic from the multiset indexing. -/
noncomputable def symmetrizedMaurerCartanCoeff (U : JetGaugeGroupI.truncationKer 0)
    (r : {r : Multiset (Fin 1 ⊕ Fin 3) // r ≠ 0}) : GaugeAlgebra :=
  eval (symmetrizedMaurerCartanForm U.1 r.1)

/-- Freeness, injectivity half: a pure jet is determined by its symmetrized
  Maurer–Cartan data. The symmetrized data determine all Maurer–Cartan Taylor data
  by strong induction with `eval_iteratedDeriv_maurerCartanForm_eq_of_symmetrized_eq`,
  hence the Maurer–Cartan form itself by Taylor determinacy, hence the pure jet by
  `maurerCartanForm_injOn_truncationKer_zero`. -/
lemma symmetrizedMaurerCartanCoeff_injective : Function.Injective symmetrizedMaurerCartanCoeff := by
  intro U V h
  -- the hypothesis extends to all multisets, the empty one trivially
  have hsym : ∀ r, eval (symmetrizedMaurerCartanForm U.1 r) =
      eval (symmetrizedMaurerCartanForm V.1 r) := by
    intro r
    by_cases hr : r = 0
    · subst hr
      simp
    · exact congrFun h ⟨r, hr⟩
  -- all Maurer–Cartan Taylor data agree, by strong induction on the number of directions
  have hall : ∀ (n : ℕ) (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3), s.card = n →
      eval (iteratedDeriv s (maurerCartanForm U.1 μ)) =
        eval (iteratedDeriv s (maurerCartanForm V.1 μ)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
        intro s μ hs
        exact eval_iteratedDeriv_maurerCartanForm_eq_of_symmetrized_eq U.1 V.1 n hsym
          (fun p ν hp => ih p.card hp p ν rfl) s μ hs
  -- hence the Maurer–Cartan forms agree, by Taylor determinacy
  have hmc : maurerCartanForm U.1 = maurerCartanForm V.1 := by
    funext μ
    exact ext_of_eval_iteratedDeriv fun s => hall s.card s μ rfl
  exact Subtype.ext (maurerCartanForm_injOn_truncationKer_zero U.2 V.2 hmc)

TODO "The below code needs cleaning up and moving to the correct place."
/-!

## The symmetrized data through the radial Maurer–Cartan component

-/

lemma symmetrizedMaurerCartanCoeff_apply (U : JetGaugeGroupI.truncationKer 0)
    (x : {r : Multiset (Fin 1 ⊕ Fin 3) // r ≠ 0}) :
    symmetrizedMaurerCartanCoeff U x = eval (symmetrizedMaurerCartanForm U.1 x.1) := rfl

lemma symmetrizedMaurerCartanCoeff_toSU3_eq (U : JetGaugeGroupI.truncationKer 0)
    (P : Matrix (Fin 3) (Fin 3) JetRing)
    (hrad : ∑ μ, (X μ : JetRing) • (maurerCartanForm U.1 μ).toSU3Matrix = P)
    (r : Multiset (Fin 1 ⊕ Fin 3)) (hr : r ≠ 0) (i j : Fin 3) :
    (symmetrizedMaurerCartanCoeff U ⟨r, hr⟩).toSU3Matrix i j =
      (1/(Multiset.card r : ℝ)) • (((∏ ν, Nat.factorial (r.count ν) : ℕ) : ℂ) *
        coeff (Multiset.toFinsupp r) (P i j)) := by
  have hentry : (∑ μ, (X μ : JetRing) • ((maurerCartanForm U.1 μ).toSU3Matrix i j)) =
      P i j := by
    have h1 : (∑ μ, (X μ : JetRing) • ((maurerCartanForm U.1 μ).toSU3Matrix i j)) =
        (∑ μ, (X μ : JetRing) • (maurerCartanForm U.1 μ).toSU3Matrix) i j := by
      rw [Matrix.sum_apply]
      exact Finset.sum_congr rfl fun μ _ => rfl
    rw [h1, hrad]
  rw [symmetrizedMaurerCartanCoeff_apply, eval_symmetrizedMaurerCartanForm_toSU3_apply,
    sum_constantCoeff_foldl_erase, hentry]

lemma symmetrizedMaurerCartanCoeff_toSU2_eq (U : JetGaugeGroupI.truncationKer 0)
    (P : Matrix (Fin 2) (Fin 2) JetRing)
    (hrad : ∑ μ, (X μ : JetRing) • (maurerCartanForm U.1 μ).toSU2Matrix = P)
    (r : Multiset (Fin 1 ⊕ Fin 3)) (hr : r ≠ 0) (i j : Fin 2) :
    (symmetrizedMaurerCartanCoeff U ⟨r, hr⟩).toSU2Matrix i j =
      (1/(Multiset.card r : ℝ)) • (((∏ ν, Nat.factorial (r.count ν) : ℕ) : ℂ) *
        coeff (Multiset.toFinsupp r) (P i j)) := by
  have hentry : (∑ μ, (X μ : JetRing) • ((maurerCartanForm U.1 μ).toSU2Matrix i j)) =
      P i j := by
    have h1 : (∑ μ, (X μ : JetRing) • ((maurerCartanForm U.1 μ).toSU2Matrix i j)) =
        (∑ μ, (X μ : JetRing) • (maurerCartanForm U.1 μ).toSU2Matrix) i j := by
      rw [Matrix.sum_apply]
      exact Finset.sum_congr rfl fun μ _ => rfl
    rw [h1, hrad]
  rw [symmetrizedMaurerCartanCoeff_apply, eval_symmetrizedMaurerCartanForm_toSU2_apply,
    sum_constantCoeff_foldl_erase, hentry]

lemma symmetrizedMaurerCartanCoeff_toU1_eq (U : JetGaugeGroupI.truncationKer 0)
    (p : JetRing)
    (hrad : ∑ μ, (X μ : JetRing) • (maurerCartanForm U.1 μ).toU1Value = p)
    (r : Multiset (Fin 1 ⊕ Fin 3)) (hr : r ≠ 0) :
    (symmetrizedMaurerCartanCoeff U ⟨r, hr⟩).toU1Value =
      (1/(Multiset.card r : ℝ)) • (((∏ ν, Nat.factorial (r.count ν) : ℕ) : ℂ) *
        coeff (Multiset.toFinsupp r) p) := by
  rw [symmetrizedMaurerCartanCoeff_apply, eval_symmetrizedMaurerCartanForm_toU1Value,
    sum_constantCoeff_foldl_erase, hrad]

/-!

## Freeness: surjectivity of the symmetrized Maurer–Cartan data

-/

/-- Freeness, surjectivity half: every prescribed family of symmetrized Maurer–Cartan
  data is realized by a pure jet. The radial component `ρ := ∑ μ x_μ ω_μ` of the
  Maurer–Cartan form carries exactly the symmetrized data, so it suffices to solve the
  radial (Euler) system `E U = −i ρ U`, `U(0) = 1` for a prescribed `ρ`; this is done
  factorwise by `exists_matrix_eulerTransport`, with unitarity and determinant one from
  the Euler vanishing principle. -/
lemma symmetrizedMaurerCartanCoeff_surjective :
    Function.Surjective symmetrizedMaurerCartanCoeff := by
  classical
  intro c
  -- the factorwise construction: a unitary Euler transport with prescribed radial data
  have hcore : ∀ (κ : Type) [Fintype κ] [DecidableEq κ]
      (E : {r : Multiset (Fin 1 ⊕ Fin 3) // r ≠ 0} → Matrix κ κ ℂ),
      (∀ x, star (E x) = E x) →
      ∃ V P : Matrix κ κ JetRing,
        (constantCoeff : JetRing →+* ℂ).mapMatrix V = 1 ∧
        V * star V = 1 ∧
        (∑ μ, (X μ : JetRing) • (Complex.I • (V.map (pderiv ℂ μ) * star V)) = P) ∧
        ((∀ x, (E x).trace = 0) →
          (∀ (M : Matrix κ κ JetRing) (μ : Fin 1 ⊕ Fin 3),
            pderiv ℂ μ M.det = (M.map (pderiv ℂ μ) * M.adjugate).trace) → V.det = 1) ∧
        (∀ (r : Multiset (Fin 1 ⊕ Fin 3)) (hr : r ≠ 0) (i j : κ),
          coeff (Multiset.toFinsupp r) (P i j) =
            (((Multiset.card r : ℕ) : ℂ) /
              ((∏ ν, Nat.factorial (r.count ν) : ℕ) : ℂ)) * E ⟨r, hr⟩ i j) := by
    intro κ _ _ E hEstar
    set P : Matrix κ κ JetRing := Matrix.of fun i j =>
      show JetRing from fun m =>
        if h : Finsupp.toMultiset m = 0 then 0
        else (((Finsupp.degree m : ℕ) : ℂ) / ((∏ ν, Nat.factorial (m ν) : ℕ) : ℂ)) *
          E ⟨Finsupp.toMultiset m, h⟩ i j with hP
    have hPcoeff : ∀ (m : (Fin 1 ⊕ Fin 3) →₀ ℕ) (i j : κ), coeff m (P i j) =
        if h : Finsupp.toMultiset m = 0 then 0
        else (((Finsupp.degree m : ℕ) : ℂ) / ((∏ ν, Nat.factorial (m ν) : ℕ) : ℂ)) *
          E ⟨Finsupp.toMultiset m, h⟩ i j := fun _ _ _ => rfl
    have hP0 : ∀ i j, constantCoeff (P i j) = 0 := fun i j => by
      rw [← coeff_zero_eq_constantCoeff, hPcoeff, dif_pos (by simp)]
    have hPstar : star P = P := by
      ext i j : 1
      ext m
      rw [Matrix.star_apply, JetRing.coeff_star, hPcoeff, hPcoeff]
      split_ifs with h
      · simp
      · rw [star_mul', show star (E ⟨Finsupp.toMultiset m, h⟩ j i)
            = E ⟨Finsupp.toMultiset m, h⟩ i j from by
          conv_rhs => rw [← hEstar ⟨Finsupp.toMultiset m, h⟩]
          exact (Matrix.star_apply _ _ _).symm,
          star_div₀, star_natCast, star_natCast]
    have hR0 : ∀ i j, constantCoeff (((-Complex.I) • P) i j) = 0 := fun i j => by
      rw [Matrix.smul_apply, ← coeff_zero_eq_constantCoeff, map_smul,
        coeff_zero_eq_constantCoeff, hP0, smul_zero]
    have hRstar : star ((-Complex.I) • P) = -((-Complex.I) • P) := by
      rw [star_smul, hPstar]
      simp
    obtain ⟨V, hV0, hEV⟩ := exists_matrix_eulerTransport ((-Complex.I) • P) hR0
    have hVu : V * star V = 1 := eulerTransport_mul_star hRstar hR0 hV0 hEV
    refine ⟨V, P, hV0, hVu, ?_, ?_, ?_⟩
    · calc ∑ μ, (X μ : JetRing) • (Complex.I • (V.map (pderiv ℂ μ) * star V))
          = Complex.I • ((∑ μ, (X μ : JetRing) • V.map (pderiv ℂ μ)) * star V) := by
            rw [Finset.sum_mul, Finset.smul_sum]
            exact Finset.sum_congr rfl fun μ _ => by
              rw [Matrix.smul_mul, smul_comm Complex.I]
        _ = P := by
            rw [hEV, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc, hVu, mul_one,
              smul_smul]
            simp
    · intro hEtr hjac
      have hPtr : P.trace = 0 := by
        ext m
        rw [show coeff m P.trace = ∑ i, coeff m (P i i) from by
            rw [show P.trace = ∑ i, P i i from rfl, map_sum],
          map_zero, Finset.sum_congr rfl fun i _ => hPcoeff m i i]
        by_cases h : Finsupp.toMultiset m = 0
        · simp [h]
        · simp only [dif_neg h]
          rw [← Finset.mul_sum,
            show (∑ i, E ⟨Finsupp.toMultiset m, h⟩ i i) = (E ⟨Finsupp.toMultiset m, h⟩).trace
              from rfl,
            hEtr, mul_zero]
      have hRtr : ((-Complex.I) • P).trace = 0 := by
        rw [Matrix.trace_smul, hPtr, smul_zero]
      exact eulerTransport_det hjac hRtr hV0 hEV
    · intro r hr i j
      have hround : Finsupp.toMultiset (Multiset.toFinsupp r) = r := by simp
      rw [hPcoeff, dif_neg (show ¬Finsupp.toMultiset (Multiset.toFinsupp r) = 0 from by
          rw [hround]; exact hr),
        show (∏ ν, Nat.factorial ((Multiset.toFinsupp r) ν)) = ∏ ν, Nat.factorial (r.count ν)
          from Finset.prod_congr rfl fun ν _ => by rw [Multiset.toFinsupp_apply],
        degree_toFinsupp_eq_card]
      exact congrArg (fun x => (((Multiset.card r : ℕ) : ℂ) /
        ((∏ ν, Nat.factorial (r.count ν) : ℕ) : ℂ)) * E x i j) (Subtype.ext hround)
  -- apply the construction on each factor
  obtain ⟨V₃, P₃, hV₃0, hV₃u, hrad₃, hdet₃, hcoeff₃⟩ :=
    hcore (Fin 3) (fun x => (c x).toSU3Matrix)
      (fun x => show star (c x).toSU3Matrix = (c x).toSU3Matrix from (c x).1.2.1)
  obtain ⟨V₂, P₂, hV₂0, hV₂u, hrad₂, hdet₂, hcoeff₂⟩ :=
    hcore (Fin 2) (fun x => (c x).toSU2Matrix)
      (fun x => show star (c x).toSU2Matrix = (c x).toSU2Matrix from (c x).2.1.2.1)
  obtain ⟨V₁, P₁, hV₁0, hV₁u, hrad₁, _, hcoeff₁⟩ :=
    hcore (Fin 1) (fun x => Matrix.of fun _ _ => (c x).toU1Value)
      (fun x => Matrix.ext fun _ _ => (c x).2.2.2)
  have hd₃ : V₃.det = 1 := hdet₃
    (fun x => show ((c x).toSU3Matrix).trace = 0 from (c x).1.2.2) jacobi_fin3
  have hd₂ : V₂.det = 1 := hdet₂
    (fun x => show ((c x).toSU2Matrix).trace = 0 from (c x).2.1.2.2) jacobi_fin2
  have hu1 : V₁ 0 0 * star (V₁ 0 0) = 1 := by
    simpa [Matrix.mul_apply] using congrArg (fun M => M (0 : Fin 1) (0 : Fin 1)) hV₁u
  have hu0 : constantCoeff (V₁ 0 0) = 1 := by
    simpa using congrArg (fun M => M (0 : Fin 1) (0 : Fin 1)) hV₁0
  -- the scalar radial identity for the `U(1)` factor
  have hrad₁' : ∑ μ, (X μ : JetRing) •
      (Complex.I • (pderiv ℂ μ (V₁ 0 0) * star (V₁ 0 0))) = P₁ 0 0 := by
    have h := congrArg (fun M => M (0 : Fin 1) (0 : Fin 1)) hrad₁
    simpa [Matrix.sum_apply, Matrix.mul_apply] using h
  refine ⟨⟨(⟨V₃, Matrix.mem_specialUnitaryGroup_iff.mpr
        ⟨Matrix.mem_unitaryGroup_iff.mpr hV₃u, hd₃⟩⟩,
      ⟨V₂, Matrix.mem_specialUnitaryGroup_iff.mpr
        ⟨Matrix.mem_unitaryGroup_iff.mpr hV₂u, hd₂⟩⟩,
      ⟨V₁ 0 0, Unitary.mem_iff.mpr ⟨by rw [mul_comm]; exact hu1, hu1⟩⟩),
    JetGaugeGroupI.mem_truncationKer_zero_iff.mpr
      (Prod.ext (Subtype.ext hV₃0) (Prod.ext (Subtype.ext hV₂0) (Subtype.ext hu0)))⟩, ?_⟩
  funext x
  obtain ⟨r, hr⟩ := x
  have hcard : ((Multiset.card r : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr fun hc => hr (Multiset.card_eq_zero.mp hc)
  have hfacne : ((∏ ν, Nat.factorial (r.count ν) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun ν _ => Nat.factorial_ne_zero _)
  have hfacne' : (∏ ν, ((Nat.factorial (r.count ν) : ℕ) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun ν _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  refine GaugeAlgebra.ext_of_matrix ?_ ?_ ?_
  · ext i j : 1
    rw [symmetrizedMaurerCartanCoeff_toSU3_eq _ P₃
        (by simp only [maurerCartanForm_toSU3Matrix]; exact hrad₃) r hr i j,
      hcoeff₃ r hr i j, Complex.real_smul]
    push_cast
    field_simp
  · ext i j : 1
    rw [symmetrizedMaurerCartanCoeff_toSU2_eq _ P₂
        (by simp only [maurerCartanForm_toSU2Matrix]; exact hrad₂) r hr i j,
      hcoeff₂ r hr i j, Complex.real_smul]
    push_cast
    field_simp
  · rw [symmetrizedMaurerCartanCoeff_toU1_eq _ (P₁ 0 0)
        (by simp only [maurerCartanForm_toU1Value]; exact hrad₁') r hr,
      hcoeff₁ r hr 0 0, Complex.real_smul, Matrix.of_apply]
    push_cast
    field_simp

end StandardModel
