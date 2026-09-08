/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.LocalGaugeData
public import Physlib.Relativity.JetRing.Matrix
/-!
# Freeness of the Maurer–Cartan data of the Standard Model jets

## i. Overview

For any faithful local-gauge-data package, a pure jet (one with identity value) is
determined by its symmetrized Maurer–Cartan data, the base-point values of the symmetrized
Maurer–Cartan form indexed by nonempty multisets of directions:
`LocalGaugeData.symmetrizedMaurerCartanCoeff` is injective. For the Standard Model jets it
is also *surjective*: every family of gauge-algebra elements indexed by nonempty multisets
is the symmetrized Maurer–Cartan data of some pure jet. Together, the symmetrized data are
free coordinates on the pure jets.

Surjectivity is a statement about power series, proved here from the matrix definitions.
The radial component `ρ = ∑_μ x_μ ω_μ` of the Maurer–Cartan form carries exactly the
symmetrized data, so it suffices to solve the Euler system `E U = −i ρ U`, `U(0) = 1` for
a prescribed `ρ`; this is done factor by factor by `JetRing.exists_matrix_eulerTransport`,
with unitarity and unit determinant from the Euler vanishing principle. The same
integration technique, applied to the full structural equation, shows that every flat jet
1-form is the Maurer–Cartan form of a pure jet, `exists_maurerCartanForm_eq_of_structure`.

## ii. Key results

- `StandardModel.exists_maurerCartanForm_eq_of_structure` : every flat jet 1-form is the
  Maurer–Cartan form of a pure jet.
- `StandardModel.symmetrizedMaurerCartanCoeff_surjective` : every family of symmetrized
  data is realized by a pure jet.
- `StandardModel.instFreeLocalGaugeData` : the package is free, so the symmetrized data are
  free coordinates on the pure jets.

## iii. Table of contents

- A. Integrating the structural equation
- B. The symmetrized Maurer–Cartan data in components
- C. Surjectivity of the symmetrized Maurer–Cartan data

-/

@[expose] public section

namespace StandardModel

open MvPowerSeries JetGaugeAlgebra JetRing

/-!

## A. Integrating the structural equation

-/

/-- Every flat jet 1-form is the Maurer–Cartan form of a pure jet: the converse of the
  structural equation. The jet is the parallel transport
  `exists_deriv_eq_of_maurerCartanForm_structure`, and unitarity turns
  `∂_μ U = −i ω_μ U` into `ω_μ = i (∂_μ U) U⁻¹`. -/
lemma exists_maurerCartanForm_eq_of_structure
    (ω : (Fin 1 ⊕ Fin 3) → JetGaugeAlgebra)
    (hω : ∀ μ ν, deriv μ (ω ν) - deriv ν (ω μ) + ⁅ω μ, ω ν⁆ = 0) :
    ∃ U ∈ localGaugeData.truncationKer 0, maurerCartanForm U = ω := by
  obtain ⟨U, hU0, hU⟩ := exists_deriv_eq_of_maurerCartanForm_structure ω hω
  refine ⟨U, localGaugeData.mem_truncationKer_zero_iff.mpr hU0, funext fun μ => ?_⟩
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

## B. The symmetrized Maurer–Cartan data in components

-/

/-- The `su(3)` entry of the evaluated symmetrized Maurer–Cartan form, as a sum of
  base-point values of iterated derivatives of the Maurer–Cartan form entries. -/
lemma eval_symmetrizedMaurerCartanForm_toSU3_apply (U : JetGaugeGroupI)
    (r : Multiset (Fin 1 ⊕ Fin 3)) (i j : Fin 3) :
    (eval (localGaugeData.symmetrizedMaurerCartanForm U r)).toSU3Matrix i j =
      (1/(r.card : ℝ)) • (r.map fun μ => constantCoeff ((r.erase μ).foldl
        (fun f ρ => pderiv ℂ ρ f) ((maurerCartanForm U μ).toSU3Matrix i j))).sum := by
  set Φ : JetGaugeAlgebra →+ ℂ := AddMonoidHom.mk'
    (fun a => (eval a).toSU3Matrix i j)
    (fun a b => by simp [map_add, GaugeAlgebra.add_toSU3Matrix]) with hΦ
  have hΦiter : ∀ μ ∈ r, Φ (iteratedDeriv (r - {μ}) (maurerCartanForm U μ)) =
      constantCoeff ((r.erase μ).foldl (fun f ρ => pderiv ℂ ρ f)
        ((maurerCartanForm U μ).toSU3Matrix i j)) := by
    intro μ hμ
    show (eval (iteratedDeriv (r - {μ}) (maurerCartanForm U μ))).toSU3Matrix i j = _
    rw [eval_toSU3Matrix_apply, iteratedDeriv_toSU3Matrix, Matrix.map_apply,
      Multiset.sub_singleton]
  rw [LocalGaugeData.symmetrizedMaurerCartanForm]
  simp only [localGaugeData_iteratedDeriv, localGaugeData_maurerCartan]
  rw [map_smul, GaugeAlgebra.smul_toSU3Matrix, Matrix.smul_apply]
  congr 1
  rw [show (eval ((r.map fun μ =>
        iteratedDeriv (r - {μ}) (maurerCartanForm U μ)).sum)).toSU3Matrix i j
      = Φ ((r.map fun μ => iteratedDeriv (r - {μ}) (maurerCartanForm U μ)).sum) from rfl,
    map_multiset_sum, Multiset.map_map]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun μ hμ => hΦiter μ hμ)

/-- The `su(2)` entry of the evaluated symmetrized Maurer–Cartan form. -/
lemma eval_symmetrizedMaurerCartanForm_toSU2_apply (U : JetGaugeGroupI)
    (r : Multiset (Fin 1 ⊕ Fin 3)) (i j : Fin 2) :
    (eval (localGaugeData.symmetrizedMaurerCartanForm U r)).toSU2Matrix i j =
      (1/(r.card : ℝ)) • (r.map fun μ => constantCoeff ((r.erase μ).foldl
        (fun f ρ => pderiv ℂ ρ f) ((maurerCartanForm U μ).toSU2Matrix i j))).sum := by
  set Φ : JetGaugeAlgebra →+ ℂ := AddMonoidHom.mk'
    (fun a => (eval a).toSU2Matrix i j)
    (fun a b => by simp [map_add, GaugeAlgebra.add_toSU2Matrix]) with hΦ
  have hΦiter : ∀ μ ∈ r, Φ (iteratedDeriv (r - {μ}) (maurerCartanForm U μ)) =
      constantCoeff ((r.erase μ).foldl (fun f ρ => pderiv ℂ ρ f)
        ((maurerCartanForm U μ).toSU2Matrix i j)) := by
    intro μ hμ
    show (eval (iteratedDeriv (r - {μ}) (maurerCartanForm U μ))).toSU2Matrix i j = _
    rw [eval_toSU2Matrix_apply, iteratedDeriv_toSU2Matrix, Matrix.map_apply,
      Multiset.sub_singleton]
  rw [LocalGaugeData.symmetrizedMaurerCartanForm]
  simp only [localGaugeData_iteratedDeriv, localGaugeData_maurerCartan]
  rw [map_smul, GaugeAlgebra.smul_toSU2Matrix, Matrix.smul_apply]
  congr 1
  rw [show (eval ((r.map fun μ =>
        iteratedDeriv (r - {μ}) (maurerCartanForm U μ)).sum)).toSU2Matrix i j
      = Φ ((r.map fun μ => iteratedDeriv (r - {μ}) (maurerCartanForm U μ)).sum) from rfl,
    map_multiset_sum, Multiset.map_map]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun μ hμ => hΦiter μ hμ)

/-- The `u(1)` value of the evaluated symmetrized Maurer–Cartan form. -/
lemma eval_symmetrizedMaurerCartanForm_toU1Value (U : JetGaugeGroupI)
    (r : Multiset (Fin 1 ⊕ Fin 3)) :
    (eval (localGaugeData.symmetrizedMaurerCartanForm U r)).toU1Value =
      (1/(r.card : ℝ)) • (r.map fun μ => constantCoeff ((r.erase μ).foldl
        (fun f ρ => pderiv ℂ ρ f) ((maurerCartanForm U μ).toU1Value))).sum := by
  set Φ : JetGaugeAlgebra →+ ℂ := AddMonoidHom.mk'
    (fun a => (eval a).toU1Value)
    (fun a b => by simp [map_add, GaugeAlgebra.add_toU1Value]) with hΦ
  have hΦiter : ∀ μ ∈ r, Φ (iteratedDeriv (r - {μ}) (maurerCartanForm U μ)) =
      constantCoeff ((r.erase μ).foldl (fun f ρ => pderiv ℂ ρ f)
        ((maurerCartanForm U μ).toU1Value)) := by
    intro μ hμ
    show (eval (iteratedDeriv (r - {μ}) (maurerCartanForm U μ))).toU1Value = _
    rw [eval_toU1Value_eq, iteratedDeriv_toU1Value, Multiset.sub_singleton]
  rw [LocalGaugeData.symmetrizedMaurerCartanForm]
  simp only [localGaugeData_iteratedDeriv, localGaugeData_maurerCartan]
  rw [map_smul, GaugeAlgebra.smul_toU1Value]
  congr 1
  rw [show (eval ((r.map fun μ =>
        iteratedDeriv (r - {μ}) (maurerCartanForm U μ)).sum)).toU1Value
      = Φ ((r.map fun μ => iteratedDeriv (r - {μ}) (maurerCartanForm U μ)).sum) from rfl,
    map_multiset_sum, Multiset.map_map]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun μ hμ => hΦiter μ hμ)

/-- The `su(3)` entry of the symmetrized Maurer–Cartan data, through the radial component
  `∑_μ x_μ ω_μ` of the Maurer–Cartan form: a coefficient of that component, normalized by
  the factorials of the multiset. -/
lemma symmetrizedMaurerCartanCoeff_toSU3_eq (U : localGaugeData.truncationKer 0)
    (P : Matrix (Fin 3) (Fin 3) JetRing)
    (hrad : ∑ μ, (X μ : JetRing) • (maurerCartanForm U.1 μ).toSU3Matrix = P)
    (r : Multiset (Fin 1 ⊕ Fin 3)) (hr : r ≠ 0) (i j : Fin 3) :
    (localGaugeData.symmetrizedMaurerCartanCoeff U ⟨r, hr⟩).toSU3Matrix i j =
      (1/(Multiset.card r : ℝ)) • (((∏ ν, Nat.factorial (r.count ν) : ℕ) : ℂ) *
        coeff (Multiset.toFinsupp r) (P i j)) := by
  have hentry : (∑ μ, (X μ : JetRing) • ((maurerCartanForm U.1 μ).toSU3Matrix i j)) =
      P i j := by
    have h1 : (∑ μ, (X μ : JetRing) • ((maurerCartanForm U.1 μ).toSU3Matrix i j)) =
        (∑ μ, (X μ : JetRing) • (maurerCartanForm U.1 μ).toSU3Matrix) i j := by
      rw [Matrix.sum_apply]
      exact Finset.sum_congr rfl fun μ _ => rfl
    rw [h1, hrad]
  rw [LocalGaugeData.symmetrizedMaurerCartanCoeff_apply, localGaugeData_evalLie,
    eval_symmetrizedMaurerCartanForm_toSU3_apply, sum_constantCoeff_foldl_erase, hentry]

/-- The `su(2)` entry of the symmetrized Maurer–Cartan data through the radial
  component. -/
lemma symmetrizedMaurerCartanCoeff_toSU2_eq (U : localGaugeData.truncationKer 0)
    (P : Matrix (Fin 2) (Fin 2) JetRing)
    (hrad : ∑ μ, (X μ : JetRing) • (maurerCartanForm U.1 μ).toSU2Matrix = P)
    (r : Multiset (Fin 1 ⊕ Fin 3)) (hr : r ≠ 0) (i j : Fin 2) :
    (localGaugeData.symmetrizedMaurerCartanCoeff U ⟨r, hr⟩).toSU2Matrix i j =
      (1/(Multiset.card r : ℝ)) • (((∏ ν, Nat.factorial (r.count ν) : ℕ) : ℂ) *
        coeff (Multiset.toFinsupp r) (P i j)) := by
  have hentry : (∑ μ, (X μ : JetRing) • ((maurerCartanForm U.1 μ).toSU2Matrix i j)) =
      P i j := by
    have h1 : (∑ μ, (X μ : JetRing) • ((maurerCartanForm U.1 μ).toSU2Matrix i j)) =
        (∑ μ, (X μ : JetRing) • (maurerCartanForm U.1 μ).toSU2Matrix) i j := by
      rw [Matrix.sum_apply]
      exact Finset.sum_congr rfl fun μ _ => rfl
    rw [h1, hrad]
  rw [LocalGaugeData.symmetrizedMaurerCartanCoeff_apply, localGaugeData_evalLie,
    eval_symmetrizedMaurerCartanForm_toSU2_apply, sum_constantCoeff_foldl_erase, hentry]

/-- The `u(1)` value of the symmetrized Maurer–Cartan data through the radial
  component. -/
lemma symmetrizedMaurerCartanCoeff_toU1_eq (U : localGaugeData.truncationKer 0)
    (p : JetRing)
    (hrad : ∑ μ, (X μ : JetRing) • (maurerCartanForm U.1 μ).toU1Value = p)
    (r : Multiset (Fin 1 ⊕ Fin 3)) (hr : r ≠ 0) :
    (localGaugeData.symmetrizedMaurerCartanCoeff U ⟨r, hr⟩).toU1Value =
      (1/(Multiset.card r : ℝ)) • (((∏ ν, Nat.factorial (r.count ν) : ℕ) : ℂ) *
        coeff (Multiset.toFinsupp r) p) := by
  rw [LocalGaugeData.symmetrizedMaurerCartanCoeff_apply, localGaugeData_evalLie,
    eval_symmetrizedMaurerCartanForm_toU1Value, sum_constantCoeff_foldl_erase, hrad]

/-!

## C. Surjectivity of the symmetrized Maurer–Cartan data

-/

/-- The factorwise construction behind surjectivity: for every hermitian family `E` of
  matrices indexed by nonempty multisets there is a unitary Euler transport `V` based at
  `1` whose radial Maurer–Cartan component `P = ∑_μ x_μ · i (∂_μ V) V†` has, at the
  monomial `r`, the coefficient `|r| / ∏ (r.count ν)!` times `E r`; and `V` has unit
  determinant when the `E r` are traceless. -/
lemma exists_eulerTransport_of_symmetrized {κ : Type} [Fintype κ] [DecidableEq κ]
    (E : {r : Multiset (Fin 1 ⊕ Fin 3) // r ≠ 0} → Matrix κ κ ℂ)
    (hEstar : ∀ x, star (E x) = E x) :
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
  classical
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

/-- Freeness, surjectivity half: every prescribed family of symmetrized Maurer–Cartan
  data is realized by a pure jet, assembled factor by factor from
  `exists_eulerTransport_of_symmetrized`. -/
theorem symmetrizedMaurerCartanCoeff_surjective :
    Function.Surjective localGaugeData.symmetrizedMaurerCartanCoeff := by
  classical
  intro c
  obtain ⟨V₃, P₃, hV₃0, hV₃u, hrad₃, hdet₃, hcoeff₃⟩ :=
    exists_eulerTransport_of_symmetrized (κ := Fin 3) (fun x => (c x).toSU3Matrix)
      (fun x => show star (c x).toSU3Matrix = (c x).toSU3Matrix from (c x).1.2.1)
  obtain ⟨V₂, P₂, hV₂0, hV₂u, hrad₂, hdet₂, hcoeff₂⟩ :=
    exists_eulerTransport_of_symmetrized (κ := Fin 2) (fun x => (c x).toSU2Matrix)
      (fun x => show star (c x).toSU2Matrix = (c x).toSU2Matrix from (c x).2.1.2.1)
  obtain ⟨V₁, P₁, hV₁0, hV₁u, hrad₁, _, hcoeff₁⟩ :=
    exists_eulerTransport_of_symmetrized (κ := Fin 1)
      (fun x => Matrix.of fun _ _ => (c x).toU1Value)
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
    localGaugeData.mem_truncationKer_zero_iff.mpr
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

/-- The Standard Model package is free: the symmetrized Maurer–Cartan data are free
  coordinates on its pure jets. Injectivity is the general
  `LocalGaugeData.symmetrizedMaurerCartanCoeff_injective` of a faithful package, and
  surjectivity is `symmetrizedMaurerCartanCoeff_surjective`. -/
instance instFreeLocalGaugeData : localGaugeData.Free where
  toFaithful := inferInstance
  symmetrizedMaurerCartanCoeff_surjective := symmetrizedMaurerCartanCoeff_surjective

end StandardModel
