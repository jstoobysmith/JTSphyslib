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
open MvPowerSeries JetGaugeAlgebra
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

## The Euler operator toolkit

-/

/-- The formal coordinates of the jet ring are self-adjoint. -/
lemma jetRing_star_X (ρ : Fin 1 ⊕ Fin 3) : star (X ρ : JetRing) = X ρ := by
  ext m
  rw [JetRing.coeff_star, show (X ρ : JetRing) = monomial (Finsupp.single ρ 1) 1 from rfl,
    coeff_monomial]
  split_ifs <;> simp

/-- The Taylor coefficients of a jet multiplied by a formal coordinate: the
  coefficient shifts down by one in that direction. -/
lemma coeff_X_smul (ρ : Fin 1 ⊕ Fin 3) (f : JetRing) (p : (Fin 1 ⊕ Fin 3) →₀ ℕ) :
    coeff p ((X ρ : JetRing) • f) =
      if Finsupp.single ρ 1 ≤ p then coeff (p - Finsupp.single ρ 1) f else 0 := by
  rw [smul_eq_mul, show (X ρ : JetRing) = monomial (Finsupp.single ρ 1) 1 from rfl,
    coeff_monomial_mul]
  split_ifs <;> simp

/-- The Euler (radial) operator acts on Taylor coefficients as multiplication by the
  total degree. -/
lemma coeff_sum_X_smul_pderiv (f : JetRing) (p : (Fin 1 ⊕ Fin 3) →₀ ℕ) :
    coeff p (∑ ρ, (X ρ : JetRing) • pderiv ℂ ρ f) =
      ((Finsupp.degree p : ℕ) : ℂ) * coeff p f := by
  classical
  rw [map_sum]
  have ht : ∀ ρ, coeff p ((X ρ : JetRing) • pderiv ℂ ρ f) = (p ρ : ℂ) * coeff p f := by
    intro ρ
    rw [coeff_X_smul]
    by_cases h : Finsupp.single ρ 1 ≤ p
    · have hρ : 1 ≤ p ρ := by simpa using Finsupp.single_le_iff.mp h
      rw [if_pos h, coeff_pderiv, tsub_add_cancel_of_le h, Finsupp.coe_tsub, Pi.sub_apply,
        Finsupp.single_eq_same, Nat.cast_sub hρ]
      push_cast
      ring
    · have hρ : p ρ = 0 := by
        by_contra hc
        exact h (Finsupp.single_le_iff.mpr (by omega))
      rw [if_neg h, hρ]
      simp
  rw [Finset.sum_congr rfl fun ρ _ => ht ρ, ← Finset.sum_mul, ← Nat.cast_sum,
    ← Finsupp.degree_eq_sum]

/-- The Euler operator on matrices of jets acts entrywise on Taylor coefficients as
  multiplication by the total degree. -/
lemma coeff_sum_X_smul_map_pderiv {κ : Type} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ JetRing) (p : (Fin 1 ⊕ Fin 3) →₀ ℕ) (i j : κ) :
    coeff p ((∑ ρ, (X ρ : JetRing) • M.map (pderiv ℂ ρ)) i j) =
      ((Finsupp.degree p : ℕ) : ℂ) * coeff p (M i j) := by
  rw [show (∑ ρ, (X ρ : JetRing) • M.map (pderiv ℂ ρ)) i j
      = ∑ ρ, (X ρ : JetRing) • pderiv ℂ ρ (M i j) from by
    rw [Matrix.sum_apply]
    exact Finset.sum_congr rfl fun ρ _ => rfl]
  exact coeff_sum_X_smul_pderiv (M i j) p

/-- The vanishing principle for the Euler operator: a matrix of jets vanishing at the
  base point and satisfying `E W = A W + W B` with `A`, `B` vanishing at the base point
  is zero. Each Taylor coefficient of `W` is a multiple of coefficients of strictly
  smaller degree, so all vanish by strong induction on the degree. -/
lemma matrix_eq_zero_of_euler_eq_mul_add_mul {κ : Type} [Fintype κ] [DecidableEq κ]
    {W : Matrix κ κ JetRing} (A B : Matrix κ κ JetRing)
    (hA : ∀ i j, constantCoeff (A i j) = 0) (hB : ∀ i j, constantCoeff (B i j) = 0)
    (h0 : ∀ i j, constantCoeff (W i j) = 0)
    (hW : ∑ ρ, (X ρ : JetRing) • W.map (pderiv ℂ ρ) = A * W + W * B) :
    W = 0 := by
  classical
  have hlow : ∀ p : (Fin 1 ⊕ Fin 3) →₀ ℕ,
      (∀ (i : κ) (j : κ) (q : (Fin 1 ⊕ Fin 3) →₀ ℕ),
        Finsupp.degree q < Finsupp.degree p → coeff q (W i j) = 0) →
      ∀ i j, coeff p ((A * W + W * B) i j) = 0 := by
    intro p hp i j
    have hAW : coeff p ((A * W) i j) = 0 := by
      rw [Matrix.mul_apply, map_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [coeff_mul]
      refine Finset.sum_eq_zero fun q hq => ?_
      rcases eq_or_ne q.1 0 with h1 | h1
      · rw [h1, coeff_zero_eq_constantCoeff, hA, zero_mul]
      · have h4 : Finsupp.degree q.1 + Finsupp.degree q.2 = Finsupp.degree p := by
          rw [← map_add, Finset.mem_antidiagonal.mp hq]
        have h3 := Nat.pos_of_ne_zero fun hc => h1 ((Finsupp.degree_eq_zero_iff _).mp hc)
        rw [hp _ _ q.2 (by omega), mul_zero]
    have hWB : coeff p ((W * B) i j) = 0 := by
      rw [Matrix.mul_apply, map_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [coeff_mul]
      refine Finset.sum_eq_zero fun q hq => ?_
      rcases eq_or_ne q.2 0 with h1 | h1
      · rw [h1, coeff_zero_eq_constantCoeff, hB, mul_zero]
      · have h4 : Finsupp.degree q.1 + Finsupp.degree q.2 = Finsupp.degree p := by
          rw [← map_add, Finset.mem_antidiagonal.mp hq]
        have h3 := Nat.pos_of_ne_zero fun hc => h1 ((Finsupp.degree_eq_zero_iff _).mp hc)
        rw [hp _ _ q.1 (by omega), zero_mul]
    rw [Matrix.add_apply, map_add, hAW, hWB, add_zero]
  have hm : ∀ (n : ℕ) (p : (Fin 1 ⊕ Fin 3) →₀ ℕ), Finsupp.degree p = n →
      ∀ i j, coeff p (W i j) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro p hp i j
      rcases Nat.eq_zero_or_pos n with hn | hn
      · have hp0 : p = 0 := (Finsupp.degree_eq_zero_iff _).mp (by omega)
        rw [hp0, coeff_zero_eq_constantCoeff]
        exact h0 i j
      · have h : coeff p ((∑ ρ, (X ρ : JetRing) • W.map (pderiv ℂ ρ)) i j) =
            coeff p ((A * W + W * B) i j) := congrArg (fun M => coeff p (M i j)) hW
        rw [coeff_sum_X_smul_map_pderiv,
          hlow p (fun i' j' q hq => ih (Finsupp.degree q) (by omega) q rfl i' j') i j] at h
        have hne : ((Finsupp.degree p : ℕ) : ℂ) ≠ 0 := by
          rw [hp]
          exact_mod_cast hn.ne'
        exact (mul_eq_zero.mp h).resolve_left hne
  ext i j : 1
  ext p
  rw [hm (Finsupp.degree p) p rfl i j]
  simp

/-- The Euler (radial) transport of a jet matrix `R` vanishing at the base point:
  a fundamental solution of the radial system `E U = R U` based at the identity,
  built order-by-order by the Euler recursion. -/
lemma exists_matrix_eulerTransport {κ : Type} [Fintype κ] [DecidableEq κ]
    (R : Matrix κ κ JetRing) (hR0 : ∀ i j, constantCoeff (R i j) = 0) :
    ∃ U : Matrix κ κ JetRing, (constantCoeff : JetRing →+* ℂ).mapMatrix U = 1 ∧
      ∑ ρ, (X ρ : JetRing) • U.map (pderiv ℂ ρ) = R * U := by
  classical
  have hRlow : ∀ (M N : Matrix κ κ JetRing) (p : (Fin 1 ⊕ Fin 3) →₀ ℕ),
      (∀ (i : κ) (j : κ) (q : (Fin 1 ⊕ Fin 3) →₀ ℕ),
        Finsupp.degree q < Finsupp.degree p → coeff q (M i j) = coeff q (N i j)) →
      ∀ i j, coeff p ((R * M) i j) = coeff p ((R * N) i j) := fun M N p h i j => by
    simp only [Matrix.mul_apply, map_sum, coeff_mul]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun q hq => ?_
    rcases eq_or_ne q.1 0 with h1 | h1
    · rw [h1, coeff_zero_eq_constantCoeff, hR0, zero_mul, zero_mul]
    · have h4 : Finsupp.degree q.1 + Finsupp.degree q.2 = Finsupp.degree p := by
        rw [← map_add, Finset.mem_antidiagonal.mp hq]
      have h3 := Nat.pos_of_ne_zero fun hc => h1 ((Finsupp.degree_eq_zero_iff _).mp hc)
      rw [h _ _ _ (by omega)]
  set T : Matrix κ κ JetRing → Matrix κ κ JetRing := fun M => 1 + (R * M).map fun f =>
    show JetRing from fun m => if m = 0 then 0 else ((Finsupp.degree m : ℕ) : ℂ)⁻¹ * f m
    with hT
  set U : Matrix κ κ JetRing :=
    Matrix.of fun i j => show JetRing from fun m => (T^[Finsupp.degree m + 1] 1) i j m with hUd
  have hUco : ∀ (p : (Fin 1 ⊕ Fin 3) →₀ ℕ) i j,
      coeff p (U i j) = coeff p ((T^[Finsupp.degree p + 1] 1) i j) := fun _ _ _ => rfl
  have hTco : ∀ (M : Matrix κ κ JetRing) i j (p : (Fin 1 ⊕ Fin 3) →₀ ℕ),
      coeff p ((T M) i j) = coeff p ((1 : Matrix κ κ JetRing) i j) +
        if p = 0 then 0 else ((Finsupp.degree p : ℕ) : ℂ)⁻¹ * coeff p ((R * M) i j) :=
    fun M i j p => by
      simp only [hT]
      rw [Matrix.add_apply, map_add, Matrix.map_apply]
      rfl
  have hmain : ∀ (n : ℕ) (p : (Fin 1 ⊕ Fin 3) →₀ ℕ), Finsupp.degree p = n → ∀ k, n < k →
      ∀ i j, coeff p ((T^[k] 1) i j) = coeff p ((T U) i j) := fun n => by
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro p hp k hk i j
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [Function.iterate_succ_apply', hTco, hTco]
      rcases eq_or_ne p 0 with h0 | h0
      · rw [if_pos h0, if_pos h0]
      · rw [if_neg h0, if_neg h0, hRlow _ U _ (fun i' j' q hq => ?_) i j]
        rw [hUco, ih (Finsupp.degree q) (by omega) q rfl k (by omega) i' j',
          ih (Finsupp.degree q) (by omega) q rfl (Finsupp.degree q + 1) (by omega) i' j']
  have hkey := fun (p : (Fin 1 ⊕ Fin 3) →₀ ℕ) (i j : κ) =>
    (hUco p i j).trans (hmain _ p rfl _ (Nat.lt_succ_self _) i j)
  have hUone : (constantCoeff : JetRing →+* ℂ).mapMatrix U = 1 := by
    ext i j
    simpa [hTco, Matrix.one_apply, apply_ite, coeff_one] using hkey 0 i j
  refine ⟨U, hUone, ?_⟩
  ext i j : 1
  ext p
  rw [coeff_sum_X_smul_map_pderiv]
  rcases eq_or_ne p 0 with rfl | h0
  · rw [show ((Finsupp.degree (0 : (Fin 1 ⊕ Fin 3) →₀ ℕ) : ℕ) : ℂ) = 0 by simp, zero_mul]
    rw [Matrix.mul_apply, map_sum]
    exact (Finset.sum_eq_zero fun k _ => by
      rw [coeff_zero_eq_constantCoeff, map_mul, hR0, zero_mul]).symm
  · rw [hkey p i j, hTco, show coeff p ((1 : Matrix κ κ JetRing) i j) = 0 from by
      simp [Matrix.one_apply, apply_ite, coeff_one, h0], zero_add, if_neg h0, ← mul_assoc,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr fun hc => h0 ((Finsupp.degree_eq_zero_iff p).mp hc)),
      one_mul]

/-!

## Unitarity and determinant of the Euler transport

-/

/-- The entrywise Leibniz rule for matrix products of jets. -/
lemma matrix_map_pderiv_mul {κ : Type} [Fintype κ] [DecidableEq κ] (ρ : Fin 1 ⊕ Fin 3)
    (M N : Matrix κ κ JetRing) :
    (M * N).map (pderiv ℂ ρ) = M.map (pderiv ℂ ρ) * N + M * N.map (pderiv ℂ ρ) := by
  ext i j : 1
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum,
    Derivation.leibniz, smul_eq_mul]
  exact (Finset.sum_congr rfl fun k _ => by ring).trans Finset.sum_add_distrib

/-- The Euler operator on matrices of jets is a derivation. -/
lemma sum_X_smul_map_pderiv_mul {κ : Type} [Fintype κ] [DecidableEq κ]
    (M N : Matrix κ κ JetRing) :
    ∑ ρ, (X ρ : JetRing) • (M * N).map (pderiv ℂ ρ) =
      (∑ ρ, (X ρ : JetRing) • M.map (pderiv ℂ ρ)) * N +
        M * ∑ ρ, (X ρ : JetRing) • N.map (pderiv ℂ ρ) := by
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [matrix_map_pderiv_mul, smul_add, Matrix.smul_mul, Matrix.mul_smul]

/-- The Euler operator commutes with the conjugate transpose. -/
lemma sum_X_smul_map_pderiv_star {κ : Type} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ JetRing) :
    ∑ ρ, (X ρ : JetRing) • (star M).map (pderiv ℂ ρ) =
      star (∑ ρ, (X ρ : JetRing) • M.map (pderiv ℂ ρ)) := by
  ext i j : 1
  simp only [Matrix.sum_apply, Matrix.star_apply, Matrix.smul_apply, Matrix.map_apply,
    smul_eq_mul, star_sum, star_mul', jetRing_star_X, ← JetRing.pderiv_star]

/-- The Euler operator kills the identity matrix. -/
lemma sum_X_smul_map_pderiv_one {κ : Type} [Fintype κ] [DecidableEq κ] :
    ∑ ρ, (X ρ : JetRing) • (1 : Matrix κ κ JetRing).map (pderiv ℂ ρ) = 0 := by
  refine Finset.sum_eq_zero fun ρ _ => ?_
  rw [show (1 : Matrix κ κ JetRing).map (pderiv ℂ ρ) = 0 from Matrix.ext fun i j => by
    simp [Matrix.map_apply, Matrix.one_apply, apply_ite (pderiv ℂ ρ)], smul_zero]

/-- A fundamental solution of the radial system `E U = R U` based at the identity is
  unitary when `R` is anti-hermitian: `U U† − 1` vanishes at the base point and
  satisfies a homogeneous linear radial system, so it vanishes identically. -/
lemma eulerTransport_mul_star {κ : Type} [Fintype κ] [DecidableEq κ]
    {R U : Matrix κ κ JetRing} (hRstar : star R = -R)
    (hR0 : ∀ i j, constantCoeff (R i j) = 0)
    (hU0 : (constantCoeff : JetRing →+* ℂ).mapMatrix U = 1)
    (hEU : ∑ ρ, (X ρ : JetRing) • U.map (pderiv ℂ ρ) = R * U) :
    U * star U = 1 := by
  have hEstar : ∑ ρ, (X ρ : JetRing) • (star U).map (pderiv ℂ ρ) = -(star U * R) := by
    rw [sum_X_smul_map_pderiv_star, hEU, star_mul, hRstar, Matrix.mul_neg]
  have hW0 : (constantCoeff : JetRing →+* ℂ).mapMatrix (U * star U - 1) = 0 := by
    rw [map_sub, map_mul, JetGaugeGroupI.mapMatrix_constantCoeff_star, hU0, star_one,
      mul_one, map_one, sub_self]
  have h0 : ∀ i j, constantCoeff ((U * star U - 1) i j) = 0 := fun i j => by
    simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using congrArg (fun M => M i j) hW0
  have hB : ∀ i j, constantCoeff ((-R) i j) = 0 := fun i j => by
    simp [hR0 i j]
  have hEW : ∑ ρ, (X ρ : JetRing) • (U * star U - 1).map (pderiv ℂ ρ) =
      R * (U * star U - 1) + (U * star U - 1) * (-R) := by
    have hsub : ∀ ρ : Fin 1 ⊕ Fin 3, (U * star U - 1).map (pderiv ℂ ρ) =
        (U * star U).map (pderiv ℂ ρ) - (1 : Matrix κ κ JetRing).map (pderiv ℂ ρ) :=
      fun ρ => Matrix.ext fun i j => by simp [Matrix.map_apply]
    simp only [hsub, smul_sub, Finset.sum_sub_distrib]
    rw [sum_X_smul_map_pderiv_mul, hEU, hEstar, sum_X_smul_map_pderiv_one, sub_zero]
    noncomm_ring
  exact sub_eq_zero.mp (matrix_eq_zero_of_euler_eq_mul_add_mul R (-R) hR0 hB h0 hEW)

/-- The scalar vanishing principle for the Euler operator: a jet vanishing at the base
  point that is killed by the Euler operator is zero. -/
lemma eq_zero_of_sum_X_smul_pderiv_eq_zero {f : JetRing} (h0 : constantCoeff f = 0)
    (hf : ∑ ρ, (X ρ : JetRing) • pderiv ℂ ρ f = 0) : f = 0 := by
  ext p
  rcases eq_or_ne p 0 with rfl | hp
  · simpa [coeff_zero_eq_constantCoeff] using h0
  · have h := congrArg (coeff p) hf
    rw [coeff_sum_X_smul_pderiv, map_zero] at h
    have hne : ((Finsupp.degree p : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr fun hc => hp ((Finsupp.degree_eq_zero_iff p).mp hc)
    simpa using (mul_eq_zero.mp h).resolve_left hne

/-- A fundamental solution of the radial system `E U = R U` based at the identity has
  determinant one when `R` is traceless: by Jacobi's formula the determinant is killed
  by the Euler operator, so it is the constant `1`. -/
lemma eulerTransport_det {κ : Type} [Fintype κ] [DecidableEq κ]
    {R U : Matrix κ κ JetRing}
    (hjac : ∀ (M : Matrix κ κ JetRing) (μ : Fin 1 ⊕ Fin 3),
      pderiv ℂ μ M.det = (M.map (pderiv ℂ μ) * M.adjugate).trace)
    (hRtr : R.trace = 0)
    (hU0 : (constantCoeff : JetRing →+* ℂ).mapMatrix U = 1)
    (hEU : ∑ ρ, (X ρ : JetRing) • U.map (pderiv ℂ ρ) = R * U) :
    U.det = 1 := by
  have hEdet : ∑ ρ, (X ρ : JetRing) • pderiv ℂ ρ U.det = 0 := by
    calc ∑ ρ, (X ρ : JetRing) • pderiv ℂ ρ U.det
        = ∑ ρ, (X ρ : JetRing) • (U.map (pderiv ℂ ρ) * U.adjugate).trace := by
          exact Finset.sum_congr rfl fun ρ _ => by rw [hjac]
      _ = ((∑ ρ, (X ρ : JetRing) • U.map (pderiv ℂ ρ)) * U.adjugate).trace := by
          rw [Finset.sum_mul, Matrix.trace_sum]
          exact Finset.sum_congr rfl fun ρ _ => by
            rw [Matrix.smul_mul, Matrix.trace_smul]
      _ = (R * (U.det • (1 : Matrix κ κ JetRing))).trace := by
          rw [hEU, Matrix.mul_assoc, Matrix.mul_adjugate]
      _ = 0 := by
          rw [mul_smul_comm, mul_one, Matrix.trace_smul, hRtr, smul_zero]
  have hd0 : constantCoeff (U.det - 1) = 0 := by
    rw [map_sub, map_one, RingHom.map_det, hU0, Matrix.det_one, sub_self]
  have hEd : ∑ ρ, (X ρ : JetRing) • pderiv ℂ ρ (U.det - 1) = 0 := by
    calc ∑ ρ, (X ρ : JetRing) • pderiv ℂ ρ (U.det - 1)
        = ∑ ρ, (X ρ : JetRing) • pderiv ℂ ρ U.det := by
          exact Finset.sum_congr rfl fun ρ _ => by rw [map_sub, pderiv_one, sub_zero]
      _ = 0 := hEdet
  exact sub_eq_zero.mp (eq_zero_of_sum_X_smul_pderiv_eq_zero hd0 hEd)

/-!

## Multiset derivative bookkeeping

-/

/-- Iterated formal derivatives over a multiset commute with a single derivative. -/
lemma foldl_pderiv_pderiv (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (f : JetRing) :
    s.foldl (fun f ρ => pderiv ℂ ρ f) (pderiv ℂ μ f) =
      pderiv ℂ μ (s.foldl (fun f ρ => pderiv ℂ ρ f) f) := by
  induction s using Multiset.induction_on generalizing f with
  | empty => simp
  | cons a t ih =>
      rw [Multiset.foldl_cons, Multiset.foldl_cons, JetRing.pderiv_comm, ih]

/-- The base-point value of an iterated formal derivative is the corresponding Taylor
  coefficient with the factorial normalization. -/
lemma constantCoeff_foldl_pderiv (s : Multiset (Fin 1 ⊕ Fin 3)) (f : JetRing) :
    constantCoeff (s.foldl (fun f ρ => pderiv ℂ ρ f) f) =
      ((∏ ν, Nat.factorial (s.count ν) : ℕ) : ℂ) * coeff s.toFinsupp f := by
  induction s using Multiset.induction_on generalizing f with
  | empty => simp [coeff_zero_eq_constantCoeff]
  | cons a t ih =>
      rw [Multiset.foldl_cons, ih, coeff_pderiv]
      have hfin : (a ::ₘ t).toFinsupp = t.toFinsupp + Finsupp.single a 1 := by
        rw [show (a ::ₘ t : Multiset (Fin 1 ⊕ Fin 3)) = {a} + t from
          (Multiset.singleton_add a t).symm, map_add, Multiset.toFinsupp_singleton, add_comm]
      have hfac : (∏ ν, Nat.factorial ((a ::ₘ t).count ν) : ℕ) =
          (t.count a + 1) * ∏ ν, Nat.factorial (t.count ν) := by
        rw [show (∏ ν, Nat.factorial ((a ::ₘ t).count ν) : ℕ) =
            ∏ ν, ((if ν = a then t.count a + 1 else 1) * Nat.factorial (t.count ν)) from
          Finset.prod_congr rfl fun ν _ => by
            rcases eq_or_ne ν a with rfl | h
            · rw [Multiset.count_cons_self, Nat.factorial_succ, if_pos rfl]
            · rw [Multiset.count_cons_of_ne h, if_neg h, one_mul],
          Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ a]
        simp
      rw [hfin, hfac, Multiset.toFinsupp_apply]
      push_cast
      ring

/-- The key combinatorial identity behind the symmetrized Maurer–Cartan data: the sum
  over a multiset `r` of base-point values of iterated derivatives of `g` in the
  complementary directions is, up to factorials, the Taylor coefficient at `r` of the
  radial contraction `∑ μ x_μ g_μ`. -/
lemma sum_constantCoeff_foldl_erase (g : (Fin 1 ⊕ Fin 3) → JetRing)
    (r : Multiset (Fin 1 ⊕ Fin 3)) :
    (r.map fun μ => constantCoeff ((r.erase μ).foldl (fun f ρ => pderiv ℂ ρ f) (g μ))).sum =
      ((∏ ν, Nat.factorial (r.count ν) : ℕ) : ℂ) *
        coeff r.toFinsupp (∑ μ, (X μ : JetRing) • g μ) := by
  classical
  rw [Finset.sum_multiset_map_count,
    Finset.sum_subset (Finset.subset_univ r.toFinset) (fun x _ hx => by
      rw [Multiset.count_eq_zero.mpr fun hmem => hx (Multiset.mem_toFinset.mpr hmem),
        zero_smul]),
    map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [coeff_X_smul, constantCoeff_foldl_pderiv]
  by_cases hμ : μ ∈ r
  · rw [if_pos (Finsupp.single_le_iff.mpr (by
      rw [Multiset.toFinsupp_apply]
      exact Multiset.one_le_count_iff_mem.mpr hμ))]
    have herase : (r.erase μ).toFinsupp = r.toFinsupp - Finsupp.single μ 1 := by
      ext ν
      rw [Multiset.toFinsupp_apply, Finsupp.coe_tsub, Pi.sub_apply, Multiset.toFinsupp_apply,
        Finsupp.single_apply]
      rcases eq_or_ne μ ν with rfl | h
      · rw [Multiset.count_erase_self, if_pos rfl]
      · rw [Multiset.count_erase_of_ne h.symm, if_neg h, Nat.sub_zero]
    have hfac : r.count μ * ∏ ν, Nat.factorial ((r.erase μ).count ν) =
        ∏ ν, Nat.factorial (r.count ν) := by
      rw [← Finset.mul_prod_erase Finset.univ
          (fun ν => Nat.factorial ((r.erase μ).count ν)) (Finset.mem_univ μ),
        ← Finset.mul_prod_erase Finset.univ
          (fun ν => Nat.factorial (r.count ν)) (Finset.mem_univ μ),
        Multiset.count_erase_self,
        Finset.prod_congr rfl fun ν hν =>
          congrArg Nat.factorial
            (Multiset.count_erase_of_ne (Finset.mem_erase.mp hν).1 r),
        ← mul_assoc, Nat.mul_factorial_pred (Multiset.count_pos.mpr hμ).ne']
    rw [herase, nsmul_eq_mul, ← mul_assoc, ← Nat.cast_mul, hfac]
  · rw [if_neg fun hle => hμ (Multiset.one_le_count_iff_mem.mp (by
        simpa [Multiset.toFinsupp_apply] using Finsupp.single_le_iff.mp hle)),
      mul_zero, Multiset.count_eq_zero.mpr hμ, zero_smul]

/-!

## Componentwise iterated derivatives on the jet gauge algebra

-/

namespace JetGaugeAlgebra

lemma iteratedDeriv_toSU3Matrix (s : Multiset (Fin 1 ⊕ Fin 3)) (a : JetGaugeAlgebra) :
    (iteratedDeriv s a).toSU3Matrix =
      a.toSU3Matrix.map fun f => s.foldl (fun f ρ => pderiv ℂ ρ f) f := by
  induction s using Multiset.induction_on with
  | empty => simp [iteratedDeriv_zero]
  | cons μ t ih =>
      rw [iteratedDeriv_cons, LinearMap.comp_apply, deriv_toSU3Matrix, ih]
      ext i j : 1
      simp only [Matrix.map_apply, Multiset.foldl_cons]
      exact (foldl_pderiv_pderiv t μ _).symm

lemma iteratedDeriv_toSU2Matrix (s : Multiset (Fin 1 ⊕ Fin 3)) (a : JetGaugeAlgebra) :
    (iteratedDeriv s a).toSU2Matrix =
      a.toSU2Matrix.map fun f => s.foldl (fun f ρ => pderiv ℂ ρ f) f := by
  induction s using Multiset.induction_on with
  | empty => simp [iteratedDeriv_zero]
  | cons μ t ih =>
      rw [iteratedDeriv_cons, LinearMap.comp_apply, deriv_toSU2Matrix, ih]
      ext i j : 1
      simp only [Matrix.map_apply, Multiset.foldl_cons]
      exact (foldl_pderiv_pderiv t μ _).symm

lemma iteratedDeriv_toU1Value (s : Multiset (Fin 1 ⊕ Fin 3)) (a : JetGaugeAlgebra) :
    (iteratedDeriv s a).toU1Value = s.foldl (fun f ρ => pderiv ℂ ρ f) a.toU1Value := by
  induction s using Multiset.induction_on with
  | empty => simp [iteratedDeriv_zero]
  | cons μ t ih =>
      rw [iteratedDeriv_cons, LinearMap.comp_apply, deriv_toU1Value, ih,
        Multiset.foldl_cons, foldl_pderiv_pderiv]

lemma eval_toSU3Matrix_apply (a : JetGaugeAlgebra) (i j : Fin 3) :
    (eval a).toSU3Matrix i j = constantCoeff (a.toSU3Matrix i j) := by
  rw [show eval a = taylorCoeff 0 a from rfl, taylorCoeff_toSU3Matrix, Matrix.map_apply,
    show Multiset.toFinsupp (0 : Multiset (Fin 1 ⊕ Fin 3)) = 0 from map_zero _,
    coeff_zero_eq_constantCoeff]

lemma eval_toSU2Matrix_apply (a : JetGaugeAlgebra) (i j : Fin 2) :
    (eval a).toSU2Matrix i j = constantCoeff (a.toSU2Matrix i j) := by
  rw [show eval a = taylorCoeff 0 a from rfl, taylorCoeff_toSU2Matrix, Matrix.map_apply,
    show Multiset.toFinsupp (0 : Multiset (Fin 1 ⊕ Fin 3)) = 0 from map_zero _,
    coeff_zero_eq_constantCoeff]

lemma eval_toU1Value_eq (a : JetGaugeAlgebra) :
    (eval a).toU1Value = constantCoeff a.toU1Value := by
  rw [show eval a = taylorCoeff 0 a from rfl, taylorCoeff_toU1Value,
    show Multiset.toFinsupp (0 : Multiset (Fin 1 ⊕ Fin 3)) = 0 from map_zero _,
    coeff_zero_eq_constantCoeff]

end JetGaugeAlgebra

/-- The `su(3)`-entry of the evaluated symmetrized Maurer–Cartan form, as a sum of
  base-point values of iterated derivatives of the Maurer–Cartan form entries. -/
lemma eval_symmetrizedMaurerCartanForm_toSU3_apply (U : JetGaugeGroupI)
    (r : Multiset (Fin 1 ⊕ Fin 3)) (i j : Fin 3) :
    (eval (symmetrizedMaurerCartanForm U r)).toSU3Matrix i j =
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
  rw [symmetrizedMaurerCartanForm, map_smul, GaugeAlgebra.smul_toSU3Matrix,
    Matrix.smul_apply]
  congr 1
  rw [show (eval ((r.map fun μ =>
        iteratedDeriv (r - {μ}) (maurerCartanForm U μ)).sum)).toSU3Matrix i j
      = Φ ((r.map fun μ => iteratedDeriv (r - {μ}) (maurerCartanForm U μ)).sum) from rfl,
    map_multiset_sum, Multiset.map_map]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun μ hμ => hΦiter μ hμ)

/-- The `su(2)`-entry of the evaluated symmetrized Maurer–Cartan form. -/
lemma eval_symmetrizedMaurerCartanForm_toSU2_apply (U : JetGaugeGroupI)
    (r : Multiset (Fin 1 ⊕ Fin 3)) (i j : Fin 2) :
    (eval (symmetrizedMaurerCartanForm U r)).toSU2Matrix i j =
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
  rw [symmetrizedMaurerCartanForm, map_smul, GaugeAlgebra.smul_toSU2Matrix,
    Matrix.smul_apply]
  congr 1
  rw [show (eval ((r.map fun μ =>
        iteratedDeriv (r - {μ}) (maurerCartanForm U μ)).sum)).toSU2Matrix i j
      = Φ ((r.map fun μ => iteratedDeriv (r - {μ}) (maurerCartanForm U μ)).sum) from rfl,
    map_multiset_sum, Multiset.map_map]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun μ hμ => hΦiter μ hμ)

/-- The `u(1)`-value of the evaluated symmetrized Maurer–Cartan form. -/
lemma eval_symmetrizedMaurerCartanForm_toU1Value (U : JetGaugeGroupI)
    (r : Multiset (Fin 1 ⊕ Fin 3)) :
    (eval (symmetrizedMaurerCartanForm U r)).toU1Value =
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
  rw [symmetrizedMaurerCartanForm, map_smul, GaugeAlgebra.smul_toU1Value]
  congr 1
  rw [show (eval ((r.map fun μ =>
        iteratedDeriv (r - {μ}) (maurerCartanForm U μ)).sum)).toU1Value
      = Φ ((r.map fun μ => iteratedDeriv (r - {μ}) (maurerCartanForm U μ)).sum) from rfl,
    map_multiset_sum, Multiset.map_map]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun μ hμ => hΦiter μ hμ)

/-!

## Jacobi's formula on the matrix factors, and degree bookkeeping

-/

lemma jacobi_fin3 (M : Matrix (Fin 3) (Fin 3) JetRing) (μ : Fin 1 ⊕ Fin 3) :
    pderiv ℂ μ M.det = (M.map (pderiv ℂ μ) * M.adjugate).trace := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.map_apply, Matrix.adjugate_fin_three, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Matrix.head_fin_const, Matrix.empty_val', Matrix.cons_val_fin_one,
    map_sub, map_add, Derivation.leibniz, smul_eq_mul]
  ring

lemma jacobi_fin2 (M : Matrix (Fin 2) (Fin 2) JetRing) (μ : Fin 1 ⊕ Fin 3) :
    pderiv ℂ μ M.det = (M.map (pderiv ℂ μ) * M.adjugate).trace := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.adjugate_fin_two, Matrix.trace_fin_two, Matrix.mul_apply,
    Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.empty_val', Matrix.cons_val_fin_one, Fin.sum_univ_two, Matrix.cons_val_one,
    map_sub, Derivation.leibniz, smul_eq_mul]
  ring

lemma degree_toFinsupp_eq_card (r : Multiset (Fin 1 ⊕ Fin 3)) :
    Finsupp.degree (Multiset.toFinsupp r) = Multiset.card r := by
  rw [Finsupp.degree_eq_sum, Finset.sum_congr rfl fun ν _ => Multiset.toFinsupp_apply r ν,
    ← Finset.sum_subset (Finset.subset_univ r.toFinset) (fun x _ hx =>
      Multiset.count_eq_zero.mpr fun hmem => hx (Multiset.mem_toFinset.mpr hmem)),
    Multiset.toFinset_sum_count_eq]

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
