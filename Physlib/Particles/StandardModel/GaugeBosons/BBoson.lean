/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.Jet
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
public import Physlib.Particles.StandardModel.GaugeGroup.MaurerCartan
/-!
# The B boson

The hypercharge gauge boson field `B_μ`: the gauge boson of the `U(1)` factor of
the Standard Model gauge group, with one Lorentz index, valued in the
one-dimensional adjoint of `U(1)`, modelled as the real vector space of hermitian
complex numbers.

The physical Z boson and photon are the electroweak-mixed combinations of this
field with the neutral `SU(2)` boson; before mixing, the `U(1)` factor's gauge
boson is the B boson formalized here.

-/

@[expose] public section

namespace MvPowerSeries

variable {σ R : Type*}

/-!

## Ab. The exponential of a monomial

The gauge invariants of the B-boson jet algebra are computed below by realizing
arbitrary translations of the jet coordinates through explicit local `U(1)` gauge
transformations. These are the formal exponentials `exp (c X^w)` of a single
monomial, defined here coefficientwise; the exponential property
`exp(c X^w) exp(c' X^w) = exp((c + c') X^w)` gives unitarity for imaginary `c`,
and the chain rule gives their Maurer–Cartan series.

-/

section ExpMonomial

variable {K : Type*} [Field K] [CharZero K] {w : σ →₀ ℕ}

open Classical in
/-- The formal exponential of `c` times the monomial with exponent `w`: the power
  series `∑ₙ (cⁿ/n!) X^{n w}`, defined coefficientwise. -/
noncomputable def expMonomial (c : K) (w : σ →₀ ℕ) : MvPowerSeries σ K :=
  fun k => if h : ∃ n : ℕ, k = n • w then c ^ h.choose / (h.choose.factorial : K) else 0

/-- A nonzero exponent has a coordinate at which it is nonzero. -/
lemma exists_apply_ne_zero_of_ne_zero (hw : w ≠ 0) : ∃ ρ, w ρ ≠ 0 := by
  obtain ⟨ρ, hρ⟩ := Finsupp.ne_iff.mp hw
  exact ⟨ρ, by simpa using hρ⟩

/-- Multiples of a nonzero exponent determine the multiplier. -/
lemma nsmul_right_cancel (hw : w ≠ 0) {n m : ℕ} (h : n • w = m • w) : n = m := by
  obtain ⟨ρ, hρ⟩ := exists_apply_ne_zero_of_ne_zero hw
  have h' := DFunLike.congr_fun h ρ
  simp only [Finsupp.smul_apply, smul_eq_mul] at h'
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hρ) h'

omit [CharZero K] in
/-- The Taylor coefficient of the exponential of a monomial at a multiple of the
  exponent. -/
lemma coeff_expMonomial_nsmul (hw : w ≠ 0) (c : K) (n : ℕ) :
    coeff (n • w) (expMonomial c w) = c ^ n / (n.factorial : K) := by
  have h : ∃ m : ℕ, n • w = m • w := ⟨n, rfl⟩
  rw [coeff_apply]
  simp only [expMonomial]
  rw [dif_pos h, show h.choose = n from (nsmul_right_cancel hw h.choose_spec).symm]

omit [CharZero K] in
/-- The Taylor coefficients of the exponential of a monomial vanish away from the
  multiples of the exponent. -/
lemma coeff_expMonomial_of_forall_ne (c : K) {k : σ →₀ ℕ} (hk : ∀ n : ℕ, k ≠ n • w) :
    coeff k (expMonomial c w) = 0 := by
  rw [coeff_apply]
  simp only [expMonomial]
  rw [dif_neg (not_exists.mpr hk)]

/-- The exponential property: exponentials of the same monomial multiply by adding
  the scalars. -/
lemma expMonomial_mul_expMonomial (hw : w ≠ 0) (c c' : K) :
    expMonomial c w * expMonomial c' w = expMonomial (c + c') w := by
  classical
  ext k
  by_cases hk : ∃ n : ℕ, k = n • w
  · obtain ⟨N, rfl⟩ := hk
    rw [coeff_mul, coeff_expMonomial_nsmul hw]
    have hsub : (Finset.range (N + 1)).image (fun n => (n • w, (N - n) • w)) ⊆
        Finset.antidiagonal (N • w) := by
      intro p hp
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hp
      rw [Finset.mem_antidiagonal, ← add_smul,
        Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))]
    have hvanish : ∀ p ∈ Finset.antidiagonal (N • w),
        p ∉ (Finset.range (N + 1)).image (fun n => (n • w, (N - n) • w)) →
        coeff p.1 (expMonomial c w) * coeff p.2 (expMonomial c' w) = 0 := by
      intro p hp hpn
      by_cases h1 : ∃ n : ℕ, p.1 = n • w
      · obtain ⟨n₁, h1⟩ := h1
        exfalso
        apply hpn
        have hsum : p.1 + p.2 = N • w := Finset.mem_antidiagonal.mp hp
        obtain ⟨ρ, hρ⟩ := exists_apply_ne_zero_of_ne_zero hw
        have hcoords : ∀ ρ', n₁ * w ρ' + p.2 ρ' = N * w ρ' := by
          intro ρ'
          have h' := DFunLike.congr_fun hsum ρ'
          simpa [h1, Finsupp.smul_apply] using h'
        have hle : n₁ ≤ N :=
          Nat.le_of_mul_le_mul_right (by have := hcoords ρ; omega)
            (Nat.pos_of_ne_zero hρ)
        have h2 : p.2 = (N - n₁) • w := by
          ext ρ'
          rw [Finsupp.smul_apply, smul_eq_mul, Nat.sub_mul]
          have := hcoords ρ'
          omega
        exact Finset.mem_image.mpr
          ⟨n₁, Finset.mem_range.mpr (Nat.lt_succ_of_le hle), by rw [← h1, ← h2]⟩
      · rw [coeff_expMonomial_of_forall_ne c (not_exists.mp h1), zero_mul]
    rw [← Finset.sum_subset hsub hvanish,
      Finset.sum_image (fun n _ m _ h => nsmul_right_cancel hw (congrArg Prod.fst h)),
      add_pow, Finset.sum_div]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [coeff_expMonomial_nsmul hw, coeff_expMonomial_nsmul hw]
    have hle : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    have hfact : ((N.choose n : K)) * (n.factorial : K) * ((N - n).factorial : K) =
        (N.factorial : K) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → K)
        (Nat.choose_mul_factorial_mul_factorial hle)
    have h1 : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have h2 : ((N - n).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (N - n).factorial_ne_zero
    have h3 : (N.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr N.factorial_ne_zero
    rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero h1 h2) h3]
    linear_combination (-(c ^ n * c' ^ (N - n))) * hfact
  · rw [coeff_expMonomial_of_forall_ne _ (not_exists.mp hk), coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    by_cases h1 : ∃ n : ℕ, p.1 = n • w
    · by_cases h2 : ∃ n : ℕ, p.2 = n • w
      · exfalso
        obtain ⟨n₁, h1⟩ := h1
        obtain ⟨n₂, h2⟩ := h2
        exact hk ⟨n₁ + n₂, by rw [← Finset.mem_antidiagonal.mp hp, h1, h2, add_smul]⟩
      · rw [coeff_expMonomial_of_forall_ne _ (not_exists.mp h2), mul_zero]
    · rw [coeff_expMonomial_of_forall_ne _ (not_exists.mp h1), zero_mul]

/-- The coefficientwise star of the exponential of a monomial is the exponential at
  the starred scalar. -/
lemma star_expMonomial {m : (Fin 1 ⊕ Fin 3) →₀ ℕ} (hw : m ≠ 0) (c : ℂ) :
    star (expMonomial c m : JetRing) = expMonomial (star c) m := by
  ext k
  rw [JetRing.coeff_star]
  by_cases hk : ∃ n : ℕ, k = n • m
  · obtain ⟨n, rfl⟩ := hk
    rw [coeff_expMonomial_nsmul hw, coeff_expMonomial_nsmul hw, star_div₀, star_pow,
      star_natCast]
  · rw [coeff_expMonomial_of_forall_ne _ (not_exists.mp hk),
      coeff_expMonomial_of_forall_ne _ (not_exists.mp hk), star_zero]

/-- The exponential of a monomial at scalar zero is one. -/
lemma expMonomial_zero (hw : w ≠ 0) : expMonomial (0 : K) w = 1 := by
  classical
  ext k
  by_cases hk : ∃ n : ℕ, k = n • w
  · obtain ⟨n, rfl⟩ := hk
    rw [coeff_expMonomial_nsmul hw, coeff_one]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [if_pos (zero_smul ℕ w)]
      simp
    · have hne : ¬n • w = 0 := by
        obtain ⟨ρ, hρ⟩ := exists_apply_ne_zero_of_ne_zero hw
        intro h0
        have h' := DFunLike.congr_fun h0 ρ
        simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply,
          Nat.mul_eq_zero] at h'
        omega
      rw [zero_pow (Nat.pos_iff_ne_zero.mp hn), zero_div, if_neg hne]
  · rw [coeff_expMonomial_of_forall_ne _ (not_exists.mp hk), coeff_one,
      if_neg (fun h => hk ⟨0, by rw [h, zero_smul]⟩)]

/-- The chain rule for the exponential of a monomial:
  `∂_ν exp(c X^w) = c w_ν X^{w - e_ν} exp(c X^w)`. -/
lemma pderiv_expMonomial (hw : w ≠ 0) (ν : σ) (c : K) :
    pderiv K ν (expMonomial c w) =
      (c * (w ν : K)) • (monomial (w - Finsupp.single ν 1) 1 * expMonomial c w) := by
  classical
  ext k
  rw [coeff_pderiv, map_smul, smul_eq_mul, coeff_monomial_mul]
  by_cases hA : ∃ n : ℕ, k + Finsupp.single ν 1 = n • w
  · obtain ⟨n, hn⟩ := hA
    have hcoords : ∀ ρ, k ρ + (Finsupp.single ν 1) ρ = n * w ρ := by
      intro ρ
      have h' := DFunLike.congr_fun hn ρ
      simpa [Finsupp.smul_apply] using h'
    have hkν : k ν + 1 = n * w ν := by
      have := hcoords ν
      rwa [Finsupp.single_eq_same] at this
    have hnpos : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; omega
      · exact h0
    have hwνpos : 0 < w ν := by
      rcases Nat.eq_zero_or_pos (w ν) with h0 | h0
      · rw [h0, Nat.mul_zero] at hkν; omega
      · exact h0
    have hdk : w - Finsupp.single ν 1 ≤ k := by
      rw [Finsupp.le_def]
      intro ρ
      rw [Finsupp.tsub_apply]
      have h1 := hcoords ρ
      have h2 : w ρ ≤ n * w ρ := Nat.le_mul_of_pos_left _ hnpos
      by_cases hρν : ρ = ν
      · subst hρν
        rw [Finsupp.single_eq_same] at h1 ⊢
        omega
      · have hsρ : (Finsupp.single ν 1) ρ = 0 :=
          Finsupp.single_eq_of_ne hρν
        rw [hsρ] at h1 ⊢
        omega
    have hkd : k - (w - Finsupp.single ν 1) = (n - 1) • w := by
      ext ρ
      rw [Finsupp.tsub_apply, Finsupp.tsub_apply, Finsupp.smul_apply, smul_eq_mul,
        Nat.sub_mul, one_mul]
      have h1 := hcoords ρ
      have h2 : w ρ ≤ n * w ρ := Nat.le_mul_of_pos_left _ hnpos
      by_cases hρν : ρ = ν
      · subst hρν
        rw [Finsupp.single_eq_same] at h1 ⊢
        omega
      · have hsρ : (Finsupp.single ν 1) ρ = 0 :=
          Finsupp.single_eq_of_ne hρν
        rw [hsρ] at h1 ⊢
        omega
    rw [if_pos hdk, one_mul, hkd, hn, coeff_expMonomial_nsmul hw,
      coeff_expMonomial_nsmul hw]
    have hcast : ((k ν : K) + 1) = (n : K) * (w ν : K) := by exact_mod_cast hkν
    rw [hcast]
    have hfac : (n.factorial : K) = (n : K) * ((n - 1).factorial : K) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → K)
        (Nat.mul_factorial_pred (Nat.pos_iff_ne_zero.mp hnpos)).symm
    have hpow : c ^ n = c * c ^ (n - 1) := by
      conv_lhs => rw [show n = 1 + (n - 1) by omega, pow_add, pow_one]
    rw [hfac, hpow]
    have h1 : ((n : K)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hnpos)
    have h2 : (((n - 1).factorial : K)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
  · rw [coeff_expMonomial_of_forall_ne _ (not_exists.mp hA), zero_mul]
    by_cases hwv : w ν = 0
    · rw [hwv]
      simp
    · have hzero : (if w - Finsupp.single ν 1 ≤ k then
          1 * coeff (k - (w - Finsupp.single ν 1)) (expMonomial c w) else 0) = 0 := by
        split_ifs with hdk
        · rw [one_mul]
          refine coeff_expMonomial_of_forall_ne _ fun m hm => ?_
          apply hA
          refine ⟨m + 1, ?_⟩
          have hle : Finsupp.single ν 1 ≤ w :=
            Finsupp.single_le_iff.mpr (Nat.pos_of_ne_zero hwv)
          have h1 : k - (w - Finsupp.single ν 1) + (w - Finsupp.single ν 1) = k :=
            tsub_add_cancel_of_le hdk
          have h2 : (w - Finsupp.single ν 1) + Finsupp.single ν 1 = w :=
            tsub_add_cancel_of_le hle
          calc k + Finsupp.single ν 1
              = k - (w - Finsupp.single ν 1) + (w - Finsupp.single ν 1) +
                Finsupp.single ν 1 := by rw [h1]
            _ = m • w + w := by rw [hm, add_assoc, h2]
            _ = (m + 1) • w := by rw [add_smul, one_smul]
        · rfl
      rw [hzero, mul_zero]

end ExpMonomial

end MvPowerSeries

namespace StandardModel

open TensorProduct

/-!

## A. The B-boson field
-/

/-- The target vector space of the B-boson field `B_μ`. It carries one Lorentz
  index, and is valued in the real vector space of hermitian complex numbers,
  corresponding to the adjoint of `U(1)`. -/
@[ext]
structure BBoson where
  /-- The Lorentz index together with the adjoint (hermitian) factor. -/
  val : Lorentz.Vector ⊗[ℝ] selfAdjoint ℂ

namespace BBoson
open Module
/-!

## B. Linear structure
-/

def valEquiv : BBoson ≃ Lorentz.Vector ⊗[ℝ] selfAdjoint ℂ where
  toFun := val
  invFun := fun m => ⟨m⟩

noncomputable instance : AddCommGroup BBoson := Equiv.addCommGroup valEquiv

noncomputable instance : Module ℝ BBoson := Equiv.module ℝ valEquiv

/-- The linear identification with the underlying tensor product. -/
def valLinEquiv : BBoson ≃ₗ[ℝ] Lorentz.Vector ⊗[ℝ] selfAdjoint ℂ where
  toFun := val
  invFun := fun m => ⟨m⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp]
lemma valLinEquiv_apply (d : BBoson) : valLinEquiv d = d.val := rfl

lemma valLinEquiv_symm_apply (m : Lorentz.Vector ⊗[ℝ] selfAdjoint ℂ) :
    valLinEquiv.symm m = ⟨m⟩ := rfl

@[simp]
lemma val_add (d₁ d₂ : BBoson) : (d₁ + d₂).val = d₁.val + d₂.val := rfl

@[simp]
lemma val_smul (r : ℝ) (d : BBoson) : (r • d).val = r • d.val := rfl

@[simp]
lemma val_zero : (0 : BBoson).val = 0 := rfl

/-- The basis of the B-boson field indexed by the Lorentz index: the standard
  Lorentz-vector basis tensored with the hermitian unit of the one-dimensional
  adjoint factor. -/
noncomputable def basis : Basis (Fin 1 ⊕ Fin 3) ℝ BBoson :=
  ((Lorentz.Vector.basis.tensorProduct
      ((Module.Basis.singleton Unit ℝ).map Complex.selfAdjointEquiv.symm)).map
    valLinEquiv.symm).reindex (Equiv.prodPUnit (Fin 1 ⊕ Fin 3))

/-- The B-boson basis vector as an explicit tensor: the Lorentz basis vector paired
  with the hermitian unit. -/
lemma basis_apply (ν : Fin 1 ⊕ Fin 3) :
    (basis ν : BBoson) =
      ⟨Lorentz.Vector.basis ν ⊗ₜ[ℝ] Complex.selfAdjointEquiv.symm 1⟩ := by
  rw [basis, Module.Basis.reindex_apply, Module.Basis.map_apply,
    Module.Basis.tensorProduct_apply', Module.Basis.map_apply,
    Module.Basis.singleton_apply, valLinEquiv_symm_apply]
  rfl

/-- A pure tensor of a Lorentz basis vector with a hermitian value is a multiple of
  the corresponding B-boson basis vector. -/
lemma mk_tmul_eq_smul_basis (ν : Fin 1 ⊕ Fin 3) (x : selfAdjoint ℂ) :
    (⟨Lorentz.Vector.basis ν ⊗ₜ[ℝ] x⟩ : BBoson) =
      Complex.selfAdjointEquiv x • basis ν := by
  apply BBoson.ext
  rw [val_smul, basis_apply,
    show ((⟨Lorentz.Vector.basis ν ⊗ₜ[ℝ] Complex.selfAdjointEquiv.symm 1⟩ : BBoson)).val =
      Lorentz.Vector.basis ν ⊗ₜ[ℝ] Complex.selfAdjointEquiv.symm 1 from rfl,
    ← TensorProduct.tmul_smul]
  congr 1
  rw [show (Complex.selfAdjointEquiv x) • (Complex.selfAdjointEquiv.symm 1) =
      Complex.selfAdjointEquiv.symm (Complex.selfAdjointEquiv x • 1) from
      (map_smul _ _ _).symm, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
  rfl
/-!

## C. Lorentz action

The Lorentz group acts on the Lorentz index and leaves the adjoint factor fixed.
-/

open Matrix MatrixGroups

/-- The Lorentz representation on the B-boson field: the vector action, through the
  covering map `SL(2,ℂ) →* LorentzGroup 3`, on the Lorentz index, and the trivial
  action on the adjoint factor. -/
noncomputable def repLorentzGroup : Representation ℝ (SL(2,ℂ)) BBoson where
  toFun Λ := valLinEquiv.symm.toLinearMap ∘ₗ
    TensorProduct.map (Lorentz.Vector.rep (Lorentz.SL2C.toLorentzGroup Λ))
      (Representation.trivial ℝ (SL(2,ℂ)) (selfAdjoint ℂ) Λ) ∘ₗ
    valLinEquiv.toLinearMap
  map_one' := by
    ext F
    simp [Module.End.one_eq_id]
  map_mul' Λ₁ Λ₂ := by
    ext1 F
    simp [TensorProduct.map_map, Module.End.mul_eq_comp, map_mul]

/-!

## D. Gauge action

The B boson is neutral: the `SU(3)` and `SU(2)` components do not act on it, and
the adjoint action of the abelian `U(1)` component is `A ↦ u * A * ū = A`, which is
trivial. The global gauge group therefore acts trivially.
-/

/-- The (trivial) adjoint action of the unquotiented Standard Model gauge group on
  the B-boson field. -/
noncomputable def repGaugeGroupI : Representation ℝ GaugeGroupI BBoson :=
  Representation.trivial ℝ GaugeGroupI BBoson

@[simp]
lemma repGaugeGroupI_apply (g : GaugeGroupI) (B : BBoson) :
    repGaugeGroupI g B = B := rfl

/-!

## E. Local gauge action through jets

A local gauge transformation acts on the B-boson field through its first-order jet.
Because the adjoint action is trivial, only the inhomogeneous Maurer–Cartan term
survives: `B_μ ↦ B_μ + i (∂_μ u)(0) ū(0)`, where `u` is the `U(1)` power-series
component of the jet. The Maurer–Cartan coefficient is hermitian by unitarity, and
since the group is abelian the cocycle identity degenerates to additivity. The
resulting action of `JetGaugeGroupI` on `BBoson` is by translations.
-/

open MvPowerSeries JetRing

/-- The Maurer–Cartan coefficient of a jet of a `U(1)` gauge transformation in the
  spacetime direction `μ`: `i (∂_μ u)(0) ū(0)`, which is hermitian by unitarity. -/
noncomputable def mcCoeff (u : unitary JetRing) (μ : Fin 1 ⊕ Fin 3) : selfAdjoint ℂ :=
  ⟨Complex.I * coeff (Finsupp.single μ 1) (u : JetRing) *
      star (constantCoeff (u : JetRing)), by
    have h := congrArg (coeff (Finsupp.single μ 1)) (Unitary.mem_iff.mp u.2).2
    rw [coeff_single_one_mul, coeff_star, constantCoeff_star,
      show coeff (Finsupp.single μ 1) (1 : JetRing) = 0 by
        rw [coeff_one, if_neg (by simp [Finsupp.single_eq_zero])]] at h
    have hI : (star Complex.I) = -Complex.I := by
      simp [Complex.conj_I]
    rw [selfAdjoint.mem_iff, star_mul', star_mul', star_star, hI]
    linear_combination (-Complex.I) * h⟩

@[simp]
lemma mcCoeff_one (μ : Fin 1 ⊕ Fin 3) : mcCoeff 1 μ = 0 := by
  apply Subtype.ext
  have h : coeff (Finsupp.single μ 1) (1 : JetRing) = 0 := by
    rw [coeff_one, if_neg (by simp [Finsupp.single_eq_zero])]
  simp [mcCoeff, h]

/-- The abelian cocycle identity: the Maurer–Cartan coefficient is additive. -/
lemma mcCoeff_mul (u₁ u₂ : unitary JetRing) (μ : Fin 1 ⊕ Fin 3) :
    mcCoeff (u₁ * u₂) μ = mcCoeff u₁ μ + mcCoeff u₂ μ := by
  have h₁ : constantCoeff (u₁ : JetRing) * star (constantCoeff (u₁ : JetRing)) = 1 := by
    have h := congrArg constantCoeff (Unitary.mem_iff.mp u₁.2).2
    rwa [map_mul, constantCoeff_star, map_one] at h
  have h₂ : constantCoeff (u₂ : JetRing) * star (constantCoeff (u₂ : JetRing)) = 1 := by
    have h := congrArg constantCoeff (Unitary.mem_iff.mp u₂.2).2
    rwa [map_mul, constantCoeff_star, map_one] at h
  apply Subtype.ext
  simp only [mcCoeff, MulMemClass.coe_mul, AddSubgroup.coe_add]
  rw [coeff_single_one_mul, map_mul, star_mul]
  linear_combination (Complex.I * coeff (Finsupp.single μ 1) (u₁ : JetRing) *
      star (constantCoeff (u₁ : JetRing))) * h₂ +
    (Complex.I * coeff (Finsupp.single μ 1) (u₂ : JetRing) *
      star (constantCoeff (u₂ : JetRing))) * h₁

/-- The first-order Taylor coefficient of a hypercharge power of a `U(1)` jet is
  the charge times the Maurer–Cartan coefficient times the value of the character:
  `(∂_μ (ū^q))(0) = q · i (∂_μu)(0)ū(0) · (ū(0))^q`. The abelian connection shift
  controls the first-order transformation of every charged field. -/
lemma coeff_single_star_pow (u : unitary JetRing) (μ : Fin 1 ⊕ Fin 3) (q : ℕ) :
    coeff (Finsupp.single μ 1) ((star (u : JetRing)) ^ q) =
      (q : ℂ) * Complex.I * (mcCoeff u μ : ℂ) *
        constantCoeff ((star (u : JetRing)) ^ q) := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    rw [pow_zero, show coeff (Finsupp.single μ 1) (1 : JetRing) = 0 by
      rw [coeff_one, if_neg (by simp [Finsupp.single_eq_zero])]]
    simp
  · have h := congrArg (coeff (Finsupp.single μ 1)) (Unitary.mem_iff.mp u.2).2
    rw [coeff_single_one_mul, coeff_star, constantCoeff_star,
      show coeff (Finsupp.single μ 1) (1 : JetRing) = 0 by
        rw [coeff_one, if_neg (by simp [Finsupp.single_eq_zero])]] at h
    have hB : constantCoeff (u : JetRing) * star (constantCoeff (u : JetRing)) = 1 := by
      have h' := congrArg constantCoeff (Unitary.mem_iff.mp u.2).2
      rwa [map_mul, constantCoeff_star, map_one] at h'
    have hσA : star (coeff (Finsupp.single μ 1) (u : JetRing)) =
        -(coeff (Finsupp.single μ 1) (u : JetRing) *
          star (constantCoeff (u : JetRing)) * star (constantCoeff (u : JetRing))) := by
      linear_combination star (constantCoeff (u : JetRing)) * h -
        star (coeff (Finsupp.single μ 1) (u : JetRing)) * hB
    have hpow : star (constantCoeff (u : JetRing)) ^ (q - 1) *
        star (constantCoeff (u : JetRing)) = star (constantCoeff (u : JetRing)) ^ q := by
      rw [← pow_succ, Nat.sub_add_cancel hq]
    rw [coeff_single_one_pow, coeff_star, constantCoeff_star, map_pow, constantCoeff_star,
      hσA, show ((mcCoeff u μ : ℂ)) = Complex.I *
        coeff (Finsupp.single μ 1) (u : JetRing) *
        star (constantCoeff (u : JetRing)) from rfl,
      show (q : ℂ) * star (constantCoeff (u : JetRing)) ^ (q - 1) *
        -(coeff (Finsupp.single μ 1) (u : JetRing) *
          star (constantCoeff (u : JetRing)) * star (constantCoeff (u : JetRing))) =
        -((q : ℂ) * coeff (Finsupp.single μ 1) (u : JetRing) *
          ((star (constantCoeff (u : JetRing)) ^ (q - 1) *
            star (constantCoeff (u : JetRing))) * star (constantCoeff (u : JetRing))))
        from by ring, hpow]
    ring_nf
    rw [Complex.I_sq]
    ring

/-- The Maurer–Cartan term of a jet of a `U(1)` gauge transformation, as a B-boson:
  the translation part of the local gauge action, with components
  `i (∂_μ u)(0) ū(0)`. -/
noncomputable def mcBBoson (u : unitary JetRing) : BBoson :=
  ⟨∑ μ, Lorentz.Vector.basis μ ⊗ₜ[ℝ] mcCoeff u μ⟩

@[simp]
lemma mcBBoson_one : mcBBoson 1 = 0 := by
  apply BBoson.ext
  simp [mcBBoson]

/-- The Maurer–Cartan term is additive in the jet. -/
lemma mcBBoson_mul (u₁ u₂ : unitary JetRing) :
    mcBBoson (u₁ * u₂) = mcBBoson u₁ + mcBBoson u₂ := by
  apply BBoson.ext
  simp [mcBBoson, mcCoeff_mul, TensorProduct.tmul_add, Finset.sum_add_distrib]

/-- The action of the jet gauge group on the B-boson field: the adjoint action is
  trivial, so a jet of gauge transformations acts purely by the Maurer–Cartan
  translation `B_μ ↦ B_μ + i (∂_μ u)(0) ū(0)` of its `U(1)` component. The action
  is affine rather than linear, which is why it is a `MulAction` and not a
  `Representation`. -/
noncomputable instance : MulAction JetGaugeGroupI BBoson where
  smul U B := B + mcBBoson U.2.2
  one_smul B := by
    show B + mcBBoson (1 : JetGaugeGroupI).2.2 = B
    simp
  mul_smul U V B := by
    show B + mcBBoson (U * V).2.2 = (B + mcBBoson V.2.2) + mcBBoson U.2.2
    rw [show (U * V).2.2 = U.2.2 * V.2.2 from rfl, mcBBoson_mul]
    abel

lemma smul_def (U : JetGaugeGroupI) (B : BBoson) : U • B = B + mcBBoson U.2.2 := rfl

/-- The jets of constant (global) gauge transformations act trivially on the B
  boson, in agreement with the trivial adjoint representation `repGaugeGroupI`: the
  Maurer–Cartan term vanishes on constant jets. -/
@[simp]
lemma ofConstant_smul (g : GaugeGroupI) (B : BBoson) :
    JetGaugeGroupI.ofConstant g • B = B := by
  rw [smul_def]
  have hmc : ∀ μ, mcCoeff (JetGaugeGroupI.ofConstant g).2.2 μ = 0 := by
    intro μ
    apply Subtype.ext
    have h : coeff (Finsupp.single μ 1)
        (((JetGaugeGroupI.ofConstant g).2.2 : unitary JetRing) : JetRing) = 0 := by
      rw [show (((JetGaugeGroupI.ofConstant g).2.2 : unitary JetRing) : JetRing) =
          MvPowerSeries.C ((g.2.2 : ℂ)) from rfl,
        coeff_C, if_neg (by simp [Finsupp.single_eq_zero])]
    simp [mcCoeff, h]
  have h0 : mcBBoson (JetGaugeGroupI.ofConstant g).2.2 = 0 := by
    apply BBoson.ext
    simp [mcBBoson, hmc]
  rw [h0, add_zero]

/-!

## The Maurer–Cartan jet series

The local gauge transformation of the B-boson field is the translation
`B_μ ↦ B_μ + i (∂_μ u) ū`, so a jet of gauge transformations shifts every
derivative coordinate `∂_s B_μ` of the field by the corresponding derivative
`∂_s (i ∂_μ u ū)(0)` of the Maurer–Cartan form at the base point. The
Maurer–Cartan coefficient `mcCoeff` records only the zeroth of these shifts —
enough for the action on the field itself, but not for the action on its jets.

To express the shift of every derivative coordinate uniformly we use the `U(1)`
Maurer–Cartan form `maurerCartanU1` of the jet gauge group: the formal power
series `i (∂_ν u) ū`, whose value at the base point is `mcCoeff` and whose
higher Taylor coefficients are the higher shifts. Its coefficients are hermitian, and it is
additive in the jet; these two facts make the induced shift of the B-boson
component functions a real-valued cocycle, which is what turns the substitution
`B ↦ B + i (∂u) ū` into a representation of the jet gauge group on the jet
algebra below.

-/

/-- The derivative of a hypercharge power of a `U(1)` jet:
  `∂_ν (u^q) = -q i mc_ν u^q`, the all-orders form of the first-order Taylor
  coefficient formula for the contragredient character. -/
lemma pderiv_pow_unitary (U : JetGaugeGroupI) (ν : Fin 1 ⊕ Fin 3) (q : ℕ) :
    pderiv ℂ ν ((U.2.2 : JetRing) ^ q) =
      MvPowerSeries.C (-(q : ℂ) * Complex.I) * (maurerCartanU1 U ν * (U.2.2 : JetRing) ^ q) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · have h1 : star (U.2.2 : JetRing) * (U.2.2 : JetRing) = 1 := (Unitary.mem_iff.mp U.2.2.2).1
    have hpow : (U.2.2 : JetRing) ^ q = (U.2.2 : JetRing) * (U.2.2 : JetRing) ^ (q - 1) := by
      conv_lhs => rw [show q = 1 + (q - 1) by omega, pow_add, pow_one]
    have hC : (MvPowerSeries.C (-(q : ℂ) * Complex.I) : JetRing) *
        MvPowerSeries.C Complex.I = MvPowerSeries.C ((q : ℕ) : ℂ) := by
      rw [← map_mul]
      congr 1
      ring_nf
      rw [Complex.I_sq]
      ring
    have hN : (MvPowerSeries.C ((q : ℕ) : ℂ) : JetRing) = ((q : ℕ) : JetRing) :=
      map_natCast _ _
    rw [MvPowerSeries.pderiv_pow, maurerCartanU1, hpow]
    linear_combination
      (-((U.2.2 : JetRing) * (U.2.2 : JetRing) ^ (q - 1) * pderiv ℂ ν (U.2.2 : JetRing) *
        star (U.2.2 : JetRing))) * hC +
      (-((U.2.2 : JetRing) ^ (q - 1) * pderiv ℂ ν (U.2.2 : JetRing) *
        MvPowerSeries.C ((q : ℕ) : ℂ))) * h1 +
      (-((U.2.2 : JetRing) ^ (q - 1) * pderiv ℂ ν (U.2.2 : JetRing))) * hN

/-- The Taylor coefficients of the Maurer–Cartan series, as hermitian scalars. -/
noncomputable def maurerCartanU1Coeff (U : JetGaugeGroupI) (ν : Fin 1 ⊕ Fin 3)
    (m : (Fin 1 ⊕ Fin 3) →₀ ℕ) : selfAdjoint ℂ :=
  ⟨coeff m (maurerCartanU1 U ν), by
    rw [selfAdjoint.mem_iff, ← coeff_star, star_maurerCartanU1]⟩

@[simp]
lemma maurerCartanU1Coeff_one (ν : Fin 1 ⊕ Fin 3) (m : (Fin 1 ⊕ Fin 3) →₀ ℕ) :
    maurerCartanU1Coeff 1 ν m = 0 := by
  apply Subtype.ext
  simp [maurerCartanU1Coeff]

/-- The Taylor coefficients of the Maurer–Cartan series are additive in the jet. -/
lemma maurerCartanU1Coeff_mul (U V : JetGaugeGroupI) (ν : Fin 1 ⊕ Fin 3)
    (m : (Fin 1 ⊕ Fin 3) →₀ ℕ) :
    maurerCartanU1Coeff (U * V) ν m = maurerCartanU1Coeff U ν m + maurerCartanU1Coeff V ν m := by
  apply Subtype.ext
  simp [maurerCartanU1Coeff, maurerCartanU1_mul]

/-- The zeroth Taylor coefficient of the Maurer–Cartan series is the
  Maurer–Cartan coefficient. -/
lemma maurerCartanU1Coeff_zero (U : JetGaugeGroupI) (ν : Fin 1 ⊕ Fin 3) :
    maurerCartanU1Coeff U ν 0 = mcCoeff U.2.2 ν := by
  apply Subtype.ext
  show coeff 0 (maurerCartanU1 U ν) = _
  rw [maurerCartanU1, coeff_zero_eq_constantCoeff, map_mul, map_mul, constantCoeff_C,
    show constantCoeff (pderiv ℂ ν (U.2.2 : JetRing)) =
      coeff (Finsupp.single ν (1 : ℕ)) (U.2.2 : JetRing) from by
      rw [← coeff_zero_eq_constantCoeff, coeff_pderiv]
      simp,
    constantCoeff_star, ← mul_assoc]
  rfl

/-- The first-order Taylor coefficients of the Maurer–Cartan series are symmetric
  in the two spacetime directions: the shift of `∂_μ B_ν` equals the shift of
  `∂_ν B_μ`. This is the gauge invariance of the abelian field strength, and rests
  on unitarity: the antisymmetric part `∂_νu ∂_μū - ∂_μu ∂_νū` vanishes because
  `∂ū = -ū (∂u) ū`. -/
lemma maurerCartanU1Coeff_single_symm (U : JetGaugeGroupI) (μ ν : Fin 1 ⊕ Fin 3) :
    maurerCartanU1Coeff U ν (Finsupp.single μ 1) = maurerCartanU1Coeff U μ (Finsupp.single ν 1) := by
  rcases eq_or_ne μ ν with rfl | hμν
  · rfl
  apply Subtype.ext
  show coeff (Finsupp.single μ 1) (maurerCartanU1 U ν) = coeff (Finsupp.single ν 1) (maurerCartanU1 U μ)
  have hb : constantCoeff (U.2.2 : JetRing) * star (constantCoeff (U.2.2 : JetRing)) = 1 := by
    have h := congrArg constantCoeff (Unitary.mem_iff.mp U.2.2.2).2
    rwa [map_mul, constantCoeff_star, map_one] at h
  have hμ := congrArg (coeff (Finsupp.single μ 1)) (Unitary.mem_iff.mp U.2.2.2).2
  rw [coeff_single_one_mul, coeff_star, constantCoeff_star,
    show coeff (Finsupp.single μ 1) (1 : JetRing) = 0 by
      rw [coeff_one, if_neg (by simp [Finsupp.single_eq_zero])]] at hμ
  have hν := congrArg (coeff (Finsupp.single ν 1)) (Unitary.mem_iff.mp U.2.2.2).2
  rw [coeff_single_one_mul, coeff_star, constantCoeff_star,
    show coeff (Finsupp.single ν 1) (1 : JetRing) = 0 by
      rw [coeff_one, if_neg (by simp [Finsupp.single_eq_zero])]] at hν
  have hσμ : star (coeff (Finsupp.single μ 1) (U.2.2 : JetRing)) =
      -(coeff (Finsupp.single μ 1) (U.2.2 : JetRing) * star (constantCoeff (U.2.2 : JetRing)) *
        star (constantCoeff (U.2.2 : JetRing))) := by
    linear_combination star (constantCoeff (U.2.2 : JetRing)) * hμ -
      star (coeff (Finsupp.single μ 1) (U.2.2 : JetRing)) * hb
  have hσν : star (coeff (Finsupp.single ν 1) (U.2.2 : JetRing)) =
      -(coeff (Finsupp.single ν 1) (U.2.2 : JetRing) * star (constantCoeff (U.2.2 : JetRing)) *
        star (constantCoeff (U.2.2 : JetRing))) := by
    linear_combination star (constantCoeff (U.2.2 : JetRing)) * hν -
      star (coeff (Finsupp.single ν 1) (U.2.2 : JetRing)) * hb
  rw [maurerCartanU1, maurerCartanU1,
    show ((C Complex.I : JetRing)) = algebraMap ℂ JetRing Complex.I from rfl,
    ← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
    coeff_single_one_mul, coeff_single_one_mul, coeff_pderiv, coeff_pderiv,
    coeff_star, coeff_star, constantCoeff_star,
    show constantCoeff (pderiv ℂ ν (U.2.2 : JetRing)) =
      coeff (Finsupp.single ν (1 : ℕ)) (U.2.2 : JetRing) from by
      rw [← coeff_zero_eq_constantCoeff, coeff_pderiv]
      simp,
    show constantCoeff (pderiv ℂ μ (U.2.2 : JetRing)) =
      coeff (Finsupp.single μ (1 : ℕ)) (U.2.2 : JetRing) from by
      rw [← coeff_zero_eq_constantCoeff, coeff_pderiv]
      simp,
    show (Finsupp.single μ 1) ν = 0 from Finsupp.single_eq_of_ne hμν.symm,
    show (Finsupp.single ν 1) μ = 0 from Finsupp.single_eq_of_ne hμν,
    show Finsupp.single ν (1 : ℕ) + Finsupp.single μ 1 =
      Finsupp.single μ 1 + Finsupp.single ν 1 from add_comm _ _,
    hσμ, hσν]
  push_cast
  ring

/-- The weighted symmetry of the Maurer–Cartan Taylor coefficients: exchanging the
  field index with a derivative index changes the coefficient by the ratio of the
  corresponding multiplicities. -/
lemma maurerCartanU1Coeff_succ_symm (U : JetGaugeGroupI) (μ ν : Fin 1 ⊕ Fin 3)
    (m : (Fin 1 ⊕ Fin 3) →₀ ℕ) :
    (m μ + 1) • maurerCartanU1Coeff U ν (m + Finsupp.single μ 1) =
      (m ν + 1) • maurerCartanU1Coeff U μ (m + Finsupp.single ν 1) := by
  have h := congrArg (coeff m) (pderiv_maurerCartanU1_symm U μ ν)
  rw [coeff_pderiv, coeff_pderiv] at h
  apply Subtype.ext
  show ((m μ + 1 : ℕ)) • coeff (m + Finsupp.single μ 1) (maurerCartanU1 U ν) =
    ((m ν + 1 : ℕ)) • coeff (m + Finsupp.single ν 1) (maurerCartanU1 U μ)
  rw [nsmul_eq_mul, nsmul_eq_mul]
  push_cast
  linear_combination h

/-!

## The Jet component vector space

-/

open Module
inductive JetGenerators where
  | dB (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3): JetGenerators
deriving DecidableEq

def JetGenerators.equiv : JetGenerators ≃ Multiset (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) where
  toFun
    | JetGenerators.dB s μ => (s, μ)
  invFun
    | (s, μ) => JetGenerators.dB s μ
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    cases x
    rfl

abbrev JetComponentSpace :=
  SymmetricAlgebra ℝ (Module.Dual ℝ Lorentz.CoVector) ⊗[ℝ] Module.Dual ℝ BBoson

/-- The basis of the B-boson jet component space indexed by the jet generators
  `∂_s B_μ`: the multiset basis of the dual derivative symbols tensored with the
  dual of the B-boson basis. -/
noncomputable def JetComponentSpace.basis : Basis JetGenerators ℝ JetComponentSpace :=
  (LagrangianTheory.dualRealJetAlgebraBasis.tensorProduct
    BBoson.basis.dualBasis).reindex JetGenerators.equiv.symm
/-!

## The Maurer–Cartan shift of the component functions

-/

open LagrangianTheory

/-- The Maurer–Cartan jet of a `U(1)` jet evaluated on the derivative symbols:
  the basis monomial of dual derivative symbols at the multi-index `m` is sent to
  the B-boson-valued `m`-th derivative of the Maurer–Cartan series at the base
  point. This is the amount by which the corresponding derivative coordinate of
  the B boson is shifted under the jet gauge transformation. -/
noncomputable def mcJet (U : JetGaugeGroupI) :
    SymmetricAlgebra ℝ (Module.Dual ℝ Lorentz.CoVector) →ₗ[ℝ] BBoson :=
  Lorentz.CoVector.basis.dualBasis.symmetricAlgebra.constr ℝ fun m =>
    ⟨∑ ν, Lorentz.Vector.basis ν ⊗ₜ[ℝ]
      ((∏ μ, Nat.factorial (m μ)) • maurerCartanU1Coeff U ν m)⟩

@[simp]
lemma mcJet_one : mcJet 1 = 0 := by
  refine Lorentz.CoVector.basis.dualBasis.symmetricAlgebra.ext fun m => ?_
  rw [mcJet, Module.Basis.constr_basis]
  apply BBoson.ext
  simp

/-- The Maurer–Cartan jet is additive in the jet: the abelian cocycle identity
  for the shift of the component functions. -/
lemma mcJet_mul (U V : JetGaugeGroupI) : mcJet (U * V) = mcJet U + mcJet V := by
  refine Lorentz.CoVector.basis.dualBasis.symmetricAlgebra.ext fun m => ?_
  rw [LinearMap.add_apply, mcJet, mcJet, mcJet, Module.Basis.constr_basis,
    Module.Basis.constr_basis, Module.Basis.constr_basis]
  apply BBoson.ext
  simp [maurerCartanU1Coeff_mul, smul_add, TensorProduct.tmul_add, Finset.sum_add_distrib]

/-- The Maurer–Cartan pairing: the amount by which a component function of the
  B-boson jet is shifted under a jet gauge transformation, i.e. the evaluation of
  the component function against the Maurer–Cartan jet. -/
noncomputable def mcPairing (U : JetGaugeGroupI) : JetComponentSpace →ₗ[ℝ] ℝ :=
  TensorProduct.lift ((Module.Dual.eval ℝ BBoson).comp (mcJet U))

@[simp]
lemma mcPairing_tmul (U : JetGaugeGroupI)
    (p : SymmetricAlgebra ℝ (Module.Dual ℝ Lorentz.CoVector))
    (φ : Module.Dual ℝ BBoson) :
    mcPairing U (p ⊗ₜ[ℝ] φ) = φ (mcJet U p) := rfl

@[simp]
lemma mcPairing_one : mcPairing 1 = 0 := by
  refine TensorProduct.ext' fun p φ => ?_
  simp

/-- The Maurer–Cartan pairing is additive in the jet. -/
lemma mcPairing_mul (U V : JetGaugeGroupI) :
    mcPairing (U * V) = mcPairing U + mcPairing V := by
  refine TensorProduct.ext' fun p φ => ?_
  simp [mcJet_mul]

/-- The multiset basis of the dual derivative symbols at a singleton, as a basis
  vector of the symmetric algebra at a single multi-index. -/
lemma dualRealJetAlgebraBasis_singleton (μ : Fin 1 ⊕ Fin 3) :
    LagrangianTheory.dualRealJetAlgebraBasis ({μ} : Multiset (Fin 1 ⊕ Fin 3)) =
      Lorentz.CoVector.basis.dualBasis.symmetricAlgebra (Finsupp.single μ 1) := by
  rw [LagrangianTheory.dualRealJetAlgebraBasis, Module.Basis.reindex_apply, Equiv.symm_symm]
  congr 1
  exact Multiset.toFinsupp_singleton μ

/-- The Maurer–Cartan jet on a first-order derivative symbol: the B boson whose
  `ν`-th component is the first-order Taylor coefficient of the Maurer–Cartan
  series. -/
lemma mcJet_singleton (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3) :
    mcJet U (LagrangianTheory.dualRealJetAlgebraBasis ({μ} : Multiset (Fin 1 ⊕ Fin 3))) =
      ⟨∑ ν, Lorentz.Vector.basis ν ⊗ₜ[ℝ]
        (maurerCartanU1Coeff U ν (Finsupp.single μ 1) : selfAdjoint ℂ)⟩ := by
  rw [dualRealJetAlgebraBasis_singleton, mcJet, Module.Basis.constr_basis]
  apply BBoson.ext
  show (∑ ν, Lorentz.Vector.basis ν ⊗ₜ[ℝ]
      ((∏ ρ, Nat.factorial ((Finsupp.single μ 1) ρ)) •
        maurerCartanU1Coeff U ν (Finsupp.single μ 1))) = _
  rw [show (∏ ρ, Nat.factorial ((Finsupp.single μ 1) ρ)) = 1 from
    Finset.prod_eq_one fun ρ _ => by
      rcases eq_or_ne μ ρ with rfl | h
      · simp
      · rw [Finsupp.single_eq_of_ne h.symm]
        rfl]
  simp

/-- The jet component basis vector at a generator, as a pure tensor. -/
lemma jetComponentSpace_basis_dB (s : Multiset (Fin 1 ⊕ Fin 3)) (ρ : Fin 1 ⊕ Fin 3) :
    JetComponentSpace.basis (.dB s ρ) =
      LagrangianTheory.dualRealJetAlgebraBasis s ⊗ₜ[ℝ] BBoson.basis.dualBasis ρ := by
  rw [JetComponentSpace.basis, Module.Basis.reindex_apply, Equiv.symm_symm]
  exact Module.Basis.tensorProduct_apply' _ _ _

/-- The Maurer–Cartan pairing on first-order generators: the shift of the component
  function `∂_μ B_ν` is the first-order Taylor coefficient of the Maurer–Cartan
  series. -/
lemma mcPairing_basis_dB (U : JetGaugeGroupI) (μ ν : Fin 1 ⊕ Fin 3) :
    mcPairing U (JetComponentSpace.basis (.dB {μ} ν)) =
      Complex.selfAdjointEquiv (maurerCartanU1Coeff U ν (Finsupp.single μ 1)) := by
  rw [jetComponentSpace_basis_dB, mcPairing_tmul, mcJet_singleton,
    show (⟨∑ ν', Lorentz.Vector.basis ν' ⊗ₜ[ℝ]
        (maurerCartanU1Coeff U ν' (Finsupp.single μ 1) : selfAdjoint ℂ)⟩ : BBoson) =
      ∑ ν', Complex.selfAdjointEquiv (maurerCartanU1Coeff U ν' (Finsupp.single μ 1)) •
        basis ν' from by
      rw [show (⟨∑ ν', Lorentz.Vector.basis ν' ⊗ₜ[ℝ]
          (maurerCartanU1Coeff U ν' (Finsupp.single μ 1) : selfAdjoint ℂ)⟩ : BBoson) =
        valLinEquiv.symm (∑ ν', Lorentz.Vector.basis ν' ⊗ₜ[ℝ]
          (maurerCartanU1Coeff U ν' (Finsupp.single μ 1) : selfAdjoint ℂ)) from rfl, map_sum]
      exact Finset.sum_congr rfl fun ν' _ => by
        rw [valLinEquiv_symm_apply, mk_tmul_eq_smul_basis],
    map_sum]
  simp only [map_smul, Module.Basis.dualBasis_apply_self, smul_eq_mul, mul_ite,
    mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ ν]
  simp

/-- The multiset basis of the dual derivative symbols, as a basis vector of the
  symmetric algebra at the corresponding multi-index. -/
lemma dualRealJetAlgebraBasis_apply' (s : Multiset (Fin 1 ⊕ Fin 3)) :
    LagrangianTheory.dualRealJetAlgebraBasis s =
      Lorentz.CoVector.basis.dualBasis.symmetricAlgebra (Multiset.toFinsupp s) := by
  rw [LagrangianTheory.dualRealJetAlgebraBasis, Module.Basis.reindex_apply, Equiv.symm_symm]
  rfl

/-- The Maurer–Cartan jet on a general derivative symbol. -/
lemma mcJet_basis (U : JetGaugeGroupI) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    mcJet U (LagrangianTheory.dualRealJetAlgebraBasis s) =
      ⟨∑ ν, Lorentz.Vector.basis ν ⊗ₜ[ℝ]
        ((∏ ρ, Nat.factorial ((Multiset.toFinsupp s) ρ)) •
          maurerCartanU1Coeff U ν (Multiset.toFinsupp s))⟩ := by
  rw [dualRealJetAlgebraBasis_apply', mcJet, Module.Basis.constr_basis]

/-- The Maurer–Cartan pairing on a general generator: the factorial-weighted
  Taylor coefficient of the Maurer–Cartan series. -/
lemma mcPairing_basis_dB' (U : JetGaugeGroupI) (s : Multiset (Fin 1 ⊕ Fin 3))
    (ν : Fin 1 ⊕ Fin 3) :
    mcPairing U (JetComponentSpace.basis (.dB s ν)) =
      (∏ ρ, Nat.factorial ((Multiset.toFinsupp s) ρ)) •
        Complex.selfAdjointEquiv (maurerCartanU1Coeff U ν (Multiset.toFinsupp s)) := by
  rw [jetComponentSpace_basis_dB, mcPairing_tmul, mcJet_basis,
    show (⟨∑ ν', Lorentz.Vector.basis ν' ⊗ₜ[ℝ]
        ((∏ ρ, Nat.factorial ((Multiset.toFinsupp s) ρ)) •
          maurerCartanU1Coeff U ν' (Multiset.toFinsupp s))⟩ : BBoson) =
      ∑ ν', ((∏ ρ, Nat.factorial ((Multiset.toFinsupp s) ρ)) •
        Complex.selfAdjointEquiv (maurerCartanU1Coeff U ν' (Multiset.toFinsupp s))) • basis ν' from by
      rw [show (⟨∑ ν', Lorentz.Vector.basis ν' ⊗ₜ[ℝ]
          ((∏ ρ, Nat.factorial ((Multiset.toFinsupp s) ρ)) •
            maurerCartanU1Coeff U ν' (Multiset.toFinsupp s))⟩ : BBoson) =
        valLinEquiv.symm (∑ ν', Lorentz.Vector.basis ν' ⊗ₜ[ℝ]
          ((∏ ρ, Nat.factorial ((Multiset.toFinsupp s) ρ)) •
            maurerCartanU1Coeff U ν' (Multiset.toFinsupp s))) from rfl, map_sum]
      refine Finset.sum_congr rfl fun ν' _ => ?_
      rw [valLinEquiv_symm_apply, mk_tmul_eq_smul_basis, map_nsmul],
    map_sum]
  simp only [map_smul, Module.Basis.dualBasis_apply_self, smul_eq_mul, mul_ite,
    mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ ν]
  simp

/-- The factorial weight of a multi-index augmented by one derivative: the
  multiplicity of the new index times the original weight. -/
lemma prod_factorial_add_single (m : (Fin 1 ⊕ Fin 3) →₀ ℕ) (κ : Fin 1 ⊕ Fin 3) :
    (∏ ρ : Fin 1 ⊕ Fin 3, Nat.factorial (((m + Finsupp.single κ 1) : (Fin 1 ⊕ Fin 3) →₀ ℕ) ρ)) =
      (m κ + 1) * ∏ ρ, Nat.factorial (m ρ) := by
  rw [show (∏ ρ : Fin 1 ⊕ Fin 3, Nat.factorial (((m + Finsupp.single κ 1) : (Fin 1 ⊕ Fin 3) →₀ ℕ) ρ)) =
      ∏ ρ, ((if ρ = κ then m κ + 1 else 1) * Nat.factorial (m ρ)) from
    Finset.prod_congr rfl fun ρ _ => by
      rcases eq_or_ne ρ κ with rfl | h
      · rw [Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ, if_pos rfl]
      · rw [Finsupp.add_apply, Finsupp.single_eq_of_ne h, add_zero, if_neg h, one_mul],
    Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ κ]
  simp

/-- Exchanging the field index with a derivative index leaves the Maurer–Cartan
  shift of the component functions unchanged: the shift is the jet of a gradient,
  whose Taylor coefficients depend only on the total multi-index. -/
lemma mcPairing_basis_dB_symm (U : JetGaugeGroupI) (s : Multiset (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) :
    mcPairing U (JetComponentSpace.basis (.dB (s + {μ}) ν)) =
      mcPairing U (JetComponentSpace.basis (.dB (s + {ν}) μ)) := by
  rw [mcPairing_basis_dB', mcPairing_basis_dB',
    show Multiset.toFinsupp (s + {μ}) = Multiset.toFinsupp s + Finsupp.single μ 1 from by
      rw [map_add, Multiset.toFinsupp_singleton],
    show Multiset.toFinsupp (s + {ν}) = Multiset.toFinsupp s + Finsupp.single ν 1 from by
      rw [map_add, Multiset.toFinsupp_singleton],
    prod_factorial_add_single, prod_factorial_add_single, mul_smul, mul_smul,
    smul_comm (Multiset.toFinsupp s μ + 1), smul_comm (Multiset.toFinsupp s ν + 1)]
  congr 1
  have h := congrArg Complex.selfAdjointEquiv
    (maurerCartanU1Coeff_succ_symm U μ ν (Multiset.toFinsupp s))
  rw [map_nsmul, map_nsmul] at h
  exact h

/-!

## Iterated derivatives of the Maurer–Cartan series

The covariance of the covariant derivatives of charged fields rests on the
higher Maurer–Cartan anomalies: the iterated formal derivatives of the
Maurer–Cartan series. Their constant coefficients are the Maurer–Cartan
pairings of the corresponding B-boson component functions.

-/

/-- The iterated formal derivatives of the Maurer–Cartan series along an ordered
  list of directions: `mc_{s,μ} = ∂_s mc_μ`. -/
noncomputable def maurerCartanU1Deriv (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3) :
    List (Fin 1 ⊕ Fin 3) → JetRing
  | [] => maurerCartanU1 U μ
  | ν :: s => pderiv ℂ ν (maurerCartanU1Deriv U μ s)

@[simp]
lemma maurerCartanU1Deriv_nil (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3) :
    maurerCartanU1Deriv U μ [] = maurerCartanU1 U μ := rfl

@[simp]
lemma maurerCartanU1Deriv_cons (U : JetGaugeGroupI) (μ ν : Fin 1 ⊕ Fin 3)
    (s : List (Fin 1 ⊕ Fin 3)) :
    maurerCartanU1Deriv U μ (ν :: s) = pderiv ℂ ν (maurerCartanU1Deriv U μ s) := rfl

/-- The factorial-weighted Taylor coefficients of the iterated derivatives of the
  Maurer–Cartan series: differentiating shifts the multi-index inside the
  factorial weight. -/
lemma factorial_coeff_maurerCartanU1Deriv (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3)
    (s : List (Fin 1 ⊕ Fin 3)) (m : (Fin 1 ⊕ Fin 3) →₀ ℕ) :
    ((∏ ρ, Nat.factorial (m ρ) : ℕ) : ℂ) * coeff m (maurerCartanU1Deriv U μ s) =
      ((∏ ρ, Nat.factorial (((m + Multiset.toFinsupp ↑s) :
          (Fin 1 ⊕ Fin 3) →₀ ℕ) ρ) : ℕ) : ℂ) *
        coeff (m + Multiset.toFinsupp ↑s) (maurerCartanU1 U μ) := by
  induction s generalizing m with
  | nil => simp
  | cons ν s ih =>
    rw [maurerCartanU1Deriv_cons, coeff_pderiv]
    have hT : Multiset.toFinsupp (↑(ν :: s) : Multiset (Fin 1 ⊕ Fin 3)) =
        Finsupp.single ν 1 + Multiset.toFinsupp (↑s : Multiset (Fin 1 ⊕ Fin 3)) := by
      rw [show (↑(ν :: s) : Multiset (Fin 1 ⊕ Fin 3)) = {ν} + ↑s from by
          rw [Multiset.singleton_add, Multiset.cons_coe],
        map_add, Multiset.toFinsupp_singleton]
    have hcast : ((∏ ρ, Nat.factorial (((m + Finsupp.single ν 1) :
          (Fin 1 ⊕ Fin 3) →₀ ℕ) ρ) : ℕ) : ℂ) =
        ((m ν + 1 : ℕ) : ℂ) * ((∏ ρ, Nat.factorial (m ρ) : ℕ) : ℂ) := by
      rw [← Nat.cast_mul, prod_factorial_add_single]
    rw [hT, show m + (Finsupp.single ν 1 + Multiset.toFinsupp (↑s : Multiset _)) =
        m + Finsupp.single ν 1 + Multiset.toFinsupp (↑s : Multiset _) from
        (add_assoc _ _ _).symm, ← ih (m + Finsupp.single ν 1), hcast]
    push_cast
    ring

/-- The constant coefficient of the iterated derivative of the Maurer–Cartan
  series is the Maurer–Cartan pairing of the corresponding B-boson component
  function. -/
lemma constantCoeff_maurerCartanU1Deriv (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3)
    (s : List (Fin 1 ⊕ Fin 3)) :
    MvPowerSeries.constantCoeff (maurerCartanU1Deriv U μ s) =
      ((mcPairing U (JetComponentSpace.basis (JetGenerators.dB ↑s μ)) : ℝ) : ℂ) := by
  have h := factorial_coeff_maurerCartanU1Deriv U μ s 0
  simp only [Finsupp.coe_zero, Pi.zero_apply, Nat.factorial_zero, Finset.prod_const_one,
    Nat.cast_one, one_mul, zero_add] at h
  rw [← coeff_zero_eq_constantCoeff_apply, h, mcPairing_basis_dB', nsmul_eq_mul]
  push_cast
  rw [Complex.coe_selfAdjointEquiv]
  rfl


/-!

## Canonical representatives of the jet generators

The Maurer–Cartan pairing of a jet gauge transformation with the component
function `∂_s B_ν` depends only on the total symmetrized multi-index `s + {ν}`.
We choose, for every jet generator, a canonical generator with the same total
multi-index. The differences between a generator and its canonical
representative are exactly the derivatives of the field strength, while the
canonical generators themselves are shifted freely by the gauge transformations
realized above; this dichotomy computes the gauge invariants of the jet algebra
below.

-/

namespace JetGenerators

/-- The total symmetrized multi-index of a jet generator: the derivative
  multi-index together with the Lorentz index of the field. The Maurer–Cartan
  shift of a component function depends only on its total multi-index. -/
def total : JetGenerators → Multiset (Fin 1 ⊕ Fin 3)
  | .dB s ν => s + {ν}

@[simp]
lemma total_dB (s : Multiset (Fin 1 ⊕ Fin 3)) (ν : Fin 1 ⊕ Fin 3) :
    total (dB s ν) = s + {ν} := rfl

lemma total_ne_zero (g : JetGenerators) : total g ≠ 0 := by
  cases g with
  | dB s ν => simp [total]

/-- A choice of element of a multiset, used to pick the canonical representative
  of each total multi-index. -/
noncomputable def pick (t : Multiset (Fin 1 ⊕ Fin 3)) : Fin 1 ⊕ Fin 3 :=
  if h : ∃ ν, ν ∈ t then h.choose else Sum.inl 0

lemma pick_mem {t : Multiset (Fin 1 ⊕ Fin 3)} (ht : t ≠ 0) : pick t ∈ t := by
  have h : ∃ ν, ν ∈ t := Multiset.exists_mem_of_ne_zero ht
  rw [pick, dif_pos h]
  exact h.choose_spec

/-- The canonical representative of a jet generator: the generator with the same
  total multi-index whose field index is the chosen element of the total. -/
noncomputable def canon (g : JetGenerators) : JetGenerators :=
  .dB ((total g).erase (pick (total g))) (pick (total g))

/-- The canonical representative has the same total multi-index. -/
@[simp]
lemma total_canon (g : JetGenerators) : total (canon g) = total g := by
  rw [canon]
  show ((total g).erase (pick (total g))) + {pick (total g)} = total g
  rw [add_comm, Multiset.singleton_add]
  exact Multiset.cons_erase (pick_mem (total_ne_zero g))

/-- Taking canonical representatives is idempotent. -/
@[simp]
lemma canon_canon (g : JetGenerators) : canon (canon g) = canon g := by
  rw [show canon (canon g) =
    JetGenerators.dB ((total (canon g)).erase (pick (total (canon g))))
      (pick (total (canon g))) from rfl, total_canon]
  rfl

/-- Two jet generators have the same canonical representative if and only if they
  have the same total multi-index. -/
lemma canon_eq_canon_iff (g g' : JetGenerators) :
    canon g = canon g' ↔ total g = total g' := by
  constructor
  · intro h
    rw [← total_canon g, ← total_canon g', h]
  · intro h
    rw [canon, canon, h]

/-- The jet generator with one further derivative in the direction `μ`. -/
def shift (μ : Fin 1 ⊕ Fin 3) : JetGenerators → JetGenerators
  | dB s ν => dB (s + {μ}) ν

@[simp]
lemma shift_dB (μ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) (ν : Fin 1 ⊕ Fin 3) :
    shift μ (dB s ν) = dB (s + {μ}) ν := rfl

/-- The jet generator with further derivatives appended from a multiset. -/
def shiftMulti (t : Multiset (Fin 1 ⊕ Fin 3)) : JetGenerators → JetGenerators
  | dB s ν => dB (s + t) ν

@[simp]
lemma shiftMulti_dB (t s : Multiset (Fin 1 ⊕ Fin 3)) (ν : Fin 1 ⊕ Fin 3) :
    shiftMulti t (dB s ν) = dB (s + t) ν := rfl

lemma shiftMulti_singleton (ν : Fin 1 ⊕ Fin 3) (g : JetGenerators) :
    shiftMulti {ν} g = shift ν g := by
  cases g with
  | dB s ρ => rfl

lemma shiftMulti_shift (t : Multiset (Fin 1 ⊕ Fin 3)) (ν : Fin 1 ⊕ Fin 3)
    (g : JetGenerators) :
    shiftMulti t (shift ν g) = shiftMulti (t + {ν}) g := by
  cases g with
  | dB s ρ =>
    simp only [shift_dB, shiftMulti_dB]
    congr 1
    rw [add_comm t ({ν} : Multiset (Fin 1 ⊕ Fin 3)), ← add_assoc]

end JetGenerators

/-!

## The jet algebra and the jet gauge action

-/

/-- The jet algebra of the B boson: the commutative algebra generated by the
  component functions of the B-boson field and its derivative coordinates. -/
abbrev JetAlgebra : Type := SymmetricAlgebra ℝ JetComponentSpace

namespace JetAlgebra


/-!

## Constructing elements of the jet algebra from the generators

-/

noncomputable def ofGenerator (x : JetGenerators) : BBoson.JetAlgebra :=
   SymmetricAlgebra.ι ℝ JetComponentSpace (BBoson.JetComponentSpace.basis x)

/-!

## A. Representation of the jet Gauge group

-/


/-!

## A.1 The real version

-/

/-- The action of the jet gauge group on the jet algebra of the B boson. The
  adjoint action is trivial and the local gauge action is the Maurer–Cartan
  translation, whose linear part is the identity; consequently no information is
  carried by a linear action on the component space itself, and the action lives
  on the unital algebra: a jet of gauge transformations acts as the substitution
  automorphism sending each generator `x` to `x + ⟨mc, x⟩ 1`, the pullback of the
  translation `B ↦ B + i (∂u) ū` on polynomial functions of the jet
  coordinates. On jets of constant gauge transformations the shift vanishes and
  the action is trivial, in agreement with `repGaugeGroupI`. -/
noncomputable def repJetGaugeGroupI : Representation ℝ JetGaugeGroupI JetAlgebra where
  toFun U := (SymmetricAlgebra.lift
    ((SymmetricAlgebra.ι ℝ JetComponentSpace) +
      (Algebra.linearMap ℝ JetAlgebra) ∘ₗ mcPairing U)).toLinearMap
  map_one' := by
    rw [show mcPairing (1 : JetGaugeGroupI) = 0 from mcPairing_one]
    suffices hs : SymmetricAlgebra.lift ((SymmetricAlgebra.ι ℝ JetComponentSpace) +
        (Algebra.linearMap ℝ JetAlgebra) ∘ₗ (0 : JetComponentSpace →ₗ[ℝ] ℝ)) =
        AlgHom.id ℝ JetAlgebra by
      rw [hs]
      rfl
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
    simp
  map_mul' U V := by
    rw [show mcPairing (U * V : JetGaugeGroupI) =
        mcPairing U + mcPairing V from mcPairing_mul U V]
    suffices hs : SymmetricAlgebra.lift ((SymmetricAlgebra.ι ℝ JetComponentSpace) +
        (Algebra.linearMap ℝ JetAlgebra) ∘ₗ (mcPairing U + mcPairing V)) =
        (SymmetricAlgebra.lift ((SymmetricAlgebra.ι ℝ JetComponentSpace) +
          (Algebra.linearMap ℝ JetAlgebra) ∘ₗ mcPairing U)).comp
        (SymmetricAlgebra.lift ((SymmetricAlgebra.ι ℝ JetComponentSpace) +
          (Algebra.linearMap ℝ JetAlgebra) ∘ₗ mcPairing V)) by
      rw [hs, AlgHom.comp_toLinearMap, Module.End.mul_eq_comp]
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
    simp [add_assoc]

/-- The jet gauge action on a generator of the jet algebra: the Maurer–Cartan
  shift by the pairing of the component function with the Maurer–Cartan jet. -/
@[simp]
lemma repJetGaugeGroupI_ι (U : JetGaugeGroupI) (x : JetComponentSpace) :
    repJetGaugeGroupI U (SymmetricAlgebra.ι ℝ JetComponentSpace x) =
      SymmetricAlgebra.ι ℝ JetComponentSpace x +
        algebraMap ℝ JetAlgebra (mcPairing U x) := by
  simp [repJetGaugeGroupI, SymmetricAlgebra.lift_ι_apply, AlgHom.toLinearMap_apply,
    Algebra.linearMap_apply]


lemma repJetGaugeGroupI_mul (U : JetGaugeGroupI) (x y : JetAlgebra) :
    repJetGaugeGroupI U (x * y) = repJetGaugeGroupI U x * repJetGaugeGroupI U y :=
  map_mul (SymmetricAlgebra.lift ((SymmetricAlgebra.ι ℝ JetComponentSpace) +
    (Algebra.linearMap ℝ JetAlgebra) ∘ₗ mcPairing U)) x y

lemma repJetGaugeGroupI_algebraMap (U : JetGaugeGroupI) (r : ℝ) :
    repJetGaugeGroupI U (algebraMap ℝ JetAlgebra r) = algebraMap ℝ JetAlgebra r :=
  AlgHom.commutes (SymmetricAlgebra.lift ((SymmetricAlgebra.ι ℝ JetComponentSpace) +
    (Algebra.linearMap ℝ JetAlgebra) ∘ₗ mcPairing U)) r

lemma repJetGaugeGroupI_one (U : JetGaugeGroupI) :
    repJetGaugeGroupI U (1 : JetAlgebra) = 1 := by
  have h := repJetGaugeGroupI_algebraMap U 1
  simpa using h


/-- Conjugating the jet gauge action by the polynomial coordinates of the jet
  algebra: under `SymmetricAlgebra.equivMvPolynomial` the substitution
  automorphism `x ↦ x + ⟨mc, x⟩ 1` becomes the translation of every polynomial
  variable by the Maurer–Cartan pairing of the corresponding component
  function. -/
lemma equivMvPolynomial_repJetGaugeGroupI (U : JetGaugeGroupI) (V : JetAlgebra) :
    SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis (repJetGaugeGroupI U V) =
      MvPolynomial.aeval (fun g => MvPolynomial.X g +
          MvPolynomial.C (mcPairing U (JetComponentSpace.basis g)))
        (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis V) := by
  have h : (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis).toAlgHom.comp
      (SymmetricAlgebra.lift ((SymmetricAlgebra.ι ℝ JetComponentSpace) +
        (Algebra.linearMap ℝ JetAlgebra) ∘ₗ mcPairing U)) =
      (MvPolynomial.aeval (fun g => MvPolynomial.X g +
          MvPolynomial.C (mcPairing U (JetComponentSpace.basis g)))).comp
        (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis).toAlgHom := by
    refine SymmetricAlgebra.algHom_ext (JetComponentSpace.basis.ext fun g => ?_)
    show (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis)
        (SymmetricAlgebra.lift ((SymmetricAlgebra.ι ℝ JetComponentSpace) +
          (Algebra.linearMap ℝ JetAlgebra) ∘ₗ mcPairing U)
          (SymmetricAlgebra.ι ℝ JetComponentSpace (JetComponentSpace.basis g))) =
      MvPolynomial.aeval (fun g => MvPolynomial.X g +
          MvPolynomial.C (mcPairing U (JetComponentSpace.basis g)))
        ((SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis)
          (SymmetricAlgebra.ι ℝ JetComponentSpace (JetComponentSpace.basis g)))
    rw [SymmetricAlgebra.lift_ι_apply]
    simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
      Algebra.linearMap_apply, map_add, AlgEquiv.commutes,
      SymmetricAlgebra.equivMvPolynomial_ι_apply, MvPolynomial.aeval_X,
      MvPolynomial.algebraMap_eq]
  exact DFunLike.congr_fun h V

/-- The conjugated action of a `U(1)` jet embedded in the jet gauge group. -/
lemma equivMvPolynomial_repJetGaugeGroupI_u1 (u : unitary JetRing) (V : JetAlgebra) :
    SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis
      (repJetGaugeGroupI (1, 1, u) V) =
      MvPolynomial.aeval (fun g => MvPolynomial.X g +
          MvPolynomial.C (mcPairing (1, 1, u) (JetComponentSpace.basis g)))
        (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis V) :=
  equivMvPolynomial_repJetGaugeGroupI (1, 1, u) V


/-!

## A.2 The complexified version

-/


/-- The action of the jet gauge group on the complexified B-boson jet algebra,
  obtained from the real representation by extension of scalars. -/
noncomputable def complexRepJetGaugeGroupI :
    Representation ℂ JetGaugeGroupI (ℂ ⊗[ℝ] BBoson.JetAlgebra) where
  toFun U := LinearMap.baseChange ℂ (BBoson.JetAlgebra.repJetGaugeGroupI U)
  map_one' := by
    ext x
    simp [Module.End.one_eq_id]
  map_mul' U V := by
    ext x
    simp [map_mul, Module.End.mul_eq_comp, LinearMap.baseChange_comp]

lemma complexRepJetGaugeGroupI_tmul (U : JetGaugeGroupI) (c : ℂ) (b : JetAlgebra) :
    complexRepJetGaugeGroupI U (c ⊗ₜ[ℝ] b) = c ⊗ₜ[ℝ] repJetGaugeGroupI U b := rfl

/-- The complexified gauge action is multiplicative. -/
lemma complexRepJetGaugeGroupI_mul (U : JetGaugeGroupI) (x y : ℂ ⊗[ℝ] JetAlgebra) :
    complexRepJetGaugeGroupI U (x * y) =
      complexRepJetGaugeGroupI U x * complexRepJetGaugeGroupI U y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    simp only [add_mul, map_add, ha, hb]
  | tmul c b =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a' b' ha' hb' =>
      simp only [mul_add, map_add, ha', hb']
    | tmul c' b' =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, complexRepJetGaugeGroupI_tmul,
        repJetGaugeGroupI_mul]

/-- The complexified gauge action on a jet-algebra generator: the Maurer–Cartan
  shift of the component function. -/
lemma complexRepJetGaugeGroupI_ofGenerator (U : JetGaugeGroupI) (g : JetGenerators) :
    complexRepJetGaugeGroupI U ((1 : ℂ) ⊗ₜ[ℝ] ofGenerator g) =
      (1 : ℂ) ⊗ₜ[ℝ] ofGenerator g +
        ((mcPairing U (JetComponentSpace.basis g) : ℝ) : ℂ) •
          ((1 : ℂ) ⊗ₜ[ℝ] (1 : JetAlgebra)) := by
  rw [complexRepJetGaugeGroupI_tmul, ofGenerator, repJetGaugeGroupI_ι,
    TensorProduct.tmul_add, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
    show ((mcPairing U (JetComponentSpace.basis g) : ℝ) : ℂ) =
      algebraMap ℝ ℂ (mcPairing U (JetComponentSpace.basis g)) from rfl,
    algebraMap_smul]

/-!

## The formal total derivative on the jet algebra

The formal total spacetime derivative `∂_μ` acts on the component functions of
the B-boson jet by appending the derivative index, `∂_s B_ν ↦ ∂_{s + {μ}} B_ν`,
and extends to the jet algebra as a derivation. It is constructed through the
polynomial coordinates of the jet algebra.

-/

/-- The formal total spacetime derivative on the B-boson jet algebra in the
  direction `μ`: the derivation sending each component function `∂_s B_ν` to
  `∂_{s + {μ}} B_ν`. -/
noncomputable def jetDeriv (μ : Fin 1 ⊕ Fin 3) : JetAlgebra →ₗ[ℝ] JetAlgebra :=
  (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis).symm.toLinearMap ∘ₗ
    (MvPolynomial.mkDerivation ℝ fun g : JetGenerators =>
      (MvPolynomial.X (JetGenerators.shift μ g) :
        MvPolynomial JetGenerators ℝ)).toLinearMap ∘ₗ
    (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis).toLinearMap

/-- The total derivative appends the derivative index to each component
  function. -/
@[simp]
lemma jetDeriv_ofGenerator (μ : Fin 1 ⊕ Fin 3) (g : JetGenerators) :
    jetDeriv μ (ofGenerator g) = ofGenerator (JetGenerators.shift μ g) := by
  simp only [jetDeriv, ofGenerator, LinearMap.coe_comp, Function.comp_apply,
    AlgEquiv.toLinearMap_apply, Derivation.coeFn_coe]
  rw [SymmetricAlgebra.equivMvPolynomial_ι_apply, MvPolynomial.mkDerivation_X,
    SymmetricAlgebra.equivMvPolynomial_symm_X]

@[simp]
lemma jetDeriv_one (μ : Fin 1 ⊕ Fin 3) : jetDeriv μ (1 : JetAlgebra) = 0 := by
  simp [jetDeriv]

/-- The total derivative is a derivation: the Leibniz rule on the jet algebra. -/
lemma jetDeriv_mul (μ : Fin 1 ⊕ Fin 3) (x y : JetAlgebra) :
    jetDeriv μ (x * y) = jetDeriv μ x * y + x * jetDeriv μ y := by
  simp only [jetDeriv, LinearMap.coe_comp, Function.comp_apply,
    AlgEquiv.toLinearMap_apply, map_mul, Derivation.coeFn_coe, Derivation.leibniz,
    smul_eq_mul, map_add, AlgEquiv.symm_apply_apply]
  ring

/-- The Leibniz rule for the complexified total derivative on the complexified
  jet algebra. -/
lemma jetDeriv_baseChange_mul (μ : Fin 1 ⊕ Fin 3) (x y : ℂ ⊗[ℝ] JetAlgebra) :
    LinearMap.baseChange ℂ (jetDeriv μ) (x * y) =
      LinearMap.baseChange ℂ (jetDeriv μ) x * y +
        x * LinearMap.baseChange ℂ (jetDeriv μ) y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    simp only [add_mul, map_add, ha, hb]
    ring
  | tmul c b =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a' b' ha' hb' =>
      simp only [mul_add, map_add, ha', hb']
      ring
    | tmul c' b' =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.baseChange_tmul,
        jetDeriv_mul, TensorProduct.tmul_add]

/-- The complexified total derivative on a jet-algebra generator. -/
lemma jetDeriv_baseChange_ofGenerator (ν : Fin 1 ⊕ Fin 3) (g : JetGenerators) :
    LinearMap.baseChange ℂ (jetDeriv ν) ((1 : ℂ) ⊗ₜ[ℝ] ofGenerator g) =
      (1 : ℂ) ⊗ₜ[ℝ] ofGenerator (JetGenerators.shift ν g) := by
  rw [LinearMap.baseChange_tmul, jetDeriv_ofGenerator]

/-- The polynomial coordinates of the total derivative. -/
lemma equivMvPolynomial_jetDeriv (ν : Fin 1 ⊕ Fin 3) (x : JetAlgebra) :
    SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis (jetDeriv ν x) =
      (MvPolynomial.mkDerivation ℝ fun g : JetGenerators =>
        (MvPolynomial.X (JetGenerators.shift ν g) : MvPolynomial JetGenerators ℝ))
        (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis x) := by
  simp only [jetDeriv, LinearMap.coe_comp, Function.comp_apply,
    AlgEquiv.toLinearMap_apply, AlgEquiv.apply_symm_apply, Derivation.coeFn_coe]

/-!

## The Maurer–Cartan correction derivations

A local gauge transformation changes the B boson by a gradient, `δB_μ = ∂_μλ`
with `λ` the phase of the `U(1)` jet (the Maurer–Cartan form is closed,
`pderiv_maurerCartanU1_symm`). On genuine field configurations this variation
commutes with differentiation, since `δ(∂_s B_μ) = ∂_s ∂_μ λ`. The jet algebra,
however, remembers of `λ` only its Taylor coefficients at the base point: the
gauge action shifts each coordinate `∂_s B_μ` by the frozen constant
`⟨mc, ∂_s B_μ⟩ = (∂_s ∂_μ λ)(0)`, and the formal total derivative annihilates
constants while sending `∂_s B_μ` to `∂_{s+ν} B_μ`. Differentiating after
transforming therefore drops exactly the term that, on fields, would come from
the derivative hitting the gauge parameter.

The correction derivation `mcDeriv U t` reinstates that term as an operator:
"differentiation acting on the gauge parameter instead of the field", the
derivation sending each component function `∂_s B_ν` to the constant
`⟨mc, ∂_{s+t} B_ν⟩`. The commutator of the gauge action with the total
derivative is the gauge action composed with the weight-`{ν}` correction
(`repJetGaugeGroupI_jetDeriv`), and commuting a correction past a further
derivative raises its weight (`mcDeriv_jetDeriv`), so the corrections close
into an algebra.

This algebra is what makes covariant derivatives of charged fields covariant:
in `D_μψ = ∂_μψ - i q B_μ ψ` the gauge shift of `B_μ` must cancel the
derivative of the hypercharge character produced by `∂_μ` acting on the
transformed `ψ`, and at higher orders the iterated derivatives of the gauge
parameter on both sides are matched precisely by the anomaly operators built
from `mcDeriv`, which annihilate the covariant derivatives (see
`QED.JetAlgebra`).

-/

/-- The Maurer–Cartan correction derivation of weight `t` of a `U(1)` jet: the
  derivation of the B-boson jet algebra sending the component function `∂_s B_ν`
  to the constant `⟨mc, ∂_{s+t} B_ν⟩`. -/
noncomputable def mcDeriv (U : JetGaugeGroupI) (t : Multiset (Fin 1 ⊕ Fin 3)) :
    JetAlgebra →ₗ[ℝ] JetAlgebra :=
  (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis).symm.toLinearMap ∘ₗ
    (MvPolynomial.mkDerivation ℝ fun g : JetGenerators =>
      (MvPolynomial.C (mcPairing U (JetComponentSpace.basis
        (JetGenerators.shiftMulti t g))) : MvPolynomial JetGenerators ℝ)).toLinearMap ∘ₗ
    (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis).toLinearMap

@[simp]
lemma mcDeriv_ofGenerator (U : JetGaugeGroupI) (t : Multiset (Fin 1 ⊕ Fin 3))
    (g : JetGenerators) :
    mcDeriv U t (ofGenerator g) = algebraMap ℝ JetAlgebra
      (mcPairing U (JetComponentSpace.basis (JetGenerators.shiftMulti t g))) := by
  simp only [mcDeriv, ofGenerator, LinearMap.coe_comp, Function.comp_apply,
    AlgEquiv.toLinearMap_apply, Derivation.coeFn_coe]
  rw [SymmetricAlgebra.equivMvPolynomial_ι_apply, MvPolynomial.mkDerivation_X,
    ← MvPolynomial.algebraMap_eq]
  exact AlgEquiv.commutes _ _

@[simp]
lemma mcDeriv_one (U : JetGaugeGroupI) (t : Multiset (Fin 1 ⊕ Fin 3)) :
    mcDeriv U t (1 : JetAlgebra) = 0 := by
  simp [mcDeriv]

/-- The correction derivations satisfy the Leibniz rule. -/
lemma mcDeriv_mul (U : JetGaugeGroupI) (t : Multiset (Fin 1 ⊕ Fin 3))
    (x y : JetAlgebra) :
    mcDeriv U t (x * y) = mcDeriv U t x * y + x * mcDeriv U t y := by
  simp only [mcDeriv, LinearMap.coe_comp, Function.comp_apply,
    AlgEquiv.toLinearMap_apply, map_mul, Derivation.coeFn_coe, Derivation.leibniz,
    smul_eq_mul, map_add, AlgEquiv.symm_apply_apply]
  ring

/-- The complexified Leibniz rule for the correction derivations. -/
lemma mcDeriv_baseChange_mul (U : JetGaugeGroupI) (t : Multiset (Fin 1 ⊕ Fin 3))
    (x y : ℂ ⊗[ℝ] JetAlgebra) :
    LinearMap.baseChange ℂ (mcDeriv U t) (x * y) =
      LinearMap.baseChange ℂ (mcDeriv U t) x * y +
        x * LinearMap.baseChange ℂ (mcDeriv U t) y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    simp only [add_mul, map_add, ha, hb]
    ring
  | tmul c b =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a' b' ha' hb' =>
      simp only [mul_add, map_add, ha', hb']
      ring
    | tmul c' b' =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.baseChange_tmul,
        mcDeriv_mul, TensorProduct.tmul_add]

/-- The polynomial coordinates of the correction derivations. -/
lemma equivMvPolynomial_mcDeriv (U : JetGaugeGroupI) (t : Multiset (Fin 1 ⊕ Fin 3))
    (x : JetAlgebra) :
    SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis (mcDeriv U t x) =
      (MvPolynomial.mkDerivation ℝ fun g : JetGenerators =>
        (MvPolynomial.C (mcPairing U (JetComponentSpace.basis
          (JetGenerators.shiftMulti t g))) : MvPolynomial JetGenerators ℝ))
        (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis x) := by
  simp only [mcDeriv, LinearMap.coe_comp, Function.comp_apply,
    AlgEquiv.toLinearMap_apply, AlgEquiv.apply_symm_apply, Derivation.coeFn_coe]

/-- Commutation of the correction derivations with the total derivative: the
  weight of the correction absorbs the derivative index. -/
lemma mcDeriv_jetDeriv (U : JetGaugeGroupI) (t : Multiset (Fin 1 ⊕ Fin 3))
    (ν : Fin 1 ⊕ Fin 3) (x : JetAlgebra) :
    mcDeriv U t (jetDeriv ν x) =
      jetDeriv ν (mcDeriv U t x) + mcDeriv U (t + {ν}) x := by
  have key : ∀ p : MvPolynomial JetGenerators ℝ,
      (MvPolynomial.mkDerivation ℝ fun g : JetGenerators =>
        (MvPolynomial.C (mcPairing U (JetComponentSpace.basis
          (JetGenerators.shiftMulti t g))) : MvPolynomial JetGenerators ℝ))
        ((MvPolynomial.mkDerivation ℝ fun g : JetGenerators =>
          (MvPolynomial.X (JetGenerators.shift ν g) : MvPolynomial JetGenerators ℝ)) p) =
      (MvPolynomial.mkDerivation ℝ fun g : JetGenerators =>
        (MvPolynomial.X (JetGenerators.shift ν g) : MvPolynomial JetGenerators ℝ))
        ((MvPolynomial.mkDerivation ℝ fun g : JetGenerators =>
          (MvPolynomial.C (mcPairing U (JetComponentSpace.basis
            (JetGenerators.shiftMulti t g))) : MvPolynomial JetGenerators ℝ)) p) +
      (MvPolynomial.mkDerivation ℝ fun g : JetGenerators =>
        (MvPolynomial.C (mcPairing U (JetComponentSpace.basis
          (JetGenerators.shiftMulti (t + {ν}) g))) : MvPolynomial JetGenerators ℝ)) p := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      simp [MvPolynomial.derivation_C]
    | add p q hp hq =>
      simp only [map_add, hp, hq]
      ring
    | mul_X p g ih =>
      have hlam : mcPairing U (JetComponentSpace.basis
          (JetGenerators.shiftMulti t (JetGenerators.shift ν g))) =
          mcPairing U (JetComponentSpace.basis
            (JetGenerators.shiftMulti (t + {ν}) g)) := by
        rw [JetGenerators.shiftMulti_shift]
      simp only [Derivation.leibniz, smul_eq_mul, MvPolynomial.mkDerivation_X,
        MvPolynomial.derivation_C, map_add, mul_zero, zero_add]
      rw [ih, hlam]
      ring
  rw [show mcDeriv U t (jetDeriv ν x) =
      (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis).symm
        (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis
          (mcDeriv U t (jetDeriv ν x))) from
      (AlgEquiv.symm_apply_apply _ _).symm,
    equivMvPolynomial_mcDeriv, equivMvPolynomial_jetDeriv, key, map_add,
    ← equivMvPolynomial_mcDeriv U t x, ← equivMvPolynomial_jetDeriv ν (mcDeriv U t x),
    AlgEquiv.symm_apply_apply, ← equivMvPolynomial_mcDeriv U (t + {ν}) x,
    AlgEquiv.symm_apply_apply]

/-- Commutation of the jet gauge action with the total derivative: the
  substitution action commutes with `∂_ν` up to the Maurer–Cartan correction
  derivation of weight `{ν}`. -/
lemma repJetGaugeGroupI_jetDeriv (U : JetGaugeGroupI) (ν : Fin 1 ⊕ Fin 3)
    (x : JetAlgebra) : repJetGaugeGroupI U (jetDeriv ν x) =
      jetDeriv ν (repJetGaugeGroupI U x) + repJetGaugeGroupI U (mcDeriv U {ν} x) := by
  have key : ∀ p : MvPolynomial JetGenerators ℝ,
      MvPolynomial.aeval (fun g => MvPolynomial.X g +
          MvPolynomial.C (mcPairing U (JetComponentSpace.basis g)))
        ((MvPolynomial.mkDerivation ℝ fun g : JetGenerators =>
          (MvPolynomial.X (JetGenerators.shift ν g) : MvPolynomial JetGenerators ℝ)) p) =
      (MvPolynomial.mkDerivation ℝ fun g : JetGenerators =>
        (MvPolynomial.X (JetGenerators.shift ν g) : MvPolynomial JetGenerators ℝ))
        (MvPolynomial.aeval (fun g => MvPolynomial.X g +
          MvPolynomial.C (mcPairing U (JetComponentSpace.basis g))) p) +
      MvPolynomial.aeval (fun g => MvPolynomial.X g +
          MvPolynomial.C (mcPairing U (JetComponentSpace.basis g)))
        ((MvPolynomial.mkDerivation ℝ fun g : JetGenerators =>
          (MvPolynomial.C (mcPairing U (JetComponentSpace.basis
            (JetGenerators.shiftMulti {ν} g))) : MvPolynomial JetGenerators ℝ)) p) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      simp [MvPolynomial.derivation_C, MvPolynomial.algebraMap_eq]
    | add p q hp hq =>
      simp only [map_add, hp, hq]
      ring
    | mul_X p g ih =>
      have hlam : mcPairing U (JetComponentSpace.basis (JetGenerators.shift ν g)) =
          mcPairing U (JetComponentSpace.basis
            (JetGenerators.shiftMulti {ν} g)) := by
        rw [JetGenerators.shiftMulti_singleton]
      simp only [Derivation.leibniz, smul_eq_mul, MvPolynomial.mkDerivation_X,
        MvPolynomial.derivation_C, map_add, map_mul, add_zero,
        MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
      rw [ih, hlam]
      ring
  rw [show repJetGaugeGroupI U (jetDeriv ν x) =
      (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis).symm
        (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis
          (repJetGaugeGroupI U (jetDeriv ν x))) from
      (AlgEquiv.symm_apply_apply _ _).symm,
    equivMvPolynomial_repJetGaugeGroupI, equivMvPolynomial_jetDeriv, key, map_add,
    ← equivMvPolynomial_repJetGaugeGroupI U x,
    ← equivMvPolynomial_jetDeriv ν (repJetGaugeGroupI U x),
    ← equivMvPolynomial_mcDeriv U {ν} x,
    ← equivMvPolynomial_repJetGaugeGroupI U (mcDeriv U {ν} x),
    AlgEquiv.symm_apply_apply]
  congr 1
  exact AlgEquiv.symm_apply_apply _ _

/-- The complexified commutation of the gauge action with the total
  derivative. -/
lemma complexRepJetGaugeGroupI_baseChange_jetDeriv (U : JetGaugeGroupI)
    (ν : Fin 1 ⊕ Fin 3) (y : ℂ ⊗[ℝ] JetAlgebra) :
    complexRepJetGaugeGroupI U (LinearMap.baseChange ℂ (jetDeriv ν) y) =
      LinearMap.baseChange ℂ (jetDeriv ν) (complexRepJetGaugeGroupI U y) +
        complexRepJetGaugeGroupI U
          (LinearMap.baseChange ℂ (mcDeriv U {ν}) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    simp only [map_add, ha, hb]
    abel
  | tmul c b =>
    simp only [LinearMap.baseChange_tmul, complexRepJetGaugeGroupI_tmul,
      repJetGaugeGroupI_jetDeriv, TensorProduct.tmul_add]

/-- The complexified commutation of the correction derivations with the total
  derivative. -/
lemma mcDeriv_baseChange_jetDeriv (U : JetGaugeGroupI)
    (t : Multiset (Fin 1 ⊕ Fin 3)) (ν : Fin 1 ⊕ Fin 3) (y : ℂ ⊗[ℝ] JetAlgebra) :
    LinearMap.baseChange ℂ (mcDeriv U t) (LinearMap.baseChange ℂ (jetDeriv ν) y) =
      LinearMap.baseChange ℂ (jetDeriv ν)
          (LinearMap.baseChange ℂ (mcDeriv U t) y) +
        LinearMap.baseChange ℂ (mcDeriv U (t + {ν})) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    simp only [map_add, ha, hb]
    abel
  | tmul c b =>
    simp only [LinearMap.baseChange_tmul, mcDeriv_jetDeriv, TensorProduct.tmul_add]


/-- The complexified correction derivation on a jet-algebra generator. -/
lemma mcDeriv_baseChange_ofGenerator (U : JetGaugeGroupI)
    (t : Multiset (Fin 1 ⊕ Fin 3)) (g : JetGenerators) :
    LinearMap.baseChange ℂ (mcDeriv U t) ((1 : ℂ) ⊗ₜ[ℝ] ofGenerator g) =
      ((mcPairing U (JetComponentSpace.basis (JetGenerators.shiftMulti t g)) : ℝ) : ℂ) •
        ((1 : ℂ) ⊗ₜ[ℝ] (1 : JetAlgebra)) := by
  rw [LinearMap.baseChange_tmul, mcDeriv_ofGenerator, Algebra.algebraMap_eq_smul_one,
    TensorProduct.tmul_smul,
    show ((mcPairing U (JetComponentSpace.basis (JetGenerators.shiftMulti t g)) : ℝ) : ℂ) =
      algebraMap ℝ ℂ (mcPairing U (JetComponentSpace.basis
        (JetGenerators.shiftMulti t g))) from rfl,
    algebraMap_smul]

/-!

## The field strength of the B boson

-/

/-- The field strength of the B boson: the antisymmetrized derivative of the
  component functions, which is gauge-invariant. -/
noncomputable def fieldStrength (μ ν : Fin 1 ⊕ Fin 3) : BBoson.JetAlgebra :=
  ofGenerator (JetGenerators.dB {μ} ν) - ofGenerator (JetGenerators.dB {ν} μ)

lemma fieldStrength_antisymm (μ ν : Fin 1 ⊕ Fin 3) :
    fieldStrength μ ν = -fieldStrength ν μ := by
  simp [fieldStrength]

lemma repJetGaugeGroupI_fieldStrength (U : JetGaugeGroupI) (μ ν : Fin 1 ⊕ Fin 3) :
    repJetGaugeGroupI U (fieldStrength μ ν) = fieldStrength μ ν := by
  simp only [fieldStrength, map_sub, ofGenerator, repJetGaugeGroupI_ι, mcPairing_basis_dB]
  rw [maurerCartanU1Coeff_single_symm]
  abel

noncomputable def fieldStrengthDeriv (s : Multiset (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) :
    BBoson.JetAlgebra :=
  ofGenerator (JetGenerators.dB (s + {μ}) ν) - ofGenerator (JetGenerators.dB (s + {ν}) μ)

lemma fieldStrengthDeriv_antisymm (s : Multiset (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) :
    fieldStrengthDeriv s μ ν = -fieldStrengthDeriv s ν μ := by
  simp [fieldStrengthDeriv]

lemma repJetGaugeGroupI_fieldStrengthDeriv (U : JetGaugeGroupI) (s : Multiset (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) :
    repJetGaugeGroupI U (fieldStrengthDeriv s μ ν) = fieldStrengthDeriv s μ ν := by
  simp only [fieldStrengthDeriv, map_sub, ofGenerator, repJetGaugeGroupI_ι]
  rw [mcPairing_basis_dB_symm]
  abel

lemma fieldStrengthDeriv_bianchi_identity (s : Multiset (Fin 1 ⊕ Fin 3)) (μ ν ρ : Fin 1 ⊕ Fin 3) :
    fieldStrengthDeriv (s + {μ}) ν ρ + fieldStrengthDeriv (s + {ν}) ρ μ +
      fieldStrengthDeriv (s + {ρ}) μ ν = 0 := by
  simp only [fieldStrengthDeriv]
  grind


/-!

## A. Invariance under the gauge group

We now want to show that the if an element of the jet algebra is invariant under
the action of the jet gauge group, then it is a polynomial
in the field strength and its derivatives.

-/


/-!

## Gauge realization of translations of the jet coordinates

To identify the gauge invariants of the jet algebra we need not only that every
jet gauge transformation shifts the component functions by the Maurer–Cartan
pairing, but also that enough shifts are realized: for every nonzero symmetrized
multi-index `t` and every real `r` there is a jet of a local `U(1)` gauge
transformation shifting every component function with total multi-index `t` by
exactly `r`, and all others by nothing. The transformation realizing this is the
exponential `exp(-i a X^t)` with `a = r / t!`, formalized through
`MvPowerSeries.expMonomial`.

-/

/-- The jet of the local `U(1)` gauge transformation `exp(-i a X^w)`: the
  exponential of an imaginary multiple of a spacetime monomial, which is unitary
  as a formal power series. -/
noncomputable def expUnitary (a : ℝ) (w : (Fin 1 ⊕ Fin 3) →₀ ℕ) (hw : w ≠ 0) :
    unitary JetRing :=
  ⟨expMonomial (-(a : ℂ) * Complex.I) w, by
    have hstar : star (-(a : ℂ) * Complex.I) = -(-(a : ℂ) * Complex.I) := by
      rw [star_mul', Complex.star_def, Complex.conj_I, map_neg, Complex.conj_ofReal]
      ring
    rw [Unitary.mem_iff, star_expMonomial hw, hstar, expMonomial_mul_expMonomial hw,
      expMonomial_mul_expMonomial hw, neg_add_cancel, add_neg_cancel,
      expMonomial_zero hw]
    exact ⟨rfl, rfl⟩⟩

/-- The Maurer–Cartan series of the exponential gauge jet: the monomial
  `a w_ν X^{w - e_ν}`, which is the jet of the gradient `a ∂_ν X^w`. -/
lemma maurerCartanU1_expUnitary (a : ℝ) (w : (Fin 1 ⊕ Fin 3) →₀ ℕ) (hw : w ≠ 0)
    (ν : Fin 1 ⊕ Fin 3) :
    maurerCartanU1 (1, 1, expUnitary a w hw) ν =
      monomial (w - Finsupp.single ν 1) ((a : ℂ) * ((w ν : ℕ) : ℂ)) := by
  have hstar : star (-(a : ℂ) * Complex.I) = -(-(a : ℂ) * Complex.I) := by
    rw [star_mul', Complex.star_def, Complex.conj_I, map_neg, Complex.conj_ofReal]
    ring
  rw [maurerCartanU1,
    show (((1, 1, expUnitary a w hw) : JetGaugeGroupI).2.2 : JetRing) =
      expMonomial (-(a : ℂ) * Complex.I) w from rfl,
    pderiv_expMonomial hw, star_expMonomial hw, hstar, smul_mul_assoc,
    mul_assoc (monomial (w - Finsupp.single ν 1) 1),
    expMonomial_mul_expMonomial hw, add_neg_cancel, expMonomial_zero hw, mul_one,
    mul_smul_comm, ← monomial_zero_eq_C_apply, monomial_mul_monomial, zero_add,
    ← map_smul, smul_eq_mul]
  congr 1
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The Maurer–Cartan pairing of the exponential gauge jet `exp(-i a X^t)` with
  `a = r / t!`: it shifts precisely the component functions whose total
  symmetrized multi-index is `t`, and shifts them all by `r`. -/
lemma mcPairing_expUnitary (t : Multiset (Fin 1 ⊕ Fin 3))
    (ht : Multiset.toFinsupp t ≠ 0) (r : ℝ) (s : Multiset (Fin 1 ⊕ Fin 3))
    (ν : Fin 1 ⊕ Fin 3) :
    mcPairing (1, 1, expUnitary (r / (∏ ρ, Nat.factorial (Multiset.toFinsupp t ρ)))
        (Multiset.toFinsupp t) ht) (JetComponentSpace.basis (.dB s ν)) =
      if s + {ν} = t then r else 0 := by
  rw [mcPairing_basis_dB', Complex.selfAdjointEquiv_apply,
    show ((maurerCartanU1Coeff (1, 1, expUnitary (r / (∏ ρ, Nat.factorial (Multiset.toFinsupp t ρ)))
        (Multiset.toFinsupp t) ht) ν (Multiset.toFinsupp s) : selfAdjoint ℂ) : ℂ) =
      coeff (Multiset.toFinsupp s) (maurerCartanU1 (1, 1, expUnitary
        (r / (∏ ρ, Nat.factorial (Multiset.toFinsupp t ρ)))
        (Multiset.toFinsupp t) ht) ν) from rfl,
    maurerCartanU1_expUnitary, coeff_monomial]
  by_cases hcase : s + {ν} = t
  · rw [if_pos hcase]
    have hmw : Multiset.toFinsupp s + Finsupp.single ν 1 = Multiset.toFinsupp t := by
      rw [← Multiset.toFinsupp_singleton, ← map_add]
      exact congrArg _ hcase
    have hwv : Multiset.toFinsupp t ν = Multiset.toFinsupp s ν + 1 := by
      rw [← hmw]
      simp
    have hm : Multiset.toFinsupp s = Multiset.toFinsupp t - Finsupp.single ν 1 :=
      eq_tsub_of_add_eq hmw
    have hF : (∏ ρ, Nat.factorial ((Multiset.toFinsupp t) ρ)) =
        ((Multiset.toFinsupp s) ν + 1) *
          ∏ ρ, Nat.factorial ((Multiset.toFinsupp s) ρ) := by
      rw [← hmw]
      exact prod_factorial_add_single (Multiset.toFinsupp s) ν
    rw [if_pos hm, nsmul_eq_mul, hwv, hF]
    have h1 : (((Multiset.toFinsupp s) ν + 1 : ℕ) : ℝ) ≠ 0 := by
      positivity
    have h2 : ((∏ ρ, Nat.factorial ((Multiset.toFinsupp s) ρ) : ℕ) : ℝ) ≠ 0 := by
      rw [Nat.cast_ne_zero]
      exact Finset.prod_ne_zero_iff.mpr fun ρ _ => Nat.factorial_ne_zero _
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re,
      Complex.natCast_im, mul_zero, sub_zero]
    push_cast
    field_simp
  · rw [if_neg hcase]
    by_cases hm : Multiset.toFinsupp s = Multiset.toFinsupp t - Finsupp.single ν 1
    · by_cases hwv : Multiset.toFinsupp t ν = 0
      · rw [if_pos hm, hwv]
        simp
      · exfalso
        apply hcase
        have hle : Finsupp.single ν 1 ≤ Multiset.toFinsupp t :=
          Finsupp.single_le_iff.mpr (Nat.pos_of_ne_zero hwv)
        have hmw : Multiset.toFinsupp s + Finsupp.single ν 1 = Multiset.toFinsupp t := by
          rw [hm, tsub_add_cancel_of_le hle]
        refine Multiset.toFinsupp.injective ?_
        rw [map_add, Multiset.toFinsupp_singleton]
        exact hmw
    · rw [if_neg hm]
      simp


/-- The difference between a jet-algebra generator and its canonical
  representative is a derivative of the field strength, or zero. -/
lemma ofGenerator_sub_ofGenerator_canon_mem (g : JetGenerators) :
    ofGenerator g - ofGenerator (JetGenerators.canon g) ∈
      Algebra.adjoin ℝ (fieldStrengthDeriv.uncurry.uncurry '' Set.univ) := by
  obtain ⟨s, ν⟩ := g
  set p := JetGenerators.pick (JetGenerators.total (JetGenerators.dB s ν)) with hp
  by_cases hpν : p = ν
  · have hcanon : JetGenerators.canon (JetGenerators.dB s ν) = JetGenerators.dB s ν := by
      rw [JetGenerators.canon, ← hp, hpν]
      congr 1
      show (s + {ν}).erase ν = s
      rw [add_comm, Multiset.singleton_add, Multiset.erase_cons_head]
    rw [hcanon, sub_self]
    exact Subalgebra.zero_mem _
  · have hmem : p ∈ s + {ν} :=
      JetGenerators.pick_mem (JetGenerators.total_ne_zero (JetGenerators.dB s ν))
    have hps : p ∈ s := by
      rcases Multiset.mem_add.mp hmem with h | h
      · exact h
      · exact absurd (Multiset.mem_singleton.mp h) hpν
    have h2 : JetGenerators.canon (JetGenerators.dB s ν) =
        JetGenerators.dB (s.erase p + {ν}) p := by
      rw [JetGenerators.canon, ← hp]
      congr 1
      show (s + {ν}).erase p = s.erase p + {ν}
      exact Multiset.erase_add_left_pos _ hps
    have h1 : JetGenerators.dB s ν = JetGenerators.dB (s.erase p + {p}) ν := by
      congr 1
      rw [add_comm, Multiset.singleton_add]
      exact (Multiset.cons_erase hps).symm
    rw [h2, h1]
    exact Algebra.subset_adjoin ⟨((s.erase p, p), ν), Set.mem_univ _, rfl⟩

/-- An EFT lagrangian with field content consisting only of
  a `B` bosons is invariant under the full gauge group if and only if
  it can be written in terms of the field strength and derivatives thereof. -/
lemma repJetGaugeGroupI_apply_eq_self_iff_mem (V : JetAlgebra) :
  (∀ U, repJetGaugeGroupI U V = V) ↔ V ∈ Algebra.adjoin ℝ
    (fieldStrengthDeriv.uncurry.uncurry '' Set.univ) := by
  constructor
  · intro hV
    have htrans : ∀ (g₀ : JetGenerators) (r : ℝ),
        MvPolynomial.aeval (fun g => MvPolynomial.X g +
          MvPolynomial.C (if JetGenerators.canon g = JetGenerators.canon g₀ then r
            else (0 : ℝ)))
          (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis V) =
          SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis V := by
      intro g₀ r
      obtain ⟨s₀, ν₀⟩ := g₀
      have hne : Multiset.toFinsupp (s₀ + {ν₀}) ≠ 0 := by
        intro h
        have h0 : s₀ + {ν₀} = 0 :=
          Multiset.toFinsupp.injective (by rw [h, Multiset.toFinsupp_zero])
        simp at h0
      have hconj := equivMvPolynomial_repJetGaugeGroupI_u1
        (expUnitary (r / (∏ ρ, Nat.factorial ((Multiset.toFinsupp (s₀ + {ν₀})) ρ)))
          (Multiset.toFinsupp (s₀ + {ν₀})) hne) V
      rw [hV _] at hconj
      have hfun : (fun g => MvPolynomial.X g + MvPolynomial.C
          (mcPairing (1, 1, expUnitary
              (r / (∏ ρ, Nat.factorial ((Multiset.toFinsupp (s₀ + {ν₀})) ρ)))
              (Multiset.toFinsupp (s₀ + {ν₀})) hne)
            (JetComponentSpace.basis g))) =
          fun g => MvPolynomial.X g + MvPolynomial.C
            (if JetGenerators.canon g = JetGenerators.canon (JetGenerators.dB s₀ ν₀)
              then r else (0 : ℝ)) := by
        funext g
        obtain ⟨s, ν⟩ := g
        rw [mcPairing_expUnitary (s₀ + {ν₀}) hne r s ν]
        have hiff : (s + {ν} = s₀ + {ν₀}) ↔
            (JetGenerators.canon (JetGenerators.dB s ν) =
              JetGenerators.canon (JetGenerators.dB s₀ ν₀)) := by
          rw [JetGenerators.canon_eq_canon_iff]
          simp
        rw [if_congr hiff rfl rfl]
      rw [hfun] at hconj
      exact hconj.symm
    have hmem := MvPolynomial.mem_adjoin_range_X_sub_X_of_forall_aeval_add_eq
      JetGenerators.canon JetGenerators.canon_canon
      (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis V) htrans
    have hVmem : V ∈ (Algebra.adjoin ℝ (Set.range fun g =>
        (MvPolynomial.X g - MvPolynomial.X (JetGenerators.canon g) :
          MvPolynomial JetGenerators ℝ))).map
        (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis).symm.toAlgHom :=
      Subalgebra.mem_map.mpr ⟨_, hmem, AlgEquiv.symm_apply_apply _ _⟩
    rw [AlgHom.map_adjoin] at hVmem
    refine Algebra.adjoin_le ?_ hVmem
    rintro x ⟨_, ⟨g, rfl⟩, rfl⟩
    have hsymm : (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis).symm.toAlgHom
        (MvPolynomial.X g - MvPolynomial.X (JetGenerators.canon g)) =
        ofGenerator g - ofGenerator (JetGenerators.canon g) := by
      show (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis).symm
        (MvPolynomial.X g - MvPolynomial.X (JetGenerators.canon g)) = _
      rw [map_sub, SymmetricAlgebra.equivMvPolynomial_symm_X,
        SymmetricAlgebra.equivMvPolynomial_symm_X]
      rfl
    rw [hsymm]
    exact ofGenerator_sub_ofGenerator_canon_mem g
  · intro hVmem U
    induction hVmem using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨⟨⟨s', μ⟩, ν⟩, -, rfl⟩ := hx
      exact repJetGaugeGroupI_fieldStrengthDeriv U s' μ ν
    | algebraMap r => exact repJetGaugeGroupI_algebraMap U r
    | add x y hx hy ihx ihy => rw [map_add, ihx, ihy]
    | mul x y hx hy ihx ihy => rw [repJetGaugeGroupI_mul, ihx, ihy]

end JetAlgebra

end BBoson

end StandardModel
