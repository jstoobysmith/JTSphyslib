/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!

# Example of the Higgs boson

This file is a self-contained example, importing only Mathlib, building up to the result
`apply_eq_sum_norm_pow`: a gauge-invariant effective potential of bounded mass dimension can be
written as a sum of even powers of the norm of the Higgs field.

It reproduces, in a single file, the prerequisites from `Physlib` needed to state and prove that
result.

-/

@[expose] public section

noncomputable section

namespace StandardModel

open Manifold
open Matrix
open Complex
open ComplexConjugate

/-!

## A. The gauge group of the Standard Model

**Talk step 1 — What is a type?**

In Lean every expression has a *type*, and a type is itself a term of the universe `Type`. Think
of a type as the collection of mathematical objects of a given kind: `ℕ` is the type of natural
numbers, `ℝ` the type of real numbers, and the `GaugeGroupI` defined below is the type whose terms
are elements of the Standard Model gauge group `SU(3) × SU(2) × U(1)`.

Writing `def GaugeGroupI : Type := ...` introduces a brand-new named object and tells the kernel
exactly what its elements are. At this stage that is *all* Lean knows about it — a collection of
elements, with no further structure attached yet.

-/

/-- The global gauge group of the Standard Model with no discrete quotients.
  The `I` in the Name is an indication of the statement that this has no discrete quotients. -/
def GaugeGroupI : Type :=
  specialUnitaryGroup (Fin 3) ℂ × specialUnitaryGroup (Fin 2) ℂ × unitary ℂ

namespace GaugeGroupI

/-!

**Talk step 2 — What is an instance?**

-/

instance : Group GaugeGroupI :=
  inferInstanceAs (Group (specialUnitaryGroup (Fin 3) ℂ × specialUnitaryGroup (Fin 2) ℂ ×
    unitary ℂ))

/-!

**Talk step 3 — How do definitions work?**

-/

/-- The underlying element of `SU(2)` of an element in `GaugeGroupI`. -/
def toSU2 : GaugeGroupI →* specialUnitaryGroup (Fin 2) ℂ where
  toFun g := g.2.1
  map_one' := rfl
  map_mul' _ _ := rfl

/-!

**Talk step 4 — How the type system rules out nonsense.**

-/

-- example (g : specialUnitaryGroup (Fin 2) ℂ) : toSU2 g = g := by sorry

example (g : specialUnitaryGroup (Fin 2) ℂ) : toSU2 ⟨1, g, 1⟩ = g := by rfl

/-- The underlying element of `U(1)` of an element in `GaugeGroupI`. -/
def toU1 : GaugeGroupI →* unitary ℂ where
  toFun g := g.2.2
  map_one' := rfl
  map_mul' _ _ := rfl

end GaugeGroupI

/-!

## B. The Higgs vector space

The target space of the Higgs field is a 2-dimensional complex vector space. In this section we
define this space, the action of the gauge group on it, and the facts about that action needed
later.

-/

/-- The vector space `HiggsVec` is defined to be the complex Euclidean space of dimension 2.
  For a given spacetime point a Higgs field gives a value in `HiggsVec`. -/
abbrev HiggsVec := EuclideanSpace ℂ (Fin 2)

namespace HiggsVec

/-!

### B.1. Relation to `(Fin 2 → ℂ)`

We define the continuous linear map from `HiggsVec` to `(Fin 2 → ℂ)` achieved by casting vectors.

-/

/-- The continuous linear map from the vector space `HiggsVec` to `(Fin 2 → ℂ)` achieved by
casting vectors. -/
def toFin2ℂ : HiggsVec →L[ℝ] (Fin 2 → ℂ) where
  toFun x := x
  map_add' x y := rfl
  map_smul' a x := rfl

/-!

### B.2. Generating Higgs vectors from real numbers

Given a real number `a` we define the Higgs vector corresponding to that real number
as `(√a, 0)`. This has the property that its norm-squared is equal to `a`.

-/

/-- Generating a Higgs vector from a real number, such that the norm-squared of that Higgs vector
  is the given real number. -/
def ofReal (a : ℝ) : HiggsVec :=
  !₂[Real.sqrt a, 0]

/-!

### B.3. Action of the gauge group on `HiggsVec`

The gauge group of the Standard Model acts on `HiggsVec` by matrix multiplication.

-/

/-!

#### B.3.1. Definition of the action

-/

instance : SMul StandardModel.GaugeGroupI HiggsVec where
  smul g φ := WithLp.toLp 2 <| g.toU1 ^ 3 • (g.toSU2.1 *ᵥ φ.ofLp)

lemma gaugeGroupI_smul_eq (g : StandardModel.GaugeGroupI) (φ : HiggsVec) :
    g • φ = (WithLp.toLp 2 <| g.toU1 ^ 3 • (g.toSU2.1 *ᵥ φ.ofLp)) := rfl

lemma gaugeGroupI_smul_eq_U1_mul_SU2 (g : StandardModel.GaugeGroupI) (φ : HiggsVec) :
    g • φ = (WithLp.toLp 2 <| g.toSU2.1 *ᵥ (g.toU1 ^ 3 • φ.ofLp)) := by
  rw [gaugeGroupI_smul_eq, ← mulVec_smul]


instance : MulAction StandardModel.GaugeGroupI HiggsVec where
  one_smul φ := by simp [gaugeGroupI_smul_eq]
  mul_smul g₁ g₂ φ := by
    rw [gaugeGroupI_smul_eq, gaugeGroupI_smul_eq, gaugeGroupI_smul_eq_U1_mul_SU2]
    rw [mulVec_smul, mulVec_smul, smul_smul, mulVec_mulVec]
    congr
    simp [mul_pow]

instance : SMulCommClass ℂ GaugeGroupI HiggsVec where
  smul_comm r g φ := by
    simp [gaugeGroupI_smul_eq, mulVec_smul]
    rw [smul_comm]


/-!

#### B.3.2. Unitary nature of the action

The action of `StandardModel.GaugeGroupI` on `HiggsVec` is unitary.

**Talk step 5 — Lemmas, tactics and `calc`.**

-/
open InnerProductSpace

@[simp]
lemma gaugeGroupI_smul_inner (g : GaugeGroupI) (φ ψ : HiggsVec) :
    ⟪g • φ, g • ψ⟫_ℂ = ⟪φ, ψ⟫_ℂ := by
  -- The gauge action is `φ ↦ S *ᵥ (U³ • φ)`, where `S = g.toSU2` is a unitary `SU(2)` matrix and
  -- `U = g.toU1` is a `U(1)` phase. Both factors are unitary, so the action preserves the
  -- Hermitian inner product. The strategy is to write the inner product as a dot product against
  -- the conjugated vector, push `S` and `U³` through the conjugation, then cancel them using
  -- `Sᴴ S = 1` and `|U³| = 1`.
  calc ⟪g • φ, g • ψ⟫_ℂ
    -- Express the Hermitian inner product as a dot product with the conjugated first argument:
    -- `⟪a, b⟫ = b ⬝ᵥ star a`.
    _ = WithLp.ofLp (g • ψ) ⬝ᵥ star (WithLp.ofLp (g • φ)) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
    -- Unfold the action on both vectors: `g • x = S *ᵥ (U³ • x)`.
    _ = (g.toSU2.1 *ᵥ (g.toU1 ^ 3 • ψ)) ⬝ᵥ star (g.toSU2.1 *ᵥ (g.toU1 ^ 3 • φ)) := by
      rw [gaugeGroupI_smul_eq_U1_mul_SU2, gaugeGroupI_smul_eq_U1_mul_SU2]
    -- Conjugate-transpose distributes over matrix–vector multiplication, `(S x)ᴴ = xᴴ Sᴴ`,
    -- i.e. `star (S *ᵥ x) = star x ᵥ* star S`.
    _ = (g.toSU2.1 *ᵥ (g.toU1 ^ 3 • ψ)) ⬝ᵥ (star ((g.toU1 ^ 3 • φ)) ᵥ* star (g.toSU2.1)) := by
      rw [star_mulVec]
      rfl
    -- Reassociate so that `S` and `Sᴴ` meet, acting as `Sᴴ S` on the left vector:
    -- `(S y) ⬝ᵥ (xᴴ Sᴴ) = (Sᴴ S y) ⬝ᵥ xᴴ`.
    _ = ((star (g.toSU2.1) * g.toSU2.1) *ᵥ (g.toU1 ^ 3 • ψ)) ⬝ᵥ star ((g.toU1 ^ 3 • φ)) := by
      rw [dotProduct_comm, ← Matrix.dotProduct_mulVec, dotProduct_comm, mulVec_mulVec]
      rfl
    -- `S` is unitary, so `Sᴴ S = 1`; the `SU(2)` matrix cancels, leaving only the `U(1)` phase.
    _ = ((g.toU1 ^ 3 • ψ)) ⬝ᵥ star ((g.toU1 ^ 3 • φ)) := by
      rw [mem_unitaryGroup_iff'.mp (GaugeGroupI.toSU2 g).2.1]
      simp
    -- Pull the scalar phase out of the conjugation: `star (U³ • φ) = star U³ • star φ`,
    -- componentwise `conj (U³ * φ i) = conj U³ * conj (φ i)`.
    _ = ((g.toU1 ^ 3 • ψ)) ⬝ᵥ star (g.toU1 ^ 3) • star (φ.toFin2ℂ) := by
      congr
      ext i
      simp only [Pi.star_apply, RCLike.star_def, star_pow, Pi.smul_apply]
      change (starRingEnd ℂ) (GaugeGroupI.toU1 g ^ 3 * φ i) = _
      simp
      rfl
    -- Collect the two scalars: the phase `U³` from `ψ` and `star U³` from `star φ` multiply to
    -- `star U³ * U³ = 1` (as `|U³| = 1`), so they cancel, leaving `ψ ⬝ᵥ star φ = ⟪φ, ψ⟫`.
    _ = (ψ ⬝ᵥ star (φ.toFin2ℂ)) := by
      rw [dotProduct_smul, WithLp.ofLp_smul, smul_dotProduct, smul_smul, Unitary.star_mul_self,
        one_smul]

@[simp]
lemma gaugeGroupI_smul_norm (g : StandardModel.GaugeGroupI) (φ : HiggsVec) :
    ‖g • φ‖ = ‖φ‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ)]
  rw [gaugeGroupI_smul_inner]

/-!

### B.4. The gauge orbit of a Higgs vector

We show that two Higgs vectors are in the same gauge orbit if and only if they have the same norm.

-/

/-!

#### B.4.1. The rotation matrix to `ofReal`

We define an element of `GaugeGroupI` which takes a given Higgs vector to the
corresponding `ofReal` Higgs vector.

-/

/-- Given a Higgs vector, a rotation matrix which puts the second component of the
  vector to zero, and the first component to a real -/
def toRealGroupElem (φ : HiggsVec) : GaugeGroupI :=
  if hφ : φ = 0 then 1 else by
  have h0 : (‖φ‖^2 : ℝ) = φ 0 * (starRingEnd ℂ) (φ 0) + φ 1 * (starRingEnd ℂ) (φ 1) := by
    rw [← @real_inner_self_eq_norm_sq]
    simp only [Fin.isValue, mul_conj, PiLp.inner_apply, Complex.inner, ofReal_re,
      Fin.sum_univ_two, ofReal_add]
  have h0' : (‖φ‖^2 : ℂ) = φ 0 * (starRingEnd ℂ) (φ 0) + φ 1 * (starRingEnd ℂ) (φ 1) := by
    rw [← h0]
    simp
  refine ⟨1, ⟨!![conj (φ 0) / ‖φ‖, conj (φ 1) / ‖φ‖; -φ 1 /‖φ‖, φ 0 /‖φ‖;], ?_, ?_⟩, 1⟩
  /- Member of the unitary group. -/
  · simp only [Fin.isValue, SetLike.mem_coe]
    rw [mem_unitaryGroup_iff']
    funext i j
    rw [Matrix.mul_apply]
    simp only [Fin.isValue, star_apply, of_apply, cons_val', cons_val_fin_one, RCLike.star_def,
      Fin.sum_univ_two, cons_val_zero, cons_val_one]
    have hφ : Complex.ofReal ‖φ‖ ≠ 0 := ofReal_inj.mp.mt (norm_ne_zero_iff.mpr hφ)
    fin_cases i <;> fin_cases j <;>
    all_goals
    · simp
      field_simp
      rw [h0']
      ring
  /- Determinant equals zero. -/
  · have h1 : (‖φ‖ : ℂ) ≠ 0 := ofReal_inj.mp.mt (norm_ne_zero_iff.mpr hφ)
    simp [det_fin_two]
    field_simp
    rw [← ofReal_pow, ← @real_inner_self_eq_norm_sq,]
    simp only [Fin.isValue, mul_conj, PiLp.inner_apply, Complex.inner, ofReal_re,
      Fin.sum_univ_two, ofReal_add]
    rw [← mul_conj, ← mul_conj]
    ring

lemma toRealGroupElem_smul_self (φ : HiggsVec) :
    (toRealGroupElem φ) • φ = ofReal (‖φ‖ ^ 2) := by
  by_cases hφ : φ = 0
  · simp [hφ, toRealGroupElem]
    ext i
    fin_cases i <;> simp [ofReal]
  rw [gaugeGroupI_smul_eq]
  have h0 : (‖φ‖^2 : ℝ) = φ 0 * (starRingEnd ℂ) (φ 0) + φ 1 * (starRingEnd ℂ) (φ 1) := by
    rw [← @real_inner_self_eq_norm_sq]
    simp only [Fin.isValue, mul_conj, PiLp.inner_apply, Complex.inner, ofReal_re,
      Fin.sum_univ_two, ofReal_add]
  have h0' : (‖φ‖^2 : ℂ) = φ 0 * (starRingEnd ℂ) (φ 0) + φ 1 * (starRingEnd ℂ) (φ 1) := by
    rw [← h0]
    simp
  simp [toRealGroupElem, hφ]
  · simp [GaugeGroupI.toU1, GaugeGroupI.toSU2]
    ext i
    have hφ : Complex.ofReal ‖φ‖ ≠ 0 := ofReal_inj.mp.mt (norm_ne_zero_iff.mpr hφ)
    fin_cases i
    · simp [ofReal]
      field_simp
      rw [h0']
      ring_nf
      rfl
    · simp [ofReal]
      field_simp
      change -(φ 1 * φ 0) + φ 0 * φ 1= _
      ring

/-!

#### B.4.2. Members of orbits

Members of the orbit of a Higgs vector under the action of `GaugeGroupI` are exactly those
Higgs vectors with the same norm.

-/

lemma mem_orbit_gaugeGroupI_iff (φ : HiggsVec) (ψ : HiggsVec) :
    ψ ∈ MulAction.orbit GaugeGroupI φ ↔ ‖ψ‖ = ‖φ‖ := by
  constructor
  · intro h
    obtain ⟨g, rfl⟩ := h
    simp
  · intro h
    use (toRealGroupElem ψ)⁻¹ * toRealGroupElem (φ)
    simp only
    rw [← smul_smul, toRealGroupElem_smul_self φ, ← h, ← toRealGroupElem_smul_self ψ, smul_smul]
    simp


/-!

### B.5. To real scalars

-/

/-- The underlying real values of the Higgs vector. -/
def toRealScalars : HiggsVec →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun x := fun
    | 0 => (x 0).re
    | 1 => (x 0).im
    | 2 => (x 1).re
    | 3 => (x 1).im
  map_add' x y := by
    ext i
    fin_cases i <;> simp
  map_smul' a x := by
    ext i
    fin_cases i <;> simp

end HiggsVec

namespace HiggsField


/-- A general potential of the Higgs field. -/
abbrev EffectivePotential : Type := HiggsVec → ℝ

namespace EffectivePotential

/-!

## C. Invariance of the potential under the gauge group

-/

/-- The proposition that the general potential is invariant under
  the global action of the gauge group. -/
def IsInvariant (V : EffectivePotential) : Prop :=
  ∀ (g : GaugeGroupI), ∀ (φ : HiggsVec), V (g • φ) = V φ

namespace IsInvariant

/-- An invariant potential is equal on gauge orbits. -/
lemma eq_on_orbits {φ1 φ2 : HiggsVec} {V : EffectivePotential} (h : IsInvariant V)
    (hφ : φ1 ∈ MulAction.orbit GaugeGroupI  φ2) :
    V φ1 = V φ2 := by
  obtain ⟨g, hg⟩ := hφ
  rw [← hg]
  exact h g φ2

/-- An invariant potential is equal on Higgs vectors with identical norms. -/
lemma eq_of_norm_eq {φ1 φ2 : HiggsVec} {V : EffectivePotential} (h : IsInvariant V)
    (hφ : ‖φ1‖ = ‖φ2‖) :
    V φ1 = V φ2 := h.eq_on_orbits <| (HiggsVec.mem_orbit_gaugeGroupI_iff φ2 φ1).mpr hφ

end IsInvariant

/-!

## D. Maximum mass dimension

-/

/-- The proposition that the potential `V` has a maximum mass dimension
  less then or equal to `n` - also implying it is a polynomial. -/
def HasMaxMassDimLE (V : EffectivePotential) (n : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin 4) ℝ, (∀ φ : HiggsVec, V φ = p.eval φ.toRealScalars) ∧
    p.totalDegree ≤ n

/-- The polynomial associated to a potential `V` with a maximum mass dimension
  less than or equal to `n`. -/
def polynomial (V : EffectivePotential) {n : ℕ} (h : HasMaxMassDimLE V n) :
    MvPolynomial (Fin 4) ℝ := Classical.choose h

lemma polynomial_totalDegree {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n) :
    (polynomial V h).totalDegree ≤ n := (Classical.choose_spec h).2

lemma apply_eq_polynomial {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n)
    (φ : HiggsVec) : V φ = (polynomial V h).eval φ.toRealScalars := (Classical.choose_spec h).1 φ

/-!

## E. Terms of a given mass dimension

-/

/-- The part of a potential at a given mass-dimension. -/
def termOfMassDim (V : EffectivePotential) {n : ℕ} (h : HasMaxMassDimLE V n) (m : ℕ) :
    HiggsVec → ℝ := fun φ => ((polynomial V h).homogeneousComponent m).eval φ.toRealScalars

lemma termOfMassDim_eq_zero_of_max_lt {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n)
    {m : ℕ} (hm : n < m) (φ : HiggsVec) :
    termOfMassDim V h m φ = 0 := by
  simp only [termOfMassDim]
  rw [MvPolynomial.homogeneousComponent_eq_zero]
  simp only [map_zero]
  have h1 := polynomial_totalDegree h
  grind

lemma termOfMassDim_homogeneity {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n) (m : ℕ)
    (φ : HiggsVec) (t : ℝ) : termOfMassDim V h m (t • φ) = t ^ m * termOfMassDim V h m φ := by
  rw [termOfMassDim, termOfMassDim, map_smul, MvPolynomial.eval_eq', MvPolynomial.eval_eq',
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i, d i = m := by
    rw [MvPolynomial.support_homogeneousComponent, Finset.mem_filter] at hd
    rw [← Finsupp.degree_eq_sum]
    exact hd.2
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hdeg]
  ring

lemma apply_eq_sum_termOfMassDim {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n)
    (φ : HiggsVec) :
    V φ = ∑ m ∈ Finset.range (n + 1), termOfMassDim V h m φ := by
  rw [apply_eq_polynomial h, ← MvPolynomial.sum_homogeneousComponent (polynomial V h)]
  simp only [map_sum]
  change  ∑ x ∈ Finset.range ((V.polynomial h).totalDegree + 1), termOfMassDim V h x φ = _
  symm
  refine Finset.eventually_constant_sum ?_ ?_
  · intro m hm
    simp [termOfMassDim]
    rw [MvPolynomial.homogeneousComponent_eq_zero _ _ (by grind)]
    simp
  · have h1 := polynomial_totalDegree h
    grind

lemma apply_smul_eq_sum_termOfMassDim {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n)
    (φ : HiggsVec) (t : ℝ) :
    V (t • φ) = ∑ m ∈ Finset.range (n + 1), t ^ m * termOfMassDim V h m φ := by
  rw [apply_eq_sum_termOfMassDim h]
  congr
  funext m
  exact termOfMassDim_homogeneity h m φ t

lemma termOfMassDim_isInvariant {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n)
    (m : ℕ) (hV : IsInvariant V) : IsInvariant (termOfMassDim V h m) := by
  intro g φ
  have hV (t : ℝ) := hV g (t • φ)
  have h1 (t : ℝ) : ∑  m ∈ Finset.range (n + 1), t ^ m * (termOfMassDim V h m (g • φ) -
      termOfMassDim V h m φ) = 0 := by
    simp [mul_sub, ← apply_smul_eq_sum_termOfMassDim]
    rw [smul_comm, hV, sub_eq_zero]
  by_cases hmn : m ≤ n
  · have hp : (∑ k ∈ Finset.range (n + 1),
        Polynomial.C (termOfMassDim V h k (g • φ) - termOfMassDim V h k φ) * Polynomial.X ^ k)
          = 0 := by
      apply Polynomial.funext
      intro x
      simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero]
      rw [← h1 x]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hcoeff := congrArg (fun p => p.coeff m) hp
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff, hmn,
      if_true, Polynomial.coeff_zero] at hcoeff
    exact sub_eq_zero.mp hcoeff
  · rw [termOfMassDim_eq_zero_of_max_lt h (not_le.mp hmn),
      termOfMassDim_eq_zero_of_max_lt h (not_le.mp hmn)]

lemma termOfMassDim_eq_mul_norm {V : EffectivePotential} {n : ℕ}
    (h : HasMaxMassDimLE V n) (m : ℕ) (hV : IsInvariant V) (φ : HiggsVec) :
    ∃ c, termOfMassDim V h m φ = c * ‖φ‖ ^ m := by
  use termOfMassDim V h m !₂[1, 0]
  rw [(termOfMassDim_isInvariant h m hV).eq_of_norm_eq (φ2 := ‖φ‖ • !₂[1, 0])
    (by simp [PiLp.norm_eq_of_L2]), termOfMassDim_homogeneity h m !₂[1, 0] ‖φ‖]
  ring

lemma termOfMassDim_zero_of_odd {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n) (m : ℕ)
    (hV : IsInvariant V) (φ : HiggsVec) (hodd : Odd m)  :
    termOfMassDim V h m φ = 0 := by
  have h1 : termOfMassDim V h m φ  = termOfMassDim V h m ((-1 : ℝ) • φ) := by
    apply (termOfMassDim_isInvariant h m hV).eq_of_norm_eq
    simp
  rw [termOfMassDim_homogeneity h m φ (-1 : ℝ), hodd.neg_one_pow] at h1
  simp only [neg_mul, one_mul] at h1
  grind

/-!

## F. The potential in terms of the norm of the Higgs field

-/

lemma apply_eq_sum_even_termOfMassDim {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n)
    (hV : IsInvariant V) (φ : HiggsVec) :
    V φ = ∑ m ∈ Finset.range (n / 2 + 1), termOfMassDim V h (2 * m) φ := by
  rw [apply_eq_sum_termOfMassDim h, ← Finset.sum_filter_add_sum_filter_not
    (Finset.range (n + 1)) Even]
  have hodd : ∑ m ∈ (Finset.range (n + 1)).filter (fun m => ¬ Even m),
      termOfMassDim V h m φ = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    simp only [Finset.mem_filter] at hm
    exact termOfMassDim_zero_of_odd h m hV φ (Nat.not_even_iff_odd.mp hm.2)
  rw [hodd, add_zero]
  have hinj : ∀ x ∈ Finset.range (n / 2 + 1), ∀ y ∈ Finset.range (n / 2 + 1),
      2 * x = 2 * y → x = y := fun x _ y _ hxy => by omega
  have hset : (Finset.range (n / 2 + 1)).image (fun k => 2 * k)
      = (Finset.range (n + 1)).filter Even := by
    ext a
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_filter, Nat.even_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨by omega, by omega⟩
    · rintro ⟨ha, hae⟩
      exact ⟨a / 2, by omega, by omega⟩
  rw [← hset, Finset.sum_image hinj]

lemma apply_eq_sum_even_termOfMassDim_fin {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n)
    (hV : IsInvariant V) (φ : HiggsVec) :
    V φ = ∑ m : Fin (n/2 + 1), termOfMassDim V h (2 * m) φ := by
  rw [apply_eq_sum_even_termOfMassDim h hV φ, Finset.sum_range]

/-- The potential is equal to the sum of norms to even powers. -/
lemma apply_eq_sum_norm_pow {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n)
    (hV : IsInvariant V) (φ : HiggsVec) :
    ∃ c : Fin (n/2 + 1) → ℝ, V φ = ∑ m, c m • ‖φ‖ ^ (2 * m.1) := by
  use fun m' => Classical.choose (termOfMassDim_eq_mul_norm h (2 * m'.1) hV φ)
  rw [apply_eq_sum_even_termOfMassDim_fin h hV φ]
  congr 1
  ext m
  simpa using Classical.choose_spec (termOfMassDim_eq_mul_norm h (2 * m.1) hV φ)

end EffectivePotential

end HiggsField

end StandardModel
end
