/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.Grading.AxisBoosts
public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.MassDim
/-!
# Grading by boost weight

The jet algebra is graded by the boost weight along each spatial axis: `x` has boost weight `k`
along the `i`-th axis when `ρ(boostAxis i t) x = t ^ k • x` for every `t`. This is proved:
`boostWeightSubmodule_isInternal` decomposes the jet algebra as an internal direct sum of the
weight submodules, and `GradedAlgebra (boostWeightSubmodule i)` is an instance for each of the
three axes.

*It is not the hypercharge construction.* The gauge group acts on every generator by a
character, so `hyperchargePoly` can send each generator to `T ^ q` times itself. A boost does
not: it mixes the time index with the boost direction, so `∂_s B_μ` and `∂_s ψ_α` in the
coordinate basis are *not* boost eigenvectors — for the `z`-boost,
`ρ(boostZel t) F_{0x} = ch F_{0x} - sh F_{zx}`. Only the light-cone combinations are
homogeneous, so a `LaurentPolynomial`-valued grading map in the style of `Grading/Hypercharge`
would need a light-cone generating set. The grading is instead established as the family of
weight submodules, which needs no change of generators.

*How exhaustiveness is proved.* Independence is immediate: the weight spaces sit inside the
eigenspaces of a single boost at the distinct eigenvalues `2 ^ k`. Exhaustiveness descends to
the component spaces, where the boost acts *linearly* and the statement propagates mechanically
— the span of eigenvectors is closed under tensor products, products, symmetric and exterior
algebras, and base change (section B). The recursion bottoms out at four- and two-dimensional
spaces: for `Module.Dual ℝ Lorentz.CoVector`, `Module.Dual ℂ Lorentz.CoℂModule` and
`Module.Dual ℝ BBoson` the eigenvectors are the light-cone combinations `b₀ ∓ b₃`, of weight
`±2`, together with the transverse directions, of weight `0`; on the spinor duals the boost is
already diagonal, with weights `∓1`. No covariance of `jetDeriv` is needed anywhere.

*The three axes.* Everything is proved for the `z`-axis and transported. The axis boosts are
conjugate — a rotation by `π/2` carries the `z`-boost to the `x`- and `y`-boosts
(`boostXel_eq_conj`, `boostYel_eq_conj`) — so `isGraded_of_isGraded_two` moves the grading
between them without repeating the descent.

With this grading we can single out the subspace of boost weight zero. Any invariant under the
Lorentz group lies in it, for every axis, since a boost fixes an invariant.

The boost weight is bounded by the mass weight: a generator of mass weight `w` carries at most
`w` units of boost weight. A bosonic generator `∂_s B_μ` of mass weight `2(1 + |s|)` has
`1 + |s|` vector indices, each contributing at most `±2`; a fermionic generator `∂_s ψ_α` of
mass weight `3 + 2|s|` has `|s|` vector indices and one spinor index, contributing at most
`2|s| + 1`. So `|boost weight| ≤ mass weight` throughout. Odd weights do occur: a single fermion
sits at `±1`.

The maps `boostAvgX`, `boostAvgY`, `boostAvgZ` are these projections wherever the boost weights
that occur are among `0, ±2, ±4, ±6`: each acts on a weight-`k` element by the value at `k` of
the interpolating polynomial `boostAvgZWeight`, which is one at `k = 0` and vanishes at
`k = ±2, ±4, ±6`. On the covariant subalgebra in mass weight eight or less those are the only
weights that occur, so there each is exactly the projection onto boost weight zero. Note that
this is a statement about the *covariant* subalgebra, not about mass weight eight alone: the
mass-weight-eight element `∂_ρ ∂_σ ∂_τ B_μ` reaches boost weight `8`, and
`boostAvgZWeight_eight_ne_zero`.

## i. Overview

The weight submodules are defined by the eigenvector condition, so the multiplicative structure
is immediate: weights add under multiplication and the unit has weight zero. The work is
exhaustiveness, and it is done once for a general representation and then applied layer by
layer to the spaces the jet algebra is built from.

## ii. Key results

- `JetAlgebra.boostAxis` : the boost along a given spatial axis, and `boostXel_eq_conj`,
  `boostYel_eq_conj` exhibiting the three as conjugate.
- `JetAlgebra.BoostWeight.IsGraded` and the transport lemmas of section B : the grading
  propagates along tensor products, products, symmetric and exterior algebras, base change and
  conjugation.
- `JetAlgebra.boostWeightSubmodule` : the elements of a given boost weight along a given axis.
- `JetAlgebra.mul_mem_boostWeightSubmodule` : boost weights add under multiplication.
- `JetAlgebra.mem_boostWeightSubmodule_zero_of_isInvariant` : an invariant has boost weight zero.
- `JetAlgebra.boostWeightSubmodule_isInternal` : the weight submodules decompose the jet algebra
  as an internal direct sum, so `GradedAlgebra (boostWeightSubmodule i)` holds.
- `JetAlgebra.boostAvgAxis_apply_of_mem` : the boost average along an axis acts on a weight-`k`
  element by `boostAvgZWeight k`, hence is the identity on boost weight zero and annihilates
  weights `±2, ±4, ±6`.

## iii. Table of contents

- A. The boosts along the three axes
- B. Boost weights of a general representation
- C. The component spaces are boost-graded
- D. The boost-weight submodules
- E. Homogeneous elements
- F. Independence of the weight submodules
- G. The span of the homogeneous elements is a subalgebra
- H. The interpolating polynomial of the boost averages
- I. The boost averages are the projections onto boost weight zero
- J. The grading

-/

@[expose] public section

namespace LeptonGaugeSector
open TensorProduct StandardModel
open scoped minkowskiMatrix PauliMatrix
open Matrix MatrixGroups

namespace JetAlgebra

/-!

## A. The boosts along the three axes

The three axis boosts are conjugate: a rotation by `π/2` carries the `z`-boost to the `x`- and
`y`-boosts. Everything below is therefore proved for the `z`-axis and transported, rather than
repeated three times.

-/

/-- The boost along the `i`-th spatial axis. -/
noncomputable def boostAxis : Fin 3 → (t : ℝ) → t ≠ 0 → SL(2,ℂ)
  | 0, t, ht => boostXel t ht
  | 1, t, ht => boostYel t ht
  | 2, t, ht => boostZel t ht

@[simp] lemma boostAxis_zero (t : ℝ) (ht : t ≠ 0) : boostAxis 0 t ht = boostXel t ht := rfl
@[simp] lemma boostAxis_one (t : ℝ) (ht : t ≠ 0) : boostAxis 1 t ht = boostYel t ht := rfl
@[simp] lemma boostAxis_two (t : ℝ) (ht : t ≠ 0) : boostAxis 2 t ht = boostZel t ht := rfl

lemma boostAxis_inv (i : Fin 3) (t : ℝ) (ht : t ≠ 0) :
    (boostAxis i t ht)⁻¹ = boostAxis i t⁻¹ (inv_ne_zero ht) := by
  fin_cases i
  · exact boostXel_inv t ht
  · exact boostYel_inv t ht
  · exact boostZel_inv t ht

private lemma sqrtTwo_sq : (((Real.sqrt 2 : ℝ) : ℂ)) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

private lemma sqrtTwo_ne_zero : (((Real.sqrt 2 : ℝ) : ℂ)) ≠ 0 := by
  simp []

private lemma sqrtTwo_inv_mul :
    ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹) * ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹) = 2⁻¹ := by
  rw [← mul_inv, ← sq, sqrtTwo_sq]

/-- The rotation by `π/2` about the `y`-axis, carrying the `z`-boost to the `x`-boost. -/
noncomputable def rotZX : SL(2,ℂ) :=
  ⟨(((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • !![1, -1; 1, 1], by
    rw [Matrix.det_smul, Matrix.det_fin_two_of, Fintype.card_fin, inv_pow, sqrtTwo_sq]
    norm_num⟩

/-- The rotation by `π/2` about the `x`-axis, carrying the `z`-boost to the `y`-boost. -/
noncomputable def rotZY : SL(2,ℂ) :=
  ⟨(((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • !![1, Complex.I; Complex.I, 1], by
    rw [Matrix.det_smul, Matrix.det_fin_two_of, Fintype.card_fin, inv_pow, sqrtTwo_sq,
      Complex.I_mul_I]
    norm_num⟩

lemma boostXel_eq_conj (t : ℝ) (ht : t ≠ 0) :
    boostXel t ht = rotZX * boostZel t ht * rotZX⁻¹ := by
  have h0 := sqrtTwo_ne_zero
  have hc := sqrtTwo_inv_mul
  have htc : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [Matrix.SpecialLinearGroup.coe_mul, rotZX, boostZel, boostXel,
        Matrix.mul_apply, Fin.sum_univ_two]
      field_simp
      simp only [sqrtTwo_sq]
      try ring

lemma boostYel_eq_conj (t : ℝ) (ht : t ≠ 0) :
    boostYel t ht = rotZY * boostZel t ht * rotZY⁻¹ := by
  have h0 := sqrtTwo_ne_zero
  have hc := sqrtTwo_inv_mul
  have htc : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [Matrix.SpecialLinearGroup.coe_mul, rotZY, boostZel, boostYel,
        Matrix.mul_apply, Fin.sum_univ_two]
      field_simp
      simp only [sqrtTwo_sq, Complex.I_sq]
      try ring

/-- Every axis boost is a rotation of the `z`-boost. -/
lemma exists_conj_boostAxis (i : Fin 3) :
    ∃ R : SL(2,ℂ), ∀ (t : ℝ) (ht : t ≠ 0),
      boostAxis i t ht = R * boostAxis 2 t ht * R⁻¹ := by
  fin_cases i
  · exact ⟨rotZX, fun t ht => boostXel_eq_conj t ht⟩
  · exact ⟨rotZY, fun t ht => boostYel_eq_conj t ht⟩
  · exact ⟨1, fun t ht => by simp⟩

/-!

## B. Boost weights of a general representation

The descent to the component spaces is uniform, so it is carried out once here for an arbitrary
representation. The weight spaces are defined exactly as `boostWeightSubmodule` is, and
`IsGraded` says that they span. The point of the section is that `IsGraded` propagates along
every construction the jet algebra is built from: tensor products, products, symmetric algebras,
exterior algebras and base change. The recursion bottoms out at a finite-dimensional space with
an eigenbasis, where the light-cone combinations do the work.

-/

namespace BoostWeight

variable {K : Type*} [Field K] [Algebra ℝ K]
variable {M N V : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  [AddCommGroup V] [Module K V]
variable {i : Fin 3}

private lemma algebraMap_ne_zero {t : ℝ} (ht : t ≠ 0) : (algebraMap ℝ K t) ≠ 0 :=
  fun h => ht ((algebraMap ℝ K).injective (by simpa using h))

/-- The weight-`w` space of a representation: the vectors scaling by `t ^ w` under the
  `z`-boost at parameter `t`. -/
def space (rep : Representation K SL(2,ℂ) M) (i : Fin 3) (w : ℤ) : Submodule K M where
  carrier := {x | ∀ (t : ℝ) (ht : t ≠ 0),
    rep (boostAxis i t ht) x = (algebraMap ℝ K t) ^ w • x}
  add_mem' {a b} ha hb := fun t ht => by rw [map_add, ha t ht, hb t ht, smul_add]
  zero_mem' := fun t ht => by rw [map_zero, smul_zero]
  smul_mem' c x hx := fun t ht => by rw [map_smul, hx t ht, smul_comm]

lemma mem_space {rep : Representation K SL(2,ℂ) M} {i : Fin 3} {w : ℤ} {x : M} :
    x ∈ space rep i w ↔ ∀ (t : ℝ) (ht : t ≠ 0),
      rep (boostAxis i t ht) x = (algebraMap ℝ K t) ^ w • x := Iff.rfl

/-- The span of all the weight spaces. -/
def weightSpan (rep : Representation K SL(2,ℂ) M) (i : Fin 3) : Submodule K M :=
  ⨆ w, space rep i w

/-- A representation is boost-graded when its weight spaces span. -/
def IsGraded (rep : Representation K SL(2,ℂ) M) (i : Fin 3) : Prop := weightSpan rep i = ⊤

lemma mem_weightSpan_of_mem_space {rep : Representation K SL(2,ℂ) M} {w : ℤ} {x : M}
    (h : x ∈ space rep i w) : x ∈ weightSpan rep i :=
  Submodule.mem_iSup_of_mem w h

lemma mem_weightSpan_of_isGraded {rep : Representation K SL(2,ℂ) M} (h : IsGraded rep i) (x : M) :
    x ∈ weightSpan rep i := by rw [IsGraded] at h; rw [h]; trivial

lemma isGraded_iff_forall_mem {rep : Representation K SL(2,ℂ) M} :
    IsGraded rep i ↔ ∀ x, x ∈ weightSpan rep i :=
  ⟨mem_weightSpan_of_isGraded, fun h => eq_top_iff.mpr fun x _ => h x⟩

/-- A representation with a spanning family of vectors in the weight span is graded. -/
lemma isGraded_of_span {rep : Representation K SL(2,ℂ) M} {S : Set M}
    (hS : Submodule.span K S = ⊤) (h : ∀ x ∈ S, x ∈ weightSpan rep i) : IsGraded rep i :=
  eq_top_iff.mpr (hS ▸ Submodule.span_le.mpr h)

/-- A representation with a basis of vectors lying in the weight span is graded. -/
lemma isGraded_of_basis {ι : Type*} {rep : Representation K SL(2,ℂ) M} (b : Module.Basis ι K M)
    (h : ∀ n, b n ∈ weightSpan rep i) : IsGraded rep i :=
  isGraded_of_span b.span_eq (by rintro _ ⟨n, rfl⟩; exact h n)

/-!

### Tensor products

-/

lemma tmul_mem_space {rep : Representation K SL(2,ℂ) M} {rep₂ : Representation K SL(2,ℂ) N}
    {a b : ℤ} {x : M} {y : N} (hx : x ∈ space rep i a) (hy : y ∈ space rep₂ i b) :
    x ⊗ₜ[K] y ∈ space (rep.tprod rep₂) i (a + b) := by
  intro t ht
  show (TensorProduct.map _ _) _ = _
  rw [TensorProduct.map_tmul, hx t ht, hy t ht]
  simp only [TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_smul]
  rw [← zpow_add₀ (algebraMap_ne_zero (K := K) ht), add_comm b a]

lemma isGraded_tprod {rep : Representation K SL(2,ℂ) M} {rep₂ : Representation K SL(2,ℂ) N}
    (h₁ : IsGraded rep i) (h₂ : IsGraded rep₂ i) : IsGraded (rep.tprod rep₂) i := by
  refine isGraded_iff_forall_mem.mpr fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add u v hu hv => exact Submodule.add_mem _ hu hv
  | tmul x y =>
    have hx := mem_weightSpan_of_isGraded h₁ x
    have hy := mem_weightSpan_of_isGraded h₂ y
    induction hx using Submodule.iSup_induction' with
    | mem a x' hx' =>
      induction hy using Submodule.iSup_induction' with
      | mem b y' hy' => exact mem_weightSpan_of_mem_space (tmul_mem_space hx' hy')
      | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
      | add u v _ _ ihu ihv => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ ihu ihv
    | zero => rw [TensorProduct.zero_tmul]; exact Submodule.zero_mem _
    | add u v _ _ ihu ihv => rw [TensorProduct.add_tmul]; exact Submodule.add_mem _ ihu ihv


/-!

### Products

-/

lemma inl_mem_space {rep : Representation K SL(2,ℂ) M} {rep₂ : Representation K SL(2,ℂ) N}
    {a : ℤ} {x : M} (hx : x ∈ space rep i a) :
    ((x, 0) : M × N) ∈ space (rep.prod rep₂) i a := by
  intro t ht
  show ((rep _ x, rep₂ _ 0) : M × N) = _
  rw [map_zero, hx t ht, Prod.smul_mk, smul_zero]

lemma inr_mem_space {rep : Representation K SL(2,ℂ) M} {rep₂ : Representation K SL(2,ℂ) N}
    {a : ℤ} {y : N} (hy : y ∈ space rep₂ i a) :
    ((0, y) : M × N) ∈ space (rep.prod rep₂) i a := by
  intro t ht
  show ((rep _ 0, rep₂ _ y) : M × N) = _
  rw [map_zero, hy t ht, Prod.smul_mk, smul_zero]

lemma isGraded_prod {rep : Representation K SL(2,ℂ) M} {rep₂ : Representation K SL(2,ℂ) N}
    (h₁ : IsGraded rep i) (h₂ : IsGraded rep₂ i) : IsGraded (rep.prod rep₂) i := by
  have hleft : ∀ x : M, ((x, (0 : N))) ∈ weightSpan (rep.prod rep₂) i := by
    intro x
    have hx := mem_weightSpan_of_isGraded h₁ x
    induction hx using Submodule.iSup_induction' with
    | mem a u hu => exact mem_weightSpan_of_mem_space (inl_mem_space hu)
    | zero => exact Submodule.zero_mem _
    | add u v _ _ ihu ihv =>
      rw [show ((u + v, (0 : N))) = ((u, (0 : N))) + ((v, (0 : N))) from by ext <;> simp]
      exact Submodule.add_mem _ ihu ihv
  have hright : ∀ y : N, (((0 : M), y)) ∈ weightSpan (rep.prod rep₂) i := by
    intro y
    have hy := mem_weightSpan_of_isGraded h₂ y
    induction hy using Submodule.iSup_induction' with
    | mem a u hu => exact mem_weightSpan_of_mem_space (inr_mem_space hu)
    | zero => exact Submodule.zero_mem _
    | add u v _ _ ihu ihv =>
      rw [show (((0 : M), u + v)) = (((0 : M), u)) + (((0 : M), v)) from by ext <;> simp]
      exact Submodule.add_mem _ ihu ihv
  refine isGraded_iff_forall_mem.mpr fun z => ?_
  rw [show z = ((z.1, (0 : N))) + (((0 : M), z.2)) from by ext <;> simp]
  exact Submodule.add_mem _ (hleft z.1) (hright z.2)

/-!

### Algebras generated in degree one

-/

variable {A : Type*} [Ring A] [Algebra K A]

lemma one_mem_space {rep : Representation K SL(2,ℂ) A} (hone : ∀ Λ, rep Λ 1 = 1) :
    (1 : A) ∈ space rep i 0 := fun t _ => by rw [hone, zpow_zero, one_smul]

lemma mul_mem_space {rep : Representation K SL(2,ℂ) A}
    (hmul : ∀ (Λ : SL(2,ℂ)) (x y : A), rep Λ (x * y) = rep Λ x * rep Λ y)
    {a b : ℤ} {x y : A} (hx : x ∈ space rep i a) (hy : y ∈ space rep i b) :
    x * y ∈ space rep i (a + b) := by
  intro t ht
  rw [hmul, hx t ht, hy t ht, smul_mul_smul_comm,
    zpow_add₀ (algebraMap_ne_zero (K := K) ht)]

lemma mul_mem_weightSpan {rep : Representation K SL(2,ℂ) A}
    (hmul : ∀ (Λ : SL(2,ℂ)) (x y : A), rep Λ (x * y) = rep Λ x * rep Λ y)
    {x y : A} (hx : x ∈ weightSpan rep i) (hy : y ∈ weightSpan rep i) :
    x * y ∈ weightSpan rep i := by
  induction hx using Submodule.iSup_induction' with
  | mem a u hu =>
    induction hy using Submodule.iSup_induction' with
    | mem b v hv => exact mem_weightSpan_of_mem_space (mul_mem_space hmul hu hv)
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add v w _ _ ihv ihw => rw [mul_add]; exact Submodule.add_mem _ ihv ihw
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add u v _ _ ihu ihv => rw [add_mul]; exact Submodule.add_mem _ ihu ihv

lemma algebraMap_mem_weightSpan {rep : Representation K SL(2,ℂ) A}
    (hone : ∀ Λ, rep Λ 1 = 1) (r : K) : algebraMap K A r ∈ weightSpan rep i := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ _ (mem_weightSpan_of_mem_space (one_mem_space hone))

/-- A symmetric algebra is boost-graded as soon as its degree-one part is. -/
lemma isGraded_symmetricAlgebra {V : Type*} [AddCommGroup V] [Module K V]
    {repV : Representation K SL(2,ℂ) V}
    {repA : Representation K SL(2,ℂ) (SymmetricAlgebra K V)}
    (hone : ∀ Λ, repA Λ 1 = 1)
    (hmul : ∀ (Λ : SL(2,ℂ)) (x y : SymmetricAlgebra K V),
      repA Λ (x * y) = repA Λ x * repA Λ y)
    (hι : ∀ (Λ : SL(2,ℂ)) (x : V),
      repA Λ (SymmetricAlgebra.ι K V x) = SymmetricAlgebra.ι K V (repV Λ x))
    (hV : IsGraded repV i) : IsGraded repA i := by
  refine isGraded_iff_forall_mem.mpr fun x => ?_
  induction x using SymmetricAlgebra.induction with
  | algebraMap r => exact algebraMap_mem_weightSpan hone r
  | ι v =>
    have hv := mem_weightSpan_of_isGraded hV v
    induction hv using Submodule.iSup_induction' with
    | mem a u hu =>
      refine mem_weightSpan_of_mem_space (w := a) fun t ht => ?_
      rw [hι, hu t ht, map_smul]
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add u v _ _ ihu ihv => rw [map_add]; exact Submodule.add_mem _ ihu ihv
  | mul u v ihu ihv => exact mul_mem_weightSpan hmul ihu ihv
  | add u v ihu ihv => exact Submodule.add_mem _ ihu ihv

/-- An exterior algebra is boost-graded as soon as its degree-one part is. -/
lemma isGraded_exteriorAlgebra {V : Type*} [AddCommGroup V] [Module K V]
    {repV : Representation K SL(2,ℂ) V}
    {repA : Representation K SL(2,ℂ) (ExteriorAlgebra K V)}
    (hone : ∀ Λ, repA Λ 1 = 1)
    (hmul : ∀ (Λ : SL(2,ℂ)) (x y : ExteriorAlgebra K V),
      repA Λ (x * y) = repA Λ x * repA Λ y)
    (hι : ∀ (Λ : SL(2,ℂ)) (x : V),
      repA Λ (ExteriorAlgebra.ι K x) = ExteriorAlgebra.ι K (repV Λ x))
    (hV : IsGraded repV i) : IsGraded repA i := by
  refine isGraded_iff_forall_mem.mpr fun x => ?_
  induction x using ExteriorAlgebra.induction with
  | algebraMap r => exact algebraMap_mem_weightSpan hone r
  | ι v =>
    have hv := mem_weightSpan_of_isGraded hV v
    induction hv using Submodule.iSup_induction' with
    | mem a u hu =>
      refine mem_weightSpan_of_mem_space (w := a) fun t ht => ?_
      rw [hι, hu t ht, map_smul]
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add u v _ _ ihu ihv => rw [map_add]; exact Submodule.add_mem _ ihu ihv
  | mul u v ihu ihv => exact mul_mem_weightSpan hmul ihu ihv
  | add u v ihu ihv => exact Submodule.add_mem _ ihu ihv

/-!

### The light-cone eigenbasis of a spacetime-indexed space

-/

/-- A space with a basis indexed by spacetime directions transforming by the columns of the
  Lorentz matrix is boost-graded: the light-cone combinations `b₀ ∓ b₃` are eigenvectors of
  weight `±2` and the transverse directions are invariant. -/
lemma isGraded_of_lorentzColumns {rep : Representation K SL(2,ℂ) M}
    (b : Module.Basis (Fin 1 ⊕ Fin 3) K M)
    (h : ∀ (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3), rep Λ (b μ) =
      ∑ j, algebraMap ℝ K ((Lorentz.SL2C.toLorentzGroup Λ).1 j μ) • b j) :
    IsGraded rep 2 := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℝ K).injective
  have key : ∀ (t : ℝ) (ht : t ≠ 0) (μ : Fin 1 ⊕ Fin 3),
      rep (boostAxis 2 t ht) (b μ) =
        ∑ j, algebraMap ℝ K (boostMatZ t j μ) • b j := by
    intro t ht μ
    rw [h]
    exact Finset.sum_congr rfl fun j _ => by
      rw [show boostAxis 2 t ht = boostZel t ht from rfl, toLorentzGroup_boostZel]
  have hplus : b (Sum.inl 0) - b (Sum.inr 2) ∈ space rep 2 2 := by
    intro t ht
    have h0 : (algebraMap ℝ K t) ≠ 0 := algebraMap_ne_zero ht
    rw [map_sub, key t ht, key t ht]
    simp only [Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, boostMatZ,
      map_zero, zero_smul, add_zero, zero_add, map_div₀, map_sub,
      map_add, map_pow, map_inv₀, map_ofNat, map_neg]
    match_scalars <;> (field_simp; try ring_nf; try norm_num)
  have hminus : b (Sum.inl 0) + b (Sum.inr 2) ∈ space rep 2 (-2) := by
    intro t ht
    have h0 : (algebraMap ℝ K t) ≠ 0 := algebraMap_ne_zero ht
    rw [map_add, key t ht, key t ht]
    simp only [Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, boostMatZ,
      map_zero, zero_smul, add_zero, zero_add, map_div₀, map_sub,
      map_add, map_pow, map_inv₀, map_ofNat, map_neg]
    match_scalars <;> (field_simp; try ring_nf; try norm_num)
  have htr : ∀ i' : Fin 3, i' = 0 ∨ i' = 1 → b (Sum.inr i') ∈ space rep 2 0 := by
    rintro i (rfl | rfl) <;>
    · intro t ht
      rw [key t ht]
      simp only [Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, boostMatZ,
        map_zero, zero_smul, add_zero, zero_add, map_one, one_smul, zpow_zero]
  refine isGraded_of_basis b fun μ => ?_
  match μ with
  | Sum.inl 0 =>
    rw [show b (Sum.inl 0) = (2⁻¹ : K) • ((b (Sum.inl 0) - b (Sum.inr 2))
        + (b (Sum.inl 0) + b (Sum.inr 2))) from by match_scalars <;> (field_simp; try ring)]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _
      (mem_weightSpan_of_mem_space hplus) (mem_weightSpan_of_mem_space hminus))
  | Sum.inr 0 => exact mem_weightSpan_of_mem_space (htr 0 (Or.inl rfl))
  | Sum.inr 1 => exact mem_weightSpan_of_mem_space (htr 1 (Or.inr rfl))
  | Sum.inr 2 =>
    rw [show b (Sum.inr 2) = (2⁻¹ : K) • ((b (Sum.inl 0) + b (Sum.inr 2))
        - (b (Sum.inl 0) - b (Sum.inr 2))) from by match_scalars <;> (field_simp; try ring)]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _
      (mem_weightSpan_of_mem_space hminus) (mem_weightSpan_of_mem_space hplus))

/-!

### Base change from the real to the complex scalars

-/

lemma isGraded_baseChange {A : Type*} [AddCommGroup A] [Module ℝ A]
    {repR : Representation ℝ SL(2,ℂ) A} {repC : Representation ℂ SL(2,ℂ) (ℂ ⊗[ℝ] A)}
    (h : ∀ (Λ : SL(2,ℂ)) (c : ℂ) (y : A), repC Λ (c ⊗ₜ[ℝ] y) = c ⊗ₜ[ℝ] repR Λ y)
    (hR : IsGraded repR i) : IsGraded repC i := by
  have htmul : ∀ (c : ℂ) (w : ℤ) (y : A), y ∈ space repR i w →
      (c ⊗ₜ[ℝ] y : ℂ ⊗[ℝ] A) ∈ space repC i w := by
    intro c w y hy t ht
    rw [h, hy t ht, TensorProduct.tmul_smul,
      show ((algebraMap ℝ ℝ) t) ^ w = t ^ w from by simp,
      ← algebraMap_smul (R := ℝ) ℂ (t ^ w) (c ⊗ₜ[ℝ] y), map_zpow₀]
  refine isGraded_iff_forall_mem.mpr fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add u v hu hv => exact Submodule.add_mem _ hu hv
  | tmul c y =>
    have hy := mem_weightSpan_of_isGraded hR y
    induction hy using Submodule.iSup_induction' with
    | mem w u hu => exact mem_weightSpan_of_mem_space (htmul c w u hu)
    | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
    | add u v _ _ ihu ihv => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ ihu ihv


/-!

### Transport between the three axes

-/

/-- The axis boosts are conjugate, so being graded for one of them is being graded for all. -/
lemma isGraded_of_isGraded_two {rep : Representation K SL(2,ℂ) M} (h : IsGraded rep 2)
    (i : Fin 3) : IsGraded rep i := by
  obtain ⟨R, hR⟩ := exists_conj_boostAxis i
  have hsurj : ∀ x : M, rep R (rep R⁻¹ x) = x := by
    intro x
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hmap : ∀ (w : ℤ) (u : M), u ∈ space rep 2 w → rep R u ∈ space rep i w := by
    intro w u hu t ht
    rw [← Module.End.mul_apply, ← map_mul, hR t ht, inv_mul_cancel_right, map_mul,
      Module.End.mul_apply, hu t ht, map_smul]
  refine isGraded_iff_forall_mem.mpr fun x => ?_
  obtain ⟨y, rfl⟩ : ∃ y, rep R y = x := ⟨rep R⁻¹ x, hsurj x⟩
  have hy := mem_weightSpan_of_isGraded h y
  induction hy using Submodule.iSup_induction' with
  | mem w u hu => exact mem_weightSpan_of_mem_space (hmap w u hu)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u v _ _ ihu ihv => rw [map_add]; exact Submodule.add_mem _ ihu ihv

end BoostWeight

/-!

## C. The component spaces are boost-graded

Each layer of the jet algebra is graded once the layer below it is: the two four-dimensional
derivative and target spaces by `isGraded_of_lorentzColumns`, the spinor duals directly (the
boost is already diagonal on them), and everything above by the tensor, product, symmetric- and
exterior-algebra transports.

-/

open BoostWeight in
/-- The real dual covectors — the derivative slots — are boost-graded. -/
lemma isGraded_coVectorDual : IsGraded (Lorentz.CoVector.sl2Rep.dual) 2 :=
  isGraded_of_lorentzColumns Lorentz.CoVector.basis.dualBasis fun Λ μ => by
    simpa using Lorentz.CoVector.sl2Rep_dual_dualBasis Λ μ

open BoostWeight in
/-- The complex dual covectors are boost-graded. -/
lemma isGraded_coℂModuleDual : IsGraded (Lorentz.CoℂModule.SL2CRep.dual) 2 :=
  isGraded_of_lorentzColumns Lorentz.complexCoBasis.dualBasis fun Λ μ => by
    simpa using Lorentz.CoℂModule.SL2CRep_dual_dualBasis Λ μ

open BoostWeight in
/-- The dual B-boson target space is boost-graded. -/
lemma isGraded_bBosonDual : IsGraded (BBoson.repLorentzGroup.dual) 2 :=
  isGraded_of_lorentzColumns BBoson.basis.dualBasis fun Λ μ => by
    simpa using BBoson.repLorentzGroup_dual_dualBasis Λ μ

open BoostWeight in
/-- The real algebra of derivative symbols is boost-graded. -/
lemma isGraded_derivAlgebraReal : IsGraded (DerivAlgebraReal.repLorentzGroup) 2 :=
  isGraded_symmetricAlgebra (repV := Lorentz.CoVector.sl2Rep.dual)
    (fun Λ => by
      show (SymmetricAlgebra.lift
        (SymmetricAlgebra.ι ℝ _ ∘ₗ Lorentz.CoVector.sl2Rep.dual Λ)) 1 = 1
      exact map_one _)
    (fun Λ x y => by
      show (SymmetricAlgebra.lift
        (SymmetricAlgebra.ι ℝ _ ∘ₗ Lorentz.CoVector.sl2Rep.dual Λ)) (x * y) = _
      exact map_mul _ _ _)
    (fun Λ x => DerivAlgebraReal.repLorentzGroup_apply_ι Λ x)
    isGraded_coVectorDual

open BoostWeight in
/-- The complex algebra of derivative symbols is boost-graded. -/
lemma isGraded_derivAlgebraComplex : IsGraded (DerivAlgebraComplex.repLorentzGroup) 2 :=
  isGraded_symmetricAlgebra (repV := Lorentz.CoℂModule.SL2CRep.dual)
    (fun Λ => DerivAlgebraComplex.repLorentzGroup_apply_one Λ)
    (fun Λ x y => DerivAlgebraComplex.repLorentzGroup_apply_mul Λ x y)
    (fun Λ x => DerivAlgebraComplex.repLorentzGroup_apply_ι Λ x)
    isGraded_coℂModuleDual

open BoostWeight in
/-- The B-boson jet component space is boost-graded. -/
lemma isGraded_bBosonJetComponentSpace :
    IsGraded (BBoson.JetComponentSpace.repLorentzGroup) 2 :=
  isGraded_tprod isGraded_derivAlgebraReal isGraded_bBosonDual

open BoostWeight in
/-- The B-boson jet algebra is boost-graded. -/
lemma isGraded_bBosonJetAlgebra : IsGraded (BBoson.JetAlgebra.repLorentzGroup) 2 :=
  isGraded_symmetricAlgebra (repV := BBoson.JetComponentSpace.repLorentzGroup)
    (fun Λ => by
      show (SymmetricAlgebra.lift
        (SymmetricAlgebra.ι ℝ _ ∘ₗ BBoson.JetComponentSpace.repLorentzGroup Λ)) 1 = 1
      exact map_one _)
    (fun Λ x y => by
      show (SymmetricAlgebra.lift
        (SymmetricAlgebra.ι ℝ _ ∘ₗ BBoson.JetComponentSpace.repLorentzGroup Λ)) (x * y) = _
      exact map_mul _ _ _)
    (fun Λ x => BBoson.JetAlgebra.repLorentzGroup_apply_ι Λ x)
    isGraded_bBosonJetComponentSpace

open BoostWeight in
/-- The complexified B-boson jet algebra is boost-graded. -/
lemma isGraded_complexBBosonJetAlgebra :
    IsGraded (BBoson.JetAlgebra.complexRepLorentzGroup) 2 :=
  isGraded_baseChange (fun _ _ _ => rfl) isGraded_bBosonJetAlgebra


open BoostWeight in
/-- The dual charged-lepton spinors are boost-graded: the boost is already diagonal on them,
  with weights `∓1`. -/
lemma isGraded_leptonSingletDual : IsGraded (LeptonSinglet.repLorentzGroup.dual) 2 := by
  refine isGraded_of_basis LeptonSinglet.basis.dualBasis fun α => ?_
  match α with
  | 0 =>
    refine mem_weightSpan_of_mem_space (w := -1) fun t ht => ?_
    rw [show boostAxis 2 t ht = boostZel t ht from rfl,
      LeptonSinglet.repLorentzGroup_dual_dualBasis, boostZel_inv_coe]
    simp only [Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply,
      Fin.isValue, Complex.star_def, map_zero, zero_smul, add_zero,
      Complex.conj_ofReal]
    rw [_root_.zpow_neg, zpow_one, Complex.ofReal_inv]
    rfl
  | 1 =>
    refine mem_weightSpan_of_mem_space (w := 1) fun t ht => ?_
    rw [show boostAxis 2 t ht = boostZel t ht from rfl,
      LeptonSinglet.repLorentzGroup_dual_dualBasis, boostZel_inv_coe]
    simp only [Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply,
      Fin.isValue, Complex.star_def, map_zero, zero_smul, zero_add,
      Complex.conj_ofReal]
    rw [zpow_one]
    rfl

open BoostWeight in
/-- The dual conjugate charged-lepton spinors are boost-graded. -/
lemma isGraded_leptonSingletConjDual : IsGraded (LeptonSinglet.repLorentzGroup.conj.dual) 2 := by
  refine isGraded_of_basis LeptonSinglet.basis.conj.dualBasis fun α => ?_
  match α with
  | 0 =>
    refine mem_weightSpan_of_mem_space (w := -1) fun t ht => ?_
    rw [show boostAxis 2 t ht = boostZel t ht from rfl,
      LeptonSinglet.repLorentzGroup_conj_dual_dualBasis, boostZel_inv_coe]
    simp only [Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply,
      Fin.isValue, zero_smul, add_zero]
    rw [_root_.zpow_neg, zpow_one, Complex.ofReal_inv]
    rfl
  | 1 =>
    refine mem_weightSpan_of_mem_space (w := 1) fun t ht => ?_
    rw [show boostAxis 2 t ht = boostZel t ht from rfl,
      LeptonSinglet.repLorentzGroup_conj_dual_dualBasis, boostZel_inv_coe]
    simp only [Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply,
      Fin.isValue, zero_smul, zero_add]
    rw [zpow_one]
    rfl

open BoostWeight in
/-- The charged-lepton jet component space is boost-graded. -/
lemma isGraded_leptonJetComponentSpace :
    IsGraded (LeptonSinglet.JetComponentSpace.repLorentzGroup) 2 :=
  isGraded_prod (isGraded_tprod isGraded_derivAlgebraComplex isGraded_leptonSingletDual)
    (isGraded_tprod isGraded_derivAlgebraComplex isGraded_leptonSingletConjDual)

open BoostWeight in
/-- The charged-lepton jet algebra is boost-graded. -/
lemma isGraded_leptonJetAlgebra : IsGraded (LeptonSinglet.JetAlgebra.repLorentzGroup) 2 :=
  isGraded_exteriorAlgebra (repV := LeptonSinglet.JetComponentSpace.repLorentzGroup)
    (fun Λ => by
      show (ExteriorAlgebra.map (LeptonSinglet.JetComponentSpace.repLorentzGroup Λ)) 1 = 1
      exact map_one _)
    (fun Λ x y => by
      show (ExteriorAlgebra.map (LeptonSinglet.JetComponentSpace.repLorentzGroup Λ)) (x * y) = _
      exact map_mul _ _ _)
    (fun Λ x => by
      show (ExteriorAlgebra.map (LeptonSinglet.JetComponentSpace.repLorentzGroup Λ))
        (ExteriorAlgebra.ι ℂ x) = _
      exact ExteriorAlgebra.map_apply_ι _ _)
    isGraded_leptonJetComponentSpace

open BoostWeight in
/-- The lepton–gauge-sector jet algebra is boost-graded. -/
lemma isGraded_jetAlgebra : IsGraded (repLorentzGroup) 2 :=
  isGraded_tprod isGraded_complexBBosonJetAlgebra isGraded_leptonJetAlgebra

/-!

## D. The boost-weight submodules

-/

variable {i : Fin 3}

/-- The scalar action of a real parameter on the jet algebra, in the form the weight condition
  presents it. -/
private lemma algebraMap_real_complex (t : ℝ) : (algebraMap ℝ ℂ) t = ((t : ℝ) : ℂ) := rfl

/-- The submodule of elements of boost weight `k` along the `i`-th spatial axis: those scaling
  by `t ^ k` under the boost with parameter `t`. -/
noncomputable def boostWeightSubmodule (i : Fin 3) (k : ℤ) : Submodule ℂ JetAlgebra :=
  BoostWeight.space repLorentzGroup i k

lemma mem_boostWeightSubmodule {k : ℤ} {x : JetAlgebra} :
    x ∈ boostWeightSubmodule i k ↔ ∀ (t : ℝ) (ht : t ≠ 0),
      repLorentzGroup (boostAxis i t ht) x = (((t : ℝ) : ℂ) ^ k) • x := Iff.rfl

/-- The unit has boost weight zero. -/
lemma one_mem_boostWeightSubmodule : (1 : JetAlgebra) ∈ boostWeightSubmodule i 0 :=
  BoostWeight.one_mem_space repLorentzGroup_apply_one

/-- Boost weights add under multiplication. -/
lemma mul_mem_boostWeightSubmodule {k l : ℤ} {x y : JetAlgebra}
    (hx : x ∈ boostWeightSubmodule i k) (hy : y ∈ boostWeightSubmodule i l) :
    x * y ∈ boostWeightSubmodule i (k + l) :=
  BoostWeight.mul_mem_space repLorentzGroup_apply_mul hx hy

instance : SetLike.GradedMonoid (boostWeightSubmodule i) where
  one_mem := one_mem_boostWeightSubmodule
  mul_mem _ _ _ _ hx hy := mul_mem_boostWeightSubmodule hx hy

/-- A Lorentz-invariant element has boost weight zero, along every axis. -/
lemma mem_boostWeightSubmodule_zero_of_isInvariant {x : JetAlgebra} (hx : IsInvariant x) :
    x ∈ boostWeightSubmodule i 0 :=
  fun t ht => by rw [hx.2 (boostAxis i t ht), zpow_zero, one_smul]

/-!

## E. Homogeneous elements

The coordinate components of a field strength are not boost eigenvectors; the light-cone
combinations are. The two components with both indices transverse to the boost — `F_{xy}` — and
the one along it — `F_{0z}` — are invariant.

-/

/-- The light-cone combination `F_{0x} - F_{zx}` has boost weight `2`. -/
lemma fieldStrengthDeriv_lightCone_mem_two :
    fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) -
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) ∈ boostWeightSubmodule 2 2 := by
  intro t ht
  simp only [algebraMap_real_complex]
  have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [map_sub, repLorentzGroup_fieldStrengthDeriv_nil, repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [boostAxis_two, toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ, fieldStrengthDeriv_self,
    mul_zero, mul_one, Complex.ofReal_zero,
    zero_smul, smul_zero, add_zero, zero_add]
  push_cast
  match_scalars <;> (field_simp; ring)

/-- The light-cone combination `F_{0x} + F_{zx}` has boost weight `-2`. -/
lemma fieldStrengthDeriv_lightCone_mem_neg_two :
    fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) +
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) ∈ boostWeightSubmodule 2 (-2) := by
  intro t ht
  simp only [algebraMap_real_complex]
  have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [map_add, repLorentzGroup_fieldStrengthDeriv_nil, repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [boostAxis_two, toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ, fieldStrengthDeriv_self,
    mul_zero, mul_one, Complex.ofReal_zero,
    zero_smul, smul_zero, add_zero, zero_add]
  push_cast
  match_scalars <;> (field_simp; ring)

/-- The transverse component `F_{xy}` has boost weight zero. -/
lemma fieldStrengthDeriv_transverse_mem_zero :
    fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) ∈ boostWeightSubmodule 2 0 := by
  intro t ht
  simp only [algebraMap_real_complex]
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [boostAxis_two, toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ, fieldStrengthDeriv_self,
    mul_zero, mul_one, Complex.ofReal_zero, Complex.ofReal_one,
    zero_smul, smul_zero, add_zero, zero_add]
  match_scalars; norm_num

/-- The zeroth-order lepton coordinate `ψ_0` has boost weight `-1`. -/
lemma Dψ_nil_zero_mem_neg_one : Dψ [] 0 ∈ boostWeightSubmodule 2 (-1) := by
  intro t ht
  simp only [algebraMap_real_complex]
  rw [boostAxis_two, repLorentzGroup_Dψ_nil, boostZel_inv_coe]
  simp only [Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply,
    Fin.isValue, Complex.star_def, map_zero, zero_smul, add_zero,
    Complex.conj_ofReal]
  rw [_root_.zpow_neg, zpow_one, Complex.ofReal_inv]

/-- The zeroth-order lepton coordinate `ψ_1` has boost weight `1`. -/
lemma Dψ_nil_one_mem_one : Dψ [] 1 ∈ boostWeightSubmodule 2 1 := by
  intro t ht
  simp only [algebraMap_real_complex]
  rw [boostAxis_two, repLorentzGroup_Dψ_nil, boostZel_inv_coe]
  simp only [Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply,
    Fin.isValue, Complex.star_def, map_zero, zero_smul, zero_add,
    Complex.conj_ofReal]
  rw [zpow_one]

/-- The zeroth-order conjugate lepton coordinate `ψ̄_0` has boost weight `-1`. -/
lemma Dbarψ_nil_zero_mem_neg_one : Dbarψ [] 0 ∈ boostWeightSubmodule 2 (-1) := by
  intro t ht
  simp only [algebraMap_real_complex]
  rw [boostAxis_two, repLorentzGroup_Dbarψ_nil, boostZel_inv_coe]
  simp only [Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply,
    Fin.isValue, zero_smul, add_zero]
  rw [_root_.zpow_neg, zpow_one, Complex.ofReal_inv]

/-- The zeroth-order conjugate lepton coordinate `ψ̄_1` has boost weight `1`. -/
lemma Dbarψ_nil_one_mem_one : Dbarψ [] 1 ∈ boostWeightSubmodule 2 1 := by
  intro t ht
  simp only [algebraMap_real_complex]
  rw [boostAxis_two, repLorentzGroup_Dbarψ_nil, boostZel_inv_coe]
  simp only [Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply,
    Fin.isValue, zero_smul, zero_add]
  rw [zpow_one]

/-- The gauge potential in the light-cone direction, `B_0 - B_z`, has boost weight `2`. -/
lemma B_lightCone_mem_two :
    [JetGenerators.dB {} (Sum.inl 0)]ₐ - [JetGenerators.dB {} (Sum.inr 2)]ₐ ∈
      boostWeightSubmodule 2 2 := by
  intro t ht
  simp only [algebraMap_real_complex]
  have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [map_sub, repLorentzGroup_B, repLorentzGroup_B]
  simp only [boostAxis_two, toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ, Complex.ofReal_zero,
    zero_smul, add_zero, zero_add]
  push_cast
  match_scalars <;> (field_simp; ring)

/-- The gauge potential in the other light-cone direction has boost weight `-2`. -/
lemma B_lightCone_mem_neg_two :
    [JetGenerators.dB {} (Sum.inl 0)]ₐ + [JetGenerators.dB {} (Sum.inr 2)]ₐ ∈
      boostWeightSubmodule 2 (-2) := by
  intro t ht
  simp only [algebraMap_real_complex]
  have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [map_add, repLorentzGroup_B, repLorentzGroup_B]
  simp only [boostAxis_two, toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ, Complex.ofReal_zero,
    zero_smul, add_zero, zero_add]
  push_cast
  match_scalars <;> (field_simp; ring)

/-!

## F. Independence of the weight submodules

The weight submodules sit inside the eigenspaces of a single boost, `ρ(boostZel 2)`, at the
pairwise distinct eigenvalues `2 ^ k`. Eigenspaces at distinct eigenvalues are independent, so
the family is independent: an element has at most one decomposition into homogeneous parts.
This is one of the two halves of `DirectSum.IsInternal`; the other, that the weight submodules
span, is section C.

-/

/-- The weight submodule of weight `k` sits inside the `2 ^ k` eigenspace of the boost at
  parameter two. -/
lemma boostWeightSubmodule_le_eigenspace (k : ℤ) :
    boostWeightSubmodule i k ≤
      Module.End.eigenspace (repLorentzGroup (boostAxis i 2 two_ne_zero)) ((2 : ℂ) ^ k) := by
  intro x hx
  rw [Module.End.mem_eigenspace_iff]
  have h := hx 2 two_ne_zero
  norm_num at h ⊢
  exact h

private lemma zpow_two_injective : Function.Injective (fun k : ℤ => ((2 : ℂ) ^ k)) := by
  have hcast : ∀ k : ℤ, ((2 : ℂ) ^ k) = (((2 : ℝ) ^ k : ℝ) : ℂ) := by
    intro k
    rw [Complex.ofReal_zpow]
    norm_num
  intro a b hab
  simp only [hcast] at hab
  exact zpow_right_injective₀ (by norm_num) (by norm_num) (Complex.ofReal_injective hab)

/-- The boost-weight submodules are independent: a decomposition into homogeneous parts is
  unique when it exists. -/
lemma boostWeightSubmodule_iSupIndep : iSupIndep (boostWeightSubmodule i) :=
  ((Module.End.eigenspaces_iSupIndep
      (repLorentzGroup (boostAxis i 2 two_ne_zero) : Module.End ℂ JetAlgebra)).comp
    zpow_two_injective).mono boostWeightSubmodule_le_eigenspace

/-!

## G. The span of the homogeneous elements is a subalgebra

-/

/-- The span of the homogeneous elements contains one. -/
lemma one_mem_iSup_boostWeightSubmodule :
    (1 : JetAlgebra) ∈ ⨆ k, boostWeightSubmodule i k :=
  Submodule.mem_iSup_of_mem 0 one_mem_boostWeightSubmodule

/-- The span of the homogeneous elements is closed under multiplication. -/
lemma mul_mem_iSup_boostWeightSubmodule {x y : JetAlgebra}
    (hx : x ∈ ⨆ k, boostWeightSubmodule i k) (hy : y ∈ ⨆ k, boostWeightSubmodule i k) :
    x * y ∈ ⨆ k, boostWeightSubmodule i k := by
  induction hx using Submodule.iSup_induction' with
  | mem k a ha =>
    induction hy using Submodule.iSup_induction' with
    | mem l b hb =>
      exact Submodule.mem_iSup_of_mem (k + l) (mul_mem_boostWeightSubmodule ha hb)
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add b c _ _ ihb ihc => rw [mul_add]; exact Submodule.add_mem _ ihb ihc
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add a b _ _ iha ihb => rw [add_mul]; exact Submodule.add_mem _ iha ihb

/-- The homogeneous elements span a subalgebra of the jet algebra. -/
noncomputable def boostWeightSubalgebra (i : Fin 3) : Subalgebra ℂ JetAlgebra :=
  Submodule.toSubalgebra (⨆ k, boostWeightSubmodule i k) one_mem_iSup_boostWeightSubmodule
    fun _ _ hx hy => mul_mem_iSup_boostWeightSubmodule hx hy

@[simp]
lemma mem_boostWeightSubalgebra {x : JetAlgebra} :
    x ∈ boostWeightSubalgebra i ↔ x ∈ ⨆ k, boostWeightSubmodule i k := Iff.rfl

/-- The homogeneous span contains the whole bosonic factor once it contains the generators. -/
private lemma inclB_mem_boostWeightSubalgebra
    (h : ∀ j : JetGenerators, [j]ₐ ∈ boostWeightSubalgebra i)
    (a : ℂ ⊗[ℝ] BBoson.JetAlgebra) : inclB a ∈ boostWeightSubalgebra i := by
  have hone : ∀ c : BBoson.JetAlgebra,
      inclB ((1 : ℂ) ⊗ₜ[ℝ] c) ∈ boostWeightSubalgebra i := by
    intro c
    induction c using SymmetricAlgebra.induction with
    | algebraMap r =>
      rw [show ((1 : ℂ) ⊗ₜ[ℝ] (algebraMap ℝ BBoson.JetAlgebra r) :
            ℂ ⊗[ℝ] BBoson.JetAlgebra) =
          algebraMap ℂ (ℂ ⊗[ℝ] BBoson.JetAlgebra) (algebraMap ℝ ℂ r) from by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
          TensorProduct.tmul_smul, TensorProduct.smul_tmul']
        rfl, AlgHom.commutes]
      exact Subalgebra.algebraMap_mem _ _
    | ι v =>
      have hv : v ∈ Submodule.span ℝ (Set.range BBoson.JetComponentSpace.basis) := by
        rw [BBoson.JetComponentSpace.basis.span_eq]
        trivial
      induction hv using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        obtain ⟨s, μ⟩ := j
        exact h (JetGenerators.dB s μ)
      | zero => simp
      | add u w _ _ ihu ihw =>
        simp only [map_add, TensorProduct.tmul_add]
        exact Subalgebra.add_mem _ ihu ihw
      | smul r u _ ihu =>
        rw [show ((1 : ℂ) ⊗ₜ[ℝ]
            (SymmetricAlgebra.ι ℝ BBoson.JetComponentSpace (r • u)) :
            ℂ ⊗[ℝ] BBoson.JetAlgebra) =
            (algebraMap ℝ ℂ r) • ((1 : ℂ) ⊗ₜ[ℝ]
              SymmetricAlgebra.ι ℝ BBoson.JetComponentSpace u) from by
          rw [map_smul, TensorProduct.tmul_smul, ← algebraMap_smul ℂ r], map_smul]
        exact Subalgebra.smul_mem _ ihu _
    | mul u v ihu ihv =>
      rw [show ((1 : ℂ) ⊗ₜ[ℝ] (u * v) : ℂ ⊗[ℝ] BBoson.JetAlgebra) =
          ((1 : ℂ) ⊗ₜ[ℝ] u) * ((1 : ℂ) ⊗ₜ[ℝ] v) from by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul], map_mul]
      exact Subalgebra.mul_mem _ ihu ihv
    | add u v ihu ihv =>
      simp only [TensorProduct.tmul_add, map_add]
      exact Subalgebra.add_mem _ ihu ihv
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => rw [map_add]; exact Subalgebra.add_mem _ hu hv
  | tmul z c =>
    rw [show (z ⊗ₜ[ℝ] c : ℂ ⊗[ℝ] BBoson.JetAlgebra) = z • ((1 : ℂ) ⊗ₜ[ℝ] c) from by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul]
    exact Subalgebra.smul_mem _ (hone c) _

/-- The homogeneous span contains the whole fermionic factor once it contains the generators. -/
private lemma inclL_mem_boostWeightSubalgebra
    (h : ∀ j : JetGenerators, [j]ₐ ∈ boostWeightSubalgebra i)
    (b : LeptonSinglet.JetAlgebra) : inclL b ∈ boostWeightSubalgebra i := by
  have hι : ∀ m : LeptonSinglet.JetComponentSpace,
      inclL (ExteriorAlgebra.ι ℂ m) ∈ boostWeightSubalgebra i := by
    intro m
    have hm : m ∈ Submodule.span ℂ (Set.range LeptonSinglet.JetComponentSpace.basis) := by
      rw [LeptonSinglet.JetComponentSpace.basis.span_eq]
      trivial
    induction hm using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      cases j with
      | dψ s α => exact h (JetGenerators.dψ s α)
      | dbarψ s α => exact h (JetGenerators.dbarψ s α)
    | zero => simp
    | add u v _ _ ihu ihv =>
      simp only [map_add]
      exact Subalgebra.add_mem _ ihu ihv
    | smul c u _ ihu =>
      simp only [map_smul]
      exact Subalgebra.smul_mem _ ihu _
  induction b using ExteriorAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact Subalgebra.algebraMap_mem _ _
  | ι m => exact hι m
  | mul u v ihu ihv => rw [map_mul]; exact Subalgebra.mul_mem _ ihu ihv
  | add u v ihu ihv => rw [map_add]; exact Subalgebra.add_mem _ ihu ihv

/-- Once every generator is a finite sum of boost eigenvectors, so is every element: the
  homogeneous elements then span the whole jet algebra. -/
theorem boostWeightSubalgebra_eq_top_of_forall_ofGenerator
    (h : ∀ j : JetGenerators, [j]ₐ ∈ boostWeightSubalgebra i) : boostWeightSubalgebra i = ⊤ := by
  refine Algebra.eq_top_iff.mpr fun x => ?_
  induction x using JetAlgebra.induction_on with
  | zero => exact Subalgebra.zero_mem _
  | add u v hu hv => exact Subalgebra.add_mem _ hu hv
  | tmul a b =>
    rw [tmul_eq_inclB_mul_inclL]
    exact Subalgebra.mul_mem _ (inclB_mem_boostWeightSubalgebra h a)
      (inclL_mem_boostWeightSubalgebra h b)

/-- The decomposition of the jet algebra into boost-weight spaces is internal exactly when the
  homogeneous elements span. Independence always holds, so this isolates the one remaining
  obligation: that every element is a finite sum of boost eigenvectors. -/
theorem boostWeightSubmodule_isInternal_iff :
    DirectSum.IsInternal (boostWeightSubmodule i) ↔ (⨆ k, boostWeightSubmodule i k) = ⊤ := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  exact ⟨And.right, fun h => ⟨boostWeightSubmodule_iSupIndep, h⟩⟩

/-- The homogeneous elements span a subalgebra which the boost weights grade internally: the
  decomposition into weights is defined on it and is unique. -/
theorem boostWeightSubmodule_isInternal_of_top
    (h : (⨆ k, boostWeightSubmodule i k) = ⊤) : DirectSum.IsInternal (boostWeightSubmodule i) :=
  boostWeightSubmodule_isInternal_iff.mpr h

/-!

## H. The interpolating polynomial of the boost averages

`boostAvgZ` is a fixed rational combination of the identity and the boosts at `t = 2, 3, 4`
paired with their inverses, so on an element of boost weight `k` it acts by the scalar obtained
by substituting `t ^ k + t ^ (-k)` for each pair. The weights were chosen to make that scalar
one at `k = 0` and zero at `k = 2, 4, 6`; being a function of `t ^ k + t ^ (-k)` it is
automatically even in `k`, so it vanishes at `k = -2, -4, -6` as well.

-/

/-- The scalar by which `boostAvgZ` acts on an element of boost weight `k`. -/
noncomputable def boostAvgZWeight (k : ℤ) : ℂ :=
  (65359/21600 : ℂ)
  + (-133264/99225 : ℂ) * ((2 : ℂ) ^ k + (2 : ℂ) ^ (-k))
  + (384183/1019200 : ℂ) * ((3 : ℂ) ^ k + (3 : ℂ) ^ (-k))
  + (-60416/1289925 : ℂ) * ((4 : ℂ) ^ k + (4 : ℂ) ^ (-k))

/-- The interpolating scalar is even in the weight. -/
lemma boostAvgZWeight_neg (k : ℤ) : boostAvgZWeight (-k) = boostAvgZWeight k := by
  simp only [boostAvgZWeight, neg_neg]
  ring

@[simp] lemma boostAvgZWeight_zero : boostAvgZWeight 0 = 1 := by norm_num [boostAvgZWeight]
@[simp] lemma boostAvgZWeight_two : boostAvgZWeight 2 = 0 := by norm_num [boostAvgZWeight]
@[simp] lemma boostAvgZWeight_four : boostAvgZWeight 4 = 0 := by norm_num [boostAvgZWeight]
@[simp] lemma boostAvgZWeight_six : boostAvgZWeight 6 = 0 := by norm_num [boostAvgZWeight]

/-- The interpolating scalar does *not* vanish at weight eight. This is why `boostAvgZ` is the
  projection only where the boost weights are among `0, ±2, ±4, ±6` — on the covariant
  subalgebra in mass weight eight — and not on all of mass weight eight, which contains the
  weight-eight element `∂_ρ ∂_σ ∂_τ B_μ`. -/
lemma boostAvgZWeight_eight_ne_zero : boostAvgZWeight 8 ≠ 0 := by
  norm_num [boostAvgZWeight]

@[simp] lemma boostAvgZWeight_neg_two : boostAvgZWeight (-2) = 0 := by
  rw [boostAvgZWeight_neg, boostAvgZWeight_two]

@[simp] lemma boostAvgZWeight_neg_four : boostAvgZWeight (-4) = 0 := by
  rw [boostAvgZWeight_neg, boostAvgZWeight_four]

@[simp] lemma boostAvgZWeight_neg_six : boostAvgZWeight (-6) = 0 := by
  rw [boostAvgZWeight_neg, boostAvgZWeight_six]

/-!

## I. The boost averages are the projections onto boost weight zero

-/

/-- The weighted boost average along the `i`-th spatial axis. -/
noncomputable def boostAvgAxis : Fin 3 → Module.End ℂ JetAlgebra
  | 0 => boostAvgX
  | 1 => boostAvgY
  | 2 => boostAvgZ

@[simp] lemma boostAvgAxis_zero : boostAvgAxis 0 = boostAvgX := rfl
@[simp] lemma boostAvgAxis_one : boostAvgAxis 1 = boostAvgY := rfl
@[simp] lemma boostAvgAxis_two : boostAvgAxis 2 = boostAvgZ := rfl

lemma boostAvgAxis_eq (i : Fin 3) :
    boostAvgAxis i = (65359/21600 : ℂ) • LinearMap.id
      + (-133264/99225 : ℂ) • (repLorentzGroup (boostAxis i 2 (by norm_num)) +
          repLorentzGroup ((boostAxis i 2 (by norm_num))⁻¹))
      + (384183/1019200 : ℂ) • (repLorentzGroup (boostAxis i 3 (by norm_num)) +
          repLorentzGroup ((boostAxis i 3 (by norm_num))⁻¹))
      + (-60416/1289925 : ℂ) • (repLorentzGroup (boostAxis i 4 (by norm_num)) +
          repLorentzGroup ((boostAxis i 4 (by norm_num))⁻¹)) := by
  fin_cases i <;> rfl

/-- The boost average along an axis acts on an element of boost weight `k` for that axis by the
  scalar `boostAvgZWeight k`. -/
lemma boostAvgAxis_apply_of_mem {i : Fin 3} {k : ℤ} {x : JetAlgebra}
    (hx : x ∈ boostWeightSubmodule i k) :
    boostAvgAxis i x = boostAvgZWeight k • x := by
  have hinv : ∀ (t : ℝ) (ht : t ≠ 0),
      repLorentzGroup ((boostAxis i t ht)⁻¹) x = ((((t : ℝ) : ℂ))⁻¹ ^ k) • x := by
    intro t ht
    rw [boostAxis_inv, hx t⁻¹ (inv_ne_zero ht), algebraMap_real_complex, Complex.ofReal_inv]
  simp only [boostAvgAxis_eq i, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    hx 2 (by norm_num), hx 3 (by norm_num), hx 4 (by norm_num),
    hinv 2 (by norm_num), hinv 3 (by norm_num), hinv 4 (by norm_num),
    algebraMap_real_complex, boostAvgZWeight]
  push_cast
  match_scalars
  simp only [_root_.inv_zpow, ← _root_.zpow_neg]
  ring

/-- On boost weight zero the average is the identity. -/
lemma boostAvgAxis_apply_of_mem_zero {i : Fin 3} {x : JetAlgebra}
    (hx : x ∈ boostWeightSubmodule i 0) : boostAvgAxis i x = x := by
  rw [boostAvgAxis_apply_of_mem hx, boostAvgZWeight_zero, one_smul]

/-- The average annihilates the boost weights `±2, ±4, ±6`. -/
lemma boostAvgAxis_apply_eq_zero_of_mem {i : Fin 3} {k : ℤ} {x : JetAlgebra}
    (hx : x ∈ boostWeightSubmodule i k)
    (hk : k = 2 ∨ k = 4 ∨ k = 6 ∨ k = -2 ∨ k = -4 ∨ k = -6) : boostAvgAxis i x = 0 := by
  rw [boostAvgAxis_apply_of_mem hx]
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- Each boost average fixes every Lorentz-invariant element, as the projection onto boost
  weight zero must. -/
lemma boostAvgAxis_apply_of_isInvariant (i : Fin 3) {x : JetAlgebra} (hx : IsInvariant x) :
    boostAvgAxis i x = x :=
  boostAvgAxis_apply_of_mem_zero (i := i) (mem_boostWeightSubmodule_zero_of_isInvariant hx)

/-- `boostAvgZ` acts on an element of `z`-boost weight `k` by `boostAvgZWeight k`. -/
lemma boostAvgZ_apply_of_mem {k : ℤ} {x : JetAlgebra} (hx : x ∈ boostWeightSubmodule 2 k) :
    boostAvgZ x = boostAvgZWeight k • x := boostAvgAxis_apply_of_mem hx

/-- `boostAvgX` acts on an element of `x`-boost weight `k` by `boostAvgZWeight k`. -/
lemma boostAvgX_apply_of_mem {k : ℤ} {x : JetAlgebra} (hx : x ∈ boostWeightSubmodule 0 k) :
    boostAvgX x = boostAvgZWeight k • x := boostAvgAxis_apply_of_mem hx

/-- `boostAvgY` acts on an element of `y`-boost weight `k` by `boostAvgZWeight k`. -/
lemma boostAvgY_apply_of_mem {k : ℤ} {x : JetAlgebra} (hx : x ∈ boostWeightSubmodule 1 k) :
    boostAvgY x = boostAvgZWeight k • x := boostAvgAxis_apply_of_mem hx

/-!

## J. The grading

The weight submodules are independent (`boostWeightSubmodule_iSupIndep`) and, by the descent
through the component spaces of section C transported along section A, they span. So they
decompose the jet algebra internally along every axis, and together with the graded-monoid
structure of section D they make it a graded algebra three times over.

-/

/-- The homogeneous elements span the jet algebra, for every axis. -/
theorem iSup_boostWeightSubmodule_eq_top (i : Fin 3) :
    (⨆ k, boostWeightSubmodule i k) = ⊤ :=
  BoostWeight.isGraded_of_isGraded_two isGraded_jetAlgebra i

/-- Every generator is a finite sum of boost eigenvectors, for every axis. -/
theorem ofGenerator_mem_boostWeightSubalgebra (i : Fin 3) (j : JetGenerators) :
    [j]ₐ ∈ boostWeightSubalgebra i := by
  rw [mem_boostWeightSubalgebra, iSup_boostWeightSubmodule_eq_top]
  trivial

/-- **The boost weight grades the jet algebra.** For each axis the weight submodules decompose
  it as an internal direct sum: every element is a finite sum of boost eigenvectors, uniquely. -/
theorem boostWeightSubmodule_isInternal (i : Fin 3) :
    DirectSum.IsInternal (boostWeightSubmodule i) :=
  boostWeightSubmodule_isInternal_iff.mpr (iSup_boostWeightSubmodule_eq_top i)

/-- The decomposition of an element of the jet algebra into its boost-weight components. -/
noncomputable instance (i : Fin 3) : DirectSum.Decomposition (boostWeightSubmodule i) :=
  (boostWeightSubmodule_isInternal i).chooseDecomposition

/-- **The jet algebra is a graded algebra for the boost weight along each axis.** Weights add
  under multiplication, the unit is neutral, and the weight components decompose every
  element. -/
noncomputable instance (i : Fin 3) : GradedAlgebra (boostWeightSubmodule i) where
  one_mem := one_mem_boostWeightSubmodule
  mul_mem _ _ _ _ hx hy := mul_mem_boostWeightSubmodule hx hy

end JetAlgebra

end LeptonGaugeSector

end
