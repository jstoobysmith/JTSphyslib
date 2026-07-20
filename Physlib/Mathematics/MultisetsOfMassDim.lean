/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Nathaneal Sajan, Jinzheng Li
-/
module

public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Rat.Floor
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
/-!

# Computable enumeration of multisets of a given mass dimension

## i. Overview

Given a finite type `F` of field specifications, a map `dim : F → ℚ` assigning to each field
its mass dimension (assumed positive), and a target `m : ℚ`, this file constructs, in a
computable way, the `Finset (Multiset F)` of all multisets of fields whose overall mass
dimension is `m`. This corresponds to the possible operators (terms) of mass dimension `m`
in an EFT Lagrangian built from the fields in `F` (excluding derivatives).

The construction proceeds by noting that if `d` is the minimal mass dimension of a field,
then a multiset of mass dimension `m` has at most `⌊m / d⌋₊` elements. We therefore
enumerate all multisets of cardinality at most this bound using `Finset.sym`, and filter
by the mass-dimension condition.

Since the construction is computable it can be used with `#eval`. However, rational
arithmetic does not reduce in the kernel, so `multisetsOfMassDim` can not directly be
used with `decide`. For this reason we also provide a version `multisetsOfMassDimNat`
with natural-number valued mass dimensions (corresponding to clearing denominators,
e.g. working in units of half mass dimensions so that a Weyl fermion has scaled
dimension `3`), which is `decide`-friendly. The lemma `multisetsOfMassDim_eq_natCast`
allows one to rewrite the former into the latter before calling `decide`.

## Key results

- `multisetsOfCard` : the finset of all multisets over `F` of a given cardinality.
- `multisetsOfMassDim` : the finset of all multisets over `F` of a given mass dimension.
- `mem_multisetsOfMassDim_iff` : the defining property
  `s ∈ multisetsOfMassDim dim m ↔ (s.map dim).sum = m`, valid whenever `dim` is positive.
- `multisetsOfMassDimNat`, `mem_multisetsOfMassDimNat_iff` : the analogous construction
  for natural-number valued (scaled) mass dimensions, usable with `decide`.
- `multisetsOfMassDim_eq_natCast` : the two constructions agree after clearing
  denominators.

-/

@[expose] public section

variable {F : Type*} [Fintype F]

/-!

## A. Multisets of a given cardinality

-/

/-- The finset of all multisets over a finite type `F` with exactly `n` elements. -/
def multisetsOfCard (F : Type*) [Fintype F] [DecidableEq F] (n : ℕ) :
    Finset (Multiset F) :=
  (Finset.univ.sym n).image Sym.toMultiset

@[simp]
lemma mem_multisetsOfCard [DecidableEq F] {n : ℕ} {s : Multiset F} :
    s ∈ multisetsOfCard F n ↔ Multiset.card s = n := by
  constructor
  · intro h
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp h
    exact x.2
  · rintro rfl
    exact Finset.mem_image.mpr
      ⟨⟨s, rfl⟩, Finset.mem_sym_iff.mpr fun a _ => Finset.mem_univ a, rfl⟩

/-!

## B. The bound on the cardinality

-/

/-- The sum of `dim` over a multiset is at least the cardinality times the minimal
  value of `dim`. Shared bound underlying `card_le_massDimCardBound` and
  `card_le_massDimCardBoundNat`. -/
lemma card_nsmul_inf'_le_sum_map {M : Type*} [AddCommMonoid M] [LinearOrder M]
    [AddLeftMono M] (huniv : (Finset.univ : Finset F).Nonempty) (dim : F → M)
    (s : Multiset F) :
    Multiset.card s • Finset.univ.inf' huniv dim ≤ (s.map dim).sum := by
  have h1 : Multiset.card (s.map dim) • Finset.univ.inf' huniv dim ≤ (s.map dim).sum := by
    refine Multiset.card_nsmul_le_sum fun x hx => ?_
    obtain ⟨f, -, rfl⟩ := Multiset.mem_map.mp hx
    exact Finset.inf'_le dim (Finset.mem_univ f)
  simpa using h1

/-- An upper bound on the number of fields in a multiset of overall mass dimension `m`:
  `⌊m / d⌋₊` where `d` is the minimal mass dimension of a field. Equal to `0` when
  `F` is empty. -/
def massDimCardBound (dim : F → ℚ) (m : ℚ) : ℕ :=
  if h : (Finset.univ : Finset F).Nonempty then ⌊m / Finset.univ.inf' h dim⌋₊ else 0

private lemma card_le_massDimCardBound {dim : F → ℚ} (hdim : ∀ f, 0 < dim f) {m : ℚ}
    {s : Multiset F} (hs : (s.map dim).sum = m) :
    Multiset.card s ≤ massDimCardBound dim m := by
  rcases eq_or_ne s 0 with rfl | hne
  · simp
  obtain ⟨f0, -⟩ := Multiset.exists_mem_of_ne_zero hne
  have huniv : (Finset.univ : Finset F).Nonempty := ⟨f0, Finset.mem_univ f0⟩
  rw [massDimCardBound, dif_pos huniv]
  have hdpos : 0 < Finset.univ.inf' huniv dim :=
    (Finset.lt_inf'_iff huniv).mpr fun i _ => hdim i
  have hle := hs ▸ card_nsmul_inf'_le_sum_map huniv dim s
  refine Nat.le_floor ?_
  rw [le_div_iff₀ hdpos]
  simpa [nsmul_eq_mul] using hle

/-!

## C. Multisets of a given mass dimension

-/

/-- The finset of all multisets over a finite type `F` whose overall mass dimension,
  as measured by `dim : F → ℚ`, is `m`. The defining property, valid when `dim` is
  positive, is `mem_multisetsOfMassDim_iff`. -/
def multisetsOfMassDim [DecidableEq F] (dim : F → ℚ) (m : ℚ) : Finset (Multiset F) :=
  ((Finset.range (massDimCardBound dim m + 1)).biUnion (multisetsOfCard F)).filter
    fun s => (s.map dim).sum = m

lemma mem_multisetsOfMassDim_iff [DecidableEq F] {dim : F → ℚ} (hdim : ∀ f, 0 < dim f) {m : ℚ}
    {s : Multiset F} :
    s ∈ multisetsOfMassDim dim m ↔ (s.map dim).sum = m := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨Multiset.card s, ?_, by simp⟩, h⟩
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (card_le_massDimCardBound hdim h))

/-!

## D. Multisets of a given scaled (natural-number) mass dimension

Rational arithmetic does not reduce in the kernel, so `multisetsOfMassDim` is usable
with `#eval` but not with `decide`. Clearing denominators in the mass dimensions
(e.g. working in units of half mass dimensions) reduces the problem to natural-number
valued dimensions, for which the analogous construction below is `decide`-friendly.

-/

/-- An upper bound on the number of fields in a multiset of overall scaled mass
  dimension `m`: `m / d` (natural-number division) where `d` is the minimal scaled
  mass dimension of a field. Equal to `0` when `F` is empty. -/
def massDimCardBoundNat (dim : F → ℕ) (m : ℕ) : ℕ :=
  if h : (Finset.univ : Finset F).Nonempty then m / Finset.univ.inf' h dim else 0

private lemma card_le_massDimCardBoundNat {dim : F → ℕ} (hdim : ∀ f, 0 < dim f) {m : ℕ}
    {s : Multiset F} (hs : (s.map dim).sum = m) :
    Multiset.card s ≤ massDimCardBoundNat dim m := by
  rcases eq_or_ne s 0 with rfl | hne
  · simp
  obtain ⟨f0, -⟩ := Multiset.exists_mem_of_ne_zero hne
  have huniv : (Finset.univ : Finset F).Nonempty := ⟨f0, Finset.mem_univ f0⟩
  rw [massDimCardBoundNat, dif_pos huniv]
  have hdpos : 0 < Finset.univ.inf' huniv dim :=
    (Finset.lt_inf'_iff huniv).mpr fun i _ => hdim i
  rw [Nat.le_div_iff_mul_le hdpos]
  simpa [hs, smul_eq_mul] using card_nsmul_inf'_le_sum_map huniv dim s

/-- The finset of all multisets over a finite type `F` whose overall scaled mass
  dimension, as measured by `dim : F → ℕ`, is `m`. The defining property, valid when
  `dim` is positive, is `mem_multisetsOfMassDimNat_iff`. Unlike `multisetsOfMassDim`,
  this construction reduces in the kernel and can be used with `decide`. -/
def multisetsOfMassDimNat [DecidableEq F] (dim : F → ℕ) (m : ℕ) : Finset (Multiset F) :=
  ((Finset.range (massDimCardBoundNat dim m + 1)).biUnion (multisetsOfCard F)).filter
    fun s => (s.map dim).sum = m

lemma mem_multisetsOfMassDimNat_iff [DecidableEq F] {dim : F → ℕ} (hdim : ∀ f, 0 < dim f)
    {m : ℕ} {s : Multiset F} :
    s ∈ multisetsOfMassDimNat dim m ↔ (s.map dim).sum = m := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨Multiset.card s, ?_, by simp⟩, h⟩
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (card_le_massDimCardBoundNat hdim h))

/-!

## E. Relating the two constructions

-/

/-- Clearing denominators: on multiplying all mass dimensions and the target mass
  dimension by a common positive scale `N` rendering them all natural numbers, the
  finset of multisets of a given mass dimension can be computed through
  `multisetsOfMassDimNat`, and hence through `decide`. -/
lemma multisetsOfMassDim_eq_natCast [DecidableEq F] {dim : F → ℚ} (hdim : ∀ f, 0 < dim f)
    {dimN : F → ℕ} {N : ℕ} (hN : 0 < N) (hdimN : ∀ f, (dimN f : ℚ) = dim f * N)
    {m : ℚ} {mN : ℕ} (hmN : (mN : ℚ) = m * N) :
    multisetsOfMassDim dim m = multisetsOfMassDimNat dimN mN := by
  have hNQ : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hdimNpos : ∀ f, 0 < dimN f := fun f => by
    have h1 : (0 : ℚ) < (dimN f : ℚ) := by
      rw [hdimN f]
      exact mul_pos (hdim f) (by exact_mod_cast hN)
    exact_mod_cast h1
  ext s
  rw [mem_multisetsOfMassDim_iff hdim, mem_multisetsOfMassDimNat_iff hdimNpos]
  have key : ((s.map dimN).sum : ℚ) = (s.map dim).sum * N := by
    induction s using Multiset.induction with
    | empty => simp
    | cons a t ih => simp [hdimN, ih, add_mul]
  constructor
  · intro h
    have h1 : ((s.map dimN).sum : ℚ) = (mN : ℚ) := by rw [key, h, hmN]
    exact_mod_cast h1
  · intro h
    have h1 : (s.map dim).sum * (N : ℚ) = m * N := by rw [← key, h, hmN]
    exact mul_right_cancel₀ hNQ h1
