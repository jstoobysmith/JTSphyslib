/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.IsospinDecomposition
/-!
# Gauge weight decompositions

## i. Overview

A **gauge weight decomposition** of a submodule `V` is a finitely supported family of
subspaces of pure gauge weight whose supremum is `V`. A gauge weight is a quadruple

  `(colour₁, colour₂, isospin, hypercharge) : ℤ × ℤ × ℤ × ℤ`,

the four exponents recording how a vector scales under the four generators of the maximal
torus of `SU(3) × SU(2) × U(1)` — two for the rank-two colour Cartan, one for weak isospin
(normalized as `2T₃`), one for hypercharge (normalized as `6Y`).

This merges `HyperchargeDecomposition` and `IsospinDecomposition` into a single object, and
adds colour. That merge is legitimate because the four generators *commute*: they live in
different factors of the product group, and the two colour generators are both diagonal. So
the four gradings are simultaneously realizable, and there is no loss in carrying them
together.

## ii. Independence, and why it is not immediate

For a single generator, independence of the weight spaces is free: they sit in eigenspaces
of one operator at the pairwise distinct eigenvalues `(exp i) ^ k`. At rank four no single
generator separates the weights, so the argument has to be iterated. `mem_iSup_of_eigenvector`
is the one-generator refinement step — an eigenvector at exponent zero lying in the span of
the pieces already lies in the span of those pieces whose corresponding coordinate vanishes —
and `mem_zero_of_invariant` applies it once per generator, peeling off one coordinate at a
time until only the zero weight survives.

## iii. Key results

- `gaugeTorusGen` : the four commuting torus generators.
- `GaugeWeightDecomposition` : a finitely supported family of pure-weight subspaces with
  supremum `V`.
- `GaugeWeightDecomposition.sup` : decompositions combine weightwise along `V ⊔ V'`.
- `GaugeWeightDecomposition.mul` : weights add under multiplication, decomposing `V * V'`.
- `GaugeWeightDecomposition.mem_zero_of_invariant` : a gauge-invariant element lies in the
  zero-weight piece.

## iv. Table of contents

- A. The colour torus generators
- B. The four torus generators and gauge weights
- C. Gauge weight decompositions
- D. Joins
- E. Products
- F. Invariants

-/

@[expose] public section

namespace StandardModel

open Matrix Pointwise

/-!

## A. The colour torus generators

-/

/-- The first colour torus generator, `diag (exp i, exp (-i), 1)`. -/
noncomputable def su3ExpIOne : specialUnitaryGroup (Fin 3) ℂ :=
  ⟨!![(expI : ℂ), 0, 0; 0, star (expI : ℂ), 0; 0, 0, 1], by
    have hms : (expI : ℂ) * (starRingEnd ℂ) (expI : ℂ) = 1 :=
      Unitary.mul_star_self_of_mem expI.2
    have hsm : (starRingEnd ℂ) (expI : ℂ) * (expI : ℂ) = 1 :=
      Unitary.star_mul_self_of_mem expI.2
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff]
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three, star_eq_conjTranspose,
          Matrix.conjTranspose_apply, hms, hsm]
    · simp [Matrix.det_fin_three, hms]⟩

/-- The second colour torus generator, `diag (1, exp i, exp (-i))`. -/
noncomputable def su3ExpITwo : specialUnitaryGroup (Fin 3) ℂ :=
  ⟨!![1, 0, 0; 0, (expI : ℂ), 0; 0, 0, star (expI : ℂ)], by
    have hms : (expI : ℂ) * (starRingEnd ℂ) (expI : ℂ) = 1 :=
      Unitary.mul_star_self_of_mem expI.2
    have hsm : (starRingEnd ℂ) (expI : ℂ) * (expI : ℂ) = 1 :=
      Unitary.star_mul_self_of_mem expI.2
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff]
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three, star_eq_conjTranspose,
          Matrix.conjTranspose_apply, hms, hsm]
    · simp [Matrix.det_fin_three, hms]⟩

/-!

## B. The four torus generators and gauge weights

-/

/-- The four generators of the maximal torus of the gauge group. They pairwise commute: the
  colour, isospin and hypercharge generators sit in different factors of the product, and the
  two colour generators are both diagonal. -/
noncomputable def gaugeTorusGen : Fin 4 → GaugeGroupI :=
  ![⟨su3ExpIOne, 1, 1⟩, ⟨su3ExpITwo, 1, 1⟩, ⟨1, su2ExpI, 1⟩, ⟨1, 1, expI⟩]

/-- A **gauge weight**: the four exponents `(colour₁, colour₂, isospin, hypercharge)`
  recording how a vector scales under `gaugeTorusGen`. Isospin is normalized as `2T₃` and
  hypercharge as `6Y`. -/
abbrev GaugeWeight : Type := ℤ × ℤ × ℤ × ℤ

/-- The exponent of a gauge weight against the `i`-th torus generator. -/
def GaugeWeight.coord (w : GaugeWeight) : Fin 4 → ℤ := ![w.1, w.2.1, w.2.2.1, w.2.2.2]

@[simp] lemma GaugeWeight.coord_zero (w : GaugeWeight) : w.coord 0 = w.1 := rfl
@[simp] lemma GaugeWeight.coord_one (w : GaugeWeight) : w.coord 1 = w.2.1 := rfl
@[simp] lemma GaugeWeight.coord_two (w : GaugeWeight) : w.coord 2 = w.2.2.1 := rfl
@[simp] lemma GaugeWeight.coord_three (w : GaugeWeight) : w.coord 3 = w.2.2.2 := rfl

lemma GaugeWeight.coord_add (w w' : GaugeWeight) (i : Fin 4) :
    (w + w').coord i = w.coord i + w'.coord i := by
  fin_cases i <;> rfl

/-- `exp i` is nonzero. -/
lemma expI_ne_zero : ((expI : ℂ)) ≠ 0 := fun h0 => by
  have h := Unitary.mul_star_self_of_mem expI.2
  rw [h0, zero_mul] at h
  exact zero_ne_one h

/-!

## C. Gauge weight decompositions

-/

variable {B : Type*} [Ring B] [Algebra ℂ B]

/-- A **gauge weight decomposition** of a submodule `V`: a finitely supported family of
  subspaces of pure gauge weight whose supremum is `V`. Purity is recorded against the four
  commuting torus generators simultaneously. -/
structure GaugeWeightDecomposition (rep : Representation ℂ GaugeGroupI B)
    (V : Submodule ℂ B) where
  /-- The piece of gauge weight `w`. -/
  piece : GaugeWeight → Submodule ℂ B
  /-- The finite set of gauge weights that occur. -/
  supp : Finset GaugeWeight
  /-- Each piece is of pure gauge weight, as seen by all four torus generators. -/
  piece_le : ∀ w, ∀ x, x ∈ piece w → ∀ i,
    rep (gaugeTorusGen i) x = ((expI : ℂ) ^ w.coord i) • x
  /-- Only the gauge weights in `supp` occur. -/
  piece_eq_bot : ∀ w ∉ supp, piece w = ⊥
  /-- The pieces exhaust `V`. -/
  iSup_piece : (⨆ w, piece w) = V

namespace GaugeWeightDecomposition

variable {rep : Representation ℂ GaugeGroupI B} {V V' : Submodule ℂ B}

/-- The weight-`w` piece lies in the eigenspace of the `i`-th torus generator at the
  eigenvalue `(exp i) ^ (w.coord i)`. This is `piece_le` phrased as an inequality of
  submodules. -/
lemma piece_le_eigenspace (d : GaugeWeightDecomposition rep V) (w : GaugeWeight) (i : Fin 4) :
    d.piece w ≤ Module.End.eigenspace (rep (gaugeTorusGen i)) ((expI : ℂ) ^ w.coord i) :=
  fun _ hy => Module.End.mem_eigenspace_iff.mpr (d.piece_le w _ hy i)

lemma piece_eq_zero_of_not_mem_supp (d : GaugeWeightDecomposition rep V) (w : GaugeWeight)
    (hw : w ∉ d.supp) : d.piece w = ⊥ := d.piece_eq_bot w hw

/-- Transport a decomposition along an equality of submodules. -/
def copy (d : GaugeWeightDecomposition rep V) (W : Submodule ℂ B) (hW : W = V) :
    GaugeWeightDecomposition rep W where
  piece := d.piece
  supp := d.supp
  piece_le := d.piece_le
  piece_eq_bot := d.piece_eq_bot
  iSup_piece := by rw [d.iSup_piece, hW]

@[simp]
lemma copy_piece (d : GaugeWeightDecomposition rep V) (W : Submodule ℂ B) (hW : W = V) :
    (d.copy W hW).piece = d.piece := rfl

/-!

## D. Joins

-/

/-- The join of two gauge weight decompositions: the pieces, supports and suprema all
  combine weightwise, decomposing `V ⊔ V'`. -/
noncomputable def sup (d : GaugeWeightDecomposition rep V)
    (d' : GaugeWeightDecomposition rep V') : GaugeWeightDecomposition rep (V ⊔ V') where
  piece w := d.piece w ⊔ d'.piece w
  supp := d.supp ∪ d'.supp
  piece_le w x hx i :=
    Module.End.mem_eigenspace_iff.mp
      (sup_le (d.piece_le_eigenspace w i) (d'.piece_le_eigenspace w i) hx)
  piece_eq_bot w hw := by
    rw [Finset.mem_union, not_or] at hw
    rw [d.piece_eq_bot w hw.1, d'.piece_eq_bot w hw.2, bot_sup_eq]
  iSup_piece := by
    rw [iSup_sup_eq, d.iSup_piece, d'.iSup_piece]

@[simp]
lemma sup_piece (d : GaugeWeightDecomposition rep V) (d' : GaugeWeightDecomposition rep V')
    (w : GaugeWeight) : (d.sup d').piece w = d.piece w ⊔ d'.piece w := rfl

/-!

## E. Products

-/

/-- The product of two gauge weight decompositions: gauge weights **add** under
  multiplication, so the weight-`w` piece of `V * V'` is spanned by the products of pieces
  whose weights sum to `w`, and the support is the pointwise sum of the supports.

  Multiplicativity of the representation is a hypothesis rather than a field: a
  `Representation` records only a linear action. -/
noncomputable def mul (hmul : ∀ (g : GaugeGroupI) (x y : B), rep g (x * y) = rep g x * rep g y)
    (d : GaugeWeightDecomposition rep V) (d' : GaugeWeightDecomposition rep V') :
    GaugeWeightDecomposition rep (V * V') where
  piece w := ⨆ w₁, ⨆ w₂, ⨆ _ : w₁ + w₂ = w, d.piece w₁ * d'.piece w₂
  supp := d.supp + d'.supp
  piece_le w x hx i := by
    have key : (⨆ w₁, ⨆ w₂, ⨆ _ : w₁ + w₂ = w, d.piece w₁ * d'.piece w₂)
        ≤ Module.End.eigenspace (rep (gaugeTorusGen i)) ((expI : ℂ) ^ w.coord i) := by
      refine iSup_le fun w₁ => iSup_le fun w₂ => iSup_le fun hw => ?_
      refine Submodule.mul_le.mpr fun m hm n hn => ?_
      refine Module.End.mem_eigenspace_iff.mpr ?_
      rw [hmul, d.piece_le w₁ m hm i, d'.piece_le w₂ n hn i, smul_mul_smul_comm,
        ← zpow_add₀ expI_ne_zero, ← GaugeWeight.coord_add, hw]
    exact Module.End.mem_eigenspace_iff.mp (key hx)
  piece_eq_bot w hw := by
    refine le_antisymm (iSup_le fun w₁ => iSup_le fun w₂ => iSup_le fun hsum => ?_) bot_le
    by_cases h1 : w₁ ∈ d.supp
    · by_cases h2 : w₂ ∈ d'.supp
      · exact absurd (hsum ▸ Finset.add_mem_add h1 h2) hw
      · rw [d'.piece_eq_bot w₂ h2, Submodule.mul_bot]
    · rw [d.piece_eq_bot w₁ h1, Submodule.bot_mul]
  iSup_piece := by
    refine le_antisymm (iSup_le fun w => iSup_le fun w₁ => iSup_le fun w₂ =>
      iSup_le fun _ => ?_) ?_
    · exact mul_le_mul' ((le_iSup d.piece w₁).trans d.iSup_piece.le)
        ((le_iSup d'.piece w₂).trans d'.iSup_piece.le)
    · have hV : (⨆ w₁, d.piece w₁) * (⨆ w₂, d'.piece w₂) = V * V' := by
        rw [d.iSup_piece, d'.iSup_piece]
      rw [← hV, Submodule.iSup_mul]
      refine iSup_le fun w₁ => ?_
      rw [Submodule.mul_iSup]
      refine iSup_le fun w₂ => ?_
      exact le_iSup_of_le (w₁ + w₂)
        (le_iSup_of_le w₁ (le_iSup_of_le w₂ (le_iSup_of_le rfl le_rfl)))

lemma mul_supp (hmul : ∀ (g : GaugeGroupI) (x y : B), rep g (x * y) = rep g x * rep g y)
    (d : GaugeWeightDecomposition rep V) (d' : GaugeWeightDecomposition rep V') :
    (d.mul hmul d').supp = d.supp + d'.supp := rfl

lemma mul_piece (hmul : ∀ (g : GaugeGroupI) (x y : B), rep g (x * y) = rep g x * rep g y)
    (d : GaugeWeightDecomposition rep V) (d' : GaugeWeightDecomposition rep V')
    (w : GaugeWeight) :
    (d.mul hmul d').piece w = ⨆ w₁, ⨆ w₂, ⨆ _ : w₁ + w₂ = w, d.piece w₁ * d'.piece w₂ := rfl

lemma mul_piece_eq_sub (hmul : ∀ (g : GaugeGroupI) (x y : B), rep g (x * y) = rep g x * rep g y)
    (d : GaugeWeightDecomposition rep V) (d' : GaugeWeightDecomposition rep V')
    (w : GaugeWeight) :
    (d.mul hmul d').piece w = ⨆ w₁ ∈ d.supp, d.piece w₁ * d'.piece (w - w₁) := by
  rw [mul_piece]
  refine le_antisymm (iSup_le fun w₁ => iSup_le fun w₂ => iSup_le fun hw => ?_) ?_
  · by_cases h1 : w₁ ∈ d.supp
    · refine le_iSup₂_of_le w₁ h1 ?_
      rw [eq_sub_of_add_eq' hw]
    · rw [d.piece_eq_bot w₁ h1, Submodule.bot_mul]
      exact bot_le
  · exact iSup₂_le fun w₁ _ =>
      le_iSup_of_le w₁ (le_iSup_of_le (w - w₁) (le_iSup_of_le (add_sub_cancel w₁ w) le_rfl))

lemma mul_piece_eq_sub' (hmul : ∀ (g : GaugeGroupI) (x y : B), rep g (x * y) = rep g x * rep g y)
    (d : GaugeWeightDecomposition rep V) (d' : GaugeWeightDecomposition rep V')
    (w : GaugeWeight) :
    (d.mul hmul d').piece w = ⨆ w₂ ∈ d'.supp, d.piece (w - w₂) * d'.piece w₂ := by
  rw [mul_piece]
  refine le_antisymm (iSup_le fun w₁ => iSup_le fun w₂ => iSup_le fun hw => ?_) ?_
  · by_cases h2 : w₂ ∈ d'.supp
    · refine le_iSup₂_of_le w₂ h2 ?_
      rw [eq_sub_of_add_eq hw]
    · rw [d'.piece_eq_bot w₂ h2, Submodule.mul_bot]
      exact bot_le
  · exact iSup₂_le fun w₂ _ =>
      le_iSup_of_le (w - w₂) (le_iSup_of_le w₂ (le_iSup_of_le (sub_add_cancel w w₂) le_rfl))


/-- The unit submodule is of weight zero: the identity of `B` is a gauge singlet, provided
  the representation preserves the unit. -/
noncomputable def one (hone : ∀ g : GaugeGroupI, rep g 1 = 1) :
    GaugeWeightDecomposition rep (1 : Submodule ℂ B) where
  piece w := if w = 0 then 1 else ⊥
  supp := {0}
  piece_le := by
    intro w x hx i
    rcases eq_or_ne w 0 with rfl | hw
    · rw [if_pos rfl, Submodule.one_eq_span, Submodule.mem_span_singleton] at hx
      obtain ⟨c, rfl⟩ := hx
      have h0 : GaugeWeight.coord 0 i = 0 := by fin_cases i <;> rfl
      rw [map_smul, hone, h0, zpow_zero, one_smul]
    · rw [if_neg hw, Submodule.mem_bot] at hx
      subst hx
      simp
  piece_eq_bot w hw := by rw [if_neg (by simpa using hw)]
  iSup_piece := by
    refine le_antisymm (iSup_le fun w => ?_) (le_iSup_of_le 0 (le_of_eq (if_pos rfl).symm))
    by_cases hw : w = 0
    · rw [if_pos hw]
    · rw [if_neg hw]
      exact bot_le

/-- When the right factor vanishes off a finite set `S` of weights, the weight-`w` piece of
  a product collapses to a join over `S`, pairing `w - v` against `v`. This is what makes the
  pieces of an iterated product computable: the double `⨆` over all of `ℤ⁴` becomes a finite
  join. -/
lemma mul_piece_of_supp (hmul : ∀ (g : GaugeGroupI) (x y : B), rep g (x * y) = rep g x * rep g y)
    (d : GaugeWeightDecomposition rep V) (d' : GaugeWeightDecomposition rep V')
    (S : Finset GaugeWeight) (hS : ∀ v ∉ S, d'.piece v = ⊥) (w : GaugeWeight) :
    (d.mul hmul d').piece w = ⨆ v ∈ S, d.piece (w - v) * d'.piece v := by
  rw [mul_piece]
  refine le_antisymm (iSup_le fun w₁ => iSup_le fun w₂ => iSup_le fun hw => ?_) ?_
  · by_cases hv : w₂ ∈ S
    · refine le_iSup₂_of_le w₂ hv ?_
      rw [eq_sub_of_add_eq hw]
    · rw [hS w₂ hv, Submodule.mul_bot]
      exact bot_le
  · exact iSup₂_le fun v _ =>
      le_iSup_of_le (w - v) (le_iSup_of_le v (le_iSup_of_le (sub_add_cancel w v) le_rfl))

@[simp]
lemma one_piece (hone : ∀ g : GaugeGroupI, rep g 1 = 1) (w : GaugeWeight) :
    (one (B := B) (rep := rep) hone).piece w = if w = 0 then 1 else ⊥ := rfl

/-- Powers of a decomposed submodule: gauge weights add, so `V ^ k` inherits a
  decomposition, built by iterating `mul` from `one`. -/
noncomputable def pow (hone : ∀ g : GaugeGroupI, rep g 1 = 1)
    (hmul : ∀ (g : GaugeGroupI) (x y : B), rep g (x * y) = rep g x * rep g y)
    (d : GaugeWeightDecomposition rep V) :
    (k : ℕ) → GaugeWeightDecomposition rep (V ^ k)
  | 0 => (one hone).copy _ (pow_zero V)
  | (k + 1) => ((pow hone hmul d k).mul hmul d).copy _ (pow_succ V k)

@[simp]
lemma pow_zero_piece (hone : ∀ g : GaugeGroupI, rep g 1 = 1)
    (hmul : ∀ (g : GaugeGroupI) (x y : B), rep g (x * y) = rep g x * rep g y)
    (d : GaugeWeightDecomposition rep V) (w : GaugeWeight) :
    (d.pow hone hmul 0).piece w = if w = 0 then 1 else ⊥ := rfl

@[simp]
lemma pow_succ_piece (hone : ∀ g : GaugeGroupI, rep g 1 = 1)
    (hmul : ∀ (g : GaugeGroupI) (x y : B), rep g (x * y) = rep g x * rep g y)
    (d : GaugeWeightDecomposition rep V) (k : ℕ) (w : GaugeWeight) :
    (d.pow hone hmul (k + 1)).piece w
      = ⨆ w₁, ⨆ w₂, ⨆ _ : w₁ + w₂ = w, (d.pow hone hmul k).piece w₁ * d.piece w₂ := rfl

/-- The `mul_piece_of_supp` collapse, applied to a power: only the weights in `S` that the
  decomposition actually carries contribute at each step. -/
lemma pow_succ_piece_of_supp (hone : ∀ g : GaugeGroupI, rep g 1 = 1)
    (hmul : ∀ (g : GaugeGroupI) (x y : B), rep g (x * y) = rep g x * rep g y)
    (d : GaugeWeightDecomposition rep V) (S : Finset GaugeWeight)
    (hS : ∀ v ∉ S, d.piece v = ⊥) (k : ℕ) (w : GaugeWeight) :
    (d.pow hone hmul (k + 1)).piece w
      = ⨆ v ∈ S, (d.pow hone hmul k).piece (w - v) * d.piece v :=
  mul_piece_of_supp hmul _ d S hS w

/-!

## F. Invariants

-/

/-- **The one-generator refinement step.** If a family of subspaces is graded along a single
  torus generator — the value of `f` at an index giving the eigenvalue exponent — then a
  vector fixed by that generator and lying in the span of the family already lies in the span
  of just those pieces on which `f` vanishes.

  This is the whole content of `mem_zero_of_invariant`, applied once per generator. At rank
  four no single generator separates the gauge weights, so the coordinates have to be peeled
  off one at a time rather than all at once. -/
lemma mem_iSup_of_fixed {ι : Type*} {T : Module.End ℂ B} {p : ι → Submodule ℂ B} {f : ι → ℤ}
    (hp : ∀ j, p j ≤ Module.End.eigenspace T ((expI : ℂ) ^ f j))
    {x : B} (hx : x ∈ ⨆ j, p j) (hT : T x = x) :
    x ∈ ⨆ j, ⨆ _ : f j = 0, p j := by
  have hQle : ∀ k : ℤ, (⨆ j, ⨆ _ : f j = k, p j)
      ≤ Module.End.eigenspace T ((expI : ℂ) ^ k) :=
    fun k => iSup₂_le fun j hj => hj ▸ hp j
  have hQsup : (⨆ k : ℤ, ⨆ j, ⨆ _ : f j = k, p j) = ⨆ j, p j := by
    rw [iSup_comm]
    exact iSup_congr fun j =>
      le_antisymm (iSup₂_le fun _ _ => le_rfl) (le_iSup₂_of_le (f j) rfl le_rfl)
  have hdisj : Disjoint (Module.End.eigenspace T ((expI : ℂ) ^ (0 : ℤ)))
      (⨆ k : ℤ, ⨆ _ : k ≠ (0 : ℤ), ⨆ j, ⨆ _ : f j = k, p j) :=
    (((Module.End.eigenspaces_iSupIndep T).comp expI_zpow_injective) 0).mono_right
      (iSup₂_mono fun k _ => hQle k)
  have key : (⨆ k : ℤ, ⨆ j, ⨆ _ : f j = k, p j)
      ⊓ Module.End.eigenspace T ((expI : ℂ) ^ (0 : ℤ)) ≤ ⨆ j, ⨆ _ : f j = 0, p j := by
    rw [iSup_split_single (fun k : ℤ => ⨆ j, ⨆ _ : f j = k, p j) 0,
      sup_inf_assoc_of_le _ (hQle 0)]
    exact sup_le le_rfl (hdisj.symm.le_bot.trans bot_le)
  refine key ⟨?_, Module.End.mem_eigenspace_iff.mpr ?_⟩
  · rw [hQsup]
    exact hx
  · rw [zpow_zero, one_smul]
    exact hT

/-- **A gauge-invariant element sits in the zero-weight piece.** Only invariance under the
  four torus generators is used. -/
lemma mem_zero_of_invariant (d : GaugeWeightDecomposition rep V) {x : B} (hx : x ∈ V)
    (hV : ∀ g : GaugeGroupI, rep g x = x) : x ∈ d.piece 0 := by
  have s0 : x ∈ ⨆ w, d.piece w := by rw [d.iSup_piece]; exact hx
  have s1 := mem_iSup_of_fixed (f := fun w : GaugeWeight => w.coord 0)
    (fun w => d.piece_le_eigenspace w 0) s0 (hV _)
  have s2 := mem_iSup_of_fixed (f := fun w : GaugeWeight => w.coord 1)
    (fun w => iSup_le fun _ => d.piece_le_eigenspace w 1) s1 (hV _)
  have s3 := mem_iSup_of_fixed (f := fun w : GaugeWeight => w.coord 2)
    (fun w => iSup_le fun _ => iSup_le fun _ => d.piece_le_eigenspace w 2) s2 (hV _)
  have s4 := mem_iSup_of_fixed (f := fun w : GaugeWeight => w.coord 3)
    (fun w => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ =>
      d.piece_le_eigenspace w 3) s3 (hV _)
  have hfin : ∀ w : GaugeWeight, (⨆ _ : w.coord 3 = 0, ⨆ _ : w.coord 2 = 0,
      ⨆ _ : w.coord 1 = 0, ⨆ _ : w.coord 0 = 0, d.piece w) ≤ d.piece 0 := by
    rintro ⟨a, b, c, e⟩
    refine iSup_le fun h3 => iSup_le fun h2 => iSup_le fun h1 => iSup_le fun h0 => ?_
    simp only [GaugeWeight.coord_zero, GaugeWeight.coord_one, GaugeWeight.coord_two,
      GaugeWeight.coord_three] at h0 h1 h2 h3
    subst h0
    subst h1
    subst h2
    subst h3
    exact le_rfl
  exact iSup_le hfin s4

end GaugeWeightDecomposition
end StandardModel
