/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Nat.SuccPred
/-!

# Defining succSuccAbove

In Mathlib there is the `Fin.succAbove` function which gives an embedding of `Fin n` into
`Fin (n + 1)` by leaving a hole at a specified index. We will need a version of this which
gives an embedding of `Fin n` into `Fin (n + 1 + 1)` by leaving holes at
two specified indices. We call this `succSuccAbove`.

We will also need an explicit inverse of this map from
`Fin (n + 1 + 1)` to `Fin n` which is defined on the complement of the two specified indices.
This is similar to `Fin.predAbove` (although not exactly the same),
for this reason we call it `predPredAbove`.

## Implementation

In previous versions of Physlib the function which is now called `succSuccAbove`
was previously called `dropPairEmb` and the function which is now called `predPredAbove` was
previously called `dropPairEmbPre`.

-/

@[expose] public section

namespace Fin

variable {n : ℕ} {c : Fin (n + 1 + 1) → C}

/-!

## Defining succSuccAbove

-/

/-- The embedding of `Fin n` into `Fin (n + 1 + 1)` which leaves a hole
  at `i` and `j`. -/
def succSuccAbove (i j : Fin (n + 1 + 1)) (m : Fin n) : Fin (n + 1 + 1) :=
  if m.1 < i.1 ∧ m.1 < j.1 then
    ⟨m, by omega⟩
  else if m.1 + 1 < i.1 ∧ j.1 ≤ m.1 then
    ⟨m + 1, by omega⟩
  else if i.1 ≤ m.1 ∧ m.1 + 1 < j.1 then
    ⟨m + 1, by omega⟩
  else
    ⟨m + 2, by omega⟩

lemma succSuccAbove_self_apply (i : Fin (n + 1 + 1)) (m : Fin n) :
    succSuccAbove i i m = if m.1 < i.1 then ⟨m.1, by omega⟩ else ⟨m.1 + 2, by omega⟩ := by
  simp [succSuccAbove]
  grind

lemma succSuccAbove_eq_succAbove_succAbove (i : Fin (n + 1 + 1)) (j : Fin (n + 1)) :
    succSuccAbove i (i.succAbove j) = i.succAbove ∘ j.succAbove := by
  ext m
  simp [succSuccAbove, Fin.succAbove, Fin.lt_def]
  grind

lemma succSuccAbove_eq_predAbove {i j : Fin (n + 1 + 1)} (hij : i ≠ j) :
    succSuccAbove i j = fun x => (i.succAbove (((Fin.predAbove 0 i).predAbove j).succAbove x)) := by
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨j, rfl⟩
  · contradiction
  · ext x
    rw [succSuccAbove_eq_succAbove_succAbove, Function.comp_apply]
    congr
    rcases eq_or_ne i 0 with rfl | hi
    · rfl
    · rw [Fin.predAbove_zero_of_ne_zero hi]
      rcases lt_or_ge (i.pred hi).castSucc (i.succAbove j) with h | h
      · rw [Fin.predAbove_of_castSucc_lt _ _ h, Fin.pred_succAbove]
        rw [← Fin.lt_succAbove_iff_le_castSucc]
        exact lt_of_le_of_ne ((Fin.castSucc_pred_lt_iff hi).mp h) hij
      · rw [Fin.predAbove_of_le_castSucc _ _ h, Fin.castPred_succAbove]
        rw [Fin.castSucc_lt_iff_succ_le, ← Fin.succAbove_lt_iff_succ_le]
        exact (Fin.le_castSucc_pred_iff hi).mp h

lemma succSuccAbove_injective {n : ℕ}
    (i j : Fin (n + 1 + 1)) : Function.Injective (succSuccAbove i j) := by
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨j, rfl⟩
  · intro a b
    simp [succSuccAbove_self_apply]
    grind
  · rw [succSuccAbove_eq_succAbove_succAbove]
    exact Function.Injective.comp Fin.succAbove_right_injective Fin.succAbove_right_injective

@[simp]
lemma succSuccAbove_eq_iff_eq {n : ℕ}
    (i j : Fin (n + 1 + 1)) (m1 m2 : Fin n) :
    succSuccAbove i j m1 = succSuccAbove i j m2 ↔ m1 = m2 := by
  rw [(succSuccAbove_injective i j).eq_iff]

@[simp]
lemma succSuccAbove_leq_iff_leq {n : ℕ}
    (i j : Fin (n + 1 + 1)) (m1 m2 : Fin n) :
    succSuccAbove i j m1 ≤ succSuccAbove i j m2 ↔ m1 ≤ m2 := by
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨j, rfl⟩
  · simp [succSuccAbove_self_apply]
    grind
  · rw [succSuccAbove_eq_succAbove_succAbove]
    simp only [Function.comp_apply]
    rw [Fin.succAbove_le_succAbove_iff]
    rw [Fin.succAbove_le_succAbove_iff]

@[simp]
lemma succSuccAbove_lt_iff_lt {n : ℕ}
    (i j : Fin (n + 1 + 1)) (m1 m2 : Fin n) :
    succSuccAbove i j m1 < succSuccAbove i j m2 ↔ m1 < m2 := by
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨j, rfl⟩
  · simp [succSuccAbove_self_apply]
    grind
  · rw [succSuccAbove_eq_succAbove_succAbove]
    simp only [Function.comp_apply]
    rw [Fin.succAbove_lt_succAbove_iff]
    rw [Fin.succAbove_lt_succAbove_iff]

@[simp]
lemma succSuccAbove_monotone {n : ℕ} (i j : Fin (n + 1 + 1)) :
    Monotone (succSuccAbove i j) := by
  intro a b
  simp

lemma succSuccAbove_eq_orderEmbOfFin {n : ℕ}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j) :
    succSuccAbove i j = (Finset.orderEmbOfFin {i, j}ᶜ
    (by rw [Finset.card_compl]; simp [Finset.card_pair hij])) := by
  let succSuccAbove : Fin n ↪o Fin (n + 1 + 1) :=
  (Finset.orderEmbOfFin {i, j}ᶜ
  (by rw [Finset.card_compl]; simp [Finset.card_pair hij]))
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨j, rfl⟩
  · simp at hij
  rw [succSuccAbove_eq_succAbove_succAbove]
  symm
  let f : Fin n ↪o Fin (n + 1 + 1) :=
    ⟨⟨i.succAboveOrderEmb ∘ j.succAboveOrderEmb, by
      refine Function.Injective.comp ?_ ?_
      exact Fin.succAbove_right_injective
      exact Fin.succAbove_right_injective⟩, by
      simp only [Function.Embedding.coeFn_mk, Function.comp_apply, OrderEmbedding.le_iff_le,
        implies_true]⟩
  have hf : succSuccAbove = f := by
    rw [← OrderEmbedding.range_inj]
    simp only [Finset.range_orderEmbOfFin, Finset.coe_compl,
      RelEmbedding.coe_mk, Function.Embedding.coeFn_mk, succSuccAbove, f]
    change _ = Set.range (i.succAbove ∘ j.succAbove)
    rw [Set.range_comp]
    simp only [Fin.range_succAbove]
    ext a
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_image]
    apply Iff.intro
    · intro h
      have ha := Fin.eq_self_or_eq_succAbove i a
      simp_all [false_or]
      obtain ⟨a, rfl⟩ := ha
      use a
      simp_all only [and_true]
      rw [Fin.succAbove_right_injective.eq_iff] at h
      exact h.2
    · intro h
      obtain ⟨a, h1, rfl⟩ := h
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
        not_or]
      rw [Fin.succAbove_right_injective.eq_iff]
      simp_all only [not_false_eq_true, and_true]
      exact Fin.succAbove_ne i a
  ext a
  have hf' := congrFun (congrArg (fun x => x.toFun) hf) a
  simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding, Function.comp_apply,
    Fin.succAboveOrderEmb_apply, f] at hf'
  rw [hf']
  rfl

lemma succSuccAbove_symm (i j : Fin (n + 1 + 1)) :
    succSuccAbove i j = succSuccAbove j i := by
  by_cases hij : i = j
  · subst hij
    rfl
  rw [succSuccAbove_eq_orderEmbOfFin i j hij,
    succSuccAbove_eq_orderEmbOfFin j i (Ne.symm hij)]
  simp [Finset.pair_comm]

@[simp, nolint simpVarHead]
lemma permCond_succSuccAbove_symm {c : Fin (n + 1 + 1) → C} (i j : Fin (n + 1 + 1))
    (k : Fin n) : c (succSuccAbove i j k) = c (succSuccAbove j i k) := by
  rw [succSuccAbove_symm]

lemma succSuccAbove_apply_eq_orderIsoOfFin {i j : Fin (n + 1 + 1)} (hij : i ≠ j) (m : Fin n) :
    (succSuccAbove i j) m = (Finset.orderIsoOfFin {i, j}ᶜ
      (by rw [Finset.card_compl]; simp [Finset.card_pair hij])) m := by
  simp [succSuccAbove_eq_orderEmbOfFin i j hij]

@[simp]
lemma succSuccAbove_range {i j : Fin (n + 1 + 1)} (hij : i ≠ j) :
    Set.range (succSuccAbove i j) = {i, j}ᶜ := by
  rw [succSuccAbove_eq_orderEmbOfFin i j hij, Finset.range_orderEmbOfFin]
  simp only [Finset.compl_insert, Finset.coe_erase, Finset.coe_compl, Finset.coe_singleton]
  ext x : 1
  simp only [Set.mem_diff, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_insert_iff, not_or]
  apply Iff.intro
  · intro a
    simp_all only [not_false_eq_true, and_self]
  · intro a
    simp_all only [not_false_eq_true, and_self]

lemma succSuccAbove_image_compl {i j : Fin (n + 1 + 1)} (hij : i ≠ j)
    (X : Set (Fin n)) :
    (succSuccAbove i j) '' Xᶜ = ({i, j} ∪ succSuccAbove i j '' X)ᶜ := by
  rw [← compl_inj_iff, Function.Injective.compl_image_eq (succSuccAbove_injective i j)]
  simp only [compl_compl, succSuccAbove_range hij]
  exact Set.union_comm ((succSuccAbove i j) '' X) {i, j}

@[simp]
lemma fst_ne_succSuccAbove_pre (i j : Fin (n + 1 + 1)) (m : Fin n) :
    ¬ i = succSuccAbove i j m := by
  by_cases hij : i = j
  · subst hij
    simp [succSuccAbove_self_apply]
    grind
  · by_contra hn
    have hi : i ∉ Set.range (succSuccAbove i j) := by
      simp [succSuccAbove_eq_orderEmbOfFin i j hij]
    nth_rewrite 2 [hn] at hi
    simp [- succSuccAbove_range] at hi

@[simp]
lemma succSuccAbove_ne_fst (i j : Fin (n + 1 + 1)) (m : Fin n) :
    ¬ succSuccAbove i j m = i := by
  apply Ne.symm
  simp

@[simp]
lemma snd_ne_succSuccAbove_pre (i j : Fin (n + 1 + 1)) (m : Fin n) :
    ¬ j = (succSuccAbove i j) m := by
  rw [succSuccAbove_symm]
  exact fst_ne_succSuccAbove_pre j i m

@[simp]
lemma succSuccAbove_ne_snd (i j : Fin (n + 1 + 1)) (m : Fin n) :
    ¬ succSuccAbove i j m = j := by
  apply Ne.symm
  simp

lemma succSuccAbove_succAbove {n : ℕ}
    (i : Fin (n + 1 + 1)) (j : Fin (n + 1)) :
    succSuccAbove i (i.succAbove j) = i.succAbove ∘ j.succAbove := by
  exact succSuccAbove_eq_succAbove_succAbove i j

lemma eq_or_exists_succSuccAbove(i j : Fin (n + 1 + 1)) (hij : i ≠ j) (m : Fin (n + 1 + 1)) :
    m = i ∨ m = j ∨ ∃ m', m = succSuccAbove i j m' := by
  by_cases h : m = i
  · subst h
    simp
  · by_cases h' : m = j
    · subst h'
      simp
    · simp_all only [false_or]
      have h'' : m ∈ Set.range (succSuccAbove i j) := by
        simp_all [succSuccAbove_eq_orderEmbOfFin]
      rw [@Set.mem_range] at h''
      obtain ⟨m', rfl⟩ := h''
      exact ⟨m', rfl⟩


lemma succSuccAbove_apply_lt_lt {n : ℕ}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j)
    (m : Fin n) (hi : m.val < i.val) (hj : m.val < j.val) :
    succSuccAbove i j m = m.castSucc.castSucc := by
  rcases Fin.eq_self_or_eq_succAbove i j with hj' | hj'
  · subst hj'
    simp at hij
  obtain ⟨j, rfl⟩ := hj'
  rw [succSuccAbove_succAbove]
  simp only [Function.comp_apply]
  have hj'' : m.val < j.val := by
    simp_all only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, ne_eq]
    grind
  rw [Fin.succAbove_of_succ_le, Fin.succAbove_of_succ_le]
  · simp only [Fin.le_def, Fin.val_succ]
    omega
  · simp_all only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, ne_eq, ite_true, Fin.le_def,
    Fin.val_succ]
    omega

set_option backward.isDefEq.respectTransparency false in
lemma succSuccAbove_natAdd_apply_castAdd {n n1 : ℕ}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j)
    (m : Fin n1) :
    (succSuccAbove (n := n1 + n) (Fin.natAdd n1 i) (Fin.natAdd n1 j))
    (Fin.castAdd n m)
    = Fin.castAdd (n + 1 + 1) (m) := by
  rw [succSuccAbove_apply_lt_lt]
  · simp [Fin.ext_iff]
  · simp_all [Fin.ne_iff_vne]
  · simp only [Fin.val_castAdd, Fin.val_natAdd]
    omega
  · simp only [Fin.val_castAdd, Fin.val_natAdd]
    omega

lemma succSuccAbove_natAdd_image_range_castAdd {n n1 : ℕ}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j) :
    (succSuccAbove (n := n1 + n) (Fin.natAdd n1 i) (Fin.natAdd n1 j)) ''
    (Set.range (Fin.castAdd (m := n) (n := n1))) = {i | i.1 < n1} := by
  ext a
  simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and, Set.mem_setOf_eq]
  conv_lhs =>
    enter [1, b]
    rw [succSuccAbove_natAdd_apply_castAdd i j hij]
  apply Iff.intro
  · intro h
    obtain ⟨b, rfl⟩ := h
    simp
  · intro h
    use ⟨a, by omega⟩
    simp

set_option backward.isDefEq.respectTransparency false in
lemma succSuccAbove_comm_natAdd {n n1 : ℕ}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j)
    (m : Fin n) :
    (succSuccAbove (n := n1 + n) (Fin.natAdd n1 i) (Fin.natAdd n1 j))
    (Fin.natAdd n1 m)
    = Fin.natAdd (n1) (succSuccAbove i j m) := by
  let f : Fin n ↪o Fin (n1 + n + 1 + 1) :=
    ⟨⟨(succSuccAbove (Fin.natAdd n1 i) (Fin.natAdd n1 j))
    ∘ Fin.natAdd n1, by
      intro i j
      simp only [Function.comp_apply, succSuccAbove_eq_iff_eq]
      simp [Fin.ext_iff]⟩, by
      intro a b
      simp only [Function.Embedding.coeFn_mk, Function.comp_apply, succSuccAbove_leq_iff_leq]
      rw [Fin.le_def, Fin.le_def]
      simp⟩
  let g : Fin n ↪o Fin (n1 + n + 1 + 1) :=
      ⟨⟨(Fin.natAdd (n1) ∘ succSuccAbove i j), by
      intro a b
      simp only [Function.comp_apply, Fin.ext_iff, Fin.val_natAdd, add_right_inj]
      simp [← Fin.ext_iff]⟩, by
      intro a b
      simp only [Function.Embedding.coeFn_mk, Function.comp_apply]
      rw [Fin.le_def, Fin.le_def]
      simp⟩
  have hcastRange : Set.range (Fin.castAdd (m := n) (n := n1)) = {i | i.1 < n1} := by
    rw [@Set.range_eq_iff]
    apply And.intro
    · intro a
      simp
    · intro b hb
      simp only [Set.mem_setOf_eq] at hb
      use ⟨b, by omega⟩
      simp
  have hnatRange : Set.range (Fin.natAdd (m := n) n1) =
    (Set.range (Fin.castAdd (m := n) (n := n1)))ᶜ := by
    rw [hcastRange]
    rw [@Set.range_eq_iff]
    apply And.intro
    · intro a
      simp
    · intro b hb
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hb
      use ⟨b - n1, by omega⟩
      simp only [Fin.natAdd_mk, Fin.ext_iff]
      omega
  have hfg : f = g := by
    rw [← OrderEmbedding.range_inj]
    simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk, f, g]
    rw [Set.range_comp, Set.range_comp]
    simp only [succSuccAbove_range hij]
    rw [hnatRange]
    rw [succSuccAbove_image_compl]
    simp only [Set.compl_union]
    rw [succSuccAbove_natAdd_image_range_castAdd i j hij]
    ext a
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      not_or, Set.mem_setOf_eq, not_lt, Set.mem_image]
    apply Iff.intro
    · intro h
      use ⟨a - n1, by omega⟩
      simp only [Fin.ext_iff, Fin.val_natAdd, Fin.natAdd_mk] at h ⊢
      omega
    · intro h
      obtain ⟨x, h1, rfl⟩ := h
      simp_all [Fin.ext_iff]
    · simp_all [Fin.ext_iff]
  simpa using congrFun (congrArg (fun x => x.toFun) hfg) m


/-!

## predPredAbove

-/

/-- The preimage of `m` under `succSuccAbove i j hij` given that `m` is not equal
  to `i` or `j`. -/
def predPredAbove (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (m : Fin (n + 1 + 1))
    (hm : m ≠ i ∧ m ≠ j) : Fin n :=
  if h1 : m.1 < i.1 ∧ m.1 < j.1 then
        ⟨m, by fin_omega⟩
      else if h2 : m.1 - 1 < i.1 ∧ j.1 ≤ m.1 then
        ⟨m - 1, by fin_omega⟩
      else if h3 : i.1 - 1 ≤ m.1 ∧ m.1 < j.1 then
        ⟨m - 1, by fin_omega⟩
      else
        ⟨m - 2, by fin_omega⟩

@[simp]
lemma succSuccAbove_predPredAbove (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (m : Fin (n + 1 + 1))
    (hm : m ≠ i ∧ m ≠ j) :
    succSuccAbove i j (predPredAbove i j hij m hm) = m := by
  dsimp [succSuccAbove, predPredAbove]
  split_ifs
  · rfl
  all_goals
    simp_all [Fin.ext_iff]
    try omega

set_option backward.isDefEq.respectTransparency false in
lemma predPredAbove_eq_orderIsoOfFin (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (m : Fin (n + 1 + 1))
    (hm : m ≠ i ∧ m ≠ j) :
    predPredAbove i j hij m hm =
    (Finset.orderIsoOfFin {i, j}ᶜ (by rw [Finset.card_compl]; simp [Finset.card_pair hij])).symm
    ⟨m, by simp [hm]⟩ := by
  apply succSuccAbove_injective i j
  conv_rhs => rw [succSuccAbove_apply_eq_orderIsoOfFin hij]
  simp

@[simp]
lemma predPredAbove_injective (i j : Fin (n + 1 + 1)) (hij : i ≠ j)
    (m1 m2 : Fin (n + 1 + 1)) (hm1 : m1 ≠ i ∧ m1 ≠ j) (hm2 : m2 ≠ i ∧ m2 ≠ j) :
    predPredAbove i j hij m1 hm1 = predPredAbove i j hij m2 hm2 ↔ m1 = m2 := by
  rw [← Function.Injective.eq_iff (succSuccAbove_injective i j)]
  simp

lemma predPredAbove_surjective (i j : Fin (n + 1 + 1)) (hij : i ≠ j)
    (m : Fin n) :
    ∃ m' : Fin (n + 1 + 1), ∃ (h : m' ≠ i ∧ m' ≠ j),
    predPredAbove i j hij m' h = m := by
  use (succSuccAbove i j) m
  have h : (succSuccAbove i j) m ≠ i ∧ (succSuccAbove i j) m ≠ j := by
    simp [Ne.symm]
  use h
  apply (succSuccAbove_injective i j)
  simp

@[simp]
lemma predPredAbove_succSuccAbove (i j : Fin (n + 1 + 1)) (hij : i ≠ j)
    (m : Fin n) :
    predPredAbove i j hij (succSuccAbove i j m) (by simp) = m := by
  apply succSuccAbove_injective i j
  simp

/-!

## Commutativity of succSuccAbove

-/
lemma succSuccAbove_comm (i1 j1 : Fin (n + 1 + 1 + 1 + 1)) (i2 j2 : Fin (n + 1 + 1))
    (hij1 : i1 ≠ j1) (hij2 : i2 ≠ j2) :
    let i2' := (succSuccAbove i1 j1 i2);
    let j2' := (succSuccAbove i1 j1 j2);
    have hi2j2' : i2' ≠ j2' := by simp [i2', j2', hij2];
    let i1' := (predPredAbove i2' j2' hi2j2' i1 (by simp [i2', j2']));
    let j1' := (predPredAbove i2' j2' hi2j2' j1 (by simp [i2', j2']));
    succSuccAbove i1 j1 ∘ succSuccAbove i2 j2 =
    succSuccAbove i2' j2' ∘
    succSuccAbove i1' j1':= by
  intro i2' j2' hi2j2'
  let fl : Fin n ↪o Fin (n + 1 + 1 + 1 + 1) :=
    ⟨⟨succSuccAbove i1 j1 ∘ succSuccAbove i2 j2, by
      apply Function.Injective.comp
      exact succSuccAbove_injective i1 j1
      exact succSuccAbove_injective _ _⟩, by simp only [Function.Embedding.coeFn_mk,
        Function.comp_apply, succSuccAbove_leq_iff_leq, implies_true]⟩
  let fr : Fin n ↪o Fin (n + 1 + 1 + 1 + 1) :=
    ⟨⟨succSuccAbove i2' j2' ∘ succSuccAbove
      (predPredAbove i2' j2' hi2j2' i1 (by simp [i2', j2']))
      (predPredAbove i2' j2' hi2j2' j1 (by simp [i2', j2'])),
      by
      apply Function.Injective.comp
      exact succSuccAbove_injective _ _
      exact succSuccAbove_injective _ _⟩, by simp only [Function.Embedding.coeFn_mk,
        Function.comp_apply, succSuccAbove_leq_iff_leq, implies_true]⟩
  have h : fl = fr := by
    rw [← OrderEmbedding.range_inj]
    simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk, Set.range_comp,
      succSuccAbove_range hij2, fl, fr, j2', i2']
    rw [succSuccAbove_range (by simp [hij1])]
    rw [succSuccAbove_image_compl, succSuccAbove_image_compl]
    congr 1
    rw [Set.image_pair, Set.image_pair]
    simp only [succSuccAbove_predPredAbove, i2', j2']
    exact Set.union_comm {i1, j1} {(succSuccAbove i1 j1) i2, (succSuccAbove i1 j1) j2}
    simp [hij2]
    simp [hij1]
  ext1 a
  have h' := congrFun (congrArg (fun x => x.toFun) h) a
  dsimp [fl, fr] at h'
  exact h'

lemma succSuccAbove_comm_apply (i1 j1 : Fin (n + 1 + 1 + 1 + 1)) (i2 j2 : Fin (n + 1 + 1))
    (hij1 : i1 ≠ j1) (hij2 : i2 ≠ j2) (m : Fin n) :
    let i2' := (succSuccAbove i1 j1 i2);
    let j2' := (succSuccAbove i1 j1 j2);
    have hi2j2' : i2' ≠ j2' := by simp [i2', j2', hij2];
    let i1' := (predPredAbove i2' j2' hi2j2' i1 (by simp [i2', j2']));
    let j1' := (predPredAbove i2' j2' hi2j2' j1 (by simp [i2', j2']));
    succSuccAbove i2' j2'
    (succSuccAbove i1' j1' m) =
    succSuccAbove i1 j1 (succSuccAbove i2 j2 m) := by
  intro i2' j2' hi2j2' i1' j1'
  change _ = (succSuccAbove i1 j1 ∘ succSuccAbove i2 j2) m
  rw [succSuccAbove_comm i1 j1 i2 j2 hij1 hij2]
  rfl

/-!

## funPredPredAbove

-/

/-- Given a bijection `Fin (n1 + 1 + 1) → Fin (n + 1 + 1))` and a pair `i j : Fin (n1 + 1 + 1)`,
  then `funPredPredAbove i j _ σ _ : Fin n1 → Fin n` corresponds to the induced bijection
  formed by dropping `i` and `j` in the source and their image in the target. -/
def funPredPredAbove {n n1 : ℕ} (i j : Fin (n1 + 1 + 1)) (hij : i ≠ j)
    (σ : Fin (n1 + 1 + 1) → Fin (n + 1 + 1)) (hσ : Function.Bijective σ)
    (m : Fin n1) : Fin n :=
  predPredAbove (σ i) (σ j)
    (by simp [hσ.injective.eq_iff, hij])
    (σ (succSuccAbove i j m)) (by simp [hσ.injective.eq_iff, Ne.symm])

lemma funPredPredAbove_injective {n n1 : ℕ} (i j : Fin (n1 + 1 + 1)) (hij : i ≠ j)
    (σ : Fin (n1 + 1 + 1) → Fin (n + 1 + 1)) (hσ : Function.Bijective σ) :
    Function.Injective (funPredPredAbove i j hij σ hσ) := by
  intro m1 m2 h
  simpa [funPredPredAbove, hσ.injective.eq_iff] using h

lemma funPredPredAbove_surjective {n n1 : ℕ} (i j : Fin (n1 + 1 + 1)) (hij : i ≠ j)
    (σ : Fin (n1 + 1 + 1) → Fin (n + 1 + 1)) (hσ : Function.Bijective σ) :
    Function.Surjective (funPredPredAbove i j hij σ hσ) := by
  intro m
  simp only [funPredPredAbove]
  obtain ⟨m, hm, rfl⟩ := predPredAbove_surjective (σ i) (σ j)
    (by simp [hσ.injective.eq_iff, hij]) m
  simp only [predPredAbove_injective]
  obtain ⟨m', rfl⟩ := hσ.surjective m
  simp only [ne_eq, hσ.injective.eq_iff] at hm ⊢
  rcases eq_or_exists_succSuccAbove i j hij m' with rfl | rfl | ⟨m'', rfl⟩
  · simp_all
  · simp_all
  · exact ⟨m'', rfl⟩

lemma funPredPredAbove_bijective {n n1 : ℕ} (i j : Fin (n1 + 1 + 1)) (hij : i ≠ j)
    (σ : Fin (n1 + 1 + 1) → Fin (n + 1 + 1)) (hσ : Function.Bijective σ) :
    Function.Bijective (funPredPredAbove i j hij σ hσ) := by
  apply And.intro
  · apply funPredPredAbove_injective
  · apply funPredPredAbove_surjective

@[simp]
lemma funPredPredAbove_id { n1 : ℕ} (i j : Fin (n1 + 1 + 1)) (hij : i ≠ j) :
    funPredPredAbove i j hij id (Function.bijective_id) = id := by
  ext1 m
  simp [funPredPredAbove]

end Fin
