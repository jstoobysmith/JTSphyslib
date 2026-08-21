/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Analysis.Real.Pi.Irrational
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
/-!
# Hypercharge decompositions

## i. Overview

A **hypercharge decomposition** of a submodule `V` is a finitely supported family of
subspaces of pure hypercharge whose supremum is `V`. Charges are normalized as `6Y`.

Purity is recorded against a *single* group element, the transformation by `exp i`: the
hypercharge-`k` piece consists of the vectors scaled by `(exp i) ^ k`. That is already
enough to make the pieces independent, with no assumption on the representation, because
`exp i` is not a root of unity — the powers `(exp i) ^ k` are pairwise distinct by the
irrationality of `π`, so the pieces sit in eigenspaces of one operator at pairwise
distinct eigenvalues.

Exhibiting a decomposition therefore collapses the per-span boilerplate. The chief
consequence is that a gauge-invariant element of `V` lies in the hypercharge-zero piece;
only invariance under the transformation by `exp i` is used.

## ii. Key results

- `expI` : the unitary scalar `exp i`, a point of the unit circle of infinite order.
- `expI_zpow_injective` : the powers of `exp i` are pairwise distinct.
- `HyperchargeDecomposition` : a finitely supported family of pure-hypercharge subspaces
  with supremum `V`.
- `HyperchargeDecomposition.sup` : two decompositions combine weightwise into one of
  `V ⊔ V'`.
- `HyperchargeDecomposition.mem_zero_of_invariant` : a gauge-invariant element lies in the
  hypercharge-zero piece.

## iii. Table of contents

- A. The transformation by `exp i`
- B. Hypercharge decompositions
- C. Invariants

-/

@[expose] public section

namespace StandardModel

/-!

## A. The transformation by `exp i`

-/

/-- The unitary scalar `exp i`: a point of the unit circle of infinite order. -/
noncomputable def expI : unitary ℂ :=
  ⟨Complex.exp Complex.I, by
    have hstar : star (Complex.exp Complex.I) = Complex.exp (-Complex.I) := by
      rw [show star (Complex.exp Complex.I)
          = (starRingEnd ℂ) (Complex.exp Complex.I) from rfl, ← Complex.exp_conj,
        Complex.conj_I]
    constructor
    · rw [hstar, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    · rw [hstar, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]⟩

/-- The powers of `exp i` are pairwise distinct: `exp i` is not a root of unity, by the
  irrationality of `π`. -/
lemma expI_zpow_injective : Function.Injective fun n : ℤ => ((expI : ℂ) ^ n) := by
  intro a b hab
  simp only [show ((expI : ℂ)) = Complex.exp Complex.I from rfl,
    ← Complex.exp_int_mul] at hab
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hab
  have hℂ : ((a : ℂ)) = b + k * (2 * (Real.pi : ℂ)) := by
    refine mul_right_cancel₀ Complex.I_ne_zero ?_
    rw [hk]
    ring
  have hℝ : ((a : ℝ)) = b + k * (2 * Real.pi) := by
    have h := congrArg Complex.re hℂ
    simpa using h
  rcases eq_or_ne k 0 with rfl | hk0
  · exact_mod_cast (by simpa using hℝ : ((a : ℝ)) = b)
  · exfalso
    refine irrational_pi ⟨(a - b) / (2 * k), ?_⟩
    have h2k : ((2 * k : ℝ)) ≠ 0 :=
      mul_ne_zero two_ne_zero (Int.cast_ne_zero.mpr hk0)
    push_cast
    rw [div_eq_iff h2k]
    linarith [hℝ]

/-!

## B. Hypercharge decompositions

-/

variable {B : Type*} [Ring B] [Algebra ℂ B]

/-- A **hypercharge decomposition** of a submodule `V`: a finitely supported family of
  subspaces of pure hypercharge whose supremum is `V`. Purity is recorded against the
  single transformation by `exp i`, which is enough to force the pieces to be
  independent. -/
structure HyperchargeDecomposition (rep : Representation ℂ GaugeGroupI B)
    (V : Submodule ℂ B) where
  /-- The hypercharge `k` piece of the decomposition. -/
  piece : ℤ → Submodule ℂ B
  /-- The finite set of hypercharges that occur. -/
  supp : Finset ℤ
  /-- Each piece is of pure hypercharge, as seen by the transformation by `exp i`. -/
  piece_le : ∀ k, ∀ x, x ∈ piece k → rep ⟨1, 1, expI⟩ x = ((expI : ℂ) ^ k) • x
  /-- Only the hypercharges in `supp` occur. -/
  piece_eq_bot : ∀ k ∉ supp, piece k = ⊥
  /-- The pieces exhaust `V`. -/
  iSup_piece : (⨆ k, piece k) = V

namespace HyperchargeDecomposition

variable {rep : Representation ℂ GaugeGroupI B} {V V' : Submodule ℂ B}

/-- The hypercharge-`k` piece lies in the `(exp i) ^ k` eigenspace of the transformation
  by `exp i`. This is `piece_le` phrased as an inequality of submodules. -/
lemma piece_le_eigenspace (h : HyperchargeDecomposition rep V) (k : ℤ) :
    h.piece k ≤ Module.End.eigenspace (rep ⟨1, 1, expI⟩) ((expI : ℂ) ^ k) :=
  fun _ hy => Module.End.mem_eigenspace_iff.mpr (h.piece_le k _ hy)

/-- The join of two hypercharge decompositions: the pieces, supports and suprema all
  combine weightwise, decomposing `V ⊔ V'`. -/
noncomputable def sup (h : HyperchargeDecomposition rep V) (h' : HyperchargeDecomposition rep V') :
    HyperchargeDecomposition rep (V ⊔ V') where
  piece k := h.piece k ⊔ h'.piece k
  supp := h.supp ∪ h'.supp
  piece_le k x hx :=
    Module.End.mem_eigenspace_iff.mp
      (sup_le (h.piece_le_eigenspace k) (h'.piece_le_eigenspace k) hx)
  piece_eq_bot k hk := by
    rw [Finset.mem_union, not_or] at hk
    rw [h.piece_eq_bot k hk.1, h'.piece_eq_bot k hk.2, bot_sup_eq]
  iSup_piece := by
    rw [iSup_sup_eq, h.iSup_piece, h'.iSup_piece]

/-!

## C. Invariants

-/

/-- **A gauge-invariant element sits in the hypercharge-zero piece.** Only invariance
  under the single `U(1)` transformation by `exp i` is used: the other pieces lie in
  eigenspaces for the eigenvalues `(exp i) ^ k`, all distinct from `1`. -/
lemma mem_zero_of_invariant (h : HyperchargeDecomposition rep V) {x : B} (hx : x ∈ V)
    (hV : ∀ g : GaugeGroupI, rep g x = x) : x ∈ h.piece 0 := by
  have hdisj : Disjoint
      (Module.End.eigenspace (rep ⟨1, 1, expI⟩) ((expI : ℂ) ^ (0 : ℤ)))
      (⨆ k, ⨆ _ : k ≠ (0 : ℤ), h.piece k) :=
    (((Module.End.eigenspaces_iSupIndep (rep ⟨1, 1, expI⟩ : Module.End ℂ B)).comp
      expI_zpow_injective) 0).mono_right (iSup₂_mono fun k _ => h.piece_le_eigenspace k)
  have key : (⨆ k, h.piece k)
      ⊓ Module.End.eigenspace (rep ⟨1, 1, expI⟩) ((expI : ℂ) ^ (0 : ℤ)) ≤ h.piece 0 := by
    rw [iSup_split_single h.piece 0, sup_inf_assoc_of_le _ (h.piece_le_eigenspace 0)]
    exact sup_le le_rfl (hdisj.symm.le_bot.trans bot_le)
  refine key ⟨?_, Module.End.mem_eigenspace_iff.mpr ?_⟩
  · rw [h.iSup_piece]
    exact hx
  · rw [zpow_zero, one_smul]
    exact hV _

end HyperchargeDecomposition
end StandardModel
