/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.HyperchargeDecomposition
/-!
# Isospin decompositions

## i. Overview

An **isospin decomposition** of a submodule `V` is a finitely supported family of subspaces
of pure weak isospin whose supremum is `V`. Weights are normalized as `2T₃`, so the two
components of a doublet carry weights `+1` and `-1`.

This is the weak-isospin twin of `HyperchargeDecomposition`, and it is built the same way.
Purity is recorded against a single element of the maximal torus of the `SU(2)` factor, the
transformation by `diag (exp i, exp (-i))`: the isospin-`k` piece consists of the vectors
scaled by `(exp i) ^ k`. Because that element has infinite order, the eigenvalues
`(exp i) ^ k` are pairwise distinct — `expI_zpow_injective`, the very same lemma the
hypercharge file uses — so the pieces are independent with no assumption on the
representation.

## ii. A warning: weight zero is weaker than invariance

For the abelian `U(1)` factor, hypercharge zero *is* the charge singlet condition. For the
non-abelian `SU(2)` factor this fails: `mem_zero_of_invariant` below is a genuine one-way
implication and there is no converse. The torus does not separate the isospin singlet from
the neutral component of a higher isospin multiplet — `H†H` and `H†σ³H` both have isospin
weight zero, but only the first is invariant.

So this file provides a *sieve*, not a characterization: it narrows the candidates for an
invariant, and the survivors must still be checked directly. The same caveat attaches to the
boost-weight grading in `Grading/BoostWeight.lean`, and for the same reason.

## iii. Key results

- `su2ExpI` : the `SU(2)` torus element `diag (exp i, exp (-i))`, of infinite order.
- `IsospinDecomposition` : a finitely supported family of pure-isospin subspaces with
  supremum `V`.
- `IsospinDecomposition.sup` : two decompositions combine weightwise into one of `V ⊔ V'`.
- `IsospinDecomposition.mem_zero_of_invariant` : a gauge-invariant element lies in the
  isospin-zero piece.

## iv. Table of contents

- A. The `SU(2)` torus element
- B. Isospin decompositions
- C. Invariants

-/

@[expose] public section

namespace StandardModel

open Matrix

/-!

## A. The `SU(2)` torus element

-/

/-- The `SU(2)` torus element `diag (exp i, exp (-i))`. Like `expI` it has infinite order,
  so its powers are pairwise distinct and it separates the isospin weights. -/
noncomputable def su2ExpI : specialUnitaryGroup (Fin 2) ℂ :=
  ⟨!![(expI : ℂ), 0; 0, star (expI : ℂ)], by
    have hms : (expI : ℂ) * (starRingEnd ℂ) (expI : ℂ) = 1 :=
      Unitary.mul_star_self_of_mem expI.2
    have hsm : (starRingEnd ℂ) (expI : ℂ) * (expI : ℂ) = 1 :=
      Unitary.star_mul_self_of_mem expI.2
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff]
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, star_eq_conjTranspose,
          Matrix.conjTranspose_apply, hms, hsm]
    · simp [Matrix.det_fin_two_of, hms]⟩

/-- The inverse of `exp i` is its star. -/
lemma expI_inv_eq_star : ((expI : ℂ))⁻¹ = star (expI : ℂ) :=
  inv_eq_of_mul_eq_one_right (Unitary.mul_star_self_of_mem expI.2)

lemma su2ExpI_coe :
    (su2ExpI : specialUnitaryGroup (Fin 2) ℂ).1 = !![(expI : ℂ), 0; 0, star (expI : ℂ)] := rfl

/-- The inverse torus element is `diag (exp (-i), exp i)`: on a doublet the two components
  are scaled by `(exp i) ^ (-1)` and `(exp i) ^ 1`. -/
lemma su2ExpI_inv_coe :
    (su2ExpI⁻¹ : specialUnitaryGroup (Fin 2) ℂ).1
      = !![star (expI : ℂ), 0; 0, (expI : ℂ)] := by
  rw [← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star, su2ExpI_coe]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

/-!

## B. Isospin decompositions

-/

variable {B : Type*} [Ring B] [Algebra ℂ B]

/-- An **isospin decomposition** of a submodule `V`: a finitely supported family of
  subspaces of pure weak isospin whose supremum is `V`. Purity is recorded against the
  single torus transformation `su2ExpI`, which is enough to force the pieces to be
  independent.

  Isospin weight zero is necessary but *not* sufficient for `SU(2)` invariance; see the
  warning in the module docstring. -/
structure IsospinDecomposition (rep : Representation ℂ GaugeGroupI B)
    (V : Submodule ℂ B) where
  /-- The isospin `k` piece of the decomposition, at weight `k = 2T₃`. -/
  piece : ℤ → Submodule ℂ B
  /-- The finite set of isospin weights that occur. -/
  supp : Finset ℤ
  /-- Each piece is of pure isospin, as seen by the torus transformation `su2ExpI`. -/
  piece_le : ∀ k, ∀ x, x ∈ piece k → rep ⟨1, su2ExpI, 1⟩ x = ((expI : ℂ) ^ k) • x
  /-- Only the isospin weights in `supp` occur. -/
  piece_eq_bot : ∀ k ∉ supp, piece k = ⊥
  /-- The pieces exhaust `V`. -/
  iSup_piece : (⨆ k, piece k) = V

namespace IsospinDecomposition

variable {rep : Representation ℂ GaugeGroupI B} {V V' : Submodule ℂ B}

/-- The isospin-`k` piece lies in the `(exp i) ^ k` eigenspace of the torus transformation
  `su2ExpI`. This is `piece_le` phrased as an inequality of submodules. -/
lemma piece_le_eigenspace (h : IsospinDecomposition rep V) (k : ℤ) :
    h.piece k ≤ Module.End.eigenspace (rep ⟨1, su2ExpI, 1⟩) ((expI : ℂ) ^ k) :=
  fun _ hy => Module.End.mem_eigenspace_iff.mpr (h.piece_le k _ hy)

/-- The join of two isospin decompositions: the pieces, supports and suprema all combine
  weightwise, decomposing `V ⊔ V'`. -/
noncomputable def sup (h : IsospinDecomposition rep V) (h' : IsospinDecomposition rep V') :
    IsospinDecomposition rep (V ⊔ V') where
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

/-- **A gauge-invariant element sits in the isospin-zero piece.** Only invariance under the
  single torus transformation `su2ExpI` is used: the other pieces lie in eigenspaces for the
  eigenvalues `(exp i) ^ k`, all distinct from `1`.

  There is no converse: the isospin-zero piece is strictly larger than the `SU(2)`
  invariants whenever a higher isospin multiplet occurs in `V`. -/
lemma mem_zero_of_invariant (h : IsospinDecomposition rep V) {x : B} (hx : x ∈ V)
    (hV : ∀ g : GaugeGroupI, rep g x = x) : x ∈ h.piece 0 := by
  have hdisj : Disjoint
      (Module.End.eigenspace (rep ⟨1, su2ExpI, 1⟩) ((expI : ℂ) ^ (0 : ℤ)))
      (⨆ k, ⨆ _ : k ≠ (0 : ℤ), h.piece k) :=
    (((Module.End.eigenspaces_iSupIndep (rep ⟨1, su2ExpI, 1⟩ : Module.End ℂ B)).comp
      expI_zpow_injective) 0).mono_right (iSup₂_mono fun k _ => h.piece_le_eigenspace k)
  have key : (⨆ k, h.piece k)
      ⊓ Module.End.eigenspace (rep ⟨1, su2ExpI, 1⟩) ((expI : ℂ) ^ (0 : ℤ)) ≤ h.piece 0 := by
    rw [iSup_split_single h.piece 0, sup_inf_assoc_of_le _ (h.piece_le_eigenspace 0)]
    exact sup_le le_rfl (hdisj.symm.le_bot.trans bot_le)
  refine key ⟨?_, Module.End.mem_eigenspace_iff.mpr ?_⟩
  · rw [h.iSup_piece]
    exact hx
  · rw [zpow_zero, one_smul]
    exact hV _

end IsospinDecomposition
end StandardModel
