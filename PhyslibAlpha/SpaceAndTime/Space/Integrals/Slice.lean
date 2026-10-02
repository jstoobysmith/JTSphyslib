/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.SpaceAndTime.Space.Slice
public import Physlib.SpaceAndTime.Space.Integrals.Basic
/-!

# Integrals over slices of `Space`

## i. Overview

The slicing map `Space.slice i : Space (d + 1) ≃L[ℝ] ℝ × Space d` is measure preserving, so
integrals over `Space (d + 1)` can be computed as iterated integrals over the `i`-th
coordinate and the remaining `Space d`.

## ii. Key results

- `Space.slice_measurePreserving` : the slicing map is measure preserving.
- `Space.integral_eq_integral_slice`, `Space.integral_eq_integral_slice'` : an integral over
  `Space (d + 1)` as an iterated integral, in either order.

## iii. Table of contents

- A. The volume on `ℝ` as a Haar measure
- B. The slicing map is measure preserving
- C. Integrals as iterated integrals

## iv. References

* None.
-/

@[expose] public section

open MeasureTheory

namespace Space

/-!

## A. The volume on `ℝ` as a Haar measure

-/

lemma real_volume_eq_singleton_addHaar :
    (volume : Measure ℝ) = (Module.Basis.singleton Unit ℝ).addHaar := by
  have hb : Orthonormal ℝ (Module.Basis.singleton Unit ℝ) :=
    orthonormal_iff_ite.mpr fun i j => by simp
  rw [← OrthonormalBasis.addHaar_eq_volume ((Module.Basis.singleton Unit ℝ).toOrthonormalBasis hb)]
  simp

/-!

## B. The slicing map is measure preserving

-/

lemma slice_apply_basis_self {d : ℕ} (i : Fin d.succ) :
    slice i (basis i) = (1, 0) := by
  rw [basis_self_eq_slice, ContinuousLinearEquiv.apply_symm_apply]

lemma slice_apply_basis_succAbove {d : ℕ} (i : Fin d.succ) (j : Fin d) :
    slice i (basis (Fin.succAbove i j)) = (0, basis j) := by
  rw [basis_succAbove_eq_slice, ContinuousLinearEquiv.apply_symm_apply]

/-- The slicing map identifies the volume on `Space (d + 1)` with the product of the volumes
on `ℝ` and on `Space d`. -/
lemma slice_measurePreserving {d : ℕ} (i : Fin d.succ) :
    MeasurePreserving (slice i) volume (volume.prod volume) := by
  refine ⟨(slice i).continuous.measurable, ?_⟩
  rw [volume_eq_addHaar, Module.Basis.map_addHaar, real_volume_eq_singleton_addHaar,
    volume_eq_addHaar, ← Module.Basis.prod_addHaar]
  let e : Fin d.succ ≃ Unit ⊕ Fin d :=
    (finSuccEquiv' i).trans ((Equiv.optionEquivSumPUnit (Fin d)).trans (Equiv.sumComm _ _))
  rw [← Module.Basis.addHaar_reindex _ e]
  congr 1
  refine DFunLike.ext _ _ fun j => ?_
  rcases j with ⟨⟩ | j
  · simp [e, Module.Basis.reindex_apply, Module.Basis.map_apply, slice_apply_basis_self]
  · simp [e, Module.Basis.reindex_apply, Module.Basis.map_apply, slice_apply_basis_succAbove]

/-!

## C. Integrals as iterated integrals

-/

lemma integral_eq_integral_slice {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (i : Fin d.succ) (f : Space d.succ → F) (hf : Integrable f) :
    ∫ x, f x = ∫ r : ℝ, ∫ y : Space d, f ((slice i).symm (r, y)) := by
  have hemb := (slice i).toHomeomorph.measurableEmbedding
  have h := (slice_measurePreserving i).integral_comp hemb (fun p => f ((slice i).symm p))
  simp only [ContinuousLinearEquiv.symm_apply_apply] at h
  rw [h, integral_prod]
  rw [← (slice_measurePreserving i).integrable_comp_emb hemb]
  simpa [Function.comp_def] using hf

lemma integral_eq_integral_slice' {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (i : Fin d.succ) (f : Space d.succ → F) (hf : Integrable f) :
    ∫ x, f x = ∫ y : Space d, ∫ r : ℝ, f ((slice i).symm (r, y)) := by
  have hemb := (slice i).toHomeomorph.measurableEmbedding
  have h := (slice_measurePreserving i).integral_comp hemb (fun p => f ((slice i).symm p))
  simp only [ContinuousLinearEquiv.symm_apply_apply] at h
  rw [h, integral_prod_symm]
  rw [← (slice_measurePreserving i).integrable_comp_emb hemb]
  simpa [Function.comp_def] using hf

end Space
