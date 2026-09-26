/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.IsSU2BiAdjoint
/-!
# Gauge tensors carrying one `su(2)` adjoint index

A single `W`-boson field strength `W^a` carries one isospin index, running over the three Pauli
directions of `su(2)`, and transforms in the adjoint representation, which is the vector
representation `3` of the rotation group. That representation contains no singlet: no linear
combination of the three components is left alone by every isospin rotation, which is why a
Lagrangian never contains a term linear in a field strength. Modulo an isospin-stable
submodule `S`, every isospin invariant of the span of the components lies in `S`.

`IsSU2Adjoint B repGauge T` records the transformation law: an isospin rotation `U ∈ SU(2)`
moves the components by the adjoint matrix of `U`, the summed index in the row slot, so the
law acts on coefficient vectors by `su2AdjointCoeffMatrix U` of `IsSU2BiAdjoint`. Nothing is
asked of the colour and hypercharge factors.

The three isospin flips show that no nonzero coefficient vector is fixed: the half turn about
the axis `a + 1` reverses the direction `a`, so a fixed coefficient vector is its own negative
in every coordinate.

- A. The transformation law
- B. No coefficient vector is fixed
- C. The reduction modulo a stable submodule
-/

@[expose] public section

namespace StandardModel

open Matrix IsSU2BiAdjoint

/-!

## A. The transformation law

The law carries one factor of the adjoint matrix, with the summed index in the row slot,
exactly as each of the two indices of a bi-adjoint family does.

-/

/-- The linear map `f` moves the components of `T` as `U ∈ SU(2)` moves a tensor with one
  adjoint index. -/
def IsSU2AdjointMat {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (U : specialUnitaryGroup (Fin 2) ℂ) (f : B →ₗ[ℂ] B) (T : Fin 3 → B) : Prop :=
  ∀ l : Fin 3, f (T l) = ∑ a : Fin 3, ((su2AdjointMatrix U a l : ℝ) : ℂ) • T a

/-- A family `T` of elements of `B`, indexed by one `su(2)` adjoint index, transforms as a
  tensor `T^a` under the isospin factor of the gauge group. Nothing is asked of the colour
  and hypercharge factors. -/
structure IsSU2Adjoint (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B) (T : Fin 3 → B) : Prop where
  repGauge_T : ∀ g : specialUnitaryGroup (Fin 2) ℂ,
    IsSU2AdjointMat g (repGauge (1, g, 1)) T

namespace IsSU2Adjoint

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B} {T : Fin 3 → B}

/-!

## B. No coefficient vector is fixed

-/

/-- An isospin flip scales each coordinate by the sign of its Pauli direction. -/
lemma su2Flip_mulVec_apply (k : Fin 3) (c : Fin 3 → ℂ) (a : Fin 3) :
    (su2AdjointCoeffMatrix (su2Flip k) *ᵥ c) a = ((su2FlipSign k a : ℤ) : ℂ) * c a := by
  simp only [mulVec, dotProduct, su2AdjointCoeffMatrix, map_apply, su2AdjointMatrix_su2Flip,
    apply_ite (fun r : ℝ => (r : ℂ)), Complex.ofReal_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, Complex.ofReal_intCast]

/-- A coefficient vector fixed by every isospin rotation is zero: the flip about the axis
  `a + 1` reverses the direction `a`. -/
lemma eq_zero_of_forall_mulVec_eq {c : Fin 3 → ℂ}
    (hc : ∀ U : specialUnitaryGroup (Fin 2) ℂ, su2AdjointCoeffMatrix U *ᵥ c = c) : c = 0 := by
  funext a
  have hs : su2FlipSign (a + 1) a = -1 := by
    revert a
    decide
  have h := congrFun (hc (su2Flip (a + 1))) a
  rw [su2Flip_mulVec_apply, hs] at h
  push_cast at h
  rw [Pi.zero_apply]
  linear_combination (-1 / 2 : ℂ) * h

/-!

## C. The reduction modulo a stable submodule

`reducesInvariantsTo_bot_of_mulVec_eq` applies section B in every quotient by a stable
submodule: the span contributes nothing to the invariants.

-/

/-- For any family of maps `σ U` obeying the law, a `σ`-invariant of the span joined with a
  `σ`-stable submodule `S` lies in `S`. -/
lemma reducesInvariantsTo_bot (σ : specialUnitaryGroup (Fin 2) ℂ → B →ₗ[ℂ] B)
    (hT : ∀ U, IsSU2AdjointMat U (σ U) T) :
    ReducesInvariantsTo σ (Submodule.span ℂ (Set.range T)) ⊥ :=
  reducesInvariantsTo_bot_of_mulVec_eq T su2AdjointCoeffMatrix hT
    (fun U => ⟨U⁻¹, su2AdjointCoeffMatrix_inv U⟩) fun _ hc => eq_zero_of_forall_mulVec_eq hc

/-- An isospin invariant of the span of the components joined with an isospin-stable
  submodule `S` lies in `S`: an `su(2)` adjoint index contributes nothing to the
  invariants. -/
lemma mem_of_mem_span_sup_su2_invariant (hT : IsSU2Adjoint B repGauge T) (x : B)
    (S : Submodule ℂ B)
    (hS : ∀ U : specialUnitaryGroup (Fin 2) ℂ, ∀ y ∈ S, repGauge (1, U, 1) y ∈ S)
    (hx : x ∈ Submodule.span ℂ (Set.range T) ⊔ S)
    (hinv : ∀ U : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, U, 1) x = x) :
    x ∈ S := by
  simpa using reducesInvariantsTo_bot _ hT.repGauge_T S hS x hx hinv

end IsSU2Adjoint

end StandardModel
