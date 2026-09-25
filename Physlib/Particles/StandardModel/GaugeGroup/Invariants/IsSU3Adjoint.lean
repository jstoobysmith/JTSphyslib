/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.IsSU3BiAdjoint
/-!
# Gauge tensors carrying one `su(3)` adjoint index

A single gluon field strength `F^a` carries one colour index, running over the eight
Gell-Mann directions of `su(3)`, and transforms in the adjoint representation `8`. That
representation contains no singlet: no linear combination of the eight components is left
alone by every colour rotation, which is why a Lagrangian never contains a term linear in a
field strength. Modulo a colour-stable submodule `S`, every colour invariant of the span of the
components lies in `S`.

`IsSU3Adjoint B repGauge T` records the transformation law: a colour rotation `U ∈ SU(3)`
moves the components by the adjoint matrix of `U`, the summed index in the row slot, so the
law acts on coefficient vectors by `su3AdjointCoeffMatrix U` of `IsSU3BiAdjoint`. Nothing is
asked of the isospin and hypercharge factors.

Two colour rotations show that no nonzero coefficient vector is fixed. The colour parities,
diagonal sign matrices of `SU(3)`, reverse the six Gell-Mann directions that mix two colours
and fix the two Cartan directions `λ₃` and `λ₈`, so a fixed coefficient vector lives in the
Cartan plane. The cyclic permutation of the colours rotates that plane through a third of a
turn, and a rotation of a plane fixes no nonzero vector.

- A. The transformation law
- B. No coefficient vector is fixed
- C. The reduction modulo a stable submodule
-/

@[expose] public section

namespace StandardModel

open Matrix IsSU3BiAdjoint

/-!

## A. The transformation law

The law carries one factor of the adjoint matrix, with the summed index in the row slot,
exactly as each of the two indices of a bi-adjoint family does.

-/

/-- The linear map `f` moves the components of `T` as `U ∈ SU(3)` moves a tensor with one
  adjoint index. -/
def IsSU3AdjointMat {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (U : specialUnitaryGroup (Fin 3) ℂ) (f : B →ₗ[ℂ] B) (T : Fin 8 → B) : Prop :=
  ∀ l : Fin 8, f (T l) = ∑ a : Fin 8, ((su3AdjointMatrix U a l : ℝ) : ℂ) • T a

/-- A family `T` of elements of `B`, indexed by one `su(3)` adjoint index, transforms as a
  tensor `T^a` under the colour factor of the gauge group. Nothing is asked of the isospin
  and hypercharge factors. -/
structure IsSU3Adjoint (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B) (T : Fin 8 → B) : Prop where
  repGauge_T : ∀ g : specialUnitaryGroup (Fin 3) ℂ,
    IsSU3AdjointMat g (repGauge (g, 1, 1)) T

namespace IsSU3Adjoint

/- `span` takes the hypothesis `hT` only to hang off it by dot notation. -/
set_option linter.unusedVariables false

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B} {T : Fin 8 → B}

/-- The span of the components. -/
@[nolint unusedArguments]
def span (hT : IsSU3Adjoint B repGauge T) : Submodule ℂ B := ⨆ d, ℂ ∙ T d

/-!

## B. No coefficient vector is fixed

-/

/-- A colour parity scales each coordinate by the sign of its Gell-Mann direction. -/
lemma su3Parity_mulVec_apply (k : Fin 3) (c : Fin 8 → ℂ) (a : Fin 8) :
    (su3AdjointCoeffMatrix (su3Parity k) *ᵥ c) a = ((paritySign k a : ℤ) : ℂ) * c a := by
  simp only [mulVec, dotProduct, su3AdjointCoeffMatrix, map_apply, su3AdjointMatrix_su3Parity,
    apply_ite (fun r : ℝ => (r : ℂ)), Complex.ofReal_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, Complex.ofReal_intCast]

/-- A coefficient vector fixed by every colour rotation is zero: the parities confine it to
  the Cartan plane, which the cyclic rotation turns through a third of a turn. -/
lemma eq_zero_of_forall_mulVec_eq {c : Fin 8 → ℂ}
    (hc : ∀ U : specialUnitaryGroup (Fin 3) ℂ, su3AdjointCoeffMatrix U *ᵥ c = c) : c = 0 := by
  -- the parities: every direction outside the Cartan plane carries a sign `-1`
  have hpar : ∀ (k : Fin 3) (a : Fin 8), paritySign k a = -1 → c a = 0 := by
    intro k a hk
    have h := congrFun (hc (su3Parity k)) a
    rw [su3Parity_mulVec_apply, hk] at h
    push_cast at h
    linear_combination (-1 / 2 : ℂ) * h
  have hroot : ∀ a : Fin 8, a ≠ 2 → a ≠ 7 → c a = 0 := by
    intro a h2 h7
    have key : paritySign 0 a = -1 ∨ paritySign 1 a = -1 := by
      revert a
      decide
    rcases key with h | h
    · exact hpar 0 a h
    · exact hpar 1 a h
  -- the Cartan plane: the cyclic rotation turns it, fixing nothing
  have hcart : c = c 2 • unitVec 2 + c 7 • unitVec 7 := by
    funext a
    have ha : a = 2 ∨ a = 7 ∨ (a ≠ 2 ∧ a ≠ 7) := by
      revert a
      decide
    rcases ha with rfl | rfl | ⟨h2, h7⟩
    · simp [unitVec]
    · simp [unitVec]
    · simp [unitVec, h2, h7, hroot a h2 h7]
  have h := hc su3Perm
  rw [hcart, mulVec_add, mulVec_smul, mulVec_smul, su3Perm_mulVec_unitVec,
    su3Perm_mulVec_unitVec] at h
  have h2 := congrFun h 2
  have h7 := congrFun h 7
  simp [permCol, unitVec] at h2 h7
  have hc7 : c 7 = 0 := by
    linear_combination (-((Real.sqrt 3 : ℝ) : ℂ) / 6) * h2 + (-(1 : ℂ) / 2) * h7
      + (-(c 7) / 12) * sqrt_three_mul_self
  have hc2 : c 2 = 0 := by
    linear_combination (-(2 : ℂ) / 3) * h2 - (((Real.sqrt 3 : ℝ) : ℂ) / 3) * hc7
  rw [hcart, hc2, hc7]
  simp

/-!

## C. The reduction modulo a stable submodule

`reducesInvariantsTo_bot_of_mulVec_eq` applies section B in every quotient by a stable
submodule: the span contributes nothing to the invariants.

-/

/-- For any family of maps `σ U` obeying the law, a `σ`-invariant of the span joined with a
  `σ`-stable submodule `S` lies in `S`. -/
lemma reducesInvariantsTo_bot (σ : specialUnitaryGroup (Fin 3) ℂ → B →ₗ[ℂ] B)
    (hT : ∀ U, IsSU3AdjointMat U (σ U) T) :
    ReducesInvariantsTo σ (⨆ i, ℂ ∙ T i) ⊥ :=
  reducesInvariantsTo_bot_of_mulVec_eq T su3AdjointCoeffMatrix hT
    (fun U => ⟨U⁻¹, su3AdjointCoeffMatrix_inv U⟩) fun _ hc => eq_zero_of_forall_mulVec_eq hc

/-- A colour invariant of the span of the components joined with a colour-stable submodule
  `S` lies in `S`: an `su(3)` adjoint index contributes nothing to the invariants. -/
lemma mem_of_mem_span_sup_su3_invariant (hT : IsSU3Adjoint B repGauge T) (x : B)
    (S : Submodule ℂ B)
    (hS : ∀ U : specialUnitaryGroup (Fin 3) ℂ, ∀ y ∈ S, repGauge (U, 1, 1) y ∈ S)
    (hx : x ∈ hT.span ⊔ S)
    (hinv : ∀ U : specialUnitaryGroup (Fin 3) ℂ, repGauge (U, 1, 1) x = x) :
    x ∈ S := by
  simpa using reducesInvariantsTo_bot _ hT.repGauge_T S hS x hx hinv

end IsSU3Adjoint

end StandardModel
