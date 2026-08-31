/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeAlgebra.Basis
/-!
# Gauge tensors carrying two `su(2)` adjoint indices

`IsSU2BiAdjoint B repGauge T` says that a family `T`, indexed by two `su(2)` adjoint
indices and valued in a module `B` carrying a representation of the gauge group
`GaugeGroupI`, transforms as a tensor `T^{a₁ a₂}` in the `su(2)` factor of the adjoint
representation.

This is the gauge analogue of `IsQuadLorentz`. The field strength of the `W` bosons
carries one `su(2)` adjoint index, so a product of two field strengths carries two, and
the proposition here records how such a product transforms.

Section A gives the proposition and the span of its components, section B the
orthogonality of the `su(2)` block of `adjointMatrix`, and section C the trace
contraction, which is the natural gauge invariant built from two adjoint indices.
-/

@[expose] public section

namespace StandardModel

open Matrix

/-!

## A. Bi-adjoint `su(2)` families and the span of their components

-/

/-- A family `T` of elements of `B`, indexed by two `su(2)` adjoint indices, transforms
  as a tensor `T^{a₁ a₂}` under the representation `repGauge` of the gauge group. -/
structure IsSU2BiAdjoint (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B)
    (T : (Fin 2 → Fin 3) → B) : Prop where
  repGauge_T : ∀ (g : GaugeGroupI) (l : Fin 2 → Fin 3),
    repGauge g (T l) = ∑ a : Fin 2 → Fin 3,
      (∏ i : Fin 2, ((GaugeAlgebra.adjointMatrix g (Sum.inr (Sum.inl (a i)))
        (Sum.inr (Sum.inl (l i))) : ℝ) : ℂ)) • T a

namespace IsSU2BiAdjoint
set_option linter.unusedVariables false

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {T : (Fin 2 → Fin 3) → B}
  (hT : IsSU2BiAdjoint B repGauge T)

/-- The span of all the components. -/
def span (hT : IsSU2BiAdjoint B repGauge T) : Submodule ℂ B := ⨆ d, ℂ ∙ T d

/-- An element of `B` lies in the span of the components of `T` precisely when it is a
  linear combination of them. -/
lemma mem_span_iff (x : B) :
    x ∈ hT.span ↔ ∃ (c : (Fin 2 → Fin 3) → ℂ), x = ∑ d, c d • T d := by
  constructor
  · intro hx
    rw [span] at hx
    refine Submodule.iSup_induction
      (motive := fun y => ∃ c : (Fin 2 → Fin 3) → ℂ, y = ∑ d, c d • T d)
      (fun d => ℂ ∙ T d) hx ?_ ?_ ?_
    · intro d y hy
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
      refine ⟨fun e => if e = d then a else 0, ?_⟩
      simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · exact ⟨0, by simp⟩
    · rintro y z ⟨c₁, rfl⟩ ⟨c₂, rfl⟩
      exact ⟨c₁ + c₂, by simp [add_smul, Finset.sum_add_distrib]⟩
  · rintro ⟨c, rfl⟩
    exact sum_mem fun d _ => Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem d (Submodule.mem_span_singleton_self _))

/-!

## B. Orthogonality of the adjoint matrix

Orthogonality of `adjointMatrix` is proved where the matrix is defined, in
`GaugeAlgebra.Basis`. All that is needed here is the row orthonormality of the block
belonging to this gauge factor, which is what makes the trace contraction of section C
gauge invariant.

-/

/-- The rows of the `su(2)` block of the adjoint matrix are orthonormal. -/
lemma sum_adjointMatrix_row_mul (g : GaugeGroupI) (c d : Fin 3) :
    ∑ a : Fin 3, GaugeAlgebra.adjointMatrix g (Sum.inr (Sum.inl c)) (Sum.inr (Sum.inl a)) *
      GaugeAlgebra.adjointMatrix g (Sum.inr (Sum.inl d)) (Sum.inr (Sum.inl a))
      = if c = d then 1 else 0 := by
  have h : (GaugeAlgebra.adjointMatrix g * (GaugeAlgebra.adjointMatrix g)ᵀ)
      (Sum.inr (Sum.inl c)) (Sum.inr (Sum.inl d)) = (1 : Matrix (Fin 8 ⊕ Fin 3 ⊕ Fin 1)
        (Fin 8 ⊕ Fin 3 ⊕ Fin 1) ℝ) (Sum.inr (Sum.inl c)) (Sum.inr (Sum.inl d)) := by
    rw [GaugeAlgebra.adjointMatrix_mul_transpose]
  rw [Matrix.mul_apply, Fintype.sum_sum_type] at h
  simpa [Fintype.sum_sum_type, Matrix.one_apply] using h

TODO (lines := 90-102) "Move this to where `adjointMatrix` is
  defined."

/-!

## C. The trace contraction

-/

/-- A sum over families of two `su(2)` adjoint indices is a double sum. -/
lemma sum_pi_two {M : Type*} [AddCommMonoid M] (F : (Fin 2 → Fin 3) → M) :
    ∑ d : Fin 2 → Fin 3, F d = ∑ x : Fin 3, ∑ y : Fin 3, F ![x, y] := by
  rw [show (∑ d : Fin 2 → Fin 3, F d) = ∑ p : Fin 3 × Fin 3, F ![p.1, p.2] from
      Fintype.sum_equiv (piFinTwoEquiv fun _ => Fin 3) _ _ fun d => by
        congr 1
        funext i
        fin_cases i <;> simp,
    Fintype.sum_prod_type]

/-- The trace contraction of a bi-adjoint family: the Kronecker contraction of the two
  `su(2)` adjoint indices. -/
def traceContraction (hT : IsSU2BiAdjoint B repGauge T) : B := ∑ a : Fin 3, T ![a, a]

/-- The trace contraction written as a sum over all pairs of adjoint indices weighted by
  the Kronecker delta. -/
lemma traceContraction_eq_sum (hT : IsSU2BiAdjoint B repGauge T) :
    hT.traceContraction
      = ∑ d : Fin 2 → Fin 3, (if d 0 = d 1 then (1 : ℂ) else 0) • T d := by
  rw [sum_pi_two]
  simp [traceContraction, ite_smul]

/-- The trace contraction lies in the span of the components. -/
lemma traceContraction_mem_span (hT : IsSU2BiAdjoint B repGauge T) :
    hT.traceContraction ∈ hT.span := by
  rw [traceContraction]
  exact sum_mem fun d _ =>
    Submodule.mem_iSup_of_mem _ (Submodule.mem_span_singleton_self _)

/-- The trace contraction of a bi-adjoint family is gauge invariant. -/
lemma repGauge_traceContraction (hT : IsSU2BiAdjoint B repGauge T) (g : GaugeGroupI) :
    repGauge g hT.traceContraction = hT.traceContraction := by
  have step : repGauge g hT.traceContraction
      = ∑ b : Fin 2 → Fin 3, (if b 0 = b 1 then (1 : ℂ) else 0) • T b := by
    show repGauge g (∑ c : Fin 3, T ![c, c]) = _
    rw [map_sum]
    have h1 : ∀ c : Fin 3, repGauge g (T ![c, c])
        = ∑ b : Fin 2 → Fin 3,
          ((GaugeAlgebra.adjointMatrix g (Sum.inr (Sum.inl (b 0))) (Sum.inr (Sum.inl c)) *
            GaugeAlgebra.adjointMatrix g (Sum.inr (Sum.inl (b 1)))
              (Sum.inr (Sum.inl c)) : ℝ) : ℂ) • T b := by
      intro c
      rw [hT.repGauge_T g ![c, c]]
      refine Finset.sum_congr rfl fun b _ => ?_
      congr 1
      simp [Fin.prod_univ_two]
    simp only [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    rw [← Complex.ofReal_sum, sum_adjointMatrix_row_mul]
    simp [apply_ite]
  rw [step, ← hT.traceContraction_eq_sum]


TODO (lines := 166-167) "Give the gauge weight decomposition of
  `Span` in the SU(2) case."

end IsSU2BiAdjoint

end StandardModel
