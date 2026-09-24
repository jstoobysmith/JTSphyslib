/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Mathematics.InvariantReduction
public import Physlib.Mathematics.LinearCombination
/-!
# Families of components and their invariants

Every file of this folder studies a family `T : ι → B` of vectors in a module `B`: the
components of a tensor with a fixed set of gauge indices, such as a product of two gluon
field strengths `F^a F^b` indexed by `ι = Fin 2 → Fin 8`. A gauge transformation moves the
components into one another by a fixed matrix, and the question is always the same: which
linear combinations of the components does every transformation leave alone? The answer,
file by file, is a specific contraction, the trace `∑ a, T ![a, a]` or an epsilon symbol,
and this file holds the two steps of the argument that do not depend on the family.

The first is bookkeeping: a vector lies in the span of the components precisely when it is a
linear combination `∑ i, c i • T i`, so the span is described by coefficient functions
`c : ι → ℂ`, on which the transformations act by the matrix of the law.

The second is the heart of the matter. An invariant vector of the span need not have an
invariant coefficient function, because the components may be linearly dependent. But the
coefficients contracting to zero form a subspace stable under the action, and when `A g⁻¹` is
the adjoint of `A g` for the standard inner product, so is its orthogonal complement.
Projecting the coefficient of an invariant vector onto that complement leaves the vector alone
and makes the coefficient invariant. So an invariant of the span is the contraction of an
invariant coefficient, and classifying invariants of the span reduces to classifying invariant
coefficient functions, a finite linear-algebra problem: `Family.exists_invariant_coeff`, the
case `g' = g⁻¹` of `Fintype.exists_invariant_coeff_of_adjoint_mem`.

The classifications are also needed modulo a stable submodule `S`. Each family file shows that
its law descends to `B ⧸ S`, applies its classification there, and lifts the result back with
`IsStableUnder.exists_smul_add_of_quotient` or `IsStableUnder.mem_sup_of_quotient` from
`Physlib.Mathematics.InvariantReduction`.
-/

@[expose] public section

namespace StandardModel

namespace Family

variable {B : Type*} [AddCommGroup B] [Module ℂ B] {ι : Type*} [Fintype ι]

/-!

## A. The span of a family

-/

/-- A vector lies in the span of the components precisely when it is a linear combination
  of them. -/
lemma mem_iSup_span_singleton_iff (T : ι → B) (x : B) :
    x ∈ (⨆ i, ℂ ∙ T i) ↔ ∃ c : ι → ℂ, x = ∑ i, c i • T i := by
  rw [← Submodule.span_range_eq_iSup, Submodule.mem_span_range_iff_exists_fun]
  exact exists_congr fun _ => eq_comm

omit [Fintype ι] in
/-- Every component lies in the span. -/
lemma mem_iSup_span_singleton (T : ι → B) (i : ι) : T i ∈ ⨆ i, ℂ ∙ T i :=
  Submodule.mem_iSup_of_mem i (Submodule.mem_span_singleton_self _)

/-- A sum over pairs of indices is a double sum. -/
lemma sum_pi_two {n : ℕ} {M : Type*} [AddCommMonoid M] (F : (Fin 2 → Fin n) → M) :
    ∑ d : Fin 2 → Fin n, F d = ∑ x : Fin n, ∑ y : Fin n, F ![x, y] := by
  rw [show (∑ d : Fin 2 → Fin n, F d) = ∑ p : Fin n × Fin n, F ![p.1, p.2] from
      Fintype.sum_equiv (piFinTwoEquiv fun _ => Fin n) _ _ fun d => by
        congr 1
        funext i
        fin_cases i <;> simp,
    Fintype.sum_prod_type]

/-!

## B. An invariant of the span is the contraction of an invariant coefficient

The transformations are a family of linear maps `φ g` on `B`, indexed by a group `G`, and
the law says that `φ g` moves a contraction `∑ i, c i • T i` to the contraction against
`A g c`, for a linear map `A g` on coefficient functions. One property of `A` is needed:
`A g⁻¹` is the adjoint of `A g` for the standard inner product on coefficients. This is
unitarity only when `A` is moreover a representation, which is not assumed. For real matrices
it follows from `A g⁻¹` being the transpose of `A g` and `A g` commuting with conjugation,
`sum_star_mul_of_transpose`.

-/

section Complement

variable {G : Type*} [Group G] (T : ι → B) (φ : G → B →ₗ[ℂ] B)
  (A : G → (ι → ℂ) →ₗ[ℂ] (ι → ℂ))

/-- For an action by real matrices, `A g⁻¹` being the transpose of `A g` and `A g`
  commuting with conjugation make `A g⁻¹` the adjoint of `A g`. -/
lemma sum_star_mul_of_transpose
    (hA : ∀ g (c d : ι → ℂ), ∑ i, A g c i * d i = ∑ i, c i * A g⁻¹ d i)
    (hstar : ∀ g (c : ι → ℂ), A g (star c) = star (A g c)) (g : G) (c d : ι → ℂ) :
    ∑ i, star (c i) * A g d i = ∑ i, star (A g⁻¹ c i) * d i := by
  have h := hA g d (star c)
  rw [hstar] at h
  simp only [Pi.star_apply] at h
  calc ∑ i, star (c i) * A g d i = ∑ i, A g d i * star (c i) := by simp_rw [mul_comm]
    _ = ∑ i, d i * star (A g⁻¹ c i) := h
    _ = ∑ i, star (A g⁻¹ c i) * d i := by simp_rw [mul_comm]

/-- An invariant of the span of a family is the contraction of an invariant coefficient
  function, provided `A g⁻¹` is the adjoint of `A g` on coefficients. -/
theorem exists_invariant_coeff
    (hφ : ∀ g (c : ι → ℂ), φ g (∑ i, c i • T i) = ∑ i, A g c i • T i)
    (hA : ∀ g (c d : ι → ℂ), ∑ i, star (c i) * A g d i = ∑ i, star (A g⁻¹ c i) * d i)
    {x : B} (hx : x ∈ ⨆ i, ℂ ∙ T i) (hinv : ∀ g, φ g x = x) :
    ∃ c : ι → ℂ, x = ∑ i, c i • T i ∧ ∀ g, A g c = c :=
  Fintype.exists_invariant_coeff_of_adjoint_mem T φ A hφ (fun g => ⟨g⁻¹, fun u v => by
    have h := hA g u.ofLp v.ofLp
    simp only [PiLp.inner_apply, RCLike.inner_apply, Complex.star_def] at h ⊢
    rw [Finset.sum_congr rfl fun i _ => mul_comm (A g v.ofLp i) _, h]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _⟩) hx hinv

end Complement

end Family

end StandardModel
