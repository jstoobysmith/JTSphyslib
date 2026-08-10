/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Span.Basic
/-!
# Averaging an invariant vector over a spanning set

The classification of invariants of a representation rests on a single
observation. Suppose a vector `y` is known to lie in the span of a set `s`, and
suppose `f` is a linear operator built from the group action which fixes `y`.
Then

`y = f y ∈ f '' (span s) = span (f '' s)`,

so `y` already lies in the span of the *transformed* set, and it suffices to
compute `f v` for the — usually far fewer, or far simpler — elements `v` of `s`.
This is `Submodule.mem_span_image_of_apply_eq_self`.

The operators `f` to which this is applied come in two flavours, both provided
here.

* The average `Representation.subgroupAverage` over a finite subgroup `S`, the
  Reynolds operator `α_S = |S|⁻¹ ∑_{g ∈ S} ρ g`. Every `S`-invariant vector is
  fixed by it, giving the theorem in its familiar form: an invariant `y` in the
  span of `v i` lies in the span of the averages `α_S (v i)`
  (`Representation.mem_span_range_subgroupAverage`).
* More generally `Representation.weightedSum`, a combination `∑ w i • ρ (g i)`
  of finitely many group elements whose weights sum to one. This still fixes
  every invariant vector, but does not require the elements to form a finite
  subgroup — which matters when the group is non-compact and carries no
  invariant average, as for the Lorentz boosts. The weights are then free
  parameters, and can be chosen to annihilate whatever else one wishes.

Polynomials in an operator that fixes `y` again fix `y` provided their
coefficients sum to one (`Module.End.sum_smul_pow_apply_of_apply_eq_self`), so
spectral projectors built this way are covered too — `boostAvgScalarProj` of
`Averages/BoostAvgProjector` is one.

Nothing here is specific to this sector; the file sits at the root of `Invariants/`
because that is where the principle is used, and every other file in the
folder is an instance of it.
-/

@[expose] public section

namespace Submodule

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- **The averaging principle.** A vector in the span of `s` which is fixed by a
  linear endomorphism `f` lies in the span of the image `f '' s`. -/
theorem mem_span_image_of_apply_eq_self {s : Set M} {f : M →ₗ[R] M} {y : M}
    (hy : y ∈ span R s) (hfy : f y = y) : y ∈ span R (f '' s) := by
  rw [span_image]
  exact ⟨y, hy, hfy⟩

/-- The averaging principle for a spanning family: a vector in the span of the
  `v i` which is fixed by `f` lies in the span of the `f (v i)`. -/
theorem mem_span_range_of_apply_eq_self {ι : Type*} {v : ι → M} {f : M →ₗ[R] M} {y : M}
    (hy : y ∈ span R (Set.range v)) (hfy : f y = y) :
    y ∈ span R (Set.range fun i => f (v i)) := by
  rw [show (Set.range fun i => f (v i)) = f '' Set.range v from Set.range_comp f v]
  exact mem_span_image_of_apply_eq_self hy hfy

end Submodule

namespace Module.End

variable {R M ι : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- A power of an operator fixing `v` fixes `v`. -/
lemma pow_apply_of_apply_eq_self {f : Module.End R M} {v : M} (hf : f v = v) :
    ∀ n : ℕ, (f ^ n) v = v
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ, Module.End.mul_apply, hf, pow_apply_of_apply_eq_self hf n]

/-- A polynomial in an operator fixing `v`, with coefficients summing to one, fixes
  `v`. Spectral projectors are of this form. -/
lemma sum_smul_pow_apply_of_apply_eq_self {f : Module.End R M} {v : M} (hf : f v = v)
    {s : Finset ι} {c : ι → R} {n : ι → ℕ} (hc : ∑ i ∈ s, c i = 1) :
    (∑ i ∈ s, c i • f ^ n i) v = v := by
  rw [LinearMap.sum_apply,
    Finset.sum_congr rfl fun i _ => by
      rw [LinearMap.smul_apply, pow_apply_of_apply_eq_self hf], ← Finset.sum_smul, hc, one_smul]

end Module.End

namespace Representation

variable {R G M ι : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

section Monoid

variable [Monoid G]

/-- A weighted combination `∑ w i • ρ (g i)` of the operators of a representation. -/
noncomputable def weightedSum (ρ : Representation R G M) (s : Finset ι) (w : ι → R) (g : ι → G) :
    M →ₗ[R] M :=
  ∑ i ∈ s, w i • ρ (g i)

lemma weightedSum_apply (ρ : Representation R G M) (s : Finset ι) (w : ι → R) (g : ι → G) (v : M) :
    ρ.weightedSum s w g v = ∑ i ∈ s, w i • ρ (g i) v := by
  simp [weightedSum, LinearMap.sum_apply]

/-- A weighted combination of group elements whose weights sum to one fixes every
  vector invariant under those elements. No subgroup, and no compactness, is
  needed. -/
lemma weightedSum_apply_of_invariant {ρ : Representation R G M} {s : Finset ι} {w : ι → R}
    {g : ι → G} {v : M} (hw : ∑ i ∈ s, w i = 1) (hv : ∀ i ∈ s, ρ (g i) v = v) :
    ρ.weightedSum s w g v = v := by
  rw [weightedSum_apply, Finset.sum_congr rfl fun i hi => by rw [hv i hi], ← Finset.sum_smul, hw,
    one_smul]

/-- An invariant vector in the span of `s` lies in the span of the image of `s` under
  any weighted combination of group elements fixing it. -/
theorem mem_span_image_weightedSum {ρ : Representation R G M} {s : Finset ι} {w : ι → R}
    {g : ι → G} {t : Set M} {y : M} (hy : y ∈ Submodule.span R t) (hw : ∑ i ∈ s, w i = 1)
    (hv : ∀ i ∈ s, ρ (g i) y = y) :
    y ∈ Submodule.span R (ρ.weightedSum s w g '' t) :=
  Submodule.mem_span_image_of_apply_eq_self hy (weightedSum_apply_of_invariant hw hv)

end Monoid

section Subgroup

variable [Group G]

/-- The average of a representation over a finite subgroup, `α_S = |S|⁻¹ ∑_{g ∈ S} ρ g`. -/
noncomputable def subgroupAverage (ρ : Representation R G M) (S : Subgroup G) [Fintype S]
    [Invertible (Fintype.card S : R)] : M →ₗ[R] M :=
  ρ.weightedSum Finset.univ (fun _ : S => ⅟(Fintype.card S : R)) (fun h => (h : G))

lemma subgroupAverage_apply (ρ : Representation R G M) (S : Subgroup G) [Fintype S]
    [Invertible (Fintype.card S : R)] (v : M) :
    ρ.subgroupAverage S v = ∑ g : S, ⅟(Fintype.card S : R) • ρ (g : G) v :=
  weightedSum_apply _ _ _ _ v

/-- The average over a subgroup fixes every vector invariant under that subgroup. -/
lemma subgroupAverage_apply_of_invariant {ρ : Representation R G M} {S : Subgroup G} [Fintype S]
    [Invertible (Fintype.card S : R)] {v : M} (hv : ∀ g ∈ S, ρ g v = v) :
    ρ.subgroupAverage S v = v := by
  refine weightedSum_apply_of_invariant ?_ fun g _ => hv (g : G) g.2
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_invOf_self]

/-- **Averaging over a subgroup.** If `y` lies in the span of `t` and is invariant
  under a finite subgroup `S`, then `y` lies in the span of the averaged set
  `α_S '' t`. -/
theorem mem_span_image_subgroupAverage {ρ : Representation R G M} {S : Subgroup G} [Fintype S]
    [Invertible (Fintype.card S : R)] {t : Set M} {y : M} (hy : y ∈ Submodule.span R t)
    (hinv : ∀ g ∈ S, ρ g y = y) :
    y ∈ Submodule.span R (ρ.subgroupAverage S '' t) :=
  Submodule.mem_span_image_of_apply_eq_self hy (subgroupAverage_apply_of_invariant hinv)

/-- **Averaging over a subgroup**, for a spanning family: an invariant `y` in the span
  of the `v i` lies in the span of the averages `α_S (v i)`. -/
theorem mem_span_range_subgroupAverage {ρ : Representation R G M} {S : Subgroup G} [Fintype S]
    [Invertible (Fintype.card S : R)] {v : ι → M} {y : M}
    (hy : y ∈ Submodule.span R (Set.range v)) (hinv : ∀ g ∈ S, ρ g y = y) :
    y ∈ Submodule.span R (Set.range fun i => ρ.subgroupAverage S (v i)) :=
  Submodule.mem_span_range_of_apply_eq_self hy (subgroupAverage_apply_of_invariant hinv)

end Subgroup

end Representation
