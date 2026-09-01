/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeAlgebra.Basis
public import Physlib.Particles.StandardModel.GaugeGroup.GaugeWeightDecomposition
public import Mathlib.RepresentationTheory.Invariants
/-!
# Gauge tensors carrying two `u(1)` adjoint indices

`IsU1BiAdjoint B repGauge T` says that a family `T`, indexed by two `u(1)` adjoint
indices and valued in a module `B` carrying a representation of the gauge group
`GaugeGroupI`, transforms as a tensor `T^{a₁ a₂}` in the `u(1)` factor of the adjoint
representation.

This is the gauge analogue of `IsQuadLorentz`. The field strength of the `B` boson
carries one `u(1)` adjoint index, so a product of two field strengths carries two, and
the proposition here records how such a product transforms.

The transformation law itself is `IsU1BiAdjointMat`, which relates one element of `U(1)`
to one linear map on `B` and mentions no other factor of the gauge group, through
`u1AdjointMatrix`, the adjoint matrix of a `U(1)` element alone. `IsU1BiAdjoint` says
that the hypercharge transformation `(1, 1, u)` obeys that law with the matrix of `u`,
for every `u` in `U(1)`, and it says nothing whatever about the colour and isospin
factors: those may move the components as they please.

The `u(1)` factor is abelian and one dimensional, so its adjoint action is trivial:
`u1AdjointMatrix` is the one by one matrix `1`, and the law reduces to `f (T l) = T l`.
So the components of `T`, and every element of their span, are fixed by the hypercharge
factor. What is no longer claimed is that they are fixed by the colour and isospin
factors, about which the law says nothing; the statements that need that, here
`span_le_invariants`, take the law at every gauge element as an explicit hypothesis,
in the way that `htc` is a hypothesis in `IsSU2BiAdjoint` and `IsSU3BiAdjoint`. The
hypothesis-free form is `span_le_repU1_invariants`, for `repU1 repGauge`, the
hypercharge part of the representation, which sends the colour and isospin factors to
the identity outright.

Section A gives the adjoint matrix of the `U(1)` factor, the transformation law, the
span of the components and the hypercharge part of a representation, section B the
orthogonality of the `u(1)` block of `adjointMatrix`, section C the trace contraction,
which is the natural invariant built from two adjoint indices, and section D the
invariance of the span, under the hypercharge factor outright and under the whole gauge
group once the law is known at every gauge element.
-/

@[expose] public section

namespace StandardModel

open Matrix

/-!

## A. The `U(1)` adjoint matrix and bi-adjoint families

A `u(1)` adjoint index is acted on by the `U(1)` factor of the gauge group alone. That
action is recorded in A.1 as `u1AdjointMatrix`, a matrix built from an element of `U(1)`
and nothing else, A.2 phrases the transformation law through it, so that no other factor
of the gauge group appears in the law nor in the hypothesis, and A.3 reads a
representation of the gauge group at its hypercharge factor alone.

## A.1. The adjoint matrix of the `U(1)` factor

The `u(1)` factor is abelian, so it acts trivially on its own algebra and the matrix is
the one by one matrix `1`, whatever the element of `U(1)`. It is the `u(1)` block of
`GaugeAlgebra.adjointMatrix`, definitionally so, and its single row is of unit length.

-/

/-- The adjoint matrix of an element of `U(1)`: the one by one matrix `1`, the `u(1)`
  factor being abelian and so acting trivially on its own algebra. -/
def u1AdjointMatrix (_u : unitary ℂ) : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of fun _ _ => 1

/-- The single entry of the adjoint matrix of an element of `U(1)` is `1`. -/
@[simp]
lemma u1AdjointMatrix_apply (u : unitary ℂ) (i j : Fin 1) :
    u1AdjointMatrix u i j = 1 := rfl

/-- The adjoint matrix of the `U(1)` factor of a gauge group element is the `u(1)` block
  of the adjoint matrix of the gauge algebra. -/
lemma u1AdjointMatrix_toU1 (g : GaugeGroupI) (i j : Fin 1) :
    u1AdjointMatrix (GaugeGroupI.toU1 g) i j
      = GaugeAlgebra.adjointMatrix g (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr j)) := rfl

/-- The rows of the adjoint matrix of an element of `U(1)` are orthonormal: there is a
  single row and it is of unit length. -/
lemma sum_u1AdjointMatrix_row_mul (u : unitary ℂ) (c d : Fin 1) :
    ∑ a : Fin 1, u1AdjointMatrix u c a * u1AdjointMatrix u d a = if c = d then 1 else 0 := by
  rw [Subsingleton.elim c d]
  simp

/-!

## A.2. Bi-adjoint `u(1)` families and the span of their components

The transformation law carries one factor of `u1AdjointMatrix` per index, with the summed
index in the row slot, exactly as `IsSU2BiAdjoint` carries one factor of the `SU(2)`
adjoint matrix per index. It is recorded by `IsU1BiAdjointMat`, a relation between one
element of `U(1)` and one linear map on `B` in which no other factor of the gauge group
appears, and it is the law obeyed by the hypercharge field strengths of `IsGaugeSector`.

Since the matrix is `1` and there is a single family of two `u(1)` indices, the law says
no more and no less than that the map fixes each component, which is
`isU1BiAdjointMat_iff`.

`IsU1BiAdjoint` then says that the gauge transformation `(1, 1, u)` obeys that law with
the matrix of `u`, for every `u` in `U(1)`. Since `u ↦ (1, 1, u)` is a monoid
homomorphism this is an action of `U(1)`, and it is all that is assumed: a gauge
transformation with a nontrivial colour or isospin factor is not mentioned, and may move
the components arbitrarily.

-/

/-- The linear map `f` moves the components of the family `T` as the `U(1)` element `u`
  moves a tensor with two adjoint indices: one factor of `u1AdjointMatrix u` per index,
  with the summed index in the row slot. -/
def IsU1BiAdjointMat {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (u : unitary ℂ) (f : B →ₗ[ℂ] B)
    (T : (Fin 2 → Fin 1) → B) : Prop :=
  ∀ l : Fin 2 → Fin 1,
    f (T l) = ∑ a : Fin 2 → Fin 1,
      (∏ i : Fin 2, ((u1AdjointMatrix u (a i) (l i) : ℝ) : ℂ)) • T a

/-- The `u(1)` transformation law says exactly that the map fixes every component: the
  adjoint matrix is `1`, and there is a single family of two `u(1)` indices to sum
  over. -/
lemma isU1BiAdjointMat_iff {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (u : unitary ℂ) (f : B →ₗ[ℂ] B) (T : (Fin 2 → Fin 1) → B) :
    IsU1BiAdjointMat u f T ↔ ∀ l : Fin 2 → Fin 1, f (T l) = T l := by
  refine forall_congr' fun l => ?_
  rw [Fintype.sum_unique, Subsingleton.elim (default : Fin 2 → Fin 1) l]
  simp

/-- A linear map obeying the `u(1)` transformation law fixes every component of the
  family, the adjoint action of the `u(1)` factor being trivial. -/
lemma IsU1BiAdjointMat.map_T {B : Type*} [AddCommMonoid B] [Module ℂ B] {u : unitary ℂ}
    {f : B →ₗ[ℂ] B} {T : (Fin 2 → Fin 1) → B} (hf : IsU1BiAdjointMat u f T)
    (l : Fin 2 → Fin 1) : f (T l) = T l :=
  (isU1BiAdjointMat_iff u f T).1 hf l

/-- A family `T` of elements of `B`, indexed by two `u(1)` adjoint indices, transforms
  as a tensor `T^{a₁ a₂}` under the representation `repGauge` of the gauge group: a
  hypercharge transformation moves the components by the `U(1)` element it is built from.
  Nothing is asked of the colour or isospin factors. -/
structure IsU1BiAdjoint (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B)
    (T : (Fin 2 → Fin 1) → B) : Prop where
  repGauge_T : ∀ g : unitary ℂ, IsU1BiAdjointMat g (repGauge (1, 1, g)) T

/-!

## A.3. The hypercharge part of a representation

Reading a representation of the gauge group at the hypercharge factor of its argument
alone gives `repU1`, again a representation of the whole gauge group. Every construction
stated for a representation of `GaugeGroupI` therefore applies to it verbatim, and a
bi-adjoint family for `repGauge` is a bi-adjoint family for `repU1 repGauge`, with the
same span and the same trace contraction. Invariance under it is invariance under the
hypercharge factor, `∀ u : U(1), repGauge (1, 1, u) x = x`, which is exactly what the
transformation law constrains.

The statements of section D are written with the hypercharge transformation `(1, 1, u)`
spelled out, so that reading one needs no unfolding, and `repU1_invariant_iff_u1` is the
bridge between the two spellings.

-/

/-- The hypercharge part of a representation of the gauge group: the representation
  reading only the `U(1)` factor of its argument and sending the colour and isospin
  factors to the identity. -/
noncomputable def repU1 {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B) : Representation ℂ GaugeGroupI B where
  toFun g := repGauge (1, 1, GaugeGroupI.toU1 g)
  map_one' := by
    have h1 : ((1, 1, GaugeGroupI.toU1 1) : GaugeGroupI) = 1 := by
      simp [Prod.ext_iff]
    rw [h1, map_one]
  map_mul' g h := by
    have hgh : ((1, 1, GaugeGroupI.toU1 (g * h)) : GaugeGroupI)
        = ((1, 1, GaugeGroupI.toU1 g) : GaugeGroupI) * (1, 1, GaugeGroupI.toU1 h) := by
      simp [map_mul]
    rw [hgh, map_mul]

/-- The hypercharge part of a representation acts by the representation itself, at the
  gauge transformation with the same hypercharge factor and nothing else. -/
lemma repU1_apply {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B) (g : GaugeGroupI) :
    repU1 repGauge g = repGauge (1, 1, GaugeGroupI.toU1 g) := rfl

/-- The hypercharge part of a representation acts by algebra maps whenever the
  representation does, each of its values being a value of that representation. -/
lemma isMulRep_repU1 {B : Type*} [Ring B] [Algebra ℂ B]
    {repGauge : Representation ℂ GaugeGroupI B} (hmul : IsMulRep repGauge) :
    IsMulRep (repU1 repGauge) :=
  fun g x y => hmul (1, 1, GaugeGroupI.toU1 g) x y

/-- Invariance under the hypercharge part of a representation is invariance under the
  gauge transformations that are trivial on colour and isospin. The hypercharge part
  reads only the hypercharge factor of its argument, and every element of `U(1)` is the
  hypercharge factor of such a transformation. -/
lemma repU1_invariant_iff_u1 {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B) (x : B) :
    (∀ g : GaugeGroupI, repU1 repGauge g x = x)
      ↔ ∀ u : unitary ℂ, repGauge (1, 1, u) x = x :=
  ⟨fun h u => h (1, 1, u), fun h g => h (GaugeGroupI.toU1 g)⟩

/-- A submodule is stable under the hypercharge part of a representation precisely when
  it is stable under the gauge transformations trivial on colour and isospin. -/
lemma repU1_stable_iff_u1 {B : Type*} [AddCommGroup B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B) (S : Submodule ℂ B) :
    (∀ g : GaugeGroupI, ∀ y ∈ S, repU1 repGauge g y ∈ S)
      ↔ ∀ u : unitary ℂ, ∀ y ∈ S, repGauge (1, 1, u) y ∈ S :=
  ⟨fun h u => h (1, 1, u), fun h g => h (GaugeGroupI.toU1 g)⟩

namespace IsU1BiAdjoint
set_option linter.unusedVariables false

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {T : (Fin 2 → Fin 1) → B}
  (hT : IsU1BiAdjoint B repGauge T)

/-- A bi-adjoint family for a representation is a bi-adjoint family for its hypercharge
  part: the transformation law reads only the hypercharge factor to begin with. The span
  and the trace contraction do not mention the representation, so every statement of this
  file transports along this and is read at the hypercharge factor alone. -/
lemma toRepU1 (hT : IsU1BiAdjoint B repGauge T) :
    IsU1BiAdjoint B (repU1 repGauge) T where
  repGauge_T g := hT.repGauge_T g

/-- The span of all the components. -/
def span (hT : IsU1BiAdjoint B repGauge T) : Submodule ℂ B := ⨆ d, ℂ ∙ T d

/-- An element of `B` lies in the span of the components of `T` precisely when it is a
  linear combination of them. -/
lemma mem_span_iff (x : B) :
    x ∈ hT.span ↔ ∃ (c : (Fin 2 → Fin 1) → ℂ), x = ∑ d, c d • T d := by
  constructor
  · intro hx
    rw [span] at hx
    refine Submodule.iSup_induction
      (motive := fun y => ∃ c : (Fin 2 → Fin 1) → ℂ, y = ∑ d, c d • T d)
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

The adjoint action of the gauge group on the `u(1)` factor is trivial, so the `u(1)`
entry of `adjointMatrix` is `1`, for every gauge group element and not only for a
hypercharge one, and the corresponding one by one block is orthogonal. This is the
`GaugeGroupI` reading of section A.1.

-/

/-- The adjoint action of the gauge group on the `u(1)` factor is trivial. -/
lemma adjointMatrix_u1 (g : GaugeGroupI) (c d : Fin 1) :
    GaugeAlgebra.adjointMatrix g (Sum.inr (Sum.inr c)) (Sum.inr (Sum.inr d)) = 1 := rfl

/-- The rows of the `u(1)` block of the adjoint matrix are orthonormal. -/
lemma sum_adjointMatrix_row_mul (g : GaugeGroupI) (c d : Fin 1) :
    ∑ a : Fin 1, GaugeAlgebra.adjointMatrix g (Sum.inr (Sum.inr c)) (Sum.inr (Sum.inr a)) *
      GaugeAlgebra.adjointMatrix g (Sum.inr (Sum.inr d)) (Sum.inr (Sum.inr a))
      = if c = d then 1 else 0 := by
  rw [Subsingleton.elim c d]
  simp

/-!

## C. The trace contraction

-/

/-- A sum over families of two `u(1)` adjoint indices is a double sum. -/
lemma sum_pi_two {M : Type*} [AddCommMonoid M] (F : (Fin 2 → Fin 1) → M) :
    ∑ d : Fin 2 → Fin 1, F d = ∑ x : Fin 1, ∑ y : Fin 1, F ![x, y] := by
  rw [show (∑ d : Fin 2 → Fin 1, F d) = ∑ p : Fin 1 × Fin 1, F ![p.1, p.2] from
      Fintype.sum_equiv (piFinTwoEquiv fun _ => Fin 1) _ _ fun d => by
        congr 1
        funext i
        fin_cases i <;> simp,
    Fintype.sum_prod_type]

/-- The trace contraction of a bi-adjoint family: the Kronecker contraction of the two
  `u(1)` adjoint indices. -/
def traceContraction (hT : IsU1BiAdjoint B repGauge T) : B := ∑ a : Fin 1, T ![a, a]

/-- The trace contraction written as a sum over all pairs of adjoint indices weighted by
  the Kronecker delta. -/
lemma traceContraction_eq_sum (hT : IsU1BiAdjoint B repGauge T) :
    hT.traceContraction
      = ∑ d : Fin 2 → Fin 1, (if d 0 = d 1 then (1 : ℂ) else 0) • T d := by
  rw [sum_pi_two]
  simp [traceContraction, ite_smul]

/-- The trace contraction lies in the span of the components. -/
lemma traceContraction_mem_span (hT : IsU1BiAdjoint B repGauge T) :
    hT.traceContraction ∈ hT.span := by
  rw [traceContraction]
  exact sum_mem fun d _ =>
    Submodule.mem_iSup_of_mem _ (Submodule.mem_span_singleton_self _)

/-- The trace contraction of a bi-adjoint family is fixed by any linear map moving the
  components by a `U(1)` matrix, such a map fixing each component already. -/
lemma map_traceContraction (hT : IsU1BiAdjoint B repGauge T)
    {u : unitary ℂ} {f : B →ₗ[ℂ] B} (hf : IsU1BiAdjointMat u f T) :
    f hT.traceContraction = hT.traceContraction := by
  rw [traceContraction, map_sum]
  exact Finset.sum_congr rfl fun a _ => hf.map_T _

/-- The trace contraction of a bi-adjoint family is fixed by the hypercharge factor. That
  is all the transformation law constrains: the colour and isospin factors are free to
  move the trace contraction, and nothing here says that they do not. -/
lemma repGauge_traceContraction (hT : IsU1BiAdjoint B repGauge T) (u : unitary ℂ) :
    repGauge (1, 1, u) hT.traceContraction = hT.traceContraction :=
  hT.map_traceContraction (hT.repGauge_T u)

/-- The trace contraction is fixed by the hypercharge factor, under the name spelling out
  which factor is meant. This is `repGauge_traceContraction`. -/
lemma repGauge_u1_traceContraction (hT : IsU1BiAdjoint B repGauge T) (u : unitary ℂ) :
    repGauge (1, 1, u) hT.traceContraction = hT.traceContraction :=
  hT.repGauge_traceContraction u

/-!

## D. Invariance of the whole span

The `u(1)` adjoint index takes a single value and the `U(1)` factor acts trivially on it,
so every component of `T` is fixed by that factor, and hence so is every linear
combination of the components. At the level of submodules this says that the span sits
inside the invariants of `repU1 repGauge`, the hypercharge part of the representation.

Invariance under the whole gauge group is a different matter, and does not follow: the
colour and isospin factors are outside the transformation law and may move the components
as they please. Where they do not, as for the hypercharge field strengths of
`IsGaugeSector`, the law holds at every gauge element, and `span_le_invariants` takes
that as its hypothesis.

-/

/-- Every component of a bi-adjoint `u(1)` family is fixed by the hypercharge factor. -/
lemma repGauge_T_self (hT : IsU1BiAdjoint B repGauge T) (u : unitary ℂ)
    (l : Fin 2 → Fin 1) : repGauge (1, 1, u) (T l) = T l := (hT.repGauge_T u).map_T l

/-- Every element of the span of the components of a bi-adjoint `u(1)` family is fixed by
  any linear map obeying the transformation law. -/
lemma map_of_mem_span (hT : IsU1BiAdjoint B repGauge T) {u : unitary ℂ} {f : B →ₗ[ℂ] B}
    (hf : IsU1BiAdjointMat u f T) {x : B} (hx : x ∈ hT.span) : f x = x := by
  obtain ⟨c, rfl⟩ := (hT.mem_span_iff x).1 hx
  rw [map_sum]
  exact Finset.sum_congr rfl fun d _ => by rw [map_smul, hf.map_T d]

/-- Every element of the span of the components of a bi-adjoint `u(1)` family is fixed by
  the hypercharge factor. -/
lemma repGauge_of_mem_span (hT : IsU1BiAdjoint B repGauge T) (u : unitary ℂ) {x : B}
    (hx : x ∈ hT.span) : repGauge (1, 1, u) x = x :=
  hT.map_of_mem_span (hT.repGauge_T u) hx

/-- The span of the components of a bi-adjoint `u(1)` family lies in the invariants of
  the hypercharge part of the representation: the submodule form of
  `repGauge_of_mem_span`. -/
lemma span_le_repU1_invariants (hT : IsU1BiAdjoint B repGauge T) :
    hT.span ≤ (repU1 repGauge).invariants :=
  fun _ hx => (Representation.mem_invariants _ _).2 fun g =>
    hT.repGauge_of_mem_span (GaugeGroupI.toU1 g) hx

/-- The span of the components of a bi-adjoint `u(1)` family lies in the gauge
  invariants, once the transformation law is known to hold at every gauge element and not
  only at the hypercharge ones. The hypothesis cannot be dropped: `IsU1BiAdjoint` says
  nothing about the colour and isospin factors, so they may move the components. Where
  they do not, as for the hypercharge field strengths, the hypothesis is supplied from
  the transformation law of the underlying field. -/
lemma span_le_invariants (hT : IsU1BiAdjoint B repGauge T)
    (hmat : ∀ g : GaugeGroupI, IsU1BiAdjointMat (GaugeGroupI.toU1 g) (repGauge g) T) :
    hT.span ≤ repGauge.invariants :=
  fun _ hx => (Representation.mem_invariants _ _).2 fun g => hT.map_of_mem_span (hmat g) hx

end IsU1BiAdjoint

end StandardModel
