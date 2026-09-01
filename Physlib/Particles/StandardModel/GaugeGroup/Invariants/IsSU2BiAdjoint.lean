/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeAlgebra.Basis
public import Physlib.Particles.StandardModel.GaugeAlgebra.RootDecomposition
public import Physlib.Particles.StandardModel.GaugeGroup.SU2PermDecomposition
public import Mathlib.Algebra.TrivSqZeroExt.Basic
/-!
# Gauge tensors carrying two `su(2)` adjoint indices

`IsSU2BiAdjoint B repGauge T` says that a family `T`, indexed by two `su(2)` adjoint
indices and valued in a module `B` carrying a representation of the gauge group
`GaugeGroupI`, transforms as a tensor `T^{a₁ a₂}` in the `su(2)` factor of the adjoint
representation.

This is the gauge analogue of `IsQuadLorentz`. The field strength of the `W` bosons
carries one `su(2)` adjoint index, so a product of two field strengths carries two, and
the proposition here records how such a product transforms.

The transformation law itself is `IsSU2BiAdjointMat`, which relates one element of
`SU(2)` to one linear map on `B` and mentions no other factor of the gauge group, through
`su2AdjointMatrix`, the adjoint matrix of an `SU(2)` element alone. `IsSU2BiAdjoint` says
that the isospin transformation `(1, U, 1)` obeys that law with the matrix of `U`, for
every `U` in `SU(2)`, and it says nothing whatever about the colour and hypercharge
factors: those may move the components as they please. So the mathematics here is `SU(2)`
mathematics twice over, in the law and in the hypothesis, and the conclusions are about
invariance under the isospin factor.

Two things follow that are worth stating at the outset. The gauge weight decomposition
must know how all four torus generators act, and only `gaugeTorusGen 2` is an isospin
transformation, so the decomposition cannot be built for `repGauge`. It is built instead
for `repSU2 repGauge` of section A.3, the isospin part of the representation, which sends
the colour and hypercharge generators to the identity and so gives them weight zero by
construction rather than by hypothesis. And the trace contraction is fixed by the isospin
factor only; the statements that need it to be gauge invariant, `mem_span_and_invariant_iff`,
`su2_invariant_iff_invariant` and `mem_span_sup_invariant_iff`, take that invariance as an
explicit hypothesis, since nothing here proves it.

Section A gives the adjoint matrix of the `SU(2)` factor, the proposition and the span of
its components, section B the trace contraction, which is the natural isospin invariant
built from two adjoint indices, and section C the gauge weight decomposition of the span,
for the isospin part of the representation, ending with the zero-weight piece, the three
lines the torus alone cannot separate. Section D classifies the isospin invariants. The
`SU(2)` Weyl element is a half turn about the Cartan axis, and it cuts the three lines to
two; a third of a turn about the diagonal axis of the three Pauli directions, which is not
in the normaliser of the torus, cuts those two down to the one line through the trace
contraction. So `mem_span_and_su2_invariant_iff` says the isospin invariants in the span
are exactly the multiples of the trace contraction, the single singlet of `3 ⊗ 3`.
Sections D.4 and D.5 shed the hypotheses that classification is stated under. The trivial
square-zero extension of a module is an algebra on which every representation acts by
algebra maps, so the classification needs no algebra structure and no multiplicativity at
all, and it then descends to the quotient by a stable submodule, which is
`mem_span_sup_su2_invariant_iff`. The row orthonormality of `su2AdjointMatrix` that
section B rests on is inherited from the `su(2)` block of `adjointMatrix`, and proved
where that matrix is defined, in `GaugeAlgebra.Basis`.
-/

@[expose] public section

namespace StandardModel

open Matrix PauliMatrix

/-!

## A. The `SU(2)` adjoint matrix and bi-adjoint families

An `su(2)` adjoint index is acted on by the `SU(2)` factor of the gauge group alone. That
action is recorded in A.1 as `su2AdjointMatrix`, a matrix built from an element of `SU(2)`
and nothing else, A.2 phrases the transformation law through it, so that no other factor
of the gauge group appears in the law nor in the hypothesis, and A.3 reads a
representation of the gauge group at its isospin factor alone.

## A.1. The adjoint matrix of the `SU(2)` factor

The matrix is the trace pairing of the Pauli basis of `su(2)` with the Pauli basis
conjugated by the `SU(2)` element. It is the `su(2)` block of
`GaugeAlgebra.adjointMatrix`, definitionally so, and inherits from it the orthonormality
of its rows.

-/

/-- The adjoint matrix of an element of `SU(2)`: the trace pairing of the Pauli basis of
  `su(2)` with the Pauli basis conjugated by that element. -/
noncomputable def su2AdjointMatrix (U : specialUnitaryGroup (Fin 2) ℂ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j =>
    2⁻¹ * (Matrix.trace (pauliMatrix (Sum.inr i) *
      (U.1 * pauliMatrix (Sum.inr j) * star U.1))).re

/-- The entries of the adjoint matrix of an element of `SU(2)`. -/
@[simp]
lemma su2AdjointMatrix_apply (U : specialUnitaryGroup (Fin 2) ℂ) (i j : Fin 3) :
    su2AdjointMatrix U i j
      = 2⁻¹ * (Matrix.trace (pauliMatrix (Sum.inr i) *
          (U.1 * pauliMatrix (Sum.inr j) * star U.1))).re := rfl

/-- The adjoint matrix of the `SU(2)` factor of a gauge group element is the `su(2)`
  block of the adjoint matrix of the gauge algebra. -/
lemma su2AdjointMatrix_toSU2 (g : GaugeGroupI) (i j : Fin 3) :
    su2AdjointMatrix (GaugeGroupI.toSU2 g) i j
      = GaugeAlgebra.adjointMatrix g (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl j)) := rfl

/-- The rows of the adjoint matrix of an element of `SU(2)` are orthonormal, the adjoint
  action preserving the trace pairing of the Pauli basis. -/
lemma sum_su2AdjointMatrix_row_mul (U : specialUnitaryGroup (Fin 2) ℂ) (c d : Fin 3) :
    ∑ a : Fin 3, su2AdjointMatrix U c a * su2AdjointMatrix U d a
      = if c = d then 1 else 0 :=
  GaugeAlgebra.sum_adjointMatrix_inr_inl_row_mul (1, U, 1) c d

/-!

## A.2. Bi-adjoint `su(2)` families and the span of their components

The transformation law carries one factor of `su2AdjointMatrix` per index, with the
summed index in the row slot, exactly as `IsSU2BiFundamental` carries one factor of the
fundamental matrix per index. It is recorded by `IsSU2BiAdjointMat`, a relation between
one element of `SU(2)` and one linear map on `B` in which no other factor of the gauge
group appears, and it is the law obeyed by the `W`-boson field strengths of
`IsGaugeSector`.

`IsSU2BiAdjoint` then says that the gauge transformation `(1, U, 1)` obeys that law with
the matrix of `U`, for every `U` in `SU(2)`. Since `U ↦ (1, U, 1)` is a monoid
homomorphism this is an action of `SU(2)`, and it is all that is assumed: a gauge
transformation with a nontrivial colour or hypercharge factor is not mentioned, and may
move the components arbitrarily. So nothing here forces the colour and hypercharge
coordinates of a weight to vanish; section C gets that instead from `repSU2`, which sends
the colour and hypercharge generators to the identity outright.

-/

/-- The linear map `f` moves the components of the family `T` as the `SU(2)` matrix `U`
  moves a tensor with two adjoint indices: one factor of `su2AdjointMatrix U` per index,
  with the summed index in the row slot. -/
def IsSU2BiAdjointMat {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (U : specialUnitaryGroup (Fin 2) ℂ) (f : B →ₗ[ℂ] B)
    (T : (Fin 2 → Fin 3) → B) : Prop :=
  ∀ l : Fin 2 → Fin 3,
    f (T l) = ∑ a : Fin 2 → Fin 3,
      (∏ i : Fin 2, ((su2AdjointMatrix U (a i) (l i) : ℝ) : ℂ)) • T a

/-- A family `T` of elements of `B`, indexed by two `su(2)` adjoint indices, transforms
  as a tensor `T^{a₁ a₂}` under the representation `repGauge` of the gauge group: an
  isospin transformation moves the components by the `SU(2)` element it is built from.
  Nothing is asked of the colour or hypercharge factors. -/
structure IsSU2BiAdjoint (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B)
    (T : (Fin 2 → Fin 3) → B) : Prop where
  repGauge_T : ∀ g : specialUnitaryGroup (Fin 2) ℂ,
    IsSU2BiAdjointMat g (repGauge (1, g, 1)) T

/-!

## A.3. The isospin part of a representation

Reading a representation of the gauge group at the isospin factor of its argument alone
gives `repSU2`, again a representation of the whole gauge group. Every construction stated
for a representation of `GaugeGroupI` therefore applies to it verbatim, and a bi-adjoint
family for `repGauge` is a bi-adjoint family for `repSU2 repGauge`, with the same span and
the same trace contraction. Invariance under it is invariance under the isospin factor,
`∀ U : SU(2), repGauge (1, U, 1) x = x`, which is exactly what the transformation law
constrains.

`repSU2` carries the weight bookkeeping of section C, which needs a representation of the
whole gauge group and is not available for `repGauge` itself, and it transports the
statements of section D that are proved for a representation of `GaugeGroupI`. The
statements themselves are written with the isospin transformation `(1, U, 1)` spelled out,
so that reading one needs no unfolding, and `repSU2_invariant_iff_su2` is the bridge
between the two spellings.

-/

/-- The isospin part of a representation of the gauge group: the representation reading
  only the `SU(2)` factor of its argument and sending the colour and hypercharge factors
  to the identity. -/
noncomputable def repSU2 {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B) : Representation ℂ GaugeGroupI B where
  toFun g := repGauge (1, GaugeGroupI.toSU2 g, 1)
  map_one' := by
    have h1 : ((1, GaugeGroupI.toSU2 1, 1) : GaugeGroupI) = 1 := by
      simp [Prod.ext_iff]
    rw [h1, map_one]
  map_mul' g h := by
    have hgh : ((1, GaugeGroupI.toSU2 (g * h), 1) : GaugeGroupI)
        = ((1, GaugeGroupI.toSU2 g, 1) : GaugeGroupI) * (1, GaugeGroupI.toSU2 h, 1) := by
      simp [map_mul]
    rw [hgh, map_mul]

/-- The isospin part of a representation acts by the representation itself, at the gauge
  transformation with the same isospin factor and nothing else. -/
lemma repSU2_apply {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B) (g : GaugeGroupI) :
    repSU2 repGauge g = repGauge (1, GaugeGroupI.toSU2 g, 1) := rfl

/-- The isospin part of a representation acts by algebra maps whenever the representation
  does, each of its values being a value of that representation. -/
lemma isMulRep_repSU2 {B : Type*} [Ring B] [Algebra ℂ B]
    {repGauge : Representation ℂ GaugeGroupI B} (hmul : IsMulRep repGauge) :
    IsMulRep (repSU2 repGauge) :=
  fun g x y => hmul (1, GaugeGroupI.toSU2 g, 1) x y

/-- Invariance under the isospin part of a representation is invariance under the gauge
  transformations that are trivial on colour and hypercharge. The isospin part reads only
  the isospin factor of its argument, and every element of `SU(2)` is the isospin factor
  of such a transformation. -/
lemma repSU2_invariant_iff_su2 {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B) (x : B) :
    (∀ g : GaugeGroupI, repSU2 repGauge g x = x)
      ↔ ∀ U : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, U, 1) x = x :=
  ⟨fun h U => h (1, U, 1), fun h g => h (GaugeGroupI.toSU2 g)⟩

/-- A submodule is stable under the isospin part of a representation precisely when it is
  stable under the gauge transformations trivial on colour and hypercharge. -/
lemma repSU2_stable_iff_su2 {B : Type*} [AddCommGroup B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B) (S : Submodule ℂ B) :
    (∀ g : GaugeGroupI, ∀ y ∈ S, repSU2 repGauge g y ∈ S)
      ↔ ∀ U : specialUnitaryGroup (Fin 2) ℂ, ∀ y ∈ S, repGauge (1, U, 1) y ∈ S :=
  ⟨fun h U => h (1, U, 1), fun h g => h (GaugeGroupI.toSU2 g)⟩

namespace IsSU2BiAdjoint
set_option linter.unusedVariables false

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {T : (Fin 2 → Fin 3) → B}
  (hT : IsSU2BiAdjoint B repGauge T)

/-- A bi-adjoint family for a representation is a bi-adjoint family for its isospin part:
  the transformation law reads only the isospin factor to begin with. The span and the
  trace contraction do not mention the representation, so every statement of this file
  transports along this and is read at the isospin factor alone. -/
lemma toRepSU2 (hT : IsSU2BiAdjoint B repGauge T) :
    IsSU2BiAdjoint B (repSU2 repGauge) T where
  repGauge_T g := hT.repGauge_T g

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

## B. The trace contraction

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

/-- The trace contraction of a bi-adjoint family is fixed by any linear map moving the
  components by an `SU(2)` matrix: the rows of `su2AdjointMatrix` are orthonormal, so the
  Kronecker delta contracting the two indices is carried to itself. -/
lemma map_traceContraction (hT : IsSU2BiAdjoint B repGauge T)
    {U : specialUnitaryGroup (Fin 2) ℂ} {f : B →ₗ[ℂ] B}
    (hf : IsSU2BiAdjointMat U f T) :
    f hT.traceContraction = hT.traceContraction := by
  have step : f hT.traceContraction
      = ∑ b : Fin 2 → Fin 3, (if b 0 = b 1 then (1 : ℂ) else 0) • T b := by
    show f (∑ c : Fin 3, T ![c, c]) = _
    rw [map_sum]
    have h1 : ∀ c : Fin 3, f (T ![c, c])
        = ∑ b : Fin 2 → Fin 3,
          ((su2AdjointMatrix U (b 0) c * su2AdjointMatrix U (b 1) c : ℝ) : ℂ) • T b := by
      intro c
      rw [hf ![c, c]]
      refine Finset.sum_congr rfl fun b _ => ?_
      congr 1
      simp [Fin.prod_univ_two]
    simp only [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    rw [← Complex.ofReal_sum, sum_su2AdjointMatrix_row_mul]
    simp [apply_ite]
  rw [step, ← hT.traceContraction_eq_sum]

/-- The trace contraction of a bi-adjoint family is fixed by the isospin factor. That is
  all the transformation law constrains: the colour and hypercharge factors are free to
  move the trace contraction, and in general they do. -/
lemma repGauge_traceContraction (hT : IsSU2BiAdjoint B repGauge T)
    (U : specialUnitaryGroup (Fin 2) ℂ) :
    repGauge (1, U, 1) hT.traceContraction = hT.traceContraction :=
  hT.map_traceContraction (hT.repGauge_T U)

/-- The trace contraction is fixed by the isospin factor, under the name spelling out
  which factor is meant. This is `repGauge_traceContraction`. -/
lemma repGauge_su2_traceContraction (hT : IsSU2BiAdjoint B repGauge T)
    (U : specialUnitaryGroup (Fin 2) ℂ) :
    repGauge (1, U, 1) hT.traceContraction = hT.traceContraction :=
  hT.repGauge_traceContraction U

end IsSU2BiAdjoint

/-!

## C. The gauge weight decomposition of the span

The Pauli basis vectors are not eigenvectors of the gauge torus, so the components `T d`
do not carry a definite gauge weight. The eigenvectors appear only after passing to the
weight basis of the `su(2)` adjoint: for the one root direction the two complex
combinations `x₁ ± i x₂` of the paired Pauli coordinates, and the Cartan direction as it
stands. That is three coordinate vectors, recorded in `wtCoeff`, with weights `wtWeight`.
The Cartan direction is named in the gauge algebra itself, as `GaugeAlgebra.su2CartanId`,
since the Cartan directions of the whole algebra are assembled from it and its `su(3)`
companions; the root pair is recorded here and matched with that of the whole algebra
below.

With two adjoint indices a weight vector is a product of two of these, contracted against
`T` by `biVec`, and its weight is the sum of the two individual weights. There are nine
such products, they span the same subspace as the components, and joining their lines one
weight at a time gives `gaugeWeightDecomposition`.

That decomposition is for `repSU2 repGauge`, not for `repGauge`. A decomposition must say
how all four torus generators act, and of the four only `gaugeTorusGen 2` is an isospin
transformation, so the transformation law says nothing about the other three. The isospin
part sends them to the identity, so it fixes every weight vector there and their colour
and hypercharge coordinates vanish for that reason. This is why
`gaugeWeightDecomposition_supp` still lists only the five weights of the tensor square of
the `su(2)` adjoint, all of them of the form `(0, 0, k, 0)`.

The stronger typeclass assumptions are forced: `GaugeWeightDecomposition` lives in an
algebra and records multiplicativity of the representation, neither of which
`IsSU2BiAdjoint` needs, so both appear as extra arguments here.

-/

namespace IsSU2BiAdjoint

set_option linter.unusedVariables false

/-!

## C.1. The weight basis of the `su(2)` adjoint

-/

/-- The index type of the `su(2)` adjoint weight basis: the positive root, the negative
  root and the Cartan direction. -/
abbrev WeightIdx : Type := Fin 1 ⊕ Fin 1 ⊕ Fin 1

/-- The pair of Pauli indices making up the root direction of `su(2)`. -/
def rootPair : Fin 3 × Fin 3 := (0, 1)

/-- The gauge weight of the `su(2)` root direction. -/
def rootWt : GaugeWeight := (0, 0, 2, 0)

/-- The root direction here is the `su(2)` root direction of the full gauge algebra. -/
lemma rootIdx_three :
    GaugeAlgebra.rootIdx 3
      = (Sum.inr (Sum.inl rootPair.1), Sum.inr (Sum.inl rootPair.2)) := rfl

/-- The root weight here is the `su(2)` root weight of the full gauge algebra. -/
lemma rootWeight_three : GaugeAlgebra.rootWeight 3 = rootWt := rfl

/-- The Cartan direction here is the `su(2)` Cartan direction of the full gauge
  algebra. -/
lemma cartanIdx_two : GaugeAlgebra.cartanIdx 2 = Sum.inr (Sum.inl GaugeAlgebra.su2CartanId) := rfl

/-- Every Pauli index is either one of the two members of the root pair or the Cartan
  index. -/
lemma eq_rootPair_or_cartanId (a : Fin 3) :
    a = rootPair.1 ∨ a = rootPair.2 ∨ a = GaugeAlgebra.su2CartanId := by
  revert a
  decide

/-!

## C.2. The `SU(2)` adjoint matrix of a torus generator in the weight basis

-/

/-- A standard coordinate functional evaluated on a standard basis vector. -/
lemma coord_stdBasis_apply (b a : Fin 8 ⊕ Fin 3 ⊕ Fin 1) :
    GaugeAlgebra.stdBasis.coord b (GaugeAlgebra.stdBasis a) = if a = b then 1 else 0 := by
  simp [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]

/-- The entries of the adjoint matrix, read off the dual adjoint action of the inverse on
  the standard coordinate functionals. -/
lemma dualMap_coord_apply (g : GaugeGroupI) (a b : Fin 8 ⊕ Fin 3 ⊕ Fin 1) :
    (GaugeAlgebra.adjointMap g⁻¹).dualMap (GaugeAlgebra.stdBasis.coord b)
        (GaugeAlgebra.stdBasis a)
      = GaugeAlgebra.adjointMatrix g a b := by
  have h1 : GaugeAlgebra.adjointMap g⁻¹ (GaugeAlgebra.stdBasis a)
      = ∑ c, GaugeAlgebra.adjointMatrix g⁻¹ c a • GaugeAlgebra.stdBasis c :=
    GaugeAlgebra.adjoint_stdBasis g⁻¹ a
  rw [LinearMap.dualMap_apply, h1, map_sum]
  simp only [map_smul, smul_eq_mul, coord_stdBasis_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [GaugeAlgebra.adjointMatrix_inv_apply]

/-- The first column of the root pair: the torus rotates the two columns of the `SU(2)`
  adjoint matrix belonging to the root direction into each other. -/
lemma su2AdjointMatrix_rootPair_fst (i : Fin 4) (a : Fin 3) :
    su2AdjointMatrix (GaugeGroupI.toSU2 (gaugeTorusGen i)) a rootPair.1
      = ((expI : ℂ) ^ GaugeWeight.coord rootWt i).re *
          (if a = rootPair.1 then 1 else 0)
        - ((expI : ℂ) ^ GaugeWeight.coord rootWt i).im *
          (if a = rootPair.2 then 1 else 0) := by
  rw [su2AdjointMatrix_toSU2]
  obtain ⟨p1, -⟩ := GaugeAlgebra.dualMap_pair_of_entry
    (GaugeAlgebra.coord_rootIdx_fst 3)
    (GaugeAlgebra.coord_rootIdx_snd 3)
    (GaugeAlgebra.rootEntry_adjointMap 3 i)
  simp only [rootIdx_three, rootWeight_three] at p1
  have e := LinearMap.congr_fun p1 (GaugeAlgebra.stdBasis (Sum.inr (Sum.inl a)))
  rw [dualMap_coord_apply] at e
  rw [e]
  simp [Finsupp.single_apply]

/-- The second column of the root pair. -/
lemma su2AdjointMatrix_rootPair_snd (i : Fin 4) (a : Fin 3) :
    su2AdjointMatrix (GaugeGroupI.toSU2 (gaugeTorusGen i)) a rootPair.2
      = ((expI : ℂ) ^ GaugeWeight.coord rootWt i).im *
          (if a = rootPair.1 then 1 else 0)
        + ((expI : ℂ) ^ GaugeWeight.coord rootWt i).re *
          (if a = rootPair.2 then 1 else 0) := by
  rw [su2AdjointMatrix_toSU2]
  obtain ⟨-, p2⟩ := GaugeAlgebra.dualMap_pair_of_entry
    (GaugeAlgebra.coord_rootIdx_fst 3)
    (GaugeAlgebra.coord_rootIdx_snd 3)
    (GaugeAlgebra.rootEntry_adjointMap 3 i)
  simp only [rootIdx_three, rootWeight_three] at p2
  have e := LinearMap.congr_fun p2 (GaugeAlgebra.stdBasis (Sum.inr (Sum.inl a)))
  rw [dualMap_coord_apply] at e
  rw [e]
  simp [Finsupp.single_apply]

/-- The torus fixes the Cartan column of the `SU(2)` adjoint matrix. -/
lemma su2AdjointMatrix_cartanId (i : Fin 4) (a : Fin 3) :
    su2AdjointMatrix (GaugeGroupI.toSU2 (gaugeTorusGen i)) a GaugeAlgebra.su2CartanId
      = if a = GaugeAlgebra.su2CartanId then 1 else 0 := by
  rw [su2AdjointMatrix_toSU2]
  have p := GaugeAlgebra.dualMap_coord_cartanIdx 2 i
  simp only [cartanIdx_two] at p
  have e := LinearMap.congr_fun p (GaugeAlgebra.stdBasis (Sum.inr (Sum.inl a)))
  rw [dualMap_coord_apply] at e
  rw [e]
  simp [Finsupp.single_apply]

/-!

## C.3. The weight vectors of one adjoint index

-/

/-- The coordinates of the `su(2)` adjoint weight basis in the Pauli basis: for the root
  the two combinations `x₁ ± i x₂` of the paired coordinates, and for the Cartan
  direction the coordinate itself. -/
noncomputable def wtCoeff : WeightIdx → Fin 3 → ℂ
  | Sum.inl _, a => (if a = rootPair.1 then 1 else 0)
      + Complex.I * (if a = rootPair.2 then 1 else 0)
  | Sum.inr (Sum.inl _), a => (if a = rootPair.1 then 1 else 0)
      - Complex.I * (if a = rootPair.2 then 1 else 0)
  | Sum.inr (Sum.inr _), a => if a = GaugeAlgebra.su2CartanId then 1 else 0

/-- The gauge weight carried by each `su(2)` adjoint weight vector. -/
def wtWeight : WeightIdx → GaugeWeight
  | Sum.inl _ => rootWt
  | Sum.inr (Sum.inl _) => -rootWt
  | Sum.inr (Sum.inr _) => 0

/-- The coordinate vector of a single Pauli direction. -/
def unitVec (a : Fin 3) : Fin 3 → ℂ := fun x => if x = a then 1 else 0

/-- The action of an element of `SU(2)` on the coordinates of one `su(2)` adjoint
  index. -/
noncomputable def rowAct (U : specialUnitaryGroup (Fin 2) ℂ) (c : Fin 3 → ℂ) :
    Fin 3 → ℂ := fun a =>
  ∑ x : Fin 3, ((su2AdjointMatrix U a x : ℝ) : ℂ) * c x

/-- Collapsing a sum against the two Kronecker deltas of the root pair. -/
lemma sum_mul_pair (f : Fin 3 → ℂ) (b₁ b₂ : Fin 3) (s : ℂ) :
    ∑ x : Fin 3, f x * ((if x = b₁ then (1 : ℂ) else 0) + s * (if x = b₂ then 1 else 0))
      = f b₁ + s * f b₂ := by
  have h : ∀ x : Fin 3,
      f x * ((if x = b₁ then (1 : ℂ) else 0) + s * (if x = b₂ then 1 else 0))
        = (if x = b₁ then f x else 0) + (if x = b₂ then s * f x else 0) := by
    intro x
    split_ifs <;> ring
  simp only [h]
  simp [Finset.sum_add_distrib]

/-- The complex pair identity behind the positive root eigenvector. -/
lemma pair_add_eq (z u v : ℂ) :
    (z.re : ℂ) * u - (z.im : ℂ) * v + Complex.I * ((z.im : ℂ) * u + (z.re : ℂ) * v)
      = z * (u + Complex.I * v) := by
  conv_rhs => rw [← Complex.re_add_im z]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The complex pair identity behind the negative root eigenvector. -/
lemma pair_sub_eq (z u v : ℂ) :
    (z.re : ℂ) * u - (z.im : ℂ) * v - Complex.I * ((z.im : ℂ) * u + (z.re : ℂ) * v)
      = (starRingEnd ℂ) z * (u - Complex.I * v) := by
  rw [show (starRingEnd ℂ) z = (z.re : ℂ) - (z.im : ℂ) * Complex.I by
    rw [Complex.ext_iff]; simp]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Each weight vector of the `su(2)` adjoint is an eigenvector of every torus generator,
  at the character of its weight. -/
lemma rowAct_wtCoeff (i : Fin 4) (k : WeightIdx) :
    rowAct (GaugeGroupI.toSU2 (gaugeTorusGen i)) (wtCoeff k)
      = ((expI : ℂ) ^ GaugeWeight.coord (wtWeight k) i) • wtCoeff k := by
  funext a
  match k with
  | Sum.inl r =>
    show ∑ x : Fin 3, _ = _
    simp only [wtCoeff]
    rw [sum_mul_pair, su2AdjointMatrix_rootPair_fst, su2AdjointMatrix_rootPair_snd]
    simp only [wtCoeff, wtWeight, Pi.smul_apply, smul_eq_mul,
      apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_one, Complex.ofReal_zero,
      Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul]
    exact pair_add_eq _ _ _
  | Sum.inr (Sum.inl r) =>
    show ∑ x : Fin 3, _ = _
    have hneg : ∀ x : Fin 3, wtCoeff (Sum.inr (Sum.inl r)) x
        = (if x = rootPair.1 then (1 : ℂ) else 0)
          + (-Complex.I) * (if x = rootPair.2 then 1 else 0) := by
      intro x
      simp only [wtCoeff]
      ring
    simp only [hneg]
    rw [sum_mul_pair, su2AdjointMatrix_rootPair_fst, su2AdjointMatrix_rootPair_snd]
    simp only [wtWeight, Pi.smul_apply, smul_eq_mul,
      apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_one, Complex.ofReal_zero,
      Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul]
    rw [show ((expI : ℂ) ^ GaugeWeight.coord (-rootWt) i)
        = (starRingEnd ℂ) ((expI : ℂ) ^ GaugeWeight.coord rootWt i) from by
      rw [starRingEnd_expI_zpow, GaugeWeight.coord_neg]]
    simp only [show ∀ x y : ℂ, x + -Complex.I * y = x - Complex.I * y from
      fun x y => by ring]
    exact pair_sub_eq _ _ _
  | Sum.inr (Sum.inr c) =>
    show ∑ x : Fin 3, _ = _
    simp only [wtCoeff, wtWeight, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, su2AdjointMatrix_cartanId, Pi.smul_apply, smul_eq_mul,
      GaugeWeight.zero_coord, zpow_zero,
      apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_one, Complex.ofReal_zero]

/-!

## C.4. The bi-adjoint weight vectors and their span

-/

section Decomposition

variable {B : Type*} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {T : (Fin 2 → Fin 3) → B}

/-- The element of `B` obtained by contracting the two `su(2)` adjoint indices of `T`
  against a pair of coordinate vectors. -/
noncomputable def biVec (hT : IsSU2BiAdjoint B repGauge T) (c₀ c₁ : Fin 3 → ℂ) : B :=
  ∑ d : Fin 2 → Fin 3, (c₀ (d 0) * c₁ (d 1)) • T d

variable (hT : IsSU2BiAdjoint B repGauge T)

/-- Contracting against a scaled coordinate vector on the left. -/
lemma biVec_smul_left (z : ℂ) (c₀ c₁ : Fin 3 → ℂ) :
    hT.biVec (z • c₀) c₁ = z • hT.biVec c₀ c₁ := by
  simp only [biVec, Finset.smul_sum, Pi.smul_apply, smul_eq_mul, smul_smul, mul_assoc]

/-- Contracting against a scaled coordinate vector on the right. -/
lemma biVec_smul_right (z : ℂ) (c₀ c₁ : Fin 3 → ℂ) :
    hT.biVec c₀ (z • c₁) = z • hT.biVec c₀ c₁ := by
  simp only [biVec, Finset.smul_sum, Pi.smul_apply, smul_eq_mul, smul_smul]
  exact Finset.sum_congr rfl fun d _ => by ring_nf

/-- Contracting against a sum of coordinate vectors on the left. -/
lemma biVec_add_left (c₀ c₀' c₁ : Fin 3 → ℂ) :
    hT.biVec (c₀ + c₀') c₁ = hT.biVec c₀ c₁ + hT.biVec c₀' c₁ := by
  simp only [biVec, Pi.add_apply, add_mul, add_smul, Finset.sum_add_distrib]

/-- Contracting against a difference of coordinate vectors on the left. -/
lemma biVec_sub_left (c₀ c₀' c₁ : Fin 3 → ℂ) :
    hT.biVec (c₀ - c₀') c₁ = hT.biVec c₀ c₁ - hT.biVec c₀' c₁ := by
  simp only [biVec, Pi.sub_apply, sub_mul, sub_smul, Finset.sum_sub_distrib]

/-- Contracting against a sum of coordinate vectors on the right. -/
lemma biVec_add_right (c₀ c₁ c₁' : Fin 3 → ℂ) :
    hT.biVec c₀ (c₁ + c₁') = hT.biVec c₀ c₁ + hT.biVec c₀ c₁' := by
  simp only [biVec, Pi.add_apply, mul_add, add_smul, Finset.sum_add_distrib]

/-- Contracting against a difference of coordinate vectors on the right. -/
lemma biVec_sub_right (c₀ c₁ c₁' : Fin 3 → ℂ) :
    hT.biVec c₀ (c₁ - c₁') = hT.biVec c₀ c₁ - hT.biVec c₀ c₁' := by
  simp only [biVec, Pi.sub_apply, mul_sub, sub_smul, Finset.sum_sub_distrib]

/-- Negating both coordinate vectors leaves the contraction unchanged: the two signs
  cancel against each other. -/
lemma biVec_neg_neg (c₀ c₁ : Fin 3 → ℂ) : hT.biVec (-c₀) (-c₁) = hT.biVec c₀ c₁ := by
  simp only [biVec, Pi.neg_apply, neg_mul_neg]

/-- Contracting against two single Pauli directions returns a component of `T`. -/
lemma biVec_unitVec (a b : Fin 3) : hT.biVec (unitVec a) (unitVec b) = T ![a, b] := by
  rw [biVec, sum_pi_two]
  simp [unitVec, ite_smul]

/-- A map moving the components by an `SU(2)` matrix moves a contraction against a pair
  of coordinate vectors by the row action of that matrix on each of them. This is the
  whole content of the transformation law in coordinate form, and it mentions no other
  factor of the gauge group. -/
lemma map_biVec (hT : IsSU2BiAdjoint B repGauge T) {U : specialUnitaryGroup (Fin 2) ℂ}
    {f : B →ₗ[ℂ] B} (hf : IsSU2BiAdjointMat U f T) (c₀ c₁ : Fin 3 → ℂ) :
    f (hT.biVec c₀ c₁) = hT.biVec (rowAct U c₀) (rowAct U c₁) := by
  have step : ∀ d : Fin 2 → Fin 3, f ((c₀ (d 0) * c₁ (d 1)) • T d)
      = ∑ a : Fin 2 → Fin 3,
        ((c₀ (d 0) * c₁ (d 1)) *
          (((su2AdjointMatrix U (a 0) (d 0) : ℝ) : ℂ) *
            ((su2AdjointMatrix U (a 1) (d 1) : ℝ) : ℂ)))
          • T a := by
    intro d
    rw [map_smul, hf d, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_smul, Fin.prod_univ_two]
  simp only [biVec, rowAct]
  rw [map_sum]
  simp only [step]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  rw [sum_pi_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

/-- An isospin transformation moves a contraction against a pair of coordinate vectors
  by the row action of its `SU(2)` element. -/
lemma repGauge_su2_biVec (U : specialUnitaryGroup (Fin 2) ℂ) (c₀ c₁ : Fin 3 → ℂ) :
    repGauge (1, U, 1) (hT.biVec c₀ c₁) = hT.biVec (rowAct U c₀) (rowAct U c₁) :=
  hT.map_biVec (hT.repGauge_T U) c₀ c₁

/-- The isospin part of the representation moves a contraction against a pair of
  coordinate vectors by the row action of the `SU(2)` factor of its argument. Unlike the
  representation itself, the isospin part is constrained at every gauge transformation,
  which is what lets the weight decomposition be built for it. -/
lemma repSU2_biVec (g : GaugeGroupI) (c₀ c₁ : Fin 3 → ℂ) :
    repSU2 repGauge g (hT.biVec c₀ c₁)
      = hT.biVec (rowAct (GaugeGroupI.toSU2 g) c₀) (rowAct (GaugeGroupI.toSU2 g) c₁) :=
  hT.repGauge_su2_biVec (GaugeGroupI.toSU2 g) c₀ c₁

/-- The bi-adjoint weight vectors are simultaneous eigenvectors of the gauge torus in the
  isospin part of the representation, at the character of the sum of the two individual
  weights. The colour and hypercharge generators have trivial isospin factor, so the
  isospin part fixes every weight vector at those, matching the vanishing colour and
  hypercharge coordinates of the weights. -/
lemma repSU2_biVec_wtCoeff (k₀ k₁ : WeightIdx) (i : Fin 4) :
    repSU2 repGauge (gaugeTorusGen i) (hT.biVec (wtCoeff k₀) (wtCoeff k₁))
      = ((expI : ℂ) ^ GaugeWeight.coord (wtWeight k₀ + wtWeight k₁) i)
        • hT.biVec (wtCoeff k₀) (wtCoeff k₁) := by
  rw [hT.repSU2_biVec, rowAct_wtCoeff, rowAct_wtCoeff, hT.biVec_smul_left,
    hT.biVec_smul_right, smul_smul, GaugeWeight.coord_add,
    zpow_add₀ expI_ne_zero]

/-- The join of the lines spanned by the bi-adjoint weight vectors. -/
noncomputable def wtSpan (hT : IsSU2BiAdjoint B repGauge T) : Submodule ℂ B :=
  ⨆ k : WeightIdx × WeightIdx, ℂ ∙ hT.biVec (wtCoeff k.1) (wtCoeff k.2)

/-- The Pauli coordinate vector of the first member of the root pair, in the weight
  basis. -/
lemma unitVec_rootPair_fst :
    unitVec rootPair.1
      = (2 : ℂ)⁻¹ • (wtCoeff (Sum.inl 0) + wtCoeff (Sum.inr (Sum.inl 0))) := by
  funext x
  simp only [unitVec, wtCoeff, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The Pauli coordinate vector of the second member of the root pair, in the weight
  basis. -/
lemma unitVec_rootPair_snd :
    unitVec rootPair.2
      = (-(Complex.I / 2)) • (wtCoeff (Sum.inl 0) - wtCoeff (Sum.inr (Sum.inl 0))) := by
  funext x
  simp only [unitVec, wtCoeff, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The Cartan direction is already a weight vector. -/
lemma unitVec_cartanId : unitVec GaugeAlgebra.su2CartanId = wtCoeff (Sum.inr (Sum.inr 0)) := rfl

/-- Contracting a weight vector against a single Pauli direction stays in the join of the
  weight lines. -/
lemma biVec_wtCoeff_unitVec_mem (k : WeightIdx) (b : Fin 3) :
    hT.biVec (wtCoeff k) (unitVec b) ∈ hT.wtSpan := by
  have hgen : ∀ k' : WeightIdx, hT.biVec (wtCoeff k) (wtCoeff k') ∈ hT.wtSpan :=
    fun k' => Submodule.mem_iSup_of_mem (k, k') (Submodule.mem_span_singleton_self _)
  rcases eq_rootPair_or_cartanId b with rfl | rfl | rfl
  · rw [unitVec_rootPair_fst, hT.biVec_smul_right, hT.biVec_add_right]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ (hgen _) (hgen _))
  · rw [unitVec_rootPair_snd, hT.biVec_smul_right, hT.biVec_sub_right]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hgen _) (hgen _))
  · rw [unitVec_cartanId]
    exact hgen _

/-- Every component of `T` lies in the join of the weight lines. -/
lemma biVec_unitVec_mem (a b : Fin 3) :
    hT.biVec (unitVec a) (unitVec b) ∈ hT.wtSpan := by
  rcases eq_rootPair_or_cartanId a with rfl | rfl | rfl
  · rw [unitVec_rootPair_fst, hT.biVec_smul_left, hT.biVec_add_left]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _
      (hT.biVec_wtCoeff_unitVec_mem _ _) (hT.biVec_wtCoeff_unitVec_mem _ _))
  · rw [unitVec_rootPair_snd, hT.biVec_smul_left, hT.biVec_sub_left]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _
      (hT.biVec_wtCoeff_unitVec_mem _ _) (hT.biVec_wtCoeff_unitVec_mem _ _))
  · rw [unitVec_cartanId]
    exact hT.biVec_wtCoeff_unitVec_mem _ _

/-- The weight vectors span the components. The change of basis from the Pauli basis
  to the weight basis is invertible, so nothing is lost. -/
lemma span_eq_wtSpan : hT.span = hT.wtSpan := by
  refine le_antisymm (iSup_le fun d => (Submodule.span_singleton_le_iff_mem _ _).mpr ?_)
    (iSup_le fun k => (Submodule.span_singleton_le_iff_mem _ _).mpr ?_)
  · have hd : T d = T ![d 0, d 1] := by
      congr 1
      funext j
      fin_cases j <;> simp
    rw [hd, ← hT.biVec_unitVec]
    exact hT.biVec_unitVec_mem _ _
  · rw [span, biVec]
    exact sum_mem fun d _ => Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem d (Submodule.mem_span_singleton_self _))

/-!

## C.5. The decomposition

-/

/-- The gauge weight decomposition of the span of a bi-adjoint `su(2)` family, for the
  isospin part of the representation. The span is the join of the lines through the nine
  products of weight vectors, and each of those carries the sum of the two weights.

  The decomposition is for `repSU2 repGauge` and not for `repGauge` itself because a
  decomposition must know how all four torus generators act, and the transformation law
  constrains only the isospin factor: of the four generators only `gaugeTorusGen 2` is an
  isospin transformation. The isospin part sends the other three to the identity, so their
  weights vanish by construction. -/
@[implicit_reducible]
noncomputable def gaugeWeightDecomposition (hT : IsSU2BiAdjoint B repGauge T)
    (hmul : IsMulRep repGauge) : GaugeWeightDecomposition (repSU2 repGauge) hT.span :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup (isMulRep_repSU2 hmul) fun k : WeightIdx × WeightIdx =>
      GaugeWeightDecomposition.spanSingleton (isMulRep_repSU2 hmul)
        (hT.biVec (wtCoeff k.1) (wtCoeff k.2)) (wtWeight k.1 + wtWeight k.2)
        (hT.repSU2_biVec_wtCoeff k.1 k.2))
    _ hT.span_eq_wtSpan

/-- The pieces of the decomposition: the weight-`w` piece is the join of the lines through
  those products of weight vectors whose weights sum to `w`. -/
lemma gaugeWeightDecomposition_piece (hmul : IsMulRep repGauge) (w : GaugeWeight) :
    (hT.gaugeWeightDecomposition hmul).piece w
      = ⨆ k : WeightIdx × WeightIdx,
        (if w = wtWeight k.1 + wtWeight k.2 then
          ℂ ∙ hT.biVec (wtCoeff k.1) (wtCoeff k.2) else ⊥) := rfl

/-- The support of the decomposition, before evaluation. -/
lemma gaugeWeightDecomposition_supp_eq (hmul : IsMulRep repGauge) :
    (hT.gaugeWeightDecomposition hmul).supp
      = Finset.univ.biUnion fun k : WeightIdx × WeightIdx =>
        ({wtWeight k.1 + wtWeight k.2} : Finset GaugeWeight) := rfl

/-- The gauge weights carried by a bi-adjoint `su(2)` family: the five weights of the
  tensor square of the `su(2)` adjoint. Every one of them has vanishing colour and
  hypercharge, the isospin part of the representation sending the colour and hypercharge
  generators to the identity. -/
lemma gaugeWeightDecomposition_supp (hmul : IsMulRep repGauge) :
    (hT.gaugeWeightDecomposition hmul).supp
      = {((0, 0, 0, 0) : GaugeWeight), (0, 0, 4, 0), (0, 0, 2, 0), (0, 0, -2, 0),
        (0, 0, -4, 0)} := by
  rw [hT.gaugeWeightDecomposition_supp_eq hmul]
  decide

/-!

## C.6. The zero-weight piece

An isospin invariant built from `T` is fixed by the isospin part of the representation at
the torus, so it lies in the zero-weight piece, which makes that piece worth describing
explicitly. A product of two weight vectors
has weight zero exactly when the two weights cancel: the root against its negative, in
either order, or the Cartan direction against itself. That is three lines, the
multiplicity of the zero weight in the tensor square of the `su(2)` adjoint.

-/

/-- Two `su(2)` adjoint weight vectors have cancelling weights precisely when they are the
  root and its negative, in either order, or the Cartan direction twice. -/
lemma wtWeight_add_eq_zero_iff (k : WeightIdx × WeightIdx) :
    wtWeight k.1 + wtWeight k.2 = 0
      ↔ k = (Sum.inl 0, Sum.inr (Sum.inl 0)) ∨ k = (Sum.inr (Sum.inl 0), Sum.inl 0)
        ∨ k = (Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)) := by
  revert k
  decide

/-- The line through a product of two weight vectors whose weights cancel lies in the
  zero-weight piece. -/
lemma span_biVec_le_piece_zero (hmul : IsMulRep repGauge) {k₀ k₁ : WeightIdx}
    (h : wtWeight k₀ + wtWeight k₁ = 0) :
    ℂ ∙ hT.biVec (wtCoeff k₀) (wtCoeff k₁)
      ≤ (hT.gaugeWeightDecomposition hmul).piece 0 := by
  rw [hT.gaugeWeightDecomposition_piece hmul]
  exact le_iSup_of_le (k₀, k₁) (le_of_eq (if_pos h.symm).symm)

/-- The raising vector paired with the lowering vector. -/
noncomputable def posNegProd (hT : IsSU2BiAdjoint B repGauge T) : B :=
  hT.biVec (wtCoeff (Sum.inl 0)) (wtCoeff (Sum.inr (Sum.inl 0)))

/-- The lowering vector paired with the raising vector. -/
noncomputable def negPosProd (hT : IsSU2BiAdjoint B repGauge T) : B :=
  hT.biVec (wtCoeff (Sum.inr (Sum.inl 0))) (wtCoeff (Sum.inl 0))

/-- The Cartan direction paired with itself. -/
noncomputable def cartanProd (hT : IsSU2BiAdjoint B repGauge T) : B :=
  hT.biVec (wtCoeff (Sum.inr (Sum.inr 0))) (wtCoeff (Sum.inr (Sum.inr 0)))

/-- The zero-weight piece of the gauge weight decomposition, explicitly: the join of the
  three lines through the products of two weight vectors of opposite weight. -/
lemma gaugeWeightDecomposition_piece_zero (hmul : IsMulRep repGauge) :
    (hT.gaugeWeightDecomposition hmul).piece 0
      = ℂ ∙ hT.posNegProd ⊔ ℂ ∙ hT.negPosProd ⊔ ℂ ∙ hT.cartanProd := by
  refine le_antisymm ?_ (sup_le (sup_le ?_ ?_) ?_)
  · rw [hT.gaugeWeightDecomposition_piece hmul]
    refine iSup_le fun k => ?_
    split_ifs with hk
    · rcases (wtWeight_add_eq_zero_iff k).1 hk.symm with rfl | rfl | rfl
      · exact le_sup_of_le_left (le_sup_of_le_left le_rfl)
      · exact le_sup_of_le_left (le_sup_of_le_right le_rfl)
      · exact le_sup_of_le_right le_rfl
    · exact bot_le
  · exact hT.span_biVec_le_piece_zero hmul (by simp [wtWeight])
  · exact hT.span_biVec_le_piece_zero hmul (by simp [wtWeight])
  · exact hT.span_biVec_le_piece_zero hmul (by simp [wtWeight])

/-- The weight vector of the positive root, in terms of the two Pauli coordinate
  directions of the root pair. -/
lemma wtCoeff_inl :
    wtCoeff (Sum.inl 0) = unitVec rootPair.1 + Complex.I • unitVec rootPair.2 := by
  funext x
  simp [wtCoeff, unitVec]

/-- The weight vector of the negative root, in terms of the two Pauli coordinate
  directions of the root pair. -/
lemma wtCoeff_inr_inl :
    wtCoeff (Sum.inr (Sum.inl 0))
      = unitVec rootPair.1 - Complex.I • unitVec rootPair.2 := by
  funext x
  simp [wtCoeff, unitVec]

/-- The raising-lowering product, written out in the components of `T`. -/
lemma posNegProd_eq :
    hT.posNegProd
      = T ![0, 0] + T ![1, 1] + Complex.I • (T ![1, 0] - T ![0, 1]) := by
  rw [posNegProd, wtCoeff_inl, wtCoeff_inr_inl, hT.biVec_add_left, hT.biVec_smul_left,
    hT.biVec_sub_right, hT.biVec_sub_right, hT.biVec_smul_right, hT.biVec_smul_right,
    hT.biVec_unitVec, hT.biVec_unitVec, hT.biVec_unitVec, hT.biVec_unitVec, smul_sub,
    smul_smul, Complex.I_mul_I, neg_one_smul, smul_sub]
  simp only [rootPair]
  abel

/-- The lowering-raising product, written out in the components of `T`. -/
lemma negPosProd_eq :
    hT.negPosProd
      = T ![0, 0] + T ![1, 1] + Complex.I • (T ![0, 1] - T ![1, 0]) := by
  rw [negPosProd, wtCoeff_inl, wtCoeff_inr_inl, hT.biVec_sub_left, hT.biVec_smul_left,
    hT.biVec_add_right, hT.biVec_add_right, hT.biVec_smul_right, hT.biVec_smul_right,
    hT.biVec_unitVec, hT.biVec_unitVec, hT.biVec_unitVec, hT.biVec_unitVec, smul_add,
    smul_smul, Complex.I_mul_I, neg_one_smul, smul_sub]
  simp only [rootPair]
  abel

/-- The two orders of the root product add to twice the pair of diagonal components of
  the root pair, the imaginary parts cancelling. -/
lemma posNegProd_add_negPosProd :
    hT.posNegProd + hT.negPosProd = (2 : ℂ) • (T ![0, 0] + T ![1, 1]) := by
  rw [hT.posNegProd_eq, hT.negPosProd_eq]
  module

/-- The Cartan product is a single component of `T`: the Cartan direction is already a
  Pauli coordinate direction. -/
lemma cartanProd_eq : hT.cartanProd = T ![2, 2] := by
  rw [cartanProd, ← unitVec_cartanId, hT.biVec_unitVec]

/-- The trace contraction lies in the zero-weight piece. The isospin factor fixes it, so
  in particular the isospin part of the representation fixes it at the torus. -/
lemma traceContraction_mem_piece_zero (hmul : IsMulRep repGauge) :
    hT.traceContraction ∈ (hT.gaugeWeightDecomposition hmul).piece 0 :=
  GaugeWeightDecomposition.mem_zero_of_invariant _ hT.traceContraction_mem_span
    ((repSU2_invariant_iff_su2 repGauge _).2 hT.repGauge_traceContraction)

/-!

## D. The isospin invariants in the span

The gauge weight decomposition sees only the torus, and the zero-weight piece it leaves is
three lines wide. Two further elements of `SU(2)` cut that down to one. The Weyl element
is the half turn about the Cartan axis; it exchanges the two orders of the root product
and so leaves two lines. A third of a turn about the diagonal axis of the three Pauli
directions is not in the normaliser of the torus at all, and it cuts the remaining two
lines to the single line through the trace contraction. Everything used is an isospin
transformation, so what is classified is the invariants of the isospin factor; the
statements about gauge invariance are the corollaries got by restricting a gauge invariant
to those transformations, and where they read the other way they carry the invariance of
the trace contraction as a hypothesis. D.3 states the classification under the hypotheses
the decomposition machinery needs, an algebra structure on `B` and a multiplicative
representation. D.4 removes both by reading the classification in the trivial square-zero
extension of a module, and D.5 pushes it down a quotient by a stable submodule,
classifying the invariants of the span joined with that submodule.

## D.1. The Weyl reflection on the zero-weight products

The `SU(2)` Weyl element `su2Perm` acts on the Pauli directions as the half turn about the
Cartan axis, negating the two members of the root pair and the Cartan direction itself.
On the weight vectors it therefore exchanges the root with its negative, up to a sign that
cancels between the two indices of a product. So it exchanges the two orders of the root
product and fixes the Cartan product, and an isospin invariant in the zero-weight piece is
a combination of the sum of the two orders and the Cartan product alone.

-/

/-- The row action on a Pauli coordinate direction is a column of the adjoint matrix. -/
lemma rowAct_unitVec (U : specialUnitaryGroup (Fin 2) ℂ) (b a : Fin 3) :
    rowAct U (unitVec b) a = ((su2AdjointMatrix U a b : ℝ) : ℂ) := by
  simp only [rowAct, unitVec, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

/-- The conjugate transpose of the `SU(2)` Weyl element. -/
lemma star_su2Perm_coe :
    star (su2Perm : specialUnitaryGroup (Fin 2) ℂ).1 = !![0, 1; -1, 0] := by
  rw [su2Perm_coe]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

/-- The adjoint matrix of the `SU(2)` Weyl element: the half turn about the Cartan axis,
  which fixes the second member of the root pair and negates the other two Pauli
  directions. -/
lemma su2AdjointMatrix_su2Perm :
    su2AdjointMatrix su2Perm = !![-1, 0, 0; 0, 1, 0; 0, 0, -1] := by
  ext a b
  rw [su2AdjointMatrix_apply, star_su2Perm_coe, su2Perm_coe]
  fin_cases a <;> fin_cases b <;>
    simp only [pauliMatrix, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.of_apply] <;>
    norm_num

/-- The exchange of the root with its negative on the weight indices, the Cartan
  direction being fixed. -/
def weylSwap : WeightIdx → WeightIdx
  | Sum.inl _ => Sum.inr (Sum.inl 0)
  | Sum.inr (Sum.inl _) => Sum.inl 0
  | Sum.inr (Sum.inr _) => Sum.inr (Sum.inr 0)

/-- The Weyl element negates every weight vector of the `su(2)` adjoint, after exchanging
  the root with its negative. -/
lemma rowAct_su2Perm_wtCoeff (k : WeightIdx) :
    rowAct su2Perm (wtCoeff k) = -wtCoeff (weylSwap k) := by
  funext a
  have hrow : rowAct su2Perm (wtCoeff k) a
      = ∑ x : Fin 3, ((su2AdjointMatrix su2Perm a x : ℝ) : ℂ) * wtCoeff k x := rfl
  rw [hrow, Fin.sum_univ_three, su2AdjointMatrix_su2Perm]
  match k with
  | Sum.inl _ => fin_cases a <;> simp [wtCoeff, weylSwap, rootPair]
  | Sum.inr (Sum.inl _) => fin_cases a <;> simp [wtCoeff, weylSwap, rootPair]
  | Sum.inr (Sum.inr _) => fin_cases a <;>
      simp [wtCoeff, weylSwap, GaugeAlgebra.su2CartanId]

/-- The Weyl element carries a product of two weight vectors to the product of the
  exchanged pair: the sign it puts on each of the two vectors cancels against the
  other. -/
lemma map_su2Perm_biVec_wtCoeff (hT : IsSU2BiAdjoint B repGauge T) {f : B →ₗ[ℂ] B}
    (hf : IsSU2BiAdjointMat su2Perm f T) (k₀ k₁ : WeightIdx) :
    f (hT.biVec (wtCoeff k₀) (wtCoeff k₁))
      = hT.biVec (wtCoeff (weylSwap k₀)) (wtCoeff (weylSwap k₁)) := by
  rw [hT.map_biVec hf, rowAct_su2Perm_wtCoeff, rowAct_su2Perm_wtCoeff, hT.biVec_neg_neg]

/-- The Weyl element exchanges the two orders of the root product. -/
lemma repGauge_su2Perm_posNegProd :
    repGauge (1, su2Perm, 1) hT.posNegProd = hT.negPosProd :=
  hT.map_su2Perm_biVec_wtCoeff (hT.repGauge_T su2Perm) (Sum.inl 0)
    (Sum.inr (Sum.inl 0))

/-- The Weyl element exchanges the two orders of the root product, the other way. -/
lemma repGauge_su2Perm_negPosProd :
    repGauge (1, su2Perm, 1) hT.negPosProd = hT.posNegProd :=
  hT.map_su2Perm_biVec_wtCoeff (hT.repGauge_T su2Perm) (Sum.inr (Sum.inl 0))
    (Sum.inl 0)

/-- The Weyl element fixes the Cartan product, negating the Cartan direction twice. -/
lemma repGauge_su2Perm_cartanProd :
    repGauge (1, su2Perm, 1) hT.cartanProd = hT.cartanProd :=
  hT.map_su2Perm_biVec_wtCoeff (hT.repGauge_T su2Perm) (Sum.inr (Sum.inr 0))
    (Sum.inr (Sum.inr 0))

/-- An isospin invariant in the zero-weight piece is a combination of the pair of
  diagonal components of the root pair and the diagonal Cartan component. The Weyl element
  exchanges the two orders of the root product, so only their sum survives, and that sum
  is twice the pair of diagonal components. -/
lemma exists_eq_of_mem_piece_zero (hmul : IsMulRep repGauge) {x : B}
    (hx : x ∈ (hT.gaugeWeightDecomposition hmul).piece 0)
    (hinv : ∀ U : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, U, 1) x = x) :
    ∃ f e : ℂ, x = f • (T ![0, 0] + T ![1, 1]) + e • T ![2, 2] := by
  rw [hT.gaugeWeightDecomposition_piece_zero hmul] at hx
  obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hu
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hw
  obtain ⟨e, rfl⟩ := Submodule.mem_span_singleton.1 hz
  have hkey := hinv su2Perm
  rw [map_add, map_add, map_smul, map_smul, map_smul,
    hT.repGauge_su2Perm_posNegProd, hT.repGauge_su2Perm_negPosProd,
    hT.repGauge_su2Perm_cartanProd] at hkey
  refine ⟨a + b, e, ?_⟩
  linear_combination (norm := module) (-1 / 2 : ℂ) • hkey
    + ((a + b) / 2 : ℂ) • hT.posNegProd_add_negPosProd + e • hT.cartanProd_eq

/-!

## D.2. A third of a turn about the diagonal axis

The gauge weight and the Weyl reflection are both read off the normaliser of the gauge
torus, and between them they leave two lines: the pair of diagonal components of the root
pair and the diagonal Cartan component. Nothing in the normaliser separates those, because
the normaliser preserves the Cartan axis, and the two lines differ precisely in how much
of each lies along it.

The element `su2Cyc` leaves the normaliser behind. Its adjoint action is a third of a turn
about the diagonal axis of the three Pauli directions, which cycles them, carrying the
Cartan direction to a root direction. Applied to an invariant it ties the three diagonal
components of `T` to each other, and that cuts the two lines down to the one through the
trace contraction.

-/

/-- The `SU(2)` element `(1 + i(σ₁ + σ₂ + σ₃))/2`. A third of a turn about the diagonal
  axis of the three Pauli directions, it lies outside the normaliser of the gauge torus:
  it carries the Cartan direction to a root direction, which no element of the normaliser
  does. -/
noncomputable def su2Cyc : specialUnitaryGroup (Fin 2) ℂ :=
  ⟨!![(1 + Complex.I) / 2, (1 + Complex.I) / 2;
      (-1 + Complex.I) / 2, (1 - Complex.I) / 2], by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff]
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, star_eq_conjTranspose,
          Matrix.conjTranspose_apply, map_div₀, Complex.conj_I, map_ofNat] <;>
        ring_nf <;>
        simp [Complex.I_sq] <;>
        ring
    · simp [Matrix.det_fin_two, Complex.ext_iff]
      norm_num⟩

/-- The underlying matrix of the third of a turn. -/
lemma su2Cyc_coe :
    (su2Cyc : specialUnitaryGroup (Fin 2) ℂ).1
      = !![(1 + Complex.I) / 2, (1 + Complex.I) / 2;
          (-1 + Complex.I) / 2, (1 - Complex.I) / 2] := rfl

/-- The conjugate transpose of the third of a turn. -/
lemma star_su2Cyc_coe :
    star (su2Cyc : specialUnitaryGroup (Fin 2) ℂ).1
      = !![(1 - Complex.I) / 2, (-1 - Complex.I) / 2;
          (1 - Complex.I) / 2, (1 + Complex.I) / 2] := by
  rw [su2Cyc_coe]
  ext a b
  fin_cases a <;> fin_cases b <;> simp <;> ring

/-- The adjoint matrix of the third of a turn: the cyclic permutation of the three Pauli
  directions. -/
lemma su2AdjointMatrix_su2Cyc :
    su2AdjointMatrix su2Cyc = !![0, 1, 0; 0, 0, 1; 1, 0, 0] := by
  ext a b
  rw [su2AdjointMatrix_apply, star_su2Cyc_coe, su2Cyc_coe]
  fin_cases a <;> fin_cases b <;>
    simp only [pauliMatrix, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.of_apply] <;>
    norm_num [Complex.ext_iff]

/-- The third of a turn as a gauge transformation: trivial on colour and hypercharge. -/
noncomputable def gaugeSU2Cyc : GaugeGroupI := ⟨1, su2Cyc, 1⟩

/-- The isospin factor of the third of a turn read as a gauge transformation is the third
  of a turn itself. -/
lemma toSU2_gaugeSU2Cyc : GaugeGroupI.toSU2 gaugeSU2Cyc = su2Cyc := rfl

/-- The cycle of Pauli indices induced by the third of a turn. -/
def cycIdx : Fin 3 → Fin 3
  | 0 => 2
  | 1 => 0
  | 2 => 1

/-- The third of a turn carries each Pauli coordinate direction to the next one in the
  cycle. -/
lemma rowAct_su2Cyc_unitVec (b : Fin 3) :
    rowAct su2Cyc (unitVec b) = unitVec (cycIdx b) := by
  funext a
  rw [rowAct_unitVec, su2AdjointMatrix_su2Cyc]
  fin_cases b <;> fin_cases a <;> simp [cycIdx, unitVec]

/-- A map moving the components by the third of a turn cycles the diagonal components of
  `T`. -/
lemma map_su2Cyc_diag (hT : IsSU2BiAdjoint B repGauge T) {f : B →ₗ[ℂ] B}
    (hf : IsSU2BiAdjointMat su2Cyc f T) (b : Fin 3) :
    f (T ![b, b]) = T ![cycIdx b, cycIdx b] := by
  rw [← hT.biVec_unitVec b b, hT.map_biVec hf, rowAct_su2Cyc_unitVec,
    hT.biVec_unitVec]

/-- The third of a turn cycles the diagonal components of `T`. -/
lemma repGauge_su2Cyc_diag (hT : IsSU2BiAdjoint B repGauge T) (b : Fin 3) :
    repGauge (1, su2Cyc, 1) (T ![b, b]) = T ![cycIdx b, cycIdx b] :=
  hT.map_su2Cyc_diag (hT.repGauge_T su2Cyc) b

/-!

## D.3. The classification

An isospin invariant in the span is fixed by the isospin part of the representation at the
torus, so it lies in the zero-weight piece, and the Weyl element then writes it as a
combination of the pair of diagonal components of the root pair and the diagonal Cartan
component. The third of a turn forces the three diagonal components to enter that
combination on the same footing, which leaves the single line through the trace
contraction: the one singlet of `3 ⊗ 3`.

`mem_span_and_su2_invariant_iff` is the classification proper. Its gauge counterpart
`mem_span_and_invariant_iff` needs the trace contraction to be gauge invariant, and takes
that as a hypothesis: the transformation law leaves the colour and hypercharge factors
free, so they may scale the trace contraction, and then the multiples of it are not gauge
invariants at all. The same hypothesis is what `su2_invariant_iff_invariant` needs to
upgrade isospin invariance in the span to gauge invariance; without it that statement is
false.

-/

/-- Every isospin invariant in the span of the components is a multiple of the trace
  contraction. The gauge weight and the Weyl element cut the span down to the two lines
  through the pair of root diagonal components and the Cartan one, and the third of a turn
  cuts those two down to one. Only the isospin factor is used, which is all the
  transformation law constrains. -/
lemma exists_smul_traceContraction_of_su2_invariant (hT : IsSU2BiAdjoint B repGauge T)
    (hmul : IsMulRep repGauge) {x : B} (hx : x ∈ hT.span)
    (hinv : ∀ U : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, U, 1) x = x) :
    ∃ c : ℂ, x = c • hT.traceContraction := by
  obtain ⟨f, e, rfl⟩ := hT.exists_eq_of_mem_piece_zero hmul
    (GaugeWeightDecomposition.mem_zero_of_invariant _ hx
      ((repSU2_invariant_iff_su2 repGauge x).2 hinv)) hinv
  have hc0 : repGauge (1, su2Cyc, 1) (T ![0, 0]) = T ![2, 2] :=
    hT.repGauge_su2Cyc_diag 0
  have hc1 : repGauge (1, su2Cyc, 1) (T ![1, 1]) = T ![0, 0] :=
    hT.repGauge_su2Cyc_diag 1
  have hc2 : repGauge (1, su2Cyc, 1) (T ![2, 2]) = T ![1, 1] :=
    hT.repGauge_su2Cyc_diag 2
  have hcyc := hinv su2Cyc
  rw [map_add, map_smul, map_smul, map_add, hc0, hc1, hc2] at hcyc
  have h1 : (f - e) • (T ![2, 2] - T ![1, 1]) = 0 := by
    linear_combination (norm := module) hcyc
  have h2 : (f - e) • (T ![1, 1] - T ![0, 0]) = 0 := by
    have h := congrArg (repGauge (1, su2Cyc, 1)) h1
    rwa [map_smul, map_sub, hc2, hc1, map_zero] at h
  refine ⟨(2 * f + e) / 3, ?_⟩
  rw [traceContraction, Fin.sum_univ_three]
  linear_combination (norm := module) (-2 / 3 : ℂ) • h1 + (-1 / 3 : ℂ) • h2

/-- Every gauge invariant in the span of the components is a multiple of the trace
  contraction. A gauge invariant is in particular fixed by the transformations trivial on
  colour and hypercharge, and those alone already force the conclusion. -/
lemma exists_smul_traceContraction_of_invariant (hT : IsSU2BiAdjoint B repGauge T)
    (hmul : IsMulRep repGauge) {x : B} (hx : x ∈ hT.span)
    (hinv : ∀ g : GaugeGroupI, repGauge g x = x) :
    ∃ c : ℂ, x = c • hT.traceContraction :=
  hT.exists_smul_traceContraction_of_su2_invariant hmul hx fun U => hinv (1, U, 1)

/-- The isospin invariants in the span of the components are exactly the multiples of the
  trace contraction. The gauge weight, the Weyl element and the third of a turn bound them
  from above, and the trace contraction is itself isospin invariant and in the span, which
  bounds them from below. This is the one singlet of `3 ⊗ 3`. -/
lemma mem_span_and_su2_invariant_iff (hT : IsSU2BiAdjoint B repGauge T)
    (hmul : IsMulRep repGauge) (x : B) :
    (x ∈ hT.span ∧ ∀ U : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, U, 1) x = x)
      ↔ x ∈ ℂ ∙ hT.traceContraction := by
  refine ⟨fun h => ?_, fun hx => ?_⟩
  · obtain ⟨c, rfl⟩ := hT.exists_smul_traceContraction_of_su2_invariant hmul h.1 h.2
    exact Submodule.mem_span_singleton.2 ⟨c, rfl⟩
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    exact ⟨Submodule.smul_mem _ _ hT.traceContraction_mem_span,
      fun U => by rw [map_smul, hT.repGauge_traceContraction]⟩

/-- The gauge invariants in the span of the components are exactly the multiples of the
  trace contraction, once the trace contraction is known to be gauge invariant. That
  hypothesis cannot be dropped: the transformation law says nothing about the colour and
  hypercharge factors, so they may well move the trace contraction, and then the
  right-hand side has invariants that the left-hand side has not. Where the two factors do
  fix it, as they do for the `W`-boson field strengths, the hypothesis is supplied from
  the transformation law of the underlying field. -/
lemma mem_span_and_invariant_iff (hT : IsSU2BiAdjoint B repGauge T)
    (hmul : IsMulRep repGauge) (x : B)
    (htc : ∀ g : GaugeGroupI, repGauge g hT.traceContraction = hT.traceContraction) :
    (x ∈ hT.span ∧ ∀ g : GaugeGroupI, repGauge g x = x)
      ↔ x ∈ ℂ ∙ hT.traceContraction := by
  refine ⟨fun h => ?_, fun hx => ?_⟩
  · obtain ⟨c, rfl⟩ := hT.exists_smul_traceContraction_of_invariant hmul h.1 h.2
    exact Submodule.mem_span_singleton.2 ⟨c, rfl⟩
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    exact ⟨Submodule.smul_mem _ _ hT.traceContraction_mem_span,
      fun g => by rw [map_smul, htc]⟩

/-- Inside the span of the components the two notions of invariance agree, provided the
  trace contraction is gauge invariant: a vector fixed by the isospin factor is then fixed
  by the whole gauge group. One direction is free, an isospin transformation being a gauge
  transformation; the other is the classification, the isospin invariants being multiples
  of the trace contraction. The hypothesis `htc` is exactly what the transformation law no
  longer supplies, and without it the statement is false, the colour and hypercharge
  factors being unconstrained. -/
lemma su2_invariant_iff_invariant (hT : IsSU2BiAdjoint B repGauge T)
    (hmul : IsMulRep repGauge)
    (htc : ∀ g : GaugeGroupI, repGauge g hT.traceContraction = hT.traceContraction)
    {x : B} (hx : x ∈ hT.span) :
    (∀ U : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, U, 1) x = x)
      ↔ ∀ g : GaugeGroupI, repGauge g x = x := by
  refine ⟨fun h g => ?_, fun h U => h (1, U, 1)⟩
  obtain ⟨c, rfl⟩ := hT.exists_smul_traceContraction_of_su2_invariant hmul hx h
  rw [map_smul, htc]

/-!

## D.4. The trivial square-zero extension of a module

Section D.3 asks for a ring: `IsMulRep` is a statement about multiplication, and the
decomposition machinery of section C is set up in an algebra. The conclusion asks for none
of that, and the gap can be closed once and for all. The trivial square-zero extension
`TrivSqZeroExt ℂ M` of a module `M` is a commutative `ℂ`-algebra built from the module
structure alone, a representation on `M` extends to it by acting trivially on the scalar
part, and that extension acts by algebra maps for free. So D.3 holds in the extension, and
the injection of `M` carries the conclusion back:
`exists_smul_traceContraction_of_su2_invariant_module` and its gauge corollary
`exists_smul_traceContraction_of_invariant_module` are D.3 with the algebra structure and
the multiplicativity hypothesis both removed.

-/

section SquareZero

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
  {ρ : Representation ℂ GaugeGroupI M} {U : (Fin 2 → Fin 3) → M}

/-- The opposite scalar action on a complex vector space, which the square-zero extension
  needs to be a ring. Since `ℂ` is commutative it is the given action read through `unop`,
  and it is given a low priority so that the action of `ℂ` on itself is unaffected. -/
noncomputable local instance (priority := 100) opModule : Module ℂᵐᵒᵖ M :=
  Module.compHom M ((RingHom.id ℂ).fromOpposite fun x y => mul_comm x y)

/-- The two scalar actions of `ℂ` on a complex vector space commute. -/
local instance (priority := 100) smulCommClassOpModule : SMulCommClass ℂ ℂᵐᵒᵖ M :=
  ⟨fun a b m => smul_comm a b.unop m⟩

/-- The opposite scalar action agrees with the given one, `ℂ` being commutative. -/
local instance (priority := 100) isCentralScalarOpModule : IsCentralScalar ℂ M :=
  ⟨fun _ _ => rfl⟩

/-- The linear map of the square-zero extension induced by a linear map of the module: the
  identity on the scalar part and the given map on the module part. -/
def sqZeroMap (f : M →ₗ[ℂ] M) : TrivSqZeroExt ℂ M →ₗ[ℂ] TrivSqZeroExt ℂ M where
  toFun u := TrivSqZeroExt.inl u.fst + TrivSqZeroExt.inr (f u.snd)
  map_add' u v := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_smul' c u := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp

/-- The induced map leaves the scalar part alone. -/
@[simp]
lemma fst_sqZeroMap (f : M →ₗ[ℂ] M) (u : TrivSqZeroExt ℂ M) :
    (sqZeroMap f u).fst = u.fst := by
  simp [sqZeroMap]

/-- The induced map acts by the given map on the module part. -/
@[simp]
lemma snd_sqZeroMap (f : M →ₗ[ℂ] M) (u : TrivSqZeroExt ℂ M) :
    (sqZeroMap f u).snd = f u.snd := by
  simp [sqZeroMap]

/-- The representation carried by the square-zero extension: trivial on the scalar part
  and the given representation on the module part. -/
def sqZeroRep (ρ : Representation ℂ GaugeGroupI M) :
    Representation ℂ GaugeGroupI (TrivSqZeroExt ℂ M) where
  toFun g := sqZeroMap (ρ g)
  map_one' := by
    refine LinearMap.ext fun u => TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_mul' g₁ g₂ := by
    refine LinearMap.ext fun u => TrivSqZeroExt.ext ?_ ?_ <;> simp [Module.End.mul_apply]

/-- The extended representation on the image of the module is the given one. -/
@[simp]
lemma sqZeroRep_inr (ρ : Representation ℂ GaugeGroupI M) (g : GaugeGroupI) (m : M) :
    sqZeroRep ρ g (TrivSqZeroExt.inr m) = TrivSqZeroExt.inr (ρ g m) := by
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp [sqZeroRep]

/-- The extended representation acts by algebra maps, whatever the representation it
  extends: the product of the extension is built from the module structure, which the
  representation is linear for. -/
lemma isMulRep_sqZeroRep (ρ : Representation ℂ GaugeGroupI M) : IsMulRep (sqZeroRep ρ) := by
  intro g u v
  refine TrivSqZeroExt.ext ?_ ?_
  · simp [sqZeroRep]
  · simp [sqZeroRep, TrivSqZeroExt.snd_mul, op_smul_eq_smul]

/-- The images of the components in the square-zero extension again form a bi-adjoint
  family. -/
lemma isSU2BiAdjoint_sqZeroRep (hU : IsSU2BiAdjoint M ρ U) :
    IsSU2BiAdjoint (TrivSqZeroExt ℂ M) (sqZeroRep ρ) fun l => TrivSqZeroExt.inr (U l) where
  repGauge_T g l := by
    rw [sqZeroRep_inr, hU.repGauge_T g l]
    simp only [TrivSqZeroExt.inr_sum, TrivSqZeroExt.inr_smul]

/-- The trace contraction of the images is the image of the trace contraction. -/
lemma traceContraction_sqZeroRep (hU : IsSU2BiAdjoint M ρ U) :
    hU.isSU2BiAdjoint_sqZeroRep.traceContraction = TrivSqZeroExt.inr hU.traceContraction := by
  simp only [traceContraction, TrivSqZeroExt.inr_sum]

/-- The image of an element of the span lies in the span of the images. -/
lemma inr_mem_span_sqZeroRep (hU : IsSU2BiAdjoint M ρ U) {x : M} (hx : x ∈ hU.span) :
    TrivSqZeroExt.inr x ∈ hU.isSU2BiAdjoint_sqZeroRep.span := by
  obtain ⟨c, rfl⟩ := (hU.mem_span_iff x).1 hx
  refine (hU.isSU2BiAdjoint_sqZeroRep.mem_span_iff _).2 ⟨c, ?_⟩
  simp only [TrivSqZeroExt.inr_sum, TrivSqZeroExt.inr_smul]

/-- Every gauge invariant in the span of the components is a multiple of the trace
  contraction, for a family valued in a mere module. Neither an algebra structure on the
  target nor multiplicativity of the representation is needed: the square-zero extension
  supplies both, and the injection of the module reflects the conclusion back. -/
lemma exists_smul_traceContraction_of_invariant_module (hU : IsSU2BiAdjoint M ρ U) {x : M}
    (hx : x ∈ hU.span) (hinv : ∀ g : GaugeGroupI, ρ g x = x) :
    ∃ c : ℂ, x = c • hU.traceContraction := by
  obtain ⟨c, hc⟩ := hU.isSU2BiAdjoint_sqZeroRep.exists_smul_traceContraction_of_invariant
    (isMulRep_sqZeroRep ρ) (hU.inr_mem_span_sqZeroRep hx)
    (fun g => by rw [sqZeroRep_inr, hinv g])
  refine ⟨c, TrivSqZeroExt.inr_injective (R := ℂ) ?_⟩
  rw [hc, hU.traceContraction_sqZeroRep, TrivSqZeroExt.inr_smul]

/-- The same classification for a family valued in a mere module, read at the isospin
  factor alone. -/
lemma exists_smul_traceContraction_of_su2_invariant_module (hU : IsSU2BiAdjoint M ρ U)
    {x : M} (hx : x ∈ hU.span)
    (hinv : ∀ V : specialUnitaryGroup (Fin 2) ℂ, ρ (1, V, 1) x = x) :
    ∃ c : ℂ, x = c • hU.traceContraction :=
  hU.toRepSU2.exists_smul_traceContraction_of_invariant_module hx
    ((repSU2_invariant_iff_su2 ρ x).2 hinv)

end SquareZero

/-!

## D.5. The invariants modulo a stable submodule

A stable submodule can be divided out: the quotient representation carries the images of
the components as a bi-adjoint family again, so D.4 applies verbatim in the quotient and
lifts to a classification modulo the submodule. Stability of the submodule is what makes
the quotient representation exist, and it cannot be dropped: for an unstable line `ℂ ∙ v`
the only invariant of the line is `0`, while an invariant of the sum may well lie outside
the span. The error term is invariant for free, since it is the difference of two
invariants.

`mem_span_sup_su2_invariant_iff` is the isospin form, stable and invariant meaning under
`repGauge (1, U, 1)` throughout, and it is the form the transformation law supports.
`mem_span_sup_invariant_iff`, the gauge form, asks in addition that the trace contraction
be gauge invariant, for the reason given in D.3: that is what makes the error term a gauge
invariant rather than merely an isospin invariant.

-/

section Quotient

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
  {ρ : Representation ℂ GaugeGroupI M} {U : (Fin 2 → Fin 3) → M}

/-- The representation induced on the quotient by a gauge-stable submodule. -/
noncomputable def quotRep (ρ : Representation ℂ GaugeGroupI M) (S : Submodule ℂ M)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, ρ g y ∈ S) :
    Representation ℂ GaugeGroupI (M ⧸ S) where
  toFun g := S.mapQ S (ρ g) fun y hy => hS g y hy
  map_one' := by
    ext y
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.mapQ_apply, map_one, Module.End.one_apply]
  map_mul' g₁ g₂ := by
    ext y
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.mapQ_apply, map_mul, Module.End.mul_apply]

/-- The quotient representation on a class is the class of the representation. -/
@[simp]
lemma quotRep_mkQ (S : Submodule ℂ M) (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, ρ g y ∈ S)
    (g : GaugeGroupI) (y : M) : quotRep ρ S hS g (S.mkQ y) = S.mkQ (ρ g y) := rfl

/-- The images of the components in the quotient by a gauge-stable submodule again form a
  bi-adjoint family. -/
lemma isSU2BiAdjoint_quotRep (hU : IsSU2BiAdjoint M ρ U) (S : Submodule ℂ M)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, ρ g y ∈ S) :
    IsSU2BiAdjoint (M ⧸ S) (quotRep ρ S hS) fun l => S.mkQ (U l) where
  repGauge_T g l := by
    rw [quotRep_mkQ, hU.repGauge_T g l, map_sum]
    exact Finset.sum_congr rfl fun a _ => map_smul _ _ _

/-- The quotient map carries the trace contraction to the trace contraction of the
  images. -/
lemma mkQ_traceContraction (hU : IsSU2BiAdjoint M ρ U) (S : Submodule ℂ M)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, ρ g y ∈ S) :
    S.mkQ hU.traceContraction = (hU.isSU2BiAdjoint_quotRep S hS).traceContraction := by
  simp only [traceContraction, map_sum]

end Quotient

/-- The gauge invariants of the span of the components together with a gauge-stable
  submodule `S`: such an element is a multiple of the trace contraction up to an error in
  `S`, and the error is gauge invariant as well, being the difference of two invariants.
  Stability of `S` is needed, and not just convenient: for an unstable line the only
  invariant of the line is zero, while the sum can carry invariants outside the span. The
  gauge invariance `htc` of the trace contraction is a hypothesis for the same reason as
  in `mem_span_and_invariant_iff`: the transformation law constrains the isospin factor
  only, so it is what makes the error term gauge invariant rather than merely isospin
  invariant. The classification is applied in the quotient by `S`, where the images of the
  components form a bi-adjoint family again. -/
lemma mem_span_sup_invariant_iff (hT : IsSU2BiAdjoint B repGauge T) (hmul : IsMulRep repGauge)
    (x : B) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (htc : ∀ g : GaugeGroupI, repGauge g hT.traceContraction = hT.traceContraction)
    (hx : x ∈ hT.span ⊔ S)
    (hinv : ∀ g : GaugeGroupI, repGauge g x = x) :
    ∃ c : ℂ, ∃ y ∈ S, x = c • hT.traceContraction + y
      ∧ ∀ g : GaugeGroupI, repGauge g y = y := by
  have hmk : S.mkQ x ∈ (hT.isSU2BiAdjoint_quotRep S hS).span := by
    obtain ⟨u, hu, z, hz, huz⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, hc⟩ := (hT.mem_span_iff u).1 hu
    refine ((hT.isSU2BiAdjoint_quotRep S hS).mem_span_iff _).2 ⟨c, ?_⟩
    rw [← huz, map_add, show S.mkQ z = 0 from (Submodule.Quotient.mk_eq_zero S).2 hz,
      add_zero, hc, map_sum]
    exact Finset.sum_congr rfl fun d _ => map_smul _ _ _
  have hinv' : ∀ g : GaugeGroupI, quotRep repGauge S hS g (S.mkQ x) = S.mkQ x :=
    fun g => by rw [quotRep_mkQ, hinv g]
  obtain ⟨c, hc⟩ :=
    (hT.isSU2BiAdjoint_quotRep S hS).exists_smul_traceContraction_of_invariant_module hmk hinv'
  rw [← hT.mkQ_traceContraction S hS] at hc
  refine ⟨c, x - c • hT.traceContraction, ?_, by abel, fun g => ?_⟩
  · have hker : x - c • hT.traceContraction ∈ LinearMap.ker S.mkQ := by
      rw [LinearMap.mem_ker, map_sub, map_smul, hc, sub_self]
    rwa [Submodule.ker_mkQ] at hker
  · rw [map_sub, map_smul, hinv g, htc g]

/-- The same statement modulo an isospin-stable submodule, read at the isospin factor
  alone: a vector of the span joined with `S` that the isospin factor fixes is a multiple
  of the trace contraction up to an error in `S`, and the error is fixed by the isospin
  factor too. -/
lemma mem_span_sup_su2_invariant_iff (hT : IsSU2BiAdjoint B repGauge T)
    (hmul : IsMulRep repGauge) (x : B) (S : Submodule ℂ B)
    (hS : ∀ U : specialUnitaryGroup (Fin 2) ℂ, ∀ y ∈ S, repGauge (1, U, 1) y ∈ S)
    (hx : x ∈ hT.span ⊔ S)
    (hinv : ∀ U : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, U, 1) x = x) :
    ∃ c : ℂ, ∃ y ∈ S, x = c • hT.traceContraction + y
      ∧ ∀ U : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, U, 1) y = y := by
  obtain ⟨c, y, hyS, hxy, hyinv⟩ :=
    hT.toRepSU2.mem_span_sup_invariant_iff (isMulRep_repSU2 hmul) x S
      ((repSU2_stable_iff_su2 repGauge S).2 hS)
      ((repSU2_invariant_iff_su2 repGauge _).2 hT.repGauge_traceContraction) hx
      ((repSU2_invariant_iff_su2 repGauge x).2 hinv)
  exact ⟨c, y, hyS, hxy, (repSU2_invariant_iff_su2 repGauge y).1 hyinv⟩

end Decomposition

end IsSU2BiAdjoint

end StandardModel
