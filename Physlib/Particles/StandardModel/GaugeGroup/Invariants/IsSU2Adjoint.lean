/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.IsSU2BiAdjoint
/-!
# Gauge tensors carrying one `su(2)` adjoint index

`IsSU2Adjoint B repGauge T` says that a family `T`, indexed by a single `su(2)` adjoint
index and valued in a module `B` carrying a representation of the gauge group
`GaugeGroupI`, transforms as a tensor `T^a` in the `su(2)` factor of the adjoint
representation.

This is the one index companion of `IsSU2BiAdjoint`. The field strength of the `W` bosons
carries one `su(2)` adjoint index, so a single field strength, or any expression built
linearly from one, transforms in this way, and the proposition here records that law.

The law itself is `IsSU2AdjointMat`, which relates one element of `SU(2)` to one linear
map on `B` and mentions no other factor of the gauge group, through `su2AdjointMatrix`,
the adjoint matrix of an `SU(2)` element alone. `IsSU2Adjoint` says that the isospin
transformation `(1, U, 1)` obeys that law with the matrix of `U`, for every `U` in
`SU(2)`, and it says nothing whatever about the colour and hypercharge factors: those may
move the components as they please.

The point of the file is that a single adjoint index carries no invariant at all. The
adjoint representation of `SU(2)` is the vector representation of the rotation group and
contains no singlet, so `eq_zero_of_su2_invariant`: an element of the span of the
components fixed by the isospin factor is zero. The proof is a single finite average. The
three isospin flips `su2Flip`, the elements `i σ₁`, `i σ₂` and `i σ₃`, are the half turns
about the three isospin axes, and they and the identity form the Klein four-group of the
rotation group. A half turn about an axis fixes that axis and reverses the other two, so
the four adjoint matrices sum to zero, and averaging an invariant over the four gives
four times the invariant on one side and zero on the other.

That average is the torus step and the Weyl step of the `su(3)` story rolled into one.
`su2Flip 2` fixes the Cartan direction and reverses the two root directions, which is what
a torus average would give; `su2Flip 0` and `su2Flip 1` reverse the Cartan direction, which
is the Weyl reflection, `su2Flip 1` being the Weyl element `su2Perm` up to a sign. That is
recorded in `su2AdjointMatrix_su2Flip_one`, which reads the sign off the existing
`su2AdjointMatrix_su2Perm`. Nothing beyond a module structure on `B` is used anywhere: no
algebra structure, no multiplicativity hypothesis and no gauge weight decomposition.

Section A gives the transformation law, the proposition and the span of the components,
and section B the contraction of the single index against a coordinate vector, through
which the law reads as the row action `IsSU2BiAdjoint.rowAct` on coordinate vectors.
Section C introduces the three flips and computes the average, and section D draws the
conclusion, in D.1 for the span itself and in D.2 for the span joined with a stable
submodule, which is the form `mem_span_sup_su2_invariant_iff` a peeling argument needs.
-/

@[expose] public section

namespace StandardModel

open Matrix PauliMatrix IsSU2BiAdjoint

/-!

## A. The transformation law and the span of the components

An `su(2)` adjoint index is acted on by the `SU(2)` factor of the gauge group alone,
through `su2AdjointMatrix`, the matrix of `IsSU2BiAdjoint` section A.1. The law carries
one factor of that matrix, with the summed index in the row slot, exactly as each of the
two indices of a bi-adjoint family does.

-/

/-- The linear map `f` moves the components of the family `T` as the `SU(2)` matrix `U`
  moves a tensor with one adjoint index: one factor of `su2AdjointMatrix U`, with the
  summed index in the row slot. -/
def IsSU2AdjointMat {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (U : specialUnitaryGroup (Fin 2) ℂ) (f : B →ₗ[ℂ] B) (T : Fin 3 → B) : Prop :=
  ∀ l : Fin 3, f (T l) = ∑ a : Fin 3, ((su2AdjointMatrix U a l : ℝ) : ℂ) • T a

/-- A family `T` of elements of `B`, indexed by one `su(2)` adjoint index, transforms as a
  tensor `T^a` under the representation `repGauge` of the gauge group: an isospin
  transformation moves the components by the `SU(2)` element it is built from. Nothing is
  asked of the colour or hypercharge factors. -/
structure IsSU2Adjoint (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B) (T : Fin 3 → B) : Prop where
  repGauge_T : ∀ g : specialUnitaryGroup (Fin 2) ℂ,
    IsSU2AdjointMat g (repGauge (1, g, 1)) T

namespace IsSU2Adjoint

set_option linter.unusedVariables false

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {T : Fin 3 → B}
  (hT : IsSU2Adjoint B repGauge T)

/-- An adjoint family for a representation is an adjoint family for its isospin part: the
  transformation law reads only the isospin factor to begin with. -/
lemma toRepSU2 (hT : IsSU2Adjoint B repGauge T) :
    IsSU2Adjoint B (repSU2 repGauge) T where
  repGauge_T g := hT.repGauge_T g

/-- The span of all the components. -/
def span (hT : IsSU2Adjoint B repGauge T) : Submodule ℂ B := ⨆ d, ℂ ∙ T d

/-- An element of `B` lies in the span of the components of `T` precisely when it is a
  linear combination of them. -/
lemma mem_span_iff (x : B) :
    x ∈ hT.span ↔ ∃ c : Fin 3 → ℂ, x = ∑ d, c d • T d := by
  constructor
  · intro hx
    rw [IsSU2Adjoint.span] at hx
    refine Submodule.iSup_induction
      (motive := fun y => ∃ c : Fin 3 → ℂ, y = ∑ d, c d • T d)
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

## B. The contraction against a coordinate vector

Contracting the single index of `T` against a coordinate vector gives `adjVec`, and the
span of the components is exactly the set of such contractions. The transformation law
says that a map moving the components by an `SU(2)` matrix moves a contraction by the row
action of that matrix on the coordinate vector, so all the work of the file happens on
coordinate vectors, where `IsSU2BiAdjoint.rowAct` and its lemmas already live.

-/

/-- The element of `B` obtained by contracting the `su(2)` adjoint index of `T` against a
  coordinate vector. -/
noncomputable def adjVec (hT : IsSU2Adjoint B repGauge T) (c : Fin 3 → ℂ) : B :=
  ∑ a : Fin 3, c a • T a

/-- Contracting against the zero coordinate vector. -/
@[simp]
lemma adjVec_zero : hT.adjVec 0 = 0 := by
  simp [adjVec]

/-- Contracting against a sum of coordinate vectors. -/
lemma adjVec_add (c c' : Fin 3 → ℂ) :
    hT.adjVec (c + c') = hT.adjVec c + hT.adjVec c' := by
  simp only [adjVec, Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- Contracting against a scaled coordinate vector. -/
lemma adjVec_smul (z : ℂ) (c : Fin 3 → ℂ) :
    hT.adjVec (z • c) = z • hT.adjVec c := by
  simp only [adjVec, Finset.smul_sum, Pi.smul_apply, smul_eq_mul, smul_smul]

/-- Contracting against a single Pauli direction returns a component of `T`. -/
lemma adjVec_unitVec (a : Fin 3) : hT.adjVec (unitVec a) = T a := by
  simp [adjVec, unitVec, ite_smul]

/-- The span of the components is the set of contractions. -/
lemma mem_span_iff_exists_adjVec (x : B) :
    x ∈ hT.span ↔ ∃ c : Fin 3 → ℂ, x = hT.adjVec c :=
  hT.mem_span_iff x

/-- Every contraction lies in the span of the components. -/
lemma adjVec_mem_span (c : Fin 3 → ℂ) : hT.adjVec c ∈ hT.span :=
  (hT.mem_span_iff_exists_adjVec _).2 ⟨c, rfl⟩

/-- A map moving the components by an `SU(2)` matrix moves a contraction by the row action
  of that matrix on the coordinate vector. This is the whole content of the transformation
  law in coordinate form, and it mentions no other factor of the gauge group. -/
lemma map_adjVec (hT : IsSU2Adjoint B repGauge T) {U : specialUnitaryGroup (Fin 2) ℂ}
    {f : B →ₗ[ℂ] B} (hf : IsSU2AdjointMat U f T) (c : Fin 3 → ℂ) :
    f (hT.adjVec c) = hT.adjVec (rowAct U c) := by
  have step : ∀ l : Fin 3, f (c l • T l)
      = ∑ a : Fin 3, (c l * ((su2AdjointMatrix U a l : ℝ) : ℂ)) • T a := by
    intro l
    rw [map_smul, hf l, Finset.smul_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [smul_smul]
  show f (∑ l : Fin 3, c l • T l) = ∑ a : Fin 3, rowAct U c a • T a
  rw [map_sum]
  simp only [step]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

/-- The isospin factor of the gauge group moves a contraction by the row action of its
  `SU(2)` element on the coordinate vector. -/
lemma repGauge_su2_adjVec (U : specialUnitaryGroup (Fin 2) ℂ) (c : Fin 3 → ℂ) :
    repGauge (1, U, 1) (hT.adjVec c) = hT.adjVec (rowAct U c) :=
  hT.map_adjVec (hT.repGauge_T U) c

end IsSU2Adjoint

/-!

## C. The isospin flips and the average over the Klein four-group

The elements `i σ₁`, `i σ₂` and `i σ₃` of `SU(2)` are the half turns about the three
isospin axes. C.1 records them, C.2 computes their adjoint matrices, which are diagonal
with a single `1` and two `-1`, and C.3 averages: the four signs attached to a Pauli
direction, one for the identity and one for each flip, are `1`, `1`, `-1`, `-1` in some
order, so they sum to zero and the average of the row action over the four elements is
zero outright.

There is no second average to do. The adjoint representation of `SU(2)` is three
dimensional, the Cartan direction is one of the three Pauli directions and the two flips
about the other two axes reverse it; a half turn about a perpendicular axis is the Weyl
reflection of `SU(2)`, so the Weyl step is inside the same average as the torus step.

## C.1. The three isospin flips

-/

/-- The matrix of the `k`-th isospin flip, the half turn `i σ` about the `k`-th isospin
  axis. It is unitary, and its determinant is `1` because `i ^ 2` cancels the determinant
  `-1` of a Pauli matrix. -/
noncomputable def su2FlipMatrix : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![0, Complex.I; Complex.I, 0]
  | 1 => !![0, 1; -1, 0]
  | 2 => !![Complex.I, 0; 0, -Complex.I]

/-- The star of the `k`-th isospin flip, which is its inverse and its negative, the Pauli
  matrices being self-adjoint. -/
noncomputable def su2FlipStarMatrix : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![0, -Complex.I; -Complex.I, 0]
  | 1 => !![0, -1; 1, 0]
  | 2 => !![-Complex.I, 0; 0, Complex.I]

/-- The `k`-th isospin flip as an element of `SU(2)`. The three flips and the identity are
  the Klein four-group of half turns inside the rotation group. -/
noncomputable def su2Flip (k : Fin 3) : specialUnitaryGroup (Fin 2) ℂ :=
  ⟨su2FlipMatrix k, by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff]
      fin_cases k <;> ext a b <;> fin_cases a <;> fin_cases b <;>
        simp [su2FlipMatrix, Matrix.mul_apply, Fin.sum_univ_two]
    · fin_cases k <;> simp [su2FlipMatrix, Matrix.det_fin_two_of]⟩

/-- The underlying matrix of an isospin flip. -/
lemma su2Flip_coe (k : Fin 3) : (su2Flip k).1 = su2FlipMatrix k := rfl

/-- The star of an isospin flip. -/
lemma star_su2FlipMatrix (k : Fin 3) :
    star (su2FlipMatrix k) = su2FlipStarMatrix k := by
  fin_cases k <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [su2FlipMatrix, su2FlipStarMatrix]

/-!

## C.2. The adjoint matrices of the flips

-/

/-- The sign by which the `k`-th isospin flip scales each Pauli direction: `1` on its own
  axis and `-1` on the other two, a half turn fixing its axis and reversing the plane
  perpendicular to it. -/
def su2FlipSign : Fin 3 → Fin 3 → ℝ
  | 0 => ![1, -1, -1]
  | 1 => ![-1, 1, -1]
  | 2 => ![-1, -1, 1]

/-- The adjoint matrix of an isospin flip is diagonal, with the sign of each Pauli
  direction on the diagonal. -/
lemma su2AdjointMatrix_su2Flip (k : Fin 3) (a b : Fin 3) :
    su2AdjointMatrix (su2Flip k) a b = if a = b then su2FlipSign k b else 0 := by
  rw [su2AdjointMatrix_apply, su2Flip_coe, star_su2FlipMatrix]
  fin_cases k <;> fin_cases a <;> fin_cases b <;>
    simp only [su2FlipMatrix, su2FlipStarMatrix, su2FlipSign, pauliMatrix,
      Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.of_apply] <;>
    norm_num [Complex.ext_iff]

/-- The flip about the second isospin axis has the adjoint matrix of the `SU(2)` Weyl
  element `su2Perm`, that element being the same half turn up to a sign. This is the
  sign check that the Weyl step of the argument is already inside the average of C.3. -/
lemma su2AdjointMatrix_su2Flip_one :
    su2AdjointMatrix (su2Flip 1) = su2AdjointMatrix su2Perm := by
  rw [su2AdjointMatrix_su2Perm]
  ext a b
  rw [su2AdjointMatrix_su2Flip]
  fin_cases a <;> fin_cases b <;> simp [su2FlipSign]

/-- The row action of an isospin flip on a coordinate vector scales each coordinate by the
  sign of its Pauli direction. -/
lemma rowAct_su2Flip_apply (k : Fin 3) (c : Fin 3 → ℂ) (a : Fin 3) :
    rowAct (su2Flip k) c a = ((su2FlipSign k a : ℝ) : ℂ) * c a := by
  show ∑ x : Fin 3, ((su2AdjointMatrix (su2Flip k) a x : ℝ) : ℂ) * c x = _
  simp only [su2AdjointMatrix_su2Flip, apply_ite (fun r : ℝ => (r : ℂ)),
    Complex.ofReal_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]

/-!

## C.3. The average

-/

/-- Averaging the row action over the Klein four-group of half turns, the three isospin
  flips together with the identity, gives zero: each Pauli direction is fixed by the
  identity and by the flip about its own axis and reversed by the other two flips, so its
  four signs cancel. This is the vector representation of the rotation group having no
  invariant vector, in coordinate form. -/
lemma sum_rowAct_su2Flip (c : Fin 3 → ℂ) :
    c + rowAct (su2Flip 0) c + rowAct (su2Flip 1) c + rowAct (su2Flip 2) c = 0 := by
  funext a
  simp only [Pi.add_apply, Pi.zero_apply, rowAct_su2Flip_apply]
  fin_cases a <;> simp [su2FlipSign]

/-!

## D. A single adjoint index carries no invariant

The average of section C is all that is needed. An isospin invariant of the span is
unchanged by each of the three flips, so four times it is the contraction of the averaged
coordinate vector, and that vector is zero. That is `eq_zero_of_su2_invariant`, and it is
the statement that the adjoint representation of `SU(2)` contains no singlet, in the form
the components of a family can carry it.

Section D.2 divides out a stable submodule. The quotient carries the images of the
components as an adjoint family again, so D.1 applies there verbatim, and an invariant of
the span joined with a stable `S` lies in `S` itself. That is the form a peeling argument
wants: an `su(2)` adjoint index contributes nothing to the invariants, so it may be
dropped from the sum and the rest of the argument continued in `S`.

## D.1. The vanishing

-/

namespace IsSU2Adjoint

set_option linter.unusedVariables false

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {T : Fin 3 → B}
  (hT : IsSU2Adjoint B repGauge T)

/-- An isospin invariant in the span of the components of an adjoint family is zero: the
  adjoint representation of `SU(2)` contains no singlet. Averaging the invariant over the
  Klein four-group of isospin flips leaves it unchanged on one side and annihilates its
  coordinate vector on the other. -/
theorem eq_zero_of_su2_invariant (hT : IsSU2Adjoint B repGauge T) {x : B}
    (hx : x ∈ hT.span)
    (hinv : ∀ U : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, U, 1) x = x) :
    x = 0 := by
  obtain ⟨c, hc⟩ := (hT.mem_span_iff_exists_adjVec x).1 hx
  have e : ∀ k : Fin 3, x = hT.adjVec (rowAct (su2Flip k) c) := fun k => by
    rw [← hT.repGauge_su2_adjVec, ← hc, hinv]
  have h4 : (4 : ℂ) • x = hT.adjVec (c + rowAct (su2Flip 0) c
      + rowAct (su2Flip 1) c + rowAct (su2Flip 2) c) := by
    rw [hT.adjVec_add, hT.adjVec_add, hT.adjVec_add, ← hc, ← e 0, ← e 1, ← e 2]
    module
  rw [sum_rowAct_su2Flip, hT.adjVec_zero] at h4
  have h := congrArg (fun y : B => (4 : ℂ)⁻¹ • y) h4
  simpa [smul_smul] using h

/-- The same for a gauge invariant, gauge invariance being invariance under the isospin
  factor and more. -/
theorem eq_zero_of_invariant (hT : IsSU2Adjoint B repGauge T) {x : B}
    (hx : x ∈ hT.span) (hinv : ∀ g : GaugeGroupI, repGauge g x = x) :
    x = 0 :=
  hT.eq_zero_of_su2_invariant hx fun U => hinv (1, U, 1)

/-!

## D.2. The invariants modulo a stable submodule

-/

/-- The images of the components in the quotient by a gauge-stable submodule again form
  an adjoint family. -/
lemma isSU2Adjoint_quotRep (hT : IsSU2Adjoint B repGauge T) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S) :
    IsSU2Adjoint (B ⧸ S) (quotRep repGauge S hS) fun l => S.mkQ (T l) where
  repGauge_T g l := by
    rw [quotRep_mkQ, hT.repGauge_T g l, map_sum]
    exact Finset.sum_congr rfl fun a _ => map_smul _ _ _

/-- An isospin invariant of the span of the components joined with an isospin-stable
  submodule `S` lies in `S` itself. The classification is applied in the quotient by `S`,
  where the images of the components form an adjoint family again and D.1 says that the
  class of the invariant is zero. The invariance is carried along for free: it is a
  hypothesis on the element, and the conclusion is about that same element. Stability of
  `S` is needed, and not just convenient: it is what makes the quotient representation
  exist. -/
theorem mem_of_mem_span_sup_su2_invariant (hT : IsSU2Adjoint B repGauge T) (x : B)
    (S : Submodule ℂ B)
    (hS : ∀ U : specialUnitaryGroup (Fin 2) ℂ, ∀ y ∈ S, repGauge (1, U, 1) y ∈ S)
    (hx : x ∈ hT.span ⊔ S)
    (hinv : ∀ U : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, U, 1) x = x) :
    x ∈ S := by
  have hS' : ∀ g : GaugeGroupI, ∀ y ∈ S, repSU2 repGauge g y ∈ S :=
    (repSU2_stable_iff_su2 repGauge S).2 hS
  have hquot := hT.toRepSU2.isSU2Adjoint_quotRep S hS'
  have hmk : S.mkQ x ∈ hquot.span := by
    obtain ⟨u, hu, z, hz, huz⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, hc⟩ := (hT.mem_span_iff u).1 hu
    refine (hquot.mem_span_iff _).2 ⟨c, ?_⟩
    rw [← huz, map_add, show S.mkQ z = 0 from (Submodule.Quotient.mk_eq_zero S).2 hz,
      add_zero, hc, map_sum]
    exact Finset.sum_congr rfl fun d _ => map_smul _ _ _
  have hinv' : ∀ U : specialUnitaryGroup (Fin 2) ℂ,
      quotRep (repSU2 repGauge) S hS' (1, U, 1) (S.mkQ x) = S.mkQ x := by
    intro U
    rw [quotRep_mkQ, (repSU2_invariant_iff_su2 repGauge x).2 hinv (1, U, 1)]
  exact (Submodule.Quotient.mk_eq_zero S).1
    (hquot.eq_zero_of_su2_invariant hmk hinv')

/-- The isospin invariants of the span of the components joined with an isospin-stable
  submodule are exactly the isospin invariants of the submodule: an `su(2)` adjoint index
  contributes nothing at all, so the join may be replaced by `S` and the invariance
  carried across unchanged. -/
theorem mem_span_sup_su2_invariant_iff (hT : IsSU2Adjoint B repGauge T) (x : B)
    (S : Submodule ℂ B)
    (hS : ∀ U : specialUnitaryGroup (Fin 2) ℂ, ∀ y ∈ S, repGauge (1, U, 1) y ∈ S) :
    (x ∈ hT.span ⊔ S ∧ ∀ U : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, U, 1) x = x)
      ↔ x ∈ S ∧ ∀ U : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, U, 1) x = x := by
  constructor
  · rintro ⟨hx, hinv⟩
    exact ⟨hT.mem_of_mem_span_sup_su2_invariant x S hS hx hinv, hinv⟩
  · rintro ⟨hx, hinv⟩
    exact ⟨Submodule.mem_sup_right hx, hinv⟩

/-- The gauge form of the same statement, for a gauge-stable submodule and a gauge
  invariant. -/
theorem mem_of_mem_span_sup_invariant (hT : IsSU2Adjoint B repGauge T) (x : B)
    (S : Submodule ℂ B) (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hx : x ∈ hT.span ⊔ S) (hinv : ∀ g : GaugeGroupI, repGauge g x = x) :
    x ∈ S :=
  hT.mem_of_mem_span_sup_su2_invariant x S (fun U => hS (1, U, 1)) hx
    fun U => hinv (1, U, 1)

end IsSU2Adjoint

end StandardModel
