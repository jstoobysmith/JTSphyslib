/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.IsSU3BiAdjoint
/-!
# Gauge tensors carrying one `su(3)` adjoint index

`IsSU3Adjoint B repGauge T` says that a family `T`, indexed by a single `su(3)` adjoint
index and valued in a module `B` carrying a representation of the gauge group
`GaugeGroupI`, transforms as a tensor `T^a` in the `su(3)` factor of the adjoint
representation.

This is the one index companion of `IsSU3BiAdjoint`. The field strength of the gluons
carries one `su(3)` adjoint index, so a single field strength, or any expression built
linearly from one, transforms in this way, and the proposition here records that law.

The law itself is `IsSU3AdjointMat`, which relates one element of `SU(3)` to one linear
map on `B` and mentions no other factor of the gauge group, through `su3AdjointMatrix`,
the adjoint matrix of an `SU(3)` element alone. `IsSU3Adjoint` says that the colour
transformation `(U, 1, 1)` obeys that law with the matrix of `U`, for every `U` in
`SU(3)`, and it says nothing whatever about the isospin and hypercharge factors: those
may move the components as they please.

The point of the file is that a single adjoint index carries no invariant at all. The
adjoint representation of `SU(3)` contains no singlet, so `eq_zero_of_su3_invariant`: an
element of the span of the components fixed by the colour factor is zero. The route to
`IsSU3BiFundamental`'s vanishing, the centre of `SU(3)`, is unavailable here, the centre
acting trivially on the adjoint. What replaces it is the torus and the Weyl group, in the
concrete form of two finite averages, and neither needs an algebra structure on `B`, a
multiplicativity hypothesis on `repGauge` or the gauge weight decomposition.

Section A gives the transformation law, the proposition and the span of the components,
and section B the contraction of the single index against a coordinate vector, through
which the law reads as the row action `IsSU3BiAdjoint.rowAct` on coordinate vectors.
Section C is the torus step: the three colour flips `su3Flip`, the diagonal sign matrices
of `SU(3)`, scale each Gell-Mann direction by a sign, and together with the identity they
average to four times the projection onto the two Cartan directions. So a colour
invariant is a combination of the two Cartan components `T 2` and `T 7` alone, which is
the statement that its gauge weight vanishes, got here without any weight bookkeeping.
Section D is the Weyl step: the cyclic colour rotation `su3Perm` scales the two Cartan
eigenvectors `IsSU3BiAdjoint.cartanVec` by `ω` and `ω ^ 2`, so the three powers of the
rotation average to zero on the Cartan plane, there being no cube root of unity summing
to a nonzero multiple of itself. Section E puts the two averages together: three times a
colour invariant of the span is the contraction of the annihilated coordinate vector, so
it vanishes, and section E.2 transports that to the quotient by a stable submodule, which
is the form `mem_span_sup_su3_invariant_iff` a peeling argument needs.
-/

@[expose] public section

namespace StandardModel

open Matrix IsSU3BiAdjoint

/-!

## A. The transformation law and the span of the components

An `su(3)` adjoint index is acted on by the `SU(3)` factor of the gauge group alone,
through `su3AdjointMatrix`, the matrix of `IsSU3BiAdjoint` section A.1. The law carries
one factor of that matrix, with the summed index in the row slot, exactly as each of the
two indices of a bi-adjoint family does.

-/

/-- The linear map `f` moves the components of the family `T` as the `SU(3)` matrix `U`
  moves a tensor with one adjoint index: one factor of `su3AdjointMatrix U`, with the
  summed index in the row slot. -/
def IsSU3AdjointMat {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (U : specialUnitaryGroup (Fin 3) ℂ) (f : B →ₗ[ℂ] B) (T : Fin 8 → B) : Prop :=
  ∀ l : Fin 8, f (T l) = ∑ a : Fin 8, ((su3AdjointMatrix U a l : ℝ) : ℂ) • T a

/-- A family `T` of elements of `B`, indexed by one `su(3)` adjoint index, transforms as a
  tensor `T^a` under the representation `repGauge` of the gauge group: a colour
  transformation moves the components by the `SU(3)` element it is built from. Nothing is
  asked of the isospin or hypercharge factors. -/
structure IsSU3Adjoint (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B) (T : Fin 8 → B) : Prop where
  repGauge_T : ∀ g : specialUnitaryGroup (Fin 3) ℂ,
    IsSU3AdjointMat g (repGauge (g, 1, 1)) T

namespace IsSU3Adjoint

set_option linter.unusedVariables false

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {T : Fin 8 → B}
  (hT : IsSU3Adjoint B repGauge T)

/-- An adjoint family for a representation is an adjoint family for its colour part: the
  transformation law reads only the colour factor to begin with. -/
lemma toRepSU3 (hT : IsSU3Adjoint B repGauge T) :
    IsSU3Adjoint B (repSU3 repGauge) T where
  repGauge_T g := hT.repGauge_T g

/-- The span of all the components. -/
def span (hT : IsSU3Adjoint B repGauge T) : Submodule ℂ B := ⨆ d, ℂ ∙ T d

/-- An element of `B` lies in the span of the components of `T` precisely when it is a
  linear combination of them. -/
lemma mem_span_iff (x : B) :
    x ∈ hT.span ↔ ∃ c : Fin 8 → ℂ, x = ∑ d, c d • T d := by
  constructor
  · intro hx
    rw [IsSU3Adjoint.span] at hx
    refine Submodule.iSup_induction
      (motive := fun y => ∃ c : Fin 8 → ℂ, y = ∑ d, c d • T d)
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
says that a map moving the components by an `SU(3)` matrix moves a contraction by the row
action of that matrix on the coordinate vector, so all the work of the file happens on
coordinate vectors, where `IsSU3BiAdjoint.rowAct` and its lemmas already live.

-/

/-- The element of `B` obtained by contracting the `su(3)` adjoint index of `T` against a
  coordinate vector. -/
noncomputable def adjVec (hT : IsSU3Adjoint B repGauge T) (c : Fin 8 → ℂ) : B :=
  ∑ a : Fin 8, c a • T a

/-- Contracting against the zero coordinate vector. -/
@[simp]
lemma adjVec_zero : hT.adjVec 0 = 0 := by
  simp [adjVec]

/-- Contracting against a sum of coordinate vectors. -/
lemma adjVec_add (c c' : Fin 8 → ℂ) :
    hT.adjVec (c + c') = hT.adjVec c + hT.adjVec c' := by
  simp only [adjVec, Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- Contracting against a scaled coordinate vector. -/
lemma adjVec_smul (z : ℂ) (c : Fin 8 → ℂ) :
    hT.adjVec (z • c) = z • hT.adjVec c := by
  simp only [adjVec, Finset.smul_sum, Pi.smul_apply, smul_eq_mul, smul_smul]

/-- Contracting against a single Gell-Mann direction returns a component of `T`. -/
lemma adjVec_unitVec (a : Fin 8) : hT.adjVec (unitVec a) = T a := by
  simp [adjVec, unitVec, ite_smul]

/-- The span of the components is the set of contractions. -/
lemma mem_span_iff_exists_adjVec (x : B) :
    x ∈ hT.span ↔ ∃ c : Fin 8 → ℂ, x = hT.adjVec c :=
  hT.mem_span_iff x

/-- Every contraction lies in the span of the components. -/
lemma adjVec_mem_span (c : Fin 8 → ℂ) : hT.adjVec c ∈ hT.span :=
  (hT.mem_span_iff_exists_adjVec _).2 ⟨c, rfl⟩

/-- A map moving the components by an `SU(3)` matrix moves a contraction by the row action
  of that matrix on the coordinate vector. This is the whole content of the transformation
  law in coordinate form, and it mentions no other factor of the gauge group. -/
lemma map_adjVec (hT : IsSU3Adjoint B repGauge T) {U : specialUnitaryGroup (Fin 3) ℂ}
    {f : B →ₗ[ℂ] B} (hf : IsSU3AdjointMat U f T) (c : Fin 8 → ℂ) :
    f (hT.adjVec c) = hT.adjVec (rowAct U c) := by
  have step : ∀ l : Fin 8, f (c l • T l)
      = ∑ a : Fin 8, (c l * ((su3AdjointMatrix U a l : ℝ) : ℂ)) • T a := by
    intro l
    rw [map_smul, hf l, Finset.smul_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [smul_smul]
  show f (∑ l : Fin 8, c l • T l) = ∑ a : Fin 8, rowAct U c a • T a
  rw [map_sum]
  simp only [step]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

/-- The colour factor of the gauge group moves a contraction by the row action of its
  `SU(3)` element on the coordinate vector. -/
lemma repGauge_su3_adjVec (U : specialUnitaryGroup (Fin 3) ℂ) (c : Fin 8 → ℂ) :
    repGauge (U, 1, 1) (hT.adjVec c) = hT.adjVec (rowAct U c) :=
  hT.map_adjVec (hT.repGauge_T U) c

end IsSU3Adjoint

/-!

## C. The torus step: the colour flips and the Cartan directions

C.1 records two facts about the Gell-Mann coordinates that the step rests on: the
coordinates of a Gell-Mann matrix are a Kronecker delta, and the coordinates are
homogeneous for a real scaling of the matrix. C.2 introduces the three colour flips
`su3Flip`, the diagonal matrices of `SU(3)` with one entry `1` and two entries `-1`, and
computes their adjoint matrices: conjugation by a diagonal sign matrix scales each
Gell-Mann matrix by a sign, so the adjoint matrix is diagonal, with the sign
`su3FlipSign` on the diagonal.

The three flips and the identity form the Klein four-group of diagonal sign matrices, and
C.3 is what that buys: the four signs attached to a Gell-Mann direction sum to `4` on the
two Cartan directions and to `0` on the six root directions, since each root direction
sees the product of two different diagonal entries and that product is negative for
exactly two of the four elements. Averaging over the four is therefore four times the
projection onto the Cartan plane. This is the finite substitute for the gauge weight
decomposition: a colour invariant has vanishing gauge weight, and the conclusion here,
`exists_cartan_of_su3_invariant`, is precisely that its coordinate vector may be taken
supported on the two Cartan indices `2` and `7`.

## C.1. Two facts about the Gell-Mann coordinates

-/

/-- The Gell-Mann coordinates of a Gell-Mann matrix are a Kronecker delta: the Gell-Mann
  matrices are a basis and the coordinates read off the coefficients in it. -/
lemma gellMannCoeff_gellMannMatrix (a b : Fin 8) :
    gellMannCoeff (gellMannMatrix b) a = if a = b then 1 else 0 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  fin_cases a <;> fin_cases b <;>
    simp [gellMannCoeff, gellMannMatrix_zero, gellMannMatrix_one, gellMannMatrix_two,
      gellMannMatrix_three, gellMannMatrix_four, gellMannMatrix_five, gellMannMatrix_six,
      gellMannMatrix_seven]
  linear_combination h3 / 3

/-- The Gell-Mann coordinates are homogeneous for a real scaling of the matrix, each of
  them being a real linear function of the entries. -/
lemma gellMannCoeff_real_smul (s : ℝ) (M : Matrix (Fin 3) (Fin 3) ℂ) (a : Fin 8) :
    gellMannCoeff ((s : ℂ) • M) a = s * gellMannCoeff M a := by
  fin_cases a <;> simp [gellMannCoeff, Matrix.smul_apply] <;> ring

/-!

## C.2. The three colour flips and their adjoint matrices

-/

/-- The matrix of the `k`-th colour flip: the diagonal matrix fixing the colour `k` and
  reversing the other two. Its determinant is the product of one `1` and two `-1`, so it
  is `1`, and it is its own star and its own inverse. -/
noncomputable def su3FlipMatrix : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ
  | 0 => !![1, 0, 0; 0, -1, 0; 0, 0, -1]
  | 1 => !![-1, 0, 0; 0, 1, 0; 0, 0, -1]
  | 2 => !![-1, 0, 0; 0, -1, 0; 0, 0, 1]

/-- The `k`-th colour flip as an element of `SU(3)`. The three flips and the identity are
  the Klein four-group of diagonal sign matrices inside `SU(3)`. -/
noncomputable def su3Flip (k : Fin 3) : specialUnitaryGroup (Fin 3) ℂ :=
  ⟨su3FlipMatrix k, by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff]
      fin_cases k <;> ext a b <;> fin_cases a <;> fin_cases b <;>
        simp [su3FlipMatrix, Matrix.mul_apply, Fin.sum_univ_three]
    · fin_cases k <;> simp [su3FlipMatrix, Matrix.det_fin_three]⟩

/-- The underlying matrix of a colour flip. -/
lemma su3Flip_coe (k : Fin 3) : (su3Flip k).1 = su3FlipMatrix k := rfl

/-- A colour flip is its own star, its entries being real. -/
lemma star_su3FlipMatrix (k : Fin 3) : star (su3FlipMatrix k) = su3FlipMatrix k := by
  fin_cases k <;> ext a b <;> fin_cases a <;> fin_cases b <;> simp [su3FlipMatrix]

/-- The sign by which the `k`-th colour flip scales each Gell-Mann direction: the product
  of the two diagonal entries of the flip that the direction pairs, which is `1` on the
  two Cartan directions and on the root pair not involving the colour `k`, and `-1` on the
  four remaining root directions. -/
def su3FlipSign : Fin 3 → Fin 8 → ℝ
  | 0 => ![-1, -1, 1, -1, -1, 1, 1, 1]
  | 1 => ![-1, -1, 1, 1, 1, -1, -1, 1]
  | 2 => ![1, 1, 1, -1, -1, -1, -1, 1]

set_option maxHeartbeats 1000000 in
/-- Conjugating a Gell-Mann matrix by a colour flip scales it by the sign of that
  direction: conjugation by a diagonal matrix multiplies the entry in row `i` and column
  `j` by the product of the `i`-th and `j`-th diagonal entries, and each Gell-Mann matrix
  is supported where that product is constant. -/
lemma conj_gellMannMatrix_su3Flip (k : Fin 3) (b : Fin 8) :
    (su3Flip k).1 * gellMannMatrix b * star (su3Flip k).1
      = ((su3FlipSign k b : ℝ) : ℂ) • gellMannMatrix b := by
  rw [su3Flip_coe, star_su3FlipMatrix]
  fin_cases k <;> fin_cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [su3FlipMatrix, su3FlipSign, gellMannMatrix_zero, gellMannMatrix_one,
      gellMannMatrix_two, gellMannMatrix_three, gellMannMatrix_four, gellMannMatrix_five,
      gellMannMatrix_six, gellMannMatrix_seven, Matrix.mul_apply, Fin.sum_univ_three]

/-- The adjoint matrix of a colour flip is diagonal, with the sign of each Gell-Mann
  direction on the diagonal. -/
lemma su3AdjointMatrix_su3Flip (k : Fin 3) (a b : Fin 8) :
    su3AdjointMatrix (su3Flip k) a b = if a = b then su3FlipSign k b else 0 := by
  rw [su3AdjointMatrix_eq_gellMannCoeff, conj_gellMannMatrix_su3Flip,
    gellMannCoeff_real_smul, gellMannCoeff_gellMannMatrix]
  split_ifs <;> ring

/-- The row action of a colour flip on a coordinate vector scales each coordinate by the
  sign of its Gell-Mann direction. -/
lemma rowAct_su3Flip_apply (k : Fin 3) (c : Fin 8 → ℂ) (a : Fin 8) :
    rowAct (su3Flip k) c a = ((su3FlipSign k a : ℝ) : ℂ) * c a := by
  show ∑ x : Fin 8, ((su3AdjointMatrix (su3Flip k) a x : ℝ) : ℂ) * c x = _
  simp only [su3AdjointMatrix_su3Flip, apply_ite (fun r : ℝ => (r : ℂ)),
    Complex.ofReal_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]

/-!

## C.3. The average over the Klein four-group

-/

/-- The coordinate vector of a combination of the two Cartan directions, the Gell-Mann
  directions `2` and `7`. -/
noncomputable def cartanCoord (α β : ℂ) : Fin 8 → ℂ := α • unitVec 2 + β • unitVec 7

/-- Averaging the row action over the Klein four-group of diagonal sign matrices, the
  three colour flips together with the identity, is four times the projection onto the
  Cartan plane: the four signs attached to a root direction cancel in pairs, while those
  attached to a Cartan direction are all `1`. -/
lemma sum_rowAct_su3Flip (c : Fin 8 → ℂ) :
    c + rowAct (su3Flip 0) c + rowAct (su3Flip 1) c + rowAct (su3Flip 2) c
      = (4 : ℂ) • cartanCoord (c 2) (c 7) := by
  funext a
  simp only [Pi.add_apply, Pi.smul_apply, rowAct_su3Flip_apply, cartanCoord, unitVec,
    smul_eq_mul]
  fin_cases a <;> simp [su3FlipSign] <;> ring

namespace IsSU3Adjoint

set_option linter.unusedVariables false

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {T : Fin 8 → B}
  (hT : IsSU3Adjoint B repGauge T)

/-- Contracting against a Cartan coordinate vector gives a combination of the two Cartan
  components of `T`. -/
lemma adjVec_cartanCoord (α β : ℂ) :
    hT.adjVec (cartanCoord α β) = α • T 2 + β • T 7 := by
  rw [cartanCoord, hT.adjVec_add, hT.adjVec_smul, hT.adjVec_smul, hT.adjVec_unitVec,
    hT.adjVec_unitVec]

/-- A colour invariant in the span of the components is a combination of the two Cartan
  components alone. Averaging the invariant over the Klein four-group of colour flips
  replaces its coordinate vector by four times the Cartan part of that vector, and an
  invariant is unchanged by the average. This is the vanishing of the gauge weight of an
  invariant, read off a finite average rather than the torus. -/
lemma exists_cartan_of_su3_invariant (hT : IsSU3Adjoint B repGauge T) {x : B}
    (hx : x ∈ hT.span)
    (hinv : ∀ U : specialUnitaryGroup (Fin 3) ℂ, repGauge (U, 1, 1) x = x) :
    ∃ α β : ℂ, x = hT.adjVec (cartanCoord α β) := by
  obtain ⟨c, hc⟩ := (hT.mem_span_iff_exists_adjVec x).1 hx
  have e : ∀ k : Fin 3, x = hT.adjVec (rowAct (su3Flip k) c) := fun k => by
    rw [← hT.repGauge_su3_adjVec, ← hc, hinv]
  refine ⟨c 2, c 7, ?_⟩
  have h4 : (4 : ℂ) • x = hT.adjVec (c + rowAct (su3Flip 0) c
      + rowAct (su3Flip 1) c + rowAct (su3Flip 2) c) := by
    rw [hT.adjVec_add, hT.adjVec_add, hT.adjVec_add, ← hc, ← e 0, ← e 1, ← e 2]
    module
  rw [sum_rowAct_su3Flip, hT.adjVec_smul] at h4
  have h := congrArg (fun y : B => (4 : ℂ)⁻¹ • y) h4
  simpa [smul_smul] using h

end IsSU3Adjoint

/-!

## D. The Weyl step: the cyclic rotation on the Cartan plane

The Klein four-group leaves the Cartan plane untouched, so it cannot be what makes an
invariant vanish; the element that moves the Cartan plane is the cyclic colour rotation
`su3Perm`, which normalises the torus and rotates the plane through `2 π / 3`. Its two
eigenvectors there are `IsSU3BiAdjoint.cartanVec`, at the eigenvalues `ω` and `ω ^ 2`,
and neither eigenvalue is `1`: the Cartan plane is the two-dimensional reflection
representation of the Weyl group `S₃` and carries no invariant vector.

The form in which that is used below is the vanishing of the symmetriser
`1 + P + P ^ 2` of the cyclic subgroup on the Cartan plane, which is
`SU3PermDecomposition`'s `su3PermSign_symmetrizer`, the statement that the three powers of
a nontrivial cube root of unity sum to zero. D.1 rewrites the two Cartan coordinate
directions in the eigenbasis and D.2 applies the symmetriser.

## D.1. The Cartan coordinate directions in the eigenbasis

-/

/-- The Gell-Mann direction `2` in the eigenbasis of the cyclic colour rotation. -/
lemma unitVec_two_eq_cartanVec :
    unitVec 2 = (2 : ℂ)⁻¹ • (cartanVec 0 + cartanVec 1) := by
  rw [show (2 : Fin 8) = GaugeAlgebra.su3CartanId 0 from rfl, unitVec_cartanId,
    wtCoeff_cartan_zero]

/-- The Gell-Mann direction `7` in the eigenbasis of the cyclic colour rotation. -/
lemma unitVec_seven_eq_cartanVec :
    unitVec 7 = (Complex.I / 2) • (cartanVec 0 - cartanVec 1) := by
  rw [show (7 : Fin 8) = GaugeAlgebra.su3CartanId 1 from rfl, unitVec_cartanId,
    wtCoeff_cartan_one]

/-- A Cartan coordinate vector in the eigenbasis of the cyclic colour rotation. -/
lemma cartanCoord_eq_cartanVec (α β : ℂ) :
    cartanCoord α β = (α / 2 + β * Complex.I / 2) • cartanVec 0
      + (α / 2 - β * Complex.I / 2) • cartanVec 1 := by
  rw [cartanCoord, unitVec_two_eq_cartanVec, unitVec_seven_eq_cartanVec]
  module

/-!

## D.2. The symmetriser of the cyclic rotation on the Cartan plane

-/

/-- The symmetriser of the cyclic colour rotation kills each Cartan eigenvector: the
  eigenvalue is a nontrivial cube root of unity, and the three powers of such a root sum
  to zero. -/
lemma su3Perm_symmetrizer_cartanVec (i : Fin 2) :
    cartanVec i + rowAct su3Perm (cartanVec i)
      + rowAct su3Perm (rowAct su3Perm (cartanVec i)) = 0 := by
  have hgrade : cartanGrade i ≠ 0 := by fin_cases i <;> decide
  have hsum := su3PermSign_symmetrizer hgrade
  rw [rowAct_su3Perm_cartanVec, rowAct_smul, rowAct_su3Perm_cartanVec, smul_smul]
  have hcomb : cartanVec i + su3PermSign (cartanGrade i) • cartanVec i
      + (su3PermSign (cartanGrade i) * su3PermSign (cartanGrade i)) • cartanVec i
      = (1 + su3PermSign (cartanGrade i) + su3PermSign (cartanGrade i) ^ 2)
        • cartanVec i := by
    module
  rw [hcomb, hsum, zero_smul]

/-- The symmetriser of the cyclic colour rotation kills every Cartan coordinate vector,
  the Cartan plane being spanned by the two eigenvectors. -/
lemma su3Perm_symmetrizer_cartanCoord (α β : ℂ) :
    cartanCoord α β + rowAct su3Perm (cartanCoord α β)
      + rowAct su3Perm (rowAct su3Perm (cartanCoord α β)) = 0 := by
  have h0 := su3Perm_symmetrizer_cartanVec 0
  have h1 := su3Perm_symmetrizer_cartanVec 1
  rw [cartanCoord_eq_cartanVec, rowAct_add, rowAct_smul, rowAct_smul, rowAct_add,
    rowAct_smul, rowAct_smul]
  have hcomb : ∀ z w : ℂ,
      (z • cartanVec 0 + w • cartanVec 1)
        + (z • rowAct su3Perm (cartanVec 0) + w • rowAct su3Perm (cartanVec 1))
        + (z • rowAct su3Perm (rowAct su3Perm (cartanVec 0))
          + w • rowAct su3Perm (rowAct su3Perm (cartanVec 1)))
      = z • (cartanVec 0 + rowAct su3Perm (cartanVec 0)
          + rowAct su3Perm (rowAct su3Perm (cartanVec 0)))
        + w • (cartanVec 1 + rowAct su3Perm (cartanVec 1)
          + rowAct su3Perm (rowAct su3Perm (cartanVec 1))) := by
    intro z w
    module
  rw [hcomb, h0, h1, smul_zero, smul_zero, add_zero]

/-!

## E. A single adjoint index carries no invariant

The two averages of sections C and D are all that is needed. A colour invariant of the
span has a Cartan coordinate vector by section C, and the symmetriser of the cyclic
rotation kills that vector by section D, while an invariant is unchanged by each of the
three powers of the rotation; so three times the invariant is the contraction of the
zero coordinate vector. That is `eq_zero_of_su3_invariant`, and it is the statement that
the adjoint representation of `SU(3)` contains no singlet, in the form the components of
a family can carry it. Nothing beyond a module structure on `B` is used: there is no
algebra, no multiplicativity hypothesis and no gauge weight decomposition anywhere in the
argument.

Section E.2 divides out a stable submodule. The quotient carries the images of the
components as an adjoint family again, so E.1 applies there verbatim, and an invariant of
the span joined with a stable `S` lies in `S` itself. That is the form a peeling argument
wants: an `su(3)` adjoint index contributes nothing to the invariants, so it may be
dropped from the sum and the rest of the argument continued in `S`.

## E.1. The vanishing

-/

namespace IsSU3Adjoint

set_option linter.unusedVariables false

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {T : Fin 8 → B}
  (hT : IsSU3Adjoint B repGauge T)

/-- A colour invariant in the span of the components of an adjoint family is zero: the
  adjoint representation of `SU(3)` contains no singlet. The colour flips of section C
  push the invariant onto the Cartan plane and the cyclic colour rotation of section D
  has no invariant vector there, the two eigenvalues being the nontrivial cube roots of
  unity. The route used for a pair of fundamental indices, the centre of `SU(3)`, is not
  available: the centre acts trivially on the adjoint. -/
theorem eq_zero_of_su3_invariant (hT : IsSU3Adjoint B repGauge T) {x : B}
    (hx : x ∈ hT.span)
    (hinv : ∀ U : specialUnitaryGroup (Fin 3) ℂ, repGauge (U, 1, 1) x = x) :
    x = 0 := by
  obtain ⟨α, β, hd⟩ := hT.exists_cartan_of_su3_invariant hx hinv
  have e1 : x = hT.adjVec (rowAct su3Perm (cartanCoord α β)) := by
    rw [← hT.repGauge_su3_adjVec, ← hd, hinv]
  have e2 : x
      = hT.adjVec (rowAct su3Perm (rowAct su3Perm (cartanCoord α β))) := by
    rw [← hT.repGauge_su3_adjVec, ← e1, hinv]
  have h3 : (3 : ℂ) • x = hT.adjVec (cartanCoord α β
      + rowAct su3Perm (cartanCoord α β)
      + rowAct su3Perm (rowAct su3Perm (cartanCoord α β))) := by
    rw [hT.adjVec_add, hT.adjVec_add, ← hd, ← e1, ← e2]
    module
  rw [su3Perm_symmetrizer_cartanCoord, hT.adjVec_zero] at h3
  have h := congrArg (fun y : B => (3 : ℂ)⁻¹ • y) h3
  simpa [smul_smul] using h

/-- The same for a gauge invariant, gauge invariance being invariance under the colour
  factor and more. -/
theorem eq_zero_of_invariant (hT : IsSU3Adjoint B repGauge T) {x : B}
    (hx : x ∈ hT.span) (hinv : ∀ g : GaugeGroupI, repGauge g x = x) :
    x = 0 :=
  hT.eq_zero_of_su3_invariant hx fun U => hinv (U, 1, 1)

/-!

## E.2. The invariants modulo a stable submodule

-/

/-- The images of the components in the quotient by a gauge-stable submodule again form
  an adjoint family. -/
lemma isSU3Adjoint_quotRep (hT : IsSU3Adjoint B repGauge T) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S) :
    IsSU3Adjoint (B ⧸ S) (quotRep repGauge S hS) fun l => S.mkQ (T l) where
  repGauge_T g l := by
    rw [quotRep_mkQ, hT.repGauge_T g l, map_sum]
    exact Finset.sum_congr rfl fun a _ => map_smul _ _ _

/-- A colour invariant of the span of the components joined with a colour-stable
  submodule `S` lies in `S` itself. The classification is applied in the quotient by `S`,
  where the images of the components form an adjoint family again and E.1 says that the
  class of the invariant is zero. The invariance is carried along for free: it is a
  hypothesis on the element, and the conclusion is about that same element. Stability of
  `S` is needed, and not just convenient: it is what makes the quotient representation
  exist. -/
theorem mem_of_mem_span_sup_su3_invariant (hT : IsSU3Adjoint B repGauge T) (x : B)
    (S : Submodule ℂ B)
    (hS : ∀ U : specialUnitaryGroup (Fin 3) ℂ, ∀ y ∈ S, repGauge (U, 1, 1) y ∈ S)
    (hx : x ∈ hT.span ⊔ S)
    (hinv : ∀ U : specialUnitaryGroup (Fin 3) ℂ, repGauge (U, 1, 1) x = x) :
    x ∈ S := by
  have hS' : ∀ g : GaugeGroupI, ∀ y ∈ S, repSU3 repGauge g y ∈ S :=
    (repSU3_stable_iff_su3 repGauge S).2 hS
  have hquot := hT.toRepSU3.isSU3Adjoint_quotRep S hS'
  have hmk : S.mkQ x ∈ hquot.span := by
    obtain ⟨u, hu, z, hz, huz⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, hc⟩ := (hT.mem_span_iff u).1 hu
    refine (hquot.mem_span_iff _).2 ⟨c, ?_⟩
    rw [← huz, map_add, show S.mkQ z = 0 from (Submodule.Quotient.mk_eq_zero S).2 hz,
      add_zero, hc, map_sum]
    exact Finset.sum_congr rfl fun d _ => map_smul _ _ _
  have hinv' : ∀ U : specialUnitaryGroup (Fin 3) ℂ,
      quotRep (repSU3 repGauge) S hS' (U, 1, 1) (S.mkQ x) = S.mkQ x := by
    intro U
    rw [quotRep_mkQ, (repSU3_invariant_iff_su3 repGauge x).2 hinv (U, 1, 1)]
  exact (Submodule.Quotient.mk_eq_zero S).1
    (hquot.eq_zero_of_su3_invariant hmk hinv')

/-- The colour invariants of the span of the components joined with a colour-stable
  submodule are exactly the colour invariants of the submodule: an `su(3)` adjoint index
  contributes nothing at all, so the join may be replaced by `S` and the invariance
  carried across unchanged. -/
theorem mem_span_sup_su3_invariant_iff (hT : IsSU3Adjoint B repGauge T) (x : B)
    (S : Submodule ℂ B)
    (hS : ∀ U : specialUnitaryGroup (Fin 3) ℂ, ∀ y ∈ S, repGauge (U, 1, 1) y ∈ S) :
    (x ∈ hT.span ⊔ S ∧ ∀ U : specialUnitaryGroup (Fin 3) ℂ, repGauge (U, 1, 1) x = x)
      ↔ x ∈ S ∧ ∀ U : specialUnitaryGroup (Fin 3) ℂ, repGauge (U, 1, 1) x = x := by
  constructor
  · rintro ⟨hx, hinv⟩
    exact ⟨hT.mem_of_mem_span_sup_su3_invariant x S hS hx hinv, hinv⟩
  · rintro ⟨hx, hinv⟩
    exact ⟨Submodule.mem_sup_right hx, hinv⟩

/-- The gauge form of the same statement, for a gauge-stable submodule and a gauge
  invariant. -/
theorem mem_of_mem_span_sup_invariant (hT : IsSU3Adjoint B repGauge T) (x : B)
    (S : Submodule ℂ B) (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hx : x ∈ hT.span ⊔ S) (hinv : ∀ g : GaugeGroupI, repGauge g x = x) :
    x ∈ S :=
  hT.mem_of_mem_span_sup_su3_invariant x S (fun U => hS (U, 1, 1)) hx
    fun U => hinv (U, 1, 1)

end IsSU3Adjoint

end StandardModel
