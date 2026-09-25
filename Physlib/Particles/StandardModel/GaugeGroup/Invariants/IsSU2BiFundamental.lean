/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Mathematics.LeviCivita.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.SU2PermDecomposition
public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.Basic
/-!
# Gauge tensors carrying two `su(2)` fundamental indices

The Higgs field and the left-handed fermions are isospin doublets: each carries one
fundamental `su(2)` index, taking two values. A product of two doublets carries two, and the
isospin invariant is the antisymmetric combination `ε_{ab} T^{ab} = T^{01} - T^{10}`: modulo
an isospin-stable submodule, every isospin invariant of the span of the components is a
multiple of this epsilon contraction. In representation theory `2 ⊗ 2 = 1 ⊕ 3`; only the
spanning statement is formalized here.

`IsSU2BiFundamental B repGauge T` records the transformation law: an isospin rotation
`U ∈ SU(2)` moves the components by one factor of `U` per index, so the law acts on
coefficient vectors by the Kronecker square of `U`, whose conjugate transpose is the matrix
of `U⁻¹`. Nothing is asked of the colour and hypercharge factors, which may well move the
components: a product of two Higgs fields carries hypercharge.

The antisymmetric symbol is Physlib's `leviCivitaSymbol` on `Fin 2`, normalized by
`ε 0 1 = 1`. It is fixed because it transforms by the determinant
(`sum_leviCivitaSymbol_mul_prod`), and the determinant of an element of `SU(2)` is one. Two
rotations pin the fixed coefficient vectors down: the diagonal element `diag(i, -i)` scales
each diagonal entry `c ![a, a]` by `i² = -1`, so the diagonal vanishes, and the Weyl element
`su2Perm = !![0, -1; 1, 0]` carries `c ![1, 0]` to `-c ![0, 1]`, so the matrix is
antisymmetric.

- A. The transformation law
- B. The antisymmetric symbol and the epsilon contraction
- C. An invariant coefficient is a multiple of the antisymmetric symbol
- D. The reduction modulo a stable submodule
- Aside: the entries of an `SU(2)` matrix under conjugation
-/

@[expose] public section

namespace StandardModel

open Matrix ComplexConjugate

/-!

## A. The transformation law

-/

/-- The linear map `f` moves the components of `T` as `U ∈ SU(2)` moves a tensor with two
  fundamental indices: one factor of `U` per index, with the summed index in the row
  slot. -/
def IsSU2BiFundamentalMat {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (U : specialUnitaryGroup (Fin 2) ℂ) (f : B →ₗ[ℂ] B)
    (T : (Fin 2 → Fin 2) → B) : Prop :=
  ∀ l : Fin 2 → Fin 2,
    f (T l) = ∑ a : Fin 2 → Fin 2, (∏ i : Fin 2, U.1 (a i) (l i)) • T a

/-- A family `T` of elements of `B`, indexed by two `su(2)` fundamental indices, transforms
  as a tensor `T^{a b}` under the isospin factor of the gauge group. Nothing is asked of the
  colour and hypercharge factors. -/
structure IsSU2BiFundamental (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B)
    (T : (Fin 2 → Fin 2) → B) : Prop where
  repGauge_T : ∀ g : specialUnitaryGroup (Fin 2) ℂ,
    IsSU2BiFundamentalMat g (repGauge (1, g, 1)) T

namespace IsSU2BiFundamental

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}

/-- The span of the components. -/
def span (T : (Fin 2 → Fin 2) → B) : Submodule ℂ B := ⨆ d, ℂ ∙ T d

/-- A vector lies in the span precisely when it is a linear combination of the
  components. -/
lemma mem_span_iff {T : (Fin 2 → Fin 2) → B} (x : B) :
    x ∈ span T ↔ ∃ (c : (Fin 2 → Fin 2) → ℂ), x = ∑ d, c d • T d :=
  Family.mem_iSup_span_singleton_iff T x

/-- Every component lies in the span. -/
lemma mem_span {T : (Fin 2 → Fin 2) → B} (d : Fin 2 → Fin 2) : T d ∈ span T :=
  Family.mem_iSup_span_singleton T d

/-- A sum over pairs of fundamental indices is a double sum. -/
lemma sum_pi_two {M : Type*} [AddCommMonoid M] (F : (Fin 2 → Fin 2) → M) :
    ∑ d : Fin 2 → Fin 2, F d = ∑ x : Fin 2, ∑ y : Fin 2, F ![x, y] :=
  Family.sum_pi_two F

/-- A finite sum of bi-fundamental isospin families is such a family again. -/
lemma sum {ι : Type} [Fintype ι] {T : ι → (Fin 2 → Fin 2) → B}
    (hT : ∀ i, IsSU2BiFundamental B repGauge (T i)) :
    IsSU2BiFundamental B repGauge (fun l => ∑ i, T i l) where
  repGauge_T V l := by
    rw [map_sum, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => (hT i).repGauge_T V l,
      Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.smul_sum.symm

/-- The matrix by which the law acts on coefficient vectors: the Kronecker square of `U`.
  The law says `f (T l) = ∑ a, coeffMatrix U a l • T a` by definition. -/
noncomputable def coeffMatrix (U : specialUnitaryGroup (Fin 2) ℂ) :
    Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ :=
  Family.powMatrix U.1 2

/-- The coefficient matrix acting on a coefficient vector, written out. -/
lemma coeffMatrix_mulVec_apply (U : specialUnitaryGroup (Fin 2) ℂ) (c : (Fin 2 → Fin 2) → ℂ)
    (a : Fin 2 → Fin 2) :
    (coeffMatrix U *ᵥ c) a = ∑ l, (∏ i : Fin 2, U.1 (a i) (l i)) * c l :=
  rfl

/-- The coefficient matrix of `U⁻¹` is the conjugate transpose of that of `U`. -/
lemma coeffMatrix_inv (U : specialUnitaryGroup (Fin 2) ℂ) :
    coeffMatrix U⁻¹ = (coeffMatrix U)ᴴ := by
  rw [coeffMatrix, coeffMatrix, Family.powMatrix_conjTranspose, ← star_eq_inv,
    specialUnitaryGroup.coe_star, star_eq_conjTranspose]

/-!

## B. The antisymmetric symbol and the epsilon contraction

The antisymmetric symbol on two indices is the Levi-Civita symbol of `Fin 2`. Its invariance
under `SU(2)` is the determinant identity `sum_leviCivitaSymbol_mul_prod` at `det U = 1`, and
it makes the epsilon contraction `T ![0, 1] - T ![1, 0]` invariant.

-/

/-- The antisymmetric symbol as a coefficient vector on pairs of `su(2)` fundamental indices:
  the Levi-Civita symbol of `Fin 2`. -/
def epsilonCoeff : (Fin 2 → Fin 2) → ℂ := fun l => (leviCivitaSymbol l : ℤ)

/-- The antisymmetric symbol `ε_{ab}` on two `su(2)` fundamental indices, normalized by
  `ε 0 1 = 1`. -/
def epsilon (a b : Fin 2) : ℂ := epsilonCoeff ![a, b]

/-- The coefficient vector at a pair of indices is the antisymmetric symbol. -/
@[simp] lemma epsilonCoeff_cons (a b : Fin 2) : epsilonCoeff ![a, b] = epsilon a b := rfl

/-- The antisymmetric symbol vanishes on the repeated lower index. -/
@[simp] lemma epsilon_zero_zero : epsilon 0 0 = 0 := by
  simp [epsilon, epsilonCoeff, leviCivitaSymbol_eq_zero_of_eq (g := ![0, 0])
    (i := 0) (j := 1) (by decide) rfl]

/-- The antisymmetric symbol on the increasing pair. -/
@[simp] lemma epsilon_zero_one : epsilon 0 1 = 1 := by
  rw [epsilon, epsilonCoeff,
    show (![0, 1] : Fin 2 → Fin 2) = id from funext fun i => by fin_cases i <;> rfl,
    leviCivitaSymbol_id]
  simp

/-- The antisymmetric symbol on the decreasing pair. -/
@[simp] lemma epsilon_one_zero : epsilon 1 0 = -1 := by
  rw [epsilon, epsilonCoeff, show (![1, 0] : Fin 2 → Fin 2) = ⇑(Equiv.swap (0 : Fin 2) 1) from
      funext fun i => by fin_cases i <;> rfl, leviCivitaSymbol_perm,
    Equiv.Perm.sign_swap (by decide)]
  simp

/-- The antisymmetric symbol vanishes on the repeated upper index. -/
@[simp] lemma epsilon_one_one : epsilon 1 1 = 0 := by
  simp [epsilon, epsilonCoeff, leviCivitaSymbol_eq_zero_of_eq (g := ![1, 1])
    (i := 0) (j := 1) (by decide) rfl]

/-- The antisymmetric symbol is fixed by every coefficient matrix: contracted against two
  rows of `U` it gives `det U` times itself, and `det U = 1`. -/
lemma coeffMatrix_mulVec_epsilonCoeff (U : specialUnitaryGroup (Fin 2) ℂ) :
    coeffMatrix U *ᵥ epsilonCoeff = epsilonCoeff := by
  funext a
  have h := sum_leviCivitaSymbol_mul_prod U.1 a
  rw [(mem_specialUnitaryGroup_iff.mp U.2).2, one_mul] at h
  rw [coeffMatrix_mulVec_apply]
  exact (Finset.sum_congr rfl fun l _ => mul_comm _ _).trans h

/-- The invariance of the antisymmetric symbol as a double sum, the form the four-index
  pairings use. -/
lemma sum_epsilon_mul (U : specialUnitaryGroup (Fin 2) ℂ) (b c : Fin 2) :
    ∑ x : Fin 2, ∑ y : Fin 2, epsilon x y * (U.1 b x * U.1 c y) = epsilon b c := by
  have h := congrFun (coeffMatrix_mulVec_epsilonCoeff U) ![b, c]
  rw [coeffMatrix_mulVec_apply, Family.sum_pi_two] at h
  simpa [Fin.prod_univ_two, mul_comm] using h

/-- The epsilon contraction: the antisymmetric contraction of the two fundamental
  indices. -/
def epsilonContraction (T : (Fin 2 → Fin 2) → B) : B := T ![0, 1] - T ![1, 0]

/-- The epsilon contraction is the contraction against the antisymmetric symbol. -/
lemma sum_epsilonCoeff_smul (T : (Fin 2 → Fin 2) → B) :
    ∑ l, epsilonCoeff l • T l = epsilonContraction T := by
  rw [sum_pi_two]
  simp [epsilonContraction, Fin.sum_univ_two, sub_eq_add_neg]

/-- The epsilon contraction lies in the span of the components. -/
lemma epsilonContraction_mem_span (T : (Fin 2 → Fin 2) → B) :
    epsilonContraction T ∈ span T :=
  sub_mem (mem_span _) (mem_span _)

/-- Any map moving the components by an element of `SU(2)` fixes the epsilon
  contraction. -/
lemma map_epsilonContraction {T : (Fin 2 → Fin 2) → B} {U : specialUnitaryGroup (Fin 2) ℂ}
    {f : B →ₗ[ℂ] B} (hf : IsSU2BiFundamentalMat U f T) :
    f (epsilonContraction T) = epsilonContraction T := by
  have h := f.map_sum_smul_eq_self_of_mulVec_eq T (coeffMatrix U) hf
    (coeffMatrix_mulVec_epsilonCoeff U)
  rwa [sum_epsilonCoeff_smul] at h

/-- The epsilon contraction is isospin invariant. Nothing constrains the colour and
  hypercharge factors, which may well move it. -/
lemma repGauge_epsilonContraction {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2BiFundamental B repGauge T) (V : specialUnitaryGroup (Fin 2) ℂ) :
    repGauge (1, V, 1) (epsilonContraction T) = epsilonContraction T :=
  map_epsilonContraction (hT.repGauge_T V)

/-!

## C. An invariant coefficient is a multiple of the antisymmetric symbol

The isospin flip `su2Flip 2` about the third axis is the diagonal matrix `diag(i, -i)`. It
scales `c ![a, b]` by the product of the two diagonal entries, which on the diagonal `a = b`
is `-1`, so an invariant coefficient has zero diagonal. The Weyl element `su2Perm`, the
matrix `!![0, -1; 1, 0]`, carries `c ![1, 0]` to `-c ![0, 1]`, so an invariant coefficient
is antisymmetric.

-/

/-- The isospin flip about the third axis is the diagonal matrix `diag(i, -i)`. -/
lemma su2Flip_two_apply (a b : Fin 2) :
    (su2Flip 2).1 a b
      = if a = b then ![Complex.I, -Complex.I] a else 0 := by
  rw [su2Flip_coe]
  fin_cases a <;> fin_cases b <;> simp [su2FlipMatrix]

/-- The flip about the third axis scales a coefficient by the product of the diagonal
  entries at its two indices. -/
lemma coeffMatrix_su2Flip_two_mulVec (c : (Fin 2 → Fin 2) → ℂ) (a b : Fin 2) :
    (coeffMatrix (su2Flip 2) *ᵥ c) ![a, b]
      = ![Complex.I, -Complex.I] a * ![Complex.I, -Complex.I] b * c ![a, b] := by
  rw [coeffMatrix_mulVec_apply, sum_pi_two, Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp [su2Flip_two_apply]
  · intro y _ hy
    simp [su2Flip_two_apply, Ne.symm hy]
  · simp
  · intro x _ hx
    simp [su2Flip_two_apply, Ne.symm hx]
  · simp

/-- The Weyl element carries the lower mixed coefficient to minus the upper one. -/
lemma coeffMatrix_su2Perm_mulVec_one_zero (c : (Fin 2 → Fin 2) → ℂ) :
    (coeffMatrix su2Perm *ᵥ c) ![1, 0] = -c ![0, 1] := by
  rw [coeffMatrix_mulVec_apply, sum_pi_two]
  simp [su2Perm_coe, Fin.sum_univ_two, Fin.prod_univ_two]

/-- A coefficient vector fixed by every coefficient matrix is a multiple of the antisymmetric
  symbol. -/
lemma exists_eq_smul_epsilonCoeff_of_forall_mulVec_eq {c : (Fin 2 → Fin 2) → ℂ}
    (hc : ∀ U : specialUnitaryGroup (Fin 2) ℂ, coeffMatrix U *ᵥ c = c) :
    ∃ z : ℂ, c = z • epsilonCoeff := by
  have hdiag : ∀ a : Fin 2, c ![a, a] = 0 := by
    intro a
    have hsq : ![Complex.I, -Complex.I] a * ![Complex.I, -Complex.I] a = -1 := by
      fin_cases a <;> simp
    have h := congrFun (hc (su2Flip 2)) ![a, a]
    rw [coeffMatrix_su2Flip_two_mulVec, hsq] at h
    linear_combination (-1 / 2 : ℂ) * h
  have hoff : c ![1, 0] = -c ![0, 1] := by
    have h := congrFun (hc su2Perm) ![1, 0]
    rw [coeffMatrix_su2Perm_mulVec_one_zero] at h
    exact h.symm
  refine ⟨c ![0, 1], funext fun l => ?_⟩
  obtain ⟨a, b, rfl⟩ : ∃ a b, l = ![a, b] := ⟨l 0, l 1, by ext i; fin_cases i <;> rfl⟩
  fin_cases a <;> fin_cases b <;> simp [hdiag, hoff]

/-!

## D. The reduction modulo a stable submodule

`reducesInvariantsTo_span_singleton_of_mulVec_eq` applies section C in every quotient by a
stable submodule. `invariantReductionToSpan` is the case of the isospin factor of the gauge
group, the form the Yukawa files consume.

-/

/-- For any family of maps `σ U` obeying the law, a `σ`-invariant of the span joined with a
  `σ`-stable submodule `S` is a multiple of the epsilon contraction plus an element of `S`. -/
lemma reducesInvariantsTo_span_epsilonContraction
    (σ : specialUnitaryGroup (Fin 2) ℂ → B →ₗ[ℂ] B) {T : (Fin 2 → Fin 2) → B}
    (hT : ∀ U, IsSU2BiFundamentalMat U (σ U) T) :
    ReducesInvariantsTo σ (span T) (ℂ ∙ epsilonContraction T) := by
  have h := reducesInvariantsTo_span_singleton_of_mulVec_eq (σ := σ) T coeffMatrix hT
    (fun U => ⟨U⁻¹, coeffMatrix_inv U⟩) epsilonCoeff fun _ hc =>
      exists_eq_smul_epsilonCoeff_of_forall_mulVec_eq hc
  rwa [sum_epsilonCoeff_smul] at h

/-- The isospin invariants of the component span reduce to the span of the epsilon
  contraction. -/
noncomputable def invariantReductionToSpan {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2BiFundamental B repGauge T) :
    InvariantReductionToSpan (fun V : specialUnitaryGroup (Fin 2) ℂ => repGauge (1, V, 1))
      (span T) :=
  InvariantReductionToSpan.ofReducesInvariantsTo
    (isStableUnder_iSup_span_singleton_of_sum fun V l => ⟨_, hT.repGauge_T V l⟩)
    (epsilonContraction T) (repGauge_epsilonContraction hT)
    (reducesInvariantsTo_span_epsilonContraction _ hT.repGauge_T)

/-!

## Aside: the entries of an `SU(2)` matrix under conjugation

Nothing from here on is used by the classification. `SU(2)` is pseudo-real: the conjugate of
an `SU(2)` matrix is its conjugate by the antisymmetric symbol, so an anti-fundamental index
is a fundamental index in another basis. `IsSU2AntiFundamental` reduces its two laws to the
one above by that change of basis, and what it needs is the four identities
`conj U₀₀ = U₁₁`, `conj U₁₁ = U₀₀`, `conj U₀₁ = -U₁₀`, `conj U₁₀ = -U₀₁`. They come from one
computation: the determinant being one, the adjugate of `U` is its inverse, and `U` being
unitary, so is its conjugate transpose. The Higgs sector uses the same four identities.

-/

/-- An index pair is the pair of its own two entries. -/
lemma eq_cons (d : Fin 2 → Fin 2) : d = ![d 0, d 1] :=
  funext fun j => by fin_cases j <;> simp

/-- The conjugate transpose of an `SU(2)` matrix is its adjugate. -/
lemma star_eq_adjugate (U : specialUnitaryGroup (Fin 2) ℂ) :
    star U.1 = Matrix.adjugate U.1 := by
  have hmem := Matrix.mem_specialUnitaryGroup_iff.mp U.2
  have hu : star U.1 * U.1 = 1 := Matrix.mem_unitaryGroup_iff'.mp hmem.1
  calc star U.1 = star U.1 * (U.1 * Matrix.adjugate U.1) := by
        rw [Matrix.mul_adjugate, hmem.2, one_smul, mul_one]
    _ = star U.1 * U.1 * Matrix.adjugate U.1 := by rw [mul_assoc]
    _ = Matrix.adjugate U.1 := by rw [hu, one_mul]

/-- The conjugate of an entry of an `SU(2)` matrix is the transposed entry of its
  adjugate. -/
lemma conj_apply (U : specialUnitaryGroup (Fin 2) ℂ) (i j : Fin 2) :
    conj (U.1 i j) = Matrix.adjugate U.1 j i := by
  have := congrFun (congrFun (star_eq_adjugate U) j) i
  simpa [Matrix.star_apply] using this

/-- Conjugating the upper left entry of an `SU(2)` matrix gives the lower right one. -/
@[simp] lemma conj_apply_zero_zero (U : specialUnitaryGroup (Fin 2) ℂ) :
    conj (U.1 0 0) = U.1 1 1 := by
  rw [conj_apply, Matrix.adjugate_fin_two]
  simp

/-- Conjugating the lower right entry of an `SU(2)` matrix gives the upper left one. -/
@[simp] lemma conj_apply_one_one (U : specialUnitaryGroup (Fin 2) ℂ) :
    conj (U.1 1 1) = U.1 0 0 := by
  rw [conj_apply, Matrix.adjugate_fin_two]
  simp

/-- Conjugating the upper right entry of an `SU(2)` matrix gives minus the lower left
  one. -/
@[simp] lemma conj_apply_zero_one (U : specialUnitaryGroup (Fin 2) ℂ) :
    conj (U.1 0 1) = -U.1 1 0 := by
  rw [conj_apply, Matrix.adjugate_fin_two]
  simp

/-- Conjugating the lower left entry of an `SU(2)` matrix gives minus the upper right
  one. -/
@[simp] lemma conj_apply_one_zero (U : specialUnitaryGroup (Fin 2) ℂ) :
    conj (U.1 1 0) = -U.1 0 1 := by
  rw [conj_apply, Matrix.adjugate_fin_two]
  simp

end IsSU2BiFundamental

end StandardModel
