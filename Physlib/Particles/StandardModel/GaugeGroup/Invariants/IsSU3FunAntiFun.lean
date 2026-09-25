/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.SU3PermDecomposition
public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.Basic
/-!
# Gauge tensors carrying a fundamental and an anti-fundamental `su(3)` index

A quark carries a fundamental colour index and an antiquark an anti-fundamental one, so a
quark-antiquark bilinear, the colour structure of every Yukawa coupling and of every fermion
kinetic term, carries one of each. The colour invariant is the Kronecker delta: modulo a
colour-stable submodule, every colour invariant of the span of the components is a multiple
of the delta contraction `∑ a, T ![a, a]`. In representation theory `3 ⊗ 3̄ = 8 ⊕ 1`; only
the spanning statement is formalized here.

`IsSU3FunAntiFun B repGauge T` records the transformation law: a colour rotation
`U ∈ SU(3)` moves the components by `U` on the first index and by the entrywise conjugate
`conj U` on the second. For unitary `U` the conjugate is `(U⁻¹)ᵀ`, so the conjugate and the
dual conventions agree here. Nothing is asked of the isospin and hypercharge factors, which
may well move the components: a quark-antiquark bilinear carries hypercharge.

The law acts on coefficient vectors by `coeffMatrix U`, the pair matrix of `U` and `conj U`,
whose conjugate transpose is `coeffMatrix U⁻¹`. The delta is fixed because the rows of `U`
are orthonormal; this uses only unitarity, so it is an invariant of `U(3)`, whereas the
epsilon of `IsSU2BiFundamental` uses the determinant. Two rotations pin down the fixed
coefficient vectors, as in `IsSU2BiAdjoint`: the colour parity fixing the colour `a` and
reversing the other two changes the sign of every entry `c ![a, b]` with `b ≠ a`, and the
cyclic permutation of the colours equates the diagonal entries.

- A. The transformation law
- B. The delta contraction
- C. An invariant coefficient is a multiple of the Kronecker delta
- D. The reduction modulo a stable submodule
-/

@[expose] public section

namespace StandardModel

open Matrix ComplexConjugate

/-!

## A. The transformation law

-/

/-- The linear map `f` moves the components of `T` as `U ∈ SU(3)` moves a tensor with one
  fundamental and one anti-fundamental index: a factor of `U` for the first index and a
  factor of `conj U` for the second. -/
def IsSU3FunAntiFunMat {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (U : specialUnitaryGroup (Fin 3) ℂ) (f : B →ₗ[ℂ] B)
    (T : (Fin 2 → Fin 3) → B) : Prop :=
  ∀ l : Fin 2 → Fin 3,
    f (T l) = ∑ a : Fin 2 → Fin 3, (U.1 (a 0) (l 0) * conj (U.1 (a 1) (l 1))) • T a

/-- A family `T` of elements of `B`, indexed by one `su(3)` fundamental and one
  anti-fundamental index, transforms as a tensor `T^{a}{}_{b}` under the colour factor of
  the gauge group. Nothing is asked of the isospin and hypercharge factors. -/
structure IsSU3FunAntiFun (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B)
    (T : (Fin 2 → Fin 3) → B) : Prop where
  repGauge_T : ∀ g : specialUnitaryGroup (Fin 3) ℂ,
    IsSU3FunAntiFunMat g (repGauge (g, 1, 1)) T

namespace IsSU3FunAntiFun

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}

/-- The span of the components. -/
def span (T : (Fin 2 → Fin 3) → B) : Submodule ℂ B := ⨆ d, ℂ ∙ T d

/-- Every component lies in the span. -/
lemma mem_span {T : (Fin 2 → Fin 3) → B} (d : Fin 2 → Fin 3) : T d ∈ span T :=
  Family.mem_iSup_span_singleton T d

/-- A sum over pairs of colour indices is a double sum. -/
lemma sum_pi_two {M : Type*} [AddCommMonoid M] (F : (Fin 2 → Fin 3) → M) :
    ∑ d : Fin 2 → Fin 3, F d = ∑ x : Fin 3, ∑ y : Fin 3, F ![x, y] :=
  Family.sum_pi_two F

/-- A finite sum of families carrying one fundamental and one anti-fundamental colour index
  is such a family again. -/
lemma sum {ι : Type} [Fintype ι] {T : ι → (Fin 2 → Fin 3) → B}
    (hT : ∀ i, IsSU3FunAntiFun B repGauge (T i)) :
    IsSU3FunAntiFun B repGauge (fun l => ∑ i, T i l) where
  repGauge_T U l := by
    rw [map_sum, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => (hT i).repGauge_T U l,
      Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.smul_sum.symm

/-- The matrix by which the law acts on coefficient vectors: `U` on the fundamental index and
  `conj U` on the anti-fundamental one. The law says `f (T l) = ∑ a, coeffMatrix U a l • T a`
  by definition. -/
noncomputable def coeffMatrix (U : specialUnitaryGroup (Fin 3) ℂ) :
    Matrix (Fin 2 → Fin 3) (Fin 2 → Fin 3) ℂ :=
  Family.pairMatrix U.1 (U.1.map conj)

/-- The coefficient matrix acting on a coefficient vector, written out. -/
lemma coeffMatrix_mulVec_apply (U : specialUnitaryGroup (Fin 3) ℂ) (c : (Fin 2 → Fin 3) → ℂ)
    (a : Fin 2 → Fin 3) :
    (coeffMatrix U *ᵥ c) a = ∑ l, (U.1 (a 0) (l 0) * conj (U.1 (a 1) (l 1))) * c l :=
  rfl

/-- The coefficient matrix of `U⁻¹` is the conjugate transpose of that of `U`. -/
lemma coeffMatrix_inv (U : specialUnitaryGroup (Fin 3) ℂ) :
    coeffMatrix U⁻¹ = (coeffMatrix U)ᴴ := by
  rw [coeffMatrix, coeffMatrix, Family.pairMatrix_conjTranspose, ← star_eq_inv,
    specialUnitaryGroup.coe_star, star_eq_conjTranspose]
  congr 1

/-!

## B. The delta contraction

-/

/-- The delta contraction: the colour trace of the family. -/
def deltaContraction (T : (Fin 2 → Fin 3) → B) : B := ∑ a : Fin 3, T ![a, a]

/-- The delta contraction lies in the span of the components. -/
lemma deltaContraction_mem_span (T : (Fin 2 → Fin 3) → B) :
    deltaContraction T ∈ span T :=
  sum_mem fun _ _ => mem_span _

/-- The Kronecker delta is fixed by every coefficient matrix: the rows of a unitary matrix
  are orthonormal, `U * (conj U)ᵀ = U * Uᴴ = 1`. -/
lemma coeffMatrix_mulVec_deltaCoeff (U : specialUnitaryGroup (Fin 3) ℂ) :
    coeffMatrix U *ᵥ Family.deltaCoeff = Family.deltaCoeff := by
  refine Family.pairMatrix_mulVec_deltaCoeff ?_
  have h : (U.1.map conj)ᵀ = star U.1 := by
    ext a b
    simp [star_apply]
  rw [h, ← mem_unitaryGroup_iff]
  exact (mem_specialUnitaryGroup_iff.mp U.2).1

/-- Any map moving the components by an element of `SU(3)` fixes the delta contraction. -/
lemma map_deltaContraction {T : (Fin 2 → Fin 3) → B} {U : specialUnitaryGroup (Fin 3) ℂ}
    {f : B →ₗ[ℂ] B} (hf : IsSU3FunAntiFunMat U f T) :
    f (deltaContraction T) = deltaContraction T := by
  have h := f.map_sum_smul_eq_self_of_mulVec_eq T (coeffMatrix U) hf
    (coeffMatrix_mulVec_deltaCoeff U)
  rwa [Family.sum_deltaCoeff_smul] at h

/-- The delta contraction is colour invariant. Nothing constrains the isospin and
  hypercharge factors, which may well move it. -/
lemma repGauge_deltaContraction {T : (Fin 2 → Fin 3) → B}
    (hT : IsSU3FunAntiFun B repGauge T) (U : specialUnitaryGroup (Fin 3) ℂ) :
    repGauge (U, 1, 1) (deltaContraction T) = deltaContraction T :=
  map_deltaContraction (hT.repGauge_T U)

/-!

## C. An invariant coefficient is a multiple of the Kronecker delta

The colour parity fixing the colour `k` and reversing the other two is the diagonal matrix
with entries `±1`, so it multiplies `c ![a, b]` by the product of the signs of `a` and `b`,
which is `-1` whenever exactly one of them is `k`: taking `k = a` kills every entry off the
diagonal. The cyclic permutation `su3Perm` of the colours carries `c ![a, a]` to
`c ![a + 1, a + 1]`, so the diagonal entries agree.

-/

/-- A colour parity multiplies an entry by the product of the signs of its two indices. -/
lemma coeffMatrix_su3Parity_mulVec (k : Fin 3) (c : (Fin 2 → Fin 3) → ℂ) (a b : Fin 3) :
    (coeffMatrix (su3Parity k) *ᵥ c) ![a, b]
      = (if a = k then 1 else -1) * (if b = k then 1 else -1) * c ![a, b] := by
  rw [coeffMatrix_mulVec_apply, sum_pi_two, Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp [su3Parity_apply, apply_ite conj]
  · intro y _ hy
    simp [su3Parity_apply, Ne.symm hy]
  · simp
  · intro x _ hx
    simp [su3Parity_apply, Ne.symm hx]
  · simp

/-- The cyclic permutation carries the first diagonal entry to the second. -/
lemma coeffMatrix_su3Perm_mulVec_one_one (c : (Fin 2 → Fin 3) → ℂ) :
    (coeffMatrix su3Perm *ᵥ c) ![1, 1] = c ![0, 0] := by
  rw [coeffMatrix_mulVec_apply, sum_pi_two]
  simp [su3Perm_coe, Fin.sum_univ_three]

/-- The cyclic permutation carries the second diagonal entry to the third. -/
lemma coeffMatrix_su3Perm_mulVec_two_two (c : (Fin 2 → Fin 3) → ℂ) :
    (coeffMatrix su3Perm *ᵥ c) ![2, 2] = c ![1, 1] := by
  rw [coeffMatrix_mulVec_apply, sum_pi_two]
  simp [su3Perm_coe, Fin.sum_univ_three]

/-- A coefficient vector fixed by every coefficient matrix is a multiple of the Kronecker
  delta. -/
lemma exists_eq_smul_deltaCoeff_of_forall_mulVec_eq {c : (Fin 2 → Fin 3) → ℂ}
    (hc : ∀ U : specialUnitaryGroup (Fin 3) ℂ, coeffMatrix U *ᵥ c = c) :
    ∃ z : ℂ, c = z • Family.deltaCoeff := by
  have hoff : ∀ a b : Fin 3, a ≠ b → c ![a, b] = 0 := by
    intro a b hab
    have h := congrFun (hc (su3Parity a)) ![a, b]
    rw [coeffMatrix_su3Parity_mulVec, ite_eq_left rfl, ite_eq_right (Ne.symm hab)] at h
    linear_combination (-1 / 2 : ℂ) * h
  have hdiag : ∀ a : Fin 3, c ![a, a] = c ![0, 0] := by
    have h1 := congrFun (hc su3Perm) ![1, 1]
    have h2 := congrFun (hc su3Perm) ![2, 2]
    rw [coeffMatrix_su3Perm_mulVec_one_one] at h1
    rw [coeffMatrix_su3Perm_mulVec_two_two] at h2
    intro a
    have ha : a = 0 ∨ a = 1 ∨ a = 2 := by
      revert a
      decide
    rcases ha with rfl | rfl | rfl
    · rfl
    · exact h1.symm
    · rw [← h2, ← h1]
  refine ⟨c ![0, 0], funext fun l => ?_⟩
  obtain ⟨a, b, rfl⟩ : ∃ a b, l = ![a, b] := ⟨l 0, l 1, by ext i; fin_cases i <;> rfl⟩
  by_cases h : a = b
  · subst h
    simp [Family.deltaCoeff, hdiag]
  · simp [Family.deltaCoeff, h, hoff a b h]

/-!

## D. The reduction modulo a stable submodule

`reducesInvariantsTo_span_singleton_of_mulVec_eq` applies section C in every quotient by a
stable submodule, so the span reduces to the span of the delta contraction for any family of
maps obeying the law. `invariantReductionToSpan` is the case of the colour factor of the
gauge group, the form the Yukawa and fermion kinetic files consume.

-/

/-- For any family of maps `σ U` obeying the law, a `σ`-invariant of the span joined with a
  `σ`-stable submodule `S` is a multiple of the delta contraction plus an element of `S`. -/
lemma reducesInvariantsTo_span_deltaContraction
    (σ : specialUnitaryGroup (Fin 3) ℂ → B →ₗ[ℂ] B) {T : (Fin 2 → Fin 3) → B}
    (hT : ∀ U, IsSU3FunAntiFunMat U (σ U) T) :
    ReducesInvariantsTo σ (span T) (ℂ ∙ deltaContraction T) := by
  have h := reducesInvariantsTo_span_singleton_of_mulVec_eq (σ := σ) T coeffMatrix hT
    (fun U => ⟨U⁻¹, coeffMatrix_inv U⟩) Family.deltaCoeff fun _ hc =>
      exists_eq_smul_deltaCoeff_of_forall_mulVec_eq hc
  rwa [Family.sum_deltaCoeff_smul] at h

/-- The colour invariants of the component span reduce to the span of the delta
  contraction. -/
noncomputable def invariantReductionToSpan {T : (Fin 2 → Fin 3) → B}
    (hT : IsSU3FunAntiFun B repGauge T) :
    InvariantReductionToSpan (fun U : specialUnitaryGroup (Fin 3) ℂ => repGauge (U, 1, 1))
      (span T) :=
  InvariantReductionToSpan.ofReducesInvariantsTo
    (isStableUnder_iSup_span_singleton_of_sum fun U l => ⟨_, hT.repGauge_T U l⟩)
    (deltaContraction T) (repGauge_deltaContraction hT)
    (reducesInvariantsTo_span_deltaContraction _ hT.repGauge_T)

end IsSU3FunAntiFun

end StandardModel
