/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.SU2Conjugation
public import Physlib.Particles.StandardModel.GaugeGroup.SU2PermDecomposition
public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.Basic
/-!
# Families with two `su(2)` fundamental indices

A family `T : (Fin 2 → Fin 2) → B` obeys the `su(2)` bi-fundamental law when an isospin
rotation `U` moves it by one factor of `U` per index, the summed index in the row slot. The
family moves like the tensor products of standard basis vectors of `ℂ²`. By the symbol
convention of `Invariants.Basic`, the products of two conjugate doublet symbols form such a
family, and so do two doublet symbols once each is re-indexed by `su2Epsilon`.

Modulo an isospin-stable submodule, every isospin invariant of the span of the family is a
multiple of the epsilon contraction `T ![0, 1] - T ![1, 0]`.

The antisymmetric symbol is fixed because `det U = 1` (`GaugeGroup.SU2Conjugation`). Two
rotations pin the fixed coefficient vectors down: the diagonal element `diag(i, -i)` scales
each diagonal entry `c ![a, a]` by `i² = -1`, so the diagonal vanishes, and the Weyl element
`su2Perm = !![0, -1; 1, 0]` carries `c ![1, 0]` to `-c ![0, 1]`, so the coefficients are
antisymmetric.

- A. The transformation law
- B. The antisymmetric symbol and the epsilon contraction
- C. An invariant coefficient is a multiple of the antisymmetric symbol
- D. The reduction modulo a stable submodule
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

The coefficient vector of the antisymmetric symbol is the Levi-Civita symbol of `Fin 2`. Its
invariance is the determinant identity `sum_leviCivitaSymbol_mul_prod` at `det U = 1`, and it
makes the epsilon contraction `T ![0, 1] - T ![1, 0]` invariant.

-/

/-- The antisymmetric symbol as a coefficient vector on pairs of `su(2)` fundamental indices:
  the Levi-Civita symbol of `Fin 2`. -/
def epsilonCoeff : (Fin 2 → Fin 2) → ℂ := fun l => (leviCivitaSymbol l : ℤ)

/-- The coefficient vector at a pair of indices is the antisymmetric symbol. -/
@[simp] lemma epsilonCoeff_cons (a b : Fin 2) : epsilonCoeff ![a, b] = su2Epsilon a b := rfl

/-- The antisymmetric symbol is fixed by every coefficient matrix: contracted against two
  rows of `U` it gives `det U` times itself, and `det U = 1`. -/
lemma coeffMatrix_mulVec_epsilonCoeff (U : specialUnitaryGroup (Fin 2) ℂ) :
    coeffMatrix U *ᵥ epsilonCoeff = epsilonCoeff := by
  funext a
  have h := sum_leviCivitaSymbol_mul_prod U.1 a
  rw [(mem_specialUnitaryGroup_iff.mp U.2).2, one_mul] at h
  rw [coeffMatrix_mulVec_apply]
  exact (Finset.sum_congr rfl fun l _ => mul_comm _ _).trans h

/-- The epsilon contraction: the antisymmetric contraction of the two fundamental
  indices. -/
def epsilonContraction (T : (Fin 2 → Fin 2) → B) : B := T ![0, 1] - T ![1, 0]

/-- The epsilon contraction is the contraction against the antisymmetric symbol. -/
lemma sum_epsilonCoeff_smul (T : (Fin 2 → Fin 2) → B) :
    ∑ l, epsilonCoeff l • T l = epsilonContraction T := by
  rw [Family.sum_pi_two]
  simp [epsilonContraction, Fin.sum_univ_two, sub_eq_add_neg]

/-- The epsilon contraction lies in the span of the components. -/
lemma epsilonContraction_mem_span (T : (Fin 2 → Fin 2) → B) :
    epsilonContraction T ∈ Submodule.span ℂ (Set.range T) :=
  sub_mem (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)

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
  rw [coeffMatrix_mulVec_apply, Family.sum_pi_two, Finset.sum_eq_single a, Finset.sum_eq_single b]
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
  rw [coeffMatrix_mulVec_apply, Family.sum_pi_two]
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
    ReducesInvariantsTo σ (Submodule.span ℂ (Set.range T)) (ℂ ∙ epsilonContraction T) := by
  have h := reducesInvariantsTo_span_singleton_of_mulVec_eq (σ := σ) T coeffMatrix hT
    (fun U => ⟨U⁻¹, coeffMatrix_inv U⟩) epsilonCoeff fun _ hc =>
      exists_eq_smul_epsilonCoeff_of_forall_mulVec_eq hc
  rwa [sum_epsilonCoeff_smul] at h

/-- The isospin invariants of the component span reduce to the span of the epsilon
  contraction. -/
noncomputable def invariantReductionToSpan {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2BiFundamental B repGauge T) :
    InvariantReductionToSpan (fun V : specialUnitaryGroup (Fin 2) ℂ => repGauge (1, V, 1))
      (Submodule.span ℂ (Set.range T)) :=
  InvariantReductionToSpan.ofReducesInvariantsTo
    (isStableUnder_span_range_of_sum fun V l => ⟨_, hT.repGauge_T V l⟩)
    (epsilonContraction T) (repGauge_epsilonContraction hT)
    (reducesInvariantsTo_span_epsilonContraction _ hT.repGauge_T)

end IsSU2BiFundamental

end StandardModel
