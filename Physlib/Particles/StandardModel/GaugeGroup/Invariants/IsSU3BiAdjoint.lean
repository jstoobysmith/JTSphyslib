/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.AdjointMatrix
public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.Basic
/-!
# Families with two `su(3)` adjoint indices

A family `T : (Fin 2 → Fin 8) → B` obeys the `su(3)` bi-adjoint law when a colour rotation `U`
moves it by one factor of `su3AdjointMatrix U` per index. The adjoint matrix is real and
orthogonal, so this law is its own dual and the symbol convention of `Invariants.Basic` plays
no role.

Modulo a colour-stable submodule, every colour invariant of the span of the family is a
multiple of the trace contraction `∑ a, T ![a, a]`.

A coefficient vector is a bilinear form on Gell-Mann coordinates. Five rotations, whose
adjoint matrices are computed in `GaugeGroup.AdjointMatrix`, force an invariant form to be a
multiple of the Kronecker delta: the three colour parities and `su3Turn` permute Gell-Mann
directions up to sign, and the cyclic permutation `su3Perm` also rotates the Cartan plane.

- A. The transformation law
- B. The coefficient matrix and the trace contraction
- C. An invariant coefficient is a multiple of the Kronecker delta
- D. The reduction modulo a stable submodule
-/

@[expose] public section

namespace StandardModel

open Matrix

/-!

## A. The transformation law

`IsSU3BiAdjointMat U f T` relates one element of `SU(3)` to one linear map on `B`.
`IsSU3BiAdjoint` asks it of the colour rotations `repGauge (U, 1, 1)` alone.

-/

/-- The linear map `f` moves the components of `T` as `U ∈ SU(3)` moves a tensor with two
  adjoint indices: one factor of the adjoint matrix per index. -/
def IsSU3BiAdjointMat {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (U : specialUnitaryGroup (Fin 3) ℂ) (f : B →ₗ[ℂ] B)
    (T : (Fin 2 → Fin 8) → B) : Prop :=
  ∀ l : Fin 2 → Fin 8,
    f (T l) = ∑ a : Fin 2 → Fin 8,
      (∏ i : Fin 2, ((su3AdjointMatrix U (a i) (l i) : ℝ) : ℂ)) • T a

/-- A family `T` of elements of `B`, indexed by two `su(3)` adjoint indices, transforms as a
  tensor `T^{a b}` under the colour factor of the gauge group. -/
structure IsSU3BiAdjoint (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B)
    (T : (Fin 2 → Fin 8) → B) : Prop where
  repGauge_T : ∀ g : specialUnitaryGroup (Fin 3) ℂ,
    IsSU3BiAdjointMat g (repGauge (g, 1, 1)) T

namespace IsSU3BiAdjoint

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B} {T : (Fin 2 → Fin 8) → B}

/-!

## B. The coefficient matrix and the trace contraction

The law acts on coefficient vectors by the Kronecker square of the complex adjoint matrix. Its
conjugate transpose is the matrix of `U⁻¹`, and it fixes the Kronecker delta because the rows
of the adjoint matrix are orthonormal.

-/

/-- The matrix by which the law acts on coefficient vectors: one factor of the adjoint matrix
  per index. The law says `f (T l) = ∑ a, coeffMatrix U a l • T a` by definition. -/
noncomputable def coeffMatrix (U : specialUnitaryGroup (Fin 3) ℂ) :
    Matrix (Fin 2 → Fin 8) (Fin 2 → Fin 8) ℂ :=
  Family.powMatrix (su3AdjointCoeffMatrix U) 2

/-- The coefficient matrix of `U⁻¹` is the conjugate transpose of that of `U`. -/
lemma coeffMatrix_inv (U : specialUnitaryGroup (Fin 3) ℂ) :
    coeffMatrix U⁻¹ = (coeffMatrix U)ᴴ := by
  rw [coeffMatrix, coeffMatrix, Family.powMatrix_conjTranspose, su3AdjointCoeffMatrix_inv]

/-- The coefficient matrix of `U⁻¹` is also the transpose of that of `U`. -/
lemma coeffMatrix_transpose (U : specialUnitaryGroup (Fin 3) ℂ) :
    (coeffMatrix U)ᵀ = coeffMatrix U⁻¹ := by
  ext a l
  simp only [transpose_apply, coeffMatrix, Family.powMatrix, of_apply,
    ← su3AdjointCoeffMatrix_transpose]

/-- The Kronecker delta is fixed by every coefficient matrix. -/
lemma coeffMatrix_mulVec_deltaCoeff (U : specialUnitaryGroup (Fin 3) ℂ) :
    coeffMatrix U *ᵥ Family.deltaCoeff = Family.deltaCoeff := by
  rw [coeffMatrix, Family.powMatrix_two]
  exact Family.pairMatrix_mulVec_deltaCoeff (su3AdjointCoeffMatrix_mul_transpose U)

/-- The trace contraction: the Kronecker contraction of the two colour indices. -/
def traceContraction (T : (Fin 2 → Fin 8) → B) : B := ∑ a : Fin 8, T ![a, a]

/-- Any map moving the components by an `SU(3)` matrix fixes the trace contraction. -/
lemma map_traceContraction {U : specialUnitaryGroup (Fin 3) ℂ} {f : B →ₗ[ℂ] B}
    (hf : IsSU3BiAdjointMat U f T) : f (traceContraction T) = traceContraction T := by
  have h := f.map_sum_smul_eq_self_of_mulVec_eq T (coeffMatrix U) hf
    (coeffMatrix_mulVec_deltaCoeff U)
  rwa [Family.sum_deltaCoeff_smul] at h

/-!

## C. An invariant coefficient is a multiple of the Kronecker delta

A coefficient `c` is a bilinear form `form c` on coordinate vectors, with `c ![a, b]` its value
on two Gell-Mann directions. If `c` is fixed by every coefficient matrix then the form is fixed
by every complex adjoint matrix (`form_mulVec`), so a rotation carrying `gellMannUnitVec a` to
`s • gellMannUnitVec a'` and `gellMannUnitVec b` to `t • gellMannUnitVec b'` gives
`c ![a, b] = s * t * c ![a', b']` (`entry_eq_of_mulVec`). The parities kill every entry joining
two directions of different sign pattern, and the turn and the cyclic rotation carry the
remaining off-diagonal entries onto killed ones (`eq_zero_of_ne`). The turn and the cyclic
rotation equate the diagonal entries, the Cartan pair through the rotation of the Cartan
plane, whose off-diagonal entries are now zero (`diag_eq`).

-/

/-- The bilinear form on coordinate vectors with coefficients `c`. -/
def form (c : (Fin 2 → Fin 8) → ℂ) (v w : Fin 8 → ℂ) : ℂ := ∑ l, v (l 0) * w (l 1) * c l

/-- The form on two scaled Gell-Mann directions is a scaled entry of `c`. -/
lemma form_smul_gellMannUnitVec (c : (Fin 2 → Fin 8) → ℂ) (s t : ℂ) (a b : Fin 8) :
    form c (s • gellMannUnitVec a) (t • gellMannUnitVec b) = s * t * c ![a, b] := by
  rw [form, Family.sum_pi_two, Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.smul_apply, gellMannUnitVec,
      ite_true, smul_eq_mul, mul_one]
  · intro y _ hy
    simp [gellMannUnitVec, hy]
  · simp
  · intro x _ hx
    simp [gellMannUnitVec, hx]
  · simp

variable {c : (Fin 2 → Fin 8) → ℂ}
  (hc : ∀ U : specialUnitaryGroup (Fin 3) ℂ, coeffMatrix U *ᵥ c = c)
include hc

/-- The form of an invariant coefficient is fixed by every complex adjoint matrix: the
  adjoint matrix acting on both arguments is the coefficient matrix acting on their product,
  and the transpose of the coefficient matrix of `U` is that of `U⁻¹`. -/
lemma form_mulVec (U : specialUnitaryGroup (Fin 3) ℂ) (v w : Fin 8 → ℂ) :
    form c (su3AdjointCoeffMatrix U *ᵥ v) (su3AdjointCoeffMatrix U *ᵥ w) = form c v w := by
  have key : ∀ l : Fin 2 → Fin 8,
      (su3AdjointCoeffMatrix U *ᵥ v) (l 0) * (su3AdjointCoeffMatrix U *ᵥ w) (l 1)
        = (coeffMatrix U *ᵥ fun m => v (m 0) * w (m 1)) l := by
    intro l
    simp only [mulVec, dotProduct, coeffMatrix, Family.powMatrix, of_apply, Fin.prod_univ_two]
    rw [Family.sum_pi_two, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  simp only [form, key]
  change (coeffMatrix U *ᵥ fun m => v (m 0) * w (m 1)) ⬝ᵥ c
    = (fun m => v (m 0) * w (m 1)) ⬝ᵥ c
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, coeffMatrix_transpose, hc,
    dotProduct_comm]

/-- The invariance equation on two Gell-Mann directions, for a rotation carrying each to a
  multiple of a Gell-Mann direction. -/
lemma entry_eq_of_mulVec {U : specialUnitaryGroup (Fin 3) ℂ} {a a' b b' : Fin 8} (s t : ℂ)
    (ha : su3AdjointCoeffMatrix U *ᵥ gellMannUnitVec a = s • gellMannUnitVec a')
    (hb : su3AdjointCoeffMatrix U *ᵥ gellMannUnitVec b = t • gellMannUnitVec b') :
    c ![a, b] = s * t * c ![a', b'] := by
  have h := form_mulVec hc U (gellMannUnitVec a) (gellMannUnitVec b)
  rw [ha, hb, form_smul_gellMannUnitVec, ← one_smul ℂ (gellMannUnitVec a),
    ← one_smul ℂ (gellMannUnitVec b), form_smul_gellMannUnitVec, one_mul, one_mul] at h
  exact h.symm

/-- The invariance equation of the cyclic rotation, read off `su3PermCol`. -/
lemma perm_entry_eq (a b a' b' : Fin 8) (s t : ℂ)
    (ha : su3PermCol a = s • gellMannUnitVec a') (hb : su3PermCol b = t • gellMannUnitVec b') :
    c ![a, b] = s * t * c ![a', b'] :=
  entry_eq_of_mulVec hc s t (by rw [su3Perm_mulVec_gellMannUnitVec, ha])
    (by rw [su3Perm_mulVec_gellMannUnitVec, hb])

/-- Every off-diagonal entry vanishes. -/
lemma eq_zero_of_ne {a b : Fin 8} (hab : a ≠ b) : c ![a, b] = 0 := by
  -- an entry joining two directions of different sign pattern is its own negative
  have hpar : ∀ {a b : Fin 8} (k : Fin 3),
      su3ParitySign k a ≠ su3ParitySign k b → c ![a, b] = 0 := by
    intro a b k hk
    have h := entry_eq_of_mulVec hc _ _ (su3Parity_mulVec_gellMannUnitVec k a)
      (su3Parity_mulVec_gellMannUnitVec k b)
    have hs : ∀ (k : Fin 3) (a b : Fin 8),
        su3ParitySign k a ≠ su3ParitySign k b → su3ParitySign k a * su3ParitySign k b = -1 := by
      decide
    rw [← Int.cast_mul, hs k a b hk] at h
    push_cast at h
    linear_combination (1 / 2 : ℂ) * h
  -- the turn carries the first root pair and the Cartan pair onto pairs a parity separates
  obtain ⟨h0, h1, h2, h7⟩ := su3Turn_mulVec_gellMannUnitVec
  have h01 : c ![0, 1] = 0 := by
    rw [entry_eq_of_mulVec hc _ _ h0 h1, hpar (a := 1) (b := 2) 0 (by decide), mul_zero]
  have h10 : c ![1, 0] = 0 := by
    rw [entry_eq_of_mulVec hc _ _ h1 h0, hpar (a := 2) (b := 1) 0 (by decide), mul_zero]
  have h27 : c ![2, 7] = 0 := by
    rw [entry_eq_of_mulVec hc _ _ h2 h7, hpar (a := 0) (b := 7) 0 (by decide), mul_zero]
  have h72 : c ![7, 2] = 0 := by
    rw [entry_eq_of_mulVec hc _ _ h7 h2, hpar (a := 7) (b := 0) 0 (by decide), mul_zero]
  -- the cyclic rotation carries each root pair onto the previous one
  have h34 : c ![3, 4] = 0 := by
    rw [perm_entry_eq hc 3 4 0 1 1 (-1) (by simp [su3PermCol]) (by simp [su3PermCol]),
      h01, mul_zero]
  have h43 : c ![4, 3] = 0 := by
    rw [perm_entry_eq hc 4 3 1 0 (-1) 1 (by simp [su3PermCol]) (by simp [su3PermCol]),
      h10, mul_zero]
  have h56 : c ![5, 6] = 0 := by
    rw [perm_entry_eq hc 5 6 3 4 1 (-1) (by simp [su3PermCol]) (by simp [su3PermCol]),
      h34, mul_zero]
  have h65 : c ![6, 5] = 0 := by
    rw [perm_entry_eq hc 6 5 4 3 (-1) 1 (by simp [su3PermCol]) (by simp [su3PermCol]),
      h43, mul_zero]
  -- every other pair of distinct directions is separated by a parity
  have key : ∀ a b : Fin 8, a ≠ b → (∃ k, su3ParitySign k a ≠ su3ParitySign k b)
      ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 2 ∧ b = 7) ∨ (a = 7 ∧ b = 2)
      ∨ (a = 3 ∧ b = 4) ∨ (a = 4 ∧ b = 3) ∨ (a = 5 ∧ b = 6) ∨ (a = 6 ∧ b = 5) := by
    decide
  rcases key a b hab with ⟨k, hk⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hpar k hk
  all_goals assumption

/-- Every diagonal entry equals the entry at the first Cartan direction. -/
lemma diag_eq (a : Fin 8) : c ![a, a] = c ![2, 2] := by
  -- the turn cycles `λ₁, λ₂, λ₃`, and the cyclic rotation moves the root directions around
  obtain ⟨h0, h1, -, -⟩ := su3Turn_mulVec_gellMannUnitVec
  have h01 : c ![0, 0] = c ![1, 1] := by rw [entry_eq_of_mulVec hc _ _ h0 h0]; ring
  have h12 : c ![1, 1] = c ![2, 2] := by rw [entry_eq_of_mulVec hc _ _ h1 h1]; ring
  have h05 : c ![0, 0] = c ![5, 5] := by
    rw [perm_entry_eq hc 0 0 5 5 1 1 (by simp [su3PermCol]) (by simp [su3PermCol])]; ring
  have h16 : c ![1, 1] = c ![6, 6] := by
    rw [perm_entry_eq hc 1 1 6 6 1 1 (by simp [su3PermCol]) (by simp [su3PermCol])]; ring
  have h53 : c ![5, 5] = c ![3, 3] := by
    rw [perm_entry_eq hc 5 5 3 3 1 1 (by simp [su3PermCol]) (by simp [su3PermCol])]; ring
  have h64 : c ![6, 6] = c ![4, 4] := by
    rw [perm_entry_eq hc 6 6 4 4 (-1) (-1) (by simp [su3PermCol]) (by simp [su3PermCol])]; ring
  -- the Cartan plane is rotated through `2π/3`, and its off-diagonal entries vanish
  have h77 : c ![7, 7] = c ![2, 2] := by
    have h := form_mulVec hc su3Perm (gellMannUnitVec 2) (gellMannUnitVec 2)
    rw [su3Perm_mulVec_gellMannUnitVec, ← one_smul ℂ (gellMannUnitVec 2),
      form_smul_gellMannUnitVec] at h
    simp only [form, su3PermCol, Family.sum_pi_two, Fin.sum_univ_eight, Matrix.cons_val_zero,
      Matrix.cons_val_one, Pi.add_apply, Pi.smul_apply, gellMannUnitVec, smul_eq_mul] at h
    simp only [Fin.isValue, Fin.reduceEq, ite_true, ite_false, mul_one, mul_zero, add_zero,
      zero_add, eq_zero_of_ne hc (show (2 : Fin 8) ≠ 7 by decide),
      eq_zero_of_ne hc (show (7 : Fin 8) ≠ 2 by decide), one_mul] at h
    have hsqrt : (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) = 3 := by
      exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    linear_combination (4 / 3 : ℂ) * h - (c ![7, 7] / 3) * hsqrt
  have key : ∀ a : Fin 8, a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 := by
    decide
  rcases key a with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h01, h12]
  · exact h12
  · rfl
  · rw [← h53, ← h05, h01, h12]
  · rw [← h64, ← h16, h12]
  · rw [← h05, h01, h12]
  · rw [← h16, h12]
  · exact h77

/-- A coefficient vector fixed by every coefficient matrix is a multiple of the Kronecker
  delta. -/
lemma exists_eq_smul_deltaCoeff_of_forall_mulVec_eq : ∃ z : ℂ, c = z • Family.deltaCoeff := by
  refine ⟨c ![2, 2], funext fun l => ?_⟩
  obtain ⟨a, b, rfl⟩ : ∃ a b, l = ![a, b] := ⟨l 0, l 1, by ext i; fin_cases i <;> rfl⟩
  by_cases h : a = b
  · subst h
    simp [Family.deltaCoeff, diag_eq hc]
  · simp [Family.deltaCoeff, h, eq_zero_of_ne hc h]

omit hc

/-!

## D. The reduction modulo a stable submodule

`reducesInvariantsTo_span_singleton_of_mulVec_eq` applies section C in every quotient by a
stable submodule. In the gauge form the law constrains only the colour factor, so the
invariance of the trace contraction under the whole gauge group is a hypothesis.

-/

/-- For any family of maps `σ U` obeying the law, a `σ`-invariant of the span joined with a
  `σ`-stable submodule `S` is a multiple of the trace contraction plus an element of `S`. -/
lemma reducesInvariantsTo_span_traceContraction
    (σ : specialUnitaryGroup (Fin 3) ℂ → B →ₗ[ℂ] B) (hT : ∀ U, IsSU3BiAdjointMat U (σ U) T) :
    ReducesInvariantsTo σ (Submodule.span ℂ (Set.range T)) (ℂ ∙ traceContraction T) := by
  have h := reducesInvariantsTo_span_singleton_of_mulVec_eq (σ := σ) T coeffMatrix hT
    (fun U => ⟨U⁻¹, coeffMatrix_inv U⟩) Family.deltaCoeff fun _ hc =>
      exists_eq_smul_deltaCoeff_of_forall_mulVec_eq hc
  rwa [Family.sum_deltaCoeff_smul] at h

/-- A gauge invariant of the span joined with a gauge-stable submodule is a multiple of the
  trace contraction plus a gauge-invariant remainder, once the trace contraction is known to
  be gauge invariant. -/
lemma exists_smul_add_of_gauge_invariant (hT : IsSU3BiAdjoint B repGauge T) (x : B)
    (S : Submodule ℂ B) (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (htc : ∀ g : GaugeGroupI, repGauge g (traceContraction T) = traceContraction T)
    (hx : x ∈ Submodule.span ℂ (Set.range T) ⊔ S) (hinv : ∀ g : GaugeGroupI, repGauge g x = x) :
    ∃ c : ℂ, ∃ y ∈ S, x = c • traceContraction T + y
      ∧ ∀ g : GaugeGroupI, repGauge g y = y := by
  obtain ⟨w, hw, y, hy, rfl, hyinv⟩ := (isFixedBy_span_singleton htc).exists_add_of_mem_sup
    ((reducesInvariantsTo_span_traceContraction _ hT.repGauge_T).comp
      (σ := fun g => repGauge g) (fun U => (U, 1, 1)) S hS x hx hinv) hinv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
  exact ⟨c, y, hy, rfl, hyinv⟩

end IsSU3BiAdjoint

end StandardModel
