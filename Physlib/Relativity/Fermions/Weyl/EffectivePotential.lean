/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Fermions.Weyl.Metric
public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
/-!

# The effective potential of Weyl fermions

## i. Overview

In this file are primary objective is to look at the potential
of a single left-handed Weyl fermion, correctly taking account
of the anti-commuting nature of the fermion.

Two facts about the (effective) potential, which we take as a given, are that:
1. It is written in terms of the components of the left-handed Weyl fermion and its conjugate.
2. Within the potential the components anti-commute.
The first of these, tells us that we should be working with the dual of the left-handed Weyl fermion
and its conjugate (since the duals are the linear functionals which pick
out the components of the fermion). The second of these tells us that we should be working with an
exterior algebra.

Thus, the type in which the potential lives is
`ExteriorAlgebra ℂ (DualLeftHandedWeyl × DualRightHandedWeyl)`. We call this type
`EffectivePotential` and define it and its properties in this file.

On `PotentialAlgebra` we define a representation of the Lorentz group, and prove that that
if the potential is invariant under the Lorentz group it must be of the form
`c + m1 * ψ 0 * ψ 1 + m2 * barψ 0 * barψ 1 + λ * ψ 0 * ψ 1 * barψ 0 * barψ 1`,
which is true to all orders.

There is as of yet no reality condition on this potential. This is a TODO.

-/

@[expose] public section

namespace Fermion
noncomputable section

open Module Matrix
open MatrixGroups
open Complex
open TensorProduct
open CategoryTheory.MonoidalCategory

/-!

## A. The Potential algebra for Weyl fermions

-/

/-- The type corresponding to the effective potential of a
  left-handed Weyl fermion. -/
abbrev EffectivePotential : Type := ExteriorAlgebra ℂ (DualLeftHandedWeyl × DualRightHandedWeyl)

namespace EffectivePotential

/-!

### A.1. The coordinate elements of the potential algebra

-/

/-- The coordinate element corresponding to the i-th basis vector as a member
  of the effective potential. -/
def ψ (i : Fin 2) : EffectivePotential :=
  (ExteriorAlgebra.ι ℂ) (LinearMap.inl ℂ _ _ (DualLeftHandedWeyl.basis i))

/-- The coordinate element corresponding to the conjugate i-th basis vector as a member
  of the effective potential. -/
def barψ (i : Fin 2) : EffectivePotential :=
  (ExteriorAlgebra.ι ℂ) (LinearMap.inr ℂ _ _ (DualRightHandedWeyl.basis i))

@[simp] lemma ψ_mul_self (i : Fin 2) : ψ i * ψ i = 0 := ExteriorAlgebra.ι_sq_zero _

@[simp] lemma ψ_one_mul_ψ_zero_swap : ψ 1 * ψ 0 = - ψ 0 * ψ 1 := by
  rw [neg_mul, eq_neg_iff_add_eq_zero]
  exact ExteriorAlgebra.ι_add_mul_swap _ _

@[simp] lemma barψ_mul_self (i : Fin 2) : barψ i * barψ i = 0 := ExteriorAlgebra.ι_sq_zero _

@[simp] lemma barψ_one_mul_barψ_zero_swap : barψ 1 * barψ 0 = - barψ 0 * barψ 1 := by
  rw [neg_mul, eq_neg_iff_add_eq_zero]
  exact ExteriorAlgebra.ι_add_mul_swap _ _


/-!

### A.2. Basis

-/

/-- The basis of the effective potential. -/
def basis : Basis (Finset (Fin 4)) ℂ EffectivePotential :=
    Module.Basis.ExteriorAlgebra ((DualLeftHandedWeyl.basis.prod DualRightHandedWeyl.basis).reindex
      finSumFinEquiv)

/-!

## A.3. The representation on the potential algebra

-/

/-- The representation of the Lorentz group on `PotentialAlgebra`. -/
def rep : Representation ℂ SL(2, ℂ) EffectivePotential where
  toFun Λ := (ExteriorAlgebra.map ((DualLeftHandedWeyl.rep Λ).prodMap
    (DualRightHandedWeyl.rep Λ))).toLinearMap
  map_one' := by
    simp only [map_one, End.one_eq_id, LinearMap.prodMap_id, ExteriorAlgebra.map_id,
      AlgHom.toLinearMap_id]
  map_mul' Λ1 Λ2 := by
    simp only [map_mul, End.mul_eq_comp, ← LinearMap.prodMap_comp, ← ExteriorAlgebra.map_comp_map,
      AlgHom.comp_toLinearMap]

lemma rep_apply (Λ : SL(2, ℂ)) (V : EffectivePotential) :
    rep Λ V = ExteriorAlgebra.map ((DualLeftHandedWeyl.rep Λ).prodMap
      (DualRightHandedWeyl.rep Λ)) V := rfl

lemma rep_mul (Λ : SL(2, ℂ)) (V W : EffectivePotential) :
    rep Λ (V * W) = rep Λ V * rep Λ W:= by
  simp [rep]

lemma rep_apply_ψ_eq_sum (Λ : SL(2, ℂ)) (i : Fin 2) :
    rep Λ (ψ i) = ∑ j, Λ⁻¹ i j • ψ j := by
  simp [rep, ψ, DualLeftHandedWeyl.rep_apply_basis, ← map_smul, ← map_add,
    -SpecialLinearGroup.coe_inv, Lorentz.SL2C.inverse_coe]

lemma rep_apply_barψ_eq_sum (Λ : SL(2, ℂ)) (i : Fin 2) :
    rep Λ (barψ i) = ∑ j, star (Λ⁻¹ i j) • barψ j := by
  simp [rep, barψ, DualRightHandedWeyl.rep_apply_basis, ← map_smul, ← map_add,
    -SpecialLinearGroup.coe_inv, Lorentz.SL2C.inverse_coe]

/-!

## B. Invariance under the Lorentz group

-/


def IsInvariant (V : EffectivePotential) : Prop := ∀ Λ, rep Λ V = V

lemma IsInvariant.eq_iff {V : EffectivePotential} :
    IsInvariant V ↔ ∀ Λ, rep Λ V = V := by rfl

lemma IsInvariant.add {V W : EffectivePotential} (hV : IsInvariant V) (hW : IsInvariant W) :
    IsInvariant (V + W) := by
  intro Λ
  simp_all [IsInvariant.eq_iff]

lemma IsInvariant.smul {V : EffectivePotential} (hV : IsInvariant V) (c : ℂ) :
    IsInvariant (c • V) := by
  intro Λ
  simp_all [IsInvariant.eq_iff]

lemma IsInvariant.mul {V W : EffectivePotential} (hV : IsInvariant V) (hW : IsInvariant W) :
    IsInvariant (V * W) := by
  intro Λ
  simp_all [IsInvariant.eq_iff, rep_mul]

lemma IsInvariant.one : IsInvariant 1 := by
  intro Λ
  simp [rep]

/-!

## B.1. Specific terms which are invariant

-/

lemma ψ_zero_mul_ψ_one_isInvariant : IsInvariant (ψ 0 * ψ 1) := by
  intro Λ
  simp [rep_mul, rep_apply_ψ_eq_sum, mul_add, add_mul]
  trans (Λ.1.adjugate 1 1 • Λ.1.adjugate 0 0 - Λ.1.adjugate 1 0 • Λ.1.adjugate 0 1) • (ψ 0 * ψ 1)
  · module
  simp only [Fin.isValue, adjugate_fin_two, of_apply, cons_val', cons_val_one, cons_val_fin_one,
    cons_val_zero, smul_eq_mul, mul_neg, neg_mul, neg_neg]
  trans Λ.1.det • (ψ 0 * ψ 1)
  · congr
    simp only [Matrix.det_fin_two]
    ring
  · simp

lemma barψ_zero_mul_barψ_one_isInvariant : IsInvariant (barψ 0 * barψ 1) := by
  intro Λ
  simp [rep_mul, rep_apply_barψ_eq_sum, mul_add, add_mul, adjugate_fin_two, smul_smul,
    ← add_smul, ← neg_smul, ← map_mul, ← map_neg, ← map_add]
  trans (starRingEnd ℂ)  Λ.1.det • (barψ 0 * barψ 1)
  · simp only [Matrix.det_fin_two]
    ring_nf
  · simp

lemma quartic_isInvariant : IsInvariant (ψ 0 * ψ 1 * barψ 0 * barψ 1) := by
  intro Λ
  simp [rep_mul, rep_apply_barψ_eq_sum, rep_apply_barψ_eq_sum, mul_add, add_mul, adjugate_fin_two,
    smul_smul, ← add_smul, ← neg_smul, ← map_mul, ← map_neg, ← map_add, mul_assoc]
  trans (starRingEnd ℂ)  Λ.1.det • ((rep Λ) (ψ 0) * ((rep Λ) (ψ 1) * (barψ 0 * barψ 1)))
  · simp only [Matrix.det_fin_two]
    ring_nf
  simp [rep_apply_ψ_eq_sum, mul_add, add_mul, ← mul_assoc, mul_add, add_mul,
    adjugate_fin_two, smul_smul, ← add_smul, ← neg_smul]
  trans Λ.1.det • (ψ 0 * ψ 1 * barψ 0 * barψ 1)
  · simp only [Matrix.det_fin_two]
    ring_nf
  · simp

/-!

## B.2. Terms which must be zero in an invariant potential

-/
/-- If `V` is invariant, then all terms with an odd number of factors vanish. -/
lemma even_of_isInvariant {V : EffectivePotential} {s : Finset (Fin 4)} (h : IsInvariant V)
    (hs : Odd s.card) : basis.repr V s = 0 := by
  suffices h : basis.repr V s = (-1 : ℂ) ^ s.card * basis.repr V s by
    simpa [hs.neg_one_pow, CharZero.eq_neg_self_iff] using h
  let Λ := (-1 : SL(2, ℂ))
  suffices Λ_basis : ∀ (t : Finset (Fin 4)), rep Λ (basis t) = (-1 : ℂ) ^ t.card • basis t by
    conv_lhs => rw [← h Λ, ← basis.sum_repr V, map_sum]
    simp [Λ_basis, Finsupp.single_apply, smul_smul, mul_comm]
  intro t
  have hF : (DualLeftHandedWeyl.rep Λ).prodMap (DualRightHandedWeyl.rep Λ)
      = -LinearMap.id := by
    have hinv : (-(1 : Matrix (Fin 2) (Fin 2) ℂ))⁻¹ = -1 := Matrix.inv_eq_left_inv (by simp)
    refine (DualLeftHandedWeyl.basis.prod DualRightHandedWeyl.basis).ext fun i => ?_
    rcases i with i | i <;> fin_cases i <;>
      simp [DualLeftHandedWeyl.rep_apply_basis, DualRightHandedWeyl.rep_apply_basis, Λ, hinv]
  have hmap (n : ℕ) (g : Fin n → DualLeftHandedWeyl × DualRightHandedWeyl) :
      ExteriorAlgebra.ιMulti ℂ n (-g) = (-1 : ℂ) ^ n • ExteriorAlgebra.ιMulti ℂ n g := by
    rw [show -g = fun i => (-1 : ℂ) • g i from funext fun i => by simp,
      AlternatingMap.map_smul_univ]
    simp
  rw [basis, ExteriorAlgebra.basis_apply_ofCard (s_card := rfl), rep_apply]
  simp only [ExteriorAlgebra.ιMulti_family]
  rw [ExteriorAlgebra.map_apply_ιMulti, hF]
  exact hmap _ _

/-- If `V` is invariant, then the mixed terms `ψ i * barψ j` have coefficient zero. -/
lemma zero_two_term_zero_of_isInvariant {V : EffectivePotential} (h : IsInvariant V) :
    basis.repr V {0, 2} = 0 ∧ basis.repr V {0, 3} = 0
    ∧ basis.repr V {1, 2} = 0 ∧ basis.repr V {1, 3} = 0 := by
  let Λ : SL(2, ℂ):= ⟨!![2 * I, 0; 0, -(I / 2)], by
    simp [Matrix.det_fin_two_of]; linear_combination -Complex.I_sq⟩
  let d : Fin 4 → ℂ := ![-(I / 2), 2 * I, I / 2, -(2 * I)]
  suffices Λ_basis : ∀ (t : Finset (Fin 4)), rep Λ (basis t) = (∏ k ∈ t, d k) • basis t by
    have hzero (a b : Fin 4) (hab : a ≠ b) (hd : d a * d b ≠ 1) :
        basis.repr V {a, b} = 0 := by
      have h1 : basis.repr V {a, b} = (d a * d b) * basis.repr V {a, b} := by
        conv_lhs => rw [← h Λ, ← basis.sum_repr V, map_sum]
        simp [Λ_basis, Finsupp.single_apply, smul_smul, mul_comm, Finset.prod_pair hab]
      by_contra hne
      exact hd (mul_right_cancel₀ hne (by linear_combination -h1))
    refine ⟨hzero 0 2 (by decide) ?_, hzero 0 3 (by decide) ?_,
      hzero 1 2 (by decide) ?_, hzero 1 3 (by decide) ?_⟩ <;>
      simp only [d, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    · rw [show -(I / 2) * (I / 2) = 1 / 4 from by linear_combination (-(1 : ℂ)/4) * Complex.I_sq]
      norm_num
    · rw [show -(I / 2) * -(2 * I) = -1 from by linear_combination Complex.I_sq]
      norm_num
    · rw [show 2 * I * (I / 2) = -1 from by linear_combination Complex.I_sq]
      norm_num
    · rw [show 2 * I * -(2 * I) = 4 from by linear_combination (-4 : ℂ) * Complex.I_sq]
      norm_num
  intro t
  have hinv : (!![2 * I, 0; 0, -(I / 2)])⁻¹ = !![-(I / 2), 0; 0, 2 * I] :=
    Matrix.inv_eq_left_inv (by ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linear_combination -Complex.I_sq)
  have hv (k : Fin 4) : ((DualLeftHandedWeyl.rep Λ).prodMap (DualRightHandedWeyl.rep Λ))
      (((DualLeftHandedWeyl.basis.prod DualRightHandedWeyl.basis).reindex finSumFinEquiv) k)
      = d k • ((DualLeftHandedWeyl.basis.prod DualRightHandedWeyl.basis).reindex
        finSumFinEquiv) k := by
    fin_cases k <;>
      simp [DualLeftHandedWeyl.rep_apply_basis, DualRightHandedWeyl.rep_apply_basis, Λ, d, hinv,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Complex.conj_ofNat, neg_div,
        show (finSumFinEquiv (m := 2) (n := 2)).symm 0 = Sum.inl 0 from rfl,
        show (finSumFinEquiv (m := 2) (n := 2)).symm 1 = Sum.inl 1 from rfl,
        show (finSumFinEquiv (m := 2) (n := 2)).symm 2 = Sum.inr 0 from rfl,
        show (finSumFinEquiv (m := 2) (n := 2)).symm 3 = Sum.inr 1 from rfl]
  have hmap (n : ℕ) (c : Fin n → ℂ) (g : Fin n → DualLeftHandedWeyl × DualRightHandedWeyl)
      (hcg : ∀ i, ((DualLeftHandedWeyl.rep Λ).prodMap (DualRightHandedWeyl.rep Λ)) (g i)
        = c i • g i) :
      ExteriorAlgebra.map ((DualLeftHandedWeyl.rep Λ).prodMap (DualRightHandedWeyl.rep Λ))
        (ExteriorAlgebra.ιMulti ℂ n g) = (∏ i, c i) • ExteriorAlgebra.ιMulti ℂ n g := by
    rw [ExteriorAlgebra.map_apply_ιMulti, show ⇑((DualLeftHandedWeyl.rep Λ).prodMap
        (DualRightHandedWeyl.rep Λ)) ∘ g = fun i => c i • g i from funext fun i => hcg i,
      AlternatingMap.map_smul_univ]
  rw [basis, ExteriorAlgebra.basis_apply_ofCard (s_card := rfl), rep_apply]
  simp only [ExteriorAlgebra.ιMulti_family, Set.powersetCard.ofFinEmbEquiv_symm_apply]
  refine (hmap _ _ _ fun i => hv _).trans ?_
  congr 1
  rw [← Finset.prod_coe_sort t d]
  exact Fintype.prod_equiv (t.orderIsoOfFin rfl).toEquiv _ _ fun i => by
    simp [Finset.coe_orderIsoOfFin_apply]

lemma isInvariant_iff {V : EffectivePotential} :
    IsInvariant V ↔ ∃ (c m1 m2 ρ : ℂ), V = c • 1 + m1 • (ψ 0 * ψ 1) + m2 • (barψ 0 * barψ 1) +
      ρ • (ψ 0 * ψ 1 * barψ 0 * barψ 1) := by
  constructor
  · intro h
    rw [← basis.sum_repr V]
    refine ⟨basis.repr V ∅, basis.repr V {0, 1}, basis.repr V {2, 3}, basis.repr V {0, 1, 2, 3}, ?_⟩
    rw [show (Finset.univ : Finset (Finset (Fin 4))) =
      {∅, {0}, {1}, {2}, {3}, {0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3},
        {0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}, {0, 1, 2, 3}} by decide]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    rw [even_of_isInvariant (s := {0}) h (by decide), even_of_isInvariant (s := {1}) h (by decide),
      even_of_isInvariant (s := {2}) h (by decide), even_of_isInvariant (s := {3}) h (by decide),
      even_of_isInvariant (s := {0, 1, 2}) h (by decide),
      even_of_isInvariant (s := {0, 1, 3}) h (by decide),
      even_of_isInvariant (s := {0, 2, 3}) h (by decide),
      even_of_isInvariant (s := {1, 2, 3}) h (by decide),
      (zero_two_term_zero_of_isInvariant h).1, (zero_two_term_zero_of_isInvariant h).2.1,
      (zero_two_term_zero_of_isInvariant h).2.2.1, (zero_two_term_zero_of_isInvariant h).2.2.2]
    simp [add_assoc]
    congr
    all_goals
      rw [basis, ExteriorAlgebra.basis_apply];
      simp [ExteriorAlgebra.ιMulti_apply,
        Set.powersetCard.ofFinEmbEquiv_symm_apply, Finset.orderEmbOfFin_apply, Finset.sort_insert,
        ψ, barψ, mul_assoc];
      try rfl
  · rintro ⟨c, m1, m2, ρ, rfl⟩
    apply_rules [IsInvariant.add, IsInvariant.smul,  IsInvariant.one,
      ψ_zero_mul_ψ_one_isInvariant, barψ_zero_mul_barψ_one_isInvariant, quartic_isInvariant]

end EffectivePotential

end
end Fermion
