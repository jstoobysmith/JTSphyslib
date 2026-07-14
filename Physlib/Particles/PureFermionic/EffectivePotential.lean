/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Fermions.Weyl.Metric
public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Physlib.Mathematics.ConjModule
/-!

# The effective potential for a left-handed Weyl fermion

## i. Overview

In this file our primary objective is to look at the potential
of a single left-handed Weyl fermion, correctly taking account
of the anti-commuting nature of the fermion.

Two facts about the (effective) potential, which we take as a given, are that:
1. It is written in terms of the components of the left-handed Weyl fermion and its conjugate.
  (For this effective potential, we do not consider derivatives.)
2. Within the potential the components anti-commute.
The first of these, tells us that we should be working with the dual of the left-handed Weyl fermion
and its conjugate (since the duals are the linear functionals which pick
out the components of the fermion). The second of these tells us that we should be working with an
exterior algebra.

Thus, the type in which the potential lives is
`ExteriorAlgebra ℂ (Module.Dual ℂ LeftHandedWeyl × Module.Dual ℂ (ConjModule LeftHandedWeyl))`.
We call this type `EffectivePotential` and define it and its properties in this file.
Note that  `Module.Dual ℂ LeftHandedWeyl` is equivalent to `DualLeftHandedWeyl` and
`Module.Dual ℂ (ConjModule LeftHandedWeyl)` is equivalent to `DualRightHandedWeyl`,
so we could equivalently define the effective potential as
`ExteriorAlgebra ℂ (DualLeftHandedWeyl × DualRightHandedWeyl)`. We have done the
former here as it generalises to other cases.

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
abbrev EffectivePotential : Type := ExteriorAlgebra ℂ
  (Module.Dual ℂ LeftHandedWeyl × Module.Dual ℂ (ConjModule LeftHandedWeyl))

namespace EffectivePotential

/-!

### A.1. The coordinate elements of the potential algebra

-/

/-- The coordinate element corresponding to the i-th basis vector as a member
  of the effective potential. -/
def ψ (α : Fin 2) : EffectivePotential :=
  (ExteriorAlgebra.ι ℂ) (LinearMap.inl ℂ _ _ (LeftHandedWeyl.basis.dualBasis α))

/-- The coordinate element corresponding to the conjugate i-th basis vector as a member
  of the effective potential. -/
def barψ (α : Fin 2) : EffectivePotential :=
  (ExteriorAlgebra.ι ℂ) (LinearMap.inr ℂ _ _ (LeftHandedWeyl.basis.conj.dualBasis α))

@[simp] lemma ψ_mul_self (α : Fin 2) : ψ α * ψ α = 0 := ExteriorAlgebra.ι_sq_zero _

@[simp] lemma ψ_one_mul_ψ_zero_swap : ψ 1 * ψ 0 = - ψ 0 * ψ 1 := by
  rw [neg_mul, eq_neg_iff_add_eq_zero]
  exact ExteriorAlgebra.ι_add_mul_swap _ _

@[simp] lemma barψ_mul_self (α : Fin 2) : barψ α * barψ α = 0 := ExteriorAlgebra.ι_sq_zero _

@[simp] lemma barψ_one_mul_barψ_zero_swap : barψ 1 * barψ 0 = - barψ 0 * barψ 1 := by
  rw [neg_mul, eq_neg_iff_add_eq_zero]
  exact ExteriorAlgebra.ι_add_mul_swap _ _

@[simp]
lemma append_apply_zero_eq : Fin.append ψ barψ 0 = ψ 0 := rfl

@[simp]
lemma append_apply_one_eq : Fin.append ψ barψ 1 = ψ 1 := rfl

@[simp]
lemma append_apply_two_eq : Fin.append ψ barψ 2 = barψ 0 := rfl

@[simp]
lemma append_apply_three_eq : Fin.append ψ barψ 3 = barψ 1 := rfl

/-!

### A.2. Of a list
-/

/-- The term of the effective potential generated from a list
  of `Fin 4`, which describe the components `[ψ 0, ψ 1, barψ 0, barψ 1]`. -/
def termOfList (l : List (Fin 4)) : EffectivePotential :=
  (l.map (Fin.append ψ barψ)).prod

@[simp]
lemma termOfList_nil : termOfList [] = 1 := by simp [termOfList]

lemma termOfList_cons (l : List (Fin 4)) (α : Fin 4) :
    termOfList (α :: l) = (Fin.append ψ barψ α) * termOfList l := by
  simp only [termOfList, List.map_cons, List.prod_cons]

/-!

### A.3. Basis

-/

/-- The basis of the effective potential. -/
def basis : Basis (Finset (Fin 4)) ℂ EffectivePotential :=
    Module.Basis.ExteriorAlgebra ((LeftHandedWeyl.basis.dualBasis.prod
    LeftHandedWeyl.basis.conj.dualBasis).reindex finSumFinEquiv)

lemma basis_eq_termOfList (s : Finset (Fin 4)) : basis s = termOfList (s.sort (· ≤ ·)) := by
  have happend : Fin.append ψ barψ = fun j => (ExteriorAlgebra.ι ℂ)
      (((LeftHandedWeyl.basis.dualBasis.prod LeftHandedWeyl.basis.conj.dualBasis).reindex
        finSumFinEquiv) j) := by
    funext j
    fin_cases j <;>
      simp [ψ, barψ, Fin.append, Fin.addCases, Basis.prod_apply,
        show (finSumFinEquiv (m := 2) (n := 2)).symm 0 = Sum.inl 0 from rfl,
        show (finSumFinEquiv (m := 2) (n := 2)).symm 1 = Sum.inl 1 from rfl,
        show (finSumFinEquiv (m := 2) (n := 2)).symm 2 = Sum.inr 0 from rfl,
        show (finSumFinEquiv (m := 2) (n := 2)).symm 3 = Sum.inr 1 from rfl]
  rw [basis, ExteriorAlgebra.basis_apply_ofCard (s_card := rfl), termOfList, happend]
  simp only [ExteriorAlgebra.ιMulti_family, Set.powersetCard.ofFinEmbEquiv_symm_apply,
    ExteriorAlgebra.ιMulti_apply]
  refine congrArg List.prod (List.ext_getElem (by simp) fun i h1 h2 => ?_)
  simp [Finset.orderEmbOfFin_apply]

/-!

### A.4. The representation on the potential algebra

-/

/-- The representation of the Lorentz group on `PotentialAlgebra`. -/
def rep : Representation ℂ SL(2, ℂ) EffectivePotential where
  toFun Λ := (ExteriorAlgebra.map ((LeftHandedWeyl.rep.dual Λ).prodMap
    (LeftHandedWeyl.rep.conj.dual Λ))).toLinearMap
  map_one' := by
    simp only [map_one, End.one_eq_id, LinearMap.prodMap_id, ExteriorAlgebra.map_id,
      AlgHom.toLinearMap_id]
  map_mul' Λ1 Λ2 := by
    simp only [map_mul, End.mul_eq_comp, ← LinearMap.prodMap_comp, ← ExteriorAlgebra.map_comp_map,
      AlgHom.comp_toLinearMap]

lemma rep_apply (Λ : SL(2, ℂ)) (V : EffectivePotential) :
    rep Λ V = ExteriorAlgebra.map ((LeftHandedWeyl.rep.dual Λ).prodMap
      (LeftHandedWeyl.rep.conj.dual Λ)) V := rfl

@[simp]
lemma rep_apply_one (Λ : SL(2, ℂ)) : rep Λ 1 = 1 := by
  simp [rep_apply]

lemma rep_mul (Λ : SL(2, ℂ)) (V W : EffectivePotential) :
    rep Λ (V * W) = rep Λ V * rep Λ W:= by
  simp [rep]

lemma rep_apply_ψ_eq_sum (Λ : SL(2, ℂ)) (i : Fin 2) :
    rep Λ (ψ i) = ∑ (j : Fin 2), Λ⁻¹ i j • ψ j := by
  simp only [ψ, Basis.coe_dualBasis, LinearMap.coe_inl, rep_apply, Representation.dual_apply,
    ExteriorAlgebra.map_apply_ι, LinearMap.prodMap_apply, map_zero, ← map_smul, Prod.smul_mk,
    smul_zero, Fin.sum_univ_two, Fin.isValue, ← map_add, Prod.mk_add_mk, add_zero,
    ExteriorAlgebra.ι_inj, Prod.mk.injEq, and_true]
  refine LeftHandedWeyl.basis.ext fun l => ?_
  fin_cases i <;> fin_cases l <;>
    simp [Module.Dual.transpose_apply, LeftHandedWeyl.rep_apply_basis,
      -SpecialLinearGroup.coe_inv]

lemma rep_apply_barψ_eq_sum (Λ : SL(2, ℂ)) (α : Fin 2) :
    rep Λ (barψ α) = ∑ β, star (Λ⁻¹ α β) • barψ β := by
  simp only [barψ, Basis.coe_dualBasis, LinearMap.coe_inr, rep_apply, Representation.dual_apply,
    ExteriorAlgebra.map_apply_ι, LinearMap.prodMap_apply, map_zero, RCLike.star_def, ← map_smul,
    Prod.smul_mk, smul_zero, Fin.sum_univ_two, Fin.isValue, ← map_add, Prod.mk_add_mk, add_zero,
    ExteriorAlgebra.ι_inj, Prod.mk.injEq, true_and]
  refine LeftHandedWeyl.basis.conj.ext fun l => ?_
  fin_cases α <;> fin_cases l <;>
    simp [Module.Dual.transpose_apply, LeftHandedWeyl.rep_apply_basis,
      -SpecialLinearGroup.coe_inv, Representation.conj_apply]

lemma rep_termOfList_eq_map_rep (Λ : SL(2, ℂ)) (l : List (Fin 4)) :
    rep Λ (termOfList l) = ((l.map (Fin.append ψ barψ)).map (rep Λ)).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp [termOfList_cons, rep_mul, ih]

lemma rep_neg_apply_append (Λ : SL(2, ℂ)) (α : Fin 4) :
    rep (- Λ) (Fin.append ψ barψ α) = (-1 : ℂ) • rep Λ (Fin.append ψ barψ α) := by
  fin_cases α
  all_goals
    simp [rep_apply_ψ_eq_sum, rep_apply_barψ_eq_sum]
    abel

lemma rep_neg_apply_termOfList (Λ : SL(2, ℂ)) (l : List (Fin 4)) :
    rep (- Λ) (termOfList l) = ((-1 : ℂ) ^ l.length) • rep Λ (termOfList l) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp [termOfList_cons, rep_mul, ih, rep_neg_apply_append, pow_succ' (-1 : ℂ) l.length]

lemma rep_neg_apply_basis (s : Finset (Fin 4))  (Λ : SL(2, ℂ)) :
    rep (- Λ) (basis s) = (-1 : ℂ) ^ s.card • rep Λ (basis s) := by
  simp [basis_eq_termOfList, rep_neg_apply_termOfList]

/-!

## B. Invariance under the Lorentz group

-/

/-- An effective potential is Lorentz invariant if it is stable under the
    action of the Lorentz group. -/
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
lemma even_of_isInvariant {V : EffectivePotential} (s : Finset (Fin 4)) (h : IsInvariant V)
    (hs : Odd s.card) : basis.repr V s = 0 := by
  suffices h : basis.repr V s = (-1 : ℂ) ^ s.card * basis.repr V s by
    simpa [hs.neg_one_pow, CharZero.eq_neg_self_iff] using h
  suffices Λ_basis : ∀ (t : Finset (Fin 4)), rep (-1 : SL(2, ℂ)) (basis t) =
      (-1 : ℂ) ^ t.card • basis t by
    conv_lhs => rw [← h (-1 : SL(2, ℂ)), ← basis.sum_repr V, map_sum]
    simp [Λ_basis, Finsupp.single_apply, smul_smul, mul_comm]
  simp [rep_neg_apply_basis]

/-- If `V` is invariant, then the mixed terms `ψ i * barψ j` have coefficient zero. -/
lemma zero_two_term_zero_of_isInvariant {V : EffectivePotential} (h : IsInvariant V) :
    basis.repr V {0, 2} = 0 ∧ basis.repr V {0, 3} = 0
    ∧ basis.repr V {1, 2} = 0 ∧ basis.repr V {1, 3} = 0 := by
  let Λ : SL(2, ℂ):= ⟨!![2 * I, 0; 0, -(I / 2)], by
    simp [Matrix.det_fin_two_of]; linear_combination -Complex.I_sq⟩
  let d : Fin 4 → ℂ := ![-(I / 2), 2 * I, I / 2, -(2 * I)]
  suffices Λ_basis_two : ∀ (a b : Fin 4) (hab : a ≠ b) (hd : d a * d b ≠ 1),
        basis.repr V {a, b} = 0 by
    refine ⟨Λ_basis_two 0 2 (by decide) ?_, Λ_basis_two 0 3 (by decide) ?_,
      Λ_basis_two 1 2 (by decide) ?_, Λ_basis_two 1 3 (by decide) ?_⟩
    all_goals
      simp [d]
      ring_nf
      simp
      try grind
  suffices Λ_basis : ∀ (t : Finset (Fin 4)), rep Λ (basis t) = (∏ k ∈ t, d k) • basis t by
    intro a b hab hd
    have h1 : basis.repr V {a, b} = (d a * d b) * basis.repr V {a, b} := by
        conv_lhs => rw [← h Λ, ← basis.sum_repr V, map_sum]
        simp [Λ_basis, Finsupp.single_apply, smul_smul, mul_comm, Finset.prod_pair hab]
    by_contra hne
    exact hd (mul_right_cancel₀ hne (by linear_combination -h1))
  suffices Λ_termOfList : ∀ (l : List (Fin 4)),
      rep Λ (termOfList l) = (l.map d).prod • termOfList l by
    intro t
    rw [basis_eq_termOfList, Λ_termOfList, ← Finset.prod_map_toList t,
      ((Finset.sort_perm_toList t fun x1 x2 => x1 ≤ x2).map d).prod_eq]
  suffices Λ_append : ∀ (i : Fin 4), rep Λ (Fin.append ψ barψ i) = d i • Fin.append ψ barψ i by
    intro l
    induction l with
    | nil => simp
    | cons i l ih => simp [termOfList_cons, rep_mul, ih, Λ_append, smul_smul, mul_comm]
  intro i
  fin_cases i
  all_goals
    simp [rep_apply_ψ_eq_sum, rep_apply_barψ_eq_sum, d, adjugate_fin_two, Λ,
      neg_smul, Complex.conj_ofNat]
    try module

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
    rw [even_of_isInvariant {0} h (by decide), even_of_isInvariant {1} h (by decide),
      even_of_isInvariant {2} h (by decide), even_of_isInvariant {3} h (by decide),
      even_of_isInvariant {0, 1, 2} h (by decide), even_of_isInvariant {0, 1, 3} h (by decide),
      even_of_isInvariant {0, 2, 3} h (by decide), even_of_isInvariant {1, 2, 3} h (by decide),
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
