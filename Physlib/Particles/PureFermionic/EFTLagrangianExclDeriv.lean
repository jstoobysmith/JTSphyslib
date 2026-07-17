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
public import Mathlib.RingTheory.GradedAlgebra.Basic
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
We call this type `EFTLagrangianExclDeriv` and define it and its properties in this file.
Note that  `Module.Dual ℂ LeftHandedWeyl` is equivalent to `DualLeftHandedWeyl` and
`Module.Dual ℂ (ConjModule LeftHandedWeyl)` is equivalent to `DualRightHandedWeyl`,
so we could equivalently define the effective potential as
`ExteriorAlgebra ℂ (DualLeftHandedWeyl × DualRightHandedWeyl)`. We have done the
former here as it generalises to other cases.

On `EFTLagrangianExclDeriv` we define a representation of the Lorentz group, and prove that that
if the potential is invariant under the Lorentz group it must be of the form
`c + m1 * ψ 0 * ψ 1 + m2 * barψ 0 * barψ 1 + λ * ψ 0 * ψ 1 * barψ 0 * barψ 1`,
which is true to all orders.

## References

- https://physics.stackexchange.com/questions/506709 describes the mass term of a
  Weyl fermion.

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

## A. The effective potential for Weyl fermions

-/

/-- The type corresponding to the effective potential of a
  left-handed Weyl fermion. -/
abbrev EFTLagrangianExclDeriv : Type := ExteriorAlgebra ℂ
  (Module.Dual ℂ LeftHandedWeyl × Module.Dual ℂ (ConjModule LeftHandedWeyl))

namespace EFTLagrangianExclDeriv

/-!

### A. The representation on the effective potential

-/

/-- The representation of the Lorentz group (here `SL(2, ℂ)`) on `EFTLagrangianExclDeriv`. -/
def rep : Representation ℂ SL(2, ℂ) EFTLagrangianExclDeriv where
  toFun Λ := (ExteriorAlgebra.map ((LeftHandedWeyl.rep.dual Λ).prodMap
    (LeftHandedWeyl.rep.conj.dual Λ))).toLinearMap
  map_one' := by
    simp only [map_one, End.one_eq_id, LinearMap.prodMap_id, ExteriorAlgebra.map_id,
      AlgHom.toLinearMap_id]
  map_mul' Λ1 Λ2 := by
    simp only [map_mul, End.mul_eq_comp, ← LinearMap.prodMap_comp, ← ExteriorAlgebra.map_comp_map,
      AlgHom.comp_toLinearMap]

lemma rep_apply (Λ : SL(2, ℂ)) (V : EFTLagrangianExclDeriv) :
    rep Λ V = ExteriorAlgebra.map ((LeftHandedWeyl.rep.dual Λ).prodMap
      (LeftHandedWeyl.rep.conj.dual Λ)) V := rfl

@[simp]
lemma rep_apply_one (Λ : SL(2, ℂ)) : rep Λ 1 = 1 := by
  simp [rep_apply]

lemma rep_mul (Λ : SL(2, ℂ)) (V W : EFTLagrangianExclDeriv) :
    rep Λ (V * W) = rep Λ V * rep Λ W:= by
  simp [rep]


/-!

## The invariance condition on

-/

/-- An effective potential is Lorentz invariant if it is stable under the
    action of the Lorentz group. -/
def IsInvariant (V : EFTLagrangianExclDeriv) : Prop := ∀ Λ, rep Λ V = V

lemma IsInvariant.eq_iff {V : EFTLagrangianExclDeriv} :
    IsInvariant V ↔ ∀ Λ, rep Λ V = V := by rfl

lemma IsInvariant.add {V W : EFTLagrangianExclDeriv} (hV : IsInvariant V) (hW : IsInvariant W) :
    IsInvariant (V + W) := by
  intro Λ
  simp_all [IsInvariant.eq_iff]

lemma IsInvariant.smul {V : EFTLagrangianExclDeriv} (hV : IsInvariant V) (c : ℂ) :
    IsInvariant (c • V) := by
  intro Λ
  simp_all [IsInvariant.eq_iff]

lemma IsInvariant.mul {V W : EFTLagrangianExclDeriv} (hV : IsInvariant V) (hW : IsInvariant W) :
    IsInvariant (V * W) := by
  intro Λ
  simp_all [IsInvariant.eq_iff, rep_mul]

lemma IsInvariant.one : IsInvariant 1 := by
  intro Λ
  simp [rep]

end EFTLagrangianExclDeriv

/-!

### B. Field specification for the theory

-/

inductive FieldSpecification : Type
  | ψ (α : Fin 2) : FieldSpecification
  | barψ (α : Fin 2) : FieldSpecification
deriving DecidableEq, Repr

namespace FieldSpecification

open EFTLagrangianExclDeriv

instance : Fintype FieldSpecification where
  elems := {ψ 0, ψ 1, barψ 0, barψ 1}
  complete := by
    intro x
    match x with
    | ψ 0 => simp
    | ψ 1 => simp
    | barψ 0 => simp
    | barψ 1 => simp

/-!

## Ordering on FieldSpecification

We define an ordering on `FieldSpecification`.
This ordering is a choice, and nothing physical can depend on this choice.
We however make it as it simplifies the proofs of lots of lemmas, and
makes it easy to do more calculational aspects.

-/

def toSumFin : FieldSpecification ≃ Fin 2 ⊕ Fin 2 where
  toFun := fun | .ψ (α : Fin 2) => Sum.inl α | .barψ α => Sum.inr α
  invFun := fun | .inl α => ψ α | .inr α => barψ α
  left_inv ψ := by
    fin_cases ψ <;> simp
  right_inv x := by fin_cases x <;> simp


def moduleBasis : Basis FieldSpecification ℂ
    (Module.Dual ℂ LeftHandedWeyl × Module.Dual ℂ (ConjModule LeftHandedWeyl)) :=
  (LeftHandedWeyl.basis.dualBasis.prod LeftHandedWeyl.basis.conj.dualBasis).reindex toSumFin.symm

def toEFTLagrangianExclDeriv (ψ : FieldSpecification) : EFTLagrangianExclDeriv :=
  ExteriorAlgebra.ι ℂ (moduleBasis ψ)

scoped notation "[" v "]ₑ" => toEFTLagrangianExclDeriv v

lemma toEFTLagrangianExclDeriv_eq (ψ : FieldSpecification) :
    toEFTLagrangianExclDeriv ψ = ExteriorAlgebra.ι ℂ (moduleBasis ψ) := rfl

lemma toEFTLagrangianExclDeriv_ψ_eq (α : Fin 2) : [ψ α]ₑ =
    ExteriorAlgebra.ι ℂ (LinearMap.inl ℂ _ _ (LeftHandedWeyl.basis.dualBasis α)) := by
  fin_cases α  <;> simp [toEFTLagrangianExclDeriv_eq, moduleBasis, toSumFin]

lemma toEFTLagrangianExclDeriv_barψ_eq (α : Fin 2) : [barψ α]ₑ =
    ExteriorAlgebra.ι ℂ (LinearMap.inr ℂ _ _ (LeftHandedWeyl.basis.conj.dualBasis α)) := by
  fin_cases α  <;> simp [toEFTLagrangianExclDeriv_eq, moduleBasis, toSumFin]

@[simp]
lemma toEFTLagrangianExclDeriv_mul_self (ψ : FieldSpecification) : [ψ]ₑ * [ψ]ₑ = 0 := by
  simp [toEFTLagrangianExclDeriv_eq]

lemma toEFTLagrangianExclDeriv_mul_anti_commute (ψ χ : FieldSpecification) :
    [ψ]ₑ * [χ]ₑ = - [χ]ₑ * [ψ]ₑ := by
  simp [toEFTLagrangianExclDeriv_eq, neg_mul, eq_neg_iff_add_eq_zero]

lemma rep_apply_toEFTLagrangianExclDeriv_ψ_eq_sum (Λ : SL(2, ℂ)) (α : Fin 2) :
    rep Λ [ψ α]ₑ = ∑ (β : Fin 2), Λ⁻¹ α β • [ψ β]ₑ := by
  simp only [toEFTLagrangianExclDeriv_ψ_eq, Basis.coe_dualBasis, LinearMap.coe_inl, rep_apply,
    Representation.dual_apply, ExteriorAlgebra.map_apply_ι, LinearMap.prodMap_apply, map_zero,
    ← map_smul, Prod.smul_mk, smul_zero, Fin.sum_univ_two, Fin.isValue, ← map_add, Prod.mk_add_mk,
    add_zero, ExteriorAlgebra.ι_inj, Prod.mk.injEq, and_true]
  refine LeftHandedWeyl.basis.ext fun l => ?_
  fin_cases α <;> fin_cases l <;>
    simp [Module.Dual.transpose_apply, LeftHandedWeyl.rep_apply_basis,
      -SpecialLinearGroup.coe_inv]

lemma rep_apply_toEFTLagrangianExclDeriv_barψ_eq_sum (Λ : SL(2, ℂ)) (α : Fin 2) :
    rep Λ [barψ α]ₑ = ∑ β, star (Λ⁻¹ α β) • [barψ β]ₑ := by
  simp only [toEFTLagrangianExclDeriv_barψ_eq, Basis.coe_dualBasis, LinearMap.coe_inr, rep_apply, Representation.dual_apply,
    ExteriorAlgebra.map_apply_ι, LinearMap.prodMap_apply, map_zero, RCLike.star_def, ← map_smul,
    Prod.smul_mk, smul_zero, Fin.sum_univ_two, Fin.isValue, ← map_add, Prod.mk_add_mk, add_zero,
    ExteriorAlgebra.ι_inj, Prod.mk.injEq, true_and]
  refine LeftHandedWeyl.basis.conj.ext fun l => ?_
  fin_cases α <;> fin_cases l <;>
    simp [Module.Dual.transpose_apply, LeftHandedWeyl.rep_apply_basis,
      -SpecialLinearGroup.coe_inv, Representation.conj_apply]

/-!

## The irreps

-/

inductive Irrep
  | ψ
  | barψ
deriving DecidableEq, Fintype

def toIrrep : FieldSpecification → Irrep
  | .ψ _ => .ψ
  | .barψ _ => .barψ

/-!

## Mass dimension

-/

def massDimension : FieldSpecification → ℚ
  | .ψ _ => 3 / 2
  | .barψ _ => 3 / 2

end FieldSpecification

namespace EFTLagrangianExclDeriv

open FieldSpecification

/-!

## Elements from a list of FieldSpecifications
-/

def termOfList (l : List FieldSpecification) : EFTLagrangianExclDeriv :=
  (l.map toEFTLagrangianExclDeriv).prod

lemma termOfList_cons (ψ : FieldSpecification) (l : List FieldSpecification) :
    termOfList (ψ :: l) = [ψ]ₑ * termOfList l := by simp [termOfList]

@[simp]
lemma termOfList_nil : termOfList [] = 1 := by simp [termOfList]

lemma termOfList_singleton (ψ : FieldSpecification) : termOfList [ψ] = [ψ]ₑ := by
  simp [termOfList_cons]

lemma termOfList_append (l1 l2 : List FieldSpecification) :
    termOfList (l1 ++ l2) = termOfList l1 * termOfList l2 := by
  simp [termOfList]

lemma mul_termOfList_of_mem (ψ : FieldSpecification) (l : List FieldSpecification)
    (hψ : ψ ∈ l) : [ψ]ₑ * termOfList l = 0 := by
  induction l with
  | nil => simp at hψ
  | cons β t ih =>
    rcases List.mem_cons.mp hψ with rfl | ha
    · simp [termOfList_cons, ← mul_assoc]
    · simp [termOfList_cons, ← mul_assoc, toEFTLagrangianExclDeriv_mul_anti_commute ψ β]
      simp [mul_assoc, ih ha]

lemma termOfList_zero_of_not_nodup (l : List FieldSpecification) (h : ¬ l.Nodup) :
    termOfList l = 0 := by
  revert h
  induction l with
  | nil => intro h; exact absurd List.nodup_nil h
  | cons a t ih =>
    intro h
    rw [termOfList_cons]
    by_cases hmem : a ∈ t
    · exact mul_termOfList_of_mem a t hmem
    · rw [ih fun hn => h (List.nodup_cons.mpr ⟨hmem, hn⟩), mul_zero]

lemma rep_termOfList_eq_map_rep (Λ : SL(2, ℂ)) (l : List FieldSpecification) :
    rep Λ (termOfList l) = ((l.map toEFTLagrangianExclDeriv).map (rep Λ)).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp [termOfList_cons, rep_mul, ih]

lemma rep_termOfList_of_monomial (g : SL(2, ℂ)) (σ : Equiv.Perm FieldSpecification)
    (d : FieldSpecification → ℂ) (hg : ∀ ψ, rep g [ψ]ₑ = d ψ • [σ ψ]ₑ)
    (l : List FieldSpecification) :
    rep g (termOfList l) = (l.map d).prod • termOfList (l.map σ):= by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [termOfList_cons, rep_mul, hg, ih]
    simp [termOfList_cons, smul_smul, mul_comm]

lemma rep_scale_termOfList_of_rep_scale_toEFTLagrangianExclDeriv (Λ : SL(2, ℂ))
    (h : ∀ ψ, ∃ c : ℂ, rep Λ [ψ]ₑ = c • [ψ]ₑ) (l : List FieldSpecification) :
    ∃ c : ℂ, rep Λ (termOfList l) = c • termOfList l := by
  induction l with
  | nil => exact ⟨1, by simp⟩
  | cons ψ t ih =>
    obtain ⟨cψ, hcψ⟩ := h ψ
    obtain ⟨ct, hct⟩ := ih
    refine ⟨cψ * ct, ?_⟩
    simp [termOfList_cons, rep_mul, hcψ, hct]
    module

lemma mem_termOfList_span (V : EFTLagrangianExclDeriv) :
    V ∈ Submodule.span ℂ (Set.range termOfList) := by
  induction V using ExteriorAlgebra.induction with
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[], termOfList_nil⟩)
  | ι v =>
    rw [← Basis.sum_repr moduleBasis v, map_sum]
    refine Submodule.sum_mem _ fun f _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[f], by simp [termOfList_singleton]; rfl⟩)
  | mul a b ha hb =>
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l1, rfl⟩ := hx
      induction hb using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨l2, rfl⟩ := hy
        exact Submodule.subset_span ⟨l1 ++ l2, termOfList_append l1 l2⟩
      | zero => simp
      | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
      | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hy
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hx
  | add a b ha hb => exact add_mem ha hb

lemma termOfList_perm_neq_zero {l1 l2 : List FieldSpecification} (h : l1.Perm l2) :
    ∃ c : ℂ, termOfList l1 = c • termOfList l2 ∧ c ≠ 0 := by
  induction h with
  | nil => exact ⟨1, by simp⟩
  | cons x _ ih =>
    obtain ⟨c, hc1, hc2⟩ := ih
    exact ⟨c, by rw [termOfList_cons, termOfList_cons, hc1, mul_smul_comm], hc2⟩
  | swap x y l =>
    refine ⟨-1, ?_⟩
    rw [termOfList_cons, termOfList_cons, termOfList_cons, termOfList_cons, ← mul_assoc,
      toEFTLagrangianExclDeriv_mul_anti_commute y x]
    simp [mul_assoc]
  | trans _ _ ih1 ih2 =>
    obtain ⟨c1, hc1, hc1'⟩ := ih1
    obtain ⟨c2, hc2, hc2'⟩ := ih2
    exact ⟨c1 * c2, by rw [hc1, hc2, smul_smul], by grind⟩

lemma termOfList_perm {l1 l2 : List FieldSpecification} (h : l1.Perm l2) :
    ∃ c : ℂ, termOfList l1 = c • termOfList l2 := by
  obtain ⟨c, h1, h2⟩ := termOfList_perm_neq_zero h
  exact ⟨c, h1⟩

lemma termOfList_eq_ιMulti (l : List FieldSpecification) :
    termOfList l = ExteriorAlgebra.ιMulti ℂ l.length (fun i => moduleBasis (l.get i)) := by
  induction l with
  | nil => simp
  | cons ψ l h =>
    simp [termOfList_cons, h]
    rfl

lemma termOfList_ofFn {n : ℕ} (g : Fin n → FieldSpecification) :
    termOfList (List.ofFn g) = ExteriorAlgebra.ιMulti ℂ n (fun i => moduleBasis (g i)) := by
  rw [ExteriorAlgebra.ιMulti_apply, termOfList, List.map_ofFn]
  rfl

/-!

## Construction of a term from a tuple

-/

def termOfTuple {n} (g : Fin n → FieldSpecification) : EFTLagrangianExclDeriv :=
  termOfList (List.ofFn g)

lemma termOfTuple_eq_ιMulti {n} (g : Fin n → FieldSpecification) :
    termOfTuple g = ExteriorAlgebra.ιMulti ℂ n (fun i => moduleBasis (g i)) := by
  rw [termOfTuple, termOfList_ofFn]

lemma termOfTuple_perm {n} (g : Fin n → FieldSpecification) {i j : Fin n} (hij : i ≠ j) :
    termOfTuple (g ∘ Equiv.swap i j) = - termOfTuple g := by
  rw [termOfTuple_eq_ιMulti, termOfTuple_eq_ιMulti]
  exact AlternatingMap.map_swap (ExteriorAlgebra.ιMulti ℂ n) (fun k => moduleBasis (g k)) hij

def termOfVectTuple {n} :
    AlternatingMap ℂ (Module.Dual ℂ LeftHandedWeyl × Module.Dual ℂ (ConjModule LeftHandedWeyl))
      EFTLagrangianExclDeriv (Fin n) := ExteriorAlgebra.ιMulti ℂ n

def coeffOfVectorTuple (s : Multiset FieldSpecification) (n : ℕ) :
    AlternatingMap ℂ (Module.Dual ℂ LeftHandedWeyl × Module.Dual ℂ (ConjModule LeftHandedWeyl))
      EFTLagrangianExclDeriv (Fin n) where
  toMultilinearMap :=
    ∑ g : Fin n → FieldSpecification,
      if Multiset.ofList (List.ofFn g) = s then
        (LinearMap.toSpanSingleton ℂ EFTLagrangianExclDeriv (termOfTuple g)).compMultilinearMap
        ((MultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compLinearMap fun i => moduleBasis.coord (g i))
      else 0
  map_eq_zero_of_eq' := by
    intro v i j hv hij
    have hvswap : ∀ k, v (Equiv.swap i j k) = v k := by
      intro k
      rcases eq_or_ne k i with rfl | hki
      · rw [Equiv.swap_apply_left]; exact hv.symm
      rcases eq_or_ne k j with rfl | hkj
      · rw [Equiv.swap_apply_right]; exact hv
      · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
    simp only [MultilinearMap.toFun_eq_coe, MultilinearMap.sum_apply]
    refine Finset.sum_involution (fun g _ => g ∘ Equiv.swap i j) ?_ ?_
      (fun g _ => Finset.mem_univ _) ?_
    · intro g _
      have hms : Multiset.ofList (List.ofFn (g ∘ Equiv.swap i j)) =
          Multiset.ofList (List.ofFn g) :=
        Multiset.coe_eq_coe.mpr ((Equiv.swap i j).ofFn_comp_perm g)
      rw [hms]
      split_ifs with h
      · simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
          MultilinearMap.mkPiAlgebra_apply, LinearMap.toSpanSingleton_apply,
          Function.comp_apply]
        have hprod : ∏ k, moduleBasis.coord (g (Equiv.swap i j k)) (v k) =
            ∏ k, moduleBasis.coord (g k) (v k) :=
          calc ∏ k, moduleBasis.coord (g (Equiv.swap i j k)) (v k)
              = ∏ k, moduleBasis.coord (g (Equiv.swap i j k)) (v (Equiv.swap i j k)) :=
                Finset.prod_congr rfl fun k _ => by rw [hvswap k]
            _ = ∏ k, moduleBasis.coord (g k) (v k) :=
                Equiv.prod_comp (Equiv.swap i j) fun k => moduleBasis.coord (g k) (v k)
        rw [hprod, termOfTuple_perm g hij, smul_neg, add_neg_cancel]
      · simp
    · intro g _ hfg hcontra
      apply hfg
      have hgji : g j = g i := by
        simpa [Equiv.swap_apply_left] using congrFun hcontra i
      have hterm : termOfTuple g = 0 := by
        rw [termOfTuple_eq_ιMulti]
        exact AlternatingMap.map_eq_zero_of_eq _ _ (by rw [hgji]) hij
      split_ifs
      · simp [hterm]
      · simp
    · intro g _
      funext k
      simp [Function.comp, Equiv.swap_apply_self]

/-!

## Coefficents

We can't define a basis on effective potential without choosing and ordering on the field
specification. To get around this, we can define the coefficient of an effective potential given a
multi-set of field specifications as a linear map which projects down onto a subspace spanned by
terms which are of the correct type. It actually projects down onto a one-dimensional subspace, and
this is where you can think of it as a coefficient.

-/

def coeff (s : Multiset FieldSpecification) : EFTLagrangianExclDeriv →ₗ[ℂ] EFTLagrangianExclDeriv :=
  ExteriorAlgebra.liftAlternating (coeffOfVectorTuple s)

lemma coeff_apply_termOfList (s : Multiset FieldSpecification) (l : List FieldSpecification) :
    coeff s (termOfList l) = if Multiset.ofList l = s then termOfList l else 0 := by
  have hterm : termOfTuple l.get = termOfList l := by rw [termOfTuple, List.ofFn_get]
  rw [coeff, termOfList_eq_ιMulti, ExteriorAlgebra.liftAlternating_apply_ιMulti]
  simp only [coeffOfVectorTuple, AlternatingMap.coe_mk, MultilinearMap.sum_apply]
  refine (Finset.sum_eq_single l.get ?_ ?_).trans ?_
  · intro g _ hg
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hg
    split_ifs with h
    · simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
        MultilinearMap.mkPiAlgebra_apply, LinearMap.toSpanSingleton_apply]
      have hzero : ∏ k, moduleBasis.coord (g k) (moduleBasis (l.get k)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by
          rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_of_ne hi])
      rw [hzero, zero_smul]
    · simp
  · intro h
    exact absurd (Finset.mem_univ _) h
  · rw [List.ofFn_get]
    split_ifs with h
    · simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
        MultilinearMap.mkPiAlgebra_apply, LinearMap.toSpanSingleton_apply, hterm]
      have hprod : ∏ i, moduleBasis.coord (l.get i) (moduleBasis (l.get i)) = 1 := by simp
      rw [hprod, one_smul]
      exact termOfList_eq_ιMulti l
    · simp

lemma coeff_one (s : Multiset FieldSpecification) : coeff s 1 = if s = ∅ then 1 else 0 := by
  trans coeff s (termOfList [])
  · simp
  · rw [coeff_apply_termOfList]
    simp
    grind

@[simp]
lemma coeff_coeff_self {s : Multiset FieldSpecification} (V : EFTLagrangianExclDeriv) :
    coeff s (coeff s V) = coeff s V := by
  induction' mem_termOfList_span V using Submodule.span_induction with V' hV' x y _ _ hx hy
    a x _ hx
  · simp at hV'
    obtain ⟨l, rfl⟩ := hV'
    simp [coeff_apply_termOfList, apply_ite]
    grind
  · simp
  · simp [hx, hy]
  · simp [hx]

lemma coeff_eq_termOfList {s : Multiset FieldSpecification}
    (V : EFTLagrangianExclDeriv) {l : List FieldSpecification} (hl : Multiset.ofList l = s) :
    ∃ c : ℂ, coeff s V = c • termOfList l := by
  induction' mem_termOfList_span V using Submodule.span_induction with V' hV' x y _ _ hx hy
    a x _ hx
  · simp at hV'
    obtain ⟨l', rfl⟩ := hV'
    simp [coeff_apply_termOfList]
    split_ifs
    · rename_i hi
      refine termOfList_perm ?_
      rw [← Multiset.coe_eq_coe]
      simp_all
    · use 0
      simp
  · use 0
    simp
  · obtain ⟨c1, hx⟩ := hx
    obtain ⟨c2, hy⟩ := hy
    use (c1 + c2)
    simp [hx, hy]
    module
  · obtain ⟨c1, hx⟩ := hx
    use a • c1
    simp [hx, smul_smul]

lemma coeff_eq_exists_termOfList (s : Multiset FieldSpecification)
    (V : EFTLagrangianExclDeriv)  :
    ∃ l, ∃ c : ℂ, coeff s V = c • termOfList l := by
  obtain ⟨c, hl⟩ := coeff_eq_termOfList V (s := s) (l := Multiset.toList s) (by simp)
  use Multiset.toList s
  use c

lemma coeff_monomial_selection_rule (g : SL(2, ℂ)) (σ : Equiv.Perm FieldSpecification)
    (d : FieldSpecification → ℂ) (hg : ∀ ψ, rep g [ψ]ₑ = d ψ • [σ ψ]ₑ)
    (s : Multiset FieldSpecification) (V : EFTLagrangianExclDeriv) (hV : IsInvariant V) :
    coeff (s.map σ) V = rep g (coeff s V) := by
  suffices h : ∀ W, coeff (s.map σ) (rep g W) = rep g (coeff s W) by
    specialize h V
    rw [hV g] at h
    exact h
  intro W
  induction' mem_termOfList_span W using Submodule.span_induction with W' hW' x y _ _ hx hy
      a x _ hx
  · simp only [Set.mem_range] at hW'
    obtain ⟨l, rfl⟩ := hW'
    rw [rep_termOfList_of_monomial g σ d hg, map_smul,
      coeff_apply_termOfList, coeff_apply_termOfList]
    have hcond : Multiset.ofList (List.map σ l) = Multiset.map σ s ↔
        Multiset.ofList l = s := by
      rw [← Multiset.map_coe]
      exact ⟨fun hc => Multiset.map_injective σ.injective hc, fun hc => by rw [hc]⟩
    split_ifs with h1 h2 h2
    · rw [rep_termOfList_of_monomial g σ d hg]
    · exact absurd (hcond.mp h1) h2
    · exact absurd (hcond.mpr h2) h1
    · simp
  · simp
  · simp [hx, hy]
  · simp [hx]

/-- If the action of `g` is to permute the fields,
  then it defines a relation between the coefficients of the effective potential. -/
lemma coeff_perm_selection_rule (g : SL(2, ℂ)) (σ : Equiv.Perm FieldSpecification)
    (hg : ∀ ψ, rep g [ψ]ₑ = [σ ψ]ₑ) (s : Multiset FieldSpecification)
    (V : EFTLagrangianExclDeriv) (hV : IsInvariant V) :
    coeff (s.map σ) V = rep g (coeff s V) := by
  apply coeff_monomial_selection_rule g σ (fun _ => 1) ?_ s V hV
  intro ψ
  simpa using hg ψ

lemma coeff_U1_selection_rule {V : EFTLagrangianExclDeriv} (hV : IsInvariant V)
    (g : SL(2, ℂ)) (d : FieldSpecification → ℂ) (hg : ∀ ψ, rep g [ψ]ₑ = d ψ • [ψ]ₑ)
    (s : Multiset FieldSpecification) (hs : (s.map d).prod ≠ 1) :
    coeff s V = 0 := by
  have h1 : coeff s V = rep g (coeff s V) := by
    simpa using coeff_monomial_selection_rule g (Equiv.refl FieldSpecification) d
      (by simpa using hg) s V hV
  have hfix : rep g (coeff s V) = (s.map d).prod • coeff s V := by
    obtain ⟨c, hl⟩ := coeff_eq_termOfList V (s := s) (l := Multiset.toList s) (by simp)
    have hprod : ((Multiset.toList s).map d).prod = (s.map d).prod := by
      rw [← Multiset.coe_toList s]
      simp
    rw [hl, map_smul,
      rep_termOfList_of_monomial g (Equiv.refl FieldSpecification) d (by simpa using hg)]
    simp [smul_smul, hprod, mul_comm]
  have h2 : (1 - (s.map d).prod) • coeff s V = 0 := by
    rw [sub_smul, one_smul, ← hfix, ← h1, sub_self]
  rcases smul_eq_zero.mp h2 with h | h
  · exact absurd (sub_eq_zero.mp h).symm hs
  · exact h

/-- The selection rule on coefficients coming from the anti-symmetry of fermionic fields. -/
lemma coeff_fermionic_selection_rule {V : EFTLagrangianExclDeriv} (hV : IsInvariant V)
    (s : Multiset FieldSpecification) (hs : ¬ s.Nodup) :
    coeff s V = 0 := by
  sorry

/-- The selection rule on coefficients saying that
  every term with an odd number of fermions is zero. -/
lemma coeff_odd_selection_rule {V : EFTLagrangianExclDeriv} (hV : IsInvariant V)
    (s : Multiset FieldSpecification) (hs : Odd s.card) : coeff s V = 0 := by
  refine coeff_U1_selection_rule hV (g := -1) (d := fun ψ => -1) ?_ s ?_
  · intro ψ
    sorry
  · simp
    sorry

/-- The support of an effective potential: the set of multisets of field specifications
  for which the corresponding coefficient is non-zero. -/
def support (V : EFTLagrangianExclDeriv) : Finset (Multiset FieldSpecification) :=
    Set.Finite.toFinset (s := {s | coeff s V ≠ 0}) <| by
  induction' mem_termOfList_span V using Submodule.span_induction with V' hV' x y _ _ hx hy
    a x _ hx
  · simp only [Set.mem_range] at hV'
    obtain ⟨l, rfl⟩ := hV'
    refine (Set.finite_singleton (Multiset.ofList l)).subset ?_
    intro s hs
    simp at hs
    rw [coeff_apply_termOfList] at hs
    rw [Set.mem_singleton_iff]
    by_contra hne
    exact hs (if_neg fun h => hne h.symm)
  · refine Set.finite_empty.subset ?_
    intro s hs
    simp at hs
  · refine (hx.union hy).subset ?_
    intro s hs
    simp at hs
    grind
  · refine hx.subset ?_
    intro s hs
    simp at hs
    grind

@[simp]
lemma support_zero_eq_empty : support (0 : EFTLagrangianExclDeriv) = ∅ := by
  simp [support]

lemma mem_support_iff {V : EFTLagrangianExclDeriv} {s : Multiset FieldSpecification} :
    s ∈ support V ↔ coeff s V ≠ 0 := by simp [support]

lemma coeff_eq_zero_of_not_mem_support {V : EFTLagrangianExclDeriv} {s : Multiset FieldSpecification}
    (h : s ∉ support V) : coeff s V = 0 := by
  simpa [support, Set.Finite.mem_toFinset] using  h

lemma support_add  {V W : EFTLagrangianExclDeriv} :
    support (V + W) ⊆ support V ∪ support W := by
  simp [support]
  grind

lemma support_smul {V : EFTLagrangianExclDeriv} (c : ℂ) :
    support (c • V) ⊆ support V := by
  simp [support]

lemma support_smul_neq_zero {V : EFTLagrangianExclDeriv} (c : ℂ) (hc : c ≠ 0) :
    support (c • V) = support V := by
  simp [support, hc]

lemma mem_support_termOfList_iff {l : List FieldSpecification} (s : Multiset FieldSpecification):
    s ∈ support (termOfList l) ↔ s = Multiset.ofList l ∧ termOfList l ≠ 0 := by
  simp [support, coeff_apply_termOfList]
  grind

lemma support_termOfList_subset (l : List FieldSpecification) :
    support (termOfList l) ⊆ {Multiset.ofList l} := by
  intro s hs
  simp [mem_support_termOfList_iff] at hs
  simp [hs.1]

lemma eq_sum_support_coeff (V : EFTLagrangianExclDeriv) : V = ∑ s ∈ support V, coeff s V := by
  induction' mem_termOfList_span V using Submodule.span_induction with V' hV' x y _ _ hx hy
    a x _ hx
  · simp only [Set.mem_range] at hV'
    obtain ⟨l, rfl⟩ := hV'
    trans ∑ s ∈ {Multiset.ofList l}, coeff s (termOfList l); swap
    · symm
      apply Finset.sum_subset (support_termOfList_subset l)
      simp
      intro hl
      simp [mem_support_termOfList_iff] at hl
      rw [hl]
      simp
    · simp [coeff_apply_termOfList]
  · simp
  · trans ∑ s ∈ x.support ∪ y.support, coeff s (x + y); swap
    · symm
      apply Finset.sum_subset
      · simp [support_add]
      · intro s hs hs'
        exact coeff_eq_zero_of_not_mem_support hs'
    · conv_lhs => rw [hx, hy]
      simp [Finset.sum_add_distrib]
      congr 1
      · apply Finset.sum_subset
        · simp
        · intro s hs hs'
          exact coeff_eq_zero_of_not_mem_support hs'
      · apply Finset.sum_subset
        · simp
        · intro s hs hs'
          exact coeff_eq_zero_of_not_mem_support hs'
  · trans ∑ s ∈ (support x).image (fun s => s), coeff s (a • x); swap
    · symm
      apply Finset.sum_subset
      · simp [support_smul]
      · intro s hs hs'
        exact coeff_eq_zero_of_not_mem_support hs'
    conv_lhs => rw [hx]
    simp [Finset.smul_sum]


/-!

##

-/

/-- Under the action of `g` an operator with field content specified by `s` mixes
  into operators with field content given by this Finset. -/
def repSupport (s : Multiset FieldSpecification) (g : SL(2, ℂ)) :
    Finset (Multiset FieldSpecification) :=
  support (rep g (termOfList (Multiset.toList s)))

lemma repSupport_eq_termOfList {s : Multiset FieldSpecification} (g : SL(2, ℂ))
    (l : List FieldSpecification) (hl : Multiset.ofList l = s) :
    repSupport s g = support (rep g (termOfList l)) := by
  simp [repSupport]
  obtain ⟨c, h1, hc⟩ := termOfList_perm_neq_zero (l1 := Multiset.toList s)  (l2 := l)
    (by apply Multiset.coe_eq_coe.mp; simp [hl])
  simp [h1]
  apply support_smul_neq_zero
  exact hc

lemma repSupport_subset_self_of_singleton_subset_self {s : Multiset FieldSpecification}
    (g : SL(2, ℂ)) (h : ∀ ψ : FieldSpecification, repSupport {ψ} g ⊆ {{ψ}}) :
    repSupport s g ⊆ {s} := by
  have hsingle : ∀ ψ : FieldSpecification, ∃ c : ℂ,
      rep g (termOfList [ψ]) = c • termOfList [ψ] := by
    intro ψ
    have hsup := h ψ
    rw [repSupport_eq_termOfList g [ψ] (by simp)] at hsup
    rcases Finset.subset_singleton_iff.mp hsup with h0 | h1
    · refine ⟨0, ?_⟩
      rw [eq_sum_support_coeff (rep g (termOfList [ψ])), h0]
      simp
    · obtain ⟨c, hc⟩ := coeff_eq_termOfList (s := {ψ}) (rep g (termOfList [ψ]))
        (l := [ψ]) (by simp)
      refine ⟨c, ?_⟩
      rw [eq_sum_support_coeff (rep g (termOfList [ψ])), h1, Finset.sum_singleton, hc]
  have hlist : ∀ l : List FieldSpecification, ∃ c : ℂ,
      rep g (termOfList l) = c • termOfList l := by
    intro l
    induction l with
    | nil => exact ⟨1, by simp⟩
    | cons a l ih =>
      obtain ⟨c, hc⟩ := ih
      obtain ⟨ca, hca⟩ := hsingle a
      refine ⟨ca * c, ?_⟩
      rw [show a :: l = [a] ++ l from rfl, termOfList_append, rep_mul, hca, hc,
        smul_mul_smul_comm]
  obtain ⟨c, hc⟩ := hlist s.toList
  intro t ht
  rw [repSupport, hc] at ht
  have ht' := support_smul c ht
  rw [mem_support_termOfList_iff] at ht'
  simpa using ht'.1


/-!


## Coefficents of irrep terms


-/

/-- The field content of a term which corresponds to a given irrep content. -/
def allTermsWithIrrepContent (i : Multiset Irrep) : Finset (Multiset FieldSpecification) :=
  ((Finset.univ.sym i.card).image Sym.toMultiset).filter (fun s => Multiset.map toIrrep s = i)

/-- The projection of a term of `EFTLagrangianExclDeriv` onto those operators which
  have an irrep content determined by `i`. -/
def irrepCoeff (i : Multiset Irrep) : EFTLagrangianExclDeriv →ₗ[ℂ] EFTLagrangianExclDeriv :=
  ∑ s ∈ allTermsWithIrrepContent i, coeff s

lemma irrepCoeff_eq_sum (i : Multiset Irrep) (V : EFTLagrangianExclDeriv) :
    irrepCoeff i V = ∑ s ∈ allTermsWithIrrepContent i, coeff s V := by
  simp [irrepCoeff]

def irrepSupport (V : EFTLagrangianExclDeriv) : Finset (Multiset Irrep) :=
  (support V).image (Multiset.map toIrrep)

lemma eq_sum_irrepCoeff (V : EFTLagrangianExclDeriv) :
    V = ∑ i ∈ irrepSupport V, irrepCoeff i V := by
  sorry

lemma irrepCoeff_rep {i : Multiset Irrep} {V : EFTLagrangianExclDeriv} (g : SL(2, ℂ)) :
    rep g (irrepCoeff i V) = irrepCoeff i (rep g V) := by
  sorry


lemma irrepCoeff_ψ_barψ_eq_zero_of_isInvariant {V : EFTLagrangianExclDeriv} (hV : IsInvariant V) :
    irrepCoeff {Irrep.ψ, Irrep.barψ} V = 0 := by
  sorry
/-!

## Mass dimension

-/

def allTermsWithMassDimension (n : ℚ) : Finset (Multiset FieldSpecification) :=
  -- Since there is no mass dimension less then 1, a term with mass dimension n
  -- can have at most `n` fields
  let x := List.range (Rat.ceil n + 1).toNat

  ((Finset.univ.sym x.card).image Sym.toMultiset).filter (fun s => (s.map massDimension).sum = n)
def massDimCoeff (n : ℚ) : EFTLagrangianExclDeriv →ₗ[ℂ] EFTLagrangianExclDeriv where
  toFun := fun V => ∑ s ∈ support V, if (s.map massDimension).sum = n then coeff s V else 0
  map_add' := by
    intro V W
    sorry
  map_smul' := by
    intro c V
    sorry

def massDimSupport (V : EFTLagrangianExclDeriv) : Finset ℚ :=
  (support V).image (fun s => (s.map massDimension).sum)

lemma eq_sum_massDimCoeff (V : EFTLagrangianExclDeriv) :
    V = ∑ n ∈ massDimSupport V, massDimCoeff n V := by
  sorry

/-!

## Constraining the effective potential

-/


end EFTLagrangianExclDeriv

end
end Fermion
