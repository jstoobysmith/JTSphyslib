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
We call this type `EffectivePotential` and define it and its properties in this file.
Note that  `Module.Dual ℂ LeftHandedWeyl` is equivalent to `DualLeftHandedWeyl` and
`Module.Dual ℂ (ConjModule LeftHandedWeyl)` is equivalent to `DualRightHandedWeyl`,
so we could equivalently define the effective potential as
`ExteriorAlgebra ℂ (DualLeftHandedWeyl × DualRightHandedWeyl)`. We have done the
former here as it generalises to other cases.

On `EffectivePotential` we define a representation of the Lorentz group, and prove that that
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
abbrev EffectivePotential : Type := ExteriorAlgebra ℂ
  (Module.Dual ℂ LeftHandedWeyl × Module.Dual ℂ (ConjModule LeftHandedWeyl))

namespace EffectivePotential

/-!

### A. The representation on the effective potential

-/

/-- The representation of the Lorentz group (here `SL(2, ℂ)`) on `EffectivePotential`. -/
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

end EffectivePotential

/-!

### B. Field specification for the theory

-/

inductive FieldSpecification : Type
  | ψ (α : Fin 2) : FieldSpecification
  | barψ (α : Fin 2) : FieldSpecification
deriving DecidableEq

namespace FieldSpecification

open EffectivePotential

instance : Fintype FieldSpecification where
  elems := {ψ 0, ψ 1, barψ 0, barψ 1}
  complete := by
    intro x
    match x with
    | ψ 0 => simp
    | ψ 1 => simp
    | barψ 0 => simp
    | barψ 1 => simp

def toSumFin : FieldSpecification ≃ Fin 2 ⊕ Fin 2 where
  toFun := fun | .ψ (α : Fin 2) => Sum.inl α | .barψ α => Sum.inr α
  invFun := fun | .inl α => ψ α | .inr α => barψ α
  left_inv ψ := by
    fin_cases ψ <;> simp
  right_inv x := by fin_cases x <;> simp

def moduleBasis : Basis FieldSpecification ℂ
    (Module.Dual ℂ LeftHandedWeyl × Module.Dual ℂ (ConjModule LeftHandedWeyl)) :=
  (LeftHandedWeyl.basis.dualBasis.prod LeftHandedWeyl.basis.conj.dualBasis).reindex toSumFin.symm

def toEffectivePotential (ψ : FieldSpecification) : EffectivePotential :=
  ExteriorAlgebra.ι ℂ (moduleBasis ψ)

scoped notation "[" v "]ₑ" => toEffectivePotential v

lemma toEffectivePotential_eq (ψ : FieldSpecification) :
    toEffectivePotential ψ = ExteriorAlgebra.ι ℂ (moduleBasis ψ) := rfl

lemma toEffectivePotential_ψ_eq (α : Fin 2) : [ψ α]ₑ =
    ExteriorAlgebra.ι ℂ (LinearMap.inl ℂ _ _ (LeftHandedWeyl.basis.dualBasis α)) := by
  fin_cases α  <;> simp [toEffectivePotential_eq, moduleBasis, toSumFin]

lemma toEffectivePotential_barψ_eq (α : Fin 2) : [barψ α]ₑ =
    ExteriorAlgebra.ι ℂ (LinearMap.inr ℂ _ _ (LeftHandedWeyl.basis.conj.dualBasis α)) := by
  fin_cases α  <;> simp [toEffectivePotential_eq, moduleBasis, toSumFin]

@[simp]
lemma toEffectivePotential_mul_self (ψ : FieldSpecification) : [ψ]ₑ * [ψ]ₑ = 0 := by
  simp [toEffectivePotential_eq]

lemma toEffectivePotential_mul_anti_commute (ψ χ : FieldSpecification) :
    [ψ]ₑ * [χ]ₑ = - [χ]ₑ * [ψ]ₑ := by
  simp [toEffectivePotential_eq, neg_mul, eq_neg_iff_add_eq_zero]

lemma rep_apply_toEffectivePotential_ψ_eq_sum (Λ : SL(2, ℂ)) (α : Fin 2) :
    rep Λ [ψ α]ₑ = ∑ (β : Fin 2), Λ⁻¹ α β • [ψ β]ₑ := by
  simp only [toEffectivePotential_ψ_eq, Basis.coe_dualBasis, LinearMap.coe_inl, rep_apply,
    Representation.dual_apply, ExteriorAlgebra.map_apply_ι, LinearMap.prodMap_apply, map_zero,
    ← map_smul, Prod.smul_mk, smul_zero, Fin.sum_univ_two, Fin.isValue, ← map_add, Prod.mk_add_mk,
    add_zero, ExteriorAlgebra.ι_inj, Prod.mk.injEq, and_true]
  refine LeftHandedWeyl.basis.ext fun l => ?_
  fin_cases α <;> fin_cases l <;>
    simp [Module.Dual.transpose_apply, LeftHandedWeyl.rep_apply_basis,
      -SpecialLinearGroup.coe_inv]

lemma rep_apply_toEffectivePotential_barψ_eq_sum (Λ : SL(2, ℂ)) (α : Fin 2) :
    rep Λ [barψ α]ₑ = ∑ β, star (Λ⁻¹ α β) • [barψ β]ₑ := by
  simp only [toEffectivePotential_barψ_eq, Basis.coe_dualBasis, LinearMap.coe_inr, rep_apply, Representation.dual_apply,
    ExteriorAlgebra.map_apply_ι, LinearMap.prodMap_apply, map_zero, RCLike.star_def, ← map_smul,
    Prod.smul_mk, smul_zero, Fin.sum_univ_two, Fin.isValue, ← map_add, Prod.mk_add_mk, add_zero,
    ExteriorAlgebra.ι_inj, Prod.mk.injEq, true_and]
  refine LeftHandedWeyl.basis.conj.ext fun l => ?_
  fin_cases α <;> fin_cases l <;>
    simp [Module.Dual.transpose_apply, LeftHandedWeyl.rep_apply_basis,
      -SpecialLinearGroup.coe_inv, Representation.conj_apply]

end FieldSpecification

namespace EffectivePotential

open FieldSpecification

/-!

## Elements from a list of FieldSpecifications
-/

def termOfList (l : List FieldSpecification) : EffectivePotential :=
  (l.map toEffectivePotential).prod

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
    · simp [termOfList_cons, ← mul_assoc, toEffectivePotential_mul_anti_commute ψ β]
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
    rep Λ (termOfList l) = ((l.map toEffectivePotential).map (rep Λ)).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp [termOfList_cons, rep_mul, ih]

lemma mem_termOfList_span (V : EffectivePotential) :
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

lemma termOfList_perm {l1 l2 : List FieldSpecification} (h : l1.Perm l2) :
    ∃ c : ℂ, termOfList l1 = c • termOfList l2 := by
  induction h with
  | nil => exact ⟨1, by simp⟩
  | cons x _ ih =>
    obtain ⟨c, hc⟩ := ih
    exact ⟨c, by rw [termOfList_cons, termOfList_cons, hc, mul_smul_comm]⟩
  | swap x y l =>
    refine ⟨-1, ?_⟩
    rw [termOfList_cons, termOfList_cons, termOfList_cons, termOfList_cons, ← mul_assoc,
      toEffectivePotential_mul_anti_commute y x]
    simp [mul_assoc]
  | trans _ _ ih1 ih2 =>
    obtain ⟨c1, hc1⟩ := ih1
    obtain ⟨c2, hc2⟩ := ih2
    exact ⟨c1 * c2, by rw [hc1, hc2, smul_smul]⟩

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

def termOfTuple {n} (g : Fin n → FieldSpecification) : EffectivePotential :=
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
      EffectivePotential (Fin n) := ExteriorAlgebra.ιMulti ℂ n

def coeffOfVectorTuple (s : Multiset FieldSpecification) (n : ℕ) :
    AlternatingMap ℂ (Module.Dual ℂ LeftHandedWeyl × Module.Dual ℂ (ConjModule LeftHandedWeyl))
      EffectivePotential (Fin n) where
  toMultilinearMap :=
    ∑ g : Fin n → FieldSpecification,
      if Multiset.ofList (List.ofFn g) = s then
        (LinearMap.toSpanSingleton ℂ EffectivePotential (termOfTuple g)).compMultilinearMap
        ((MultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compLinearMap fun i => moduleBasis.coord (g i))
      else 0
  map_eq_zero_of_eq' := by
    sorry

def coeff (s : Multiset FieldSpecification) : EffectivePotential →ₗ[ℂ] EffectivePotential :=
  ExteriorAlgebra.liftAlternating (coeffOfVectorTuple s)

/-!

## Submodules

Without choosing an ordering on FieldSpecification we cannot
write down a basis of EffectivePotential. However, what we
can do it split EffectivePotential into submodules of dimension 1.
These submodules are determined by the set of field components which
appear in them.

We will define the projection of an element in the effective
potential onto these submodules, and show that two elements of
the effective potential are equal if and only if all their projections
onto these submodules are equal.

These are in general not invariant under the group action.
-/


def SubmoduleOfSet (s : Multiset FieldSpecification) : Submodule ℂ EffectivePotential :=
  Submodule.span ℂ {V | ∃ (l : List FieldSpecification), Multiset.ofList l = s ∧ V = termOfList l}

lemma termOfList_mem_submoduleOfSet (l : List FieldSpecification) :
    termOfList l ∈ SubmoduleOfSet (Multiset.ofList l) :=
  Submodule.subset_span ⟨l, rfl, rfl⟩

lemma multiset_ofList_ofFn_comp_perm {n : ℕ} (g : Fin n → FieldSpecification)
    (σ : Equiv.Perm (Fin n)) :
    Multiset.ofList (List.ofFn (g ∘ σ)) = Multiset.ofList (List.ofFn g) := by
  have hperm : (List.ofFn (⇑σ)).Perm (List.ofFn (id : Fin n → Fin n)) :=
    List.perm_of_nodup_nodup_toFinset_eq
      (List.nodup_ofFn.mpr σ.injective) (List.nodup_ofFn.mpr fun _ _ h => h)
      (by
        ext k
        simp only [List.mem_toFinset, List.mem_ofFn]
        exact ⟨fun _ => ⟨k, rfl⟩, fun _ => ⟨σ.symm k, σ.apply_symm_apply k⟩⟩)
  calc Multiset.ofList (List.ofFn (g ∘ σ))
      = Multiset.ofList ((List.ofFn (⇑σ)).map g) := by rw [List.map_ofFn]
    _ = Multiset.ofList ((List.ofFn (id : Fin n → Fin n)).map g) :=
        Multiset.coe_eq_coe.2 (hperm.map g)
    _ = Multiset.ofList (List.ofFn g) := by rw [List.map_ofFn]; rfl

/-- The value of the projection onto `SubmoduleOfSet s` on a tuple of field specifications:
  the term of the tuple if its multiset is `s`, and zero otherwise. -/
def SubmoduleOfSet.tupleValue (s : Multiset FieldSpecification) {n : ℕ}
    (g : Fin n → FieldSpecification) : SubmoduleOfSet s :=
  if h : Multiset.ofList (List.ofFn g) = s then
    ⟨termOfList (List.ofFn g), h ▸ termOfList_mem_submoduleOfSet (List.ofFn g)⟩ else 0

lemma SubmoduleOfSet.tupleValue_comp_swap (s : Multiset FieldSpecification) {n : ℕ}
    (g : Fin n → FieldSpecification) {i j : Fin n} (hij : i ≠ j) :
    SubmoduleOfSet.tupleValue s (g ∘ Equiv.swap i j) = - SubmoduleOfSet.tupleValue s g := by
  rw [SubmoduleOfSet.tupleValue, SubmoduleOfSet.tupleValue]
  by_cases h : Multiset.ofList (List.ofFn g) = s
  · rw [dif_pos h, dif_pos (by rw [multiset_ofList_ofFn_comp_perm]; exact h)]
    apply Subtype.ext
    show termOfList (List.ofFn (g ∘ Equiv.swap i j)) = -termOfList (List.ofFn g)
    rw [termOfList_ofFn, termOfList_ofFn]
    exact AlternatingMap.map_swap (ExteriorAlgebra.ιMulti ℂ n)
      (fun k => moduleBasis (g k)) hij
  · rw [dif_neg h, dif_neg (by rw [multiset_ofList_ofFn_comp_perm]; exact h), neg_zero]

/-- The multilinear map underlying the projection onto `SubmoduleOfSet s` in degree `n`:
  each tuple of vectors is expanded in `moduleBasis` and the coefficients of tuples of
  field specifications with multiset `s` are collected. -/
def SubmoduleOfSet.projMultilinear (s : Multiset FieldSpecification) (n : ℕ) :
    MultilinearMap ℂ
      (fun _ : Fin n => Module.Dual ℂ LeftHandedWeyl × Module.Dual ℂ (ConjModule LeftHandedWeyl))
      (SubmoduleOfSet s) :=
  ∑ g : Fin n → FieldSpecification,
    (LinearMap.toSpanSingleton ℂ (SubmoduleOfSet s)
      (SubmoduleOfSet.tupleValue s g)).compMultilinearMap
      ((MultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compLinearMap fun i => moduleBasis.coord (g i))

lemma SubmoduleOfSet.projMultilinear_apply_basis (s : Multiset FieldSpecification) {n : ℕ}
    (v : Fin n → FieldSpecification) :
    SubmoduleOfSet.projMultilinear s n (fun i => moduleBasis (v i)) =
      SubmoduleOfSet.tupleValue s v := by
  rw [SubmoduleOfSet.projMultilinear, MultilinearMap.sum_apply]
  simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, LinearMap.toSpanSingleton_apply]
  rw [Finset.sum_eq_single_of_mem v (Finset.mem_univ v)]
  · have h1 : (∏ i, moduleBasis.coord (v i) (moduleBasis (v i))) = 1 := by
      simp [Basis.coord_apply, Basis.repr_self]
    rw [h1, one_smul]
  · intro g _ hgv
    obtain ⟨k, hk⟩ : ∃ k, g k ≠ v k := by
      by_contra hcon
      push Not at hcon
      exact hgv (funext hcon)
    have hzero : moduleBasis.coord (g k) (moduleBasis (v k)) = 0 := by
      rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, if_neg (Ne.symm hk)]
    rw [Finset.prod_eq_zero (Finset.mem_univ k) hzero, zero_smul]

lemma SubmoduleOfSet.projMultilinear_map_eq_zero (s : Multiset FieldSpecification) {n : ℕ}
    (v : Fin n → Module.Dual ℂ LeftHandedWeyl × Module.Dual ℂ (ConjModule LeftHandedWeyl))
    {i j : Fin n} (hv : v i = v j) (hij : i ≠ j) :
    SubmoduleOfSet.projMultilinear s n v = 0 := by
  have hvswap : ∀ k, v (Equiv.swap i j k) = v k := by
    intro k
    rcases eq_or_ne k i with rfl | hki
    · rw [Equiv.swap_apply_left]; exact hv.symm
    rcases eq_or_ne k j with rfl | hkj
    · rw [Equiv.swap_apply_right]; exact hv
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hinv : Function.Involutive
      (fun g : Fin n → FieldSpecification => g ∘ ⇑(Equiv.swap i j)) := fun g => by
    funext k
    simp [Function.comp_apply, Equiv.swap_apply_self]
  rw [SubmoduleOfSet.projMultilinear, MultilinearMap.sum_apply]
  simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, LinearMap.toSpanSingleton_apply]
  set S := ∑ g : Fin n → FieldSpecification,
    (∏ k, moduleBasis.coord (g k) (v k)) • SubmoduleOfSet.tupleValue s g with hS
  have hre : S = ∑ g : Fin n → FieldSpecification,
      (∏ k, moduleBasis.coord ((g ∘ Equiv.swap i j) k) (v k)) •
        SubmoduleOfSet.tupleValue s (g ∘ Equiv.swap i j) := by
    rw [hS]
    refine Fintype.sum_equiv (Function.Involutive.toPerm _ hinv) _ _ fun g => ?_
    rw [Function.Involutive.coe_toPerm]
    rw [show (g ∘ ⇑(Equiv.swap i j)) ∘ ⇑(Equiv.swap i j) = g from hinv g]
  have hpair : ∀ g : Fin n → FieldSpecification,
      (∏ k, moduleBasis.coord (g k) (v k)) • SubmoduleOfSet.tupleValue s g +
      (∏ k, moduleBasis.coord ((g ∘ Equiv.swap i j) k) (v k)) •
        SubmoduleOfSet.tupleValue s (g ∘ Equiv.swap i j) = 0 := by
    intro g
    have hcoef : (∏ k, moduleBasis.coord ((g ∘ Equiv.swap i j) k) (v k)) =
        ∏ k, moduleBasis.coord (g k) (v k) := by
      calc ∏ k, moduleBasis.coord ((g ∘ Equiv.swap i j) k) (v k)
          = ∏ k, moduleBasis.coord (g (Equiv.swap i j k)) (v (Equiv.swap i j k)) :=
            Finset.prod_congr rfl fun k _ => by rw [Function.comp_apply, hvswap]
        _ = ∏ k, moduleBasis.coord (g k) (v k) :=
            Equiv.prod_comp (Equiv.swap i j) (fun k => moduleBasis.coord (g k) (v k))
    rw [hcoef, SubmoduleOfSet.tupleValue_comp_swap s g hij, smul_neg, add_neg_cancel]
  have hSS : S + S = 0 := by
    nth_rewrite 2 [hre]
    rw [hS, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun g _ => hpair g
  have h2 : (2 : ℂ) • S = 0 := by rw [two_smul]; exact hSS
  have h3 : ((2 : ℂ)⁻¹ * 2) • S = 0 := by rw [mul_smul, h2, smul_zero]
  rwa [show ((2 : ℂ)⁻¹ * 2) = 1 by norm_num, one_smul] at h3

/-- The alternating map underlying the projection onto `SubmoduleOfSet s` in degree `n`. -/
def SubmoduleOfSet.projAlternating (s : Multiset FieldSpecification) (n : ℕ) :
    (Module.Dual ℂ LeftHandedWeyl ×
      Module.Dual ℂ (ConjModule LeftHandedWeyl)) [⋀^Fin n]→ₗ[ℂ] SubmoduleOfSet s :=
  { SubmoduleOfSet.projMultilinear s n with
    map_eq_zero_of_eq' := fun v _ _ hv hij =>
      SubmoduleOfSet.projMultilinear_map_eq_zero s v hv hij }

lemma SubmoduleOfSet.projAlternating_apply (s : Multiset FieldSpecification) (n : ℕ)
    (v : Fin n → Module.Dual ℂ LeftHandedWeyl × Module.Dual ℂ (ConjModule LeftHandedWeyl)) :
    SubmoduleOfSet.projAlternating s n v = SubmoduleOfSet.projMultilinear s n v := rfl

def SubmoduleOfSet.proj (s : Multiset FieldSpecification) :
    EffectivePotential →ₗ[ℂ] SubmoduleOfSet s :=
  ExteriorAlgebra.liftAlternating (SubmoduleOfSet.projAlternating s)

lemma SubmoduleOfSet.proj_apply_termOfList (s : Multiset FieldSpecification)
    (l : List FieldSpecification) :
    (SubmoduleOfSet.proj s (termOfList l) : EffectivePotential) =
      if Multiset.ofList l = s then termOfList l else 0 := by
  conv_lhs => rw [termOfList_eq_ιMulti]
  rw [SubmoduleOfSet.proj, ExteriorAlgebra.liftAlternating_apply_ιMulti,
    SubmoduleOfSet.projAlternating_apply, SubmoduleOfSet.projMultilinear_apply_basis]
  simp only [SubmoduleOfSet.tupleValue, List.ofFn_get]
  split_ifs with h
  · rfl
  · rfl


/-!

## Gradings

-/

variable {M : Type} [AddCommMonoid M]


def GradedSubmodule (g : FieldSpecification → M) (a : M) : Submodule ℂ EffectivePotential :=
  Submodule.span ℂ {V | ∃ (l : List FieldSpecification), (l.map g).sum = a ∧ V = termOfList l}

lemma termOfList_mem_gradedSubmodule (g : FieldSpecification → M) (l : List FieldSpecification) :
    termOfList l ∈ GradedSubmodule g ((l.map g).sum) :=
  Submodule.subset_span ⟨l, rfl, rfl⟩

lemma toEffectivePotential_mem_gradedSubmodule (g : FieldSpecification → M)
    (f : FieldSpecification) : [f]ₑ ∈ GradedSubmodule g (g f) := by
  simpa [termOfList_singleton] using termOfList_mem_gradedSubmodule g [f]


/-!

## The irrep grading

-/

def irrepGrading : FieldSpecification → ℤ × ℤ
  | ψ _ => (1, 0)
  | barψ _ => (0, 1)

/-!

## Mass dimension grading

-/

def massDimGrading : FieldSpecification → ℚ := fun _ => 3/2


/-!

## Below here is old and WIP

-/


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

abbrev ψbarψ : Fin 4 → EffectivePotential := Fin.append ψ barψ

@[simp]
lemma ψbarψ_zero_eq_ψ_zero : ψbarψ 0 = ψ 0 := rfl

@[simp]
lemma ψbarψ_one_eq_ψ_one : ψbarψ 1 = ψ 1 := rfl

@[simp]
lemma ψbarψ_two_eq_barψ_zero : ψbarψ 2 = barψ 0 := rfl

@[simp]
lemma ψbarψ_three_eq_barψ_one : ψbarψ 3 = barψ 1 := rfl

@[simp]
lemma ψbarψ_mul_self (α : Fin 4) : ψbarψ α * ψbarψ α = 0 := by
  fin_cases α
  · exact ψ_mul_self 0
  · exact ψ_mul_self 1
  · exact barψ_mul_self 0
  · exact barψ_mul_self 1

lemma ψbarψ_swap (α β : Fin 4) : ψbarψ α * ψbarψ β = - ψbarψ β * ψbarψ α := by
  fin_cases α <;> fin_cases β <;>
    simp [ψbarψ, neg_mul, eq_neg_iff_add_eq_zero]
    <;> exact ExteriorAlgebra.ι_add_mul_swap _ _

@[simp]
lemma ψbarψ_apply_zero_eq : ψbarψ 0 = ψ 0 := rfl

@[simp]
lemma ψbarψ_apply_one_eq : ψbarψ 1 = ψ 1 := rfl

@[simp]
lemma ψbarψ_apply_two_eq : ψbarψ 2 = barψ 0 := rfl

@[simp]
lemma ψbarψ_apply_three_eq : ψbarψ 3 = barψ 1 := rfl

/-!

### A.2. Of a list
-/

/-- The term of the effective potential generated from a list
  of `Fin 4`, which describe the components `[ψ 0, ψ 1, barψ 0, barψ 1]`. -/
def termOfList (l : List (Fin 4)) : EffectivePotential :=
  (l.map ψbarψ).prod

@[simp]
lemma termOfList_nil : termOfList [] = 1 := by simp [termOfList]

lemma termOfList_cons (l : List (Fin 4)) (α : Fin 4) :
    termOfList (α :: l) = ψbarψ α * termOfList l := by
  simp only [termOfList, List.map_cons, List.prod_cons]

lemma termOfList_append (l₁ l₂ : List (Fin 4)) :
    termOfList (l₁ ++ l₂) = termOfList l₁ * termOfList l₂ := by
  simp [termOfList]

lemma ψbarψ_mul_termOfList_mem (α : Fin 4) (l : List (Fin 4)) (h : α ∈ l) :
    ψbarψ α * termOfList l = 0 := by
  induction l with
  | nil => simp at h
  | cons β t ih =>
    rcases List.mem_cons.mp h with rfl | ha
    · simp [termOfList_cons, ← mul_assoc]
    · simp [termOfList_cons, ← mul_assoc, ψbarψ_swap α β]
      simp [mul_assoc, ih ha]

lemma termOfList_zero_of_not_nodup (l : List (Fin 4)) (h : ¬ l.Nodup) :
    termOfList l = 0 := by
  revert h
  induction l with
  | nil => intro h; exact absurd List.nodup_nil h
  | cons a t ih =>
    intro h
    rw [termOfList_cons]
    by_cases hmem : a ∈ t
    · exact ψbarψ_mul_termOfList_mem a t hmem
    · rw [ih fun hn => h (List.nodup_cons.mpr ⟨hmem, hn⟩), mul_zero]
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

lemma basis_empty_eq_one : basis ∅ = 1 := by simp [basis_eq_termOfList]

lemma ψ_zero_eq_basis : ψ 0 = basis {0} := by
  rw [basis, ExteriorAlgebra.basis_apply]
  simp [ExteriorAlgebra.ιMulti_apply, Set.powersetCard.ofFinEmbEquiv_symm_apply,
    Finset.orderEmbOfFin_apply, ψ]
  rfl

lemma ψ_one_eq_basis : ψ 1 = basis {1} := by
  rw [basis, ExteriorAlgebra.basis_apply]
  simp [ExteriorAlgebra.ιMulti_apply, Set.powersetCard.ofFinEmbEquiv_symm_apply,
    Finset.orderEmbOfFin_apply, ψ]
  rfl

lemma barψ_zero_eq_basis : barψ 0 = basis {2} := by
  rw [basis, ExteriorAlgebra.basis_apply]
  simp [ExteriorAlgebra.ιMulti_apply, Set.powersetCard.ofFinEmbEquiv_symm_apply,
    Finset.orderEmbOfFin_apply, barψ]
  rfl

lemma barψ_one_eq_basis : barψ 1 = basis {3} := by
  rw [basis, ExteriorAlgebra.basis_apply]
  simp [ExteriorAlgebra.ιMulti_apply, Set.powersetCard.ofFinEmbEquiv_symm_apply,
    Finset.orderEmbOfFin_apply, barψ]
  rfl



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

lemma rep_diagonal_apply_append (α : Fin 4) (c : ℂˣ) :
    rep ⟨diagonal ![c, c⁻¹], by simp⟩ (Fin.append ψ barψ α) =
      (![(c⁻¹).1, c.1, starRingEnd ℂ (c⁻¹).1, starRingEnd ℂ c] α) • Fin.append ψ barψ α := by
  fin_cases α <;> simp [rep_apply_ψ_eq_sum, rep_apply_barψ_eq_sum, Finset.univ_fin2]
  all_goals simp [Finset.pair_comm]

lemma rep_diagonal_apply_termOfList (l : List (Fin 4)) (c : ℂˣ) :
    rep ⟨diagonal ![c, c⁻¹], by simp⟩ (termOfList l) =
      ((l.map (![(c⁻¹).1, c.1, starRingEnd ℂ (c⁻¹).1, starRingEnd ℂ c])).prod) • termOfList l := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp [termOfList_cons, rep_mul, ih, rep_diagonal_apply_append, smul_smul, mul_comm]

lemma rep_diagonal_apply_basis (s : Finset (Fin 4)) (c : ℂˣ) :
    rep ⟨diagonal ![c, c⁻¹], by simp⟩ (basis s) =
      (∏ i ∈ s, (![(c⁻¹).1, c.1, starRingEnd ℂ (c⁻¹).1, starRingEnd ℂ c] i)) • basis s := by
  rw [basis_eq_termOfList, rep_diagonal_apply_termOfList, ← Finset.prod_map_toList _,
      ((Finset.sort_perm_toList _ fun x1 x2 => x1 ≤ x2).map _).prod_eq]

/-!

### A.5. Multidegrees

Since ψ fields rotate among themselves under the action of the Lorentz group,
and barψ fields rotate among themselves, it is natural to decompose
the effective potential into submodules which have a fixed number of ψ and barψ
fields appearing in them. The submodules are closed under the action of the
Lorentz group.

-/

def FieldSpecification.ofIndex : Fin 4 → FieldSpecification
  | 0 => FieldSpecification.ψ
  | 1 => FieldSpecification.ψ
  | 2 => FieldSpecification.barψ
  | 3 => FieldSpecification.barψ

/-- The submodules of `EffectivePotential` which have a fixed number of
  `ψ` and `barψ` fields appearing in them. -/
def multiDegreeSubmodule (d : Multiset FieldSpecification) : Submodule ℂ EffectivePotential :=
  Submodule.span ℂ {V | ∃ s : Finset (Fin 4),
    (↑(s.val.map FieldSpecification.ofIndex) : Multiset FieldSpecification) = d ∧ basis s = V}

lemma basis_mem_multiDegreeSubmodule (s : Finset (Fin 4)) :
    basis s ∈ multiDegreeSubmodule ↑(s.val.map FieldSpecification.ofIndex) :=
  Submodule.subset_span ⟨s, rfl, rfl⟩

lemma termOfList_mem_multiDegreeSubmodule (l : List (Fin 4)) :
    termOfList l ∈ multiDegreeSubmodule ↑(l.map FieldSpecification.ofIndex) :=
  Submodule.subset_span ⟨l.toFinset, by simp [Multiset.coe_toFinset, Multiset.map_map], by
    simp [basis_eq_termOfList]⟩
lemma one_mem_multiDegreeSubmodule_zero : (1 : EffectivePotential) ∈ multiDegreeSubmodule 0 :=
  Submodule.subset_span ⟨∅, rfl, by simp [basis_empty_eq_one]⟩

lemma append_mem_multiDegreeSubmodule (α : Fin 4) :
    Fin.append ψ barψ α ∈ multiDegreeSubmodule {FieldSpecification.ofIndex α} :=
  Submodule.subset_span ⟨{α}, rfl, by
    fin_cases α <;>
      simp [ψ_zero_eq_basis, barψ_zero_eq_basis, ψ_one_eq_basis, barψ_one_eq_basis]⟩

lemma ψ_mem_multiDegreeSubmodule (i : Fin 2) :
    ψ i ∈ multiDegreeSubmodule {FieldSpecification.ψ} := by
  fin_cases i
  · exact append_mem_multiDegreeSubmodule 0
  · exact append_mem_multiDegreeSubmodule 1

lemma barψ_mem_multiDegreeSubmodule (i : Fin 2) :
    barψ i ∈ multiDegreeSubmodule {FieldSpecification.barψ} := by
  fin_cases i
  · exact append_mem_multiDegreeSubmodule 2
  · exact append_mem_multiDegreeSubmodule 3

lemma rep_basis_mem_multiDegreeSubmodule (Λ : SL(2, ℂ)) (s : Finset (Fin 4)) :
    rep Λ (basis s) ∈ multiDegreeSubmodule ↑(s.val.map FieldSpecification.ofIndex) := by
  sorry

/-!

### A.6. Stability of multidegrees under the group action

-/

lemma rep_ψ_mem_multiDegreeSubmodule (Λ : SL(2, ℂ)) (i : Fin 2) :
    rep Λ (ψ i) ∈ multiDegreeSubmodule {FieldSpecification.ψ} := by
  rw [rep_apply_ψ_eq_sum]
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (ψ_mem_multiDegreeSubmodule j)

lemma rep_barψ_mem_multiDegreeSubmodule (Λ : SL(2, ℂ)) (i : Fin 2) :
    rep Λ (barψ i) ∈ multiDegreeSubmodule {FieldSpecification.barψ} := by
  rw [rep_apply_barψ_eq_sum]
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (barψ_mem_multiDegreeSubmodule j)

lemma rep_append_mem_multiDegreeSubmodule (Λ : SL(2, ℂ)) (α : Fin 4) :
    rep Λ (Fin.append ψ barψ α) ∈ multiDegreeSubmodule {FieldSpecification.ofIndex α} :=
  match α with
  | 0 => rep_ψ_mem_multiDegreeSubmodule Λ 0
  | 1 => rep_ψ_mem_multiDegreeSubmodule Λ 1
  | 2 => rep_barψ_mem_multiDegreeSubmodule Λ 0
  | 3 => rep_barψ_mem_multiDegreeSubmodule Λ 1

lemma rep_termOfList_mem_multiDegreeSubmodule (Λ : SL(2, ℂ)) (l : List (Fin 4)) :
    rep Λ (termOfList l) ∈ multiDegreeSubmodule ↑(l.map FieldSpecification.ofIndex) := by
  induction l with
  | nil => simpa using one_mem_multiDegreeSubmodule_zero
  | cons α l ih =>
    rw [termOfList_cons, rep_mul]
    simpa [Multiset.singleton_add] using
      mul_mem_multiDegreeSubmodule (rep_append_mem_multiDegreeSubmodule Λ α) ih

/-- The multidegree submodules are stable under the action of the Lorentz group. -/
lemma rep_mem_multiDegreeSubmodule {d : Multiset FieldSpecification} (Λ : SL(2, ℂ))
    {V : EffectivePotential} (hV : V ∈ multiDegreeSubmodule d) :
    rep Λ V ∈ multiDegreeSubmodule d := by
  induction hV using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    exact hl ▸ rep_termOfList_mem_multiDegreeSubmodule Λ l
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

/-- The multidegree submodules are sent to themselves under the action
  of the Lorentz group. -/
lemma multiDegreeSubmodule_map_rep (Λ : SL(2, ℂ)) (d : Multiset FieldSpecification) :
    (multiDegreeSubmodule d).map (rep Λ) = multiDegreeSubmodule d := by
  refine le_antisymm (Submodule.map_le_iff_le_comap.2 fun V hV =>
    rep_mem_multiDegreeSubmodule Λ hV) fun V hV => ?_
  refine ⟨rep Λ⁻¹ V, rep_mem_multiDegreeSubmodule Λ⁻¹ hV, ?_⟩
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

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
  sorry


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

/-!

## C. Coefficent list

-/

/-- The coefficients of an effective potential relevant for invariant potentials, as a
  linear map: the coefficients of `1`, `ψ 0 * ψ 1`, `barψ 0 * barψ 1` and
  `ψ 0 * ψ 1 * barψ 0 * barψ 1`. -/
def invCoeffList : EffectivePotential →ₗ[ℂ] (Fin 4 → ℂ) :=
  LinearMap.pi ![basis.coord ∅, basis.coord {0, 1}, basis.coord {2, 3}, basis.coord {0, 1, 2, 3}]

@[simp]
lemma invCoeffList_one : invCoeffList 1 = ![1, 0, 0, 0] := by
  rw [← basis_empty_eq_one]
  ext i
  fin_cases i <;> simp [invCoeffList]

@[simp]
lemma invCoeffList_ψ_zero_mul_ψ_one : invCoeffList (ψ 0 * ψ 1) = ![0, 1, 0, 0] := by
  trans invCoeffList (basis {0, 1})
  · congr
    rw [basis, ExteriorAlgebra.basis_apply]
    simp [ExteriorAlgebra.ιMulti_apply, Set.powersetCard.ofFinEmbEquiv_symm_apply,
      Finset.orderEmbOfFin_apply, Finset.sort_insert, ψ]
    rfl
  ext i
  fin_cases i <;> simp [invCoeffList, Finsupp.single_apply]
  · decide
  · decide

@[simp]
lemma invCoeffList_barψ_zero_mul_barψ_one : invCoeffList (barψ 0 * barψ 1) = ![0, 0, 1, 0] := by
  trans invCoeffList (basis {2, 3})
  · congr
    rw [basis, ExteriorAlgebra.basis_apply]
    simp [ExteriorAlgebra.ιMulti_apply, Set.powersetCard.ofFinEmbEquiv_symm_apply,
      Finset.orderEmbOfFin_apply, Finset.sort_insert, barψ]
    rfl
  ext i
  fin_cases i <;> simp [invCoeffList, Finsupp.single_apply]
  · decide
  · decide

@[simp]
lemma invCoeffList_quartic : invCoeffList (ψ 0 * ψ 1 * barψ 0 * barψ 1) = ![0, 0, 0, 1] := by
  trans invCoeffList (basis {0, 1, 2, 3})
  · congr
    rw [basis, ExteriorAlgebra.basis_apply];
    simp [ExteriorAlgebra.ιMulti_apply,
      Set.powersetCard.ofFinEmbEquiv_symm_apply, Finset.orderEmbOfFin_apply, Finset.sort_insert,
      ψ, barψ, mul_assoc];
    rfl
  ext i
  fin_cases i <;> simp [invCoeffList, Finsupp.single_apply]
  · decide
  · decide

lemma invCoeffList_injective {V1 V2 : EffectivePotential} (h1 : IsInvariant V1)
    (h2 : IsInvariant V2) (h : invCoeffList V1 = invCoeffList V2) : V1 = V2 := by
  obtain ⟨c1, m11, m21, ρ1, rfl⟩ := isInvariant_iff.1 h1
  obtain ⟨c2, m12, m22, ρ2, rfl⟩ := isInvariant_iff.1 h2
  simp at h
  rcases h with ⟨rfl, rfl, rfl, rfl⟩
  rfl

/-!

## D. Conjugation

-/

/-- The conjugation operator on the effective potential.
  This takes the complex conjugate of the coefficients, swaps the generators `ψ α` and `barψ α`,
  and reverses the order of products. -/
def conjugate : EffectivePotential →ₛₗ[starRingEnd ℂ] EffectivePotential :=
  let conjSwap :
    (Module.Dual ℂ LeftHandedWeyl × Module.Dual ℂ (ConjModule LeftHandedWeyl))
      →ₛₗ[starRingEnd ℂ]
      Module.Dual ℂ LeftHandedWeyl × Module.Dual ℂ (ConjModule LeftHandedWeyl) :=
    { toFun := Prod.map conjDualEquiv.symm conjDualEquiv ∘ Prod.swap
      map_add' p q := by simp [Prod.ext_iff]
      map_smul' c p := by simp [Prod.ext_iff, map_smulₛₗ]}
  CliffordAlgebra.reverse.comp <|
  (conjEquiv (k := ℂ)).symm.comp <|
  (ExteriorAlgebra.lift ℂ
  ⟨(conjEquiv (k := ℂ)).comp ((ExteriorAlgebra.ι ℂ).comp conjSwap),
    fun v =>  ExteriorAlgebra.ι_sq_zero _⟩).toLinearMap

lemma conjugate_eq_comp_algebra_map : ∃ (A: EffectivePotential →ₐ[ℂ] ConjModule EffectivePotential),
    conjugate = CliffordAlgebra.reverse.comp ((conjEquiv (k := ℂ)).symm.comp A.toLinearMap) := by
  let conjSwap :
    (Module.Dual ℂ LeftHandedWeyl × Module.Dual ℂ (ConjModule LeftHandedWeyl))
      →ₛₗ[starRingEnd ℂ]
      Module.Dual ℂ LeftHandedWeyl × Module.Dual ℂ (ConjModule LeftHandedWeyl) :=
    { toFun := Prod.map conjDualEquiv.symm conjDualEquiv ∘ Prod.swap
      map_add' p q := by simp [Prod.ext_iff]
      map_smul' c p := by simp [Prod.ext_iff, map_smulₛₗ]}
  use ExteriorAlgebra.lift ℂ
    ⟨(conjEquiv (k := ℂ)).comp ((ExteriorAlgebra.ι ℂ).comp conjSwap),
      fun v =>  ExteriorAlgebra.ι_sq_zero _⟩
  rfl

lemma conjugate_apply_ι (v : Dual ℂ LeftHandedWeyl × Dual ℂ (ConjModule LeftHandedWeyl)) :
    conjugate (ExteriorAlgebra.ι ℂ v) =
    (CliffordAlgebra.reverse <| conjEquiv (k := ℂ) <|
    ExteriorAlgebra.ι ℂ <| Prod.map conjDualEquiv.symm conjDualEquiv ∘ Prod.swap <| v) := by
  simp [conjugate]
  erw [AlgHom.toLinearMap_apply]
  rw [ExteriorAlgebra.lift_ι_apply]
  rfl

@[simp]
lemma conjugate_one : conjugate 1 = 1 := by
  simp [conjugate]
  erw [AlgHom.toLinearMap_apply]
  rw [map_one]
  exact CliffordAlgebra.reverse.map_one

@[simp]
lemma conjugate_algebraMap (c : ℂ) : conjugate (algebraMap ℂ EffectivePotential c) =
    algebraMap ℂ EffectivePotential (starRingEnd ℂ c) := by
  simp [Algebra.algebraMap_eq_smul_one]

lemma conjugate_mul (V W : EffectivePotential) :
    conjugate (V * W) = conjugate W * conjugate V := by
  obtain ⟨A, hA⟩ := conjugate_eq_comp_algebra_map
  simp [hA]
  erw [AlgHom.coe_toLinearMap, AlgHom.toLinearMap_apply]
  simp [conjEquiv]
  erw [CliffordAlgebra.reverse.map_mul]

@[simp]
lemma conjugate_conjugate (V : EffectivePotential) : conjugate (conjugate V) = V := by
  induction' V using ExteriorAlgebra.induction with r v a b ha hb a b ha hb
  · simp [conjugate_algebraMap]
  · simp [conjugate_apply_ι, conjEquiv]
    obtain ⟨fst, snd⟩ := v
    simp_all only [Prod.swap_prod_mk, Prod.map_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.apply_symm_apply]
  · simp [conjugate_mul, ha, hb]
  · simp [ha, hb]

lemma conjugate_injective : Function.Injective conjugate := by
  intro V W h
  have h' : conjugate (conjugate V) = conjugate (conjugate W) := by rw [h]
  simp only [conjugate_conjugate] at h'
  exact h'

@[simp]
lemma conjugate_ψ (α : Fin 2) : conjugate (ψ α) = barψ α := by
  simp [ψ, conjugate_apply_ι]
  trans CliffordAlgebra.reverse (barψ α)
  · congr 1
    simp only [conjEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, barψ,
      Basis.coe_dualBasis, LinearMap.coe_inr, ExteriorAlgebra.ι_inj, Prod.mk.injEq, true_and]
    rfl
  simp [barψ]

@[simp]
lemma conjugate_barψ (α : Fin 2) : conjugate (barψ α) = ψ α := by
  apply conjugate_injective
  simp [conjugate_ψ]

/-!

## E. Reality condition

-/

/-- The effective potential is real if it is equal to its conjugate. -/
def IsReal (V : EffectivePotential) : Prop := conjugate V = V

lemma isReal_iff {V : EffectivePotential} : IsReal V ↔ conjugate V = V := by rfl

/-- The necessary and sufficent condition for a real potential to be
  invariant under the Lorentz group. -/
lemma isInvariant_iff_of_isReal {V : EffectivePotential} (h : IsReal V) :
    IsInvariant V ↔ ∃ (c : ℝ), ∃ (m : ℂ), ∃ (ρ : ℝ), V =
      c • 1 + m • ψ 0 * ψ 1 - star m • barψ 0 * barψ 1 + ρ • (ψ 0 * ψ 1 * barψ 0 * barψ 1) := by
  rw [isInvariant_iff]
  constructor
  · rintro ⟨c, m1, m2, ρ, rfl⟩
    simp [isReal_iff, conjugate_mul, ← mul_assoc] at h
    have h1 := congrArg invCoeffList h
    simp at h1
    rcases h1 with ⟨h1, h2, rfl, h3⟩
    use c.re, m1, ρ.re
    have hc : c = (c.re : ℂ) := by rw [← propext (re_eq_ofReal_of_isSelfAdjoint h1)]
    have hρ : ρ = (ρ.re : ℂ) := by rw [← propext (re_eq_ofReal_of_isSelfAdjoint h3)]
    rw [hc, hρ]
    simp only [coe_smul, Fin.isValue, neg_smul, ofReal_re, Algebra.smul_mul_assoc, RCLike.star_def,
      add_left_inj]
    abel
  · rintro ⟨c, m1, ρ, rfl⟩
    use c, m1, -star m1, ρ
    simp
    abel

end EffectivePotential

end
end Fermion
