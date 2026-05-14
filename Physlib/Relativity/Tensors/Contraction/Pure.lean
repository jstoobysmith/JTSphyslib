/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.Basic
/-!

# Contractions on pure tensors

-/

@[expose] public section

open IndexNotation
open CategoryTheory
open MonoidalCategory

namespace TensorSpecies
open OverColor

variable {k : Type} [CommRing k] {C G : Type} [Group G]
  {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
  {S : TensorSpecies k C G basisIdx}

namespace Tensor

/-!

## Pure.contrPCoeff

-/

namespace Pure

/-!

## dropPair

-/
open Fin

set_option linter.unusedVariables false in
/-- Given `i j : Fin (n + 1 + 1)`, `c : Fin (n + 1 + 1) → C` and a pure tensor `p : Pure S c`,
  `dropPair i j _ p` is the tensor formed by dropping the `i`th and `j`th parts of `p`. -/
@[nolint unusedArguments]
def dropPair (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (p : Pure S c) :
    Pure S (c ∘ succSuccAbove i j) :=
    fun m => p (succSuccAbove i j m)

@[simp]
lemma dropPair_equivariant {n : ℕ} {c : Fin (n + 1 + 1) → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (p : Pure S c) (g : G) :
    dropPair i j hij (g • p) = g • dropPair i j hij p := by
  ext m
  simp only [dropPair, actionP_eq]
  rfl

lemma dropPair_symm (i j : Fin (n + 1 + 1)) (hij : i ≠ j)
    (p : Pure S c) : dropPair i j hij p =
    permP id (by simp) (dropPair j i hij.symm p) := by
  ext m
  simp only [Function.comp_apply, dropPair, permP, id_eq]
  refine (congr_right _ _ _ ?_).symm
  rw [succSuccAbove_symm]

lemma dropPair_comm {n : ℕ} {c : Fin (n + 1 + 1 + 1 + 1) → C}
    (i1 j1 : Fin (n + 1 + 1 + 1 + 1)) (i2 j2 : Fin (n + 1 + 1))
    (hij1 : i1 ≠ j1) (hij2 : i2 ≠ j2) (p : Pure S c) :
    let i2' := (succSuccAbove i1 j1 i2);
    let j2' := (succSuccAbove i1 j1 j2);
    have hi2j2' : i2' ≠ j2' := by simp [i2', j2', hij2];
    let i1' := (predPredAbove i2' j2' hi2j2' i1 (by simp [i2', j2']));
    let j1' := (predPredAbove i2' j2' hi2j2' j1 (by simp [i2', j2']));
    dropPair i2 j2 hij2 (dropPair i1 j1 hij1 p) =
    permP id (PermCond.succSuccAbove_comm i1 j1 i2 j2 hij1 hij2)
    ((dropPair i1' j1' (by simp [i1', j1', hij1]) (dropPair i2' j2' hi2j2' p))) := by
  ext m
  simp only [Function.comp_apply, dropPair, permP, id_eq]
  apply (congr_right _ _ _ ?_).symm
  rw [succSuccAbove_comm_apply]
  · simp [hij1]
  · simp [hij2]

@[simp]
lemma dropPair_update_fst {n : ℕ} [inst : DecidableEq (Fin (n + 1 +1))] {c : Fin (n + 1 + 1) → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (p : Pure S c)
    (x : S.FD.obj (Discrete.mk (c i))) :
    dropPair i j hij (p.update i x) = dropPair i j hij p := by
  ext m
  simp only [Function.comp_apply, dropPair, update]
  rw [Function.update_of_ne]
  exact Ne.symm (fst_ne_succSuccAbove_pre i j m)

@[simp]
lemma dropPair_update_snd {n : ℕ} [inst : DecidableEq (Fin (n + 1 +1))] {c : Fin (n + 1 + 1) → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (p : Pure S c)
    (x : S.FD.obj (Discrete.mk (c j))) :
    dropPair i j hij (p.update j x) = dropPair i j hij p := by
  rw [dropPair_symm]
  simp only [dropPair_update_fst]
  conv_rhs => rw [dropPair_symm]

@[simp]
lemma dropPair_update_succSuccAbove {n : ℕ} [inst : DecidableEq (Fin (n + 1 +1))]
    {c : Fin (n + 1 + 1) → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (p : Pure S c)
    (m : Fin n)
    (x : S.FD.obj (Discrete.mk (c (succSuccAbove i j m)))) :
    dropPair i j hij (p.update (succSuccAbove i j m) x) =
    (dropPair i j hij p).update m x := by
  ext m'
  simp only [Function.comp_apply, dropPair, update]
  by_cases h : m' = m
  · subst h
    simp
  · rw [Function.update_of_ne, Function.update_of_ne]
    · rfl
    · simp [h]
    · simp [h]

TODO "Prove lemmas relating to the commutation rules of `dropPair` and `prodP`."

@[simp]
lemma dropPair_permP {n n1 : ℕ} {c : Fin (n + 1 + 1) → C}
    {c1 : Fin (n1 + 1 + 1) → C} (i j : Fin (n1 + 1 + 1)) (hij : i ≠ j)
    (σ : Fin (n1 + 1 + 1) → Fin (n + 1 + 1)) (hσ : PermCond c c1 σ) (p : Pure S c) :
    dropPair i j hij (permP σ hσ p) = permP _ (hσ.succSuccAbove i j hij)
    (dropPair (σ i) (σ j) (by simp [hσ.1.injective.eq_iff, hij]) p) := by
  ext m
  simp only [Function.comp_apply, dropPair, permP, funPredPredAbove]
  apply congr_mid
  · simp
  · simp [hσ.2]
  · simp [hσ.2]

/-!

## Contraction coefficient

-/

/-- Given a pure tensor `p : Pure S c` and a `i j : Fin n`
  corresponding to dual colors in `c`, `contrPCoeff i j _ p` is the
  element of the underlying ring `k` formed by contracting `p i` and `p j`. -/
noncomputable def contrPCoeff {n : ℕ} {c : Fin n → C}
    (i j : Fin n) (hij : i ≠ j ∧ S.τ (c i) = c j) (p : Pure S c) : k :=
    (S.contr.app (Discrete.mk (c i))) (p i ⊗ₜ ((S.FD.map (eqToHom (by simp [hij]))) (p j)))

@[simp]
lemma contrPCoeff_permP {n n1 : ℕ} {c : Fin n → C}
    {c1 : Fin n1 → C} (i j : Fin n1) (hij : i ≠ j ∧ S.τ (c1 i) = c1 j)
    (σ : Fin n1 → Fin n) (hσ : PermCond c c1 σ) (p : Pure S c) :
    contrPCoeff i j hij (permP σ hσ p) =
    contrPCoeff (σ i) (σ j) (by simp [hσ.1.injective.eq_iff, hij, hσ.2]) p := by
  simp only [contrPCoeff, Monoidal.tensorUnit_obj,
    Functor.comp_obj, Discrete.functor_obj_eq_as, Function.comp_apply, permP]
  conv_rhs => erw [S.contr_congr (c (σ i)) ((c1 i)) (by simp [hσ.2])]
  simp only [Monoidal.tensorUnit_obj,
    Functor.comp_obj, Discrete.functor_obj_eq_as, Function.comp_apply]
  apply congrArg
  congr 1
  change ((S.FD.map (eqToHom _) ≫ S.FD.map (eqToHom _)).hom) _ =
    ((S.FD.map (eqToHom _) ≫ S.FD.map (eqToHom _)).hom) _
  rw [← Functor.map_comp, ← Functor.map_comp]
  simp

@[simp]
lemma contrPCoeff_update_succSuccAbove {n : ℕ} [inst : DecidableEq (Fin (n + 1 +1))]
    {c : Fin (n + 1 + 1) → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j) (m : Fin n)
    (p : Pure S c) (x : S.FD.obj (Discrete.mk (c (succSuccAbove i j m)))) :
    contrPCoeff i j hij (p.update (succSuccAbove i j m) x) =
    contrPCoeff i j hij p := by
  simp only [contrPCoeff]
  congr
  · simp [update]
  · simp [update]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma contrPCoeff_update_fst_add {n : ℕ} [inst : DecidableEq (Fin n)] {c : Fin n → C}
    (i j : Fin n) (hij : i ≠ j ∧ S.τ (c i) = c j)
    (p : Pure S c) (x y : S.FD.obj (Discrete.mk (c i))) :
    contrPCoeff i j hij (p.update i (x + y)) =
    contrPCoeff i j hij (p.update i x) + contrPCoeff i j hij (p.update i y) := by
  change ((S.contr.app { as := c i })).hom.toLinearMap _ =
    ((S.contr.app { as := c i })).hom.toLinearMap _
    + ((S.contr.app { as := c i })).hom.toLinearMap _
  simp [Function.update_of_ne (Ne.symm hij.1), update, TensorProduct.add_tmul, LinearMap.map_add]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma contrPCoeff_update_snd_add {n : ℕ} [inst : DecidableEq (Fin n)] {c : Fin n → C}
    (i j : Fin n) (hij : i ≠ j ∧ S.τ (c i) = c j)
    (p : Pure S c) (x y : S.FD.obj (Discrete.mk (c j))) :
    contrPCoeff i j hij (p.update j (x + y)) =
    contrPCoeff i j hij (p.update j x) + contrPCoeff i j hij (p.update j y) := by
  simp only [contrPCoeff, Monoidal.tensorUnit_obj,
    Functor.comp_obj, Discrete.functor_obj_eq_as, Function.comp_apply, update, Function.update_self]
  change ((S.contr.app { as := c i })).hom.toLinearMap _ =
    ((S.contr.app { as := c i })).hom.toLinearMap _
    + ((S.contr.app { as := c i })).hom.toLinearMap _
  rw [Function.update_of_ne hij.1, Function.update_of_ne hij.1,
    Function.update_of_ne hij.1]
  conv_lhs =>
    enter [2, 3]
    change ((S.FD.map (eqToHom _))).hom.toLinearMap (x + y)
  simp only [Monoidal.tensorUnit_obj, TensorProduct.tmul_add, LinearMap.map_add]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma contrPCoeff_update_fst_smul {n : ℕ} [inst : DecidableEq (Fin n)] {c : Fin n → C}
    (i j : Fin n) (hij : i ≠ j ∧ S.τ (c i) = c j)
    (p : Pure S c) (r : k) (x : S.FD.obj (Discrete.mk (c i))) :
    contrPCoeff i j hij (p.update i (r • x)) =
    r * contrPCoeff i j hij (p.update i x) := by
  simp only [contrPCoeff, Monoidal.tensorUnit_obj,
    Functor.comp_obj, Discrete.functor_obj_eq_as, Function.comp_apply, update, Function.update_self,
    TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  change ((S.contr.app { as := c i })).hom.toLinearMap _ = r * _
  simp only [Monoidal.tensorUnit_obj, LinearMap.map_smul, smul_eq_mul]
  congr 1
  change ((S.contr.app { as := c i })).hom.toLinearMap _ =
    ((S.contr.app { as := c i })).hom.toLinearMap _
  rw [Function.update_of_ne (Ne.symm hij.1), Function.update_of_ne (Ne.symm hij.1)]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma contrPCoeff_update_snd_smul {n : ℕ} [inst : DecidableEq (Fin n)] {c : Fin n → C}
    (i j : Fin n) (hij : i ≠ j ∧ S.τ (c i) = c j)
    (p : Pure S c) (r : k) (x : S.FD.obj (Discrete.mk (c j))) :
    contrPCoeff i j hij (p.update j (r • x)) =
    r * contrPCoeff i j hij (p.update j x) := by
  simp only [contrPCoeff, Monoidal.tensorUnit_obj,
    Functor.comp_obj, Discrete.functor_obj_eq_as, Function.comp_apply, update, Function.update_self]
  change ((S.contr.app { as := c i })).hom.toLinearMap _ = r * _
  rw [Function.update_of_ne hij.1, Function.update_of_ne hij.1]
  conv_lhs =>
    enter [2, 3]
    change ((S.FD.map (eqToHom _))).hom.toLinearMap (r • _)
  simp only [Monoidal.tensorUnit_obj, LinearMap.map_smul, TensorProduct.tmul_smul, smul_eq_mul]
  rfl

lemma contrPCoeff_dropPair {n : ℕ} {c : Fin (n + 1 + 1) → C}
    (a b : Fin (n + 1 + 1)) (hab : a ≠ b)
    (i j : Fin n) (hij : i ≠ j ∧ S.τ (c (succSuccAbove a b i)) = (c (succSuccAbove a b j)))
    (p : Pure S c) : (p.dropPair a b hab).contrPCoeff i j hij =
    p.contrPCoeff (succSuccAbove a b i) (succSuccAbove a b j)
      (by simpa using hij) := by rfl

lemma contrPCoeff_symm {n : ℕ} {c : Fin n → C} {i j : Fin n} {hij : i ≠ j ∧ S.τ (c i) = c j}
    {p : Pure S c} :
    p.contrPCoeff i j hij = p.contrPCoeff j i ⟨hij.1.symm, by simp [← hij.2]⟩ := by
  rw [contrPCoeff, contrPCoeff]
  erw [S.contr_tmul_symm]
  rw [S.contr_congr (S.τ (c i)) (c j)]
  simp only [Monoidal.tensorUnit_obj,
    Functor.comp_obj, Discrete.functor_obj_eq_as, Function.comp_apply]
  change _ = (S.contr.app { as := c j }).hom _
  congr 2
  · change ((S.FD.map (eqToHom _) ≫ S.FD.map (eqToHom _)).hom) _ = _
    rw [← S.FD.map_comp]
    simp
  · change ((S.FD.map (eqToHom _) ≫ S.FD.map (eqToHom _)).hom) _ = _
    rw [← S.FD.map_comp]
    simp only [eqToHom_trans]
    rfl
  · simp [hij.2]

lemma contrPCoeff_mul_dropPair {n : ℕ} {c : Fin (n + 1 + 1 + 1 + 1) → C}
    (i1 j1 : Fin (n + 1 + 1 + 1 + 1)) (i2 j2 : Fin (n + 1 + 1))
    (hij1 : i1 ≠ j1 ∧ S.τ (c i1) = (c j1))
    (hij2 : i2 ≠ j2 ∧ S.τ (c (succSuccAbove i1 j1 i2)) = (c (succSuccAbove i1 j1 j2)))
    (p : Pure S c) :
    let i2' := (succSuccAbove i1 j1 i2);
    let j2' := (succSuccAbove i1 j1 j2);
    have hi2j2' : i2' ≠ j2' := by simp [i2', j2', hij2];
    let i1' := (predPredAbove i2' j2' hi2j2' i1 (by simp [i2', j2']));
    let j1' := (predPredAbove i2' j2' hi2j2' j1 (by simp [i2', j2']));
    (p.contrPCoeff i1 j1 hij1) * (dropPair i1 j1 hij1.1 p).contrPCoeff i2 j2 hij2 =
    (p.contrPCoeff i2' j2' (by simp [i2', j2', hij2])) *
    (dropPair i2' j2' (by simp [i2', j2', hij2]) p).contrPCoeff i1' j1'
      (by simp [i1', j1', hij1]) := by
  simp only [contrPCoeff_dropPair, succSuccAbove_predPredAbove]
  rw [mul_comm]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma contrPCoeff_invariant {n : ℕ} {c : Fin n → C} {i j : Fin n}
    {hij : i ≠ j ∧ S.τ (c i) = c j} {p : Pure S c}
    (g : G) : (g • p).contrPCoeff i j hij = p.contrPCoeff i j hij := by
  calc (g • p).contrPCoeff i j hij
    _ = (S.contr.app (Discrete.mk (c i)))
          ((S.FD.obj _).ρ g (p i) ⊗ₜ ((S.FD.map (eqToHom (by simp [hij])))
          ((S.FD.obj _).ρ g (p j)))) := rfl
    _ = (S.contr.app (Discrete.mk (c i)))
          ((S.FD.obj _).ρ g (p i) ⊗ₜ (S.FD.obj _).ρ g ((S.FD.map (eqToHom (by simp [hij])))
          (p j))) := by
        congr 2
        simp only [Functor.comp_obj, Discrete.functor_obj_eq_as, Function.comp_apply]
        have h1 := (S.FD.map (eqToHom (by simp [hij] : { as := c j } =
          (Discrete.functor (Discrete.mk ∘ S.τ)).obj { as := c i }))).hom.isIntertwining' g
        exact LinearMap.congr_fun h1 (p j)
  have h1 := (S.contr.app (Discrete.mk (c i))).hom.isIntertwining' g
  exact LinearMap.congr_fun h1 ((p i) ⊗ₜ ((S.FD.map (eqToHom (by simp [hij]))) (p j)))

/-!

## Contractions

-/

/-- For `c : Fin (n + 1 + 1) → C`, `i j : Fin (n + 1 + 1)` with dual color, and a pure tensor
  `p : Pure S c`, `contrP i j _ p` is the tensor (not pure due to the `n = 0` case)
  formed by contracting the `i`th index of `p`
  with the `j`th index. -/
noncomputable def contrP {n : ℕ} {c : Fin (n + 1 + 1) → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j) (p : Pure S c) :
    S.Tensor (c ∘ succSuccAbove i j) :=
  (p.contrPCoeff i j hij) • (p.dropPair i j hij.1).toTensor

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma contrP_update_add {n : ℕ} [inst : DecidableEq (Fin (n + 1 +1))] {c : Fin (n + 1 + 1) → C}
    (i j m : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j)
    (p : Pure S c) (x y : S.FD.obj (Discrete.mk (c m))) :
    contrP i j hij (p.update m (x + y)) =
    contrP i j hij (p.update m x) + contrP i j hij (p.update m y) := by
  rcases eq_or_exists_succSuccAbove i j hij.1 m with rfl | rfl | ⟨m', rfl⟩
  · simp [contrP, add_smul]
  · simp [contrP, add_smul]
  · simp [contrP]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma contrP_update_smul {n : ℕ} [inst : DecidableEq (Fin (n + 1 +1))] {c : Fin (n + 1 + 1) → C}
    (i j m : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j)
    (p : Pure S c) (r : k) (x : S.FD.obj (Discrete.mk (c m))) :
    contrP i j hij (p.update m (r • x)) =
    r • contrP i j hij (p.update m x) := by
  rcases eq_or_exists_succSuccAbove i j hij.1 m with rfl | rfl | ⟨m', rfl⟩
  · simp [contrP, smul_smul]
  · simp [contrP, smul_smul]
  · simp [contrP, smul_smul, mul_comm]

@[simp]
lemma contrP_equivariant {n : ℕ} {c : Fin (n + 1 + 1) → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j) (p : Pure S c) (g : G) :
    contrP i j hij (g • p) = g • contrP i j hij p := by
  simp [contrP, contrPCoeff_invariant, dropPair_equivariant, actionT_pure]

lemma contrP_symm {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i j : Fin (n + 1 + 1)} {hij : i ≠ j ∧ S.τ (c i) = c j} {p : Pure S c} :
    contrP i j hij p = permT id (by simp)
    (contrP j i ⟨hij.1.symm, by simp [← hij.2]⟩ p) := by
  rw [contrP, contrPCoeff_symm, dropPair_symm]
  simp [contrP, permT_pure]

/-!

## contrP as a multilinear map

-/

set_option backward.isDefEq.respectTransparency false in
/-- The multi-linear map formed by contracting a pair of indices of pure tensors. -/
noncomputable def contrPMultilinear {n : ℕ} {c : Fin (n + 1 + 1) → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j) :
    MultilinearMap k (fun i => S.FD.obj (Discrete.mk (c i)))
      (S.Tensor (c ∘ succSuccAbove i j))where
  toFun p := contrP i j hij p
  map_update_add' p m x y := by
    change (update p m (x + y)).contrP i j hij = _
    simp only [contrP_update_add]
    rfl
  map_update_smul' p k r y := by
    change (update p k (r • y)).contrP i j hij = _
    rw [Pure.contrP_update_smul]
    rfl

end Pure

end Tensor

end TensorSpecies
