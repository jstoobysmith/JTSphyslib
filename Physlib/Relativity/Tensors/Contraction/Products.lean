/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.Contraction.Basic
public import Physlib.Relativity.Tensors.Product
/-!

# The interaction of contractions and products

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

## Products and contractions

-/

set_option backward.isDefEq.respectTransparency false in
lemma Pure.contrPCoeff_natAdd {n n1 : ℕ} {c : Fin (n + 1 + 1) → C}
    {c1 : Fin n1 → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j)
    (p : Pure S c) (p1 : Pure S c1) :
    contrPCoeff (Fin.natAdd n1 i) (Fin.natAdd n1 j)
    (by simp_all [Fin.ext_iff]) (p1.prodP p)
    = contrPCoeff i j hij p := by
  simp only [contrPCoeff, Monoidal.tensorUnit_obj, Functor.comp_obj, Discrete.functor_obj_eq_as,
    Function.comp_apply, prodP_apply_natAdd]
  conv_lhs => erw [S.contr_congr _ ((c i)) (by simp)]
  apply congrArg
  congr 1
  · change (ConcreteCategory.hom (S.FD.map (Discrete.eqToHom _)))
      ((ConcreteCategory.hom (S.FD.map (eqToHom _))) (p i)) = _
    simp [map_map_apply]
  · change (ConcreteCategory.hom (S.FD.map (Discrete.eqToHom _)))
      ((ConcreteCategory.hom (S.FD.map (eqToHom _))) _) = _
    simp [map_map_apply]

set_option backward.isDefEq.respectTransparency false in
lemma Pure.contrPCoeff_castAdd {n n1 : ℕ} {c : Fin (n + 1 + 1) → C}
    {c1 : Fin n1 → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j)
    (p : Pure S c) (p1 : Pure S c1) :
    contrPCoeff (Fin.castAdd n1 i) (Fin.castAdd n1 j)
    (by simp_all [Fin.ext_iff]) (p.prodP p1)
    = contrPCoeff i j hij p := by
  simp only [contrPCoeff, Monoidal.tensorUnit_obj, Functor.comp_obj, Discrete.functor_obj_eq_as,
    Function.comp_apply, prodP_apply_castAdd]
  conv_lhs => erw [S.contr_congr _ ((c i)) (by simp)]
  apply congrArg
  congr 1
  · change (ConcreteCategory.hom (S.FD.map (Discrete.eqToHom _)))
      ((ConcreteCategory.hom (S.FD.map (eqToHom _))) (p i)) = _
    simp [map_map_apply]
  · change (ConcreteCategory.hom (S.FD.map (Discrete.eqToHom _)))
      ((ConcreteCategory.hom (S.FD.map (eqToHom _))) _) = _
    simp [map_map_apply]

set_option backward.isDefEq.respectTransparency false in
lemma Pure.prodP_dropPair {n n1 : ℕ} {c : Fin (n + 1 + 1) → C}
    {c1 : Fin n1 → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j)
    (p : Pure S c) (p1 : Pure S c1) :
    p1.prodP (dropPair i j hij.1 p) = permP id (PermCond.append_right_succSuccAbove i j)
    (dropPair (Fin.natAdd n1 i) (Fin.natAdd n1 j)
    (by simp_all [Fin.ext_iff]) (p1.prodP p)) := by
  ext x
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective x
  rw [prodP_apply_finSumFinEquiv]
  simp only [Function.comp_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, dropPair,
    permP, Nat.add_eq, id_eq]
  match x with
  | Sum.inl x =>
    simp only [finSumFinEquiv_apply_left]
    rw [← congr_right (p1.prodP p) _ (Fin.castAdd (n + 1 + 1) x)
      (by rw [Fin.succSuccAbove_natAdd_apply_castAdd i j])]
    simp [map_map_apply]
  | Sum.inr m =>
    simp only [finSumFinEquiv_apply_right]
    rw [← congr_right (p1.prodP p) _ (Fin.natAdd n1 (i.succSuccAbove j m))
      (by rw [Fin.succSuccAbove_comm_natAdd i j])]
    simp [map_map_apply]

set_option backward.isDefEq.respectTransparency false in
lemma Pure.prodP_contrP_snd {n n1 : ℕ} {c : Fin (n + 1 + 1) → C}
    {c1 : Fin n1 → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j)
    (p : Pure S c) (p1 : Pure S c1) :
    prodT p1.toTensor (contrP i j hij p) =
    ((permT id (PermCond.append_right_succSuccAbove i j)) <|
    contrP
      (finSumFinEquiv (m := n1) (Sum.inr i))
      (finSumFinEquiv (m := n1) (Sum.inr j))
      (by simpa using hij) <|
    prodP p1 p) := by
  simp only [contrP, map_smul, Nat.add_eq, finSumFinEquiv_apply_right]
  rw [contrPCoeff_natAdd i j hij]
  congr 1
  rw [prodT_pure, permT_pure]
  congr
  rw [prodP_dropPair _ _ hij]

set_option backward.isDefEq.respectTransparency false in
lemma prodT_contrT_snd {n n1 : ℕ} {c : Fin (n + 1 + 1) → C}
    {c1 : Fin n1 → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j)
    (t : Tensor S c) (t1 : Tensor S c1) :
    prodT t1 (contrT n i j hij t) =
    ((permT id (PermCond.append_right_succSuccAbove i j)) <|
    contrT _
      (finSumFinEquiv (m := n1) (Sum.inr i))
      (finSumFinEquiv (m := n1) (Sum.inr j))
      (by simpa using hij) <|
    prodT t1 t) := by
  generalize_proofs ha hb hc hd
  let P (t : Tensor S c) (t1 : Tensor S c1) : Prop :=
    prodT t1 (contrT _ i j hij t) =
    ((permT id (PermCond.append_right_succSuccAbove i j)) <|
    contrT _
      (finSumFinEquiv (m := n1) (Sum.inr i))
      (finSumFinEquiv (m := n1) (Sum.inr j)) hc <|
    prodT t1 t)
  let P1 (t : Tensor S c) := P t t1
  change P1 t
  refine induction_on_pure ?_
    (fun r t h1 => by
      dsimp only [P1, P] at h1
      simp only [h1, map_smul, P1, P])
    (fun t1 t2 h1 h2 => by
      dsimp only [P1, P] at h1 h2
      simp only [h1, h2, map_add, P1, P]) t
  intro p
  let P2 (t1 : Tensor S c1) := P p.toTensor t1
  change P2 t1
  refine induction_on_pure ?_
    (fun r t h1 => by
      dsimp only [P1, P, P2] at h1
      simp only [h1, map_smul, LinearMap.smul_apply, P, P2])
    (fun t1 t2 h1 h2 => by
      dsimp only [P1, P, P2] at h1 h2
      simp only [map_add, LinearMap.add_apply, h1, h2, P2, P]) t1
  intro p1
  simp only [Nat.add_eq, finSumFinEquiv_apply_right, contrT_pure, P2, P]
  rw [Pure.prodP_contrP_snd, prodT_pure, contrT_pure]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma contrT_prodT_snd {n n1 : ℕ} {c : Fin (n + 1 + 1) → C}
    {c1 : Fin n1 → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j)
    (t : Tensor S c) (t1 : Tensor S c1) :
    (contrT _ (finSumFinEquiv (m := n1) (Sum.inr i)) (finSumFinEquiv (m := n1) (Sum.inr j))
      (by simpa using hij) <| prodT t1 t) =
    ((permT id (PermCond.on_id_symm (PermCond.append_right_succSuccAbove i j))) <|
      (prodT t1 (contrT n i j hij t))) := by
  rw [prodT_contrT_snd]
  simp

end Tensor

end TensorSpecies
