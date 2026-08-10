/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.Terms.MaxwellTerm
/-!
# The theta term

The topological term `ε^{μνρσ} F_{μν} F_{ρσ}`, the alternating contraction of two
field strengths. Its Lorentz invariance is the statement that the alternating
four-fold contraction of a Lorentz matrix is its determinant, which is one; like
the Maxwell term it has mass weight eight.
-/

@[expose] public section

set_option maxHeartbeats 1000000

namespace LeptonGaugeSector
open TensorProduct StandardModel

namespace JetAlgebra

open scoped minkowskiMatrix PauliMatrix
open Matrix MatrixGroups

/-- The topological theta term `ε^{μνρσ} F_{μν} F_{ρσ}`, written as a sum over
  the permutations of the four spacetime indices weighted by their signs. Mass
  weight eight. -/
noncomputable def thetaTerm : JetAlgebra :=
  ∑ p : Equiv.Perm (Fin 4), (Equiv.Perm.sign p : ℤ) •
    (fieldStrengthDeriv {} ((finSumFinEquiv (m := 1) (n := 3)).symm (p 0))
        ((finSumFinEquiv (m := 1) (n := 3)).symm (p 1)) *
      fieldStrengthDeriv {} ((finSumFinEquiv (m := 1) (n := 3)).symm (p 2))
        ((finSumFinEquiv (m := 1) (n := 3)).symm (p 3)))

lemma repJetGaugeGroupI_thetaTerm (U : JetGaugeGroupI) :
    repJetGaugeGroupI U thetaTerm = thetaTerm := by
  rw [thetaTerm, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_zsmul]
  congr 1
  rw [repJetGaugeGroupI_mul', repJetGaugeGroupI_fieldStrengthDeriv,
    repJetGaugeGroupI_fieldStrengthDeriv]

/-- The transformation law of a product of two field strengths. -/
lemma repLorentzGroup_fieldStrengthDeriv_mul (Λ : SL(2,ℂ))
    (μ ν ρ τ : Fin 1 ⊕ Fin 3) :
    repLorentzGroup Λ (fieldStrengthDeriv {} μ ν * fieldStrengthDeriv {} ρ τ) =
      ∑ a, ∑ b, ∑ a', ∑ b',
        ((((Lorentz.SL2C.toLorentzGroup Λ).1 a μ *
          (Lorentz.SL2C.toLorentzGroup Λ).1 b ν : ℝ) : ℂ) *
          (((Lorentz.SL2C.toLorentzGroup Λ).1 a' ρ *
            (Lorentz.SL2C.toLorentzGroup Λ).1 b' τ : ℝ) : ℂ)) •
        (fieldStrengthDeriv {} a b * fieldStrengthDeriv {} a' b') := by
  rw [repLorentzGroup_apply_mul, repLorentzGroup_fieldStrengthDeriv_nil,
    repLorentzGroup_fieldStrengthDeriv_nil]
  have hsm : ∀ (f : (Fin 1 ⊕ Fin 3) → JetAlgebra) (y : JetAlgebra),
      (∑ x, f x) * y = ∑ x, f x * y := fun f y => by
    rw [show (∑ x, f x) * y = LinearMap.mulRight ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hms : ∀ (f : (Fin 1 ⊕ Fin 3) → JetAlgebra) (y : JetAlgebra),
      y * (∑ x, f x) = ∑ x, y * f x := fun f y => by
    rw [show y * (∑ x, f x) = LinearMap.mulLeft ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hsmul : ∀ (c d : ℂ) (x y : JetAlgebra),
      (c • x) * (d • y) = (c * d) • (x * y) := fun c d x y => by
    rw [smul_mul_smul_comm]
  simp only [hsm, hms, hsmul]

/-- The alternating four-fold contraction of Lorentz matrices is a determinant:
  the combinatorial identity behind the invariance of the theta term. -/
lemma sum_perm_sign_mul_prod_eq_det (Λ : SL(2,ℂ)) (v : Fin 4 → Fin 1 ⊕ Fin 3) :
    (∑ p : Equiv.Perm (Fin 4), ((Equiv.Perm.sign p : ℤ) : ℝ) *
      ∏ i, (Lorentz.SL2C.toLorentzGroup Λ).1 (v i)
        ((finSumFinEquiv (m := 1) (n := 3)).symm (p i))) =
    Matrix.det (Matrix.of fun i j : Fin 4 =>
      (Lorentz.SL2C.toLorentzGroup Λ).1 (v i)
        ((finSumFinEquiv (m := 1) (n := 3)).symm j)) := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  rfl

/-- The alternating contraction matrix of a non-injective index tuple has two
  equal rows, so its determinant vanishes. -/
lemma det_toLorentzGroup_of_not_injective (Λ : SL(2,ℂ)) {v : Fin 4 → Fin 1 ⊕ Fin 3}
    (hv : ¬ Function.Injective v) :
    Matrix.det (Matrix.of fun i j : Fin 4 =>
      (Lorentz.SL2C.toLorentzGroup Λ).1 (v i)
        ((finSumFinEquiv (m := 1) (n := 3)).symm j)) = 0 := by
  rw [Function.not_injective_iff] at hv
  obtain ⟨i, j, hij, hne⟩ := hv
  exact Matrix.det_zero_of_row_eq hne (funext fun k => by simp [hij])

/-- On an index tuple obtained by permuting the four spacetime indices, the
  alternating contraction matrix has determinant the sign of the permutation,
  by `det Λ = 1`. -/
lemma det_toLorentzGroup_comp_perm (Λ : SL(2,ℂ)) (q : Equiv.Perm (Fin 4)) :
    Matrix.det (Matrix.of fun i j : Fin 4 =>
      (Lorentz.SL2C.toLorentzGroup Λ).1
        ((finSumFinEquiv (m := 1) (n := 3)).symm (q i))
        ((finSumFinEquiv (m := 1) (n := 3)).symm j)) =
      ((Equiv.Perm.sign q : ℤ) : ℝ) := by
  have h1 : (Matrix.of fun i j : Fin 4 =>
      (Lorentz.SL2C.toLorentzGroup Λ).1
        ((finSumFinEquiv (m := 1) (n := 3)).symm (q i))
        ((finSumFinEquiv (m := 1) (n := 3)).symm j)) =
      ((Lorentz.SL2C.toLorentzGroup Λ).1.submatrix
        (finSumFinEquiv (m := 1) (n := 3)).symm
        (finSumFinEquiv (m := 1) (n := 3)).symm).submatrix q id := rfl
  rw [h1, Matrix.det_permute,
    Matrix.det_submatrix_equiv_self (finSumFinEquiv (m := 1) (n := 3)).symm,
    Lorentz.SL2C.toLorentzGroup_det_one, mul_one]

set_option maxHeartbeats 4000000 in
/-- Lorentz invariance of the theta term: the alternating contraction is the
  determinant of the Lorentz matrix, which is one. -/
lemma repLorentzGroup_thetaTerm (Λ : SL(2,ℂ)) :
    repLorentzGroup Λ thetaTerm = thetaTerm := by
  classical
  rw [thetaTerm, map_sum]
  conv_lhs => enter [2, p]; rw [map_zsmul, repLorentzGroup_fieldStrengthDeriv_mul]
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  conv_lhs => enter [2, a]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a, 2, b]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a, 2, b, 2, a']; rw [Finset.sum_comm]
  have hdet : ∀ a b a' b' : Fin 1 ⊕ Fin 3,
      (∑ p : Equiv.Perm (Fin 4), (Equiv.Perm.sign p : ℤ) •
        ((((Lorentz.SL2C.toLorentzGroup Λ).1 a
            ((finSumFinEquiv (m := 1) (n := 3)).symm (p 0)) *
          (Lorentz.SL2C.toLorentzGroup Λ).1 b
            ((finSumFinEquiv (m := 1) (n := 3)).symm (p 1)) : ℝ) : ℂ) *
          (((Lorentz.SL2C.toLorentzGroup Λ).1 a'
            ((finSumFinEquiv (m := 1) (n := 3)).symm (p 2)) *
          (Lorentz.SL2C.toLorentzGroup Λ).1 b'
            ((finSumFinEquiv (m := 1) (n := 3)).symm (p 3)) : ℝ) : ℂ)) •
          (fieldStrengthDeriv {} a b * fieldStrengthDeriv {} a' b')) =
      ((Matrix.det (Matrix.of fun i j : Fin 4 =>
        (Lorentz.SL2C.toLorentzGroup Λ).1 (![a, b, a', b'] i)
          ((finSumFinEquiv (m := 1) (n := 3)).symm j)) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} a b * fieldStrengthDeriv {} a' b') := by
    intro a b a' b'
    rw [← sum_perm_sign_mul_prod_eq_det Λ ![a, b, a', b'], Complex.ofReal_sum,
      Finset.sum_smul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Fin.prod_univ_four]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
    rw [← Int.cast_smul_eq_zsmul ℂ, smul_smul]
    congr 1
    push_cast
    ring
  conv_lhs => enter [2, a, 2, b, 2, a', 2, b']; rw [hdet a b a' b']
  have hflat : ∀ (G : (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) →
      (Fin 1 ⊕ Fin 3) → JetAlgebra),
      (∑ a, ∑ b, ∑ a', ∑ b', G a b a' b') =
      ∑ t : (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3),
        G t.1 t.2.1 t.2.2.1 t.2.2.2 := fun G => by
    symm
    simp only [Fintype.sum_prod_type]
  rw [hflat]
  rw [← Finset.sum_filter_of_ne
    (p := fun t : (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) ×
      (Fin 1 ⊕ Fin 3) => Function.Injective ![t.1, t.2.1, t.2.2.1, t.2.2.2])
    (fun t _ hne => by
      by_contra hni
      exact hne (by
        rw [det_toLorentzGroup_of_not_injective Λ hni, Complex.ofReal_zero,
          zero_smul]))]
  have hcard : Fintype.card (Fin 4) = Fintype.card (Fin 1 ⊕ Fin 3) := by simp
  refine Finset.sum_bij
    (i := fun t ht => (Equiv.ofBijective ![t.1, t.2.1, t.2.2.1, t.2.2.2]
      ((Fintype.bijective_iff_injective_and_card _).mpr
        ⟨(Finset.mem_filter.mp ht).2, hcard⟩)).trans
      (finSumFinEquiv (m := 1) (n := 3)))
    ?_ ?_ ?_ ?_
  · intro t ht
    exact Finset.mem_univ _
  · intro t₁ ht₁ t₂ ht₂ h
    have hv : ∀ i : Fin 4, ![t₁.1, t₁.2.1, t₁.2.2.1, t₁.2.2.2] i =
        ![t₂.1, t₂.2.1, t₂.2.2.1, t₂.2.2.2] i := by
      intro i
      have := congrArg (fun q : Equiv.Perm (Fin 4) =>
        (finSumFinEquiv (m := 1) (n := 3)).symm (q i)) h
      simpa using this
    have h0 := hv 0
    have h1 := hv 1
    have h2 := hv 2
    have h3 := hv 3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] at h0 h1 h2 h3
    exact Prod.ext h0 (Prod.ext h1 (Prod.ext h2 h3))
  · intro q _
    refine ⟨((finSumFinEquiv (m := 1) (n := 3)).symm (q 0),
      (finSumFinEquiv (m := 1) (n := 3)).symm (q 1),
      (finSumFinEquiv (m := 1) (n := 3)).symm (q 2),
      (finSumFinEquiv (m := 1) (n := 3)).symm (q 3)), ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have hveq : ![(finSumFinEquiv (m := 1) (n := 3)).symm (q 0),
          (finSumFinEquiv (m := 1) (n := 3)).symm (q 1),
          (finSumFinEquiv (m := 1) (n := 3)).symm (q 2),
          (finSumFinEquiv (m := 1) (n := 3)).symm (q 3)] =
          fun i => (finSumFinEquiv (m := 1) (n := 3)).symm (q i) := by
        funext i
        fin_cases i <;> rfl
      rw [hveq]
      exact ((finSumFinEquiv (m := 1) (n := 3)).symm.injective).comp q.injective
    · refine Equiv.ext fun i => ?_
      show (finSumFinEquiv (m := 1) (n := 3))
        (![(finSumFinEquiv (m := 1) (n := 3)).symm (q 0),
          (finSumFinEquiv (m := 1) (n := 3)).symm (q 1),
          (finSumFinEquiv (m := 1) (n := 3)).symm (q 2),
          (finSumFinEquiv (m := 1) (n := 3)).symm (q 3)] i) = q i
      fin_cases i <;> simp
  · intro t ht
    have hq : ∀ i : Fin 4, (finSumFinEquiv (m := 1) (n := 3)).symm
        (((Equiv.ofBijective ![t.1, t.2.1, t.2.2.1, t.2.2.2]
          ((Fintype.bijective_iff_injective_and_card _).mpr
            ⟨(Finset.mem_filter.mp ht).2, hcard⟩)).trans
          (finSumFinEquiv (m := 1) (n := 3))) i) =
        ![t.1, t.2.1, t.2.2.1, t.2.2.2] i := by
      intro i
      simp [Equiv.ofBijective]
    have hmat : (Matrix.of fun i j : Fin 4 =>
        (Lorentz.SL2C.toLorentzGroup Λ).1 (![t.1, t.2.1, t.2.2.1, t.2.2.2] i)
          ((finSumFinEquiv (m := 1) (n := 3)).symm j)) =
        (Matrix.of fun i j : Fin 4 =>
        (Lorentz.SL2C.toLorentzGroup Λ).1
          ((finSumFinEquiv (m := 1) (n := 3)).symm
            (((Equiv.ofBijective ![t.1, t.2.1, t.2.2.1, t.2.2.2]
              ((Fintype.bijective_iff_injective_and_card _).mpr
                ⟨(Finset.mem_filter.mp ht).2, hcard⟩)).trans
              (finSumFinEquiv (m := 1) (n := 3))) i))
          ((finSumFinEquiv (m := 1) (n := 3)).symm j)) := by
      refine congrArg Matrix.of (funext fun i => funext fun j => ?_)
      rw [hq i]
    rw [hmat, det_toLorentzGroup_comp_perm]
    have h0 := hq 0
    have h1 := hq 1
    have h2 := hq 2
    have h3 := hq 3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] at h0 h1 h2 h3
    rw [h0, h1, h2, h3, ← Int.cast_smul_eq_zsmul ℂ]
    module

lemma thetaTerm_mem_massWeightLESubmodule :
    thetaTerm ∈ MassWeightLESubmodule 8 := by
  rw [thetaTerm]
  refine Submodule.sum_mem _ fun p _ => zsmul_mem ?_ _
  exact mem_massWeightLESubmodule_of_forall_massWeightScale (m := 4 + 4) le_rfl
    (massWeightScale_mul_eigen (m := 4) (n := 4)
      (fun c => massWeightScale_fieldStrengthDeriv c {} _ _)
      (fun c => massWeightScale_fieldStrengthDeriv c {} _ _))

set_option maxHeartbeats 8000000 in
set_option linter.unusedSimpArgs false in
/-- The theta term as an explicit combination of the three pair-partition
  products of field strengths. -/
lemma thetaTerm_eq : thetaTerm =
    (8 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2))
    + (-8 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2))
    + (8 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) := by
  have hnm : ∀ u v : JetAlgebra, (-u) * v = -(u * v) := by grind
  have hmn : ∀ u v : JetAlgebra, u * (-v) = -(u * v) := by grind
  rw [thetaTerm]
  conv_lhs =>
    enter [2, p]
    rw [show (1 : Fin 4) = (0 : Fin 3).succ from rfl,
      show (2 : Fin 4) = (1 : Fin 3).succ from rfl,
      show (3 : Fin 4) = (2 : Fin 3).succ from rfl]
  rw [Finset.univ_perm_fin_succ, Finset.sum_map, Fintype.sum_prod_type]
  conv_lhs =>
    enter [2, i]
    rw [Finset.univ_perm_fin_succ, Finset.sum_map, Fintype.sum_prod_type]
  conv_lhs =>
    enter [2, i, 2, j]
    rw [Finset.univ_perm_fin_succ, Finset.sum_map, Fintype.sum_prod_type]
  conv_lhs =>
    enter [2, i, 2, j, 2, k]
    rw [Fintype.sum_subsingleton _ (1 : Equiv.Perm (Fin 1))]
  simp only [Equiv.coe_toEmbedding, Fin.sum_univ_four, Fin.sum_univ_three,
    Fin.sum_univ_two,
    show ((1 : Fin 3)) = (0 : Fin 2).succ from rfl,
    show ((2 : Fin 3)) = (1 : Fin 2).succ from rfl,
    Equiv.Perm.decomposeFin_symm_of_one,
    Equiv.Perm.decomposeFin.symm_sign,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one,
    Equiv.Perm.decomposeFin_symm_apply_succ]
  simp only [show ((0 : Fin 2).succ) = (1 : Fin 3) from rfl,
    show ((1 : Fin 2).succ) = (2 : Fin 3) from rfl,
    show ((0 : Fin 3).succ) = (1 : Fin 4) from rfl,
    show ((1 : Fin 3).succ) = (2 : Fin 4) from rfl,
    show ((2 : Fin 3).succ) = (3 : Fin 4) from rfl,
    Equiv.swap_self, Equiv.Perm.sign_refl, Equiv.refl_apply, Equiv.Perm.sign_one,
    Equiv.swap_apply_left, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne,
    Equiv.Perm.sign_swap', Fin.reduceEq, reduceIte, ne_eq, not_false_iff,
    show ((finSumFinEquiv (m := 1) (n := 3)).symm 0) = Sum.inl 0 from rfl,
    show ((finSumFinEquiv (m := 1) (n := 3)).symm 1) = Sum.inr 0 from rfl,
    show ((finSumFinEquiv (m := 1) (n := 3)).symm 2) = Sum.inr 1 from rfl,
    show ((finSumFinEquiv (m := 1) (n := 3)).symm 3) = Sum.inr 2 from rfl,
    Units.val_one, Units.val_neg, one_smul, neg_smul, one_mul, mul_one]
  simp only [
    show fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) =
      -fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) from
      fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 0),
    show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) =
      -fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) from
      fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 1),
    show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) =
      -fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) from
      fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 2),
    show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) =
      -fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) from
      fieldStrengthDeriv_antisymm {} (Sum.inr 0) (Sum.inr 1),
    show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) =
      -fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) from
      fieldStrengthDeriv_antisymm {} (Sum.inr 0) (Sum.inr 2),
    show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) =
      -fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) from
      fieldStrengthDeriv_antisymm {} (Sum.inr 1) (Sum.inr 2),
    hnm, hmn, neg_neg]
  simp only [
    show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) =
      fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) from
      fieldStrengthDeriv_mul_comm {} {} _ _ _ _,
    show fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) =
      fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) from
      fieldStrengthDeriv_mul_comm {} {} _ _ _ _,
    show fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) =
      fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) from
      fieldStrengthDeriv_mul_comm {} {} _ _ _ _]
  module

end JetAlgebra

end LeptonGaugeSector
