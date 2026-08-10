/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.FieldStrength
/-!
# The total spacetime derivative on the lepton–gauge-sector jet algebra

The formal total derivative `∂_μ`, the Leibniz extension of the total
derivatives of the B-boson and charged-lepton factors, together with its action
on the generators and its commutation relations.
-/

@[expose] public section


namespace LeptonGaugeSector
open TensorProduct StandardModel

namespace JetAlgebra

/-!

## Jet derivatives

The formal total spacetime derivative `∂_μ` on the lepton–gauge-sector jet algebra: the Leibniz
extension of the total derivatives of the two factors. Both factor derivatives
are even derivations, so the total derivative is an even derivation on the full
jet algebra, with no Koszul signs.

-/

/-- The formal total spacetime derivative on the lepton–gauge-sector jet algebra in the
  direction `μ`: the Leibniz extension of the total derivatives of the B-boson
  and charged-lepton factors. -/
noncomputable def jetDeriv (μ : Fin 1 ⊕ Fin 3) : JetAlgebra →ₗ[ℂ] JetAlgebra :=
  TensorProduct.map (LinearMap.baseChange ℂ (BBoson.JetAlgebra.jetDeriv μ)) LinearMap.id +
    TensorProduct.map LinearMap.id (LeptonSinglet.JetAlgebra.jetDeriv μ)

lemma jetDeriv_tmul (μ : Fin 1 ⊕ Fin 3) (p : ℂ ⊗[ℝ] BBoson.JetAlgebra)
    (l : LeptonSinglet.JetAlgebra) :
    jetDeriv μ (p ⊗ⱼ l) =
      (LinearMap.baseChange ℂ (BBoson.JetAlgebra.jetDeriv μ) p) ⊗ⱼ l +
        p ⊗ⱼ LeptonSinglet.JetAlgebra.jetDeriv μ l := rfl

@[simp]
lemma jetDeriv_one (μ : Fin 1 ⊕ Fin 3) : jetDeriv μ (1 : JetAlgebra) = 0 := by
  have hB : LinearMap.baseChange ℂ (BBoson.JetAlgebra.jetDeriv μ)
      (1 : ℂ ⊗[ℝ] BBoson.JetAlgebra) = 0 := by
    rw [show (1 : ℂ ⊗[ℝ] BBoson.JetAlgebra) = (1 : ℂ) ⊗ₜ[ℝ] (1 : BBoson.JetAlgebra) from rfl,
      LinearMap.baseChange_tmul, BBoson.JetAlgebra.jetDeriv_one, TensorProduct.tmul_zero]
  rw [one_eq_tmul, jetDeriv_tmul, hB, LeptonSinglet.JetAlgebra.jetDeriv_one, zero_tmul,
    tmul_zero, add_zero]

/-- The total derivative is an even derivation on the lepton–gauge-sector jet algebra: the
  Leibniz rule holds with no Koszul signs. -/
lemma jetDeriv_mul (μ : Fin 1 ⊕ Fin 3) (x y : JetAlgebra) :
    jetDeriv μ (x * y) = jetDeriv μ x * y + x * jetDeriv μ y := by
  induction x using JetAlgebra.induction_on with
  | zero => simp
  | add a b ha hb =>
    simp only [add_mul, map_add, ha, hb]
    abel
  | tmul p l =>
    induction y using JetAlgebra.induction_on with
    | zero => simp
    | add a' b' ha' hb' =>
      simp only [mul_add, map_add, ha', hb']
      abel
    | tmul p' l' =>
      simp only [tmul_mul_tmul, jetDeriv_tmul,
        BBoson.JetAlgebra.jetDeriv_baseChange_mul, LeptonSinglet.JetAlgebra.jetDeriv_mul,
        ← tmul_add_tmul_left, ← tmul_add_tmul_right, add_mul, mul_add, tmul_mul_tmul]
      abel

lemma jetDeriv_comm (μ ν : Fin 1 ⊕ Fin 3) (x : JetAlgebra) :
    jetDeriv μ (jetDeriv ν x) = jetDeriv ν (jetDeriv μ x) := by
  induction x using JetAlgebra.induction_on with
  | zero => simp
  | add a b ha hb =>
    simp only [map_add, ha, hb]
  | tmul p l =>
    simp only [jetDeriv_tmul, map_add, LeptonSinglet.JetAlgebra.jetDeriv_comm μ ν,
      BBoson.JetAlgebra.jetDeriv_baseChange_comm μ ν p]
    abel

/-- Total derivatives commute, so an iterated derivative may be indexed by a
  multiset of directions rather than by a list. -/
instance : LeftCommutative
    (fun (ν : Fin 1 ⊕ Fin 3) (A : JetAlgebra →ₗ[ℂ] JetAlgebra) =>
      jetDeriv ν ∘ₗ A) where
  left_comm ν₁ ν₂ A := by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply]
    exact jetDeriv_comm ν₁ ν₂ (A x)

/-!

## Jet derivatives over a multiset.


-/
/-- The iterated total spacetime derivative along a multiset of directions:
  `∂_t = ∂_{μ₁} ⋯ ∂_{μ_k}` for `t = {μ₁, …, μ_k}`. The order is immaterial by
  `jetDeriv_comm`, so the index is a multiset. -/
noncomputable def jetDerivM (t : Multiset (Fin 1 ⊕ Fin 3)) :
    JetAlgebra →ₗ[ℂ] JetAlgebra :=
  Multiset.foldr (fun ν A => jetDeriv ν ∘ₗ A) LinearMap.id t

@[simp]
lemma jetDerivM_zero : jetDerivM 0 = LinearMap.id := by
  simp [jetDerivM]

lemma jetDerivM_cons (ν : Fin 1 ⊕ Fin 3) (t : Multiset (Fin 1 ⊕ Fin 3)) :
    jetDerivM (ν ::ₘ t) = jetDeriv ν ∘ₗ jetDerivM t := by
  simp [jetDerivM]

lemma jetDerivM_singleton (μ : Fin 1 ⊕ Fin 3) : jetDerivM {μ} = jetDeriv μ := by
  rw [show ({μ} : Multiset (Fin 1 ⊕ Fin 3)) = μ ::ₘ 0 from rfl, jetDerivM_cons,
    jetDerivM_zero, LinearMap.comp_id]

lemma jetDerivM_add (s t : Multiset (Fin 1 ⊕ Fin 3)) :
    jetDerivM (s + t) = jetDerivM s ∘ₗ jetDerivM t := by
  induction s using Multiset.induction_on with
  | empty => simp [jetDerivM_zero]
  | cons μ s ih =>
    trans jetDerivM (μ ::ₘ (s + t))
    · simp
    simp only [jetDerivM_cons, ih]
    exact Eq.symm (LinearMap.comp_assoc (jetDerivM t) (jetDerivM s) (jetDeriv μ))

lemma jetDerivM_cons' (ν : Fin 1 ⊕ Fin 3) (t : Multiset (Fin 1 ⊕ Fin 3)) :
    jetDerivM (ν ::ₘ t) = jetDerivM t ∘ₗ jetDeriv ν := by
  trans jetDerivM (t + {ν})
  · congr
    rw [add_comm]
    simp
  · rw [jetDerivM_add, jetDerivM_singleton]

lemma jetDerivM_jetDerivM (s t : Multiset (Fin 1 ⊕ Fin 3)) (x : JetAlgebra) :
    jetDerivM t (jetDerivM s x) = jetDerivM (t + s) x := by
  rw [jetDerivM_add]
  simp

lemma jetDerivM_jetDeriv (μ : Fin 1 ⊕ Fin 3) (t : Multiset (Fin 1 ⊕ Fin 3))
    (a : JetAlgebra) :
    jetDerivM t (jetDeriv μ a) = jetDerivM (μ ::ₘ t) a := by
  trans (jetDerivM t ∘ₗ jetDeriv μ) a
  · rfl
  rw [← jetDerivM_cons']

lemma jetDeriv_jetDerivM (μ : Fin 1 ⊕ Fin 3) (t : Multiset (Fin 1 ⊕ Fin 3))
    (a : JetAlgebra) :
    jetDeriv μ (jetDerivM t a) = jetDerivM (μ ::ₘ t) a := by
  trans (jetDeriv μ ∘ₗ jetDerivM t) a
  · rfl
  rw [← jetDerivM_cons]

lemma ofGenerator_dB_eq_jetDerivM (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) :
    [JetGenerators.dB s μ]ₐ = jetDerivM s [.dB 0 μ]ₐ := by
  induction s using Multiset.induction_on with
  | empty => rw [jetDerivM_zero, LinearMap.id_coe, id_eq]
  | cons ν t ih =>
    rw [jetDerivM_cons, LinearMap.comp_apply, ← ih]
    simp only [ofGenerator]
    rw [jetDeriv_tmul, LinearMap.baseChange_tmul]
    simp only [LeptonSinglet.JetAlgebra.jetDeriv_one, tmul_zero,
      zero_add, BBoson.JetAlgebra.jetDeriv_ofGenerator, BBoson.JetGenerators.shift_dB]
    congr 2
    rw [add_comm, Multiset.singleton_add]

lemma jetDerivM_apply_mul_eq_powerset_sum (t : Multiset (Fin 1 ⊕ Fin 3)) (x y : JetAlgebra) :
    jetDerivM t (x * y) = (t.powerset.map fun s => jetDerivM s x * jetDerivM (t - s) y).sum := by
  induction t using Multiset.induction_on with
  | empty =>
    simp only [jetDerivM_zero, LinearMap.id_coe, id_eq, Multiset.powerset_zero, zero_tsub,
      Multiset.map_singleton, Multiset.sum_singleton]
  | cons ν t ih =>
    calc _
      _ = jetDeriv ν (jetDerivM t (x * y)) := by simp [jetDerivM_cons]
      _ = jetDeriv ν ((t.powerset.map fun s => jetDerivM s x * jetDerivM (t - s) y).sum) := by
        congr
      _ = (t.powerset.map (jetDeriv ν  ∘ fun s => (jetDerivM s x * jetDerivM (t - s) y))).sum := by
       rw [← Multiset.map_map]
       exact map_multiset_sum (jetDeriv ν) _
      _ = (t.powerset.map (fun s => jetDeriv ν (jetDerivM s x * jetDerivM (t - s) y))).sum := by
        rfl
      _ =  (t.powerset.map (fun s => jetDeriv ν (jetDerivM s x) * jetDerivM (t - s) y
          + jetDerivM s x * jetDeriv ν (jetDerivM (t - s) y))).sum := by
        simp [jetDeriv_mul]
      _ = (t.powerset.map (fun s => jetDeriv ν (jetDerivM s x) * jetDerivM (t - s) y)).sum +
          (t.powerset.map (fun s => jetDerivM s x * jetDeriv ν (jetDerivM (t - s) y))).sum := by
        exact Multiset.sum_map_add
      _ =  (t.powerset.map (fun s => jetDerivM s x * jetDeriv ν (jetDerivM (t - s) y))).sum
        + (t.powerset.map (fun s => jetDeriv ν (jetDerivM s x) * jetDerivM (t - s) y)).sum
         := by abel
    conv_rhs => rw [Multiset.powerset_cons]
    simp only [Multiset.map_add, Multiset.map_map, Function.comp_apply, Multiset.sub_cons,
      Multiset.erase_cons_head, Multiset.sum_add]
    congr 1
    · congr 1
      apply Multiset.map_congr (by rfl)
      intro s hs
      rw [jetDeriv_jetDerivM]
      congr
      exact (Multiset.cons_sub_of_le ν (Multiset.mem_powerset.mp hs)).symm
    · congr
      funext s
      simp [jetDeriv_jetDerivM]

lemma jetDerivM_apply_mul (s : Multiset (Fin 1 ⊕ Fin 3)) (x y : JetAlgebra) :
    jetDerivM s (x * y) = ∑ p ∈ Finset.antidiagonal (Multiset.toFinsupp s),
        ((∏ ν, (Multiset.toFinsupp s ν).choose (p.1 ν) : ℕ) : ℂ) •
          (jetDerivM (Finsupp.toMultiset p.1) x * jetDerivM (Finsupp.toMultiset p.2) y) := by
  have hcount : ∀ u t : Multiset (Fin 1 ⊕ Fin 3), Multiset.count t u.powerset =
      ∏ ν, (Multiset.count ν u).choose (Multiset.count ν t) := by
    intro u
    induction u using Multiset.induction_on with
    | empty =>
      intro t
      rcases eq_or_ne t 0 with rfl | h
      · simp
      · obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero h
        rw [Finset.prod_eq_zero (Finset.mem_univ a)]
        · simp [h]
        · simp [Nat.choose_eq_zero_of_lt, Multiset.count_pos.mpr ha]
    | cons a u ih =>
      intro t
      rw [Multiset.powerset_cons, Multiset.count_add]
      by_cases ha : a ∈ t
      · obtain ⟨m, hm⟩ : ∃ m, Multiset.count a t = m + 1 :=
          ⟨Multiset.count a t - 1, by have := Multiset.count_pos.mpr ha; omega⟩
        have h2 : Multiset.count t (u.powerset.map (Multiset.cons a)) =
            Multiset.count (t.erase a) u.powerset := by
          conv_lhs => rw [← Multiset.cons_erase ha]
          exact Multiset.count_map_eq_count' _ _ (fun v w h => by simpa using h) _
        have hQ : ∀ ν ∈ Finset.univ.erase a,
            (Multiset.count ν u).choose (Multiset.count ν (t.erase a)) =
            (Multiset.count ν u).choose (Multiset.count ν t) := fun ν hν => by
          rw [Multiset.count_erase_of_ne (Finset.mem_erase.mp hν).1]
        have hR : ∀ ν ∈ Finset.univ.erase a,
            (Multiset.count ν (a ::ₘ u)).choose (Multiset.count ν t) =
            (Multiset.count ν u).choose (Multiset.count ν t) := fun ν hν => by
          rw [Multiset.count_cons_of_ne (Finset.mem_erase.mp hν).1]
        rw [h2, ih t, ih (t.erase a)]
        simp only [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a)]
        rw [Finset.prod_congr rfl hQ, Finset.prod_congr rfl hR, ← add_mul,
          Multiset.count_erase_self, Multiset.count_cons_self, hm, Nat.add_sub_cancel,
          Nat.choose_succ_succ']
        ring
      · have h2 : Multiset.count t (u.powerset.map (Multiset.cons a)) = 0 :=
          Multiset.count_eq_zero.mpr fun h => by
            obtain ⟨v, _, rfl⟩ := Multiset.mem_map.mp h
            exact ha (Multiset.mem_cons_self a v)
        rw [h2, ih t, add_zero]
        refine Finset.prod_congr rfl fun ν _ => ?_
        rcases eq_or_ne ν a with rfl | hν
        · simp [Multiset.count_eq_zero.mpr ha]
        · rw [Multiset.count_cons_of_ne hν]
  have hsum : ∀ p ∈ Finset.antidiagonal (Multiset.toFinsupp s),
      Finsupp.toMultiset p.1 + Finsupp.toMultiset p.2 = s := fun p hp => by
    rw [← map_add, Finset.mem_antidiagonal.mp hp, Multiset.toFinsupp_toMultiset]
  rw [jetDerivM_apply_mul_eq_powerset_sum, Finset.sum_multiset_map_count]
  refine Finset.sum_nbij' (fun t => (Multiset.toFinsupp t, Multiset.toFinsupp (s - t)))
    (fun p => Finsupp.toMultiset p.1) (fun t ht => ?_) (fun p hp => ?_)
    (fun t _ => Multiset.toFinsupp_toMultiset t) (fun p hp => ?_) (fun t _ => ?_)
  · rw [Finset.mem_antidiagonal, ← map_add, add_tsub_cancel_of_le (by simpa using ht)]
  · simpa using Multiset.le_iff_exists_add.mpr ⟨Finsupp.toMultiset p.2, (hsum p hp).symm⟩
  · refine Prod.ext (Finsupp.toMultiset_toFinsupp p.1) ?_
    rw [← hsum p hp, add_tsub_cancel_left]
    exact Finsupp.toMultiset_toFinsupp p.2
  · simp only [Multiset.toFinsupp_apply, Multiset.toFinsupp_toMultiset, hcount]
    exact (Nat.cast_smul_eq_nsmul ℂ _ _).symm
end JetAlgebra

end LeptonGaugeSector
