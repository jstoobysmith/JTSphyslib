/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.QED.JetAlgebra.Invariants.Decomposition
/-!
# The neutral sectors of weight at most eight

The charge-zero covariant monomials of weight four are the field strengths
`F_{μν}`, of weight six the derivatives `∂_ρ F_{μν}` and the fermion pairs
`ψ̄_α ψ_β`, and of weight eight the products `F F`, the second derivatives
`∂_ρ ∂_τ F_{μν}`, and the one-derivative fermion pairs
(`chargeCovSpan_four_le`, `chargeCovSpan_six_le`, `chargeCovSpan_eight_le`).

Averaging over the Klein four-group of parity rotations kills the weight-four
sector outright, and combining it with the trace-free kill operator `sixKill`
kills the weight-six sector. The file closes with the four invariants written
out in the monomial basis, which is what the weight-eight analysis consumes.
-/

@[expose] public section

set_option maxHeartbeats 1000000

namespace QED
open TensorProduct StandardModel

namespace JetAlgebra

open scoped minkowskiMatrix PauliMatrix
open Matrix MatrixGroups

/-!

## The Lorentz analysis of the neutral sectors

TODO: the remaining sector lemmas. The charge-zero covariant monomials of
weight four are the field strengths `F_{μν}`, of weight six the derivatives
`∂_ρ F_{μν}` and the fermion pairs `ψ̄_α ψ_β`, of weight eight the products
`F F`, the second derivatives `∂_ρ ∂_τ F_{μν}`, and the one-derivative fermion
pairs. Lorentz invariance kills the weight-four and weight-six sectors and
reduces the weight-eight sector to the span of the Maxwell term, the theta
term, and the two fermion kinetic terms.

-/

/-- Each invariant generator is a weight eigenvector of weight at least
  three. -/
lemma exists_weight_of_mem_invariantGenerators {g : JetAlgebra}
    (hg : g ∈ invariantGenerators) :
    ∃ w, 3 ≤ w ∧ ∀ c : ℂ, massWeightScale c g = c ^ w • g := by
  rcases hg with (⟨p, rfl⟩ | ⟨p, rfl⟩) | ⟨p, rfl⟩
  · exact ⟨4 + 2 * Multiset.card p.1, by omega,
      fun c => massWeightScale_fieldStrengthDeriv c p.1 p.2.1 p.2.2⟩
  · exact ⟨3 + 2 * p.1.length, by omega, fun c => massWeightScale_Dψ c p.1 p.2⟩
  · exact ⟨3 + 2 * p.1.length, by omega, fun c => massWeightScale_Dbarψ c p.1 p.2⟩

/-- The product of a list of invariant generators is a weight eigenvector of
  weight at least three times the length. -/
lemma exists_weight_of_list_prod {l : List JetAlgebra}
    (hl : ∀ g ∈ l, g ∈ invariantGenerators) :
    ∃ w, 3 * l.length ≤ w ∧
      ∀ c : ℂ, massWeightScale c l.prod = c ^ w • l.prod := by
  induction l with
  | nil =>
    exact ⟨0, by simp, fun c => by
      rw [List.prod_nil, pow_zero, one_smul]
      exact (massWeightScale c).map_one⟩
  | cons g l ih =>
    obtain ⟨wg, hwg3, hwg⟩ := exists_weight_of_mem_invariantGenerators
      (hl g List.mem_cons_self)
    obtain ⟨wl, hwl3, hwl⟩ := ih fun x hx => hl x (List.mem_cons_of_mem g hx)
    refine ⟨wg + wl, by simp only [List.length_cons]; omega, fun c => ?_⟩
    rw [List.prod_cons]
    exact massWeightScale_mul_eigen hwg hwl c

/-- The constant gauge character of a product of two lepton factors: charge
  two. -/
lemma rep_ofConstant_Dψ_mul_Dψ (g : GaugeGroupI) (l l' : List (Fin 1 ⊕ Fin 3))
    (α β : Fin 2) :
    repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) (Dψ l α * Dψ l' β) =
      ((g.2.2 : ℂ)) ^ (6 * (2 : ℤ)) • (Dψ l α * Dψ l' β) := by
  rw [repJetGaugeGroupI_mul', repJetGaugeGroupI_Dψ, repJetGaugeGroupI_Dψ,
    JetGaugeGroupI.eval_ofConstant, Submonoid.smul_def, Submonoid.smul_def,
    SubmonoidClass.coe_pow, smul_mul_smul_comm, ← pow_add,
    show (6 * (2 : ℤ)) = ((12 : ℕ) : ℤ) from rfl, zpow_natCast]

/-- The constant gauge character of a product of two conjugate lepton factors:
  charge minus two. -/
lemma rep_ofConstant_Dbarψ_mul_Dbarψ (g : GaugeGroupI)
    (l l' : List (Fin 1 ⊕ Fin 3)) (α β : Fin 2) :
    repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) (Dbarψ l α * Dbarψ l' β) =
      ((g.2.2 : ℂ)) ^ (6 * (-2 : ℤ)) • (Dbarψ l α * Dbarψ l' β) := by
  have hinv : star ((g.2.2 : ℂ)) = ((g.2.2 : ℂ))⁻¹ :=
    eq_inv_of_mul_eq_one_left (Unitary.mem_iff.mp (g.2.2).2).1
  rw [repJetGaugeGroupI_mul', repJetGaugeGroupI_Dbarψ, repJetGaugeGroupI_Dbarψ,
    JetGaugeGroupI.eval_ofConstant, Submonoid.smul_def, Submonoid.smul_def,
    SubmonoidClass.coe_pow, Unitary.coe_star, smul_mul_smul_comm, ← pow_add,
    hinv, inv_pow, show (6 + 6 : ℕ) = 12 from rfl,
    show (6 * (-2 : ℤ)) = -((12 : ℕ) : ℤ) from rfl, _root_.zpow_neg, zpow_natCast]

/-- The weight-four neutral sector: spanned by the embedded field strengths. -/
lemma chargeCovSpan_four_le :
    chargeCovSpan 4 0 ≤ Submodule.span ℂ
      (Set.range fun p : (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) =>
        fieldStrengthDeriv {} p.1 p.2) := by
  rw [chargeCovSpan, Submodule.span_le]
  rintro y ⟨hy1, hy2, -⟩
  obtain ⟨l, hl, hprod⟩ := Submonoid.exists_list_of_mem_closure hy1
  subst hprod
  rcases l with _ | ⟨g, _ | ⟨g', t⟩⟩
  · rw [List.prod_nil] at hy2 ⊢
    rw [eq_zero_of_eigen_ne (m := 0)
      (fun c => by rw [pow_zero, one_smul]; exact (massWeightScale c).map_one)
      hy2 (by omega)]
    exact Submodule.zero_mem _
  · rw [List.prod_cons, List.prod_nil, mul_one] at hy2 ⊢
    rcases hl g List.mem_cons_self with (⟨p, rfl⟩ | ⟨p, rfl⟩) | ⟨p, rfl⟩ <;>
      dsimp only at hy2 ⊢
    · by_cases hcard : Multiset.card p.1 = 0
      · rw [Multiset.card_eq_zero.mp hcard]
        exact Submodule.subset_span ⟨(p.2.1, p.2.2), rfl⟩
      · rw [eq_zero_of_eigen_ne
          (fun c => massWeightScale_fieldStrengthDeriv c p.1 p.2.1 p.2.2) hy2
          (by omega)]
        exact Submodule.zero_mem _
    · rw [eq_zero_of_eigen_ne (fun c => massWeightScale_Dψ c p.1 p.2) hy2
        (by omega)]
      exact Submodule.zero_mem _
    · rw [eq_zero_of_eigen_ne (fun c => massWeightScale_Dbarψ c p.1 p.2) hy2
        (by omega)]
      exact Submodule.zero_mem _
  · obtain ⟨w, hw, hweig⟩ := exists_weight_of_list_prod hl
    rw [eq_zero_of_eigen_ne hweig hy2 (by
      simp only [List.length_cons] at hw
      omega)]
    exact Submodule.zero_mem _

set_option maxHeartbeats 4000000 in
/-- The weight-six neutral sector: spanned by the first derivatives of the
  field strength and the zero-derivative lepton pairs. -/
lemma chargeCovSpan_six_le :
    chargeCovSpan 6 0 ≤ Submodule.span ℂ
      ((Set.range fun p : (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) =>
        fieldStrengthDeriv {p.1} p.2.1 p.2.2) ∪
      (Set.range fun p : Fin 2 × Fin 2 => Dbarψ [] p.1 * Dψ [] p.2) ∪
      (Set.range fun p : Fin 2 × Fin 2 => Dψ [] p.1 * Dbarψ [] p.2)) := by
  rw [chargeCovSpan, Submodule.span_le]
  rintro y ⟨hy1, hy2, hy3⟩
  simp only [mul_zero, zpow_zero, one_smul] at hy3
  obtain ⟨l, hl, hprod⟩ := Submonoid.exists_list_of_mem_closure hy1
  subst hprod
  rcases l with _ | ⟨g, _ | ⟨g', _ | ⟨g'', t⟩⟩⟩
  · rw [List.prod_nil] at hy2 ⊢
    rw [eq_zero_of_eigen_ne (m := 0)
      (fun c => by rw [pow_zero, one_smul]; exact (massWeightScale c).map_one)
      hy2 (by omega)]
    exact Submodule.zero_mem _
  · rw [List.prod_cons, List.prod_nil, mul_one] at hy2 ⊢
    rcases hl g List.mem_cons_self with (⟨p, rfl⟩ | ⟨p, rfl⟩) | ⟨p, rfl⟩ <;>
      dsimp only at hy2 ⊢
    · by_cases hcard : Multiset.card p.1 = 1
      · obtain ⟨ρ, hρ⟩ := Multiset.card_eq_one.mp hcard
        rw [hρ]
        exact Submodule.subset_span (Or.inl (Or.inl ⟨(ρ, p.2.1, p.2.2), rfl⟩))
      · rw [eq_zero_of_eigen_ne
          (fun c => massWeightScale_fieldStrengthDeriv c p.1 p.2.1 p.2.2) hy2
          (by omega)]
        exact Submodule.zero_mem _
    · rw [eq_zero_of_eigen_ne (fun c => massWeightScale_Dψ c p.1 p.2) hy2
        (by omega)]
      exact Submodule.zero_mem _
    · rw [eq_zero_of_eigen_ne (fun c => massWeightScale_Dbarψ c p.1 p.2) hy2
        (by omega)]
      exact Submodule.zero_mem _
  · rw [List.prod_cons, List.prod_cons, List.prod_nil, mul_one] at hy2 hy3 ⊢
    rcases hl g List.mem_cons_self with (⟨p, rfl⟩ | ⟨p, rfl⟩) | ⟨p, rfl⟩ <;>
      rcases hl g' (List.mem_cons_of_mem _ List.mem_cons_self) with
        (⟨q, rfl⟩ | ⟨q, rfl⟩) | ⟨q, rfl⟩ <;>
      dsimp only at hy2 hy3 ⊢
    · rw [eq_zero_of_eigen_ne (massWeightScale_mul_eigen
        (fun c => massWeightScale_fieldStrengthDeriv c p.1 p.2.1 p.2.2)
        (fun c => massWeightScale_fieldStrengthDeriv c q.1 q.2.1 q.2.2)) hy2
        (by omega)]
      exact Submodule.zero_mem _
    · rw [eq_zero_of_eigen_ne (massWeightScale_mul_eigen
        (fun c => massWeightScale_fieldStrengthDeriv c p.1 p.2.1 p.2.2)
        (fun c => massWeightScale_Dψ c q.1 q.2)) hy2 (by omega)]
      exact Submodule.zero_mem _
    · rw [eq_zero_of_eigen_ne (massWeightScale_mul_eigen
        (fun c => massWeightScale_fieldStrengthDeriv c p.1 p.2.1 p.2.2)
        (fun c => massWeightScale_Dbarψ c q.1 q.2)) hy2 (by omega)]
      exact Submodule.zero_mem _
    · rw [eq_zero_of_eigen_ne (massWeightScale_mul_eigen
        (fun c => massWeightScale_Dψ c p.1 p.2)
        (fun c => massWeightScale_fieldStrengthDeriv c q.1 q.2.1 q.2.2)) hy2
        (by omega)]
      exact Submodule.zero_mem _
    · rw [eq_zero_of_charge_ne_zero (k := 2) (by omega)
        (fun gc => rep_ofConstant_Dψ_mul_Dψ gc p.1 q.1 p.2 q.2) hy3]
      exact Submodule.zero_mem _
    · by_cases hlen : p.1.length = 0 ∧ q.1.length = 0
      · rw [List.length_eq_zero_iff.mp hlen.1, List.length_eq_zero_iff.mp hlen.2]
        exact Submodule.subset_span (Or.inr ⟨(p.2, q.2), rfl⟩)
      · rw [eq_zero_of_eigen_ne (massWeightScale_mul_eigen
          (fun c => massWeightScale_Dψ c p.1 p.2)
          (fun c => massWeightScale_Dbarψ c q.1 q.2)) hy2 (by omega)]
        exact Submodule.zero_mem _
    · rw [eq_zero_of_eigen_ne (massWeightScale_mul_eigen
        (fun c => massWeightScale_Dbarψ c p.1 p.2)
        (fun c => massWeightScale_fieldStrengthDeriv c q.1 q.2.1 q.2.2)) hy2
        (by omega)]
      exact Submodule.zero_mem _
    · by_cases hlen : p.1.length = 0 ∧ q.1.length = 0
      · rw [List.length_eq_zero_iff.mp hlen.1, List.length_eq_zero_iff.mp hlen.2]
        exact Submodule.subset_span (Or.inl (Or.inr ⟨(p.2, q.2), rfl⟩))
      · rw [eq_zero_of_eigen_ne (massWeightScale_mul_eigen
          (fun c => massWeightScale_Dbarψ c p.1 p.2)
          (fun c => massWeightScale_Dψ c q.1 q.2)) hy2 (by omega)]
        exact Submodule.zero_mem _
    · rw [eq_zero_of_charge_ne_zero (k := -2) (by omega)
        (fun gc => rep_ofConstant_Dbarψ_mul_Dbarψ gc p.1 q.1 p.2 q.2) hy3]
      exact Submodule.zero_mem _
  · obtain ⟨w, hw, hweig⟩ := exists_weight_of_list_prod hl
    rw [eq_zero_of_eigen_ne hweig hy2 (by
      simp only [List.length_cons] at hw
      omega)]
    exact Submodule.zero_mem _

set_option maxHeartbeats 4000000 in
/-- The weight-eight neutral sector: spanned by the field-strength squares, the
  second derivatives of the field strength, and the one-derivative lepton
  pairs. -/
lemma chargeCovSpan_eight_le :
    chargeCovSpan 8 0 ≤ Submodule.span ℂ
      ((Set.range fun p : ((Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)) ×
          (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) =>
        fieldStrengthDeriv {} p.1.1 p.1.2 * fieldStrengthDeriv {} p.2.1 p.2.2) ∪
      (Set.range fun p : ((Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)) ×
          (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) =>
        fieldStrengthDeriv {p.1.1, p.1.2} p.2.1 p.2.2) ∪
      (Set.range fun p : (Fin 2 × Fin 2) × (Fin 1 ⊕ Fin 3) =>
        Dbarψ [] p.1.1 * Dψ [p.2] p.1.2) ∪
      (Set.range fun p : (Fin 2 × Fin 2) × (Fin 1 ⊕ Fin 3) =>
        Dψ [p.2] p.1.2 * Dbarψ [] p.1.1) ∪
      (Set.range fun p : (Fin 2 × Fin 2) × (Fin 1 ⊕ Fin 3) =>
        Dψ [] p.1.1 * Dbarψ [p.2] p.1.2) ∪
      (Set.range fun p : (Fin 2 × Fin 2) × (Fin 1 ⊕ Fin 3) =>
        Dbarψ [p.2] p.1.2 * Dψ [] p.1.1)) := by
  rw [chargeCovSpan, Submodule.span_le]
  rintro y ⟨hy1, hy2, hy3⟩
  simp only [mul_zero, zpow_zero, one_smul] at hy3
  obtain ⟨l, hl, hprod⟩ := Submonoid.exists_list_of_mem_closure hy1
  subst hprod
  rcases l with _ | ⟨g, _ | ⟨g', _ | ⟨g'', t⟩⟩⟩
  · rw [List.prod_nil] at hy2 ⊢
    rw [eq_zero_of_eigen_ne (m := 0)
      (fun c => by rw [pow_zero, one_smul]; exact (massWeightScale c).map_one)
      hy2 (by omega)]
    exact Submodule.zero_mem _
  · rw [List.prod_cons, List.prod_nil, mul_one] at hy2 ⊢
    rcases hl g List.mem_cons_self with (⟨p, rfl⟩ | ⟨p, rfl⟩) | ⟨p, rfl⟩ <;>
      dsimp only at hy2 ⊢
    · by_cases hcard : Multiset.card p.1 = 2
      · obtain ⟨ρ, τ, hρτ⟩ := Multiset.card_eq_two.mp hcard
        rw [hρτ]
        exact Submodule.subset_span (Or.inl (Or.inl (Or.inl (Or.inl
          (Or.inr ⟨((ρ, τ), p.2.1, p.2.2), rfl⟩)))))
      · rw [eq_zero_of_eigen_ne
          (fun c => massWeightScale_fieldStrengthDeriv c p.1 p.2.1 p.2.2) hy2
          (by omega)]
        exact Submodule.zero_mem _
    · rw [eq_zero_of_eigen_ne (fun c => massWeightScale_Dψ c p.1 p.2) hy2
        (by omega)]
      exact Submodule.zero_mem _
    · rw [eq_zero_of_eigen_ne (fun c => massWeightScale_Dbarψ c p.1 p.2) hy2
        (by omega)]
      exact Submodule.zero_mem _
  · rw [List.prod_cons, List.prod_cons, List.prod_nil, mul_one] at hy2 hy3 ⊢
    rcases hl g List.mem_cons_self with (⟨p, rfl⟩ | ⟨p, rfl⟩) | ⟨p, rfl⟩ <;>
      rcases hl g' (List.mem_cons_of_mem _ List.mem_cons_self) with
        (⟨q, rfl⟩ | ⟨q, rfl⟩) | ⟨q, rfl⟩ <;>
      dsimp only at hy2 hy3 ⊢
    · by_cases hcard : Multiset.card p.1 = 0 ∧ Multiset.card q.1 = 0
      · rw [Multiset.card_eq_zero.mp hcard.1, Multiset.card_eq_zero.mp hcard.2]
        exact Submodule.subset_span (Or.inl (Or.inl (Or.inl (Or.inl
          (Or.inl ⟨((p.2.1, p.2.2), q.2.1, q.2.2), rfl⟩)))))
      · rw [eq_zero_of_eigen_ne (massWeightScale_mul_eigen
          (fun c => massWeightScale_fieldStrengthDeriv c p.1 p.2.1 p.2.2)
          (fun c => massWeightScale_fieldStrengthDeriv c q.1 q.2.1 q.2.2)) hy2
          (by omega)]
        exact Submodule.zero_mem _
    · rw [eq_zero_of_eigen_ne (massWeightScale_mul_eigen
        (fun c => massWeightScale_fieldStrengthDeriv c p.1 p.2.1 p.2.2)
        (fun c => massWeightScale_Dψ c q.1 q.2)) hy2 (by omega)]
      exact Submodule.zero_mem _
    · rw [eq_zero_of_eigen_ne (massWeightScale_mul_eigen
        (fun c => massWeightScale_fieldStrengthDeriv c p.1 p.2.1 p.2.2)
        (fun c => massWeightScale_Dbarψ c q.1 q.2)) hy2 (by omega)]
      exact Submodule.zero_mem _
    · rw [eq_zero_of_eigen_ne (massWeightScale_mul_eigen
        (fun c => massWeightScale_Dψ c p.1 p.2)
        (fun c => massWeightScale_fieldStrengthDeriv c q.1 q.2.1 q.2.2)) hy2
        (by omega)]
      exact Submodule.zero_mem _
    · rw [eq_zero_of_charge_ne_zero (k := 2) (by omega)
        (fun gc => rep_ofConstant_Dψ_mul_Dψ gc p.1 q.1 p.2 q.2) hy3]
      exact Submodule.zero_mem _
    · by_cases hlen : p.1.length = 0 ∧ q.1.length = 1
      · obtain ⟨μ, hμ⟩ := List.length_eq_one_iff.mp hlen.2
        rw [List.length_eq_zero_iff.mp hlen.1, hμ]
        exact Submodule.subset_span (Or.inl (Or.inr ⟨((p.2, q.2), μ), rfl⟩))
      · by_cases hlen' : p.1.length = 1 ∧ q.1.length = 0
        · obtain ⟨μ, hμ⟩ := List.length_eq_one_iff.mp hlen'.1
          rw [List.length_eq_zero_iff.mp hlen'.2, hμ]
          exact Submodule.subset_span (Or.inl (Or.inl (Or.inr
            ⟨((q.2, p.2), μ), rfl⟩)))
        · rw [eq_zero_of_eigen_ne (massWeightScale_mul_eigen
            (fun c => massWeightScale_Dψ c p.1 p.2)
            (fun c => massWeightScale_Dbarψ c q.1 q.2)) hy2 (by omega)]
          exact Submodule.zero_mem _
    · rw [eq_zero_of_eigen_ne (massWeightScale_mul_eigen
        (fun c => massWeightScale_Dbarψ c p.1 p.2)
        (fun c => massWeightScale_fieldStrengthDeriv c q.1 q.2.1 q.2.2)) hy2
        (by omega)]
      exact Submodule.zero_mem _
    · by_cases hlen : p.1.length = 0 ∧ q.1.length = 1
      · obtain ⟨μ, hμ⟩ := List.length_eq_one_iff.mp hlen.2
        rw [List.length_eq_zero_iff.mp hlen.1, hμ]
        exact Submodule.subset_span (Or.inl (Or.inl (Or.inl (Or.inr
          ⟨((p.2, q.2), μ), rfl⟩))))
      · by_cases hlen' : p.1.length = 1 ∧ q.1.length = 0
        · obtain ⟨μ, hμ⟩ := List.length_eq_one_iff.mp hlen'.1
          rw [List.length_eq_zero_iff.mp hlen'.2, hμ]
          exact Submodule.subset_span (Or.inr ⟨((q.2, p.2), μ), rfl⟩)
        · rw [eq_zero_of_eigen_ne (massWeightScale_mul_eigen
            (fun c => massWeightScale_Dbarψ c p.1 p.2)
            (fun c => massWeightScale_Dψ c q.1 q.2)) hy2 (by omega)]
          exact Submodule.zero_mem _
    · rw [eq_zero_of_charge_ne_zero (k := -2) (by omega)
        (fun gc => rep_ofConstant_Dbarψ_mul_Dbarψ gc p.1 q.1 p.2 q.2) hy3]
      exact Submodule.zero_mem _
  · have h0 : (g :: g' :: g'' :: t).prod = 0 := by
      obtain ⟨w, hw, hweig⟩ := exists_weight_of_list_prod hl
      exact eq_zero_of_eigen_ne hweig hy2 (by
        simp only [List.length_cons] at hw
        omega)
    exact Set.mem_of_eq_of_mem h0 (Submodule.zero_mem _)

/-!

### The parity rotations

The three rotations by `π` about the coordinate axes lift to `SL(2,ℂ)` as
`i σ_k`; their Lorentz matrices are the diagonal sign matrices fixing the time
axis and the rotation axis and reversing the two others. Averaging over this
Klein four-group kills every tensor component with an odd index pattern; since
every antisymmetric index pair is odd under exactly two of the three parities,
the weight-four sector admits no invariant.

-/

/-- The lift `diag(i, -i)` of the rotation by `π` about the `z`-axis. -/
noncomputable def parityZ : SL(2,ℂ) :=
  ⟨!![Complex.I, 0; 0, -Complex.I], by
    simp [Matrix.det_fin_two_of]⟩

/-- The lift `i σ1` of the rotation by `π` about the `x`-axis. -/
noncomputable def parityX : SL(2,ℂ) :=
  ⟨!![0, Complex.I; Complex.I, 0], by
    simp [Matrix.det_fin_two_of]⟩

/-- The lift `i σ2` of the rotation by `π` about the `y`-axis. -/
noncomputable def parityY : SL(2,ℂ) :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two_of]⟩

/-- The sign pattern of the rotation by `π` about the `z`-axis. -/
def paritySignZ : Fin 1 ⊕ Fin 3 → ℝ
  | Sum.inl _ => 1
  | Sum.inr 0 => -1
  | Sum.inr 1 => -1
  | Sum.inr 2 => 1

/-- The sign pattern of the rotation by `π` about the `x`-axis. -/
def paritySignX : Fin 1 ⊕ Fin 3 → ℝ
  | Sum.inl _ => 1
  | Sum.inr 0 => 1
  | Sum.inr 1 => -1
  | Sum.inr 2 => -1

/-- The sign pattern of the rotation by `π` about the `y`-axis. -/
def paritySignY : Fin 1 ⊕ Fin 3 → ℝ
  | Sum.inl _ => 1
  | Sum.inr 0 => -1
  | Sum.inr 1 => 1
  | Sum.inr 2 => -1

/-- The Lorentz matrix of the `z`-parity is the diagonal sign matrix. -/
lemma toLorentzGroup_parityZ (a b : Fin 1 ⊕ Fin 3) :
    (Lorentz.SL2C.toLorentzGroup parityZ).1 a b =
      if a = b then paritySignZ a else 0 := by
  refine Complex.ofReal_injective ?_
  rw [Lorentz.SL2C.toLorentzGroup_eq_trace]
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    · simp [parityZ, paritySignZ, PauliMatrix.pauliSelfAdjoint', PauliMatrix.pauliMatrix,
        Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose,
        Matrix.diag]
      simp [Matrix.vecMul, Matrix.vecHead, Matrix.vecTail]

/-- The Lorentz matrix of the `x`-parity is the diagonal sign matrix. -/
lemma toLorentzGroup_parityX (a b : Fin 1 ⊕ Fin 3) :
    (Lorentz.SL2C.toLorentzGroup parityX).1 a b =
      if a = b then paritySignX a else 0 := by
  refine Complex.ofReal_injective ?_
  rw [Lorentz.SL2C.toLorentzGroup_eq_trace]
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    · simp [parityX, paritySignX, PauliMatrix.pauliSelfAdjoint', PauliMatrix.pauliMatrix,
        Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose,
        Matrix.diag]
      simp [Matrix.vecMul, Matrix.vecHead, Matrix.vecTail]

/-- The Lorentz matrix of the `y`-parity is the diagonal sign matrix. -/
lemma toLorentzGroup_parityY (a b : Fin 1 ⊕ Fin 3) :
    (Lorentz.SL2C.toLorentzGroup parityY).1 a b =
      if a = b then paritySignY a else 0 := by
  refine Complex.ofReal_injective ?_
  rw [Lorentz.SL2C.toLorentzGroup_eq_trace]
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    · simp [parityY, paritySignY, PauliMatrix.pauliSelfAdjoint', PauliMatrix.pauliMatrix,
        Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose,
        Matrix.diag]
      simp [Matrix.vecMul, Matrix.vecHead, Matrix.vecTail]

/-- Under a diagonal Lorentz transformation the field strength scales by the
  product of the signs of its two indices. -/
lemma repLorentzGroup_diag_fieldStrengthDeriv {M : SL(2,ℂ)}
    {sgn : Fin 1 ⊕ Fin 3 → ℝ}
    (hM : ∀ a b, (Lorentz.SL2C.toLorentzGroup M).1 a b =
      if a = b then sgn a else 0) (μ ν : Fin 1 ⊕ Fin 3) :
    repLorentzGroup M (fieldStrengthDeriv {} μ ν) =
      ((sgn μ * sgn ν : ℝ) : ℂ) • fieldStrengthDeriv {} μ ν := by
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  rw [Finset.sum_eq_single μ (fun a _ ha => Finset.sum_eq_zero fun b _ => by
      rw [hM a μ, if_neg ha, zero_mul, Complex.ofReal_zero, zero_smul])
    (fun h => absurd (Finset.mem_univ μ) h)]
  rw [Finset.sum_eq_single ν (fun b _ hb => by
      rw [hM b ν, if_neg hb, mul_zero, Complex.ofReal_zero, zero_smul])
    (fun h => absurd (Finset.mem_univ ν) h)]
  rw [hM μ μ, if_pos rfl, hM ν ν, if_pos rfl]

/-- The field strength vanishes on a repeated index. -/
lemma fieldStrengthDeriv_self (s : Multiset (Fin 1 ⊕ Fin 3))
    (μ : Fin 1 ⊕ Fin 3) : fieldStrengthDeriv s μ μ = 0 := by
  have h : (fieldStrengthDeriv s μ μ : JetAlgebra) =
      [JetGenerators.dB (s + {μ}) μ]ₐ - [JetGenerators.dB (s + {μ}) μ]ₐ := by
    rw [fieldStrengthDeriv, BBoson.JetAlgebra.fieldStrengthDeriv,
      TensorProduct.tmul_sub, TensorProduct.sub_tmul]
    rfl
  rw [h, sub_self]

set_option maxHeartbeats 2000000 in
/-- No Lorentz invariant of mass weight four: an invariant combination of the
  field strengths `F_{μν}` vanishes, since every antisymmetric index pair is
  odd under two of the three parity rotations. -/
lemma eq_zero_of_mem_chargeCovSpan_four {y : JetAlgebra}
    (hy : y ∈ chargeCovSpan 4 0)
    (hinv : ∀ Λ : SL(2,ℂ), repLorentzGroup Λ y = y) : y = 0 := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp
    (chargeCovSpan_four_le hy)
  have h4 : ((4 : ℂ)⁻¹ • (y + repLorentzGroup parityZ y +
      repLorentzGroup parityY y + repLorentzGroup parityX y)) = y := by
    rw [hinv, hinv, hinv]
    module
  rw [← h4, ← hc, map_sum, map_sum, map_sum]
  simp only [map_smul, repLorentzGroup_diag_fieldStrengthDeriv
      toLorentzGroup_parityZ,
    repLorentzGroup_diag_fieldStrengthDeriv toLorentzGroup_parityY,
    repLorentzGroup_diag_fieldStrengthDeriv toLorentzGroup_parityX]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, Finset.smul_sum]
  refine Finset.sum_eq_zero fun p _ => ?_
  rcases eq_or_ne p.1 p.2 with hp | hp
  · rw [hp, fieldStrengthDeriv_self]
    simp
  · rw [smul_smul, smul_smul, smul_smul, ← add_smul, ← add_smul, ← add_smul,
      smul_smul]
    rw [show ((4 : ℂ)⁻¹ * (c p + c p * ((paritySignZ p.1 * paritySignZ p.2 : ℝ) : ℂ) +
        c p * ((paritySignY p.1 * paritySignY p.2 : ℝ) : ℂ) +
        c p * ((paritySignX p.1 * paritySignX p.2 : ℝ) : ℂ))) = 0 from by
      rcases p with ⟨μ, ν⟩
      rcases μ with μ | μ <;> rcases ν with ν | ν <;>
        first
          | (exact absurd rfl (by simpa using hp))
          | (fin_cases μ <;> fin_cases ν <;>
              simp_all [paritySignZ, paritySignY, paritySignX] <;>
              norm_num [Complex.ext_iff] <;> ring)]
    rw [zero_smul]

/-!

### The transformation law of the derivative field strength

-/

/-- The transformation law of the embedded first-derivative field strength:
  a three-index tensor, all indices transforming by the Lorentz matrix. -/
lemma repLorentzGroup_fieldStrengthDeriv_singleton (Λ : SL(2,ℂ))
    (ρ μ ν : Fin 1 ⊕ Fin 3) :
    repLorentzGroup Λ (fieldStrengthDeriv {ρ} μ ν) =
      ∑ r, ∑ a, ∑ b, ((((Lorentz.SL2C.toLorentzGroup Λ).1 r ρ *
        ((Lorentz.SL2C.toLorentzGroup Λ).1 a μ *
          (Lorentz.SL2C.toLorentzGroup Λ).1 b ν) : ℝ)) : ℂ) •
        fieldStrengthDeriv {r} a b := by
  have hconv : ∀ (r : ℝ) (X : ℂ ⊗[ℝ] BBoson.JetAlgebra),
      (r • X) ⊗ₜ[ℂ] (1 : LeptonSinglet.JetAlgebra) = ((r : ℂ)) • (X ⊗ₜ[ℂ] 1) := by
    intro r X
    rw [← algebraMap_smul (R := ℝ) ℂ r X, ← TensorProduct.smul_tmul']
    rfl
  have happ : repLorentzGroup Λ (((1 : ℂ) ⊗ₜ[ℝ]
      BBoson.JetAlgebra.fieldStrengthDeriv {ρ} μ ν) ⊗ₜ[ℂ]
        (1 : LeptonSinglet.JetAlgebra)) =
      (BBoson.JetAlgebra.complexRepLorentzGroup Λ ((1 : ℂ) ⊗ₜ[ℝ]
        BBoson.JetAlgebra.fieldStrengthDeriv {ρ} μ ν)) ⊗ₜ[ℂ]
      (LeptonSinglet.JetAlgebra.repLorentzGroup Λ
        (1 : LeptonSinglet.JetAlgebra)) := rfl
  rw [fieldStrengthDeriv, happ,
    BBoson.JetAlgebra.complexRepLorentzGroup_one_tmul_fieldStrengthDeriv_singleton,
    LeptonSinglet.JetAlgebra.repLorentzGroup_apply_one]
  simp only [TensorProduct.sum_tmul, hconv, fieldStrengthDeriv]

/-- Under a diagonal Lorentz transformation the derivative field strength
  scales by the product of the signs of its three indices. -/
lemma repLorentzGroup_diag_fieldStrengthDeriv_singleton {M : SL(2,ℂ)}
    {sgn : Fin 1 ⊕ Fin 3 → ℝ}
    (hM : ∀ a b, (Lorentz.SL2C.toLorentzGroup M).1 a b =
      if a = b then sgn a else 0) (ρ μ ν : Fin 1 ⊕ Fin 3) :
    repLorentzGroup M (fieldStrengthDeriv {ρ} μ ν) =
      ((sgn ρ * (sgn μ * sgn ν) : ℝ) : ℂ) • fieldStrengthDeriv {ρ} μ ν := by
  rw [repLorentzGroup_fieldStrengthDeriv_singleton]
  rw [Finset.sum_eq_single ρ (fun r _ hr => Finset.sum_eq_zero fun a _ =>
      Finset.sum_eq_zero fun b _ => by
        rw [hM r ρ, if_neg hr, zero_mul, Complex.ofReal_zero, zero_smul])
    (fun h => absurd (Finset.mem_univ ρ) h)]
  rw [Finset.sum_eq_single μ (fun a _ ha => Finset.sum_eq_zero fun b _ => by
      rw [hM a μ, if_neg ha, zero_mul, mul_zero, Complex.ofReal_zero, zero_smul])
    (fun h => absurd (Finset.mem_univ μ) h)]
  rw [Finset.sum_eq_single ν (fun b _ hb => by
      rw [hM b ν, if_neg hb, mul_zero, mul_zero, Complex.ofReal_zero, zero_smul])
    (fun h => absurd (Finset.mem_univ ν) h)]
  rw [hM ρ ρ, if_pos rfl, hM μ μ, if_pos rfl, hM ν ν, if_pos rfl]

/-- Antisymmetry of the embedded field-strength derivatives in the two field
  indices. -/
lemma fieldStrengthDeriv_antisymm (s : Multiset (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) :
    fieldStrengthDeriv s ν μ = - fieldStrengthDeriv s μ ν := by
  have h : ∀ a b : Fin 1 ⊕ Fin 3, (fieldStrengthDeriv s a b : JetAlgebra) =
      [JetGenerators.dB (s + {a}) b]ₐ - [JetGenerators.dB (s + {b}) a]ₐ := by
    intro a b
    rw [fieldStrengthDeriv, BBoson.JetAlgebra.fieldStrengthDeriv,
      TensorProduct.tmul_sub, TensorProduct.sub_tmul]
    rfl
  rw [h, h, neg_sub]

/-- The canonical orientation of a mixed field-strength component: the time
  index first. -/
lemma fieldStrengthDeriv_inr_inl (s : Multiset (Fin 1 ⊕ Fin 3)) (i : Fin 3)
    (j : Fin 1) :
    fieldStrengthDeriv s (Sum.inr i) (Sum.inl j) =
      - fieldStrengthDeriv s (Sum.inl j) (Sum.inr i) :=
  fieldStrengthDeriv_antisymm s (Sum.inl j) (Sum.inr i)

/-!

### The boosts along the `z`-axis

Two diagonal boosts `diag(t, t⁻¹)` with `t = 2, 3`. Together with the Klein
four-group of parity rotations they suffice to kill the neutral weight-six
sector: the Klein average projects onto the twelve surviving field-strength
components and the diagonal fermion pairs, and a rational combination of the
two boosts (with weights summing to one) annihilates all of them.

-/

/-- The lift `diag(2, 1/2)` of the boost along the `z`-axis with rapidity
  `log 4`. -/
noncomputable def boostA : SL(2,ℂ) :=
  ⟨!![2, 0; 0, 2⁻¹], by norm_num [Matrix.det_fin_two_of]⟩

/-- The lift `diag(3, 1/3)` of the boost along the `z`-axis with rapidity
  `log 9`. -/
noncomputable def boostB : SL(2,ℂ) :=
  ⟨!![3, 0; 0, 3⁻¹], by norm_num [Matrix.det_fin_two_of]⟩

/-- The Lorentz matrix of `boostA`. -/
noncomputable def boostMatA : (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → ℝ
  | Sum.inl _, Sum.inl _ => 17/8
  | Sum.inl _, Sum.inr 2 => -(15/8)
  | Sum.inr 2, Sum.inl _ => -(15/8)
  | Sum.inr 0, Sum.inr 0 => 1
  | Sum.inr 1, Sum.inr 1 => 1
  | Sum.inr 2, Sum.inr 2 => 17/8
  | _, _ => 0

/-- The Lorentz matrix of `boostB`. -/
noncomputable def boostMatB : (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → ℝ
  | Sum.inl _, Sum.inl _ => 41/9
  | Sum.inl _, Sum.inr 2 => -(40/9)
  | Sum.inr 2, Sum.inl _ => -(40/9)
  | Sum.inr 0, Sum.inr 0 => 1
  | Sum.inr 1, Sum.inr 1 => 1
  | Sum.inr 2, Sum.inr 2 => 41/9
  | _, _ => 0

set_option maxHeartbeats 2000000 in
/-- The Lorentz matrix of the first boost. -/
lemma toLorentzGroup_boostA (a b : Fin 1 ⊕ Fin 3) :
    (Lorentz.SL2C.toLorentzGroup boostA).1 a b = boostMatA a b := by
  refine Complex.ofReal_injective ?_
  rw [Lorentz.SL2C.toLorentzGroup_eq_trace]
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    · try simp [boostA, boostMatA, PauliMatrix.pauliSelfAdjoint',
        PauliMatrix.pauliMatrix, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose, Matrix.diag]
      try simp [Matrix.vecMul, Matrix.vecHead, Matrix.vecTail]
      try norm_num [Complex.ext_iff]

set_option maxHeartbeats 2000000 in
/-- The Lorentz matrix of the second boost. -/
lemma toLorentzGroup_boostB (a b : Fin 1 ⊕ Fin 3) :
    (Lorentz.SL2C.toLorentzGroup boostB).1 a b = boostMatB a b := by
  refine Complex.ofReal_injective ?_
  rw [Lorentz.SL2C.toLorentzGroup_eq_trace]
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    · try simp [boostB, boostMatB, PauliMatrix.pauliSelfAdjoint',
        PauliMatrix.pauliMatrix, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose, Matrix.diag]
      try simp [Matrix.vecMul, Matrix.vecHead, Matrix.vecTail]
      try norm_num [Complex.ext_iff]

/-- The inverse of the `z`-parity, entrywise. -/
lemma parityZ_inv_coe :
    (parityZ⁻¹ : SL(2,ℂ)).1 = !![-Complex.I, 0; 0, Complex.I] := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [parityZ]

/-- The inverse of the `y`-parity, entrywise. -/
lemma parityY_inv_coe :
    (parityY⁻¹ : SL(2,ℂ)).1 = !![0, -1; 1, 0] := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [parityY]

/-- The inverse of the `x`-parity, entrywise. -/
lemma parityX_inv_coe :
    (parityX⁻¹ : SL(2,ℂ)).1 = !![0, -Complex.I; -Complex.I, 0] := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [parityX]

/-- The inverse of the first boost, entrywise, with real entries. -/
lemma boostA_inv_coe :
    (boostA⁻¹ : SL(2,ℂ)).1 = !![((2⁻¹ : ℝ) : ℂ), 0; 0, ((2 : ℝ) : ℂ)] := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [boostA]

/-- The inverse of the second boost, entrywise, with real entries. -/
lemma boostB_inv_coe :
    (boostB⁻¹ : SL(2,ℂ)).1 = !![((3⁻¹ : ℝ) : ℂ), 0; 0, ((3 : ℝ) : ℂ)] := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [boostB]

/-- The Lorentz action on a zero-derivative fermion pair `ψ̄_α ψ_β`. -/
lemma repLorentzGroup_Dbarψ_nil_mul_Dψ_nil (Λ : SL(2,ℂ)) (α β : Fin 2) :
    repLorentzGroup Λ (Dbarψ [] α * Dψ [] β) =
      ∑ γ, ∑ δ, ((Λ⁻¹).1 α γ * star ((Λ⁻¹).1 β δ)) •
        (Dbarψ [] γ * Dψ [] δ) := by
  have hsm : ∀ (f : Fin 2 → JetAlgebra) (y : JetAlgebra),
      (∑ x, f x) * y = ∑ x, f x * y := fun f y => by
    rw [show (∑ x, f x) * y = LinearMap.mulRight ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hms : ∀ (f : Fin 2 → JetAlgebra) (y : JetAlgebra),
      y * (∑ x, f x) = ∑ x, y * f x := fun f y => by
    rw [show y * (∑ x, f x) = LinearMap.mulLeft ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hsmul : ∀ (c d : ℂ) (x y : JetAlgebra),
      (c • x) * (d • y) = (c * d) • (x * y) := fun c d x y => by
    rw [smul_mul_smul_comm]
  rw [repLorentzGroup_apply_mul, repLorentzGroup_Dbarψ_nil, repLorentzGroup_Dψ_nil]
  simp only [hsm, hms, hsmul]

/-- The Lorentz action on a zero-derivative fermion pair `ψ_α ψ̄_β`. -/
lemma repLorentzGroup_Dψ_nil_mul_Dbarψ_nil (Λ : SL(2,ℂ)) (α β : Fin 2) :
    repLorentzGroup Λ (Dψ [] α * Dbarψ [] β) =
      ∑ γ, ∑ δ, (star ((Λ⁻¹).1 α γ) * (Λ⁻¹).1 β δ) •
        (Dψ [] γ * Dbarψ [] δ) := by
  have hsm : ∀ (f : Fin 2 → JetAlgebra) (y : JetAlgebra),
      (∑ x, f x) * y = ∑ x, f x * y := fun f y => by
    rw [show (∑ x, f x) * y = LinearMap.mulRight ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hms : ∀ (f : Fin 2 → JetAlgebra) (y : JetAlgebra),
      y * (∑ x, f x) = ∑ x, y * f x := fun f y => by
    rw [show y * (∑ x, f x) = LinearMap.mulLeft ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hsmul : ∀ (c d : ℂ) (x y : JetAlgebra),
      (c • x) * (d • y) = (c * d) • (x * y) := fun c d x y => by
    rw [smul_mul_smul_comm]
  rw [repLorentzGroup_apply_mul, repLorentzGroup_Dψ_nil, repLorentzGroup_Dbarψ_nil]
  simp only [hsm, hms, hsmul]

/-!

### The kill operator of the weight-six sector

-/

/-- The averaging operator over the Klein four-group of parity rotations. -/
noncomputable def kleinAvg : Module.End ℂ JetAlgebra :=
  (4 : ℂ)⁻¹ • (LinearMap.id + repLorentzGroup parityZ +
    repLorentzGroup parityY + repLorentzGroup parityX)

/-- The boost-weighted Klein average: an operator fixing every
  Lorentz-invariant vector and annihilating the neutral weight-six sector.
  The weights `-13/24, 8/3, -9/8` sum to one and are chosen so that
  `w₁ + w₂ t² + w₃ s² = 0` for `t² ∈ {4, 1/4}` and `s² ∈ {9, 1/9}`
  respectively, killing both eigendirections of the two boosts. -/
noncomputable def sixKill : Module.End ℂ JetAlgebra :=
  ((-13/24 : ℂ) • LinearMap.id + (8/3 : ℂ) • repLorentzGroup boostA +
    (-9/8 : ℂ) • repLorentzGroup boostB) ∘ₗ kleinAvg

/-- The Klein average, termwise. -/
lemma kleinAvg_apply (v : JetAlgebra) :
    kleinAvg v = (4 : ℂ)⁻¹ • (v + repLorentzGroup parityZ v +
      repLorentzGroup parityY v + repLorentzGroup parityX v) := by
  simp only [kleinAvg, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.id_apply]

/-- The kill operator, termwise. -/
lemma sixKill_apply (v : JetAlgebra) :
    sixKill v = (-13/24 : ℂ) • kleinAvg v +
      (8/3 : ℂ) • repLorentzGroup boostA (kleinAvg v) +
      (-9/8 : ℂ) • repLorentzGroup boostB (kleinAvg v) := by
  simp only [sixKill, LinearMap.comp_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.id_apply]

set_option maxHeartbeats 8000000 in
/-- The kill operator annihilates every embedded derivative field strength:
  the Klein average kills every component with an odd index pattern, and the
  boost combination kills the twelve surviving components. -/
lemma sixKill_fieldStrengthDeriv_singleton (ρ μ ν : Fin 1 ⊕ Fin 3) :
    sixKill (fieldStrengthDeriv {ρ} μ ν) = 0 := by
  rcases eq_or_ne μ ν with rfl | hμν
  · rw [fieldStrengthDeriv_self]
    exact map_zero _
  · have hK : kleinAvg (fieldStrengthDeriv {ρ} μ ν) =
        (((1 + paritySignZ ρ * (paritySignZ μ * paritySignZ ν) +
          paritySignY ρ * (paritySignY μ * paritySignY ν) +
          paritySignX ρ * (paritySignX μ * paritySignX ν)) / 4 : ℝ) : ℂ) •
          fieldStrengthDeriv {ρ} μ ν := by
      rw [kleinAvg_apply,
        repLorentzGroup_diag_fieldStrengthDeriv_singleton toLorentzGroup_parityZ,
        repLorentzGroup_diag_fieldStrengthDeriv_singleton toLorentzGroup_parityY,
        repLorentzGroup_diag_fieldStrengthDeriv_singleton toLorentzGroup_parityX]
      push_cast
      module
    rw [sixKill_apply, hK, map_smul, map_smul]
    rcases ρ with ρ | ρ <;> rcases μ with μ | μ <;> rcases ν with ν | ν <;>
      fin_cases ρ <;> fin_cases μ <;> fin_cases ν <;>
      first
      | (simp only [fieldStrengthDeriv_self, map_zero, smul_zero, add_zero]; done)
      | (norm_num [paritySignZ, paritySignY, paritySignX]; done)
      | (norm_num [paritySignZ, paritySignY, paritySignX]
         rw [repLorentzGroup_fieldStrengthDeriv_singleton boostA,
           repLorentzGroup_fieldStrengthDeriv_singleton boostB]
         simp only [Fintype.sum_sum_type, Fin.sum_univ_three, Fin.sum_univ_one,
           toLorentzGroup_boostA, toLorentzGroup_boostB]
         norm_num [boostMatA, boostMatB, fieldStrengthDeriv_self,
           fieldStrengthDeriv_inr_inl]
         push_cast
         module)

set_option maxHeartbeats 4000000 in
/-- The kill operator annihilates every zero-derivative pair `ψ̄_α ψ_β`: the
  Klein average kills the off-diagonal pairs and symmetrises the diagonal
  ones, which the boost combination then kills. -/
lemma sixKill_Dbarψ_mul_Dψ (α β : Fin 2) :
    sixKill (Dbarψ [] α * Dψ [] β) = 0 := by
  rw [sixKill_apply, kleinAvg_apply]
  fin_cases α <;> fin_cases β <;>
    · simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_nil, map_add, map_smul,
        map_sum, parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
        boostA_inv_coe, boostB_inv_coe, Fin.sum_univ_two, Fin.zero_eta,
        Fin.mk_one, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
        Matrix.cons_val_fin_one,
        star_zero, star_neg, star_one, Complex.star_def, Complex.conj_I,
        Complex.conj_ofReal, map_one, map_zero, map_neg, neg_mul, mul_neg,
        neg_neg,
        zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
        Complex.I_mul_I, one_mul, mul_one, smul_add, smul_smul, Finset.smul_sum]
      try push_cast
      try module

set_option maxHeartbeats 4000000 in
/-- The kill operator annihilates every zero-derivative pair `ψ_α ψ̄_β`. -/
lemma sixKill_Dψ_mul_Dbarψ (α β : Fin 2) :
    sixKill (Dψ [] α * Dbarψ [] β) = 0 := by
  rw [sixKill_apply, kleinAvg_apply]
  fin_cases α <;> fin_cases β <;>
    · simp only [repLorentzGroup_Dψ_nil_mul_Dbarψ_nil, map_add, map_smul,
        map_sum, parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
        boostA_inv_coe, boostB_inv_coe, Fin.sum_univ_two, Fin.zero_eta,
        Fin.mk_one, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
        Matrix.cons_val_fin_one,
        star_zero, star_neg, star_one, Complex.star_def, Complex.conj_I,
        Complex.conj_ofReal, map_one, map_zero, map_neg, neg_mul, mul_neg,
        neg_neg,
        zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
        Complex.I_mul_I, one_mul, mul_one, smul_add, smul_smul, Finset.smul_sum]
      try push_cast
      try module

/-- No Lorentz invariant of mass weight six: an invariant combination of the
  field-strength derivatives `∂_ρ F_{μν}` and the fermion pairs `ψ̄_α ψ_β`
  vanishes. -/
lemma eq_zero_of_mem_chargeCovSpan_six {y : JetAlgebra}
    (hy : y ∈ chargeCovSpan 6 0)
    (hinv : ∀ Λ : SL(2,ℂ), repLorentzGroup Λ y = y) : y = 0 := by
  have h := chargeCovSpan_six_le hy
  rw [Submodule.span_union, Submodule.span_union] at h
  obtain ⟨u, hu, w, hw, hy'⟩ := Submodule.mem_sup.mp h
  obtain ⟨u1, hu1, u2, hu2, hu'⟩ := Submodule.mem_sup.mp hu
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hu1
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hu2
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hw
  have hKy : kleinAvg y = y := by
    rw [kleinAvg_apply, hinv parityZ, hinv parityY, hinv parityX]
    module
  have hself : sixKill y = y := by
    rw [sixKill_apply, hKy, hinv boostA, hinv boostB]
    module
  have hkill : sixKill y = 0 := by
    rw [← hy', ← hu', ← ha, ← hd, ← he]
    simp only [map_add, map_sum, map_smul, sixKill_fieldStrengthDeriv_singleton,
      sixKill_Dbarψ_mul_Dψ, sixKill_Dψ_mul_Dbarψ, smul_zero,
      Finset.sum_const_zero, add_zero]
  exact hself.symm.trans hkill

/-!

### The transformation law of the second-derivative field strength

-/

set_option maxHeartbeats 2000000 in
/-- The transformation law of the embedded second-derivative field strength:
  a four-index tensor, all indices transforming by the Lorentz matrix. -/
lemma repLorentzGroup_fieldStrengthDeriv_pair (Λ : SL(2,ℂ))
    (ρ τ μ ν : Fin 1 ⊕ Fin 3) :
    repLorentzGroup Λ (fieldStrengthDeriv {ρ, τ} μ ν) =
      ∑ r, ∑ s, ∑ a, ∑ b, ((((Lorentz.SL2C.toLorentzGroup Λ).1 r ρ *
        ((Lorentz.SL2C.toLorentzGroup Λ).1 s τ *
          ((Lorentz.SL2C.toLorentzGroup Λ).1 a μ *
          (Lorentz.SL2C.toLorentzGroup Λ).1 b ν)) : ℝ)) : ℂ) •
        fieldStrengthDeriv {r, s} a b := by
  have hconv : ∀ (r : ℝ) (X : ℂ ⊗[ℝ] BBoson.JetAlgebra),
      (r • X) ⊗ₜ[ℂ] (1 : LeptonSinglet.JetAlgebra) = ((r : ℂ)) • (X ⊗ₜ[ℂ] 1) := by
    intro r X
    rw [← algebraMap_smul (R := ℝ) ℂ r X, ← TensorProduct.smul_tmul']
    rfl
  have happ : repLorentzGroup Λ (((1 : ℂ) ⊗ₜ[ℝ]
      BBoson.JetAlgebra.fieldStrengthDeriv {ρ, τ} μ ν) ⊗ₜ[ℂ]
        (1 : LeptonSinglet.JetAlgebra)) =
      (BBoson.JetAlgebra.complexRepLorentzGroup Λ ((1 : ℂ) ⊗ₜ[ℝ]
        BBoson.JetAlgebra.fieldStrengthDeriv {ρ, τ} μ ν)) ⊗ₜ[ℂ]
      (LeptonSinglet.JetAlgebra.repLorentzGroup Λ
        (1 : LeptonSinglet.JetAlgebra)) := rfl
  rw [fieldStrengthDeriv, happ,
    BBoson.JetAlgebra.complexRepLorentzGroup_one_tmul_fieldStrengthDeriv_pair,
    LeptonSinglet.JetAlgebra.repLorentzGroup_apply_one]
  simp only [TensorProduct.sum_tmul, hconv, fieldStrengthDeriv]

end JetAlgebra

end QED
