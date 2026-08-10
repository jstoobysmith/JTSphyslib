/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.Invariants.Grading.MassWeightAndHypercharge
/-!
# The neutral sectors of weight at most eight

The charge-zero covariant monomials of each even weight up to eight: the field
strengths `F_{μν}` at weight four, the derivatives `∂_ρ F_{μν}` and the fermion
pairs `ψ̄_α ψ_β` at weight six, and the products `F F`, the second derivatives
`∂_ρ ∂_τ F_{μν}` and the one-derivative fermion pairs at weight eight
(`chargeCovSpan_four_le`, `chargeCovSpan_six_le`, `chargeCovSpan_eight_le`).

This is the reduction step of the classification: it replaces "an invariant of
weight `m` and hypercharge zero" by a *finite explicit spanning family*, on
which the subgroups of `Subgroups/` and the averages of `Averages/` can then be
computed one monomial at a time. That the weight-four and weight-six sectors
contain no invariant at all is proved where the relevant average is defined, in
`Averages/RotationAverage` and `Averages/RotationPiBoostAverage`.
-/

@[expose] public section

set_option maxHeartbeats 1000000

namespace LeptonGaugeSector
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

end JetAlgebra

end LeptonGaugeSector
