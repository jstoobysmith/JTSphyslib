/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Invariants.LorentzCovariance
public import Physlib.Mathematics.InvariantReduction
public meta import Mathlib.Data.Fintype.Sum
public meta import Mathlib.Data.Fintype.Pi
/-!
# Lorentz invariants among two four-vector indices

A rank-two tensor `T^{μν}` has `16` components, and the metric trace

`metricContraction = η_{μν} T^{μν}`

is fixed by every rotation and boost. Every Lorentz invariant in the span of the components is
a multiple of it: nothing else ties two indices, the Levi-Civita symbol needing four. That is
`exists_smul_metricContraction_of_invariant`, and
`exists_smul_metricContraction_of_invariant_subset` is the same statement modulo a
Lorentz-stable subspace `S`, the form the Standard Model files use. The metric contraction is
the only invariant up to scale; for a given `T` it may be zero.

The components are vectors `T d` of a complex vector space `B` carrying a representation
`repLorentz` of `SL(2,ℂ)`, indexed by two directions, and `IsLorentzCovariant 2` says the
group moves them with one factor of the Lorentz matrix per slot. `Submodule.span ℂ (Set.range T)`
is the set of their combinations.

An invariant of the span is `∑_d c_d • T d` for a coefficient tensor `c` that the Lorentz
matrices themselves fix (from `Invariants.Basic`), and three kinds of transformation pin `c`
down (B). The half turn about each axis has a diagonal Lorentz matrix with entries `±1`, and
for `μ ≠ ν` one of the three negates `c_{μν}`, so the off-diagonal coefficients vanish. The
cyclic rotation `x → y → z → x` permutes the spatial directions, so `c_xx = c_yy = c_zz`. The
boost along `z` scales the light-cone component of `c` along `D₀ - D_z` in both slots by `t⁴`,
so that component vanishes, and with the off-diagonal coefficients gone it is `c_tt + c_zz`.
So `c` is `c_tt` times the Minkowski metric. Invariance under the whole group implies
invariance under these elements; nothing is claimed about the group they generate. Section C
divides out `S`.
-/

@[expose] public section

namespace Lorentz

open TensorProduct Matrix MatrixGroups SL2C Invariants

namespace RankTwo

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {T : (Fin 2 → (Fin 1 ⊕ Fin 3)) → B}

/-!

## A. The metric contraction

-/

/-- The metric contraction `g^{μν} T_{μν}`, the only invariant contraction of two
  four-vector indices. -/
noncomputable def metricContraction : B :=
  ∑ d : Fin 2 → Fin 1 ⊕ Fin 3, ((minkowskiMatrixZ (d 0) (d 1) : ℤ) : ℂ) • T d

/-- The Minkowski metric, as a coefficient tensor on two slots, is fixed by every Lorentz
  matrix: `Λ η Λᵀ = η`, which is `LorentzGroup.sum_minkowskiMatrixZ_mul`. -/
lemma isInvariantCoeff_minkowskiMatrixZ :
    IsInvariantCoeff fun d : Fin 2 → Fin 1 ⊕ Fin 3 => ((minkowskiMatrixZ (d 0) (d 1) : ℤ) : ℂ) := by
  intro g
  funext a
  simp only [act]
  rw [← (piFinTwoEquiv fun _ => Fin 1 ⊕ Fin 3).symm.sum_comp, Fintype.sum_prod_type]
  simp only [piFinTwoEquiv_symm_apply, Fin.prod_univ_two]
  exact LorentzGroup.sum_minkowskiMatrixZ_mul (SL2C.toLorentzGroup g) (a 0) (a 1)

/-- The metric contraction of a rank-two family is a Lorentz invariant. -/
lemma repLorentz_metricContraction (hT : IsLorentzCovariant 2 B repLorentz T) (g : SL(2,ℂ)) :
    repLorentz g (metricContraction (T := T)) = metricContraction (T := T) :=
  hT.isInvariant_sum_smul isInvariantCoeff_minkowskiMatrixZ g

/-!

## B. The classification of the Lorentz invariants

The half turns kill the off-diagonal coefficients, the cyclic rotation equates the three
spatial diagonal ones, and the boost along `z` relates the spatial diagonal to the time
diagonal. Together these leave `c_tt` times the metric.

-/

/-- Two distinct directions are told apart by the half turn about some axis: it keeps one and
  negates the other, a finite check. -/
lemma exists_halfTurnSign_mul_ne_one :
    ∀ μ ν : Fin 1 ⊕ Fin 3, μ ≠ ν → ∃ k, halfTurnSign k μ * halfTurnSign k ν ≠ 1 := by
  decide

/-- An invariant coefficient tensor has no off-diagonal coefficients: for `μ ≠ ν` some half
  turn multiplies `c_{μν}` by `-1`. -/
lemma eq_zero_of_ne {c : (Fin 2 → Fin 1 ⊕ Fin 3) → ℂ} (hc : IsInvariantCoeff c)
    {d : Fin 2 → Fin 1 ⊕ Fin 3} (hd : d 0 ≠ d 1) : c d = 0 := by
  obtain ⟨k, hk⟩ := exists_halfTurnSign_mul_ne_one _ _ hd
  exact hc.eq_zero_of_prod_halfTurnSign_ne_one (k := k) (by rwa [Fin.prod_univ_two])

/-- The three spatial diagonal coefficients of an invariant coefficient tensor agree: the
  cyclic rotation carries `c_xx` to `c_yy` to `c_zz`. -/
lemma apply_inr_inr_eq {c : (Fin 2 → Fin 1 ⊕ Fin 3) → ℂ} (hc : IsInvariantCoeff c)
    (j : Fin 3) : c ![Sum.inr j, Sum.inr j] = c ![Sum.inr 2, Sum.inr 2] := by
  have hcyc (j : Fin 3) : c ![Sum.inr (j + 1), Sum.inr (j + 1)] = c ![Sum.inr j, Sum.inr j] := by
    have h := hc.apply_cycIdx ![Sum.inr j, Sum.inr j]
    rwa [show cycIdx ![Sum.inr j, Sum.inr j] = ![Sum.inr (j + 1), Sum.inr (j + 1)] from
      cycDir_comp_two _ _] at h
  fin_cases j
  · exact hcyc 2
  · exact (hcyc 0).trans (hcyc 2)
  · rfl

/-- The time and spatial diagonal coefficients of an invariant coefficient tensor are opposite.
  The boost along `z` scales the light-cone component along `D₀ - D_z` in both slots by `t⁴`, so
  that component, `c_tt - c_tz - c_zt + c_zz`, vanishes, and the mixed terms are `0`. -/
lemma apply_inl_inl_add_apply_inr_inr {c : (Fin 2 → Fin 1 ⊕ Fin 3) → ℂ}
    (hc : IsInvariantCoeff c) : c ![Sum.inl 0, Sum.inl 0] + c ![Sum.inr 2, Sum.inr 2] = 0 := by
  have h := hc.lightConeComponent_eq_zero 2 (κ := ![0, 0]) (by decide)
  rw [lightConeComponent, ← (finTwoArrowEquiv _).symm.sum_comp, Fintype.sum_prod_type] at h
  simp [Fintype.sum_sum_type, Fin.sum_univ_three, lightConeCoeff] at h
  rw [eq_zero_of_ne hc (d := ![Sum.inl 0, Sum.inr 2]) (by simp),
    eq_zero_of_ne hc (d := ![Sum.inr 2, Sum.inl 0]) (by simp)] at h
  linear_combination h

/-- An invariant coefficient tensor is `c_tt` times the Minkowski metric. -/
lemma eq_smul_minkowskiMatrixZ {c : (Fin 2 → Fin 1 ⊕ Fin 3) → ℂ} (hc : IsInvariantCoeff c)
    (d : Fin 2 → Fin 1 ⊕ Fin 3) :
    c d = c ![Sum.inl 0, Sum.inl 0] * ((minkowskiMatrixZ (d 0) (d 1) : ℤ) : ℂ) := by
  by_cases hd : d 0 = d 1
  · have hd' : d = ![d 0, d 0] := by
      funext s
      fin_cases s
      · rfl
      · exact hd.symm
    rw [hd', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero]
    rcases d 0 with a | j
    · rw [Subsingleton.elim a 0]
      simp [minkowskiMatrixZ]
    · rw [apply_inr_inr_eq hc j]
      simp [minkowskiMatrixZ]
      linear_combination apply_inl_inl_add_apply_inr_inr hc
  · rw [eq_zero_of_ne hc hd]
    simp [minkowskiMatrixZ, Matrix.diagonal_apply_ne _ hd]

/-- Every Lorentz invariant in the span of the components is a multiple of the metric
  contraction. -/
theorem exists_smul_metricContraction_of_invariant (hT : IsLorentzCovariant 2 B repLorentz T)
    {x : B} (hx : x ∈ Submodule.span ℂ (Set.range T)) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, x = a • metricContraction (T := T) := by
  obtain ⟨c, hc, rfl⟩ := hT.exists_isInvariantCoeff_of_mem_span_range hx hinv
  refine ⟨c ![Sum.inl 0, Sum.inl 0], ?_⟩
  rw [metricContraction, Finset.smul_sum]
  exact Finset.sum_congr rfl fun d _ => by rw [smul_smul, ← eq_smul_minkowskiMatrixZ hc d]

/-!

## C. The classification modulo a Lorentz-stable submodule

A stable subspace `S` is divided out by passing to the quotient `B ⧸ S`, that is `B` with
`S` declared zero: the classes of the components again form a rank-two family, so
section B applies there and lifts back with an error term in `S`.

-/

/-- The quotient map carries the metric contraction to the metric contraction of the
  images. -/
lemma mkQ_metricContraction (S : Submodule ℂ B) :
    S.mkQ (metricContraction (T := T))
      = metricContraction (T := fun l => S.mkQ (T l)) := by
  rw [metricContraction, metricContraction, map_sum]
  exact Finset.sum_congr rfl fun d _ => map_smul _ _ _

/-- The same modulo a Lorentz-stable subspace `S`: a multiple of the metric contraction plus an
  error in `S`. -/
lemma exists_smul_metricContraction_of_invariant_subset
    (hT : IsLorentzCovariant 2 B repLorentz T) {x : B} (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S)
    (hx : x ∈ Submodule.span ℂ (Set.range T) ⊔ S) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, ∃ y ∈ S, x = a • metricContraction (T := T) + y := by
  obtain ⟨a, y, hy, rfl, -⟩ := IsStableUnder.exists_smul_add_of_quotient
    (σ := fun g : SL(2,ℂ) => repLorentz g) hS (repLorentz_metricContraction hT)
    (fun z hz hzinv => by
      rw [mkQ_metricContraction]
      exact exists_smul_metricContraction_of_invariant (hT.quotient S hS)
        ((Submodule.map_span_range S.mkQ T).le hz) hzinv) hx hinv
  exact ⟨a, y, hy, rfl⟩

end RankTwo

end Lorentz
