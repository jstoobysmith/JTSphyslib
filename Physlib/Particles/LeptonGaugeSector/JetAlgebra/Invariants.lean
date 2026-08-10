/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.Invariants.SpanOfRenormalizableTerms
/-!
# Classification of the renormalizable Lagrangian densities of the lepton–gauge sector

The gauge- and Lorentz-invariant elements of the lepton–gauge-sector jet algebra of mass
dimension at most four are exactly the linear combinations of the constants,
the Maxwell term, the theta term and the two fermion kinetic terms:

`InvariantMassWeightSubmodule 8 = span ℂ massDimFourInvariants`.

The inclusion `≥` is `span_massDimFourInvariants_le`. For `≤`, an invariant
`x` of weight `≤ 8` decomposes into `massWeightScale`-eigenvectors, each
lying in a `covMonomialSpan`; the rotation and hypercharge selection rules leave
only the neutral even-weight components, the weight-four and weight-six
sectors are killed by the rotation average and `rotationPiBoostAvg`, and the weight-eight
sector is pinned down by the projector `boostAvgScalarProj`.

## The two techniques, and the layout of `Invariants/`

Everything below the top level rests on one principle, proved in
`Invariants/GroupAverage`. If `T` is a linear operator built from the group
action which fixes every invariant vector, then for an invariant `y` lying in a
span,

`y ∈ span S` and `T y = y` give `y = T y ∈ span (T '' S)`,

so it suffices to compute `T v` for the finitely many `v ∈ S`. The operators
used are of two kinds:

* genuine averages over a finite subgroup — `rotationPiAvg` is the Reynolds
  operator of the Klein four-group `{1, R_x, R_y, R_z}` of rotations by `π`.
  Such an average is idempotent, so it projects onto the invariants outright;
* weighted combinations whose weights sum to one, so that they still fix the
  invariants, but which are engineered to annihilate the unwanted eigenvalues
  of the operator they are built from. The boosts are non-compact and admit no
  invariant average, so `boostAvgZ`, `boostAvgX`, `boostAvgY` pair `B(t)` with
  `B(t)⁻¹` at `t = 2, 3, 4` with rational weights and `boostAvg` is their mean
  over the three axes, while `rotationPiBoostAvg` weights the identity against
  two `z`-boosts. Despite the names these are not idempotent, and the last step
  of the argument needs one that is: `boostAvgScalarProj` is the degree-five
  polynomial in `boostAvg` vanishing on each of its other five eigenvalues and
  equal to one on the invariants — a spectral projector, not an average.

Alongside these sit the reduction steps, which cut the problem down to a
finite spanning set before any operator is applied: separation of components
by a character (the powers `c ^ m` for the mass weight, roots of unity for the
hypercharge), selection rules read off a single group element (the gauge
element with `u 0 = i` kills every odd-weight component), and the explicit
monomial spanning sets of each sector.

The subdirectories group the files by which of these they carry, and each
subgroup sits opposite the average taken over it.

* `Invariants/GroupAverage` — the averaging principle itself, stated for an
  arbitrary representation: the span lemma above, weighted sums of group
  elements, the average over a finite subgroup, and the fact that a polynomial
  with unit coefficient sum in an operator fixing `y` again fixes `y`.
* `Invariants/Grading/` — which grading is being used.
  `MassWeightAndHypercharge` builds the two gradings, by mass weight and by
  hypercharge, together with the selection rules that follow from them.
  `NeutralSectors` reduces each charge-neutral sector of weight four, six and
  eight to a finite explicit spanning family of monomials.
* `Invariants/Subgroups/` — which subgroup, acting on what. `RotationsPi`
  defines the rotations by `π` and the subgroup they generate; `AxisBoosts`
  defines the one-parameter boosts along the three coordinate axes and the two
  fixed `z`-boosts; `BoostsOnFieldStrength`,
  `BoostsOnFieldStrengthDerivatives`, `BoostsOnPhotonTerms` and
  `BoostsOnFermionTerms` tabulate how the boosts move `F_{μν}`,
  `∂_ρ ∂_τ F_{μν}`, the products `F F` and the fermion bilinears.
* `Invariants/Averages/` — the average over each of those subgroups, and what
  it does to the monomials. `RotationAverage` stands opposite
  `Subgroups/RotationsPi` and kills the weight-four sector;
  `RotationPiBoostAverage` follows it with a weighting of the two `z`-boosts
  and kills the weight-six sector; `BoostAverage` stands opposite
  `Subgroups/AxisBoosts` and, the boosts being non-compact, replaces the
  missing invariant average by the weighted combinations `boostAvgZ/X/Y` and
  their mean `boostAvg`. `BoostAvgProjector` then turns `boostAvg` into a
  genuine projector, and `BoostAvgProjectorOnPhotonPairs`,
  `BoostAvgProjectorOnDerivativesAndFermions` and
  `BoostAvgProjectorOnMonomials` evaluate it on each kind of weight-eight term.

`Invariants/Basic` (the four renormalizable terms, defined one per file in
`LeptonGaugeSector/JetAlgebra/Terms/`, collected into one set together with the easy
inclusion) and `Invariants/SpanOfRenormalizableTerms` (the projected monomials
land in their span) bracket these and stay at the top level.
-/

@[expose] public section

set_option maxHeartbeats 1000000

namespace LeptonGaugeSector
open TensorProduct StandardModel

namespace JetAlgebra

open scoped minkowskiMatrix PauliMatrix
open Matrix MatrixGroups

set_option maxHeartbeats 4000000 in
/-- The weight-eight classification: a Lorentz-invariant neutral element of
  mass weight eight is a combination of the Maxwell term, the theta term, and
  the two fermion kinetic terms. -/
lemma mem_span_of_mem_chargeCovSpan_eight {y : JetAlgebra}
    (hy : y ∈ chargeCovSpan 8 0)
    (hinv : ∀ Λ : SL(2,ℂ), repLorentzGroup Λ y = y) :
    y ∈ Submodule.span ℂ massDimFourInvariants := by
  have h := chargeCovSpan_eight_le hy
  rw [Submodule.span_union, Submodule.span_union, Submodule.span_union,
    Submodule.span_union, Submodule.span_union] at h
  obtain ⟨u5, hu5, w6, hw6, hE6⟩ := Submodule.mem_sup.mp h
  obtain ⟨u4, hu4, w5, hw5, hE5⟩ := Submodule.mem_sup.mp hu5
  obtain ⟨u3, hu3, w4, hw4, hE4⟩ := Submodule.mem_sup.mp hu4
  obtain ⟨u2, hu2, w3, hw3, hE3⟩ := Submodule.mem_sup.mp hu3
  obtain ⟨w1, hw1, w2, hw2, hE2⟩ := Submodule.mem_sup.mp hu2
  obtain ⟨c1, hc1⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hw1
  obtain ⟨c2, hc2⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hw2
  obtain ⟨c3, hc3⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hw3
  obtain ⟨c4, hc4⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hw4
  obtain ⟨c5, hc5⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hw5
  obtain ⟨c6, hc6⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hw6
  have hKy : rotationPiAvg y = y := by
    rw [rotationPiAvg_apply, hinv rotationPiZ, hinv rotationPiY, hinv rotationPiX]
    module
  have hself : boostAvgScalarProj (rotationPiAvg y) = y := by
    rw [hKy]
    exact boostAvgScalarProj_apply_of_invariant hinv
  rw [← hself, ← hE6, ← hE5, ← hE4, ← hE3, ← hE2, ← hc1, ← hc2, ← hc3, ← hc4,
    ← hc5, ← hc6]
  simp only [map_add, map_sum, map_smul]
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_) ?_) ?_
  · exact Submodule.sum_mem _ fun p _ =>
      Submodule.smul_mem _ _ (boostAvgScalarProj_rotationPiAvg_FF_mem p.1.1 p.1.2 p.2.1 p.2.2)
  · exact Submodule.sum_mem _ fun p _ =>
      Submodule.smul_mem _ _ (boostAvgScalarProj_rotationPiAvg_DDF_mem p.1.1 p.1.2 p.2.1 p.2.2)
  · exact Submodule.sum_mem _ fun p _ =>
      Submodule.smul_mem _ _ (boostAvgScalarProj_rotationPiAvg_FM1_mem p.2 p.1.1 p.1.2)
  · exact Submodule.sum_mem _ fun p _ =>
      Submodule.smul_mem _ _ (boostAvgScalarProj_rotationPiAvg_FM1r_mem p.2 p.1.1 p.1.2)
  · exact Submodule.sum_mem _ fun p _ =>
      Submodule.smul_mem _ _ (boostAvgScalarProj_rotationPiAvg_FM2r_mem p.2 p.1.1 p.1.2)
  · exact Submodule.sum_mem _ fun p _ =>
      Submodule.smul_mem _ _ (boostAvgScalarProj_rotationPiAvg_FM2_mem p.2 p.1.2 p.1.1)

/-- The classification of the renormalizable Lagrangian densities of the lepton–gauge sector: the
  gauge- and Lorentz-invariant elements of mass weight at most eight are spanned
  by the constants, the Maxwell term, the theta term, and the two fermion
  kinetic terms.

  The inclusion `⊇` is `span_massDimFourInvariants_le`: each of the five
  elements is invariant and of weight at most eight.

  The completeness direction `⊆` is proved as follows.
  1. By `InvariantSubmodule.mem_iff_isInvariant` and
     `isInvariant_iff_mem_adjoin_invariantGenerators`, an invariant `x` of
     weight at most eight lies in the algebra generated by the covariant
     generators, is fixed by the jets of constant gauge transformations, and is
     Lorentz invariant.
  2. Graded decomposition (`exists_covMonomialSpan_decomp`): `x` is a sum of
     nine components `z m ∈ covMonomialSpan m` of exact weights `0, …, 8`,
     using the homogeneity of the covariant monomials and the linear
     independence of the powers `c ↦ c ^ m`
     (`eq_zero_of_forall_sum_pow_smul_eq_zero`).
  3. Componentwise invariance: the mass-dimension scaling commutes with the
     Lorentz action and with the constant gauge action, so each component
     `z m` inherits both invariances, again by independence of powers.
  4. Sector analysis. `m = 0`: the weight-zero monomial span is the constants.
     `m = 1, 2`: there are no covariant monomials of these weights, since the
     generators have weights at least three. Odd `m = 3, 5, 7`: odd weight
     forces an odd number of fermionic factors, and the constant gauge
     transformation with `u(0) = i` acts on such a monomial by
     `(i⁶)^{n_ψ} ((-i)⁶)^{n_ψ̄} = (-1)^{n_ψ + n_ψ̄} = -1`, so invariance forces
     `z m = 0`. `m = 4, 6`: after splitting off the hypercharge `±12` sectors
     with a further root of unity, the surviving monomials (`F_{μν}`;
     `∂_ρ F_{μν}` and the zero-derivative fermion pairs `ψ̄_α ψ_β`) admit no
     Lorentz invariant. `m = 8`: the charge-balanced monomials are `F · F`,
     `∂∂F`, and the one-derivative fermion pairs; their Lorentz invariants are
     spanned by the Maxwell term, the theta term, and the two σ-contracted
     kinetic terms.

  Steps 3–4 remain to be formalized: they require the commutation of the
  scaling with the two group actions at the sector level, the linear independence
  of the covariant monomials, and the invariant theory of `SL(2,ℂ)` on the
  finite-dimensional weight sectors. -/
lemma invariantMassWeightSubmodule_eight_eq_span_massDimFourInvariants :
    InvariantMassWeightSubmodule 8 = Submodule.span ℂ massDimFourInvariants := by
  refine le_antisymm ?_ span_massDimFourInvariants_le
  intro x hx
  obtain ⟨hxw, hxinv⟩ := Submodule.mem_inf.mp hx
  rw [InvariantSubmodule.mem_iff_isInvariant] at hxinv
  obtain ⟨hadj, hconst, hlor⟩ :=
    (isInvariant_iff_mem_adjoin_invariantGenerators x).mp hxinv
  obtain ⟨z, hzmem, hxeq⟩ := exists_covMonomialSpan_decomp hxw hadj
  rw [hxeq]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hzlor : ∀ Λ : SL(2,ℂ), repLorentzGroup Λ (z m) = z m := fun Λ =>
    repLorentzGroup_covComponent_eq hzmem Λ (by rw [← hxeq]; exact hlor Λ) hm
  have hzconst : ∀ g : GaugeGroupI,
      repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) (z m) = z m := fun g =>
    repJetGaugeGroupI_ofConstant_covComponent_eq hzmem g
      (by rw [← hxeq]; exact hconst g) hm
  have hm9 := Finset.mem_range.mp hm
  interval_cases m
  · exact Submodule.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
      (covMonomialSpan_zero_le (hzmem 0))
  · rw [show z 1 = 0 from (Submodule.mem_bot ℂ).mp
      (covMonomialSpan_le_bot_of_lt_three le_rfl (by omega) (hzmem 1))]
    exact Submodule.zero_mem _
  · rw [show z 2 = 0 from (Submodule.mem_bot ℂ).mp
      (covMonomialSpan_le_bot_of_lt_three (by omega) (by omega) (hzmem 2))]
    exact Submodule.zero_mem _
  · rw [eq_zero_of_mem_covMonomialSpan_odd (by norm_num) (hzmem 3)
      (hzconst fermionParityGauge)]
    exact Submodule.zero_mem _
  · rw [eq_zero_of_mem_chargeCovSpan_four
      (mem_chargeCovSpan_zero_of_invariant (hzmem 4) hzconst) hzlor]
    exact Submodule.zero_mem _
  · rw [eq_zero_of_mem_covMonomialSpan_odd (by norm_num) (hzmem 5)
      (hzconst fermionParityGauge)]
    exact Submodule.zero_mem _
  · rw [eq_zero_of_mem_chargeCovSpan_six
      (mem_chargeCovSpan_zero_of_invariant (hzmem 6) hzconst) hzlor]
    exact Submodule.zero_mem _
  · rw [eq_zero_of_mem_covMonomialSpan_odd (by norm_num) (hzmem 7)
      (hzconst fermionParityGauge)]
    exact Submodule.zero_mem _
  · exact mem_span_of_mem_chargeCovSpan_eight
      (mem_chargeCovSpan_zero_of_invariant (hzmem 8) hzconst) hzlor
end JetAlgebra

end LeptonGaugeSector
