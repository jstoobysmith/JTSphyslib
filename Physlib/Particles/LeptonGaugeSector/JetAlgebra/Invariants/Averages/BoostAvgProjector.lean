/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.Invariants.Averages.BoostAverage
/-!
# The scalar projector built from the boost average

`boostAvgScalarProj` is *not* an average. It is a polynomial in the boost
average `boostAvg` of `Averages/BoostAverage`, and the distinction matters.

An average over a finite subgroup is idempotent, so it projects onto the
invariants outright. The boosts are not finite — not even compact — and
`boostAvg` is only a weighted combination with weights summing to one: it fixes
every Lorentz-invariant element, but it is not idempotent, and on the
rotation-averaged weight-eight sector it acts with the six eigenvalues
`1, 5/6, 2/3, 1/2, 1/3, 1/6`. The invariants are exactly the eigenvalue-one
eigenspace.

Turning that operator into a projector is Sylvester's formula: for the unique
quintic `p` with `p 1 = 1` and `p λ = 0` at the other five eigenvalues,

`p x = (324/5) (x - 5/6) (x - 2/3) (x - 1/2) (x - 1/3) (x - 1/6)`
`    = -1 + (137/10) x - (135/2) x² + 153 x³ - 162 x⁴ + (324/5) x⁵,`

the operator `p boostAvg` kills every other eigenspace and is the identity on
the invariants. That operator is `boostAvgScalarProj`. Its coefficients sum to
one, so `Module.End.sum_smul_pow_apply_of_apply_eq_self` of
`Invariants/GroupAverage` applies verbatim and it fixes Lorentz invariants just
as an average would (`boostAvgScalarProj_apply_of_invariant`); that is all the
averaging principle ever needs of it.

Its values on the weight-eight monomials are computed in
`BoostAvgProjectorOnPhotonPairs`, `BoostAvgProjectorOnDerivativesAndFermions`
and `BoostAvgProjectorOnMonomials`.
-/

@[expose] public section

set_option maxHeartbeats 1000000

namespace LeptonGaugeSector
open TensorProduct StandardModel

namespace JetAlgebra

open scoped minkowskiMatrix PauliMatrix
open Matrix MatrixGroups

/-!

## A. Sylvester's polynomial

The projector is a polynomial in the boost average, so it acts on an eigenvector of that average
by the value of the polynomial at the eigenvalue. Since the polynomial was built to take the
value one at the eigenvalue one and to vanish at the other five, every computation of the
projector on a concrete vector reduces to a single linear-algebra step: decompose the vector
into eigenvectors of `boostAvg` and read off the eigenvalue-one part. No iterate of the operator
ever has to be computed.

-/

/-- Sylvester's interpolation polynomial for the spectrum of the boost average:
  `(324/5) (c - 5/6) (c - 2/3) (c - 1/2) (c - 1/3) (c - 1/6)`, normalized to take the value one
  at `c = 1`. -/
noncomputable def sylvester (c : ℂ) : ℂ :=
  -1 + (137/10) * c + (-(135/2)) * c ^ 2 + 153 * c ^ 3 + (-162) * c ^ 4 + (324/5) * c ^ 5

@[simp] lemma sylvester_one : sylvester (1 : ℂ) = 1 := by norm_num [sylvester]
@[simp] lemma sylvester_five_sixths : sylvester (5/6 : ℂ) = 0 := by norm_num [sylvester]
@[simp] lemma sylvester_two_thirds : sylvester (2/3 : ℂ) = 0 := by norm_num [sylvester]
@[simp] lemma sylvester_half : sylvester (1/2 : ℂ) = 0 := by norm_num [sylvester]
@[simp] lemma sylvester_third : sylvester (1/3 : ℂ) = 0 := by norm_num [sylvester]
@[simp] lemma sylvester_sixth : sylvester (1/6 : ℂ) = 0 := by norm_num [sylvester]

/-- Sylvester's polynomial evaluated on an endomorphism. Stated for an arbitrary module, since
  nothing about the jet algebra is used. -/
noncomputable def sylvesterEnd {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) : Module.End ℂ M :=
  (-1 : ℂ) • T ^ 0 + (137/10 : ℂ) • T ^ 1 + (-(135/2) : ℂ) • T ^ 2 + (153 : ℂ) • T ^ 3
    + (-162 : ℂ) • T ^ 4 + (324/5 : ℂ) • T ^ 5

lemma sylvesterEnd_apply {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) (v : M) :
    sylvesterEnd T v = (-1 : ℂ) • v + (137/10 : ℂ) • T v + (-(135/2) : ℂ) • T (T v)
      + (153 : ℂ) • T (T (T v)) + (-162 : ℂ) • T (T (T (T v)))
      + (324/5 : ℂ) • T (T (T (T (T v)))) := by
  simp [sylvesterEnd, pow_succ, Module.End.mul_apply]

lemma pow_apply_of_eigen {M : Type*} [AddCommGroup M] [Module ℂ M]
    {T : Module.End ℂ M} {c : ℂ} {v : M} (h : T v = c • v) (n : ℕ) :
    (T ^ n) v = c ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, h, map_smul, ih, smul_smul, pow_succ]
    ring_nf

/-- On an eigenvector, a polynomial in the operator acts by the value of the polynomial at the
  eigenvalue. This is the only fact about `sylvesterEnd` that the computations need. -/
lemma sylvesterEnd_of_eigen {M : Type*} [AddCommGroup M] [Module ℂ M]
    {T : Module.End ℂ M} {c : ℂ} {v : M} (h : T v = c • v) :
    sylvesterEnd T v = sylvester c • v := by
  simp only [sylvesterEnd, LinearMap.add_apply, LinearMap.smul_apply, pow_apply_of_eigen h,
    smul_smul, sylvester]
  module

/-!

## B. The projector

-/

/-- The spectral projector onto the Lorentz scalars, obtained from the boost
  average `boostAvg` by Sylvester's formula. Not an average itself: it is the
  unique quintic in `boostAvg` taking the value one at the eigenvalue one and
  vanishing at the other five eigenvalues `5/6, 2/3, 1/2, 1/3, 1/6` of
  `boostAvg` on the rotation-averaged weight-eight sector, namely
  `(324/5) (x - 5/6) (x - 2/3) (x - 1/2) (x - 1/3) (x - 1/6)`. Unlike `boostAvg`
  it is idempotent there, which is what pins the sector down. -/
noncomputable def boostAvgScalarProj : Module.End ℂ JetAlgebra :=
  (-1 : ℂ) • (1 : Module.End ℂ JetAlgebra) + (137/10 : ℂ) • boostAvg
    + (-(135/2) : ℂ) • (boostAvg * boostAvg) + (153 : ℂ) • (boostAvg * boostAvg * boostAvg)
    + (-162 : ℂ) • (boostAvg * boostAvg * boostAvg * boostAvg)
    + (324/5 : ℂ) • (boostAvg * boostAvg * boostAvg * boostAvg * boostAvg)

/-- The projector polynomial, termwise. -/
lemma boostAvgScalarProj_apply (v : JetAlgebra) :
    boostAvgScalarProj v = (-1 : ℂ) • v + (137/10 : ℂ) • boostAvg v
      + (-(135/2) : ℂ) • boostAvg (boostAvg v) + (153 : ℂ) • boostAvg (boostAvg (boostAvg v))
      + (-162 : ℂ) • boostAvg (boostAvg (boostAvg (boostAvg v)))
      + (324/5 : ℂ) • boostAvg (boostAvg (boostAvg (boostAvg (boostAvg v)))) := by
  simp only [boostAvgScalarProj, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    Module.End.mul_apply]

/-- The projector is Sylvester's polynomial evaluated on the boost average. -/
lemma boostAvgScalarProj_eq_sylvesterEnd : boostAvgScalarProj = sylvesterEnd boostAvg := by
  simp [boostAvgScalarProj, sylvesterEnd, pow_succ]

/-- On an eigenvector of the boost average the projector acts by the value of Sylvester's
  polynomial at the eigenvalue. Together with `sylvester_one` and the four vanishing values
  this reduces every evaluation of the projector to an eigenvector decomposition. -/
lemma boostAvgScalarProj_of_eigen {c : ℂ} {v : JetAlgebra} (h : boostAvg v = c • v) :
    boostAvgScalarProj v = sylvester c • v := by
  rw [boostAvgScalarProj_eq_sylvesterEnd, sylvesterEnd_of_eigen h]

/-- The projector fixes every Lorentz-invariant vector: `boostAvg` fixes it and the
  coefficients sum to one. -/
lemma boostAvgScalarProj_apply_of_invariant {y : JetAlgebra}
    (hinv : ∀ Λ : SL(2,ℂ), repLorentzGroup Λ y = y) : boostAvgScalarProj y = y := by
  have hS : boostAvg y = y := boostAvg_apply_of_invariant hinv
  rw [boostAvgScalarProj_apply]
  simp only [hS]
  match_scalars
  norm_num

end JetAlgebra

end LeptonGaugeSector
