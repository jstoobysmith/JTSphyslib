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
