/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.Invariants.Averages.BoostAvgProjector
/-!
# The Lorentz-scalar projector on the photon pairs

`boostAvgScalarProj` is the polynomial in `boostAvg` that annihilates every eigenvalue of
`boostAvg` other than `1`; it therefore fixes the Lorentz-invariant vectors and projects the
weight-eight monomials onto the invariant subspace. The `scalarProjFF*` lemmas evaluate that
polynomial on the nine products of two field strengths.

Each is proved by decomposing the monomial into eigenvectors of the average and applying
`sylvesterEnd_of_eigen`: the polynomial was built to kill the five non-unit eigenvalues, so only
the eigenvalue-one part survives. On the six squares `F01_F01, …, F23_F23` the average acts as
`2/3 - (1/6) A` for `A` the adjacency of the six-cycle `F01, F12, F02, F23, F03, F13`, whose
eigenvalues `2, 1, 1, -1, -1, -2` give the average the eigenvalues `1/3, 1/2, 1/2, 5/6, 5/6, 1`;
the alternating vector around that cycle is the Maxwell term. On the three products
`F01_F23, F02_F13, F03_F12` the average has eigenvalues `1/2, 1/2, 1`, the invariant being the
theta term.

No iterate of the operator is computed: every proof applies the average once, inside the
eigenvector lemmas, which is why no heartbeat bump is needed here.
-/

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace LeptonGaugeSector
open TensorProduct StandardModel

namespace JetAlgebra

open scoped minkowskiMatrix PauliMatrix
open Matrix MatrixGroups

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 : M}
variable
    (h0 : T v0 = (2/3 : ℂ) • v0 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v7)
    (h1 : T v1 = (2/3 : ℂ) • v1 + (-(1/6) : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h2 : T v2 = (2/3 : ℂ) • v2 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v8)
    (h3 : T v3 = (2/3 : ℂ) • v3 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h4 : T v4 = (2/3 : ℂ) • v4 + (-(1/6) : ℂ) • v7 + (-(1/6) : ℂ) • v8)
    (h5 : T v5 = (2/3 : ℂ) • v5 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (-(1/6) : ℂ) • v2 + (-(1/6) : ℂ) • v4)

/-!

## A. The eigenvectors of the average on the field-strength squares

-/

include h0 h2 h4 h6 h7 h8 in
/-- The Maxwell combination is invariant: the alternating vector on the six-cycle. -/
lemma ffEigenMaxwell : T (v0 + v2 + v4 - v6 - v7 - v8) = (1 : ℂ) • (v0 + v2 + v4 - v6 - v7 - v8) := by
  simp only [map_add, map_sub, h0, h2, h4, h6, h7, h8]
  module

include h0 h2 h4 h6 h7 h8 in
/-- The total sum of the squares is an eigenvector of eigenvalue `1/3`. -/
lemma ffEigenTrace : T (v0 + v2 + v4 + v6 + v7 + v8) = (1/3 : ℂ) • (v0 + v2 + v4 + v6 + v7 + v8) := by
  simp only [map_add, h0, h2, h4, h6, h7, h8]
  module

include h0 h2 h4 h6 h7 h8 in
/-- First eigenvector of eigenvalue `1/2`. -/
lemma ffEigenHalf₁ : T ((2 : ℂ) • v0 - v2 - v4 + v6 + v7 - (2 : ℂ) • v8) =
    (1/2 : ℂ) • ((2 : ℂ) • v0 - v2 - v4 + v6 + v7 - (2 : ℂ) • v8) := by
  simp only [map_add, map_sub, map_smul, h0, h2, h4, h6, h7, h8]
  module

include h2 h4 h6 h7 in
/-- Second eigenvector of eigenvalue `1/2`. -/
lemma ffEigenHalf₂ : T (v2 - v4 + v6 - v7) = (1/2 : ℂ) • (v2 - v4 + v6 - v7) := by
  simp only [map_add, map_sub, h2, h4, h6, h7]
  module

include h0 h2 h4 h6 h7 h8 in
/-- First eigenvector of eigenvalue `5/6`. -/
lemma ffEigenFiveSixths₁ : T ((2 : ℂ) • v0 - v2 - v4 - v6 - v7 + (2 : ℂ) • v8) =
    (5/6 : ℂ) • ((2 : ℂ) • v0 - v2 - v4 - v6 - v7 + (2 : ℂ) • v8) := by
  simp only [map_add, map_sub, map_smul, h0, h2, h4, h6, h7, h8]
  module

include h2 h4 h6 h7 in
/-- Second eigenvector of eigenvalue `5/6`. -/
lemma ffEigenFiveSixths₂ : T (-v2 + v4 + v6 - v7) = (5/6 : ℂ) • (-v2 + v4 + v6 - v7) := by
  simp only [map_add, map_sub, map_neg, h2, h4, h6, h7]
  module

/-!

## B. The eigenvectors of the average on the dual pairs

-/

include h1 h3 h5 in
/-- The theta combination is invariant. -/
lemma ffEigenTheta : T (v1 - v3 + v5) = (1 : ℂ) • (v1 - v3 + v5) := by
  simp only [map_add, map_sub, h1, h3, h5]
  module

include h1 h3 in
/-- First eigenvector of eigenvalue `1/2` on the dual pairs. -/
lemma ffEigenThetaHalf₁ : T (v1 + v3) = (1/2 : ℂ) • (v1 + v3) := by
  simp only [map_add, h1, h3]
  module

include h1 h5 in
/-- Second eigenvector of eigenvalue `1/2` on the dual pairs. -/
lemma ffEigenThetaHalf₂ : T (-v1 + v5) = (1/2 : ℂ) • (-v1 + v5) := by
  simp only [map_add, map_neg, h1, h5]
  module

/-!

## C. The projector on each column

-/

include h0 h1 h2 h3 h4 h5 h6 h7 h8 in
/-- The projector polynomial on column 0 of the FF block, the field-strength square `F01_F01`. -/
lemma scalarProjFF0 :
    (-1 : ℂ) • v0 + (137/10 : ℂ) • T v0 + (-(135/2) : ℂ) • T (T v0)
      + (153 : ℂ) • T (T (T v0)) + (-162 : ℂ) • T (T (T (T v0)))
      + (324/5 : ℂ) • T (T (T (T (T v0)))) =
    (-(1/12) : ℂ) • ((-2 : ℂ) • v0 + (-2 : ℂ) • v2 + (-2 : ℂ) • v4 + (2 : ℂ) • v6 + (2 : ℂ) • v7 +
        (2 : ℂ) • v8) := by
  have key : sylvesterEnd T v0 = (1/6 : ℂ) • (v0 + v2 + v4 - v6 - v7 - v8) := by
    conv_lhs =>
      rw [show v0 = (1/6 : ℂ) • (v0 + v2 + v4 - v6 - v7 - v8)
          + (1/6 : ℂ) • (v0 + v2 + v4 + v6 + v7 + v8)
          + (1/6 : ℂ) • ((2 : ℂ) • v0 - v2 - v4 + v6 + v7 - (2 : ℂ) • v8)
          + (1/6 : ℂ) • ((2 : ℂ) • v0 - v2 - v4 - v6 - v7 + (2 : ℂ) • v8) from by module]
    simp only [map_add, map_smul,
      sylvesterEnd_of_eigen (ffEigenMaxwell T h0 h2 h4 h6 h7 h8),
      sylvesterEnd_of_eigen (ffEigenTrace T h0 h2 h4 h6 h7 h8),
      sylvesterEnd_of_eigen (ffEigenHalf₁ T h0 h2 h4 h6 h7 h8),
      sylvesterEnd_of_eigen (ffEigenFiveSixths₁ T h0 h2 h4 h6 h7 h8),
      sylvester_one, sylvester_third, sylvester_half, sylvester_five_sixths]
    module
  rw [← sylvesterEnd_apply, key]
  module

include h0 h1 h2 h3 h4 h5 h6 h7 h8 in
/-- The projector polynomial on column 1 of the FF block, the field-strength product `F01_F23`. -/
lemma scalarProjFF1 :
    (-1 : ℂ) • v1 + (137/10 : ℂ) • T v1 + (-(135/2) : ℂ) • T (T v1)
      + (153 : ℂ) • T (T (T v1)) + (-162 : ℂ) • T (T (T (T v1)))
      + (324/5 : ℂ) • T (T (T (T (T v1)))) =
    (1/24 : ℂ) • ((8 : ℂ) • v1 + (-8 : ℂ) • v3 + (8 : ℂ) • v5) := by
  have key : sylvesterEnd T v1 = (1/3 : ℂ) • (v1 - v3 + v5) := by
    conv_lhs =>
      rw [show v1 = (1/3 : ℂ) • (v1 - v3 + v5)
          + (1/3 : ℂ) • (v1 + v3)
          + (-(1/3) : ℂ) • (-v1 + v5) from by module]
    simp only [map_add, map_smul,
      sylvesterEnd_of_eigen (ffEigenTheta T h1 h3 h5),
      sylvesterEnd_of_eigen (ffEigenThetaHalf₁ T h1 h3),
      sylvesterEnd_of_eigen (ffEigenThetaHalf₂ T h1 h5),
      sylvester_one, sylvester_half]
    module
  rw [← sylvesterEnd_apply, key]
  module

include h0 h1 h2 h3 h4 h5 h6 h7 h8 in
/-- The projector polynomial on column 2 of the FF block, the field-strength square `F02_F02`. -/
lemma scalarProjFF2 :
    (-1 : ℂ) • v2 + (137/10 : ℂ) • T v2 + (-(135/2) : ℂ) • T (T v2)
      + (153 : ℂ) • T (T (T v2)) + (-162 : ℂ) • T (T (T (T v2)))
      + (324/5 : ℂ) • T (T (T (T (T v2)))) =
    (-(1/12) : ℂ) • ((-2 : ℂ) • v0 + (-2 : ℂ) • v2 + (-2 : ℂ) • v4 + (2 : ℂ) • v6 + (2 : ℂ) • v7 +
        (2 : ℂ) • v8) := by
  have key : sylvesterEnd T v2 = (1/6 : ℂ) • (v0 + v2 + v4 - v6 - v7 - v8) := by
    conv_lhs =>
      rw [show v2 = (1/6 : ℂ) • (v0 + v2 + v4 - v6 - v7 - v8)
          + (1/6 : ℂ) • (v0 + v2 + v4 + v6 + v7 + v8)
          + (-(1/12) : ℂ) • ((2 : ℂ) • v0 - v2 - v4 + v6 + v7 - (2 : ℂ) • v8)
          + (1/4 : ℂ) • (v2 - v4 + v6 - v7)
          + (-(1/12) : ℂ) • ((2 : ℂ) • v0 - v2 - v4 - v6 - v7 + (2 : ℂ) • v8)
          + (-(1/4) : ℂ) • (-v2 + v4 + v6 - v7) from by module]
    simp only [map_add, map_smul,
      sylvesterEnd_of_eigen (ffEigenMaxwell T h0 h2 h4 h6 h7 h8),
      sylvesterEnd_of_eigen (ffEigenTrace T h0 h2 h4 h6 h7 h8),
      sylvesterEnd_of_eigen (ffEigenHalf₁ T h0 h2 h4 h6 h7 h8),
      sylvesterEnd_of_eigen (ffEigenHalf₂ T h2 h4 h6 h7),
      sylvesterEnd_of_eigen (ffEigenFiveSixths₁ T h0 h2 h4 h6 h7 h8),
      sylvesterEnd_of_eigen (ffEigenFiveSixths₂ T h2 h4 h6 h7),
      sylvester_one, sylvester_third, sylvester_half, sylvester_five_sixths]
    module
  rw [← sylvesterEnd_apply, key]
  module

include h0 h1 h2 h3 h4 h5 h6 h7 h8 in
/-- The projector polynomial on column 3 of the FF block, the field-strength product `F02_F13`. -/
lemma scalarProjFF3 :
    (-1 : ℂ) • v3 + (137/10 : ℂ) • T v3 + (-(135/2) : ℂ) • T (T v3)
      + (153 : ℂ) • T (T (T v3)) + (-162 : ℂ) • T (T (T (T v3)))
      + (324/5 : ℂ) • T (T (T (T (T v3)))) =
    (-(1/24) : ℂ) • ((8 : ℂ) • v1 + (-8 : ℂ) • v3 + (8 : ℂ) • v5) := by
  have key : sylvesterEnd T v3 = (-(1/3) : ℂ) • (v1 - v3 + v5) := by
    conv_lhs =>
      rw [show v3 = (-(1/3) : ℂ) • (v1 - v3 + v5)
          + (2/3 : ℂ) • (v1 + v3)
          + (1/3 : ℂ) • (-v1 + v5) from by module]
    simp only [map_add, map_smul,
      sylvesterEnd_of_eigen (ffEigenTheta T h1 h3 h5),
      sylvesterEnd_of_eigen (ffEigenThetaHalf₁ T h1 h3),
      sylvesterEnd_of_eigen (ffEigenThetaHalf₂ T h1 h5),
      sylvester_one, sylvester_half]
    module
  rw [← sylvesterEnd_apply, key]
  module

include h0 h1 h2 h3 h4 h5 h6 h7 h8 in
/-- The projector polynomial on column 4 of the FF block, the field-strength square `F03_F03`. -/
lemma scalarProjFF4 :
    (-1 : ℂ) • v4 + (137/10 : ℂ) • T v4 + (-(135/2) : ℂ) • T (T v4)
      + (153 : ℂ) • T (T (T v4)) + (-162 : ℂ) • T (T (T (T v4)))
      + (324/5 : ℂ) • T (T (T (T (T v4)))) =
    (-(1/12) : ℂ) • ((-2 : ℂ) • v0 + (-2 : ℂ) • v2 + (-2 : ℂ) • v4 + (2 : ℂ) • v6 + (2 : ℂ) • v7 +
        (2 : ℂ) • v8) := by
  have key : sylvesterEnd T v4 = (1/6 : ℂ) • (v0 + v2 + v4 - v6 - v7 - v8) := by
    conv_lhs =>
      rw [show v4 = (1/6 : ℂ) • (v0 + v2 + v4 - v6 - v7 - v8)
          + (1/6 : ℂ) • (v0 + v2 + v4 + v6 + v7 + v8)
          + (-(1/12) : ℂ) • ((2 : ℂ) • v0 - v2 - v4 + v6 + v7 - (2 : ℂ) • v8)
          + (-(1/4) : ℂ) • (v2 - v4 + v6 - v7)
          + (-(1/12) : ℂ) • ((2 : ℂ) • v0 - v2 - v4 - v6 - v7 + (2 : ℂ) • v8)
          + (1/4 : ℂ) • (-v2 + v4 + v6 - v7) from by module]
    simp only [map_add, map_smul,
      sylvesterEnd_of_eigen (ffEigenMaxwell T h0 h2 h4 h6 h7 h8),
      sylvesterEnd_of_eigen (ffEigenTrace T h0 h2 h4 h6 h7 h8),
      sylvesterEnd_of_eigen (ffEigenHalf₁ T h0 h2 h4 h6 h7 h8),
      sylvesterEnd_of_eigen (ffEigenHalf₂ T h2 h4 h6 h7),
      sylvesterEnd_of_eigen (ffEigenFiveSixths₁ T h0 h2 h4 h6 h7 h8),
      sylvesterEnd_of_eigen (ffEigenFiveSixths₂ T h2 h4 h6 h7),
      sylvester_one, sylvester_third, sylvester_half, sylvester_five_sixths]
    module
  rw [← sylvesterEnd_apply, key]
  module

include h0 h1 h2 h3 h4 h5 h6 h7 h8 in
/-- The projector polynomial on column 5 of the FF block, the field-strength product `F03_F12`. -/
lemma scalarProjFF5 :
    (-1 : ℂ) • v5 + (137/10 : ℂ) • T v5 + (-(135/2) : ℂ) • T (T v5)
      + (153 : ℂ) • T (T (T v5)) + (-162 : ℂ) • T (T (T (T v5)))
      + (324/5 : ℂ) • T (T (T (T (T v5)))) =
    (1/24 : ℂ) • ((8 : ℂ) • v1 + (-8 : ℂ) • v3 + (8 : ℂ) • v5) := by
  have key : sylvesterEnd T v5 = (1/3 : ℂ) • (v1 - v3 + v5) := by
    conv_lhs =>
      rw [show v5 = (1/3 : ℂ) • (v1 - v3 + v5)
          + (1/3 : ℂ) • (v1 + v3)
          + (2/3 : ℂ) • (-v1 + v5) from by module]
    simp only [map_add, map_smul,
      sylvesterEnd_of_eigen (ffEigenTheta T h1 h3 h5),
      sylvesterEnd_of_eigen (ffEigenThetaHalf₁ T h1 h3),
      sylvesterEnd_of_eigen (ffEigenThetaHalf₂ T h1 h5),
      sylvester_one, sylvester_half]
    module
  rw [← sylvesterEnd_apply, key]
  module

include h0 h1 h2 h3 h4 h5 h6 h7 h8 in
/-- The projector polynomial on column 6 of the FF block, the field-strength square `F12_F12`. -/
lemma scalarProjFF6 :
    (-1 : ℂ) • v6 + (137/10 : ℂ) • T v6 + (-(135/2) : ℂ) • T (T v6)
      + (153 : ℂ) • T (T (T v6)) + (-162 : ℂ) • T (T (T (T v6)))
      + (324/5 : ℂ) • T (T (T (T (T v6)))) =
    (1/12 : ℂ) • ((-2 : ℂ) • v0 + (-2 : ℂ) • v2 + (-2 : ℂ) • v4 + (2 : ℂ) • v6 + (2 : ℂ) • v7 +
        (2 : ℂ) • v8) := by
  have key : sylvesterEnd T v6 = (-(1/6) : ℂ) • (v0 + v2 + v4 - v6 - v7 - v8) := by
    conv_lhs =>
      rw [show v6 = (-(1/6) : ℂ) • (v0 + v2 + v4 - v6 - v7 - v8)
          + (1/6 : ℂ) • (v0 + v2 + v4 + v6 + v7 + v8)
          + (1/12 : ℂ) • ((2 : ℂ) • v0 - v2 - v4 + v6 + v7 - (2 : ℂ) • v8)
          + (1/4 : ℂ) • (v2 - v4 + v6 - v7)
          + (-(1/12) : ℂ) • ((2 : ℂ) • v0 - v2 - v4 - v6 - v7 + (2 : ℂ) • v8)
          + (1/4 : ℂ) • (-v2 + v4 + v6 - v7) from by module]
    simp only [map_add, map_smul,
      sylvesterEnd_of_eigen (ffEigenMaxwell T h0 h2 h4 h6 h7 h8),
      sylvesterEnd_of_eigen (ffEigenTrace T h0 h2 h4 h6 h7 h8),
      sylvesterEnd_of_eigen (ffEigenHalf₁ T h0 h2 h4 h6 h7 h8),
      sylvesterEnd_of_eigen (ffEigenHalf₂ T h2 h4 h6 h7),
      sylvesterEnd_of_eigen (ffEigenFiveSixths₁ T h0 h2 h4 h6 h7 h8),
      sylvesterEnd_of_eigen (ffEigenFiveSixths₂ T h2 h4 h6 h7),
      sylvester_one, sylvester_third, sylvester_half, sylvester_five_sixths]
    module
  rw [← sylvesterEnd_apply, key]
  module

include h0 h1 h2 h3 h4 h5 h6 h7 h8 in
/-- The projector polynomial on column 7 of the FF block, the field-strength square `F13_F13`. -/
lemma scalarProjFF7 :
    (-1 : ℂ) • v7 + (137/10 : ℂ) • T v7 + (-(135/2) : ℂ) • T (T v7)
      + (153 : ℂ) • T (T (T v7)) + (-162 : ℂ) • T (T (T (T v7)))
      + (324/5 : ℂ) • T (T (T (T (T v7)))) =
    (1/12 : ℂ) • ((-2 : ℂ) • v0 + (-2 : ℂ) • v2 + (-2 : ℂ) • v4 + (2 : ℂ) • v6 + (2 : ℂ) • v7 +
        (2 : ℂ) • v8) := by
  have key : sylvesterEnd T v7 = (-(1/6) : ℂ) • (v0 + v2 + v4 - v6 - v7 - v8) := by
    conv_lhs =>
      rw [show v7 = (-(1/6) : ℂ) • (v0 + v2 + v4 - v6 - v7 - v8)
          + (1/6 : ℂ) • (v0 + v2 + v4 + v6 + v7 + v8)
          + (1/12 : ℂ) • ((2 : ℂ) • v0 - v2 - v4 + v6 + v7 - (2 : ℂ) • v8)
          + (-(1/4) : ℂ) • (v2 - v4 + v6 - v7)
          + (-(1/12) : ℂ) • ((2 : ℂ) • v0 - v2 - v4 - v6 - v7 + (2 : ℂ) • v8)
          + (-(1/4) : ℂ) • (-v2 + v4 + v6 - v7) from by module]
    simp only [map_add, map_smul,
      sylvesterEnd_of_eigen (ffEigenMaxwell T h0 h2 h4 h6 h7 h8),
      sylvesterEnd_of_eigen (ffEigenTrace T h0 h2 h4 h6 h7 h8),
      sylvesterEnd_of_eigen (ffEigenHalf₁ T h0 h2 h4 h6 h7 h8),
      sylvesterEnd_of_eigen (ffEigenHalf₂ T h2 h4 h6 h7),
      sylvesterEnd_of_eigen (ffEigenFiveSixths₁ T h0 h2 h4 h6 h7 h8),
      sylvesterEnd_of_eigen (ffEigenFiveSixths₂ T h2 h4 h6 h7),
      sylvester_one, sylvester_third, sylvester_half, sylvester_five_sixths]
    module
  rw [← sylvesterEnd_apply, key]
  module

include h0 h1 h2 h3 h4 h5 h6 h7 h8 in
/-- The projector polynomial on column 8 of the FF block, the field-strength square `F23_F23`. -/
lemma scalarProjFF8 :
    (-1 : ℂ) • v8 + (137/10 : ℂ) • T v8 + (-(135/2) : ℂ) • T (T v8)
      + (153 : ℂ) • T (T (T v8)) + (-162 : ℂ) • T (T (T (T v8)))
      + (324/5 : ℂ) • T (T (T (T (T v8)))) =
    (1/12 : ℂ) • ((-2 : ℂ) • v0 + (-2 : ℂ) • v2 + (-2 : ℂ) • v4 + (2 : ℂ) • v6 + (2 : ℂ) • v7 +
        (2 : ℂ) • v8) := by
  have key : sylvesterEnd T v8 = (-(1/6) : ℂ) • (v0 + v2 + v4 - v6 - v7 - v8) := by
    conv_lhs =>
      rw [show v8 = (-(1/6) : ℂ) • (v0 + v2 + v4 - v6 - v7 - v8)
          + (1/6 : ℂ) • (v0 + v2 + v4 + v6 + v7 + v8)
          + (-(1/6) : ℂ) • ((2 : ℂ) • v0 - v2 - v4 + v6 + v7 - (2 : ℂ) • v8)
          + (1/6 : ℂ) • ((2 : ℂ) • v0 - v2 - v4 - v6 - v7 + (2 : ℂ) • v8) from by module]
    simp only [map_add, map_smul,
      sylvesterEnd_of_eigen (ffEigenMaxwell T h0 h2 h4 h6 h7 h8),
      sylvesterEnd_of_eigen (ffEigenTrace T h0 h2 h4 h6 h7 h8),
      sylvesterEnd_of_eigen (ffEigenHalf₁ T h0 h2 h4 h6 h7 h8),
      sylvesterEnd_of_eigen (ffEigenFiveSixths₁ T h0 h2 h4 h6 h7 h8),
      sylvester_one, sylvester_third, sylvester_half, sylvester_five_sixths]
    module
  rw [← sylvesterEnd_apply, key]
  module

end JetAlgebra

end LeptonGaugeSector
