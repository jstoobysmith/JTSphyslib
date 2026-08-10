/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.Invariants.Averages.BoostAvgProjector
/-!
# The Lorentz-scalar projector on the photon pairs

`boostAvgScalarProj` is the polynomial in `boostAvg` that annihilates every eigenvalue of `boostAvg`
other than `1`; it therefore fixes the Lorentz-invariant vectors and projects
the weight-eight monomials onto the invariant subspace. The `scalarProjFF*`,
`scalarProjDDF*` and `scalarProjFMu*` lemmas evaluate that polynomial on each eigenvalue
pattern occurring in the weight-eight basis.
-/

@[expose] public section

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace LeptonGaugeSector
open TensorProduct StandardModel

namespace JetAlgebra

open scoped minkowskiMatrix PauliMatrix
open Matrix MatrixGroups

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 0 of the FF block. -/
lemma scalarProjFF0 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 : M}
    (h0 : T v0 = (2/3 : ℂ) • v0 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v7)
    (h1 : T v1 = (2/3 : ℂ) • v1 + (-(1/6) : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h2 : T v2 = (2/3 : ℂ) • v2 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v8)
    (h3 : T v3 = (2/3 : ℂ) • v3 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h4 : T v4 = (2/3 : ℂ) • v4 + (-(1/6) : ℂ) • v7 + (-(1/6) : ℂ) • v8)
    (h5 : T v5 = (2/3 : ℂ) • v5 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (-(1/6) : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v0 + (137/10 : ℂ) • T v0 + (-(135/2) : ℂ) • T (T v0)
      + (153 : ℂ) • T (T (T v0)) + (-162 : ℂ) • T (T (T (T v0)))
      + (324/5 : ℂ) • T (T (T (T (T v0)))) =
    (-(1/12) : ℂ) • ((-2 : ℂ) • v0 + (-2 : ℂ) • v2 + (-2 : ℂ) • v4 + (2 : ℂ) • v6 + (2 : ℂ) • v7 +
        (2 : ℂ) • v8) := by
  have i2 : T (T v0) =
      (1/2 : ℂ) • (v0)
      + (1/36 : ℂ) • (v2)
      + (1/36 : ℂ) • (v4)
      + (-(2/9) : ℂ) • (v6)
      + (-(2/9) : ℂ) • (v7) := by
    rw [h0]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i3 : T (T (T v0)) =
      (11/27 : ℂ) • (v0)
      + (1/18 : ℂ) • (v2)
      + (1/18 : ℂ) • (v4)
      + (-(17/72) : ℂ) • (v6)
      + (-(17/72) : ℂ) • (v7)
      + (-(1/108) : ℂ) • (v8) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v0))) =
      (227/648 : ℂ) • (v0)
      + (101/1296 : ℂ) • (v2)
      + (101/1296 : ℂ) • (v4)
      + (-(19/81) : ℂ) • (v6)
      + (-(19/81) : ℂ) • (v7)
      + (-(2/81) : ℂ) • (v8) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v0)))) =
      (101/324 : ℂ) • (v0)
      + (185/1944 : ℂ) • (v2)
      + (185/1944 : ℂ) • (v4)
      + (-(1771/7776) : ℂ) • (v6)
      + (-(1771/7776) : ℂ) • (v7)
      + (-(55/1296) : ℂ) • (v8) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h0]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 1 of the FF block. -/
lemma scalarProjFF1 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 : M}
    (h0 : T v0 = (2/3 : ℂ) • v0 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v7)
    (h1 : T v1 = (2/3 : ℂ) • v1 + (-(1/6) : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h2 : T v2 = (2/3 : ℂ) • v2 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v8)
    (h3 : T v3 = (2/3 : ℂ) • v3 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h4 : T v4 = (2/3 : ℂ) • v4 + (-(1/6) : ℂ) • v7 + (-(1/6) : ℂ) • v8)
    (h5 : T v5 = (2/3 : ℂ) • v5 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (-(1/6) : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v1 + (137/10 : ℂ) • T v1 + (-(135/2) : ℂ) • T (T v1)
      + (153 : ℂ) • T (T (T v1)) + (-162 : ℂ) • T (T (T (T v1)))
      + (324/5 : ℂ) • T (T (T (T (T v1)))) =
    (1/24 : ℂ) • ((8 : ℂ) • v1 + (-8 : ℂ) • v3 + (8 : ℂ) • v5) := by
  have i2 : T (T v1) =
      (1/2 : ℂ) • (v1)
      + (-(1/4) : ℂ) • (v3)
      + (1/4 : ℂ) • (v5) := by
    rw [h1]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i3 : T (T (T v1)) =
      (5/12 : ℂ) • (v1)
      + (-(7/24) : ℂ) • (v3)
      + (7/24 : ℂ) • (v5) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v1))) =
      (3/8 : ℂ) • (v1)
      + (-(5/16) : ℂ) • (v3)
      + (5/16 : ℂ) • (v5) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v1)))) =
      (17/48 : ℂ) • (v1)
      + (-(31/96) : ℂ) • (v3)
      + (31/96 : ℂ) • (v5) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h1]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 2 of the FF block. -/
lemma scalarProjFF2 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 : M}
    (h0 : T v0 = (2/3 : ℂ) • v0 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v7)
    (h1 : T v1 = (2/3 : ℂ) • v1 + (-(1/6) : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h2 : T v2 = (2/3 : ℂ) • v2 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v8)
    (h3 : T v3 = (2/3 : ℂ) • v3 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h4 : T v4 = (2/3 : ℂ) • v4 + (-(1/6) : ℂ) • v7 + (-(1/6) : ℂ) • v8)
    (h5 : T v5 = (2/3 : ℂ) • v5 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (-(1/6) : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v2 + (137/10 : ℂ) • T v2 + (-(135/2) : ℂ) • T (T v2)
      + (153 : ℂ) • T (T (T v2)) + (-162 : ℂ) • T (T (T (T v2)))
      + (324/5 : ℂ) • T (T (T (T (T v2)))) =
    (-(1/12) : ℂ) • ((-2 : ℂ) • v0 + (-2 : ℂ) • v2 + (-2 : ℂ) • v4 + (2 : ℂ) • v6 + (2 : ℂ) • v7 +
        (2 : ℂ) • v8) := by
  have i2 : T (T v2) =
      (1/36 : ℂ) • (v0)
      + (1/2 : ℂ) • (v2)
      + (1/36 : ℂ) • (v4)
      + (-(2/9) : ℂ) • (v6)
      + (-(2/9) : ℂ) • (v8) := by
    rw [h2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i3 : T (T (T v2)) =
      (1/18 : ℂ) • (v0)
      + (11/27 : ℂ) • (v2)
      + (1/18 : ℂ) • (v4)
      + (-(17/72) : ℂ) • (v6)
      + (-(1/108) : ℂ) • (v7)
      + (-(17/72) : ℂ) • (v8) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v2))) =
      (101/1296 : ℂ) • (v0)
      + (227/648 : ℂ) • (v2)
      + (101/1296 : ℂ) • (v4)
      + (-(19/81) : ℂ) • (v6)
      + (-(2/81) : ℂ) • (v7)
      + (-(19/81) : ℂ) • (v8) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v2)))) =
      (185/1944 : ℂ) • (v0)
      + (101/324 : ℂ) • (v2)
      + (185/1944 : ℂ) • (v4)
      + (-(1771/7776) : ℂ) • (v6)
      + (-(55/1296) : ℂ) • (v7)
      + (-(1771/7776) : ℂ) • (v8) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h2]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 3 of the FF block. -/
lemma scalarProjFF3 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 : M}
    (h0 : T v0 = (2/3 : ℂ) • v0 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v7)
    (h1 : T v1 = (2/3 : ℂ) • v1 + (-(1/6) : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h2 : T v2 = (2/3 : ℂ) • v2 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v8)
    (h3 : T v3 = (2/3 : ℂ) • v3 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h4 : T v4 = (2/3 : ℂ) • v4 + (-(1/6) : ℂ) • v7 + (-(1/6) : ℂ) • v8)
    (h5 : T v5 = (2/3 : ℂ) • v5 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (-(1/6) : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v3 + (137/10 : ℂ) • T v3 + (-(135/2) : ℂ) • T (T v3)
      + (153 : ℂ) • T (T (T v3)) + (-162 : ℂ) • T (T (T (T v3)))
      + (324/5 : ℂ) • T (T (T (T (T v3)))) =
    (-(1/24) : ℂ) • ((8 : ℂ) • v1 + (-8 : ℂ) • v3 + (8 : ℂ) • v5) := by
  have i2 : T (T v3) =
      (-(1/4) : ℂ) • (v1)
      + (1/2 : ℂ) • (v3)
      + (-(1/4) : ℂ) • (v5) := by
    rw [h3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i3 : T (T (T v3)) =
      (-(7/24) : ℂ) • (v1)
      + (5/12 : ℂ) • (v3)
      + (-(7/24) : ℂ) • (v5) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v3))) =
      (-(5/16) : ℂ) • (v1)
      + (3/8 : ℂ) • (v3)
      + (-(5/16) : ℂ) • (v5) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v3)))) =
      (-(31/96) : ℂ) • (v1)
      + (17/48 : ℂ) • (v3)
      + (-(31/96) : ℂ) • (v5) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h3]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 4 of the FF block. -/
lemma scalarProjFF4 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 : M}
    (h0 : T v0 = (2/3 : ℂ) • v0 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v7)
    (h1 : T v1 = (2/3 : ℂ) • v1 + (-(1/6) : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h2 : T v2 = (2/3 : ℂ) • v2 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v8)
    (h3 : T v3 = (2/3 : ℂ) • v3 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h4 : T v4 = (2/3 : ℂ) • v4 + (-(1/6) : ℂ) • v7 + (-(1/6) : ℂ) • v8)
    (h5 : T v5 = (2/3 : ℂ) • v5 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (-(1/6) : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v4 + (137/10 : ℂ) • T v4 + (-(135/2) : ℂ) • T (T v4)
      + (153 : ℂ) • T (T (T v4)) + (-162 : ℂ) • T (T (T (T v4)))
      + (324/5 : ℂ) • T (T (T (T (T v4)))) =
    (-(1/12) : ℂ) • ((-2 : ℂ) • v0 + (-2 : ℂ) • v2 + (-2 : ℂ) • v4 + (2 : ℂ) • v6 + (2 : ℂ) • v7 +
        (2 : ℂ) • v8) := by
  have i2 : T (T v4) =
      (1/36 : ℂ) • (v0)
      + (1/36 : ℂ) • (v2)
      + (1/2 : ℂ) • (v4)
      + (-(2/9) : ℂ) • (v7)
      + (-(2/9) : ℂ) • (v8) := by
    rw [h4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i3 : T (T (T v4)) =
      (1/18 : ℂ) • (v0)
      + (1/18 : ℂ) • (v2)
      + (11/27 : ℂ) • (v4)
      + (-(1/108) : ℂ) • (v6)
      + (-(17/72) : ℂ) • (v7)
      + (-(17/72) : ℂ) • (v8) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v4))) =
      (101/1296 : ℂ) • (v0)
      + (101/1296 : ℂ) • (v2)
      + (227/648 : ℂ) • (v4)
      + (-(2/81) : ℂ) • (v6)
      + (-(19/81) : ℂ) • (v7)
      + (-(19/81) : ℂ) • (v8) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v4)))) =
      (185/1944 : ℂ) • (v0)
      + (185/1944 : ℂ) • (v2)
      + (101/324 : ℂ) • (v4)
      + (-(55/1296) : ℂ) • (v6)
      + (-(1771/7776) : ℂ) • (v7)
      + (-(1771/7776) : ℂ) • (v8) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h4]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 5 of the FF block. -/
lemma scalarProjFF5 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 : M}
    (h0 : T v0 = (2/3 : ℂ) • v0 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v7)
    (h1 : T v1 = (2/3 : ℂ) • v1 + (-(1/6) : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h2 : T v2 = (2/3 : ℂ) • v2 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v8)
    (h3 : T v3 = (2/3 : ℂ) • v3 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h4 : T v4 = (2/3 : ℂ) • v4 + (-(1/6) : ℂ) • v7 + (-(1/6) : ℂ) • v8)
    (h5 : T v5 = (2/3 : ℂ) • v5 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (-(1/6) : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v5 + (137/10 : ℂ) • T v5 + (-(135/2) : ℂ) • T (T v5)
      + (153 : ℂ) • T (T (T v5)) + (-162 : ℂ) • T (T (T (T v5)))
      + (324/5 : ℂ) • T (T (T (T (T v5)))) =
    (1/24 : ℂ) • ((8 : ℂ) • v1 + (-8 : ℂ) • v3 + (8 : ℂ) • v5) := by
  have i2 : T (T v5) =
      (1/4 : ℂ) • (v1)
      + (-(1/4) : ℂ) • (v3)
      + (1/2 : ℂ) • (v5) := by
    rw [h5]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i3 : T (T (T v5)) =
      (7/24 : ℂ) • (v1)
      + (-(7/24) : ℂ) • (v3)
      + (5/12 : ℂ) • (v5) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v5))) =
      (5/16 : ℂ) • (v1)
      + (-(5/16) : ℂ) • (v3)
      + (3/8 : ℂ) • (v5) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v5)))) =
      (31/96 : ℂ) • (v1)
      + (-(31/96) : ℂ) • (v3)
      + (17/48 : ℂ) • (v5) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h5]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 6 of the FF block. -/
lemma scalarProjFF6 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 : M}
    (h0 : T v0 = (2/3 : ℂ) • v0 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v7)
    (h1 : T v1 = (2/3 : ℂ) • v1 + (-(1/6) : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h2 : T v2 = (2/3 : ℂ) • v2 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v8)
    (h3 : T v3 = (2/3 : ℂ) • v3 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h4 : T v4 = (2/3 : ℂ) • v4 + (-(1/6) : ℂ) • v7 + (-(1/6) : ℂ) • v8)
    (h5 : T v5 = (2/3 : ℂ) • v5 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (-(1/6) : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v6 + (137/10 : ℂ) • T v6 + (-(135/2) : ℂ) • T (T v6)
      + (153 : ℂ) • T (T (T v6)) + (-162 : ℂ) • T (T (T (T v6)))
      + (324/5 : ℂ) • T (T (T (T (T v6)))) =
    (1/12 : ℂ) • ((-2 : ℂ) • v0 + (-2 : ℂ) • v2 + (-2 : ℂ) • v4 + (2 : ℂ) • v6 + (2 : ℂ) • v7 + (2 :
        ℂ) • v8) := by
  have i2 : T (T v6) =
      (-(2/9) : ℂ) • (v0)
      + (-(2/9) : ℂ) • (v2)
      + (1/2 : ℂ) • (v6)
      + (1/36 : ℂ) • (v7)
      + (1/36 : ℂ) • (v8) := by
    rw [h6]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i3 : T (T (T v6)) =
      (-(17/72) : ℂ) • (v0)
      + (-(17/72) : ℂ) • (v2)
      + (-(1/108) : ℂ) • (v4)
      + (11/27 : ℂ) • (v6)
      + (1/18 : ℂ) • (v7)
      + (1/18 : ℂ) • (v8) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v6))) =
      (-(19/81) : ℂ) • (v0)
      + (-(19/81) : ℂ) • (v2)
      + (-(2/81) : ℂ) • (v4)
      + (227/648 : ℂ) • (v6)
      + (101/1296 : ℂ) • (v7)
      + (101/1296 : ℂ) • (v8) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v6)))) =
      (-(1771/7776) : ℂ) • (v0)
      + (-(1771/7776) : ℂ) • (v2)
      + (-(55/1296) : ℂ) • (v4)
      + (101/324 : ℂ) • (v6)
      + (185/1944 : ℂ) • (v7)
      + (185/1944 : ℂ) • (v8) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h6]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 7 of the FF block. -/
lemma scalarProjFF7 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 : M}
    (h0 : T v0 = (2/3 : ℂ) • v0 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v7)
    (h1 : T v1 = (2/3 : ℂ) • v1 + (-(1/6) : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h2 : T v2 = (2/3 : ℂ) • v2 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v8)
    (h3 : T v3 = (2/3 : ℂ) • v3 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h4 : T v4 = (2/3 : ℂ) • v4 + (-(1/6) : ℂ) • v7 + (-(1/6) : ℂ) • v8)
    (h5 : T v5 = (2/3 : ℂ) • v5 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (-(1/6) : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v7 + (137/10 : ℂ) • T v7 + (-(135/2) : ℂ) • T (T v7)
      + (153 : ℂ) • T (T (T v7)) + (-162 : ℂ) • T (T (T (T v7)))
      + (324/5 : ℂ) • T (T (T (T (T v7)))) =
    (1/12 : ℂ) • ((-2 : ℂ) • v0 + (-2 : ℂ) • v2 + (-2 : ℂ) • v4 + (2 : ℂ) • v6 + (2 : ℂ) • v7 + (2 :
        ℂ) • v8) := by
  have i2 : T (T v7) =
      (-(2/9) : ℂ) • (v0)
      + (-(2/9) : ℂ) • (v4)
      + (1/36 : ℂ) • (v6)
      + (1/2 : ℂ) • (v7)
      + (1/36 : ℂ) • (v8) := by
    rw [h7]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i3 : T (T (T v7)) =
      (-(17/72) : ℂ) • (v0)
      + (-(1/108) : ℂ) • (v2)
      + (-(17/72) : ℂ) • (v4)
      + (1/18 : ℂ) • (v6)
      + (11/27 : ℂ) • (v7)
      + (1/18 : ℂ) • (v8) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v7))) =
      (-(19/81) : ℂ) • (v0)
      + (-(2/81) : ℂ) • (v2)
      + (-(19/81) : ℂ) • (v4)
      + (101/1296 : ℂ) • (v6)
      + (227/648 : ℂ) • (v7)
      + (101/1296 : ℂ) • (v8) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v7)))) =
      (-(1771/7776) : ℂ) • (v0)
      + (-(55/1296) : ℂ) • (v2)
      + (-(1771/7776) : ℂ) • (v4)
      + (185/1944 : ℂ) • (v6)
      + (101/324 : ℂ) • (v7)
      + (185/1944 : ℂ) • (v8) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h7]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 8 of the FF block. -/
lemma scalarProjFF8 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 : M}
    (h0 : T v0 = (2/3 : ℂ) • v0 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v7)
    (h1 : T v1 = (2/3 : ℂ) • v1 + (-(1/6) : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h2 : T v2 = (2/3 : ℂ) • v2 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v8)
    (h3 : T v3 = (2/3 : ℂ) • v3 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h4 : T v4 = (2/3 : ℂ) • v4 + (-(1/6) : ℂ) • v7 + (-(1/6) : ℂ) • v8)
    (h5 : T v5 = (2/3 : ℂ) • v5 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (-(1/6) : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v8 + (137/10 : ℂ) • T v8 + (-(135/2) : ℂ) • T (T v8)
      + (153 : ℂ) • T (T (T v8)) + (-162 : ℂ) • T (T (T (T v8)))
      + (324/5 : ℂ) • T (T (T (T (T v8)))) =
    (1/12 : ℂ) • ((-2 : ℂ) • v0 + (-2 : ℂ) • v2 + (-2 : ℂ) • v4 + (2 : ℂ) • v6 + (2 : ℂ) • v7 + (2 :
        ℂ) • v8) := by
  have i2 : T (T v8) =
      (-(2/9) : ℂ) • (v2)
      + (-(2/9) : ℂ) • (v4)
      + (1/36 : ℂ) • (v6)
      + (1/36 : ℂ) • (v7)
      + (1/2 : ℂ) • (v8) := by
    rw [h8]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i3 : T (T (T v8)) =
      (-(1/108) : ℂ) • (v0)
      + (-(17/72) : ℂ) • (v2)
      + (-(17/72) : ℂ) • (v4)
      + (1/18 : ℂ) • (v6)
      + (1/18 : ℂ) • (v7)
      + (11/27 : ℂ) • (v8) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v8))) =
      (-(2/81) : ℂ) • (v0)
      + (-(19/81) : ℂ) • (v2)
      + (-(19/81) : ℂ) • (v4)
      + (101/1296 : ℂ) • (v6)
      + (101/1296 : ℂ) • (v7)
      + (227/648 : ℂ) • (v8) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v8)))) =
      (-(55/1296) : ℂ) • (v0)
      + (-(1771/7776) : ℂ) • (v2)
      + (-(1771/7776) : ℂ) • (v4)
      + (185/1944 : ℂ) • (v6)
      + (185/1944 : ℂ) • (v7)
      + (101/324 : ℂ) • (v8) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h8]
  match_scalars <;> norm_num
end JetAlgebra

end LeptonGaugeSector
