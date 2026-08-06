/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.QED.JetAlgebra.Invariants.Projectors
/-!
# The projector polynomial on the derivative and fermion patterns

Evaluation of the projector polynomial `opPi` on the eigenvalue patterns of
the second-derivative field strengths (`projDDF*`) and of the fermion
bilinears (`projFMu*`, `projFMubar*`).
-/

@[expose] public section

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace QED
open TensorProduct StandardModel

namespace JetAlgebra

open scoped minkowskiMatrix PauliMatrix
open Matrix MatrixGroups
set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 0 of the DDF block. -/
lemma projDDF0 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : M}
    (h0 : T v0 = (1/3 : ℂ) • v0 + (1/6 : ℂ) • v7 + (1/6 : ℂ) • v9)
    (h1 : T v1 = (1/3 : ℂ) • v1 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v8)
    (h2 : T v2 = (1/3 : ℂ) • v2 + (-(1/6) : ℂ) • v7 + (1/6 : ℂ) • v11)
    (h3 : T v3 = (1/3 : ℂ) • v3 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v10)
    (h4 : T v4 = (1/3 : ℂ) • v4 + (-(1/6) : ℂ) • v9 + (-(1/6) : ℂ) • v11)
    (h5 : T v5 = (1/3 : ℂ) • v5 + (-(1/6) : ℂ) • v8 + (1/6 : ℂ) • v10)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h9 : T v9 = (2/3 : ℂ) • v9 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h10 : T v10 = (2/3 : ℂ) • v10 + (1/6 : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h11 : T v11 = (2/3 : ℂ) • v11 + (1/6 : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v0 + (137/10 : ℂ) • T v0 + (-(135/2) : ℂ) • T (T v0)
      + (153 : ℂ) • T (T (T v0)) + (-162 : ℂ) • T (T (T (T v0)))
      + (324/5 : ℂ) • T (T (T (T (T v0)))) =
    (0 : M) := by
  have i2 : T (T v0) =
      (1/6 : ℂ) • (v0)
      + (-(1/36) : ℂ) • (v2)
      + (-(1/36) : ℂ) • (v4)
      + (1/6 : ℂ) • (v7)
      + (1/6 : ℂ) • (v9) := by
    rw [h0]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i3 : T (T (T v0)) =
      (1/9 : ℂ) • (v0)
      + (-(1/27) : ℂ) • (v2)
      + (-(1/27) : ℂ) • (v4)
      + (31/216 : ℂ) • (v7)
      + (31/216 : ℂ) • (v9) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v0))) =
      (55/648 : ℂ) • (v0)
      + (-(47/1296) : ℂ) • (v2)
      + (-(47/1296) : ℂ) • (v4)
      + (13/108 : ℂ) • (v7)
      + (13/108 : ℂ) • (v9) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v0)))) =
      (133/1944 : ℂ) • (v0)
      + (-(125/3888) : ℂ) • (v2)
      + (-(125/3888) : ℂ) • (v4)
      + (781/7776 : ℂ) • (v7)
      + (781/7776 : ℂ) • (v9) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h0]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 1 of the DDF block. -/
lemma projDDF1 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : M}
    (h0 : T v0 = (1/3 : ℂ) • v0 + (1/6 : ℂ) • v7 + (1/6 : ℂ) • v9)
    (h1 : T v1 = (1/3 : ℂ) • v1 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v8)
    (h2 : T v2 = (1/3 : ℂ) • v2 + (-(1/6) : ℂ) • v7 + (1/6 : ℂ) • v11)
    (h3 : T v3 = (1/3 : ℂ) • v3 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v10)
    (h4 : T v4 = (1/3 : ℂ) • v4 + (-(1/6) : ℂ) • v9 + (-(1/6) : ℂ) • v11)
    (h5 : T v5 = (1/3 : ℂ) • v5 + (-(1/6) : ℂ) • v8 + (1/6 : ℂ) • v10)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h9 : T v9 = (2/3 : ℂ) • v9 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h10 : T v10 = (2/3 : ℂ) • v10 + (1/6 : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h11 : T v11 = (2/3 : ℂ) • v11 + (1/6 : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v1 + (137/10 : ℂ) • T v1 + (-(135/2) : ℂ) • T (T v1)
      + (153 : ℂ) • T (T (T v1)) + (-162 : ℂ) • T (T (T (T v1)))
      + (324/5 : ℂ) • T (T (T (T (T v1)))) =
    (0 : M) := by
  have i2 : T (T v1) =
      (1/6 : ℂ) • (v1)
      + (1/36 : ℂ) • (v3)
      + (-(1/36) : ℂ) • (v5)
      + (-(1/6) : ℂ) • (v6)
      + (1/6 : ℂ) • (v8) := by
    rw [h1]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i3 : T (T (T v1)) =
      (1/9 : ℂ) • (v1)
      + (1/27 : ℂ) • (v3)
      + (-(1/27) : ℂ) • (v5)
      + (-(31/216) : ℂ) • (v6)
      + (31/216 : ℂ) • (v8) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v1))) =
      (55/648 : ℂ) • (v1)
      + (47/1296 : ℂ) • (v3)
      + (-(47/1296) : ℂ) • (v5)
      + (-(13/108) : ℂ) • (v6)
      + (13/108 : ℂ) • (v8) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v1)))) =
      (133/1944 : ℂ) • (v1)
      + (125/3888 : ℂ) • (v3)
      + (-(125/3888) : ℂ) • (v5)
      + (-(781/7776) : ℂ) • (v6)
      + (781/7776 : ℂ) • (v8) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h1]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 2 of the DDF block. -/
lemma projDDF2 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : M}
    (h0 : T v0 = (1/3 : ℂ) • v0 + (1/6 : ℂ) • v7 + (1/6 : ℂ) • v9)
    (h1 : T v1 = (1/3 : ℂ) • v1 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v8)
    (h2 : T v2 = (1/3 : ℂ) • v2 + (-(1/6) : ℂ) • v7 + (1/6 : ℂ) • v11)
    (h3 : T v3 = (1/3 : ℂ) • v3 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v10)
    (h4 : T v4 = (1/3 : ℂ) • v4 + (-(1/6) : ℂ) • v9 + (-(1/6) : ℂ) • v11)
    (h5 : T v5 = (1/3 : ℂ) • v5 + (-(1/6) : ℂ) • v8 + (1/6 : ℂ) • v10)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h9 : T v9 = (2/3 : ℂ) • v9 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h10 : T v10 = (2/3 : ℂ) • v10 + (1/6 : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h11 : T v11 = (2/3 : ℂ) • v11 + (1/6 : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v2 + (137/10 : ℂ) • T v2 + (-(135/2) : ℂ) • T (T v2)
      + (153 : ℂ) • T (T (T v2)) + (-162 : ℂ) • T (T (T (T v2)))
      + (324/5 : ℂ) • T (T (T (T (T v2)))) =
    (0 : M) := by
  have i2 : T (T v2) =
      (-(1/36) : ℂ) • (v0)
      + (1/6 : ℂ) • (v2)
      + (-(1/36) : ℂ) • (v4)
      + (-(1/6) : ℂ) • (v7)
      + (1/6 : ℂ) • (v11) := by
    rw [h2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i3 : T (T (T v2)) =
      (-(1/27) : ℂ) • (v0)
      + (1/9 : ℂ) • (v2)
      + (-(1/27) : ℂ) • (v4)
      + (-(31/216) : ℂ) • (v7)
      + (31/216 : ℂ) • (v11) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v2))) =
      (-(47/1296) : ℂ) • (v0)
      + (55/648 : ℂ) • (v2)
      + (-(47/1296) : ℂ) • (v4)
      + (-(13/108) : ℂ) • (v7)
      + (13/108 : ℂ) • (v11) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v2)))) =
      (-(125/3888) : ℂ) • (v0)
      + (133/1944 : ℂ) • (v2)
      + (-(125/3888) : ℂ) • (v4)
      + (-(781/7776) : ℂ) • (v7)
      + (781/7776 : ℂ) • (v11) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h2]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 3 of the DDF block. -/
lemma projDDF3 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : M}
    (h0 : T v0 = (1/3 : ℂ) • v0 + (1/6 : ℂ) • v7 + (1/6 : ℂ) • v9)
    (h1 : T v1 = (1/3 : ℂ) • v1 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v8)
    (h2 : T v2 = (1/3 : ℂ) • v2 + (-(1/6) : ℂ) • v7 + (1/6 : ℂ) • v11)
    (h3 : T v3 = (1/3 : ℂ) • v3 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v10)
    (h4 : T v4 = (1/3 : ℂ) • v4 + (-(1/6) : ℂ) • v9 + (-(1/6) : ℂ) • v11)
    (h5 : T v5 = (1/3 : ℂ) • v5 + (-(1/6) : ℂ) • v8 + (1/6 : ℂ) • v10)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h9 : T v9 = (2/3 : ℂ) • v9 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h10 : T v10 = (2/3 : ℂ) • v10 + (1/6 : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h11 : T v11 = (2/3 : ℂ) • v11 + (1/6 : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v3 + (137/10 : ℂ) • T v3 + (-(135/2) : ℂ) • T (T v3)
      + (153 : ℂ) • T (T (T v3)) + (-162 : ℂ) • T (T (T (T v3)))
      + (324/5 : ℂ) • T (T (T (T (T v3)))) =
    (0 : M) := by
  have i2 : T (T v3) =
      (1/36 : ℂ) • (v1)
      + (1/6 : ℂ) • (v3)
      + (1/36 : ℂ) • (v5)
      + (-(1/6) : ℂ) • (v6)
      + (1/6 : ℂ) • (v10) := by
    rw [h3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i3 : T (T (T v3)) =
      (1/27 : ℂ) • (v1)
      + (1/9 : ℂ) • (v3)
      + (1/27 : ℂ) • (v5)
      + (-(31/216) : ℂ) • (v6)
      + (31/216 : ℂ) • (v10) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v3))) =
      (47/1296 : ℂ) • (v1)
      + (55/648 : ℂ) • (v3)
      + (47/1296 : ℂ) • (v5)
      + (-(13/108) : ℂ) • (v6)
      + (13/108 : ℂ) • (v10) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v3)))) =
      (125/3888 : ℂ) • (v1)
      + (133/1944 : ℂ) • (v3)
      + (125/3888 : ℂ) • (v5)
      + (-(781/7776) : ℂ) • (v6)
      + (781/7776 : ℂ) • (v10) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h3]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 4 of the DDF block. -/
lemma projDDF4 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : M}
    (h0 : T v0 = (1/3 : ℂ) • v0 + (1/6 : ℂ) • v7 + (1/6 : ℂ) • v9)
    (h1 : T v1 = (1/3 : ℂ) • v1 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v8)
    (h2 : T v2 = (1/3 : ℂ) • v2 + (-(1/6) : ℂ) • v7 + (1/6 : ℂ) • v11)
    (h3 : T v3 = (1/3 : ℂ) • v3 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v10)
    (h4 : T v4 = (1/3 : ℂ) • v4 + (-(1/6) : ℂ) • v9 + (-(1/6) : ℂ) • v11)
    (h5 : T v5 = (1/3 : ℂ) • v5 + (-(1/6) : ℂ) • v8 + (1/6 : ℂ) • v10)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h9 : T v9 = (2/3 : ℂ) • v9 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h10 : T v10 = (2/3 : ℂ) • v10 + (1/6 : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h11 : T v11 = (2/3 : ℂ) • v11 + (1/6 : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v4 + (137/10 : ℂ) • T v4 + (-(135/2) : ℂ) • T (T v4)
      + (153 : ℂ) • T (T (T v4)) + (-162 : ℂ) • T (T (T (T v4)))
      + (324/5 : ℂ) • T (T (T (T (T v4)))) =
    (0 : M) := by
  have i2 : T (T v4) =
      (-(1/36) : ℂ) • (v0)
      + (-(1/36) : ℂ) • (v2)
      + (1/6 : ℂ) • (v4)
      + (-(1/6) : ℂ) • (v9)
      + (-(1/6) : ℂ) • (v11) := by
    rw [h4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i3 : T (T (T v4)) =
      (-(1/27) : ℂ) • (v0)
      + (-(1/27) : ℂ) • (v2)
      + (1/9 : ℂ) • (v4)
      + (-(31/216) : ℂ) • (v9)
      + (-(31/216) : ℂ) • (v11) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v4))) =
      (-(47/1296) : ℂ) • (v0)
      + (-(47/1296) : ℂ) • (v2)
      + (55/648 : ℂ) • (v4)
      + (-(13/108) : ℂ) • (v9)
      + (-(13/108) : ℂ) • (v11) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v4)))) =
      (-(125/3888) : ℂ) • (v0)
      + (-(125/3888) : ℂ) • (v2)
      + (133/1944 : ℂ) • (v4)
      + (-(781/7776) : ℂ) • (v9)
      + (-(781/7776) : ℂ) • (v11) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h4]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 5 of the DDF block. -/
lemma projDDF5 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : M}
    (h0 : T v0 = (1/3 : ℂ) • v0 + (1/6 : ℂ) • v7 + (1/6 : ℂ) • v9)
    (h1 : T v1 = (1/3 : ℂ) • v1 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v8)
    (h2 : T v2 = (1/3 : ℂ) • v2 + (-(1/6) : ℂ) • v7 + (1/6 : ℂ) • v11)
    (h3 : T v3 = (1/3 : ℂ) • v3 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v10)
    (h4 : T v4 = (1/3 : ℂ) • v4 + (-(1/6) : ℂ) • v9 + (-(1/6) : ℂ) • v11)
    (h5 : T v5 = (1/3 : ℂ) • v5 + (-(1/6) : ℂ) • v8 + (1/6 : ℂ) • v10)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h9 : T v9 = (2/3 : ℂ) • v9 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h10 : T v10 = (2/3 : ℂ) • v10 + (1/6 : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h11 : T v11 = (2/3 : ℂ) • v11 + (1/6 : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v5 + (137/10 : ℂ) • T v5 + (-(135/2) : ℂ) • T (T v5)
      + (153 : ℂ) • T (T (T v5)) + (-162 : ℂ) • T (T (T (T v5)))
      + (324/5 : ℂ) • T (T (T (T (T v5)))) =
    (0 : M) := by
  have i2 : T (T v5) =
      (-(1/36) : ℂ) • (v1)
      + (1/36 : ℂ) • (v3)
      + (1/6 : ℂ) • (v5)
      + (-(1/6) : ℂ) • (v8)
      + (1/6 : ℂ) • (v10) := by
    rw [h5]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i3 : T (T (T v5)) =
      (-(1/27) : ℂ) • (v1)
      + (1/27 : ℂ) • (v3)
      + (1/9 : ℂ) • (v5)
      + (-(31/216) : ℂ) • (v8)
      + (31/216 : ℂ) • (v10) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v5))) =
      (-(47/1296) : ℂ) • (v1)
      + (47/1296 : ℂ) • (v3)
      + (55/648 : ℂ) • (v5)
      + (-(13/108) : ℂ) • (v8)
      + (13/108 : ℂ) • (v10) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v5)))) =
      (-(125/3888) : ℂ) • (v1)
      + (125/3888 : ℂ) • (v3)
      + (133/1944 : ℂ) • (v5)
      + (-(781/7776) : ℂ) • (v8)
      + (781/7776 : ℂ) • (v10) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h5]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 6 of the DDF block. -/
lemma projDDF6 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : M}
    (h0 : T v0 = (1/3 : ℂ) • v0 + (1/6 : ℂ) • v7 + (1/6 : ℂ) • v9)
    (h1 : T v1 = (1/3 : ℂ) • v1 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v8)
    (h2 : T v2 = (1/3 : ℂ) • v2 + (-(1/6) : ℂ) • v7 + (1/6 : ℂ) • v11)
    (h3 : T v3 = (1/3 : ℂ) • v3 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v10)
    (h4 : T v4 = (1/3 : ℂ) • v4 + (-(1/6) : ℂ) • v9 + (-(1/6) : ℂ) • v11)
    (h5 : T v5 = (1/3 : ℂ) • v5 + (-(1/6) : ℂ) • v8 + (1/6 : ℂ) • v10)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h9 : T v9 = (2/3 : ℂ) • v9 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h10 : T v10 = (2/3 : ℂ) • v10 + (1/6 : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h11 : T v11 = (2/3 : ℂ) • v11 + (1/6 : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v6 + (137/10 : ℂ) • T v6 + (-(135/2) : ℂ) • T (T v6)
      + (153 : ℂ) • T (T (T v6)) + (-162 : ℂ) • T (T (T (T v6)))
      + (324/5 : ℂ) • T (T (T (T (T v6)))) =
    (0 : M) := by
  have i2 : T (T v6) =
      (-(1/6) : ℂ) • (v1)
      + (-(1/6) : ℂ) • (v3)
      + (1/2 : ℂ) • (v6)
      + (-(1/36) : ℂ) • (v8)
      + (-(1/36) : ℂ) • (v10) := by
    rw [h6]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i3 : T (T (T v6)) =
      (-(31/216) : ℂ) • (v1)
      + (-(31/216) : ℂ) • (v3)
      + (7/18 : ℂ) • (v6)
      + (-(5/108) : ℂ) • (v8)
      + (-(5/108) : ℂ) • (v10) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v6))) =
      (-(13/108) : ℂ) • (v1)
      + (-(13/108) : ℂ) • (v3)
      + (199/648 : ℂ) • (v6)
      + (-(71/1296) : ℂ) • (v8)
      + (-(71/1296) : ℂ) • (v10) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v6)))) =
      (-(781/7776) : ℂ) • (v1)
      + (-(781/7776) : ℂ) • (v3)
      + (119/486 : ℂ) • (v6)
      + (-(55/972) : ℂ) • (v8)
      + (-(55/972) : ℂ) • (v10) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h6]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 7 of the DDF block. -/
lemma projDDF7 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : M}
    (h0 : T v0 = (1/3 : ℂ) • v0 + (1/6 : ℂ) • v7 + (1/6 : ℂ) • v9)
    (h1 : T v1 = (1/3 : ℂ) • v1 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v8)
    (h2 : T v2 = (1/3 : ℂ) • v2 + (-(1/6) : ℂ) • v7 + (1/6 : ℂ) • v11)
    (h3 : T v3 = (1/3 : ℂ) • v3 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v10)
    (h4 : T v4 = (1/3 : ℂ) • v4 + (-(1/6) : ℂ) • v9 + (-(1/6) : ℂ) • v11)
    (h5 : T v5 = (1/3 : ℂ) • v5 + (-(1/6) : ℂ) • v8 + (1/6 : ℂ) • v10)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h9 : T v9 = (2/3 : ℂ) • v9 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h10 : T v10 = (2/3 : ℂ) • v10 + (1/6 : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h11 : T v11 = (2/3 : ℂ) • v11 + (1/6 : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v7 + (137/10 : ℂ) • T v7 + (-(135/2) : ℂ) • T (T v7)
      + (153 : ℂ) • T (T (T v7)) + (-162 : ℂ) • T (T (T (T v7)))
      + (324/5 : ℂ) • T (T (T (T (T v7)))) =
    (0 : M) := by
  have i2 : T (T v7) =
      (1/6 : ℂ) • (v0)
      + (-(1/6) : ℂ) • (v2)
      + (1/2 : ℂ) • (v7)
      + (1/36 : ℂ) • (v9)
      + (-(1/36) : ℂ) • (v11) := by
    rw [h7]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i3 : T (T (T v7)) =
      (31/216 : ℂ) • (v0)
      + (-(31/216) : ℂ) • (v2)
      + (7/18 : ℂ) • (v7)
      + (5/108 : ℂ) • (v9)
      + (-(5/108) : ℂ) • (v11) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v7))) =
      (13/108 : ℂ) • (v0)
      + (-(13/108) : ℂ) • (v2)
      + (199/648 : ℂ) • (v7)
      + (71/1296 : ℂ) • (v9)
      + (-(71/1296) : ℂ) • (v11) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v7)))) =
      (781/7776 : ℂ) • (v0)
      + (-(781/7776) : ℂ) • (v2)
      + (119/486 : ℂ) • (v7)
      + (55/972 : ℂ) • (v9)
      + (-(55/972) : ℂ) • (v11) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h7]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 8 of the DDF block. -/
lemma projDDF8 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : M}
    (h0 : T v0 = (1/3 : ℂ) • v0 + (1/6 : ℂ) • v7 + (1/6 : ℂ) • v9)
    (h1 : T v1 = (1/3 : ℂ) • v1 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v8)
    (h2 : T v2 = (1/3 : ℂ) • v2 + (-(1/6) : ℂ) • v7 + (1/6 : ℂ) • v11)
    (h3 : T v3 = (1/3 : ℂ) • v3 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v10)
    (h4 : T v4 = (1/3 : ℂ) • v4 + (-(1/6) : ℂ) • v9 + (-(1/6) : ℂ) • v11)
    (h5 : T v5 = (1/3 : ℂ) • v5 + (-(1/6) : ℂ) • v8 + (1/6 : ℂ) • v10)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h9 : T v9 = (2/3 : ℂ) • v9 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h10 : T v10 = (2/3 : ℂ) • v10 + (1/6 : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h11 : T v11 = (2/3 : ℂ) • v11 + (1/6 : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v8 + (137/10 : ℂ) • T v8 + (-(135/2) : ℂ) • T (T v8)
      + (153 : ℂ) • T (T (T v8)) + (-162 : ℂ) • T (T (T (T v8)))
      + (324/5 : ℂ) • T (T (T (T (T v8)))) =
    (0 : M) := by
  have i2 : T (T v8) =
      (1/6 : ℂ) • (v1)
      + (-(1/6) : ℂ) • (v5)
      + (-(1/36) : ℂ) • (v6)
      + (1/2 : ℂ) • (v8)
      + (-(1/36) : ℂ) • (v10) := by
    rw [h8]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i3 : T (T (T v8)) =
      (31/216 : ℂ) • (v1)
      + (-(31/216) : ℂ) • (v5)
      + (-(5/108) : ℂ) • (v6)
      + (7/18 : ℂ) • (v8)
      + (-(5/108) : ℂ) • (v10) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v8))) =
      (13/108 : ℂ) • (v1)
      + (-(13/108) : ℂ) • (v5)
      + (-(71/1296) : ℂ) • (v6)
      + (199/648 : ℂ) • (v8)
      + (-(71/1296) : ℂ) • (v10) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v8)))) =
      (781/7776 : ℂ) • (v1)
      + (-(781/7776) : ℂ) • (v5)
      + (-(55/972) : ℂ) • (v6)
      + (119/486 : ℂ) • (v8)
      + (-(55/972) : ℂ) • (v10) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h8]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 9 of the DDF block. -/
lemma projDDF9 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : M}
    (h0 : T v0 = (1/3 : ℂ) • v0 + (1/6 : ℂ) • v7 + (1/6 : ℂ) • v9)
    (h1 : T v1 = (1/3 : ℂ) • v1 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v8)
    (h2 : T v2 = (1/3 : ℂ) • v2 + (-(1/6) : ℂ) • v7 + (1/6 : ℂ) • v11)
    (h3 : T v3 = (1/3 : ℂ) • v3 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v10)
    (h4 : T v4 = (1/3 : ℂ) • v4 + (-(1/6) : ℂ) • v9 + (-(1/6) : ℂ) • v11)
    (h5 : T v5 = (1/3 : ℂ) • v5 + (-(1/6) : ℂ) • v8 + (1/6 : ℂ) • v10)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h9 : T v9 = (2/3 : ℂ) • v9 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h10 : T v10 = (2/3 : ℂ) • v10 + (1/6 : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h11 : T v11 = (2/3 : ℂ) • v11 + (1/6 : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v9 + (137/10 : ℂ) • T v9 + (-(135/2) : ℂ) • T (T v9)
      + (153 : ℂ) • T (T (T v9)) + (-162 : ℂ) • T (T (T (T v9)))
      + (324/5 : ℂ) • T (T (T (T (T v9)))) =
    (0 : M) := by
  have i2 : T (T v9) =
      (1/6 : ℂ) • (v0)
      + (-(1/6) : ℂ) • (v4)
      + (1/36 : ℂ) • (v7)
      + (1/2 : ℂ) • (v9)
      + (1/36 : ℂ) • (v11) := by
    rw [h9]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i3 : T (T (T v9)) =
      (31/216 : ℂ) • (v0)
      + (-(31/216) : ℂ) • (v4)
      + (5/108 : ℂ) • (v7)
      + (7/18 : ℂ) • (v9)
      + (5/108 : ℂ) • (v11) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v9))) =
      (13/108 : ℂ) • (v0)
      + (-(13/108) : ℂ) • (v4)
      + (71/1296 : ℂ) • (v7)
      + (199/648 : ℂ) • (v9)
      + (71/1296 : ℂ) • (v11) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v9)))) =
      (781/7776 : ℂ) • (v0)
      + (-(781/7776) : ℂ) • (v4)
      + (55/972 : ℂ) • (v7)
      + (119/486 : ℂ) • (v9)
      + (55/972 : ℂ) • (v11) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h9]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 10 of the DDF block. -/
lemma projDDF10 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : M}
    (h0 : T v0 = (1/3 : ℂ) • v0 + (1/6 : ℂ) • v7 + (1/6 : ℂ) • v9)
    (h1 : T v1 = (1/3 : ℂ) • v1 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v8)
    (h2 : T v2 = (1/3 : ℂ) • v2 + (-(1/6) : ℂ) • v7 + (1/6 : ℂ) • v11)
    (h3 : T v3 = (1/3 : ℂ) • v3 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v10)
    (h4 : T v4 = (1/3 : ℂ) • v4 + (-(1/6) : ℂ) • v9 + (-(1/6) : ℂ) • v11)
    (h5 : T v5 = (1/3 : ℂ) • v5 + (-(1/6) : ℂ) • v8 + (1/6 : ℂ) • v10)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h9 : T v9 = (2/3 : ℂ) • v9 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h10 : T v10 = (2/3 : ℂ) • v10 + (1/6 : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h11 : T v11 = (2/3 : ℂ) • v11 + (1/6 : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v10 + (137/10 : ℂ) • T v10 + (-(135/2) : ℂ) • T (T v10)
      + (153 : ℂ) • T (T (T v10)) + (-162 : ℂ) • T (T (T (T v10)))
      + (324/5 : ℂ) • T (T (T (T (T v10)))) =
    (0 : M) := by
  have i2 : T (T v10) =
      (1/6 : ℂ) • (v3)
      + (1/6 : ℂ) • (v5)
      + (-(1/36) : ℂ) • (v6)
      + (-(1/36) : ℂ) • (v8)
      + (1/2 : ℂ) • (v10) := by
    rw [h10]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i3 : T (T (T v10)) =
      (31/216 : ℂ) • (v3)
      + (31/216 : ℂ) • (v5)
      + (-(5/108) : ℂ) • (v6)
      + (-(5/108) : ℂ) • (v8)
      + (7/18 : ℂ) • (v10) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v10))) =
      (13/108 : ℂ) • (v3)
      + (13/108 : ℂ) • (v5)
      + (-(71/1296) : ℂ) • (v6)
      + (-(71/1296) : ℂ) • (v8)
      + (199/648 : ℂ) • (v10) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v10)))) =
      (781/7776 : ℂ) • (v3)
      + (781/7776 : ℂ) • (v5)
      + (-(55/972) : ℂ) • (v6)
      + (-(55/972) : ℂ) • (v8)
      + (119/486 : ℂ) • (v10) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h10]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 11 of the DDF block. -/
lemma projDDF11 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : M}
    (h0 : T v0 = (1/3 : ℂ) • v0 + (1/6 : ℂ) • v7 + (1/6 : ℂ) • v9)
    (h1 : T v1 = (1/3 : ℂ) • v1 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v8)
    (h2 : T v2 = (1/3 : ℂ) • v2 + (-(1/6) : ℂ) • v7 + (1/6 : ℂ) • v11)
    (h3 : T v3 = (1/3 : ℂ) • v3 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v10)
    (h4 : T v4 = (1/3 : ℂ) • v4 + (-(1/6) : ℂ) • v9 + (-(1/6) : ℂ) • v11)
    (h5 : T v5 = (1/3 : ℂ) • v5 + (-(1/6) : ℂ) • v8 + (1/6 : ℂ) • v10)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h9 : T v9 = (2/3 : ℂ) • v9 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h10 : T v10 = (2/3 : ℂ) • v10 + (1/6 : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h11 : T v11 = (2/3 : ℂ) • v11 + (1/6 : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v11 + (137/10 : ℂ) • T v11 + (-(135/2) : ℂ) • T (T v11)
      + (153 : ℂ) • T (T (T v11)) + (-162 : ℂ) • T (T (T (T v11)))
      + (324/5 : ℂ) • T (T (T (T (T v11)))) =
    (0 : M) := by
  have i2 : T (T v11) =
      (1/6 : ℂ) • (v2)
      + (-(1/6) : ℂ) • (v4)
      + (-(1/36) : ℂ) • (v7)
      + (1/36 : ℂ) • (v9)
      + (1/2 : ℂ) • (v11) := by
    rw [h11]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i3 : T (T (T v11)) =
      (31/216 : ℂ) • (v2)
      + (-(31/216) : ℂ) • (v4)
      + (-(5/108) : ℂ) • (v7)
      + (5/108 : ℂ) • (v9)
      + (7/18 : ℂ) • (v11) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v11))) =
      (13/108 : ℂ) • (v2)
      + (-(13/108) : ℂ) • (v4)
      + (-(71/1296) : ℂ) • (v7)
      + (71/1296 : ℂ) • (v9)
      + (199/648 : ℂ) • (v11) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v11)))) =
      (781/7776 : ℂ) • (v2)
      + (-(781/7776) : ℂ) • (v4)
      + (-(55/972) : ℂ) • (v7)
      + (55/972 : ℂ) • (v9)
      + (119/486 : ℂ) • (v11) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h11]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 0 of the FMu block. -/
lemma projFMu0 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 : M}
    (h0 : T v0 = (1/2 : ℂ) • v0 + (-(1/6) : ℂ) • v1 + (-(Complex.I/6)) • v2 + (-(1/6) : ℂ) • v3)
    (h1 : T v1 = (5/6 : ℂ) • v1 + (-(1/6) : ℂ) • v0)
    (h2 : T v2 = (5/6 : ℂ) • v2 + (Complex.I/6) • v0)
    (h3 : T v3 = (5/6 : ℂ) • v3 + (-(1/6) : ℂ) • v0) :
    (-1 : ℂ) • v0 + (137/10 : ℂ) • T v0 + (-(135/2) : ℂ) • T (T v0)
      + (153 : ℂ) • T (T (T v0)) + (-162 : ℂ) • T (T (T (T v0)))
      + (324/5 : ℂ) • T (T (T (T (T v0)))) =
    (-(Complex.I/4)) • (Complex.I • (v0 - v1 - Complex.I • v2 - v3)) := by
  have i2 : T (T v0) =
      (1/3 : ℂ) • (v0)
      + (-(2/9) : ℂ) • (v1)
      + ((-(2/9) : ℂ) * Complex.I) • (v2)
      + (-(2/9) : ℂ) • (v3) := by
    rw [h0]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i3 : T (T (T v0)) =
      (5/18 : ℂ) • (v0)
      + (-(13/54) : ℂ) • (v1)
      + ((-(13/54) : ℂ) * Complex.I) • (v2)
      + (-(13/54) : ℂ) • (v3) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i4 : T (T (T (T v0))) =
      (7/27 : ℂ) • (v0)
      + (-(20/81) : ℂ) • (v1)
      + ((-(20/81) : ℂ) * Complex.I) • (v2)
      + (-(20/81) : ℂ) • (v3) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i5 : T (T (T (T (T v0)))) =
      (41/162 : ℂ) • (v0)
      + (-(121/486) : ℂ) • (v1)
      + ((-(121/486) : ℂ) * Complex.I) • (v2)
      + (-(121/486) : ℂ) • (v3) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  rw [i5, i4, i3, i2, h0]
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 1 of the FMu block. -/
lemma projFMu1 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 : M}
    (h0 : T v0 = (1/2 : ℂ) • v0 + (-(1/6) : ℂ) • v1 + (-(Complex.I/6)) • v2 + (-(1/6) : ℂ) • v3)
    (h1 : T v1 = (5/6 : ℂ) • v1 + (-(1/6) : ℂ) • v0)
    (h2 : T v2 = (5/6 : ℂ) • v2 + (Complex.I/6) • v0)
    (h3 : T v3 = (5/6 : ℂ) • v3 + (-(1/6) : ℂ) • v0) :
    (-1 : ℂ) • v1 + (137/10 : ℂ) • T v1 + (-(135/2) : ℂ) • T (T v1)
      + (153 : ℂ) • T (T (T v1)) + (-162 : ℂ) • T (T (T (T v1)))
      + (324/5 : ℂ) • T (T (T (T (T v1)))) =
    (Complex.I/4) • (Complex.I • (v0 - v1 - Complex.I • v2 - v3)) := by
  have i2 : T (T v1) =
      (-(2/9) : ℂ) • (v0)
      + (13/18 : ℂ) • (v1)
      + ((1/36 : ℂ) * Complex.I) • (v2)
      + (1/36 : ℂ) • (v3) := by
    rw [h1]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i3 : T (T (T v1)) =
      (-(13/54) : ℂ) • (v0)
      + (23/36 : ℂ) • (v1)
      + ((13/216 : ℂ) * Complex.I) • (v2)
      + (13/216 : ℂ) • (v3) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i4 : T (T (T (T v1))) =
      (-(20/81) : ℂ) • (v0)
      + (371/648 : ℂ) • (v1)
      + ((13/144 : ℂ) * Complex.I) • (v2)
      + (13/144 : ℂ) • (v3) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i5 : T (T (T (T (T v1)))) =
      (-(121/486) : ℂ) • (v0)
      + (2015/3888 : ℂ) • (v1)
      + ((905/7776 : ℂ) * Complex.I) • (v2)
      + (905/7776 : ℂ) • (v3) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  rw [i5, i4, i3, i2, h1]
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 2 of the FMu block. -/
lemma projFMu2 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 : M}
    (h0 : T v0 = (1/2 : ℂ) • v0 + (-(1/6) : ℂ) • v1 + (-(Complex.I/6)) • v2 + (-(1/6) : ℂ) • v3)
    (h1 : T v1 = (5/6 : ℂ) • v1 + (-(1/6) : ℂ) • v0)
    (h2 : T v2 = (5/6 : ℂ) • v2 + (Complex.I/6) • v0)
    (h3 : T v3 = (5/6 : ℂ) • v3 + (-(1/6) : ℂ) • v0) :
    (-1 : ℂ) • v2 + (137/10 : ℂ) • T v2 + (-(135/2) : ℂ) • T (T v2)
      + (153 : ℂ) • T (T (T v2)) + (-162 : ℂ) • T (T (T (T v2)))
      + (324/5 : ℂ) • T (T (T (T (T v2)))) =
    (1/4 : ℂ) • (Complex.I • (v0 - v1 - Complex.I • v2 - v3)) := by
  have i2 : T (T v2) =
      ((2/9 : ℂ) * Complex.I) • (v0)
      + ((-(1/36) : ℂ) * Complex.I) • (v1)
      + (13/18 : ℂ) • (v2)
      + ((-(1/36) : ℂ) * Complex.I) • (v3) := by
    rw [h2]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i3 : T (T (T v2)) =
      ((13/54 : ℂ) * Complex.I) • (v0)
      + ((-(13/216) : ℂ) * Complex.I) • (v1)
      + (23/36 : ℂ) • (v2)
      + ((-(13/216) : ℂ) * Complex.I) • (v3) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i4 : T (T (T (T v2))) =
      ((20/81 : ℂ) * Complex.I) • (v0)
      + ((-(13/144) : ℂ) * Complex.I) • (v1)
      + (371/648 : ℂ) • (v2)
      + ((-(13/144) : ℂ) * Complex.I) • (v3) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i5 : T (T (T (T (T v2)))) =
      ((121/486 : ℂ) * Complex.I) • (v0)
      + ((-(905/7776) : ℂ) * Complex.I) • (v1)
      + (2015/3888 : ℂ) • (v2)
      + ((-(905/7776) : ℂ) * Complex.I) • (v3) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  rw [i5, i4, i3, i2, h2]
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 3 of the FMu block. -/
lemma projFMu3 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 : M}
    (h0 : T v0 = (1/2 : ℂ) • v0 + (-(1/6) : ℂ) • v1 + (-(Complex.I/6)) • v2 + (-(1/6) : ℂ) • v3)
    (h1 : T v1 = (5/6 : ℂ) • v1 + (-(1/6) : ℂ) • v0)
    (h2 : T v2 = (5/6 : ℂ) • v2 + (Complex.I/6) • v0)
    (h3 : T v3 = (5/6 : ℂ) • v3 + (-(1/6) : ℂ) • v0) :
    (-1 : ℂ) • v3 + (137/10 : ℂ) • T v3 + (-(135/2) : ℂ) • T (T v3)
      + (153 : ℂ) • T (T (T v3)) + (-162 : ℂ) • T (T (T (T v3)))
      + (324/5 : ℂ) • T (T (T (T (T v3)))) =
    (Complex.I/4) • (Complex.I • (v0 - v1 - Complex.I • v2 - v3)) := by
  have i2 : T (T v3) =
      (-(2/9) : ℂ) • (v0)
      + (1/36 : ℂ) • (v1)
      + ((1/36 : ℂ) * Complex.I) • (v2)
      + (13/18 : ℂ) • (v3) := by
    rw [h3]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i3 : T (T (T v3)) =
      (-(13/54) : ℂ) • (v0)
      + (13/216 : ℂ) • (v1)
      + ((13/216 : ℂ) * Complex.I) • (v2)
      + (23/36 : ℂ) • (v3) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i4 : T (T (T (T v3))) =
      (-(20/81) : ℂ) • (v0)
      + (13/144 : ℂ) • (v1)
      + ((13/144 : ℂ) * Complex.I) • (v2)
      + (371/648 : ℂ) • (v3) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i5 : T (T (T (T (T v3)))) =
      (-(121/486) : ℂ) • (v0)
      + (905/7776 : ℂ) • (v1)
      + ((905/7776 : ℂ) * Complex.I) • (v2)
      + (2015/3888 : ℂ) • (v3) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  rw [i5, i4, i3, i2, h3]
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 0 of the FMubar block. -/
lemma projFMubar0 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 : M}
    (h0 : T v0 = (1/2 : ℂ) • v0 + (-(1/6) : ℂ) • v1 + (-(Complex.I/6)) • v2 + (-(1/6) : ℂ) • v3)
    (h1 : T v1 = (5/6 : ℂ) • v1 + (-(1/6) : ℂ) • v0)
    (h2 : T v2 = (5/6 : ℂ) • v2 + (Complex.I/6) • v0)
    (h3 : T v3 = (5/6 : ℂ) • v3 + (-(1/6) : ℂ) • v0) :
    (-1 : ℂ) • v0 + (137/10 : ℂ) • T v0 + (-(135/2) : ℂ) • T (T v0)
      + (153 : ℂ) • T (T (T v0)) + (-162 : ℂ) • T (T (T (T v0)))
      + (324/5 : ℂ) • T (T (T (T (T v0)))) =
    (Complex.I/4) • ((-Complex.I) • (v0 - v1 - Complex.I • v2 - v3)) := by
  have i2 : T (T v0) =
      (1/3 : ℂ) • (v0)
      + (-(2/9) : ℂ) • (v1)
      + ((-(2/9) : ℂ) * Complex.I) • (v2)
      + (-(2/9) : ℂ) • (v3) := by
    rw [h0]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i3 : T (T (T v0)) =
      (5/18 : ℂ) • (v0)
      + (-(13/54) : ℂ) • (v1)
      + ((-(13/54) : ℂ) * Complex.I) • (v2)
      + (-(13/54) : ℂ) • (v3) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i4 : T (T (T (T v0))) =
      (7/27 : ℂ) • (v0)
      + (-(20/81) : ℂ) • (v1)
      + ((-(20/81) : ℂ) * Complex.I) • (v2)
      + (-(20/81) : ℂ) • (v3) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i5 : T (T (T (T (T v0)))) =
      (41/162 : ℂ) • (v0)
      + (-(121/486) : ℂ) • (v1)
      + ((-(121/486) : ℂ) * Complex.I) • (v2)
      + (-(121/486) : ℂ) • (v3) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  rw [i5, i4, i3, i2, h0]
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 1 of the FMubar block. -/
lemma projFMubar1 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 : M}
    (h0 : T v0 = (1/2 : ℂ) • v0 + (-(1/6) : ℂ) • v1 + (-(Complex.I/6)) • v2 + (-(1/6) : ℂ) • v3)
    (h1 : T v1 = (5/6 : ℂ) • v1 + (-(1/6) : ℂ) • v0)
    (h2 : T v2 = (5/6 : ℂ) • v2 + (Complex.I/6) • v0)
    (h3 : T v3 = (5/6 : ℂ) • v3 + (-(1/6) : ℂ) • v0) :
    (-1 : ℂ) • v1 + (137/10 : ℂ) • T v1 + (-(135/2) : ℂ) • T (T v1)
      + (153 : ℂ) • T (T (T v1)) + (-162 : ℂ) • T (T (T (T v1)))
      + (324/5 : ℂ) • T (T (T (T (T v1)))) =
    (-(Complex.I/4)) • ((-Complex.I) • (v0 - v1 - Complex.I • v2 - v3)) := by
  have i2 : T (T v1) =
      (-(2/9) : ℂ) • (v0)
      + (13/18 : ℂ) • (v1)
      + ((1/36 : ℂ) * Complex.I) • (v2)
      + (1/36 : ℂ) • (v3) := by
    rw [h1]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i3 : T (T (T v1)) =
      (-(13/54) : ℂ) • (v0)
      + (23/36 : ℂ) • (v1)
      + ((13/216 : ℂ) * Complex.I) • (v2)
      + (13/216 : ℂ) • (v3) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i4 : T (T (T (T v1))) =
      (-(20/81) : ℂ) • (v0)
      + (371/648 : ℂ) • (v1)
      + ((13/144 : ℂ) * Complex.I) • (v2)
      + (13/144 : ℂ) • (v3) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i5 : T (T (T (T (T v1)))) =
      (-(121/486) : ℂ) • (v0)
      + (2015/3888 : ℂ) • (v1)
      + ((905/7776 : ℂ) * Complex.I) • (v2)
      + (905/7776 : ℂ) • (v3) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  rw [i5, i4, i3, i2, h1]
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 2 of the FMubar block. -/
lemma projFMubar2 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 : M}
    (h0 : T v0 = (1/2 : ℂ) • v0 + (-(1/6) : ℂ) • v1 + (-(Complex.I/6)) • v2 + (-(1/6) : ℂ) • v3)
    (h1 : T v1 = (5/6 : ℂ) • v1 + (-(1/6) : ℂ) • v0)
    (h2 : T v2 = (5/6 : ℂ) • v2 + (Complex.I/6) • v0)
    (h3 : T v3 = (5/6 : ℂ) • v3 + (-(1/6) : ℂ) • v0) :
    (-1 : ℂ) • v2 + (137/10 : ℂ) • T v2 + (-(135/2) : ℂ) • T (T v2)
      + (153 : ℂ) • T (T (T v2)) + (-162 : ℂ) • T (T (T (T v2)))
      + (324/5 : ℂ) • T (T (T (T (T v2)))) =
    (-(1/4) : ℂ) • ((-Complex.I) • (v0 - v1 - Complex.I • v2 - v3)) := by
  have i2 : T (T v2) =
      ((2/9 : ℂ) * Complex.I) • (v0)
      + ((-(1/36) : ℂ) * Complex.I) • (v1)
      + (13/18 : ℂ) • (v2)
      + ((-(1/36) : ℂ) * Complex.I) • (v3) := by
    rw [h2]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i3 : T (T (T v2)) =
      ((13/54 : ℂ) * Complex.I) • (v0)
      + ((-(13/216) : ℂ) * Complex.I) • (v1)
      + (23/36 : ℂ) • (v2)
      + ((-(13/216) : ℂ) * Complex.I) • (v3) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i4 : T (T (T (T v2))) =
      ((20/81 : ℂ) * Complex.I) • (v0)
      + ((-(13/144) : ℂ) * Complex.I) • (v1)
      + (371/648 : ℂ) • (v2)
      + ((-(13/144) : ℂ) * Complex.I) • (v3) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i5 : T (T (T (T (T v2)))) =
      ((121/486 : ℂ) * Complex.I) • (v0)
      + ((-(905/7776) : ℂ) * Complex.I) • (v1)
      + (2015/3888 : ℂ) • (v2)
      + ((-(905/7776) : ℂ) * Complex.I) • (v3) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  rw [i5, i4, i3, i2, h2]
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 3 of the FMubar block. -/
lemma projFMubar3 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 : M}
    (h0 : T v0 = (1/2 : ℂ) • v0 + (-(1/6) : ℂ) • v1 + (-(Complex.I/6)) • v2 + (-(1/6) : ℂ) • v3)
    (h1 : T v1 = (5/6 : ℂ) • v1 + (-(1/6) : ℂ) • v0)
    (h2 : T v2 = (5/6 : ℂ) • v2 + (Complex.I/6) • v0)
    (h3 : T v3 = (5/6 : ℂ) • v3 + (-(1/6) : ℂ) • v0) :
    (-1 : ℂ) • v3 + (137/10 : ℂ) • T v3 + (-(135/2) : ℂ) • T (T v3)
      + (153 : ℂ) • T (T (T v3)) + (-162 : ℂ) • T (T (T (T v3)))
      + (324/5 : ℂ) • T (T (T (T (T v3)))) =
    (-(Complex.I/4)) • ((-Complex.I) • (v0 - v1 - Complex.I • v2 - v3)) := by
  have i2 : T (T v3) =
      (-(2/9) : ℂ) • (v0)
      + (1/36 : ℂ) • (v1)
      + ((1/36 : ℂ) * Complex.I) • (v2)
      + (13/18 : ℂ) • (v3) := by
    rw [h3]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i3 : T (T (T v3)) =
      (-(13/54) : ℂ) • (v0)
      + (13/216 : ℂ) • (v1)
      + ((13/216 : ℂ) * Complex.I) • (v2)
      + (23/36 : ℂ) • (v3) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i4 : T (T (T (T v3))) =
      (-(20/81) : ℂ) • (v0)
      + (13/144 : ℂ) • (v1)
      + ((13/144 : ℂ) * Complex.I) • (v2)
      + (371/648 : ℂ) • (v3) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i5 : T (T (T (T (T v3)))) =
      (-(121/486) : ℂ) • (v0)
      + (905/7776 : ℂ) • (v1)
      + ((905/7776 : ℂ) * Complex.I) • (v2)
      + (2015/3888 : ℂ) • (v3) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  rw [i5, i4, i3, i2, h3]
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
end JetAlgebra

end QED
