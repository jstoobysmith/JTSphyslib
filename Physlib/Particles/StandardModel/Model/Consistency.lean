/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.LocalGaugeData
public import Physlib.Particles.StandardModel.Fermions.QuarkDoublet.GaugeAlgebraAction
/-!
# Consistency of the Standard Model table with the existing formalisation

## i. Overview

The Standard Model of `Physlib.Particles.StandardModel.Basic` is built from its table
alone. This file checks it against the hand-built formalisation: the local gauge data
assembled from the factors is the existing `StandardModel.localGaugeData`, and the quark
row acts by the existing colour–weak matrix of the quark doublet.

## ii. Key results

- `StandardModel.Model.localGaugeData_eq` : the gauge data of the table is the existing
  local gauge data of the Standard Model.
- `StandardModel.Model.quarkDoublet_rep_mat` : the quark row reproduces
  `QuarkDoublet.jetGaugeMatrix`.

-/

@[expose] public section

open LocalGaugeData Matrix

namespace StandardModel

namespace Model

/-- The local gauge data assembled from the factors of the table is the existing local
  gauge data of the Standard Model. -/
theorem localGaugeData_eq : StandardModel.localGaugeData = gaugeData := rfl

/-- The charges of the quark row. -/
abbrev quarkCharges : Charges factors := (.fund, .fund, 1)

/-- The quark row acts on its colour–weak index by the existing matrix `u · (U₃ ⊗ U₂)` of
  the quark doublet, up to the trivial index of the `U(1)` factor. -/
lemma quarkDoublet_rep_mat (U : JetGaugeGroupI) :
    Matrix.reindex (Equiv.prodCongr (Equiv.refl (Fin 3)) (Equiv.prodUnique (Fin 2) (Fin 1)))
        (Equiv.prodCongr (Equiv.refl (Fin 3)) (Equiv.prodUnique (Fin 2) (Fin 1)))
        ((Charges.rep factors quarkCharges).mat U)
      = QuarkDoublet.jetGaugeMatrix U := by
  show Matrix.reindex (Equiv.prodCongr (Equiv.refl (Fin 3)) (Equiv.prodUnique (Fin 2) (Fin 1)))
        (Equiv.prodCongr (Equiv.refl (Fin 3)) (Equiv.prodUnique (Fin 2) (Fin 1)))
        (Matrix.kroneckerMap (· * ·) U.1.1 (Matrix.kroneckerMap (· * ·) U.2.1.1
          (MatterField.chargePow 1 U.2.2 • (1 : Matrix (Fin 1) (Fin 1) JetRing))))
      = QuarkDoublet.jetGaugeMatrix U
  refine Matrix.ext fun i j => ?_
  simp [Matrix.kroneckerMap_apply, MatterField.chargePow, QuarkDoublet.jetGaugeMatrix]
  ring

end Model

end StandardModel
