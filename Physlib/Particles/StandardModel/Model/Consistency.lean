/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.LocalGaugeData
public import Physlib.Particles.StandardModel.Fermions.QuarkDoublet.GaugeAlgebraAction
public import Physlib.Particles.StandardModel.Fermions.LeptonDoublet.GaugeAlgebraAction
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
- `StandardModel.Model.quarkDoublet_rep_mat`, `leptonDoublet_rep_mat` : the quark and lepton
  rows reproduce `QuarkDoublet.jetGaugeMatrix` and `LeptonDoublet.doubletMatrix`, on the
  same index types.

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

/-- The charges of the lepton row. -/
abbrev leptonCharges : Charges factors := (.singlet, .fund, -3)

/-- The quark row is indexed by a colour and a weak index, as the existing quark doublet. -/
example : Idx factors quarkCharges = (Fin 3 × Fin 2) := rfl

/-- The lepton row is indexed by a weak index alone, as the existing lepton doublet. -/
example : Idx factors leptonCharges = Fin 2 := rfl

/-- The quark row acts on its colour–weak index by the existing matrix `u · (U₃ ⊗ U₂)` of
  the quark doublet. -/
lemma quarkDoublet_rep_mat (U : JetGaugeGroupI) :
    (Charges.rep factors quarkCharges).mat U = QuarkDoublet.jetGaugeMatrix U := by
  show MatterField.chargePow 1 U.2.2 • Matrix.kroneckerMap (· * ·) U.1.1 U.2.1.1
    = QuarkDoublet.jetGaugeMatrix U
  simp [MatterField.chargePow, QuarkDoublet.jetGaugeMatrix]

/-- The lepton row acts on its weak index by the existing matrix `ū³ · U₂` of the lepton
  doublet. -/
lemma leptonDoublet_rep_mat (U : JetGaugeGroupI) :
    (Charges.rep factors leptonCharges).mat U = LeptonDoublet.doubletMatrix U := by
  show MatterField.chargePow (-3) U.2.2 • U.2.1.1 = LeptonDoublet.doubletMatrix U
  rw [LeptonDoublet.doubletMatrix]
  congr 1

end Model

end StandardModel
