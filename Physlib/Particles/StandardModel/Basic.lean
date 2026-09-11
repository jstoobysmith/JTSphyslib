/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.OfFactors
/-!
# The Standard Model

## i. Overview

The Standard Model as a model table: the gauge group `SU(3) × SU(2) × U(1)` named by its
factors, one row per fermion field and one row per scalar field. Everything else is
derived: the local gauge data of the gauge group is assembled from the factors by
`LocalGaugeData.ofFactors`, and the table compiles, through
`Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.MatrixRep.Table`, to the field
content `StandardModel.Model.fieldData : GaugeFieldData gaugeData`, from which the general
theory derives the algebra of field operators and the gauge and Lorentz actions.

Each row lists the name of the field, its number of generations, its chirality, and its
charges in the order of the factors: the `SU(3)` label, the `SU(2)` label and the
hypercharge. Hypercharges are integers, six times the conventional `Y`, so that the gauge
group acting is the honest `U(1)` of unitary jets. The right-handed singlets are
right-handed Weyl spinors in the fundamental of colour rather than conjugate left-handed
fields.

## ii. Key results

- `StandardModel.Model.gauge` : the gauge group, as a list of factors.
- `StandardModel.Model.gaugeData` : its local gauge data.
- `StandardModel.Model.fermions`, `scalars` : the field tables.
- `StandardModel.Model.fieldData` : the field content of the Standard Model.

## iii. Table of contents

- A. The gauge group
- B. The fields
- C. The field content

-/

@[expose] public section

open LocalGaugeData

namespace StandardModel

namespace Model

/-!

## A. The gauge group

-/

/-- The gauge group `SU(3) × SU(2) × U(1)`, as a list of factors. -/
abbrev gauge : List FactorSpec := [.SU 3, .SU 2, .U1]

/-- The local gauge data of the Standard Model gauge group: jets of `SU(3) × SU(2) × U(1)`
  gauge transformations with their Lie algebra of jets. -/
noncomputable abbrev gaugeData := ofFactors gauge

/-- The factors of the gauge group, as what the rows are charged under. -/
noncomputable abbrev factors : Factors gaugeData := Factors.factors gauge

/-!

## B. The fields

-/

/-- The fermion fields: `q ∼ (3, 2)_{1}`, `l ∼ (1, 2)_{-3}`, `u ∼ (3, 1)_{4}`,
  `d ∼ (3, 1)_{-2}`, `e ∼ (1, 1)_{-6}`, three generations each. -/
def fermions : List (FermionRow factors) :=
  [ ⟨"q", 3, .L, (.fund, .fund, 1)⟩,
    ⟨"l", 3, .L, (.singlet, .fund, -3)⟩,
    ⟨"u", 3, .R, (.fund, .singlet, 4)⟩,
    ⟨"d", 3, .R, (.fund, .singlet, -2)⟩,
    ⟨"e", 3, .R, (.singlet, .singlet, -6)⟩ ]

/-- The scalar fields: the Higgs `H ∼ (1, 2)_{3}`. -/
def scalars : List (ScalarRow factors) := [⟨"H", 1, (.singlet, .fund, 3)⟩]

/-!

## C. The field content

-/

/-- **The Standard Model table.** -/
noncomputable def table : Table gaugeData := ⟨factors, fermions, scalars⟩

/-- **The field content of the Standard Model**: the fifteen fermionic species (five rows
  in three generations) and the Higgs, as matter fields of `gaugeData`. -/
noncomputable def fieldData : GaugeFieldData gaugeData := table.fieldData

/-- The Standard Model has fifteen fermionic species. -/
lemma card_fermionSpecies : Fintype.card fieldData.FermionSpecies = 15 := by decide

/-- The Standard Model has one bosonic species. -/
lemma card_bosonSpecies : Fintype.card fieldData.BosonSpecies = 1 := by decide

end Model

end StandardModel
