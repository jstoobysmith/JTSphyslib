/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.MaurerCartan.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.Jet.Pure
public import Physlib.Particles.StandardModel.GaugeAlgebra.JetGaugeAlgebra
public import Physlib.Relativity.Tensors.ComplexTensor.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Representation
public import Physlib.Relativity.SL2C.Basic
public import Physlib.Mathematics.ConjModule
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Physlib.Particles.LagrangianTheory.Basic
public import Physlib.Mathematics.MvPowerSeriesDerivative
public import Physlib.Mathematics.MvPolynomialTranslation
public import Mathlib.Algebra.MvPolynomial.Derivation
/-!
# The Maurer–Cartan forms and the pure subgroup
-/

@[expose] public section
namespace StandardModel
open MvPowerSeries JetGaugeAlgebra
namespace JetGaugeGroup
namespace PureSubgroup

/-- Projecting onto the pure subgroup does not change the Maurer–Cartan form: by the
  cocycle law, right-multiplication by a constant gauge transformation drops out. -/
lemma maurerCartanForm_proj (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3) :
    maurerCartanForm (proj U : JetGaugeGroupI) μ = maurerCartanForm U μ := by
  rw [show (proj U : JetGaugeGroupI) = U * (JetGaugeGroupI.ofConstant U.eval)⁻¹ from rfl,
    ← map_inv, maurerCartanForm_cocycle, maurerCartanForm_ofConstant]
  simp

end PureSubgroup
end JetGaugeGroup
end StandardModel
