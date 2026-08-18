/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.MaurerCartan.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.Jet.Truncation
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
# The Maurer–Cartan forms and the truncation kernels
-/

@[expose] public section
namespace StandardModel
open MvPowerSeries JetGaugeAlgebra
/-- Projecting onto the zeroth truncation kernel does not change the Maurer–Cartan
  form: by the cocycle law, right-multiplication by a constant gauge transformation
  drops out. -/
lemma maurerCartanForm_truncationProjZero (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3) :
    maurerCartanForm (JetGaugeGroupI.truncationProjZero U : JetGaugeGroupI) μ =
      maurerCartanForm U μ := by
  rw [show (JetGaugeGroupI.truncationProjZero U : JetGaugeGroupI) =
      U * (JetGaugeGroupI.ofConstant U.eval)⁻¹ from rfl,
    ← map_inv, maurerCartanForm_cocycle, maurerCartanForm_ofConstant]
  simp

/-- A pure jet is determined by its Maurer–Cartan form: on the kernel of the zeroth
  truncation, `U ↦ ω(U)` is injective. By the cocycle and inverse laws
  `ω(V⁻¹ U) = Ad_{V⁻¹}(ω(U) − ω(V)) = 0`, so `V⁻¹ U` is a constant jet, and purity
  of `U` and `V` forces that constant to be the identity. -/
lemma maurerCartanForm_injOn_truncationKer_zero {U V : JetGaugeGroupI}
    (hU : U ∈ JetGaugeGroupI.truncationKer 0) (hV : V ∈ JetGaugeGroupI.truncationKer 0)
    (h : maurerCartanForm U = maurerCartanForm V) : U = V := by
  have h1 : maurerCartanForm (V⁻¹ * U) = 0 := by
    funext μ
    rw [maurerCartanForm_cocycle, maurerCartanForm_inv, congrFun h μ]
    simp
  obtain ⟨c, hc⟩ := (maurerCartanForm_eq_zero_iff_ofConstant _).mp h1
  have hc1 : c = 1 := by
    have he := congrArg JetGaugeGroupI.eval hc
    rw [map_mul, map_inv, JetGaugeGroupI.mem_truncationKer_zero_iff.mp hU,
      JetGaugeGroupI.mem_truncationKer_zero_iff.mp hV, JetGaugeGroupI.eval_ofConstant] at he
    simpa using he.symm
  rw [hc1, map_one] at hc
  exact (inv_mul_eq_one.mp hc).symm

/-!

## Freeness: injectivity of the symmetrized Maurer–Cartan data

-/

/-- The symmetrized Maurer–Cartan data of a pure jet: the base-point values of its
  symmetrized Maurer–Cartan forms, indexed by nonempty multisets of directions.
  Total symmetry is automatic from the multiset indexing. -/
noncomputable def symmetrizedMaurerCartanCoeff (U : JetGaugeGroupI.truncationKer 0)
    (r : {r : Multiset (Fin 1 ⊕ Fin 3) // r ≠ 0}) : GaugeAlgebra :=
  eval (symmetrizedMaurerCartanForm U.1 r.1)

/-- Freeness, injectivity half: a pure jet is determined by its symmetrized
  Maurer–Cartan data. The symmetrized data determine all Maurer–Cartan Taylor data
  by strong induction with `eval_iteratedDeriv_maurerCartanForm_eq_of_symmetrized_eq`,
  hence the Maurer–Cartan form itself by Taylor determinacy, hence the pure jet by
  `maurerCartanForm_injOn_truncationKer_zero`. -/
lemma symmetrizedMaurerCartanCoeff_injective : Function.Injective symmetrizedMaurerCartanCoeff := by
  intro U V h
  -- the hypothesis extends to all multisets, the empty one trivially
  have hsym : ∀ r, eval (symmetrizedMaurerCartanForm U.1 r) =
      eval (symmetrizedMaurerCartanForm V.1 r) := by
    intro r
    by_cases hr : r = 0
    · subst hr
      simp
    · exact congrFun h ⟨r, hr⟩
  -- all Maurer–Cartan Taylor data agree, by strong induction on the number of directions
  have hall : ∀ (n : ℕ) (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3), s.card = n →
      eval (iteratedDeriv s (maurerCartanForm U.1 μ)) =
        eval (iteratedDeriv s (maurerCartanForm V.1 μ)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
        intro s μ hs
        exact eval_iteratedDeriv_maurerCartanForm_eq_of_symmetrized_eq U.1 V.1 n hsym
          (fun p ν hp => ih p.card hp p ν rfl) s μ hs
  -- hence the Maurer–Cartan forms agree, by Taylor determinacy
  have hmc : maurerCartanForm U.1 = maurerCartanForm V.1 := by
    funext μ
    exact ext_of_eval_iteratedDeriv fun s => hall s.card s μ rfl
  exact Subtype.ext (maurerCartanForm_injOn_truncationKer_zero U.2 V.2 hmc)

end StandardModel
