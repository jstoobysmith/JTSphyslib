/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.LorentzAction
public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.DerivativeOrder
/-!
# Invariance in the lepton–gauge-sector jet algebra

An element of the jet algebra is invariant when it is fixed by the jet gauge group and by the
Lorentz group. This file defines that condition, collects the invariants into a submodule,
and characterises them: an element is invariant exactly when it lies in the algebra generated
by the field-strength derivatives and the covariant derivatives, is fixed by the constant
gauge transformations, and is Lorentz invariant.

The forward direction is `mem_covariantAlgebra_of_forall_repJetGaugeGroupI_eq`, proved
through the derivative-order filtration; the backward direction holds because a jet of gauge
transformations acts on the covariant generators only through its value at the base point.
-/

@[expose] public section

namespace LeptonGaugeSector
open TensorProduct StandardModel

namespace JetAlgebra

open Matrix MatrixGroups

/-!

## A. The invariance condition

-/

def IsInvariant (x : JetAlgebra) : Prop :=
  (∀ U : JetGaugeGroupI, repJetGaugeGroupI U x = x)
  ∧ (∀ Λ : SL(2,ℂ), repLorentzGroup Λ x = x)

lemma IsInvariant.add {x y : JetAlgebra} (hx : IsInvariant x) (hy : IsInvariant y) :
    IsInvariant (x + y) := by
  constructor
  · intro U
    simp [hx.left, hy.left]
  · intro Λ
    simp [hx.right, hy.right]

lemma IsInvariant.smul {x : JetAlgebra} (hx : IsInvariant x) (r : ℂ) :
    IsInvariant (r • x) := by
  constructor
  · intro U
    simp [hx.left]
  · intro Λ
    simp [hx.right]

noncomputable def InvariantSubmodule : Submodule ℂ JetAlgebra :=
  Submodule.span ℂ {x | IsInvariant x}

lemma InvariantSubmodule.mem_iff_isInvariant (x : JetAlgebra) :
    x ∈ InvariantSubmodule ↔ IsInvariant x := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact hy
    | zero => exact ⟨fun U => map_zero _, fun Λ => map_zero _⟩
    | add y z hy hz ihy ihz =>
      exact ⟨fun U => by rw [map_add, ihy.1 U, ihz.1 U],
        fun Λ => by rw [map_add, ihy.2 Λ, ihz.2 Λ]⟩
    | smul c y hy ihy =>
      exact ⟨fun U => by rw [map_smul, ihy.1 U],
        fun Λ => by rw [map_smul, ihy.2 Λ]⟩
  · exact fun hx => Submodule.subset_span hx


/-- Characterisation of the invariants of the lepton–gauge-sector jet algebra: an element is
  invariant under the jet gauge group and the Lorentz group precisely when it lies in the
  covariant subalgebra, is fixed by the constant gauge transformations, and is Lorentz
  invariant. The forward direction is the classification theorem; the backward direction holds
  because a jet of gauge transformations acts on the covariant generators only through its
  value at the base point. -/
lemma isInvariant_iff_mem_covariantAlgebra (x : JetAlgebra) :
    IsInvariant x ↔ x ∈ CovariantAlgebra ∧
      (∀ g : GaugeGroupI, repJetGaugeGroupI (.ofConstant g) x = x) ∧
      (∀ Λ : SL(2, ℂ), repLorentzGroup Λ x = x) := by
  constructor
  · intro h
    exact ⟨mem_covariantAlgebra_of_forall_repJetGaugeGroupI_eq x h.1, fun g => h.1 _, h.2⟩
  · rintro ⟨hmem, hconst, hlor⟩
    refine ⟨fun U => ?_, hlor⟩
    suffices hkey : repJetGaugeGroupI U x =
        repJetGaugeGroupI (JetGaugeGroupI.ofConstant U.eval) x by
      rw [hkey]
      exact hconst U.eval
    clear hconst hlor
    induction hmem using CovariantAlgebra.induction_on with
    | fieldStrength s μ ν =>
      rw [repJetGaugeGroupI_fieldStrengthDeriv, repJetGaugeGroupI_fieldStrengthDeriv]
    | lepton l α =>
      rw [repJetGaugeGroupI_Dψ, repJetGaugeGroupI_Dψ, JetGaugeGroupI.eval_ofConstant]
    | conjLepton l α =>
      rw [repJetGaugeGroupI_Dbarψ, repJetGaugeGroupI_Dbarψ, JetGaugeGroupI.eval_ofConstant]
    | algebraMap r =>
      rw [Algebra.algebraMap_eq_smul_one, map_smul, map_smul,
        repJetGaugeGroupI_apply_one, repJetGaugeGroupI_apply_one]
    | add u v _ _ ihu ihv => rw [map_add, map_add, ihu, ihv]
    | mul u v _ _ ihu ihv =>
      rw [repJetGaugeGroupI_apply_mul, repJetGaugeGroupI_apply_mul, ihu, ihv]

end JetAlgebra

end LeptonGaugeSector
