/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.HiggsBoson.Basic
/-!

# The Two Higgs Doublet Model

The two Higgs doublet model is the standard model plus an additional Higgs doublet.

## i. Overview

The two Higgs doublet model (2HDM) is an extension of the Standard Model which adds a second Higgs
doublet.

## References

- https://arxiv.org/abs/hep-ph/0605184
- https://arxiv.org/abs/1605.03237

-/

@[expose] public section

open StandardModel

/-!

## A. The configuration space

-/

/-- The configuration space of the two Higgs doublet model.
  In otherwords, the underlying vector space associated with the model. -/
structure TwoHiggsDoublet where
  /-- The first Higgs doublet. -/
  Φ1 : HiggsVec
  /-- The second Higgs doublet. -/
  Φ2 : HiggsVec

namespace TwoHiggsDoublet

open InnerProductSpace

@[ext]
lemma ext_of_fst_snd {H1 H2 : TwoHiggsDoublet}
    (h1 : H1.Φ1 = H2.Φ1) (h2 : H1.Φ2 = H2.Φ2) : H1 = H2 := by
  cases H1
  cases H2
  congr
/-!

## B. Gauge group actions

-/

noncomputable instance : SMul StandardModel.GaugeGroupI TwoHiggsDoublet where
  smul g H :=
    { Φ1 := g • H.Φ1
      Φ2 := g • H.Φ2 }

@[simp]
lemma gaugeGroupI_smul_fst (g : StandardModel.GaugeGroupI) (H : TwoHiggsDoublet) :
    (g • H).Φ1 = g • H.Φ1 := rfl

@[simp]
lemma gaugeGroupI_smul_snd (g : StandardModel.GaugeGroupI) (H : TwoHiggsDoublet) :
    (g • H).Φ2 = g • H.Φ2 := rfl

noncomputable instance : MulAction StandardModel.GaugeGroupI TwoHiggsDoublet where
  one_smul H := by
    ext <;> simp
  mul_smul g1 g2 H := by
    ext <;> simp [mul_smul]

/-!

## The structure of a module

-/

instance : Add TwoHiggsDoublet where
  add H1 H2 := { Φ1 := H1.Φ1 + H2.Φ1, Φ2 := H1.Φ2 + H2.Φ2 }

@[simp]
lemma add_fst (H1 H2 : TwoHiggsDoublet) : (H1 + H2).Φ1 = H1.Φ1 + H2.Φ1 := rfl

@[simp]
lemma add_snd (H1 H2 : TwoHiggsDoublet) : (H1 + H2).Φ2 = H1.Φ2 + H2.Φ2 := rfl

instance : Zero TwoHiggsDoublet where
  zero := { Φ1 := 0, Φ2 := 0 }

@[simp]
lemma zero_fst : (0 : TwoHiggsDoublet).Φ1 = 0 := rfl

@[simp]
lemma zero_snd : (0 : TwoHiggsDoublet).Φ2 = 0 := rfl

instance : SMul ℂ TwoHiggsDoublet where
  smul c H := { Φ1 := c • H.Φ1, Φ2 := c • H.Φ2 }

@[simp]
lemma smul_fst (c : ℂ) (H : TwoHiggsDoublet) : (c • H).Φ1 = c • H.Φ1 := rfl

@[simp]
lemma smul_snd (c : ℂ) (H : TwoHiggsDoublet) : (c • H).Φ2 = c • H.Φ2 := rfl

instance : AddCommMonoid TwoHiggsDoublet where
  add_assoc H1 H2 H3 := by
    ext <;> simp [add_assoc]
  zero_add H := by
    ext <;> simp
  add_zero H := by
    ext <;> simp
  nsmul := nsmulRec
  add_comm H1 H2 := by
    ext <;> simp [add_comm]

instance : Module ℂ TwoHiggsDoublet where
  smul_add c H1 H2 := by
    ext <;> simp [smul_add]
  add_smul c1 c2 H := by
    ext <;> simp [add_smul]
  one_smul H := by
    ext <;> simp [one_smul]
  mul_smul c1 c2 H := by
    ext <;> simp [mul_smul]
  smul_zero c := by
    ext <;> simp [smul_zero]
  zero_smul H := by
    ext <;> simp [zero_smul]

end TwoHiggsDoublet
