/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.LorentzAction
/-!
# The jet derivative is a Lorentz vector

The total derivative `∂_μ` on the jet algebra carries a spacetime index, and this file proves
that it carries it covariantly:

`ρ(Λ) (∂_μ x) = ∑ a, Λ_{aμ} • ∂_a (ρ(Λ) x)`.

*The proof follows the derivation.* On the B-boson factor the jet algebra is the symmetric
algebra of the component space, `∂_μ` is the derivation determined by appending `μ` to the
derivative multiset, and appending is, at the component level, multiplication of the
derivative-symbol factor by `∂_μ` (`JetComponentSpace.shiftLin`). The representation is
multiplicative there, and `∂_μ` transforms as a dual covector
(`Lorentz.CoVector.sl2Rep_dual_dualBasis`), which gives the identity on the component space;
the symmetric-algebra induction then carries it to the jet algebra, the Leibniz rule handling
the products. Base change to `ℂ` and the tensor decomposition of the lepton–gauge-sector jet
algebra give the statement on the purely bosonic part, which is where the derivatives of the
field strength live.

## Key results

- `StandardModel.BBoson.JetAlgebra.repLorentzGroup_jetDeriv` : the covariance on the B-boson
  jet algebra.
- `LeptonGaugeSector.JetAlgebra.repLorentzGroup_jetDeriv_tmul_one` : the covariance on the
  bosonic part of the lepton–gauge-sector jet algebra.

-/

@[expose] public section

namespace LeptonGaugeSector
open TensorProduct StandardModel Matrix MatrixGroups

namespace JetAlgebra

set_option maxHeartbeats 1000000 in
/-- **The jet derivative of a gauge-field element is a Lorentz vector.** On the purely bosonic
  part of the jet algebra — where the second derivatives of the field strength live — the total
  derivative `∂_μ` transforms as a covector, mixing the spacetime directions by the columns of
  the Lorentz matrix. -/
lemma repLorentzGroup_jetDeriv_tmul_one (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3)
    (p : ℂ ⊗[ℝ] BBoson.JetAlgebra) :
    repLorentzGroup Λ (jetDeriv μ (p ⊗ⱼ (1 : LeptonSinglet.JetAlgebra))) =
      ∑ a, (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) •
        jetDeriv a (repLorentzGroup Λ (p ⊗ⱼ (1 : LeptonSinglet.JetAlgebra))) := by
  have hone : LeptonSinglet.JetAlgebra.repLorentzGroup Λ (1 : LeptonSinglet.JetAlgebra) = 1 :=
    LeptonSinglet.JetAlgebra.repLorentzGroup_apply_one Λ
  have hd : ∀ (q : ℂ ⊗[ℝ] BBoson.JetAlgebra) (ν : Fin 1 ⊕ Fin 3),
      jetDeriv ν (q ⊗ⱼ (1 : LeptonSinglet.JetAlgebra)) =
        (LinearMap.baseChange ℂ (BBoson.JetAlgebra.jetDeriv ν) q) ⊗ⱼ
          (1 : LeptonSinglet.JetAlgebra) := fun q ν => by
    rw [jetDeriv_tmul, LeptonSinglet.JetAlgebra.jetDeriv_one, tmul_zero, add_zero]
  rw [hd, repLorentzGroup_tmul, repLorentzGroup_tmul, hone,
    BBoson.JetAlgebra.complexRepLorentzGroup_baseChange_jetDeriv, sum_tmul]
  exact Finset.sum_congr rfl fun a _ => by rw [hd, smul_tmul']

/-!

## The bosonic part and the light-cone derivatives

-/

/-- The purely bosonic part of the jet algebra: the elements whose lepton factor is trivial.
  The derivatives of the field strength live here. -/
noncomputable def bosonic : Submodule ℂ JetAlgebra :=
  LinearMap.range ((TensorProduct.mk ℂ (ℂ ⊗[ℝ] BBoson.JetAlgebra)
    LeptonSinglet.JetAlgebra).flip (1 : LeptonSinglet.JetAlgebra))

/-- Membership of the bosonic part, unfolded. -/
lemma mem_bosonic {x : JetAlgebra} :
    x ∈ bosonic ↔ ∃ p : ℂ ⊗[ℝ] BBoson.JetAlgebra,
      p ⊗ⱼ (1 : LeptonSinglet.JetAlgebra) = x := Iff.rfl

lemma fieldStrengthDeriv_mem_bosonic (s : Multiset (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) :
    fieldStrengthDeriv s μ ν ∈ bosonic := mem_bosonic.2 ⟨_, rfl⟩

lemma jetDeriv_mem_bosonic (μ : Fin 1 ⊕ Fin 3) {x : JetAlgebra} (hx : x ∈ bosonic) :
    jetDeriv μ x ∈ bosonic := by
  obtain ⟨p, rfl⟩ := mem_bosonic.1 hx
  refine mem_bosonic.2 ⟨LinearMap.baseChange ℂ (BBoson.JetAlgebra.jetDeriv μ) p, ?_⟩
  rw [jetDeriv_tmul, LeptonSinglet.JetAlgebra.jetDeriv_one, tmul_zero, add_zero]

/-- Bosonic elements are central in the jet algebra: the bosonic factor is commutative, and
  it commutes with the lepton factor across the tensor product. -/
lemma mul_comm_of_mem_bosonic {x : JetAlgebra} (hx : x ∈ bosonic) (y : JetAlgebra) :
    x * y = y * x := by
  obtain ⟨p, rfl⟩ := mem_bosonic.1 hx
  induction y using JetAlgebra.induction_on with
  | zero => rw [mul_zero, zero_mul]
  | add u v hu hv => rw [mul_add, add_mul, hu, hv]
  | tmul b l => rw [tmul_mul_tmul, tmul_mul_tmul, mul_one, one_mul, mul_comm p b]

/-- The covariance of the jet derivative on the bosonic part. -/
lemma repLorentzGroup_jetDeriv_of_mem_bosonic (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3)
    {x : JetAlgebra} (hx : x ∈ bosonic) :
    repLorentzGroup Λ (jetDeriv μ x) =
      ∑ a, (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) •
        jetDeriv a (repLorentzGroup Λ x) := by
  obtain ⟨p, rfl⟩ := mem_bosonic.1 hx
  exact repLorentzGroup_jetDeriv_tmul_one Λ μ p

set_option maxHeartbeats 4000000 in
/-- **The jet derivative on the lepton–gauge-sector jet algebra is a Lorentz vector.** The
  covariance of `repLorentzGroup_jetDeriv_of_mem_bosonic`, extended to the whole jet algebra
  by combining the covariance on the two tensor factors through the Leibniz rule. -/
lemma repLorentzGroup_jetDeriv (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) (x : JetAlgebra) :
    repLorentzGroup Λ (jetDeriv μ x) =
      ∑ a, (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) •
        jetDeriv a (repLorentzGroup Λ x) := by
  induction x using JetAlgebra.induction_on with
  | zero => simp
  | add u v hu hv =>
    rw [map_add, map_add, map_add, hu, hv, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [map_add, smul_add]
  | tmul p l =>
    rw [jetDeriv_tmul, map_add, repLorentzGroup_tmul, repLorentzGroup_tmul,
      repLorentzGroup_tmul, BBoson.JetAlgebra.complexRepLorentzGroup_baseChange_jetDeriv,
      LeptonSinglet.JetAlgebra.repLorentzGroup_jetDeriv, sum_tmul, tmul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [jetDeriv_tmul, smul_add, smul_tmul', tmul_smul]

end JetAlgebra

end LeptonGaugeSector

end
