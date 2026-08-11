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

namespace StandardModel
open TensorProduct Matrix MatrixGroups

namespace BBoson

/-- The real derivative-algebra representation is multiplicative: it is the lift of a linear
  map to the symmetric algebra. -/
lemma _root_.DerivAlgebraReal.repLorentzGroup_apply_mul (Λ : SL(2,ℂ))
    (a b : DerivAlgebraReal) :
    DerivAlgebraReal.repLorentzGroup Λ (a * b) =
      DerivAlgebraReal.repLorentzGroup Λ a * DerivAlgebraReal.repLorentzGroup Λ b := by
  simp [DerivAlgebraReal.repLorentzGroup]

namespace JetComponentSpace

/-- Appending a derivative index, as a linear map on the B-boson jet component space: it
  multiplies the derivative-symbol factor by the symbol `∂_μ`. -/
noncomputable def shiftLin (μ : Fin 1 ⊕ Fin 3) : JetComponentSpace →ₗ[ℝ] JetComponentSpace :=
  TensorProduct.map
    (LinearMap.mulRight ℝ (LagrangianTheory.dualRealJetAlgebraBasis ({μ} : Multiset _)))
    LinearMap.id

lemma shiftLin_tmul (μ : Fin 1 ⊕ Fin 3)
    (p : SymmetricAlgebra ℝ (Module.Dual ℝ Lorentz.CoVector))
    (f : Module.Dual ℝ BBoson) :
    shiftLin μ (p ⊗ₜ[ℝ] f) =
      (p * LagrangianTheory.dualRealJetAlgebraBasis ({μ} : Multiset _)) ⊗ₜ[ℝ] f := rfl

/-- On the basis, the shift appends the derivative index. -/
@[simp]
lemma shiftLin_basis (μ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (ν : Fin 1 ⊕ Fin 3) :
    shiftLin μ (JetComponentSpace.basis (.dB s ν)) =
      JetComponentSpace.basis (.dB (s + {μ}) ν) := by
  rw [jetComponentSpace_basis_dB, shiftLin_tmul, dualRealJetAlgebraBasis_mul,
    jetComponentSpace_basis_dB]


/-- **The shift is Lorentz covariant on the component space.** Appending `∂_μ` and then acting
  is acting and then appending the transformed `∂_μ`, which is a combination of the `∂_a`. -/
lemma repLorentzGroup_shiftLin (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) (v : JetComponentSpace) :
    JetComponentSpace.repLorentzGroup Λ (shiftLin μ v) =
      ∑ a, (Lorentz.SL2C.toLorentzGroup Λ).1 a μ •
        shiftLin a (JetComponentSpace.repLorentzGroup Λ v) := by
  have hsym : DerivAlgebraReal.repLorentzGroup Λ
      (LagrangianTheory.dualRealJetAlgebraBasis ({μ} : Multiset _)) =
      ∑ a, (Lorentz.SL2C.toLorentzGroup Λ).1 a μ •
        LagrangianTheory.dualRealJetAlgebraBasis ({a} : Multiset _) := by
    rw [dualRealJetAlgebraBasis_singleton, DerivAlgebraReal.repLorentzGroup_apply_ι,
      Lorentz.CoVector.sl2Rep_dual_dualBasis, map_sum]
    exact Finset.sum_congr rfl fun a _ => by
      rw [map_smul, dualRealJetAlgebraBasis_singleton]
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, map_add, map_add, hx, hy, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [map_add, smul_add]
  | tmul p f =>
    have hrep : ∀ q : SymmetricAlgebra ℝ (Module.Dual ℝ Lorentz.CoVector),
        JetComponentSpace.repLorentzGroup Λ (q ⊗ₜ[ℝ] f) =
          (DerivAlgebraReal.repLorentzGroup Λ q) ⊗ₜ[ℝ]
            (BBoson.repLorentzGroup.dual Λ f) := fun _ => rfl
    rw [shiftLin_tmul, hrep, hrep, DerivAlgebraReal.repLorentzGroup_apply_mul, hsym,
      Finset.mul_sum, TensorProduct.sum_tmul]
    exact Finset.sum_congr rfl fun a _ => by
      rw [mul_smul_comm, shiftLin_tmul, TensorProduct.smul_tmul']

end JetComponentSpace

namespace JetAlgebra

/-- The jet derivative on a linear generator is the component-space shift. -/
lemma jetDeriv_ι (μ : Fin 1 ⊕ Fin 3) (v : JetComponentSpace) :
    jetDeriv μ (SymmetricAlgebra.ι ℝ JetComponentSpace v) =
      SymmetricAlgebra.ι ℝ JetComponentSpace (JetComponentSpace.shiftLin μ v) := by
  have key : (jetDeriv μ) ∘ₗ (SymmetricAlgebra.ι ℝ JetComponentSpace) =
      (SymmetricAlgebra.ι ℝ JetComponentSpace) ∘ₗ (JetComponentSpace.shiftLin μ) := by
    refine JetComponentSpace.basis.ext fun g => ?_
    cases g with
    | dB s ν =>
      simp only [LinearMap.coe_comp, Function.comp_apply,
        show SymmetricAlgebra.ι ℝ JetComponentSpace (JetComponentSpace.basis (.dB s ν)) =
          ofGenerator (.dB s ν) from rfl,
        jetDeriv_ofGenerator, JetGenerators.shift_dB,
        JetComponentSpace.shiftLin_basis]
      rfl
  exact DFunLike.congr_fun key v

set_option maxHeartbeats 4000000 in
/-- **The jet derivative on the B-boson jet algebra is a Lorentz vector.** -/
lemma repLorentzGroup_jetDeriv (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) (x : JetAlgebra) :
    repLorentzGroup Λ (jetDeriv μ x) =
      ∑ a, (Lorentz.SL2C.toLorentzGroup Λ).1 a μ • jetDeriv a (repLorentzGroup Λ x) := by
  induction x using SymmetricAlgebra.induction with
  | algebraMap r =>
    have h1 : jetDeriv μ (algebraMap ℝ JetAlgebra r) = 0 := by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, jetDeriv_one, smul_zero]
    rw [h1, map_zero]
    refine (Finset.sum_eq_zero fun a _ => ?_).symm
    rw [Algebra.algebraMap_eq_smul_one, map_smul, repLorentzGroup_apply_one, map_smul,
      jetDeriv_one, smul_zero, smul_zero]
  | ι v =>
    rw [jetDeriv_ι, repLorentzGroup_apply_ι, repLorentzGroup_apply_ι,
      JetComponentSpace.repLorentzGroup_shiftLin, map_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [map_smul, jetDeriv_ι]
  | mul a b ha hb =>
    rw [jetDeriv_mul, map_add, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul, ha, hb,
      Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib, repLorentzGroup_apply_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [jetDeriv_mul, smul_add, smul_mul_assoc, mul_smul_comm]
  | add a b ha hb =>
    rw [map_add, map_add, map_add, ha, hb, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [map_add, smul_add]


set_option maxHeartbeats 1000000 in
/-- **The complexified jet derivative is a Lorentz vector.** -/
lemma complexRepLorentzGroup_baseChange_jetDeriv (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3)
    (p : ℂ ⊗[ℝ] JetAlgebra) :
    complexRepLorentzGroup Λ (LinearMap.baseChange ℂ (jetDeriv μ) p) =
      ∑ a, (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) •
        LinearMap.baseChange ℂ (jetDeriv a) (complexRepLorentzGroup Λ p) := by
  have hrep : ∀ (c : ℂ) (y : JetAlgebra), complexRepLorentzGroup Λ (c ⊗ₜ[ℝ] y) =
      c ⊗ₜ[ℝ] repLorentzGroup Λ y := fun _ _ => rfl
  induction p using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, map_add, map_add, hx, hy, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [map_add, smul_add]
  | tmul c y =>
    rw [LinearMap.baseChange_tmul, hrep, hrep, repLorentzGroup_jetDeriv,
      TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [TensorProduct.tmul_smul, LinearMap.baseChange_tmul,
      ← algebraMap_smul (R := ℝ) ℂ]
    rfl

end JetAlgebra

end BBoson

end StandardModel

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

/-- The covariance of the jet derivative on the bosonic part. -/
lemma repLorentzGroup_jetDeriv_of_mem_bosonic (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3)
    {x : JetAlgebra} (hx : x ∈ bosonic) :
    repLorentzGroup Λ (jetDeriv μ x) =
      ∑ a, (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) •
        jetDeriv a (repLorentzGroup Λ x) := by
  obtain ⟨p, rfl⟩ := mem_bosonic.1 hx
  exact repLorentzGroup_jetDeriv_tmul_one Λ μ p

end JetAlgebra

end LeptonGaugeSector

end
