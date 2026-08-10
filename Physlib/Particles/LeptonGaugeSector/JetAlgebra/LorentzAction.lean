/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.DerivativeOrder
public import Physlib.Relativity.MinkowskiMatrix
public import Physlib.Relativity.PauliMatrices.Basic
/-!
# THe Lorentz group action on the lepton–gauge-sector jet algebra
-/

@[expose] public section

namespace LeptonGaugeSector
open TensorProduct StandardModel

namespace JetAlgebra

/-!

### B.1. The action of the Lorentz group

-/
open Matrix MatrixGroups

noncomputable def repLorentzGroup : Representation ℂ (SL(2,ℂ)) JetAlgebra :=
  BBoson.JetAlgebra.complexRepLorentzGroup.tprod LeptonSinglet.JetAlgebra.repLorentzGroup

/-- The Lorentz action on a pure tensor. -/
lemma repLorentzGroup_tmul (Λ : SL(2,ℂ)) (p : ℂ ⊗[ℝ] BBoson.JetAlgebra)
    (l : LeptonSinglet.JetAlgebra) :
    repLorentzGroup Λ (p ⊗ₜ[ℂ] l) =
      (BBoson.JetAlgebra.complexRepLorentzGroup Λ p) ⊗ₜ[ℂ]
        (LeptonSinglet.JetAlgebra.repLorentzGroup Λ l) := rfl

/-- The Lorentz action on the lepton–gauge-sector jet algebra agrees with the algebra
  homomorphism obtained as the tensor product of the complexified B-boson
  action with the exterior-algebra action on the charged-lepton factor. -/
lemma repLorentzGroup_eq_algHom (Λ : SL(2,ℂ)) (x : JetAlgebra) :
    repLorentzGroup Λ x = Algebra.TensorProduct.map
        (BBoson.JetAlgebra.complexRepLorentzGroupAlgHom Λ)
        (LeptonSinglet.JetAlgebra.repLorentzGroupAlgHom Λ) x := rfl

/-- The Lorentz action on the lepton–gauge-sector jet algebra is multiplicative (term-level
  form). -/
lemma repLorentzGroup_apply_mul (Λ : SL(2,ℂ)) (a b : JetAlgebra) :
    repLorentzGroup Λ (a * b) = repLorentzGroup Λ a * repLorentzGroup Λ b := by
  simp [repLorentzGroup_eq_algHom]

lemma repLorentzGroup_apply_one (Λ : SL(2,ℂ)) :
    repLorentzGroup Λ (1 : JetAlgebra) = 1 := by
  simp [repLorentzGroup_eq_algHom]

/-- The Lorentz action on the zeroth-order lepton generator: the spinor index
  transforms contragrediently, by the conjugate inverse matrix. -/
lemma repLorentzGroup_ψ (Λ : SL(2,ℂ)) (α : Fin 2) :
    repLorentzGroup Λ [JetGenerators.dψ {} α]ₐ =
      ∑ β, star ((Λ⁻¹).1 α β) • [JetGenerators.dψ {} β]ₐ := by
  rw [show ([JetGenerators.dψ {} α]ₐ : JetAlgebra) =
      (1 : ℂ ⊗[ℝ] BBoson.JetAlgebra) ⊗ₜ[ℂ]
        LeptonSinglet.JetAlgebra.ofGenerator
          (LeptonSinglet.JetGenerators.dψ {} α) from rfl,
    repLorentzGroup_tmul, BBoson.JetAlgebra.complexRepLorentzGroup_apply_one,
    LeptonSinglet.JetAlgebra.repLorentzGroup_ofGenerator_ψ_nil,
    TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [TensorProduct.tmul_smul]
  rfl

/-- The Lorentz action on the first-order lepton generator. -/
lemma repLorentzGroup_dψ_singleton (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3)
    (α : Fin 2) :
    repLorentzGroup Λ [JetGenerators.dψ {μ} α]ₐ =
      ∑ ν, ∑ β, ((((Lorentz.SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) *
        star ((Λ⁻¹).1 α β)) • [JetGenerators.dψ {ν} β]ₐ := by
  rw [show ([JetGenerators.dψ {μ} α]ₐ : JetAlgebra) =
      (1 : ℂ ⊗[ℝ] BBoson.JetAlgebra) ⊗ₜ[ℂ]
        LeptonSinglet.JetAlgebra.ofGenerator
          (LeptonSinglet.JetGenerators.dψ {μ} α) from rfl,
    repLorentzGroup_tmul, BBoson.JetAlgebra.complexRepLorentzGroup_apply_one,
    LeptonSinglet.JetAlgebra.repLorentzGroup_ofGenerator_ψ_singleton,
    TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [TensorProduct.tmul_smul]
  rfl

/-- The Lorentz action on the zeroth-order conjugate lepton generator: the
  spinor index transforms by the inverse matrix. -/
lemma repLorentzGroup_barψ (Λ : SL(2,ℂ)) (α : Fin 2) :
    repLorentzGroup Λ [JetGenerators.dbarψ {} α]ₐ =
      ∑ β, (Λ⁻¹).1 α β • [JetGenerators.dbarψ {} β]ₐ := by
  rw [show ([JetGenerators.dbarψ {} α]ₐ : JetAlgebra) =
      (1 : ℂ ⊗[ℝ] BBoson.JetAlgebra) ⊗ₜ[ℂ]
        LeptonSinglet.JetAlgebra.ofGenerator
          (LeptonSinglet.JetGenerators.dbarψ {} α) from rfl,
    repLorentzGroup_tmul, BBoson.JetAlgebra.complexRepLorentzGroup_apply_one,
    LeptonSinglet.JetAlgebra.repLorentzGroup_ofGenerator_barψ_nil,
    TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [TensorProduct.tmul_smul]
  rfl

/-- The Lorentz action on the first-order conjugate lepton generator. -/
lemma repLorentzGroup_dbarψ_singleton (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3)
    (α : Fin 2) :
    repLorentzGroup Λ [JetGenerators.dbarψ {μ} α]ₐ =
      ∑ ν, ∑ β, ((((Lorentz.SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) *
        (Λ⁻¹).1 α β) • [JetGenerators.dbarψ {ν} β]ₐ := by
  rw [show ([JetGenerators.dbarψ {μ} α]ₐ : JetAlgebra) =
      (1 : ℂ ⊗[ℝ] BBoson.JetAlgebra) ⊗ₜ[ℂ]
        LeptonSinglet.JetAlgebra.ofGenerator
          (LeptonSinglet.JetGenerators.dbarψ {μ} α) from rfl,
    repLorentzGroup_tmul, BBoson.JetAlgebra.complexRepLorentzGroup_apply_one,
    LeptonSinglet.JetAlgebra.repLorentzGroup_ofGenerator_barψ_singleton,
    TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [TensorProduct.tmul_smul]
  rfl

/-- The Lorentz action on the zeroth-order B-boson generator of the lepton–gauge-sector jet
  algebra. -/
lemma repLorentzGroup_B (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) :
    repLorentzGroup Λ [JetGenerators.dB {} μ]ₐ =
      ∑ ν, (((Lorentz.SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) •
        [JetGenerators.dB {} ν]ₐ := by
  have hconv : ∀ (r : ℝ) (X : ℂ ⊗[ℝ] BBoson.JetAlgebra),
      (r • X) ⊗ₜ[ℂ] (1 : LeptonSinglet.JetAlgebra) = ((r : ℂ)) • (X ⊗ₜ[ℂ] 1) := by
    intro r X
    rw [← algebraMap_smul (R := ℝ) ℂ r X, ← TensorProduct.smul_tmul']
    rfl
  rw [show ([JetGenerators.dB {} μ]ₐ : JetAlgebra) =
      ((1 : ℂ) ⊗ₜ[ℝ] BBoson.JetAlgebra.ofGenerator (BBoson.JetGenerators.dB {} μ))
        ⊗ₜ[ℂ] (1 : LeptonSinglet.JetAlgebra) from rfl,
    repLorentzGroup_tmul,
    show BBoson.JetAlgebra.complexRepLorentzGroup Λ ((1 : ℂ) ⊗ₜ[ℝ]
        BBoson.JetAlgebra.ofGenerator (BBoson.JetGenerators.dB {} μ)) =
      (1 : ℂ) ⊗ₜ[ℝ] BBoson.JetAlgebra.repLorentzGroup Λ
        (BBoson.JetAlgebra.ofGenerator (BBoson.JetGenerators.dB {} μ)) from rfl,
    BBoson.JetAlgebra.repLorentzGroup_ofGenerator_dB_nil,
    LeptonSinglet.JetAlgebra.repLorentzGroup_apply_one, TensorProduct.tmul_sum,
    TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [TensorProduct.tmul_smul, hconv]
  rfl


/-- The transformation law of the embedded field strength: an antisymmetric
  two-tensor with both indices transforming by the Lorentz matrix. -/
lemma repLorentzGroup_fieldStrengthDeriv_nil (Λ : SL(2,ℂ)) (μ ν : Fin 1 ⊕ Fin 3) :
    repLorentzGroup Λ (fieldStrengthDeriv {} μ ν) =
      ∑ a, ∑ b, (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ *
        (Lorentz.SL2C.toLorentzGroup Λ).1 b ν : ℝ) : ℂ) •
        fieldStrengthDeriv {} a b := by
  have hconv : ∀ (r : ℝ) (X : ℂ ⊗[ℝ] BBoson.JetAlgebra),
      (r • X) ⊗ₜ[ℂ] (1 : LeptonSinglet.JetAlgebra) = ((r : ℂ)) • (X ⊗ₜ[ℂ] 1) := by
    intro r X
    rw [← algebraMap_smul (R := ℝ) ℂ r X, ← TensorProduct.smul_tmul']
    rfl
  have happ : repLorentzGroup Λ (((1 : ℂ) ⊗ₜ[ℝ]
      BBoson.JetAlgebra.fieldStrengthDeriv {} μ ν) ⊗ₜ[ℂ]
        (1 : LeptonSinglet.JetAlgebra)) =
      (BBoson.JetAlgebra.complexRepLorentzGroup Λ ((1 : ℂ) ⊗ₜ[ℝ]
        BBoson.JetAlgebra.fieldStrengthDeriv {} μ ν)) ⊗ₜ[ℂ]
      (LeptonSinglet.JetAlgebra.repLorentzGroup Λ
        (1 : LeptonSinglet.JetAlgebra)) := rfl
  rw [fieldStrengthDeriv, happ,
    BBoson.JetAlgebra.complexRepLorentzGroup_one_tmul_fieldStrengthDeriv_nil,
    LeptonSinglet.JetAlgebra.repLorentzGroup_apply_one]
  simp only [TensorProduct.sum_tmul, hconv, fieldStrengthDeriv]

/-- Covariance of the zeroth covariant derivatives under the Lorentz group. -/
lemma repLorentzGroup_Dψ_nil (Λ : SL(2,ℂ)) (α : Fin 2) :
    repLorentzGroup Λ (Dψ [] α) = ∑ β, star ((Λ⁻¹).1 α β) • Dψ [] β := by
  rw [Dψ_nil, repLorentzGroup_ψ]
  simp only [Dψ_nil]

lemma repLorentzGroup_Dbarψ_nil (Λ : SL(2,ℂ)) (α : Fin 2) :
    repLorentzGroup Λ (Dbarψ [] α) = ∑ β, (Λ⁻¹).1 α β • Dbarψ [] β := by
  rw [Dbarψ_nil, repLorentzGroup_barψ]
  simp only [Dbarψ_nil]

/-- Multiplication distributes over a finite sum on the left. Stated through
  `LinearMap.mulRight` because the generic `Finset.sum_mul` does not match the
  multiplication instance of the tensor-product algebra. -/
lemma sum_mul' {ι : Type*} [Fintype ι] (f : ι → JetAlgebra) (y : JetAlgebra) :
    (∑ i, f i) * y = ∑ i, f i * y := by
  rw [show (∑ i, f i) * y = LinearMap.mulRight ℂ y (∑ i, f i) from rfl, map_sum]
  rfl

/-- Multiplication distributes over a finite sum on the right; see `sum_mul'`. -/
lemma mul_sum' {ι : Type*} [Fintype ι] (y : JetAlgebra) (f : ι → JetAlgebra) :
    y * (∑ i, f i) = ∑ i, y * f i := by
  rw [show y * (∑ i, f i) = LinearMap.mulLeft ℂ y (∑ i, f i) from rfl, map_sum]
  rfl

/-- Bilinearity of the product against two scaled finite sums: the form in which
  the gauge-field term of a covariant derivative is expanded after the Lorentz
  action has been distributed over each factor. -/
lemma smul_sum_mul_sum {ι κ : Type*} [Fintype ι] [Fintype κ] (c : ℂ)
    (f : ι → ℂ) (g : κ → ℂ) (x : ι → JetAlgebra) (y : κ → JetAlgebra) :
    c • ((∑ i, f i • x i) * (∑ j, g j • y j)) =
      ∑ i, ∑ j, (f i * g j * c) • (x i * y j) := by
  rw [sum_mul']
  simp only [mul_sum', smul_mul_smul_comm, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  ring

/-- Covariance of the first covariant derivative under the Lorentz group: the
  gauge-field term transforms exactly as the derivative term. -/
lemma repLorentzGroup_Dψ_singleton (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3)
    (α : Fin 2) :
    repLorentzGroup Λ (Dψ [μ] α) =
      ∑ ν, ∑ β, ((((Lorentz.SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) *
        star ((Λ⁻¹).1 α β)) • Dψ [ν] β := by
  simp only [Dψ_singleton, map_sub, map_smul, repLorentzGroup_apply_mul,
    repLorentzGroup_B, repLorentzGroup_ψ, repLorentzGroup_dψ_singleton,
    smul_sub, Finset.sum_sub_distrib, smul_smul, smul_sum_mul_sum]

/-- Covariance of the first conjugate covariant derivative under the Lorentz
  group. -/
lemma repLorentzGroup_Dbarψ_singleton (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3)
    (α : Fin 2) :
    repLorentzGroup Λ (Dbarψ [μ] α) =
      ∑ ν, ∑ β, ((((Lorentz.SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) *
        (Λ⁻¹).1 α β) • Dbarψ [ν] β := by
  simp only [Dbarψ_singleton, map_add, map_smul, repLorentzGroup_apply_mul,
    repLorentzGroup_B, repLorentzGroup_barψ, repLorentzGroup_dbarψ_singleton,
    smul_add, Finset.sum_add_distrib, smul_smul, smul_sum_mul_sum]

/-!

### The transformation law of the field strengths

The embedded field-strength derivatives are tensors: every index, the
derivative indices included, transforms by the Lorentz matrix. For a
*diagonal* Lorentz matrix this collapses to a scaling by the product of the
signs carried by the indices, which is what the parity and boost arguments of
`Invariants/` use.

-/

/-- Under a diagonal Lorentz transformation the field strength scales by the
  product of the signs of its two indices. -/
lemma repLorentzGroup_diag_fieldStrengthDeriv {M : SL(2,ℂ)}
    {sgn : Fin 1 ⊕ Fin 3 → ℝ}
    (hM : ∀ a b, (Lorentz.SL2C.toLorentzGroup M).1 a b =
      if a = b then sgn a else 0) (μ ν : Fin 1 ⊕ Fin 3) :
    repLorentzGroup M (fieldStrengthDeriv {} μ ν) =
      ((sgn μ * sgn ν : ℝ) : ℂ) • fieldStrengthDeriv {} μ ν := by
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  rw [Finset.sum_eq_single μ (fun a _ ha => Finset.sum_eq_zero fun b _ => by
      rw [hM a μ, if_neg ha, zero_mul, Complex.ofReal_zero, zero_smul])
    (fun h => absurd (Finset.mem_univ μ) h)]
  rw [Finset.sum_eq_single ν (fun b _ hb => by
      rw [hM b ν, if_neg hb, mul_zero, Complex.ofReal_zero, zero_smul])
    (fun h => absurd (Finset.mem_univ ν) h)]
  rw [hM μ μ, if_pos rfl, hM ν ν, if_pos rfl]

/-- The transformation law of the embedded first-derivative field strength:
  a three-index tensor, all indices transforming by the Lorentz matrix. -/
lemma repLorentzGroup_fieldStrengthDeriv_singleton (Λ : SL(2,ℂ))
    (ρ μ ν : Fin 1 ⊕ Fin 3) :
    repLorentzGroup Λ (fieldStrengthDeriv {ρ} μ ν) =
      ∑ r, ∑ a, ∑ b, ((((Lorentz.SL2C.toLorentzGroup Λ).1 r ρ *
        ((Lorentz.SL2C.toLorentzGroup Λ).1 a μ *
          (Lorentz.SL2C.toLorentzGroup Λ).1 b ν) : ℝ)) : ℂ) •
        fieldStrengthDeriv {r} a b := by
  have hconv : ∀ (r : ℝ) (X : ℂ ⊗[ℝ] BBoson.JetAlgebra),
      (r • X) ⊗ₜ[ℂ] (1 : LeptonSinglet.JetAlgebra) = ((r : ℂ)) • (X ⊗ₜ[ℂ] 1) := by
    intro r X
    rw [← algebraMap_smul (R := ℝ) ℂ r X, ← TensorProduct.smul_tmul']
    rfl
  have happ : repLorentzGroup Λ (((1 : ℂ) ⊗ₜ[ℝ]
      BBoson.JetAlgebra.fieldStrengthDeriv {ρ} μ ν) ⊗ₜ[ℂ]
        (1 : LeptonSinglet.JetAlgebra)) =
      (BBoson.JetAlgebra.complexRepLorentzGroup Λ ((1 : ℂ) ⊗ₜ[ℝ]
        BBoson.JetAlgebra.fieldStrengthDeriv {ρ} μ ν)) ⊗ₜ[ℂ]
      (LeptonSinglet.JetAlgebra.repLorentzGroup Λ
        (1 : LeptonSinglet.JetAlgebra)) := rfl
  rw [fieldStrengthDeriv, happ,
    BBoson.JetAlgebra.complexRepLorentzGroup_one_tmul_fieldStrengthDeriv_singleton,
    LeptonSinglet.JetAlgebra.repLorentzGroup_apply_one]
  simp only [TensorProduct.sum_tmul, hconv, fieldStrengthDeriv]

/-- Under a diagonal Lorentz transformation the derivative field strength
  scales by the product of the signs of its three indices. -/
lemma repLorentzGroup_diag_fieldStrengthDeriv_singleton {M : SL(2,ℂ)}
    {sgn : Fin 1 ⊕ Fin 3 → ℝ}
    (hM : ∀ a b, (Lorentz.SL2C.toLorentzGroup M).1 a b =
      if a = b then sgn a else 0) (ρ μ ν : Fin 1 ⊕ Fin 3) :
    repLorentzGroup M (fieldStrengthDeriv {ρ} μ ν) =
      ((sgn ρ * (sgn μ * sgn ν) : ℝ) : ℂ) • fieldStrengthDeriv {ρ} μ ν := by
  rw [repLorentzGroup_fieldStrengthDeriv_singleton]
  rw [Finset.sum_eq_single ρ (fun r _ hr => Finset.sum_eq_zero fun a _ =>
      Finset.sum_eq_zero fun b _ => by
        rw [hM r ρ, if_neg hr, zero_mul, Complex.ofReal_zero, zero_smul])
    (fun h => absurd (Finset.mem_univ ρ) h)]
  rw [Finset.sum_eq_single μ (fun a _ ha => Finset.sum_eq_zero fun b _ => by
      rw [hM a μ, if_neg ha, zero_mul, mul_zero, Complex.ofReal_zero, zero_smul])
    (fun h => absurd (Finset.mem_univ μ) h)]
  rw [Finset.sum_eq_single ν (fun b _ hb => by
      rw [hM b ν, if_neg hb, mul_zero, mul_zero, Complex.ofReal_zero, zero_smul])
    (fun h => absurd (Finset.mem_univ ν) h)]
  rw [hM ρ ρ, if_pos rfl, hM μ μ, if_pos rfl, hM ν ν, if_pos rfl]

set_option maxHeartbeats 2000000 in
/-- The transformation law of the embedded second-derivative field strength:
  a four-index tensor, all indices transforming by the Lorentz matrix. -/
lemma repLorentzGroup_fieldStrengthDeriv_pair (Λ : SL(2,ℂ))
    (ρ τ μ ν : Fin 1 ⊕ Fin 3) :
    repLorentzGroup Λ (fieldStrengthDeriv {ρ, τ} μ ν) =
      ∑ r, ∑ s, ∑ a, ∑ b, ((((Lorentz.SL2C.toLorentzGroup Λ).1 r ρ *
        ((Lorentz.SL2C.toLorentzGroup Λ).1 s τ *
          ((Lorentz.SL2C.toLorentzGroup Λ).1 a μ *
          (Lorentz.SL2C.toLorentzGroup Λ).1 b ν)) : ℝ)) : ℂ) •
        fieldStrengthDeriv {r, s} a b := by
  have hconv : ∀ (r : ℝ) (X : ℂ ⊗[ℝ] BBoson.JetAlgebra),
      (r • X) ⊗ₜ[ℂ] (1 : LeptonSinglet.JetAlgebra) = ((r : ℂ)) • (X ⊗ₜ[ℂ] 1) := by
    intro r X
    rw [← algebraMap_smul (R := ℝ) ℂ r X, ← TensorProduct.smul_tmul']
    rfl
  have happ : repLorentzGroup Λ (((1 : ℂ) ⊗ₜ[ℝ]
      BBoson.JetAlgebra.fieldStrengthDeriv {ρ, τ} μ ν) ⊗ₜ[ℂ]
        (1 : LeptonSinglet.JetAlgebra)) =
      (BBoson.JetAlgebra.complexRepLorentzGroup Λ ((1 : ℂ) ⊗ₜ[ℝ]
        BBoson.JetAlgebra.fieldStrengthDeriv {ρ, τ} μ ν)) ⊗ₜ[ℂ]
      (LeptonSinglet.JetAlgebra.repLorentzGroup Λ
        (1 : LeptonSinglet.JetAlgebra)) := rfl
  rw [fieldStrengthDeriv, happ,
    BBoson.JetAlgebra.complexRepLorentzGroup_one_tmul_fieldStrengthDeriv_pair,
    LeptonSinglet.JetAlgebra.repLorentzGroup_apply_one]
  simp only [TensorProduct.sum_tmul, hconv, fieldStrengthDeriv]

/-!

### The transformation law of a zero-derivative fermion pair

-/

set_option maxHeartbeats 1000000 in
/-- The Lorentz action on a zero-derivative fermion pair `ψ̄_α ψ_β`. -/
lemma repLorentzGroup_Dbarψ_nil_mul_Dψ_nil (Λ : SL(2,ℂ)) (α β : Fin 2) :
    repLorentzGroup Λ (Dbarψ [] α * Dψ [] β) =
      ∑ γ, ∑ δ, ((Λ⁻¹).1 α γ * star ((Λ⁻¹).1 β δ)) •
        (Dbarψ [] γ * Dψ [] δ) := by
  have hsm : ∀ (f : Fin 2 → JetAlgebra) (y : JetAlgebra),
      (∑ x, f x) * y = ∑ x, f x * y := fun f y => by
    rw [show (∑ x, f x) * y = LinearMap.mulRight ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hms : ∀ (f : Fin 2 → JetAlgebra) (y : JetAlgebra),
      y * (∑ x, f x) = ∑ x, y * f x := fun f y => by
    rw [show y * (∑ x, f x) = LinearMap.mulLeft ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hsmul : ∀ (c d : ℂ) (x y : JetAlgebra),
      (c • x) * (d • y) = (c * d) • (x * y) := fun c d x y => by
    rw [smul_mul_smul_comm]
  rw [repLorentzGroup_apply_mul, repLorentzGroup_Dbarψ_nil, repLorentzGroup_Dψ_nil]
  simp only [hsm, hms, hsmul]

set_option maxHeartbeats 1000000 in
/-- The Lorentz action on a zero-derivative fermion pair `ψ_α ψ̄_β`. -/
lemma repLorentzGroup_Dψ_nil_mul_Dbarψ_nil (Λ : SL(2,ℂ)) (α β : Fin 2) :
    repLorentzGroup Λ (Dψ [] α * Dbarψ [] β) =
      ∑ γ, ∑ δ, (star ((Λ⁻¹).1 α γ) * (Λ⁻¹).1 β δ) •
        (Dψ [] γ * Dbarψ [] δ) := by
  have hsm : ∀ (f : Fin 2 → JetAlgebra) (y : JetAlgebra),
      (∑ x, f x) * y = ∑ x, f x * y := fun f y => by
    rw [show (∑ x, f x) * y = LinearMap.mulRight ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hms : ∀ (f : Fin 2 → JetAlgebra) (y : JetAlgebra),
      y * (∑ x, f x) = ∑ x, y * f x := fun f y => by
    rw [show y * (∑ x, f x) = LinearMap.mulLeft ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hsmul : ∀ (c d : ℂ) (x y : JetAlgebra),
      (c • x) * (d • y) = (c * d) • (x * y) := fun c d x y => by
    rw [smul_mul_smul_comm]
  rw [repLorentzGroup_apply_mul, repLorentzGroup_Dψ_nil, repLorentzGroup_Dbarψ_nil]
  simp only [hsm, hms, hsmul]

/-!

### B.2. The invarance condition

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


/-- Characterization of the invariants of the lepton–gauge-sector jet algebra: an element is
  invariant under the jet gauge group and the Lorentz group precisely when it
  lies in the algebra generated by the field-strength derivatives and the
  covariant derivatives, is invariant under the constant gauge transformations,
  and is Lorentz invariant. The forward direction is the main theorem above; the
  backward direction holds because on the covariant generators a jet of gauge
  transformations acts only through its value at the base point. -/
lemma isInvariant_iff_mem_adjoin_invariantGenerators (x : JetAlgebra) :
    IsInvariant x ↔ x ∈ Algebra.adjoin ℂ invariantGenerators ∧
    (∀ g : GaugeGroupI, repJetGaugeGroupI (.ofConstant g) x = x)
    ∧ (∀ Λ : SL(2, ℂ), repLorentzGroup Λ x = x) := by
  constructor
  · intro h
    exact ⟨mem_adjoin_invariantGenerators_of_forall_repJetGaugeGroupI_eq x h.1,
      fun g => h.1 _, h.2⟩
  · rintro ⟨hmem, hconst, hlor⟩
    refine ⟨fun U => ?_, hlor⟩
    suffices hkey : repJetGaugeGroupI U x =
        repJetGaugeGroupI (JetGaugeGroupI.ofConstant U.eval) x by
      rw [hkey]
      exact hconst U.eval
    clear hconst hlor
    induction hmem using Algebra.adjoin_induction with
    | mem z hz =>
      rcases hz with (⟨p, rfl⟩ | ⟨p, rfl⟩) | ⟨p, rfl⟩
      · show repJetGaugeGroupI U (fieldStrengthDeriv p.1 p.2.1 p.2.2) =
          repJetGaugeGroupI (JetGaugeGroupI.ofConstant U.eval)
            (fieldStrengthDeriv p.1 p.2.1 p.2.2)
        rw [repJetGaugeGroupI_fieldStrengthDeriv, repJetGaugeGroupI_fieldStrengthDeriv]
      · show repJetGaugeGroupI U (Dψ p.1 p.2) =
          repJetGaugeGroupI (JetGaugeGroupI.ofConstant U.eval) (Dψ p.1 p.2)
        rw [repJetGaugeGroupI_Dψ, repJetGaugeGroupI_Dψ, JetGaugeGroupI.eval_ofConstant]
      · show repJetGaugeGroupI U (Dbarψ p.1 p.2) =
          repJetGaugeGroupI (JetGaugeGroupI.ofConstant U.eval) (Dbarψ p.1 p.2)
        rw [repJetGaugeGroupI_Dbarψ, repJetGaugeGroupI_Dbarψ,
          JetGaugeGroupI.eval_ofConstant]
    | algebraMap r =>
      simp only [repJetGaugeGroupI_eq_algHom, AlgHom.commutes]
    | add u v hu hv ihu ihv =>
      exact (map_add (repJetGaugeGroupI U) u v).trans
        ((congrArg₂ (· + ·) ihu ihv).trans
          (map_add (repJetGaugeGroupI (JetGaugeGroupI.ofConstant U.eval)) u v).symm)
    | mul u v hu hv ihu ihv =>
      exact (repJetGaugeGroupI_apply_mul U u v).trans
        ((congrArg₂ (· * ·) ihu ihv).trans
          (repJetGaugeGroupI_apply_mul (JetGaugeGroupI.ofConstant U.eval) u v).symm)

end JetAlgebra

end LeptonGaugeSector
