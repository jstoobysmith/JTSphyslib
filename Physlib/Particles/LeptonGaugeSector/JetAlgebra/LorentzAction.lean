/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.GaugeAction
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
    repLorentzGroup Λ (p ⊗ⱼ l) =
      (BBoson.JetAlgebra.complexRepLorentzGroup Λ p) ⊗ⱼ
        (LeptonSinglet.JetAlgebra.repLorentzGroup Λ l) := rfl

/-- The Lorentz action on the lepton–gauge-sector jet algebra is multiplicative (term-level
  form). -/
lemma repLorentzGroup_apply_mul (Λ : SL(2,ℂ)) (a b : JetAlgebra) :
    repLorentzGroup Λ (a * b) = repLorentzGroup Λ a * repLorentzGroup Λ b := by
  induction a using JetAlgebra.induction_on with
  | zero => simp
  | add u v hu hv => simp only [add_mul, map_add, hu, hv]
  | tmul p l =>
    induction b using JetAlgebra.induction_on with
    | zero => simp
    | add u v hu hv => simp only [mul_add, map_add, hu, hv]
    | tmul q k =>
      simp only [tmul_mul_tmul, repLorentzGroup_tmul,
        BBoson.JetAlgebra.complexRepLorentzGroup_apply_mul,
        LeptonSinglet.JetAlgebra.repLorentzGroup_apply_mul]

lemma repLorentzGroup_apply_one (Λ : SL(2,ℂ)) :
    repLorentzGroup Λ (1 : JetAlgebra) = 1 := by
  rw [one_eq_tmul, repLorentzGroup_tmul,
    BBoson.JetAlgebra.complexRepLorentzGroup_apply_one,
    LeptonSinglet.JetAlgebra.repLorentzGroup_apply_one, ← one_eq_tmul]

/-- The Lorentz action packaged as an algebra homomorphism of the jet algebra. Stating
  results with this rather than the underlying `Algebra.TensorProduct.map` keeps the terms
  small enough for the elaborator. -/
noncomputable def repLorentzGroupAlgHom (Λ : SL(2,ℂ)) : JetAlgebra →ₐ[ℂ] JetAlgebra where
  toFun := repLorentzGroup Λ
  map_add' := LinearMap.map_add _
  map_zero' := LinearMap.map_zero _
  map_one' := repLorentzGroup_apply_one Λ
  map_mul' := repLorentzGroup_apply_mul Λ
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, repLorentzGroup_apply_one,
      ← Algebra.algebraMap_eq_smul_one]


/-- The Lorentz action on the zeroth-order lepton generator: the spinor index
  transforms contragrediently, by the conjugate inverse matrix. -/
lemma repLorentzGroup_ψ (Λ : SL(2,ℂ)) (α : Fin 2) :
    repLorentzGroup Λ [JetGenerators.dψ {} α]ₐ =
      ∑ β, star ((Λ⁻¹).1 α β) • [JetGenerators.dψ {} β]ₐ := by
  rw [show ([JetGenerators.dψ {} α]ₐ : JetAlgebra) =
      (1 : ℂ ⊗[ℝ] BBoson.JetAlgebra) ⊗ⱼ
        LeptonSinglet.JetAlgebra.ofGenerator
          (LeptonSinglet.JetGenerators.dψ {} α) from rfl,
    repLorentzGroup_tmul, BBoson.JetAlgebra.complexRepLorentzGroup_apply_one,
    LeptonSinglet.JetAlgebra.repLorentzGroup_ofGenerator_ψ_nil,
    tmul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [tmul_smul]
  rfl

/-- The Lorentz action on the first-order lepton generator. -/
lemma repLorentzGroup_dψ_singleton (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3)
    (α : Fin 2) :
    repLorentzGroup Λ [JetGenerators.dψ {μ} α]ₐ =
      ∑ ν, ∑ β, ((((Lorentz.SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) *
        star ((Λ⁻¹).1 α β)) • [JetGenerators.dψ {ν} β]ₐ := by
  rw [show ([JetGenerators.dψ {μ} α]ₐ : JetAlgebra) =
      (1 : ℂ ⊗[ℝ] BBoson.JetAlgebra) ⊗ⱼ
        LeptonSinglet.JetAlgebra.ofGenerator
          (LeptonSinglet.JetGenerators.dψ {μ} α) from rfl,
    repLorentzGroup_tmul, BBoson.JetAlgebra.complexRepLorentzGroup_apply_one,
    LeptonSinglet.JetAlgebra.repLorentzGroup_ofGenerator_ψ_singleton,
    tmul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [tmul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [tmul_smul]
  rfl

/-- The Lorentz action on the zeroth-order conjugate lepton generator: the
  spinor index transforms by the inverse matrix. -/
lemma repLorentzGroup_barψ (Λ : SL(2,ℂ)) (α : Fin 2) :
    repLorentzGroup Λ [JetGenerators.dbarψ {} α]ₐ =
      ∑ β, (Λ⁻¹).1 α β • [JetGenerators.dbarψ {} β]ₐ := by
  rw [show ([JetGenerators.dbarψ {} α]ₐ : JetAlgebra) =
      (1 : ℂ ⊗[ℝ] BBoson.JetAlgebra) ⊗ⱼ
        LeptonSinglet.JetAlgebra.ofGenerator
          (LeptonSinglet.JetGenerators.dbarψ {} α) from rfl,
    repLorentzGroup_tmul, BBoson.JetAlgebra.complexRepLorentzGroup_apply_one,
    LeptonSinglet.JetAlgebra.repLorentzGroup_ofGenerator_barψ_nil,
    tmul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [tmul_smul]
  rfl

/-- The Lorentz action on the first-order conjugate lepton generator. -/
lemma repLorentzGroup_dbarψ_singleton (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3)
    (α : Fin 2) :
    repLorentzGroup Λ [JetGenerators.dbarψ {μ} α]ₐ =
      ∑ ν, ∑ β, ((((Lorentz.SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) *
        (Λ⁻¹).1 α β) • [JetGenerators.dbarψ {ν} β]ₐ := by
  rw [show ([JetGenerators.dbarψ {μ} α]ₐ : JetAlgebra) =
      (1 : ℂ ⊗[ℝ] BBoson.JetAlgebra) ⊗ⱼ
        LeptonSinglet.JetAlgebra.ofGenerator
          (LeptonSinglet.JetGenerators.dbarψ {μ} α) from rfl,
    repLorentzGroup_tmul, BBoson.JetAlgebra.complexRepLorentzGroup_apply_one,
    LeptonSinglet.JetAlgebra.repLorentzGroup_ofGenerator_barψ_singleton,
    tmul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [tmul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [tmul_smul]
  rfl

/-- The Lorentz action on the zeroth-order B-boson generator of the lepton–gauge-sector jet
  algebra. -/
lemma repLorentzGroup_B (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) :
    repLorentzGroup Λ [JetGenerators.dB {} μ]ₐ =
      ∑ ν, (((Lorentz.SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) •
        [JetGenerators.dB {} ν]ₐ := by
  have hconv : ∀ (r : ℝ) (X : ℂ ⊗[ℝ] BBoson.JetAlgebra),
      (r • X) ⊗ⱼ (1 : LeptonSinglet.JetAlgebra) = ((r : ℂ)) • (X ⊗ⱼ 1) := by
    intro r X
    rw [← algebraMap_smul (R := ℝ) ℂ r X, ← smul_tmul']
    rfl
  rw [show ([JetGenerators.dB {} μ]ₐ : JetAlgebra) =
      ((1 : ℂ) ⊗ₜ[ℝ] BBoson.JetAlgebra.ofGenerator (BBoson.JetGenerators.dB {} μ))
        ⊗ⱼ (1 : LeptonSinglet.JetAlgebra) from rfl,
    repLorentzGroup_tmul,
    show BBoson.JetAlgebra.complexRepLorentzGroup Λ ((1 : ℂ) ⊗ₜ[ℝ]
        BBoson.JetAlgebra.ofGenerator (BBoson.JetGenerators.dB {} μ)) =
      (1 : ℂ) ⊗ₜ[ℝ] BBoson.JetAlgebra.repLorentzGroup Λ
        (BBoson.JetAlgebra.ofGenerator (BBoson.JetGenerators.dB {} μ)) from rfl,
    BBoson.JetAlgebra.repLorentzGroup_ofGenerator_dB_nil,
    LeptonSinglet.JetAlgebra.repLorentzGroup_apply_one, TensorProduct.tmul_sum,
    sum_tmul]
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
      (r • X) ⊗ⱼ (1 : LeptonSinglet.JetAlgebra) = ((r : ℂ)) • (X ⊗ⱼ 1) := by
    intro r X
    rw [← algebraMap_smul (R := ℝ) ℂ r X, ← smul_tmul']
    rfl
  have happ : repLorentzGroup Λ (((1 : ℂ) ⊗ₜ[ℝ]
      BBoson.JetAlgebra.fieldStrengthDeriv {} μ ν) ⊗ⱼ
        (1 : LeptonSinglet.JetAlgebra)) =
      (BBoson.JetAlgebra.complexRepLorentzGroup Λ ((1 : ℂ) ⊗ₜ[ℝ]
        BBoson.JetAlgebra.fieldStrengthDeriv {} μ ν)) ⊗ⱼ
      (LeptonSinglet.JetAlgebra.repLorentzGroup Λ
        (1 : LeptonSinglet.JetAlgebra)) := rfl
  rw [fieldStrengthDeriv, happ,
    BBoson.JetAlgebra.complexRepLorentzGroup_one_tmul_fieldStrengthDeriv_nil,
    LeptonSinglet.JetAlgebra.repLorentzGroup_apply_one]
  simp only [sum_tmul, hconv, fieldStrengthDeriv]

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
      (r • X) ⊗ⱼ (1 : LeptonSinglet.JetAlgebra) = ((r : ℂ)) • (X ⊗ⱼ 1) := by
    intro r X
    rw [← algebraMap_smul (R := ℝ) ℂ r X, ← smul_tmul']
    rfl
  have happ : repLorentzGroup Λ (((1 : ℂ) ⊗ₜ[ℝ]
      BBoson.JetAlgebra.fieldStrengthDeriv {ρ} μ ν) ⊗ⱼ
        (1 : LeptonSinglet.JetAlgebra)) =
      (BBoson.JetAlgebra.complexRepLorentzGroup Λ ((1 : ℂ) ⊗ₜ[ℝ]
        BBoson.JetAlgebra.fieldStrengthDeriv {ρ} μ ν)) ⊗ⱼ
      (LeptonSinglet.JetAlgebra.repLorentzGroup Λ
        (1 : LeptonSinglet.JetAlgebra)) := rfl
  rw [fieldStrengthDeriv, happ,
    BBoson.JetAlgebra.complexRepLorentzGroup_one_tmul_fieldStrengthDeriv_singleton,
    LeptonSinglet.JetAlgebra.repLorentzGroup_apply_one]
  simp only [sum_tmul, hconv, fieldStrengthDeriv]

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
      (r • X) ⊗ⱼ (1 : LeptonSinglet.JetAlgebra) = ((r : ℂ)) • (X ⊗ⱼ 1) := by
    intro r X
    rw [← algebraMap_smul (R := ℝ) ℂ r X, ← smul_tmul']
    rfl
  have happ : repLorentzGroup Λ (((1 : ℂ) ⊗ₜ[ℝ]
      BBoson.JetAlgebra.fieldStrengthDeriv {ρ, τ} μ ν) ⊗ⱼ
        (1 : LeptonSinglet.JetAlgebra)) =
      (BBoson.JetAlgebra.complexRepLorentzGroup Λ ((1 : ℂ) ⊗ₜ[ℝ]
        BBoson.JetAlgebra.fieldStrengthDeriv {ρ, τ} μ ν)) ⊗ⱼ
      (LeptonSinglet.JetAlgebra.repLorentzGroup Λ
        (1 : LeptonSinglet.JetAlgebra)) := rfl
  rw [fieldStrengthDeriv, happ,
    BBoson.JetAlgebra.complexRepLorentzGroup_one_tmul_fieldStrengthDeriv_pair,
    LeptonSinglet.JetAlgebra.repLorentzGroup_apply_one]
  simp only [sum_tmul, hconv, fieldStrengthDeriv]

/-!

### The transformation law of a zero-derivative fermion pair

-/

set_option maxHeartbeats 2000000 in
/-- The Lorentz action on a fermion pair `ψ̄_α (Dψ_μ)_β` with one derivative on
  the unbarred factor. -/
lemma repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (Λ : SL(2,ℂ))
    (μ : Fin 1 ⊕ Fin 3) (α β : Fin 2) :
    repLorentzGroup Λ (Dbarψ [] α * Dψ [μ] β) =
      ∑ γ, ∑ ν, ∑ δ, ((Λ⁻¹).1 α γ *
        ((((Lorentz.SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) *
          star ((Λ⁻¹).1 β δ))) • (Dbarψ [] γ * Dψ [ν] δ) := by
  have hsm : ∀ (f : Fin 2 → JetAlgebra) (y : JetAlgebra),
      (∑ x, f x) * y = ∑ x, f x * y := fun f y => by
    rw [show (∑ x, f x) * y = LinearMap.mulRight ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hms : ∀ (f : (Fin 1 ⊕ Fin 3) → JetAlgebra) (y : JetAlgebra),
      y * (∑ x, f x) = ∑ x, y * f x := fun f y => by
    rw [show y * (∑ x, f x) = LinearMap.mulLeft ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hms₂ : ∀ (f : Fin 2 → JetAlgebra) (y : JetAlgebra),
      y * (∑ x, f x) = ∑ x, y * f x := fun f y => by
    rw [show y * (∑ x, f x) = LinearMap.mulLeft ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hsmul : ∀ (c d : ℂ) (x y : JetAlgebra),
      (c • x) * (d • y) = (c * d) • (x * y) := fun c d x y => by
    rw [smul_mul_smul_comm]
  rw [repLorentzGroup_apply_mul, repLorentzGroup_Dbarψ_nil, repLorentzGroup_Dψ_singleton]
  simp only [hsm, hms, hms₂, hsmul]

set_option maxHeartbeats 2000000 in
/-- The Lorentz action on a fermion pair `(D̄ψ̄_μ)_α ψ_β` with one derivative on
  the barred factor. -/
lemma repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (Λ : SL(2,ℂ))
    (μ : Fin 1 ⊕ Fin 3) (α β : Fin 2) :
    repLorentzGroup Λ (Dbarψ [μ] α * Dψ [] β) =
      ∑ ν, ∑ γ, ∑ δ, (((((Lorentz.SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) *
        (Λ⁻¹).1 α γ) * star ((Λ⁻¹).1 β δ)) • (Dbarψ [ν] γ * Dψ [] δ) := by
  have hsm : ∀ (f : (Fin 1 ⊕ Fin 3) → JetAlgebra) (y : JetAlgebra),
      (∑ x, f x) * y = ∑ x, f x * y := fun f y => by
    rw [show (∑ x, f x) * y = LinearMap.mulRight ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hsm₂ : ∀ (f : Fin 2 → JetAlgebra) (y : JetAlgebra),
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
  rw [repLorentzGroup_apply_mul, repLorentzGroup_Dbarψ_singleton, repLorentzGroup_Dψ_nil]
  simp only [hsm, hsm₂, hms, hsmul]


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
end JetAlgebra

end LeptonGaugeSector
