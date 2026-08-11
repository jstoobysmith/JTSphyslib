/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.CovariantDeriv
public import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating
/-!
# Linear independence of the fermion bilinears

The sixteen products `ψ̄_α D_μ ψ_β` are linearly independent. Statements about
an explicit span of such products — the boost-weight-zero part of the fermion
kinetic sector, say — then reduce to linear algebra on coefficients, with no
need for a grading certificate.

The proof exhibits a dual family. The lepton factor of the jet algebra is an
exterior algebra, so a pair of dual basis vectors `φ`, `ψ` on the jet component
space gives an alternating two-form `φ ⊗ ψ - ψ ⊗ φ`, and
`ExteriorAlgebra.liftAlternating` turns it into a functional picking out the
coefficient of `ι x * ι y`. Tensoring with the augmentation of the B-boson
factor gives a functional `fermionPairDual` on the whole jet algebra, and
`fermionPairDual_Dbarψ_mul_Dψ` shows it is dual to the sixteen bilinears: the
`- 6 i B_μ ψ_β` tail of `D_μ ψ_β` contributes nothing, because its fermionic
part carries no derivative index.

## Key results

- `fermionPairDual` : the functional dual to a chosen fermion bilinear.
- `Dbarψ_mul_Dψ_linearIndependent` : the sixteen bilinears are independent.

-/

@[expose] public section

namespace LeptonGaugeSector
open TensorProduct StandardModel

namespace JetAlgebra

/-!

## A. An alternating two-form from a pair of functionals

-/

/-- The alternating two-form `φ ∧ ψ` built from a pair of linear functionals. -/
noncomputable def altPair {V : Type} [AddCommGroup V] [Module ℂ V]
    (φ ψ : Module.Dual ℂ V) : V [⋀^Fin 2]→ₗ[ℂ] ℂ where
  toFun v := φ (v 0) * ψ (v 1) - φ (v 1) * ψ (v 0)
  map_update_add' v i x y := by fin_cases i <;> simp <;> ring
  map_update_smul' v i c x := by fin_cases i <;> simp <;> ring
  map_eq_zero_of_eq' v i j h hij := by
    fin_cases i <;> fin_cases j <;> simp_all

@[simp]
lemma altPair_apply {V : Type} [AddCommGroup V] [Module ℂ V]
    (φ ψ : Module.Dual ℂ V) (x y : V) :
    altPair φ ψ ![x, y] = φ x * ψ y - φ y * ψ x := rfl

/-- The family of alternating forms that is `altPair φ ψ` in degree two and zero
  elsewhere; the input to `ExteriorAlgebra.liftAlternating`. -/
noncomputable def altPairFamily {V : Type} [AddCommGroup V] [Module ℂ V]
    (φ ψ : Module.Dual ℂ V) : (i : ℕ) → V [⋀^Fin i]→ₗ[ℂ] ℂ
  | 2 => altPair φ ψ
  | _ => 0

/-- The functional on an exterior algebra picking out the coefficient of the
  degree-two monomial dual to `φ` and `ψ`. -/
noncomputable def extPairDual {V : Type} [AddCommGroup V] [Module ℂ V]
    (φ ψ : Module.Dual ℂ V) : ExteriorAlgebra ℂ V →ₗ[ℂ] ℂ :=
  ExteriorAlgebra.liftAlternating (altPairFamily φ ψ)

@[simp]
lemma extPairDual_ι_mul_ι {V : Type} [AddCommGroup V] [Module ℂ V]
    (φ ψ : Module.Dual ℂ V) (x y : V) :
    extPairDual φ ψ (ExteriorAlgebra.ι ℂ x * ExteriorAlgebra.ι ℂ y) =
      φ x * ψ y - φ y * ψ x := by
  rw [extPairDual, ExteriorAlgebra.liftAlternating_ι_mul,
    ExteriorAlgebra.liftAlternating_ι]
  rfl

/-!

## B. The dual family for the fermion bilinears

-/

/-- The augmentation of the B-boson factor: the algebra map to `ℂ` sending every
  gauge-field generator to zero. -/
noncomputable def augB : (ℂ ⊗[ℝ] BBoson.JetAlgebra) →ₐ[ℂ] ℂ :=
  Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ)
    (SymmetricAlgebra.lift (0 : BBoson.JetComponentSpace →ₗ[ℝ] ℂ))
    (fun _ _ => Commute.all _ _)

/-- The functional on the jet algebra dual to a chosen fermion bilinear: the
  augmentation on the B-boson factor tensored with `extPairDual` on the lepton
  factor. -/
noncomputable def fermionPairDual
    (φ ψ : Module.Dual ℂ LeptonSinglet.JetComponentSpace) : JetAlgebra →ₗ[ℂ] ℂ :=
  TensorProduct.lift
    (((LinearMap.mul ℂ ℂ).comp augB.toLinearMap).compl₂ (extPairDual φ ψ))

@[simp]
lemma fermionPairDual_tmul (φ ψ : Module.Dual ℂ LeptonSinglet.JetComponentSpace)
    (a : ℂ ⊗[ℝ] BBoson.JetAlgebra) (b : LeptonSinglet.JetAlgebra) :
    fermionPairDual φ ψ (a ⊗ⱼ b) = augB a * extPairDual φ ψ b := rfl

/-- The augmentation kills a gauge-field generator. -/
@[simp]
lemma augB_ofGenerator (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) :
    augB (1 ⊗ₜ[ℝ] BBoson.JetAlgebra.ofGenerator (BBoson.JetGenerators.dB s μ)) = 0 := by
  simp [augB, BBoson.JetAlgebra.ofGenerator]

/-- The augmentation is unital. -/
@[simp]
lemma augB_one_tmul_one : augB (1 ⊗ₜ[ℝ] (1 : BBoson.JetAlgebra)) = 1 := by
  rw [show (1 : ℂ) ⊗ₜ[ℝ] (1 : BBoson.JetAlgebra) = 1 from rfl, map_one]

/-- The functional dual to the fermion bilinear `ψ̄_α D_μ ψ_β`. -/
noncomputable def fermionDual (q : Fin 2 × (Fin 1 ⊕ Fin 3) × Fin 2) :
    JetAlgebra →ₗ[ℂ] ℂ :=
  fermionPairDual
    (LeptonSinglet.JetComponentSpace.basis.coord
      (LeptonSinglet.JetGenerators.dbarψ {} q.1))
    (LeptonSinglet.JetComponentSpace.basis.coord
      (LeptonSinglet.JetGenerators.dψ {q.2.1} q.2.2))

/-- `fermionDual` is dual to the sixteen fermion bilinears. The `- 6 i B_μ ψ_β`
  tail of `D_μ ψ_β` drops out twice over: the augmentation kills its gauge-field
  factor, and its fermionic factor carries no derivative index. -/
lemma fermionDual_Dbarψ_mul_Dψ (q p : Fin 2 × (Fin 1 ⊕ Fin 3) × Fin 2) :
    fermionDual q (Dbarψ [] p.1 * Dψ [p.2.1] p.2.2) = if p = q then 1 else 0 := by
  obtain ⟨α₀, μ₀, β₀⟩ := q
  obtain ⟨α, μ, β⟩ := p
  rw [Dbarψ_nil, Dψ_singleton, mul_sub, mul_smul_comm, ← mul_assoc]
  simp only [ofGenerator_dbarψ_eq, ofGenerator_dψ_eq, ofGenerator_B_eq,
    JetAlgebra.tmul_mul_tmul, mul_one, map_sub, map_smul,
    fermionDual, fermionPairDual_tmul,
    LeptonSinglet.JetAlgebra.ofGenerator, extPairDual_ι_mul_ι]
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_apply, LeptonSinglet.JetGenerators.dbarψ.injEq,
    LeptonSinglet.JetGenerators.dψ.injEq, reduceCtorEq, Prod.mk.injEq]
  simp only [Multiset.singleton_inj, true_and, mul_ite, mul_one, mul_zero]
  by_cases hα : α = α₀ <;> by_cases hμ : μ = μ₀ <;> by_cases hβ : β = β₀ <;>
    simp [hα, hμ, hβ]

/-- `fermionDual_Dbarψ_mul_Dψ` with the three indices given separately, so that
  it fires on bilinears written out rather than through a product index. -/
@[simp]
lemma fermionDual_apply (q : Fin 2 × (Fin 1 ⊕ Fin 3) × Fin 2) (α : Fin 2)
    (μ : Fin 1 ⊕ Fin 3) (β : Fin 2) :
    fermionDual q (Dbarψ [] α * Dψ [μ] β) = if (α, μ, β) = q then 1 else 0 :=
  fermionDual_Dbarψ_mul_Dψ q (α, μ, β)

/-- The sixteen fermion bilinears `ψ̄_α D_μ ψ_β` are linearly independent. -/
theorem Dbarψ_mul_Dψ_linearIndependent :
    LinearIndependent ℂ (fun p : Fin 2 × (Fin 1 ⊕ Fin 3) × Fin 2 =>
      Dbarψ [] p.1 * Dψ [p.2.1] p.2.2) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc q
  have h := congrArg (fermionDual q) hc
  rw [map_sum, map_zero] at h
  simp only [map_smul, smul_eq_mul, fermionDual_Dbarψ_mul_Dψ, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq' Finset.univ q c, Finset.mem_univ, if_true] at h
  exact h

end JetAlgebra

end LeptonGaugeSector

end
