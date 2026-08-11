/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.FermionicKineticTerm.LinearIndependence
/-!
# Linear independence of the conjugate fermion bilinears

The sixteen products `(D̄_μ ψ̄)_α ψ_β` — the derivative on the conjugate lepton rather than on
the lepton — are linearly independent. Statements about an explicit span of such products, the
boost-weight-zero part of the conjugate fermion kinetic sector say, then reduce to linear algebra
on coefficients.

The dual family is the one of `FermionicKineticTerm.LinearIndependence`, evaluated at the other
pair of dual basis vectors: `fermionPairDual` pairs a functional on the conjugate lepton with one
on the lepton, and here the derivative index is carried by the first rather than the second.
The `+ 6 i B_μ ψ̄_α` tail of `D̄_μ ψ̄_α` again contributes nothing, because its conjugate-lepton
factor carries no derivative index.

## Key results

- `fermionBarDual` : the functional dual to a chosen conjugate fermion bilinear.
- `Dbarψ_singleton_mul_Dψ_nil_linearIndependent` : the sixteen bilinears are independent.

-/

@[expose] public section

namespace LeptonGaugeSector
open TensorProduct StandardModel

namespace JetAlgebra

/-- The functional dual to the conjugate fermion bilinear `(D̄_μ ψ̄)_α ψ_β`. -/
noncomputable def fermionBarDual (q : Fin 2 × (Fin 1 ⊕ Fin 3) × Fin 2) :
    JetAlgebra →ₗ[ℂ] ℂ :=
  fermionPairDual
    (LeptonSinglet.JetComponentSpace.basis.coord
      (LeptonSinglet.JetGenerators.dbarψ {q.2.1} q.1))
    (LeptonSinglet.JetComponentSpace.basis.coord
      (LeptonSinglet.JetGenerators.dψ {} q.2.2))

/-- `fermionBarDual` is dual to the sixteen conjugate fermion bilinears. The `+ 6 i B_μ ψ̄_α`
  tail of `D̄_μ ψ̄_α` drops out twice over: the augmentation kills its gauge-field factor, and its
  conjugate-lepton factor carries no derivative index. -/
lemma fermionBarDual_Dbarψ_mul_Dψ (q p : Fin 2 × (Fin 1 ⊕ Fin 3) × Fin 2) :
    fermionBarDual q (Dbarψ [p.2.1] p.1 * Dψ [] p.2.2) = if p = q then 1 else 0 := by
  obtain ⟨α₀, μ₀, β₀⟩ := q
  obtain ⟨α, μ, β⟩ := p
  rw [Dbarψ_singleton, Dψ_nil, add_mul, smul_mul_assoc, mul_assoc]
  simp only [ofGenerator_dbarψ_eq, ofGenerator_dψ_eq, ofGenerator_B_eq,
    JetAlgebra.tmul_mul_tmul, one_mul, map_add, map_smul,
    fermionBarDual, fermionPairDual_tmul,
    LeptonSinglet.JetAlgebra.ofGenerator, extPairDual_ι_mul_ι]
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_apply, LeptonSinglet.JetGenerators.dbarψ.injEq,
    LeptonSinglet.JetGenerators.dψ.injEq, reduceCtorEq, Prod.mk.injEq]
  simp only [Multiset.singleton_inj, true_and, mul_ite, mul_one, mul_zero]
  by_cases hα : α = α₀ <;> by_cases hμ : μ = μ₀ <;> by_cases hβ : β = β₀ <;>
    simp [hα, hμ, hβ]

/-- `fermionBarDual_Dbarψ_mul_Dψ` with the three indices given separately, so that it fires on
  bilinears written out rather than through a product index. -/
@[simp]
lemma fermionBarDual_apply (q : Fin 2 × (Fin 1 ⊕ Fin 3) × Fin 2) (α : Fin 2)
    (μ : Fin 1 ⊕ Fin 3) (β : Fin 2) :
    fermionBarDual q (Dbarψ [μ] α * Dψ [] β) = if (α, μ, β) = q then 1 else 0 :=
  fermionBarDual_Dbarψ_mul_Dψ q (α, μ, β)

/-- The sixteen conjugate fermion bilinears `(D̄_μ ψ̄)_α ψ_β` are linearly independent. -/
theorem Dbarψ_singleton_mul_Dψ_nil_linearIndependent :
    LinearIndependent ℂ (fun p : Fin 2 × (Fin 1 ⊕ Fin 3) × Fin 2 =>
      Dbarψ [p.2.1] p.1 * Dψ [] p.2.2) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc q
  have h := congrArg (fermionBarDual q) hc
  rw [map_sum, map_zero] at h
  simp only [map_smul, smul_eq_mul, fermionBarDual_Dbarψ_mul_Dψ, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq' Finset.univ q c, Finset.mem_univ, if_true] at h
  exact h

end JetAlgebra

end LeptonGaugeSector

end
