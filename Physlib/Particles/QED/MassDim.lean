/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.QED.JetAlgebra
public import Physlib.Relativity.MinkowskiMatrix
public import Physlib.Relativity.PauliMatrices.Basic
/-!
# Mass dimension on the QED jet algebra

-/

@[expose] public section

namespace QED
open TensorProduct StandardModel

/-- We define the mass weight of a term as two times its mass dimnesion. -/
def MassWeight : JetGenerators → ℕ
  | JetGenerators.dB s _ => 2 * (1 + s.card)
  | JetGenerators.dψ s _ => 3 + 2 * s.card
  | JetGenerators.dbarψ s _ => 3 + 2 * s.card

namespace JetAlgebra

/-- The mass-dimension scaling on the QED jet algebra: the algebra map
  multiplying each generator by `c ^ w`, where `w` is twice its mass dimension.
  It is the tensor product of the scalings on the B-boson and charged-lepton
  jet algebras. -/
noncomputable def massWeightScale (c : ℂ) : JetAlgebra →ₐ[ℂ] JetAlgebra :=
  Algebra.TensorProduct.map (BBoson.JetAlgebra.massWeightScale c)
    (LeptonSinglet.JetAlgebra.massWeightScale c)

/-- Each generator scales by `c` to the power of its mass weight. -/
@[simp]
lemma massWeightScale_ofGenerator (c : ℂ) (j : JetGenerators) :
    massWeightScale c [j]ₐ = c ^ MassWeight j • [j]ₐ := by
  cases j with
  | dB s μ =>
    simp only [ofGenerator, massWeightScale, Algebra.TensorProduct.map_tmul, map_one,
      BBoson.JetAlgebra.massWeightScale_tmul_ofGenerator, ← TensorProduct.smul_tmul']
    rfl
  | dψ s α =>
    simp only [ofGenerator, massWeightScale, Algebra.TensorProduct.map_tmul,
      ← Algebra.TensorProduct.one_def, map_one,
      LeptonSinglet.JetAlgebra.massWeightScale_ofGenerator, TensorProduct.tmul_smul]
    rfl
  | dbarψ s α =>
    simp only [ofGenerator, massWeightScale, Algebra.TensorProduct.map_tmul,
      ← Algebra.TensorProduct.one_def, map_one,
      LeptonSinglet.JetAlgebra.massWeightScale_ofGenerator, TensorProduct.tmul_smul]
    rfl


noncomputable def MassDimSubmodule (n : ℕ) : Submodule ℂ JetAlgebra :=
    Submodule.span ℂ { x | ∀ c : ℂ, massWeightScale c x = c ^ n • x }

noncomputable def MassWeightLESubmodule (n : ℕ) : Submodule ℂ JetAlgebra :=
  Submodule.span ℂ {x | ∃ m ≤ n, ∀ c : ℂ, massWeightScale c x = c ^ n • x}

noncomputable def InvariantMassWeightSubmodule (n : ℕ) : Submodule ℂ JetAlgebra :=
  MassWeightLESubmodule n ⊓ InvariantSubmodule

/-!

## The renormalizable invariants

The gauge- and Lorentz-invariant elements of mass dimension at most four (mass
weight at most eight). Besides the constants these are kinetic terms alone: the
Maxwell term `F_{μν} F^{μν}`, the topological theta term
`ε^{μνρσ} F_{μν} F_{ρσ}`, and the two fermion kinetic terms
`i ψ̄ σ^μ (D_μ ψ)` and `-i (D̄_μ ψ̄) σ^μ ψ` (equal up to a total derivative).
No mass term exists: `ψψ` and `ψ̄ψ̄` carry hypercharge `±12`, and `ψ̄ψ` is not a
Lorentz scalar for a single Weyl fermion. All other candidate weights `≤ 8` are
excluded by charge balance or by the absence of a Lorentz invariant:
`∂^μ ∂^ν F_{μν} = 0` and `η^{μν} F_{μν} = 0` identically.

-/

open scoped minkowskiMatrix PauliMatrix

/-- The Maxwell kinetic term `F_{μν} F^{μν}`: the field-strength square with
  both indices raised by the (diagonal) Minkowski metric. Mass weight eight. -/
noncomputable def maxwellTerm : JetAlgebra :=
  ∑ μ, ∑ ν, ((η μ μ * η ν ν : ℝ) : ℂ) •
    (fieldStrengthDeriv {} μ ν * fieldStrengthDeriv {} μ ν)

/-- The topological theta term `ε^{μνρσ} F_{μν} F_{ρσ}`, written as a sum over
  the permutations of the four spacetime indices weighted by their signs. Mass
  weight eight. -/
noncomputable def thetaTerm : JetAlgebra :=
  ∑ p : Equiv.Perm (Fin 4), (Equiv.Perm.sign p : ℤ) •
    (fieldStrengthDeriv {} ((finSumFinEquiv (m := 1) (n := 3)).symm (p 0))
        ((finSumFinEquiv (m := 1) (n := 3)).symm (p 1)) *
      fieldStrengthDeriv {} ((finSumFinEquiv (m := 1) (n := 3)).symm (p 2))
        ((finSumFinEquiv (m := 1) (n := 3)).symm (p 3)))

/-- The fermion kinetic term `i ψ̄_α (σ^μ)_{α β} (D_μ ψ)_β` of the right-handed
  charged-lepton singlet, with the covariant derivative on the lepton. Mass
  weight eight. -/
noncomputable def fermionKineticTerm : JetAlgebra :=
  Complex.I • ∑ μ, ∑ α, ∑ β, σ μ α β • (Dbarψ [] α * Dψ [μ] β)

/-- The conjugate fermion kinetic term `-i (D̄_μ ψ̄)_α (σ^μ)_{α β} ψ_β`, with the
  covariant derivative on the conjugate lepton. Mass weight eight. -/
noncomputable def fermionKineticTermBar : JetAlgebra :=
  (-Complex.I) • ∑ μ, ∑ α, ∑ β, σ μ α β • (Dbarψ [μ] α * Dψ [] β)

/-- The invariants of the QED jet algebra of mass dimension at most four: the
  constants and the four kinetic terms. These span
  `InvariantMassWeightSubmodule 8`, the renormalizable QED Lagrangian densities. -/
def massDimFourInvariants : Set JetAlgebra :=
  {1, maxwellTerm, thetaTerm, fermionKineticTerm, fermionKineticTermBar}

lemma invariantMassWeightSubmodule_eight_eq_span_massDimFourInvariants :
    InvariantMassWeightSubmodule 8 = Submodule.span ℂ massDimFourInvariants := by
  sorry

end JetAlgebra

end QED
