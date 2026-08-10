/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.Basic
/-!
# The field strengths of the lepton–gauge-sector jet algebra

The derivatives `∂_s F_{μν}` of the B-boson field strength, embedded in the
lepton–gauge-sector
jet algebra as elements of its bosonic factor, together with the identities
that hold of them as elements of that algebra: antisymmetry in the two field
indices, vanishing on a repeated index, and commutativity, the field strengths
lying in the commutative bosonic factor.
-/

@[expose] public section


namespace LeptonGaugeSector
open TensorProduct StandardModel

namespace JetAlgebra

/-- The derivatives of the B-boson field strength, embedded in the lepton–gauge-sector jet
  algebra. -/
noncomputable def fieldStrengthDeriv (s : Multiset (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) : JetAlgebra :=
  ((1 : ℂ) ⊗ₜ[ℝ] BBoson.JetAlgebra.fieldStrengthDeriv s μ ν) ⊗ⱼ 1


/-- Reordering the two derivative indices of a second-derivative field
  strength. -/
lemma fieldStrengthDeriv_pair_swap (r s a b : Fin 1 ⊕ Fin 3) :
    fieldStrengthDeriv {r, s} a b = fieldStrengthDeriv {s, r} a b := by
  have h : ({r, s} : Multiset (Fin 1 ⊕ Fin 3)) = {s, r} := Multiset.cons_swap r s 0
  rw [h]

/-- Antisymmetry of the embedded field-strength derivatives in the two field
  indices. -/
lemma fieldStrengthDeriv_antisymm (s : Multiset (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) :
    fieldStrengthDeriv s ν μ = - fieldStrengthDeriv s μ ν := by
  have h : ∀ a b : Fin 1 ⊕ Fin 3, (fieldStrengthDeriv s a b : JetAlgebra) =
      [JetGenerators.dB (s + {a}) b]ₐ - [JetGenerators.dB (s + {b}) a]ₐ := by
    intro a b
    rw [fieldStrengthDeriv, BBoson.JetAlgebra.fieldStrengthDeriv,
      TensorProduct.tmul_sub, sub_tmul]
    rfl
  rw [h, h, neg_sub]

/-- The canonical orientation of a mixed field-strength component: the time
  index first. -/
lemma fieldStrengthDeriv_inr_inl (s : Multiset (Fin 1 ⊕ Fin 3)) (i : Fin 3)
    (j : Fin 1) :
    fieldStrengthDeriv s (Sum.inr i) (Sum.inl j) =
      - fieldStrengthDeriv s (Sum.inl j) (Sum.inr i) :=
  fieldStrengthDeriv_antisymm s (Sum.inl j) (Sum.inr i)

/-- The field strength vanishes on a repeated index. -/
@[simp]
lemma fieldStrengthDeriv_self (s : Multiset (Fin 1 ⊕ Fin 3))
    (μ : Fin 1 ⊕ Fin 3) : fieldStrengthDeriv s μ μ = 0 := by
  have h : (fieldStrengthDeriv s μ μ : JetAlgebra) =
      [JetGenerators.dB (s + {μ}) μ]ₐ - [JetGenerators.dB (s + {μ}) μ]ₐ := by
    rw [fieldStrengthDeriv, BBoson.JetAlgebra.fieldStrengthDeriv,
      TensorProduct.tmul_sub, sub_tmul]
    rfl
  rw [h, sub_self]

/-- The embedded field-strength derivatives commute: they live in the
  commutative bosonic factor of the jet algebra. -/
lemma fieldStrengthDeriv_mul_comm (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (μ ν ρ τ : Fin 1 ⊕ Fin 3) :
    fieldStrengthDeriv s μ ν * fieldStrengthDeriv s' ρ τ =
      fieldStrengthDeriv s' ρ τ * fieldStrengthDeriv s μ ν := by
  rw [fieldStrengthDeriv, fieldStrengthDeriv, tmul_mul_tmul, tmul_mul_tmul]
  congr 1
  exact mul_comm _ _

end JetAlgebra

end LeptonGaugeSector
