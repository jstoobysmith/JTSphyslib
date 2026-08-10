/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.JetDeriv
/-!
# The covariant derivatives of the charged lepton

The covariant derivative `D_l ψ_α` of the charged lepton and its conjugate
`D̄_l ψ̄_α`, built by iterating the covariant step `∂_μ + 6 i B_μ`, and the
covariant substitution that trades the plain fermionic coordinates for them.
-/

@[expose] public section


namespace LeptonGaugeSector
open TensorProduct StandardModel

namespace JetAlgebra

/-!

## Covariant derivatives

The covariant derivative `D_l ψ_α` of the charged lepton, indexed by an ordered
list `l` of spacetime directions: covariant derivatives do not commute — their
commutator is the field strength — so the index is a list rather than a
multiset, with the head of the list the outermost derivative.

The component functions of the lepton transform contragrediently, through the
hypercharge power series `u ^ 6`, so the covariant step on component functions
is `D_μ = ∂_μ - 6 i B_μ`: under a jet gauge transformation `∂_μ ψ_α` shifts by
`- 6 i mc_μ ψ_α` while `B_μ`, being a component function too, shifts
contragrediently by `- mc_μ` (`BBoson.mcShift`), and the two contributions
cancel for the coupling `- 6 i` — and only for that coupling. The step is
defined on the whole jet algebra; applied repeatedly to the zeroth-order
component function of `ψ` it produces the covariant derivatives.

-/

/-- One covariant-derivative step `D_μ = ∂_μ - 6 i B_μ` on the lepton–gauge-sector
  jet algebra:
  the total spacetime derivative together with multiplication by the gauge field
  weighted by the hypercharge coupling. The sign is fixed by covariance: the
  component function `ψ_α` carries hypercharge `+6`, so `∂_μ ψ_α` picks up
  `- 6 i mc_μ ψ_α`, while `B_μ` shifts contragrediently by `- mc_μ`
  (`BBoson.mcShift`); the two cancel only for the coupling `- 6 i`. -/
noncomputable def covariantStep (μ : Fin 1 ⊕ Fin 3) : JetAlgebra →ₗ[ℂ] JetAlgebra :=
  jetDeriv μ - ((6 : ℂ) * Complex.I) • LinearMap.mulLeft ℂ [JetGenerators.dB {} μ]ₐ

@[simp]
lemma covariantStep_apply (μ : Fin 1 ⊕ Fin 3) (x : JetAlgebra) :
    covariantStep μ x =
      jetDeriv μ x - ((6 : ℂ) * Complex.I) • ([JetGenerators.dB {} μ]ₐ * x) := by
  rw [covariantStep, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.mulLeft_apply]

/-- The covariant derivative `D_l ψ_α` of the charged lepton along the ordered
  list of directions `l`, with the head of the list the outermost derivative. -/
noncomputable def Dψ (l : List (Fin 1 ⊕ Fin 3)) (α : Fin 2) :
    JetAlgebra :=
  l.foldr (fun μ x => covariantStep μ x) [JetGenerators.dψ {} α]ₐ

/-- The zeroth covariant derivative is the lepton component function itself. -/
@[simp]
lemma Dψ_nil (α : Fin 2) :
    Dψ [] α = [JetGenerators.dψ {} α]ₐ := rfl

@[simp]
lemma Dψ_cons (μ : Fin 1 ⊕ Fin 3) (l : List (Fin 1 ⊕ Fin 3))
    (α : Fin 2) :
    Dψ (μ :: l) α = covariantStep μ (Dψ l α) :=
  rfl

/-- The first covariant derivative: `D_μ ψ_α = ∂_μ ψ_α - 6 i B_μ ψ_α`. -/
lemma Dψ_singleton (μ : Fin 1 ⊕ Fin 3) (α : Fin 2) :
    Dψ [μ] α = [JetGenerators.dψ {μ} α]ₐ -
      ((6 : ℂ) * Complex.I) • ([JetGenerators.dB {} μ]ₐ * [JetGenerators.dψ {} α]ₐ) := by
  rw [Dψ_cons, Dψ_nil, covariantStep_apply]
  congr 1
  simp only [ofGenerator]
  rw [jetDeriv_tmul, LinearMap.baseChange_tmul]
  simp only [BBoson.JetAlgebra.jetDeriv_one, TensorProduct.tmul_zero, tmul_zero,
    TensorProduct.zero_tmul, zero_tmul, zero_add, LeptonSinglet.JetAlgebra.jetDeriv_ofGenerator,
    LeptonSinglet.JetGenerators.shift_dψ, Multiset.empty_eq_zero]

/-- One covariant-derivative step `D̄_μ = ∂_μ + 6 i B_μ` for the conjugate
  lepton on the lepton–gauge-sector jet algebra: the conjugate component
  function `ψ̄_α` carries
  hypercharge `-6`, so its coupling is the opposite of that in
  `covariantStep`. -/
noncomputable def covariantStepBar (μ : Fin 1 ⊕ Fin 3) : JetAlgebra →ₗ[ℂ] JetAlgebra :=
  jetDeriv μ + ((6 : ℂ) * Complex.I) • LinearMap.mulLeft ℂ [JetGenerators.dB {} μ]ₐ

@[simp]
lemma covariantStepBar_apply (μ : Fin 1 ⊕ Fin 3) (x : JetAlgebra) :
    covariantStepBar μ x =
      jetDeriv μ x + ((6 : ℂ) * Complex.I) • ([JetGenerators.dB {} μ]ₐ * x) := by
  rw [covariantStepBar, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.mulLeft_apply]

/-- The covariant derivative `D̄_l ψ̄_α` of the conjugate lepton along the
  ordered list of directions `l`, with the head of the list the outermost
  derivative. -/
noncomputable def Dbarψ (l : List (Fin 1 ⊕ Fin 3)) (α : Fin 2) : JetAlgebra :=
  l.foldr (fun μ x => covariantStepBar μ x) [JetGenerators.dbarψ {} α]ₐ

/-- The zeroth covariant derivative is the conjugate-lepton component function
  itself. -/
@[simp]
lemma Dbarψ_nil (α : Fin 2) :
    Dbarψ [] α = [JetGenerators.dbarψ {} α]ₐ := rfl

@[simp]
lemma Dbarψ_cons (μ : Fin 1 ⊕ Fin 3) (l : List (Fin 1 ⊕ Fin 3)) (α : Fin 2) :
    Dbarψ (μ :: l) α = covariantStepBar μ (Dbarψ l α) := rfl

/-- The first conjugate covariant derivative:
  `D̄_μ ψ̄_α = ∂_μ ψ̄_α + 6 i B_μ ψ̄_α`. -/
lemma Dbarψ_singleton (μ : Fin 1 ⊕ Fin 3) (α : Fin 2) :
    Dbarψ [μ] α = [JetGenerators.dbarψ {μ} α]ₐ + ((6 : ℂ) * Complex.I) •
        ([JetGenerators.dB {} μ]ₐ * [JetGenerators.dbarψ {} α]ₐ) := by
  rw [Dbarψ_cons, Dbarψ_nil, covariantStepBar_apply]
  congr 1
  simp only [ofGenerator]
  rw [jetDeriv_tmul, LinearMap.baseChange_tmul]
  simp only [BBoson.JetAlgebra.jetDeriv_one, TensorProduct.tmul_zero, tmul_zero,
    TensorProduct.zero_tmul, zero_tmul, zero_add,
    LeptonSinglet.JetAlgebra.jetDeriv_ofGenerator,
    LeptonSinglet.JetGenerators.shift_dbarψ, Multiset.empty_eq_zero]

/-!

### The covariant substitution

The change of variables from the plain fermionic coordinates `∂_s ψ_α`,
`∂_s ψ̄_α` to the covariant coordinates `D_s ψ_α`, `D̄_s ψ̄_α`, as an algebra
endomorphism of the lepton–gauge-sector jet algebra fixing the B-boson factor.

-/

/-- A canonical list presentation of a multiset of spacetime indices. -/
noncomputable def sortList (s : Multiset (Fin 1 ⊕ Fin 3)) : List (Fin 1 ⊕ Fin 3) :=
  ((s.map finSumFinEquiv).sort (· ≤ ·)).map finSumFinEquiv.symm

@[simp]
lemma coe_sortList (s : Multiset (Fin 1 ⊕ Fin 3)) :
    (↑(sortList s) : Multiset (Fin 1 ⊕ Fin 3)) = s := by
  rw [sortList, ← Multiset.map_coe, Multiset.sort_eq, Multiset.map_map]
  simp

@[simp]
lemma length_sortList (s : Multiset (Fin 1 ⊕ Fin 3)) :
    (sortList s).length = Multiset.card s := by
  rw [sortList, List.length_map, Multiset.length_sort, Multiset.card_map]

/-- The derivative degree of a lepton jet generator. -/
def genDeg : LeptonSinglet.JetGenerators → ℕ
  | .dψ s _ => Multiset.card s
  | .dbarψ s _ => Multiset.card s

/-- The covariant element associated with a lepton jet generator: the covariant
  derivative along a canonical ordering of the multiset of derivative indices. -/
noncomputable def covGenerator : LeptonSinglet.JetGenerators → JetAlgebra
  | .dψ s α => Dψ (sortList s) α
  | .dbarψ s α => Dbarψ (sortList s) α

/-- The linear map sending each fermionic component function to its covariant
  version. -/
noncomputable def covMap : LeptonSinglet.JetComponentSpace →ₗ[ℂ] JetAlgebra :=
  LeptonSinglet.JetComponentSpace.basis.constr ℂ covGenerator

@[simp]
lemma covMap_basis (g : LeptonSinglet.JetGenerators) :
    covMap (LeptonSinglet.JetComponentSpace.basis g) = covGenerator g := by
  rw [covMap, Module.Basis.constr_basis]
end JetAlgebra

end LeptonGaugeSector
