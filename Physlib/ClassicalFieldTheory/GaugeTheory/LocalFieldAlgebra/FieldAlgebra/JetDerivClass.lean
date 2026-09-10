/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.FieldAlgebra.Basic
/-!
# The total derivative on a field algebra: the interface

The formal total spacetime derivative `∂_μ` on a field algebra is a derivation extending the
shift `∂_s ψ_α ↦ ∂_{s + {μ}} ψ_α` of the component functions. Its *construction* depends on
the statistics — a derivation of the symmetric algebra for bosons, an even derivation of the
exterior algebra for fermions — but its *properties* do not: the Leibniz rule has the same
form in both cases. This file records those properties as the class `HasJetDeriv`; the
constructions are `BosonicAlgebra.jetDeriv` and `FermionicAlgebra.jetDeriv`, and everything
built on them is in
`Physlib.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.FieldAlgebra.JetDeriv`.
-/

@[expose] public section

variable {G : Type} [Group G] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {G₀ : Type} [Group G₀] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {jets : LocalGaugeData G 𝔤 G₀ 𝔤J} {M : MatterField jets}

/-- **A total derivative on a field algebra**: for each direction `μ` a linear map which is
  an (even) derivation and acts on the generators by `shift μ`, the shift of the derivative
  label on the component space.

  The shift is carried as a second `outParam` rather than being read off a matter field,
  for the same reason `IsFieldAlgebra` is stated on the component space: a matter field is
  not recoverable from `A`, while both `C` and the shift on it are, so instance resolution
  keeps working. For the component space of a matter field the shift is
  `JetComponentSpace.jetDeriv`. -/
class HasJetDeriv (C : outParam Type) [AddCommGroup C] [Module ℂ C]
    (shift : outParam ((Fin 1 ⊕ Fin 3) → C →ₗ[ℂ] C))
    (A : Type) [Ring A] [Algebra ℂ A] [IsFieldAlgebra C A] where
  /-- The total derivative in the direction `μ`. -/
  jetDeriv : (Fin 1 ⊕ Fin 3) → A →ₗ[ℂ] A
  jetDeriv_ι : ∀ (μ : Fin 1 ⊕ Fin 3) (x : C),
    jetDeriv μ (FieldAlgebra.ι A x) = FieldAlgebra.ι A (shift μ x)
  jetDeriv_algebraMap : ∀ (μ : Fin 1 ⊕ Fin 3) (r : ℂ), jetDeriv μ (algebraMap ℂ A r) = 0
  jetDeriv_mul : ∀ (μ : Fin 1 ⊕ Fin 3) (x y : A),
    jetDeriv μ (x * y) = jetDeriv μ x * y + x * jetDeriv μ y

namespace FieldAlgebra

variable {A : Type} [Ring A] [Algebra ℂ A] [IsFieldAlgebra (JetComponentSpace M) A]
  [HasJetDeriv (JetComponentSpace M) (JetComponentSpace.jetDeriv (M := M)) A]

/-- The formal total spacetime derivative on the field algebra in the direction `μ`. -/
noncomputable def jetDeriv (μ : Fin 1 ⊕ Fin 3) : A →ₗ[ℂ] A := HasJetDeriv.jetDeriv μ

/-- On a component function the total derivative is the shift of the derivative label. -/
@[simp]
lemma jetDeriv_ι (μ : Fin 1 ⊕ Fin 3) (x : JetComponentSpace M) :
    jetDeriv μ (ι A x) = ι A (JetComponentSpace.jetDeriv μ x) :=
  HasJetDeriv.jetDeriv_ι μ x

@[simp]
lemma jetDeriv_algebraMap (μ : Fin 1 ⊕ Fin 3) (r : ℂ) :
    jetDeriv μ (algebraMap ℂ A r) = 0 :=
  HasJetDeriv.jetDeriv_algebraMap μ r

@[simp]
lemma jetDeriv_one (μ : Fin 1 ⊕ Fin 3) : jetDeriv (A := A) μ 1 = 0 := by
  rw [← (algebraMap ℂ A).map_one, jetDeriv_algebraMap]

/-- The total derivative is an (even) derivation: the Leibniz rule holds on the field
  algebra, with no Koszul signs. -/
lemma jetDeriv_mul (μ : Fin 1 ⊕ Fin 3) (x y : A) :
    jetDeriv μ (x * y) = jetDeriv μ x * y + x * jetDeriv μ y :=
  HasJetDeriv.jetDeriv_mul μ x y

end FieldAlgebra
