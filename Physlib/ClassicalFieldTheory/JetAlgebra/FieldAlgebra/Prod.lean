/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Physlib.ClassicalFieldTheory.JetAlgebra.FieldAlgebra.Statistics
public import Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.Prod
/-!
# The field algebras of a direct sum

## i. Overview

Two matter fields, valued in `V` and `W`, are jointly a single matter field valued in
`V × W`. For bosonic fields its algebra is the ordinary tensor product of the two bosonic
algebras (`BosonicAlgebra.prodEquiv`); for fermionic fields it is the *graded* tensor
product of the two fermionic algebras with their Fermi-parity grading
(`FermionicAlgebra.prodEquiv`), which is what makes fermions of different species
anticommute.

## ii. Key results

- `BosonicAlgebra.prodEquiv` :
  `BosonicAlgebra (V × W) ≃ₐ[ℂ] BosonicAlgebra M ⊗[ℂ] BosonicAlgebra N`.
- `FermionicAlgebra.evenOdd` : the Fermi-parity grading.
- `FermionicAlgebra.prodEquiv` : the graded tensor product decomposition.

-/

@[expose] public section

variable {G : Type} [Group G] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {G₀ : Type} [Group G₀] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {jets : LocalGaugeData G 𝔤 G₀ 𝔤J}

section Bosonic

open scoped TensorProduct


/-!

## A. The tensor product decomposition

-/

/-- **The bosonic algebra of a direct sum is the tensor product of the bosonic algebras.**
  Two bosonic matter fields of the same mass weight taken together are one field valued in
  the direct sum of their target spaces, and its bosonic algebra is the tensor product of
  theirs. The shared weight is what `MatterField.prod` needs to exist; the equivalence
  itself does not use it. The ordinary —
  rather than the graded — tensor product is correct here: bosonic generators commute
  across species just as they do within one. -/
noncomputable def BosonicAlgebra.prodEquiv (M N : MatterField jets)
    (h : M.massWeight = N.massWeight) :
    BosonicAlgebra (M.prod N h) ≃ₐ[ℂ] BosonicAlgebra M ⊗[ℂ] BosonicAlgebra N :=
  (SymmetricAlgebra.congr (JetComponentSpace.prodEquiv M N h)).trans
    SymmetricAlgebra.prodEquiv

end Bosonic

section Fermionic

open scoped TensorProduct

/-- Transport of an exterior algebra along a linear equivalence of the underlying module. -/
noncomputable def ExteriorAlgebra.congr {R A B : Type*} [CommRing R] [AddCommGroup A]
    [Module R A] [AddCommGroup B] [Module R B] (e : A ≃ₗ[R] B) :
    ExteriorAlgebra R A ≃ₐ[R] ExteriorAlgebra R B :=
  CliffordAlgebra.equivOfIsometry ⟨e, fun _ => rfl⟩



/-!

## A. The component space of a direct sum

The splitting `JetComponentSpace.prodEquiv` of the component space of a direct sum lives
with the component space itself, in
  `Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.JetComponentSpace.Basic`.

-/

/-!

## B. The Fermi-parity grading

-/

/-- **The Fermi-parity grading** of the fermionic algebra: the `ZMod 2` grading of the
  exterior algebra by the number of component functions in a monomial. An even element
  commutes with everything; two odd elements anticommute. -/
abbrev FermionicAlgebra.evenOdd (M : MatterField jets) :
    ZMod 2 → Submodule ℂ (FermionicAlgebra M) :=
  CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (JetComponentSpace M))

/-!

## C. The exterior product decomposition

-/

/-- **The fermionic algebra of a direct sum is the exterior product of the fermionic
  algebras.** Two matter fields of the same mass weight taken together are one field valued
  in the direct sum of their target spaces, and its fermionic algebra is the graded tensor
  product of theirs.

  The tensor product must be the *graded* one `ᵍ⊗`: an ordinary `⊗[ℂ]` would make a
  generator of the first field commute with a generator of the second, whereas fermionic
  generators anticommute across species just as they do within one. -/
noncomputable def FermionicAlgebra.prodEquiv (M N : MatterField jets)
    (h : M.massWeight = N.massWeight) :
    FermionicAlgebra (M.prod N h) ≃ₐ[ℂ]
      (FermionicAlgebra.evenOdd M ᵍ⊗[ℂ] FermionicAlgebra.evenOdd N) :=
  (ExteriorAlgebra.congr (JetComponentSpace.prodEquiv M N h)).trans <|
    (CliffordAlgebra.equivOfIsometry
        (Q₁ := (0 : QuadraticForm ℂ (JetComponentSpace M × JetComponentSpace N)))
        (Q₂ := (0 : QuadraticForm ℂ (JetComponentSpace M)).prod
          (0 : QuadraticForm ℂ (JetComponentSpace N)))
        ⟨LinearEquiv.refl ℂ _, fun _ => by simp⟩).trans
      (CliffordAlgebra.prodEquiv _ _)

end Fermionic
