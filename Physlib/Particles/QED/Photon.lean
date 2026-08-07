/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Electromagnetism.Kinematics.GaugeTransformation
public import Physlib.Electromagnetism.Dynamics.KineticTerm
/-!
# The jet algebra of the photon

## i. Overview

This file builds, from scratch, the jet algebra of the electromagnetic potential
of `Physlib.Electromagnetism`: the free commutative algebra on formal symbols
`∂_s A_μ`, one for every multiset `s` of spacetime directions and every Lorentz
index `μ`, together with the `U(1)_em` gauge action on those symbols and the
evaluation of the algebra on an honest potential.

It deliberately does *not* use `Physlib.Particles.StandardModel.GaugeBosons.BBoson`.
The `B` boson is the gauge boson of `U(1)_Y`, defined before electroweak symmetry
breaking; the photon is the mixed combination `A = cos θ_W B + sin θ_W W³`, and
the two are not the same field.  Building the photon jet algebra directly on
`ElectromagneticPotential` avoids that identification, and also avoids inheriting
the Standard Model charge normalisation `6Y`, which has no meaning for `U(1)_em`.

The two results the file is built around are:

* the field strength and the Maxwell term are invariant under the formal gauge
  action, and the proof is exactly the commutativity of multiset addition
  (`gaugeAction_fieldStrength`);
* evaluated on any differentiable potential `A`, the formal Maxwell term
  `F_{μν} F^{μν}` is `-4 μ₀` times `ElectromagneticPotential.kineticTerm`
  (`evalPotential_maxwellTerm`).

Nothing here involves the charged lepton.  Note that a faithful QED matter
sector needs a *Dirac* electron, that is two Weyl spinors of the same chirality
with charges `±Q`, which is what makes the dimension-three mass term
`m ψ̄ ψ` available; a single Weyl fermion admits no such term.

## ii. Key results

- `JetGenerators`, `JetAlgebra` : the formal jet coordinates `∂_s A_μ` and the
  algebra of real polynomials in them.
- `fieldStrength` : the formal field strength `∂_s F_{μν}`.
- `maxwellTerm` : the formal Maxwell term `F_{μν} F^{μν}`.
- `gaugeAction` : the `U(1)_em` gauge action `∂_s A_μ ↦ ∂_s A_μ + ∂_s ∂_μ χ`.
- `gaugeAction_fieldStrength`, `gaugeAction_maxwellTerm` : gauge invariance.
- `derivMultiset` : the iterated partial derivative `∂_s` along a multiset.
- `evalPotential` : the evaluation of the jet algebra on a potential.
- `evalPotential_maxwellTerm` : the formal Maxwell term is the Maxwell
  Lagrangian of `Physlib.Electromagnetism`.
- `evalPotential_fieldStrength_gaugeTransform` : the evaluation is compatible
  with the concrete gauge transformation `A ↦ A + ∂χ`.

## iii. Table of contents

- A. The jet coordinates of the photon
  - A.1. The field strength
  - A.2. The Maxwell term
- B. The gauge action
  - B.1. Gauge invariance of the field strength and the Maxwell term
- C. Iterated derivatives indexed by a multiset
- D. Evaluation on a potential
  - D.1. Evaluation of the field strength
  - D.2. The Maxwell term is the Maxwell Lagrangian
  - D.3. Compatibility with concrete gauge transformations

## iv. References

The concrete side is `Physlib/Electromagnetism/Kinematics/GaugeTransformation.lean`
and `Physlib/Electromagnetism/Dynamics/KineticTerm.lean`.

-/

@[expose] public section

namespace QED

open Electromagnetism SpaceTime minkowskiMatrix

attribute [-simp] Fintype.sum_sum_type

namespace Photon

/-!

## A. The jet coordinates of the photon

A jet coordinate is a formal symbol `∂_s A_μ`, where `s` is a *multiset* of
spacetime directions: for a smooth potential the partial derivatives commute, so
only the number of times each direction occurs matters.  The jet algebra is the
algebra of real polynomials in these symbols.

-/

/-- The jet coordinates of the electromagnetic potential: the symbol `∂_s A_μ`,
  the `s`-th derivative of the `μ`-th covariant component. -/
inductive JetGenerators where
  /-- The jet coordinate `∂_s A_μ`. -/
  | dA (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) : JetGenerators
  deriving DecidableEq

/-- The jet algebra of the photon: real polynomials in the jet coordinates. -/
abbrev JetAlgebra : Type := MvPolynomial JetGenerators ℝ

namespace JetAlgebra

/-- The jet coordinate `∂_s A_μ` as an element of the jet algebra. -/
noncomputable def coord (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) : JetAlgebra :=
  MvPolynomial.X (JetGenerators.dA s μ)

/-!

### A.1. The field strength

-/

/-- The formal field strength `∂_s F_{μν} = ∂_s ∂_μ A_ν - ∂_s ∂_ν A_μ`. -/
noncomputable def fieldStrength (s : Multiset (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) :
    JetAlgebra :=
  coord (s + {μ}) ν - coord (s + {ν}) μ

lemma fieldStrength_antisymm (s : Multiset (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) :
    fieldStrength s μ ν = -fieldStrength s ν μ := by
  simp [fieldStrength]

@[simp]
lemma fieldStrength_self (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) :
    fieldStrength s μ μ = 0 := by
  simp [fieldStrength]

/-!

### A.2. The Maxwell term

-/

/-- The formal Maxwell term `F_{μν} F^{μν}`, both indices raised with the
  (diagonal) Minkowski metric. -/
noncomputable def maxwellTerm : JetAlgebra :=
  ∑ μ, ∑ ν, (η μ μ * η ν ν) • (fieldStrength 0 μ ν * fieldStrength 0 μ ν)

/-!

## B. The gauge action

A `U(1)_em` gauge transformation sends `A_μ ↦ A_μ + ∂_μ χ`, hence on jet
coordinates `∂_s A_μ ↦ ∂_s A_μ + ∂_s ∂_μ χ`.  All that the jet algebra sees of
the gauge function `χ` is the family of its symmetrised derivatives at the base
point, which is what `GaugeJet` records; the shift of `∂_s A_μ` is then the
value of that family at `s + {μ}`.

-/

/-- A gauge jet: the family `s ↦ ∂_s χ` of symmetrised derivatives of a gauge
  function at the base point.  This is all the jet algebra sees of a gauge
  transformation. -/
abbrev GaugeJet : Type := Multiset (Fin 1 ⊕ Fin 3) → ℝ

/-- The gauge action on the jet algebra: the algebra map determined by
  `∂_s A_μ ↦ ∂_s A_μ + ∂_s ∂_μ χ`. -/
noncomputable def gaugeAction (c : GaugeJet) : JetAlgebra →ₐ[ℝ] JetAlgebra :=
  MvPolynomial.aeval fun j => match j with
    | JetGenerators.dA s μ => coord s μ + MvPolynomial.C (c (s + {μ}))

@[simp]
lemma gaugeAction_coord (c : GaugeJet) (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) :
    gaugeAction c (coord s μ) = coord s μ + MvPolynomial.C (c (s + {μ})) := by
  rw [coord, gaugeAction, MvPolynomial.aeval_X]
  rfl

@[simp]
lemma gaugeAction_C (c : GaugeJet) (r : ℝ) :
    gaugeAction c (MvPolynomial.C r) = MvPolynomial.C r := by
  rw [gaugeAction, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]

/-- Gauge jets compose by addition: the gauge transformations form a group
  acting on the jet algebra. -/
lemma gaugeAction_comp (c₁ c₂ : GaugeJet) :
    (gaugeAction c₁).comp (gaugeAction c₂) = gaugeAction (c₁ + c₂) := by
  refine MvPolynomial.algHom_ext fun j => ?_
  obtain ⟨s, μ⟩ := j
  rw [AlgHom.comp_apply]
  show gaugeAction c₁ (gaugeAction c₂ (coord s μ)) = gaugeAction (c₁ + c₂) (coord s μ)
  rw [gaugeAction_coord, gaugeAction_coord, map_add, gaugeAction_coord, gaugeAction_C,
    add_assoc, ← MvPolynomial.C_add]
  rfl

@[simp]
lemma gaugeAction_zero : gaugeAction 0 = AlgHom.id ℝ JetAlgebra := by
  refine MvPolynomial.algHom_ext fun j => ?_
  obtain ⟨s, μ⟩ := j
  show gaugeAction 0 (coord s μ) = coord s μ
  simp

/-!

### B.1. Gauge invariance of the field strength and the Maxwell term

The field strength is gauge invariant, and the reason is exactly that multiset
addition is commutative: the two shifts are `∂_s ∂_μ ∂_ν χ` and
`∂_s ∂_ν ∂_μ χ`, indexed by `s + {μ} + {ν}` and `s + {ν} + {μ}`.  Clairaut's
theorem is built into the indexing.

-/

@[simp]
theorem gaugeAction_fieldStrength (c : GaugeJet) (s : Multiset (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) :
    gaugeAction c (fieldStrength s μ ν) = fieldStrength s μ ν := by
  have hcomm : s + {μ} + {ν} = s + {ν} + {μ} := by
    rw [add_assoc, add_assoc, add_comm ({μ} : Multiset _)]
  rw [fieldStrength, map_sub, gaugeAction_coord, gaugeAction_coord, hcomm]
  ring

@[simp]
theorem gaugeAction_maxwellTerm (c : GaugeJet) : gaugeAction c maxwellTerm = maxwellTerm := by
  rw [maxwellTerm, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [map_smul, map_mul, gaugeAction_fieldStrength]

/-!

## C. Iterated derivatives indexed by a multiset

To evaluate a jet coordinate on a potential we must differentiate along a
multiset of directions, so we must choose an order; we choose the canonical one,
sorting `s` through `Fin 1 ⊕ Fin 3 ≃ Fin 4`.  For a `C^∞` potential the choice
is immaterial, by Clairaut's theorem (`SpaceTime.deriv_commute`).

-/

/-- The iterated partial derivative `∂_s f` along a multiset `s` of spacetime
  directions, taken in the canonical order obtained by sorting `s`. -/
noncomputable def derivMultiset (s : Multiset (Fin 1 ⊕ Fin 3)) (f : SpaceTime 3 → ℝ) :
    SpaceTime 3 → ℝ :=
  ((s.map (finSumFinEquiv (m := 1) (n := 3))).sort).foldr
    (fun i g => ∂_ ((finSumFinEquiv (m := 1) (n := 3)).symm i) g) f

@[simp]
lemma derivMultiset_zero (f : SpaceTime 3 → ℝ) : derivMultiset 0 f = f := by
  simp [derivMultiset]

@[simp]
lemma derivMultiset_singleton (μ : Fin 1 ⊕ Fin 3) (f : SpaceTime 3 → ℝ) :
    derivMultiset {μ} f = ∂_ μ f := by
  simp [derivMultiset]

/-!

## D. Evaluation on a potential

`ElectromagneticPotential` stores the contravariant components `A^μ`, whereas a
gauge potential carries a lower index, so the jet coordinate `∂_s A_μ` evaluates
to the `s`-th derivative of `A_μ = η_{μμ} A^μ`.

-/

/-- The covariant components `A_μ = η_{μμ} A^μ` of an electromagnetic potential. -/
noncomputable def coPotential (A : ElectromagneticPotential 3) (μ : Fin 1 ⊕ Fin 3) :
    SpaceTime 3 → ℝ := fun x => η μ μ * A x μ

/-- The evaluation of the photon jet algebra at an electromagnetic potential `A`:
  the algebra map sending the formal jet coordinate `∂_s A_μ` to the honest
  function `∂_s A_μ` on spacetime. -/
noncomputable def evalPotential (A : ElectromagneticPotential 3) :
    JetAlgebra →ₐ[ℝ] (SpaceTime 3 → ℝ) :=
  MvPolynomial.aeval fun j => match j with
    | JetGenerators.dA s μ => derivMultiset s (coPotential A μ)

@[simp]
lemma evalPotential_coord (A : ElectromagneticPotential 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (μ : Fin 1 ⊕ Fin 3) :
    evalPotential A (coord s μ) = derivMultiset s (coPotential A μ) := by
  rw [coord, evalPotential, MvPolynomial.aeval_X]

/-!

### D.1. Evaluation of the field strength

-/

/-- The derivative of a covariant component.  Differentiability is needed to move
  the constant `η_{νν}` through the derivative. -/
lemma deriv_coPotential (A : ElectromagneticPotential 3) (hA : Differentiable ℝ A)
    (μ ν : Fin 1 ⊕ Fin 3) (x : SpaceTime 3) :
    ∂_ μ (coPotential A ν) x = η ν ν * ∂_ μ A x ν := by
  have hd : Differentiable ℝ (fun y => A y ν) := (SpaceTime.differentiable_vector _).mpr hA ν
  rw [SpaceTime.deriv_apply_eq μ ν _ hA x]
  show fderiv ℝ (fun y => η ν ν * A y ν) x (Lorentz.Vector.basis μ) = _
  rw [fderiv_const_mul (hd x)]
  simp

lemma evalPotential_fieldStrength_zero_apply (A : ElectromagneticPotential 3)
    (hA : Differentiable ℝ A) (μ ν : Fin 1 ⊕ Fin 3) (x : SpaceTime 3) :
    evalPotential A (fieldStrength 0 μ ν) x = η ν ν * ∂_ μ A x ν - η μ μ * ∂_ ν A x μ := by
  rw [fieldStrength, map_sub]
  simp only [zero_add, evalPotential_coord, derivMultiset_singleton, Pi.sub_apply]
  rw [deriv_coPotential A hA μ ν x, deriv_coPotential A hA ν μ x]

/-- The formal field strength evaluates to the field strength of the potential
  with both indices lowered, `F_{μν} = η_{μμ} η_{νν} F^{μν}`. -/
lemma evalPotential_fieldStrength_zero (A : ElectromagneticPotential 3)
    (hA : Differentiable ℝ A) (μ ν : Fin 1 ⊕ Fin 3) (x : SpaceTime 3) :
    evalPotential A (fieldStrength 0 μ ν) x =
      η μ μ * η ν ν * A.fieldStrengthMatrix x (μ, ν) := by
  rw [evalPotential_fieldStrength_zero_apply A hA μ ν x,
    ElectromagneticPotential.toFieldStrength_basis_repr_apply_eq_single (μν := (μ, ν))]
  rcases mul_self_eq_one_iff.mp (minkowskiMatrix.η_apply_mul_η_apply_diag μ) with h1 | h1 <;>
    rcases mul_self_eq_one_iff.mp (minkowskiMatrix.η_apply_mul_η_apply_diag ν) with h2 | h2 <;>
    rw [h1, h2] <;> ring

/-!

### D.2. The Maxwell term is the Maxwell Lagrangian

-/

/-- **The formal Maxwell term is the Maxwell Lagrangian.**  Evaluated on any
  differentiable electromagnetic potential, the gauge-invariant jet polynomial
  `F_{μν} F^{μν}` is `-4 μ₀` times the kinetic term
  `- 1/(4 μ₀) F_{μν} F^{μν}` of `Physlib.Electromagnetism`. -/
theorem evalPotential_maxwellTerm (𝓕 : FreeSpace) (A : ElectromagneticPotential 3)
    (hA : Differentiable ℝ A) (x : SpaceTime 3) :
    evalPotential A maxwellTerm x = -(4 * 𝓕.μ₀) * A.kineticTerm 𝓕 x := by
  rw [ElectromagneticPotential.kineticTerm_eq_sum_potential, maxwellTerm, map_sum]
  simp only [Finset.sum_apply, map_sum, map_smul, Pi.smul_apply, smul_eq_mul, map_mul,
    Pi.mul_apply]
  simp only [evalPotential_fieldStrength_zero_apply A hA]
  /- Both sides are now explicit double sums in `∂_ μ A x ν`. -/
  have key : ∀ μ ν : Fin 1 ⊕ Fin 3,
      η μ μ * η ν ν * ((η ν ν * ∂_ μ A x ν - η μ μ * ∂_ ν A x μ) *
        (η ν ν * ∂_ μ A x ν - η μ μ * ∂_ ν A x μ)) =
      (η μ μ * η ν ν * (∂_ μ A x ν) ^ 2 - ∂_ μ A x ν * ∂_ ν A x μ) +
      (η ν ν * η μ μ * (∂_ ν A x μ) ^ 2 - ∂_ ν A x μ * ∂_ μ A x ν) := by
    intro μ ν
    rcases mul_self_eq_one_iff.mp (minkowskiMatrix.η_apply_mul_η_apply_diag μ) with h1 | h1 <;>
      rcases mul_self_eq_one_iff.mp (minkowskiMatrix.η_apply_mul_η_apply_diag ν) with h2 | h2 <;>
      rw [h1, h2] <;> ring
  rw [Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => key μ ν]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun μ ν : Fin 1 ⊕ Fin 3 =>
      η ν ν * η μ μ * (∂_ ν A x μ) ^ 2 - ∂_ ν A x μ * ∂_ μ A x ν)]
  have hμ₀ : 𝓕.μ₀ ≠ 0 := ne_of_gt 𝓕.μ₀_pos
  field_simp
  ring

/-!

### D.3. Compatibility with concrete gauge transformations

The formal gauge invariance of section B.1 is matched on the concrete side: the
evaluation of the field strength, and hence of the Maxwell term, is unchanged
when the potential is replaced by `A + ∂χ`.

-/

lemma differentiable_gaugeTransform {A : ElectromagneticPotential 3} {χ : SpaceTime 3 → ℝ}
    (hA : Differentiable ℝ A) (hχ : ContDiff ℝ 2 χ) :
    Differentiable ℝ (ElectromagneticPotential.gaugeTransform χ A) :=
  hA.add (ElectromagneticPotential.differentiable_ofGradient hχ)

/-- The evaluated field strength is invariant under the concrete gauge
  transformation `A ↦ A + ∂χ`, matching `gaugeAction_fieldStrength`. -/
theorem evalPotential_fieldStrength_gaugeTransform (A : ElectromagneticPotential 3)
    (χ : SpaceTime 3 → ℝ) (hA : Differentiable ℝ A) (hχ : ContDiff ℝ 2 χ)
    (μ ν : Fin 1 ⊕ Fin 3) (x : SpaceTime 3) :
    evalPotential (ElectromagneticPotential.gaugeTransform χ A) (fieldStrength 0 μ ν) x =
      evalPotential A (fieldStrength 0 μ ν) x := by
  rw [evalPotential_fieldStrength_zero _ (differentiable_gaugeTransform hA hχ),
    evalPotential_fieldStrength_zero A hA,
    ElectromagneticPotential.fieldStrengthMatrix_gaugeTransform A χ hA hχ]

/-- The Maxwell Lagrangian is gauge invariant, as read off from the jet algebra. -/
theorem evalPotential_maxwellTerm_gaugeTransform (A : ElectromagneticPotential 3)
    (χ : SpaceTime 3 → ℝ) (hA : Differentiable ℝ A) (hχ : ContDiff ℝ 2 χ)
    (x : SpaceTime 3) :
    evalPotential (ElectromagneticPotential.gaugeTransform χ A) maxwellTerm x =
      evalPotential A maxwellTerm x := by
  rw [maxwellTerm, map_sum, map_sum]
  simp only [Finset.sum_apply, map_sum, map_smul, Pi.smul_apply, smul_eq_mul, map_mul,
    Pi.mul_apply]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  rw [evalPotential_fieldStrength_gaugeTransform A χ hA hχ]

end JetAlgebra

end Photon

end QED
