/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Relativity.DerivAlgebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Physlib.Relativity.Tensors.ComplexTensor.Vector.Pre.Basic
/-!

# The jet gauge group

## i. Overview

For the Standard Model on Minkowski spacetime,
gauge transforms are maps from spacetime to the gauge group `G := SU(3) × SU(2) × U(1)`.

If one is considering a gauge transformation `g` at a point `x`, its action
on all the fields and their derivatives at `x` is determined by the
value of `g` and all its derivatives at `x`.  The collection of all
possible values of `g` and their derivatives at `x` is called the *jet* of `g` at `x`.
These form a group, which we call `JetGaugeGroupI`.

The group `JetGaugeGroupI` acts on all the fields and their derivatives at `x`,
every gauge transformation `g` has a corresponding element of `JetGaugeGroupI`,
and the action of `g` on the fields and their derivatives at `x` is determined by this element.

Thus locally it is enough to consider the action of `JetGaugeGroupI` on the fields and
their derivatives at a point, instead of the full set of gauge transformations on spacetime,
which is large and unwieldy.

-/

@[expose] public section

namespace StandardModel

open Matrix MvPowerSeries JetRing
open scoped Nat

/-!

## B. The jet gauge group

The ring `JetRing` of formal power series in the spacetime coordinates, in which
jets of fields and of gauge transformations are valued, is defined in
`Physlib.Relativity.DerivAlgebra`, together with the algebra of derivative
symbols `DerivAlgebraComplex` and the action `DerivAlgebraComplex.jetRingAction`
of the jet ring on it.

-/

/-- The group of formal infinite-order jets, at a spacetime point, of local gauge
  transformations of the Standard Model: the `R`-points of the gauge group for `R`
  the ring `JetRing` of formal power series in the spacetime coordinates.

  Since gauge transformations multiply pointwise, jets multiply as power series and
  the group structure is that of the matrix groups over `JetRing`. The unitarity and
  determinant constraints hold as power-series identities, i.e. at every jet order.

  Evaluation at the base point recovers `GaugeGroupI`; see `JetGaugeGroupI.eval`. -/
abbrev JetGaugeGroupI : Type :=
  specialUnitaryGroup (Fin 3) JetRing × specialUnitaryGroup (Fin 2) JetRing ×
  unitary JetRing

namespace JetGaugeGroupI

/-!

## C. Evaluation at the base point

The constant coefficient of a power series is its value at the base point of the
jet. Applied entrywise it sends jets of gauge transformations to their zeroth-order
parts, giving a group homomorphism `JetGaugeGroupI →* GaugeGroupI`.

-/

/-- Entrywise evaluation at the base point commutes with the conjugate transpose. -/
lemma mapMatrix_constantCoeff_star {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n JetRing) :
    (constantCoeff : JetRing →+* ℂ).mapMatrix (star A) =
      star ((constantCoeff : JetRing →+* ℂ).mapMatrix A) := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.star_apply]

/-- Evaluation of a jet of a special-unitary gauge transformation at the base point:
  the entrywise constant coefficient. -/
noncomputable def evalSU (n : Type) [Fintype n] [DecidableEq n] :
    specialUnitaryGroup n JetRing →* specialUnitaryGroup n ℂ where
  toFun U := ⟨(constantCoeff : JetRing →+* ℂ).mapMatrix U.1, by
    obtain ⟨h1, h2⟩ := mem_specialUnitaryGroup_iff.mp U.2
    rw [mem_specialUnitaryGroup_iff]
    constructor
    · rw [mem_unitaryGroup_iff] at h1 ⊢
      rw [show star ((constantCoeff : JetRing →+* ℂ).mapMatrix U.1) =
          (constantCoeff : JetRing →+* ℂ).mapMatrix (star U.1) from
          (mapMatrix_constantCoeff_star U.1).symm, ← map_mul, h1, map_one]
    · rw [← RingHom.map_det, h2, map_one]⟩
  map_one' := Subtype.ext (map_one ((constantCoeff : JetRing →+* ℂ).mapMatrix))
  map_mul' U V := Subtype.ext (map_mul ((constantCoeff : JetRing →+* ℂ).mapMatrix) U.1 V.1)

/-- Evaluation of a jet of a `U(1)` gauge transformation at the base point: the
  constant coefficient. -/
noncomputable def evalU1 : unitary JetRing →* unitary ℂ where
  toFun u := ⟨constantCoeff u.1, by
    obtain ⟨h1, h2⟩ := Unitary.mem_iff.mp u.2
    exact Unitary.mem_iff.mpr
      ⟨by rw [← constantCoeff_star, ← map_mul, h1, map_one],
        by rw [← constantCoeff_star, ← map_mul, h2, map_one]⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' u v := Subtype.ext (map_mul _ u.1 v.1)

/-- Evaluation of a jet of a gauge transformation at the base point, projecting the
  jet gauge group onto the gauge group `GaugeGroupI` by taking zeroth-order parts on
  each factor. -/
noncomputable def eval : JetGaugeGroupI →* GaugeGroupI :=
  (evalSU (Fin 3)).prodMap ((evalSU (Fin 2)).prodMap evalU1)

/-!

## D. Constant jets

The constant power series embed the gauge group `GaugeGroupI` into the jet gauge
group, as the jets of constant (global) gauge transformations. This is a section of
the evaluation `eval`.

-/

/-- Entrywise inclusion of constants commutes with the conjugate transpose. -/
lemma mapMatrix_C_star {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    (C : ℂ →+* JetRing).mapMatrix (star A) = star ((C : ℂ →+* JetRing).mapMatrix A) := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.star_apply]

/-- The jet of a constant special-unitary gauge transformation: the entrywise
  inclusion of constants. -/
noncomputable def ofConstantSU (n : Type) [Fintype n] [DecidableEq n] :
    specialUnitaryGroup n ℂ →* specialUnitaryGroup n JetRing where
  toFun u := ⟨(C : ℂ →+* JetRing).mapMatrix u.1, by
    obtain ⟨h1, h2⟩ := mem_specialUnitaryGroup_iff.mp u.2
    rw [mem_specialUnitaryGroup_iff]
    constructor
    · rw [mem_unitaryGroup_iff] at h1 ⊢
      rw [show star ((C : ℂ →+* JetRing).mapMatrix u.1) =
          (C : ℂ →+* JetRing).mapMatrix (star u.1) from (mapMatrix_C_star u.1).symm,
        ← map_mul, h1, map_one]
    · rw [← RingHom.map_det, h2, map_one]⟩
  map_one' := Subtype.ext (map_one ((C : ℂ →+* JetRing).mapMatrix))
  map_mul' u v := Subtype.ext (map_mul ((C : ℂ →+* JetRing).mapMatrix) u.1 v.1)

/-- The jet of a constant `U(1)` gauge transformation: the inclusion of constants. -/
noncomputable def ofConstantU1 : unitary ℂ →* unitary JetRing where
  toFun u := ⟨C u.1, by
    obtain ⟨h1, h2⟩ := Unitary.mem_iff.mp u.2
    exact Unitary.mem_iff.mpr
      ⟨by rw [star_C, ← map_mul, h1, map_one],
        by rw [star_C, ← map_mul, h2, map_one]⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' u v := Subtype.ext (map_mul _ u.1 v.1)

/-- The embedding of the gauge group into the jet gauge group as the jets of
  constant (global) gauge transformations. -/
noncomputable def ofConstant : GaugeGroupI →* JetGaugeGroupI :=
  (ofConstantSU (Fin 3)).prodMap ((ofConstantSU (Fin 2)).prodMap ofConstantU1)

/-- Evaluating the jet of a constant gauge transformation at the base point recovers
  the gauge transformation: `ofConstant` is a section of `eval`. -/
@[simp]
lemma eval_ofConstant (g : GaugeGroupI) : eval (ofConstant g) = g := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
  · ext i j
    simp [eval, ofConstant, evalSU, ofConstantSU,
      RingHom.mapMatrix_apply, Matrix.map_apply]
  · ext i j
    simp [eval, ofConstant, evalSU, ofConstantSU,
      RingHom.mapMatrix_apply, Matrix.map_apply]
  · simp [eval, ofConstant, evalU1, ofConstantU1]

end JetGaugeGroupI

end StandardModel
