/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.MatrixJets
/-!
# The local gauge data of `U(1)`

## i. Overview

The abelian gauge group `U(1)`, with its jets, its Lie algebra and the jets of its Lie
algebra, packaged as local gauge data `LocalGaugeData.u1`. The jets of gauge
transformations are the unitary formal power series, the Lie algebra is the self-adjoint
(real) scalars and its jets the self-adjoint power series, with vanishing bracket and
trivial adjoint action. The Maurer–Cartan form is `i (∂_μ u) u⁻¹`.

Read as `1 × 1` matrices, this is a presentation by matrices of jets,
`LocalGaugeData.u1MatrixJets`, so the laws of the local gauge data and its faithfulness come
from `Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.MatrixJets`. What this file
supplies is the carriers, the structure maps on them, and the canonical `U1Factor`.

## ii. Key results

- `U1`, `JetU1`, `U1Algebra`, `JetU1Algebra` : the carriers.
- `LocalGaugeData.u1MatrixJets` : the presentation of `U(1)` by `1 × 1` matrices of jets.
- `LocalGaugeData.u1` : the local gauge data of `U(1)`.
- `LocalGaugeData.u1Factor` : its canonical `U(1)` factor.
- `LocalGaugeData.instFaithfulU1` : the package is faithful.
- `LocalGaugeData.instFreeU1` : the package is free.

## iii. Table of contents

- A. The carriers
- B. The structure maps
- C. The Maurer–Cartan form
- D. Scalars as `1 × 1` matrices
- E. The presentation and the local gauge data
- F. The canonical factor

-/

@[expose] public section

open MvPowerSeries

/-!

## A. The carriers

-/

/-- The gauge group `U(1)`. -/
abbrev U1 : Type := ↥(unitary ℂ)

/-- Jets of `U(1)` gauge transformations: unitary formal power series. -/
abbrev JetU1 : Type := ↥(unitary JetRing)

/-- The Lie algebra `u(1)` over a `*`-ring: the self-adjoint elements, with vanishing
  bracket. -/
abbrev U1AlgebraOver (R : Type) [Ring R] [StarRing R] : Type := ↥(selfAdjoint R)

/-- The Lie algebra `u(1)`: the self-adjoint (real) scalars. -/
abbrev U1Algebra : Type := U1AlgebraOver ℂ

/-- Jets of the Lie algebra `u(1)`: the self-adjoint formal power series. -/
abbrev JetU1Algebra : Type := U1AlgebraOver JetRing

namespace U1AlgebraOver

variable {R : Type} [CommRing R] [StarRing R]

instance : Bracket (U1AlgebraOver R) (U1AlgebraOver R) := ⟨fun _ _ => 0⟩

@[simp]
lemma bracket_eq_zero (a b : U1AlgebraOver R) : ⁅a, b⁆ = 0 := rfl

instance : LieRing (U1AlgebraOver R) where
  add_lie _ _ _ := by simp
  lie_add _ _ _ := by simp
  lie_self _ := rfl
  leibniz_lie _ _ _ := by simp

instance [Algebra ℝ R] [StarModule ℝ R] : LieAlgebra ℝ (U1AlgebraOver R) where
  lie_smul _ _ _ := by simp

end U1AlgebraOver

instance : Module.Finite ℝ U1Algebra :=
  inferInstanceAs (Module.Finite ℝ (selfAdjoint.submodule ℝ ℂ))

namespace JetU1

/-!

## B. The structure maps

-/

/-- Evaluation of a jet of a `U(1)` gauge transformation at the base point. -/
noncomputable def eval : JetU1 →* U1 where
  toFun u := ⟨constantCoeff u.1, by
    obtain ⟨h1, h2⟩ := Unitary.mem_iff.mp u.2
    exact Unitary.mem_iff.mpr
      ⟨by rw [← JetRing.constantCoeff_star, ← map_mul, h1, map_one],
        by rw [← JetRing.constantCoeff_star, ← map_mul, h2, map_one]⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' u v := Subtype.ext (map_mul _ u.1 v.1)

@[simp]
lemma eval_val (u : JetU1) : (eval u : ℂ) = constantCoeff (u : JetRing) := rfl

/-- The jet of a constant `U(1)` gauge transformation. -/
noncomputable def ofConstant : U1 →* JetU1 where
  toFun u := ⟨C u.1, by
    obtain ⟨h1, h2⟩ := Unitary.mem_iff.mp u.2
    exact Unitary.mem_iff.mpr
      ⟨by rw [JetRing.star_C, ← map_mul, h1, map_one],
        by rw [JetRing.star_C, ← map_mul, h2, map_one]⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' u v := Subtype.ext (map_mul _ u.1 v.1)

@[simp]
lemma ofConstant_val (u : U1) : (ofConstant u : JetRing) = C (u : ℂ) := rfl

/-- The formal derivative of a `u(1)` jet. -/
noncomputable def deriv (μ : Fin 1 ⊕ Fin 3) : JetU1Algebra →ₗ[ℝ] JetU1Algebra where
  toFun a := ⟨pderiv μ a.1, by
    show star (pderiv μ a.1) = pderiv μ a.1
    rw [← JetRing.pderiv_star, a.2]⟩
  map_add' a b := Subtype.ext (map_add _ _ _)
  map_smul' r a := Subtype.ext (by
    show pderiv μ (r • a.1) = r • pderiv μ a.1
    rw [← algebraMap_smul ℂ r, Derivation.map_smul, algebraMap_smul])

@[simp]
lemma deriv_val (μ : Fin 1 ⊕ Fin 3) (a : JetU1Algebra) : (deriv μ a : JetRing) = pderiv μ a :=
  rfl

/-- Multiplication of a `u(1)` jet by the coordinate `x_μ`. -/
noncomputable def coord (μ : Fin 1 ⊕ Fin 3) : JetU1Algebra →ₗ[ℝ] JetU1Algebra where
  toFun a := ⟨(X μ : JetRing) * a.1, by
    show star ((X μ : JetRing) * a.1) = (X μ : JetRing) * a.1
    rw [star_mul', JetRing.star_X, a.2]⟩
  map_add' a b := Subtype.ext (mul_add _ _ _)
  map_smul' r a := Subtype.ext (mul_smul_comm _ _ _)

@[simp]
lemma coord_val (μ : Fin 1 ⊕ Fin 3) (a : JetU1Algebra) :
    (coord μ a : JetRing) = (X μ : JetRing) * a := rfl

/-- Evaluation of a `u(1)` jet at the base point. -/
noncomputable def evalLie : JetU1Algebra →ₗ[ℝ] U1Algebra where
  toFun a := ⟨constantCoeff a.1, by
    show star (constantCoeff a.1) = constantCoeff a.1
    rw [← JetRing.constantCoeff_star, a.2]⟩
  map_add' a b := Subtype.ext (map_add _ _ _)
  map_smul' r a := Subtype.ext (by
    show constantCoeff (r • a.1) = r • constantCoeff a.1
    rw [← algebraMap_smul ℂ r, constantCoeff_smul, algebraMap_smul])

@[simp]
lemma evalLie_val (a : JetU1Algebra) : (evalLie a : ℂ) = constantCoeff (a : JetRing) := rfl

/-- A constant as a `u(1)` jet. -/
noncomputable def ofConstantLie : U1Algebra →ₗ[ℝ] JetU1Algebra where
  toFun a := ⟨C a.1, by
    show star (C a.1 : JetRing) = C a.1
    rw [JetRing.star_C, a.2]⟩
  map_add' a b := Subtype.ext (map_add _ _ _)
  map_smul' r a := Subtype.ext (by
    show (C (r • a.1) : JetRing) = r • C a.1
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, MvPowerSeries.algebraMap_apply])

@[simp]
lemma ofConstantLie_val (a : U1Algebra) : (ofConstantLie a : JetRing) = C (a : ℂ) := rfl

/-!

## C. The Maurer–Cartan form

-/

/-- The Maurer–Cartan scalar `i (∂_μ u) u⁻¹` of a unitary jet is self-adjoint. -/
lemma star_mcVal (u : JetU1) (μ : Fin 1 ⊕ Fin 3) :
    star (Complex.I • (pderiv μ (u : JetRing) * star (u : JetRing)))
      = Complex.I • (pderiv μ (u : JetRing) * star (u : JetRing)) := by
  have hu : (u : JetRing) * star (u : JetRing) = 1 := Unitary.mul_star_self_of_mem u.2
  have h0 : pderiv μ ((u : JetRing) * star (u : JetRing)) = 0 := by rw [hu, pderiv_one]
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h0
  rw [star_smul, star_mul', star_star, ← JetRing.pderiv_star, Complex.star_def, Complex.conj_I,
    neg_smul, show pderiv μ (star (u : JetRing)) * (u : JetRing)
      = -(pderiv μ (u : JetRing) * star (u : JetRing)) from by linear_combination h0,
    smul_neg, neg_neg]

/-- The Maurer–Cartan form `i (∂_μ u) u⁻¹` of a `U(1)` jet. -/
noncomputable def mc (u : JetU1) (μ : Fin 1 ⊕ Fin 3) : JetU1Algebra :=
  ⟨Complex.I • (pderiv μ (u : JetRing) * star (u : JetRing)), star_mcVal u μ⟩

@[simp]
lemma mc_val (u : JetU1) (μ : Fin 1 ⊕ Fin 3) :
    (mc u μ : JetRing) = Complex.I • (pderiv μ (u : JetRing) * star (u : JetRing)) := rfl

/-!

## D. Scalars as `1 × 1` matrices

The presentation of `U(1)` by matrices reads a scalar as the `1 × 1` scalar matrix.

-/

section Scalar

variable {R : Type} [CommRing R] [StarRing R]

lemma scalar_star (x : R) : star (Matrix.scalar (Fin 1) x) = Matrix.scalar (Fin 1) (star x) := by
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose]
  rfl

omit [StarRing R] in
lemma scalar_map {S : Type} [CommRing S] (f : R → S) (hf : f 0 = 0) (x : R) :
    (Matrix.scalar (Fin 1) x).map f = Matrix.scalar (Fin 1) (f x) := by
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map hf]

omit [StarRing R] in
lemma scalar_smul {M : Type} [Monoid M] [DistribMulAction M R] (c : M) (x : R) :
    Matrix.scalar (Fin 1) (c • x) = c • Matrix.scalar (Fin 1) x := by
  rw [Matrix.scalar_apply, Matrix.scalar_apply, ← Matrix.diagonal_smul]
  rfl

end Scalar

/-!

## E. The presentation and the local gauge data

-/

end JetU1

namespace LocalGaugeData

open JetU1

/-- **The presentation of `U(1)` by `1 × 1` matrices of jets.** -/
noncomputable def u1MatrixJets : MatrixJets (Fin 1) U1 U1Algebra JetU1 JetU1Algebra where
  toMat₀ := (Matrix.scalar (Fin 1) : ℂ →+* _).toMonoidHom.comp (unitary ℂ).subtype
  toMat₀_injective _ _ h := Subtype.ext (Matrix.scalar_inj.mp h)
  toMatJ := (Matrix.scalar (Fin 1) : JetRing →+* _).toMonoidHom.comp (unitary JetRing).subtype
  toMatJ_injective _ _ h := Subtype.ext (Matrix.scalar_inj.mp h)
  toMatJ_mul_star u := by
    show Matrix.scalar (Fin 1) u.1 * star (Matrix.scalar (Fin 1) u.1) = 1
    rw [scalar_star, ← map_mul, Unitary.mul_star_self_of_mem u.2, map_one]
  star_toMatJ_mul u := by
    show star (Matrix.scalar (Fin 1) u.1) * Matrix.scalar (Fin 1) u.1 = 1
    rw [scalar_star, ← map_mul, Unitary.star_mul_self_of_mem u.2, map_one]
  lie₀ :=
    { toFun a := Matrix.scalar (Fin 1) a.1
      map_add' a b := by rw [AddSubgroup.coe_add, map_add]
      map_smul' r a := by rw [selfAdjoint.val_smul, scalar_smul, RingHom.id_apply] }
  lie₀_injective _ _ h := Subtype.ext (Matrix.scalar_inj.mp h)
  lie₀_bracket a b := by
    show Matrix.scalar (Fin 1) ((0 : U1Algebra) : ℂ)
      = Complex.I • (Matrix.scalar (Fin 1) a.1 * Matrix.scalar (Fin 1) b.1
        - Matrix.scalar (Fin 1) b.1 * Matrix.scalar (Fin 1) a.1)
    rw [ZeroMemClass.coe_zero, map_zero, ← map_mul, ← map_mul, mul_comm a.1 b.1, sub_self,
      smul_zero]
  lieJ :=
    { toFun a := Matrix.scalar (Fin 1) a.1
      map_add' a b := by rw [AddSubgroup.coe_add, map_add]
      map_smul' r a := by rw [selfAdjoint.val_smul, scalar_smul, RingHom.id_apply] }
  lieJ_injective _ _ h := Subtype.ext (Matrix.scalar_inj.mp h)
  lieJ_bracket a b := by
    show Matrix.scalar (Fin 1) ((0 : JetU1Algebra) : JetRing)
      = Complex.I • (Matrix.scalar (Fin 1) a.1 * Matrix.scalar (Fin 1) b.1
        - Matrix.scalar (Fin 1) b.1 * Matrix.scalar (Fin 1) a.1)
    rw [ZeroMemClass.coe_zero, map_zero, ← map_mul, ← map_mul, mul_comm a.1 b.1, sub_self,
      smul_zero]
  eval := JetU1.eval
  toMat₀_eval u := by
    show Matrix.scalar (Fin 1) (constantCoeff u.1) = (Matrix.scalar (Fin 1) u.1).map constantCoeff
    rw [scalar_map _ (map_zero _)]
  ofConstant := JetU1.ofConstant
  toMatJ_ofConstant u := by
    show Matrix.scalar (Fin 1) (C u.1) = (Matrix.scalar (Fin 1) u.1).map C
    rw [scalar_map _ (map_zero _)]
  evalLie := JetU1.evalLie
  lie₀_evalLie a := by
    show Matrix.scalar (Fin 1) (constantCoeff a.1) = (Matrix.scalar (Fin 1) a.1).map constantCoeff
    rw [scalar_map _ (map_zero _)]
  ofConstantLie := JetU1.ofConstantLie
  lieJ_ofConstantLie a := by
    show Matrix.scalar (Fin 1) (C a.1) = (Matrix.scalar (Fin 1) a.1).map C
    rw [scalar_map _ (map_zero _)]
  deriv := JetU1.deriv
  lieJ_deriv μ a := by
    show Matrix.scalar (Fin 1) (pderiv μ a.1) = (Matrix.scalar (Fin 1) a.1).map (pderiv μ)
    rw [scalar_map _ (map_zero _)]
  coord := JetU1.coord
  lieJ_coord μ a := by
    show Matrix.scalar (Fin 1) ((X μ : JetRing) * a.1) = (X μ : JetRing) • Matrix.scalar (Fin 1) a.1
    rw [← smul_eq_mul, scalar_smul]
  adjoint := Representation.trivial ℝ JetU1 JetU1Algebra
  lieJ_adjoint u a := by
    show Matrix.scalar (Fin 1) a.1
      = Matrix.scalar (Fin 1) u.1 * Matrix.scalar (Fin 1) a.1 * star (Matrix.scalar (Fin 1) u.1)
    rw [scalar_star, ← map_mul, ← map_mul, mul_comm u.1, mul_assoc,
      Unitary.mul_star_self_of_mem u.2, mul_one]
  adjointValue := Representation.trivial ℝ U1 U1Algebra
  lie₀_adjointValue u a := by
    show Matrix.scalar (Fin 1) a.1
      = Matrix.scalar (Fin 1) u.1 * Matrix.scalar (Fin 1) a.1 * star (Matrix.scalar (Fin 1) u.1)
    rw [scalar_star, ← map_mul, ← map_mul, mul_comm u.1, mul_assoc,
      Unitary.mul_star_self_of_mem u.2, mul_one]
  maurerCartan := JetU1.mc
  lieJ_maurerCartan u μ := by
    show Matrix.scalar (Fin 1) (Complex.I • (pderiv μ u.1 * star u.1))
      = Complex.I • ((Matrix.scalar (Fin 1) u.1).map (pderiv μ) * star (Matrix.scalar (Fin 1) u.1))
    rw [scalar_smul, map_mul, scalar_star, scalar_map _ (map_zero _)]

/-- **The local gauge data of `U(1)`**: unitary jets, self-adjoint scalar jets with
  vanishing bracket and trivial adjoint action, and the Maurer–Cartan form
  `i (∂_μ u) u⁻¹`. -/
noncomputable def u1 : LocalGaugeData U1 U1Algebra JetU1 JetU1Algebra :=
  u1MatrixJets.toLocalGaugeData

@[simp] lemma u1_eval : u1.eval = JetU1.eval := rfl
@[simp] lemma u1_ofConstant : u1.ofConstant = JetU1.ofConstant := rfl
@[simp] lemma u1_evalLie_apply (a : JetU1Algebra) : u1.evalLie a = JetU1.evalLie a := rfl
@[simp] lemma u1_ofConstantLie : u1.ofConstantLie = JetU1.ofConstantLie := rfl
@[simp] lemma u1_deriv (μ : Fin 1 ⊕ Fin 3) : u1.deriv μ = JetU1.deriv μ := rfl
@[simp] lemma u1_maurerCartan : u1.maurerCartan = JetU1.mc := rfl
@[simp] lemma u1_adjoint (u : JetU1) (a : JetU1Algebra) : u1.adjoint u a = a := rfl

/-- The iterated derivative on `u(1)` jets is the iterated formal derivative. -/
lemma u1_iteratedDeriv_val (s : Multiset (Fin 1 ⊕ Fin 3)) (a : JetU1Algebra) :
    (u1.iteratedDeriv s a : JetRing) = s.foldl (fun h ρ => pderiv ρ h) (a : JetRing) := by
  induction s using Multiset.induction_on generalizing a with
  | empty => rw [iteratedDeriv_zero, LinearMap.id_apply, Multiset.foldl_zero]
  | cons μ t ih =>
    rw [iteratedDeriv_cons, LinearMap.comp_apply, u1_deriv, JetU1.deriv_val, ih,
      Multiset.foldl_cons, JetRing.foldl_pderiv_pderiv]

/-- The local gauge data of `U(1)` is faithful. -/
instance instFaithfulU1 : u1.Faithful := u1MatrixJets.faithful

/-- A `1 × 1` matrix is the scalar matrix of its entry. -/
lemma _root_.JetU1.eq_scalar {R : Type} [CommRing R] (A : Matrix (Fin 1) (Fin 1) R) :
    A = Matrix.scalar (Fin 1) (A 0 0) := by
  ext i j
  rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
  simp

/-- The local gauge data of `U(1)` is free. Real Taylor data give a self-adjoint jet, and
  the unitary Euler transport of a `1 × 1` matrix is a unitary jet. -/
instance instFreeU1 : u1.Free :=
  u1MatrixJets.free
    (fun c => ⟨⟨JetRing.taylorSeries fun s => ((c s : U1Algebra) : ℂ), by
      rw [selfAdjoint.mem_iff, JetRing.star_taylorSeries]
      exact congrArg _ (funext fun s => (c s).2)⟩, by
      rw [JetU1.eq_scalar (JetRing.taylorMatrix _), JetRing.taylorMatrix_apply]
      rfl⟩)
    (fun a => by
      show star (Matrix.scalar (Fin 1) a.1) = Matrix.scalar (Fin 1) a.1
      rw [JetU1.scalar_star, a.2])
    (fun ρ V hV0 hVu hEV => by
      have hu : V 0 0 * star (V 0 0) = 1 := by
        simpa [Matrix.mul_apply] using congrArg (fun A => A 0 0) hVu
      exact ⟨⟨V 0 0, Unitary.mem_iff.mpr ⟨by rw [mul_comm]; exact hu, hu⟩⟩,
        (JetU1.eq_scalar V).symm⟩)

/-!

## F. The canonical factor

-/

/-- The canonical `U(1)` factor of the local gauge data of `U(1)`. -/
noncomputable def u1Factor : U1Factor u1 where
  u := MonoidHom.id JetU1
  φ :=
    { toFun a := (a : ℂ)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  φJ a := (a : JetRing)
  φJ_ofConstantLie _ := rfl
  φJ_cc_foldl p a := by
    show constantCoeff (p.foldl (fun h ρ => pderiv ρ h) (a : JetRing))
      = constantCoeff (u1.iteratedDeriv p a : JetRing)
    rw [u1_iteratedDeriv_val]
  φJ_maurerCartan _ _ := rfl
  φJ_adjoint _ _ := rfl

end LocalGaugeData
