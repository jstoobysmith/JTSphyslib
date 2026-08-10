/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeBosons.BBoson.Basic
public import Physlib.Mathematics.PolynomialEval
/-!

# The mass dimension associated with the `B` boson

**Important:** Since it is easier to work with natural numbers rather then rationals,
  we will work with twice the mass dimension which we will call the `mass weight`.


-/

@[expose] public section

set_option maxHeartbeats 1000000


namespace StandardModel

open TensorProduct

namespace BBoson
open Module
namespace JetAlgebra

/-!

## The mass weight polynomial

We define a polynomial associated with each element of the jet algebra, where the coefficient of
`X ^ n` is the sum of all components of mass weight `n`.
This is useful for checking that certain elements are zero,
since an element is zero if and only if all coefficients of its mass-weight polynomial are zero.

-/
/-- The mass-weight polynomial on the complexified B-boson jet algebra: the
  `ℂ`-algebra map sending each generator `j` to `X ^ w * j`, where `w` is the
  mass weight of `j`.

  The component space is a real vector space, so the symmetric-algebra lift
  produces an `ℝ`-algebra map; `AlgHom.liftEquiv` turns it into a `ℂ`-algebra map
  on the complexification, being the universal property of base change: a
  `ℂ`-algebra map out of `ℂ ⊗[ℝ] A` is the same thing as an `ℝ`-algebra map out
  of `A`. -/
noncomputable def massWeightPoly :
    (ℂ ⊗[ℝ] JetAlgebra) →ₐ[ℂ] Polynomial (ℂ ⊗[ℝ] JetAlgebra) :=
  AlgHom.liftEquiv ℝ ℂ JetAlgebra _
    (SymmetricAlgebra.lift (JetComponentSpace.basis.constr ℝ fun j =>
      Polynomial.monomial j.massWeight ((1 : ℂ) ⊗ₜ[ℝ] ofGenerator j)))

/-- The scalar of the complexification passes straight through. -/
lemma massWeightPoly_tmul (c : ℂ) (b : JetAlgebra) :
    massWeightPoly (c ⊗ₜ[ℝ] b) = c • massWeightPoly ((1 : ℂ) ⊗ₜ[ℝ] b) := by
  rw [massWeightPoly, AlgHom.liftEquiv_tmul, AlgHom.liftEquiv_tmul, one_smul]

/-- Each generator is sent to `j * X ^ w`, where `w` is its mass weight. -/
@[simp]
lemma massWeightPoly_ofGenerator (j : JetGenerators) :
    massWeightPoly ((1 : ℂ) ⊗ₜ[ℝ] ofGenerator j) =
      Polynomial.monomial j.massWeight ((1 : ℂ) ⊗ₜ[ℝ] ofGenerator j) := by
  rw [massWeightPoly, AlgHom.liftEquiv_tmul, one_smul, ofGenerator,
    SymmetricAlgebra.lift_ι_apply, Module.Basis.constr_basis]
  rfl

/-- Setting the formal variable to one recovers the original element. -/
lemma massWeightPoly_eval_one (x : ℂ ⊗[ℝ] JetAlgebra) :
    (massWeightPoly x).eval 1 = x := by
  have h : (Polynomial.eval₂AlgHom (AlgHom.id ℂ (ℂ ⊗[ℝ] JetAlgebra)) 1
      fun a => Commute.all a _).comp massWeightPoly =
      AlgHom.id ℂ (ℂ ⊗[ℝ] JetAlgebra) := by
    refine (AlgHom.liftEquiv ℝ ℂ JetAlgebra _).symm.injective ?_
    refine SymmetricAlgebra.algHom_ext
      (Module.Basis.ext JetComponentSpace.basis fun j => ?_)
    simp [massWeightPoly, ofGenerator]
  exact AlgHom.congr_fun h x

/-- Every element is the sum of the coefficients of its mass-weight polynomial. -/
lemma eq_sum_massWeightPoly_coeff (x : ℂ ⊗[ℝ] JetAlgebra) :
    x = ∑ n ∈ Polynomial.support (massWeightPoly x), (massWeightPoly x).coeff n := by
  conv_lhs => rw [← massWeightPoly_eval_one x]
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  simp

/-- `massWeightPoly` is injective, however, it is not surjective. -/
lemma massWeightPoly_injective : Function.Injective massWeightPoly := by
  intro x y h
  rw [← massWeightPoly_eval_one x, ← massWeightPoly_eval_one y]
  simp [h]


/-- Homogeneity of the coefficients for a linear generator: each basis vector is
  homogeneous, and a general vector is a combination of basis vectors. -/
lemma massWeightPoly_coeff_massWeightPoly_ι (n : ℕ) (v : JetComponentSpace) :
    massWeightPoly ((massWeightPoly ((1 : ℂ) ⊗ₜ[ℝ]
        SymmetricAlgebra.ι ℝ JetComponentSpace v)).coeff n) =
      Polynomial.monomial n ((massWeightPoly ((1 : ℂ) ⊗ₜ[ℝ]
        SymmetricAlgebra.ι ℝ JetComponentSpace v)).coeff n) := by
  have hv : v ∈ Submodule.span ℝ (Set.range JetComponentSpace.basis) := by
    rw [JetComponentSpace.basis.span_eq]
    trivial
  induction hv using Submodule.span_induction generalizing n with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    rw [show SymmetricAlgebra.ι ℝ JetComponentSpace (JetComponentSpace.basis j) =
        ofGenerator j from rfl, massWeightPoly_ofGenerator, Polynomial.coeff_monomial]
    split_ifs with h
    · rw [← h, massWeightPoly_ofGenerator]
    · simp only [map_zero]
  | zero => simp only [map_zero, TensorProduct.tmul_zero, Polynomial.coeff_zero]
  | add y z _ _ hy hz =>
    simp only [map_add, TensorProduct.tmul_add, Polynomial.coeff_add]
    rw [hy n, hz n]
  | smul c y _ hy =>
    have h : ((1 : ℂ) ⊗ₜ[ℝ] SymmetricAlgebra.ι ℝ JetComponentSpace (c • y)
          : ℂ ⊗[ℝ] JetAlgebra) =
        (algebraMap ℝ ℂ c) • ((1 : ℂ) ⊗ₜ[ℝ] SymmetricAlgebra.ι ℝ JetComponentSpace y) := by
      rw [map_smul, TensorProduct.tmul_smul, ← algebraMap_smul ℂ c]
    rw [h, map_smul, Polynomial.coeff_smul, map_smul, hy n, Polynomial.smul_monomial]

/-- Homogeneity of the coefficients is inherited by products: the `n`-th
  coefficient of a product is a sum of products of coefficients of complementary
  degrees. -/
lemma massWeightPoly_coeff_massWeightPoly_mul {a b : ℂ ⊗[ℝ] JetAlgebra}
    (ha : ∀ n, massWeightPoly ((massWeightPoly a).coeff n) =
      Polynomial.monomial n ((massWeightPoly a).coeff n))
    (hb : ∀ n, massWeightPoly ((massWeightPoly b).coeff n) =
      Polynomial.monomial n ((massWeightPoly b).coeff n)) (n : ℕ) :
    massWeightPoly ((massWeightPoly (a * b)).coeff n) =
      Polynomial.monomial n ((massWeightPoly (a * b)).coeff n) := by
  rw [map_mul massWeightPoly a b, Polynomial.coeff_mul, map_sum massWeightPoly,
    map_sum (Polynomial.monomial n)]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  subst hp
  rw [map_mul massWeightPoly, ha p.1, hb p.2, Polynomial.monomial_mul_monomial]

/-- Homogeneity on the real part of the complexification, by induction over the
  symmetric algebra. -/
lemma massWeightPoly_coeff_massWeightPoly_one_tmul (n : ℕ) (b : JetAlgebra) :
    massWeightPoly ((massWeightPoly ((1 : ℂ) ⊗ₜ[ℝ] b)).coeff n) =
      Polynomial.monomial n ((massWeightPoly ((1 : ℂ) ⊗ₜ[ℝ] b)).coeff n) := by
  induction b using SymmetricAlgebra.induction generalizing n with
  | algebraMap r =>
    rw [show (1 : ℂ) ⊗ₜ[ℝ] (algebraMap ℝ JetAlgebra r) =
        algebraMap ℂ (ℂ ⊗[ℝ] JetAlgebra) (r : ℂ) from by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      rfl]
    rw [AlgHom.commutes, Polynomial.algebraMap_apply, Polynomial.coeff_C]
    split_ifs with h
    · subst h
      rw [AlgHom.commutes, Polynomial.algebraMap_apply, Polynomial.monomial_zero_left]
    · simp only [map_zero]
  | ι v => exact massWeightPoly_coeff_massWeightPoly_ι n v
  | mul a b ha hb =>
    rw [show (1 : ℂ) ⊗ₜ[ℝ] (a * b) = ((1 : ℂ) ⊗ₜ[ℝ] a) * ((1 : ℂ) ⊗ₜ[ℝ] b) from by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]]
    exact massWeightPoly_coeff_massWeightPoly_mul ha hb n
  | add a b ha hb =>
    rw [TensorProduct.tmul_add, map_add massWeightPoly, Polynomial.coeff_add,
      map_add massWeightPoly, ha n, hb n]
    exact (map_add (Polynomial.monomial n) _ _).symm

/-- The coefficients of a mass-weight polynomial are homogeneous: the coefficient
  of `X ^ n` in `massWeightPoly x` is sent by `massWeightPoly` to `X ^ n` times
  itself.

  This fails for a general `p : Polynomial (ℂ ⊗[ℝ] JetAlgebra)` in place of
  `massWeightPoly x`: for `p = Polynomial.monomial 5 1` it would say
  `1 = X ^ 5`. -/
lemma massWeightPoly_coeff_massWeightPoly (n : ℕ) (x : ℂ ⊗[ℝ] JetAlgebra) :
    massWeightPoly ((massWeightPoly x).coeff n) =
      Polynomial.monomial n ((massWeightPoly x).coeff n) := by
  induction x using TensorProduct.induction_on generalizing n with
  | zero => simp only [map_zero, Polynomial.coeff_zero]
  | add a b ha hb =>
    rw [map_add massWeightPoly, Polynomial.coeff_add, map_add massWeightPoly, ha n, hb n]
    exact (map_add (Polynomial.monomial n) _ _).symm
  | tmul c b =>
    rw [massWeightPoly_tmul, Polynomial.coeff_smul, map_smul,
      massWeightPoly_coeff_massWeightPoly_one_tmul n b, Polynomial.smul_monomial]


/-!

## B. The mass weight submodule

We combine the coefficents of `massWeightPoly` into a submodule.
-/


/-- The submodule of elements of mass weight `n`: those `x` whose mass-weight
  polynomial is `x * X ^ n`. -/
def massWeightSubmodule (n : ℕ) : Submodule ℂ (ℂ ⊗[ℝ] JetAlgebra) where
  carrier := {x | massWeightPoly x = Polynomial.monomial n x}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
    rw [ha, hb]
  zero_mem' := by simp
  smul_mem' c x hx := by
    simp only [Set.mem_setOf_eq, map_smul] at hx ⊢
    rw [hx, Polynomial.smul_monomial]

@[simp]
lemma mem_massWeightSubmodule {n : ℕ} {x : ℂ ⊗[ℝ] JetAlgebra} :
    x ∈ massWeightSubmodule n ↔ massWeightPoly x = Polynomial.monomial n x := Iff.rfl

/-- The generator `j` has mass weight `j.massWeight`. -/
lemma ofGenerator_mem_massWeightSubmodule (j : JetGenerators) :
    (1 : ℂ) ⊗ₜ[ℝ] ofGenerator j ∈ massWeightSubmodule j.massWeight :=
  massWeightPoly_ofGenerator j

/-- Mass weights add under multiplication, and `1` has mass weight zero. -/
instance : SetLike.GradedMonoid massWeightSubmodule where
  one_mem := by simp
  mul_mem {m n x y} hx hy := by
    simp only [mem_massWeightSubmodule, map_mul] at hx hy ⊢
    rw [hx, hy, Polynomial.monomial_mul_monomial]

/-- The coefficient of `X ^ n` in the mass-weight polynomial of `x` has mass
  weight `n`. -/
lemma coeff_massWeightPoly_mem_massWeightSubmodule (n : ℕ) (x : ℂ ⊗[ℝ] JetAlgebra) :
    (massWeightPoly x).coeff n ∈ massWeightSubmodule n :=
  massWeightPoly_coeff_massWeightPoly n x

/-!

## C. Evaluating the mass-weight polynomial

The mass-weight polynomial and the mass-weight scaling are two descriptions of the same
grading: evaluating the polynomial at a scalar gives the scaling by that scalar. Since a
polynomial with coefficients in an algebra over an infinite field is determined by its
values at the scalars, statements proved for one description transfer to the other.

-/

/-- Evaluating the mass-weight polynomial at a scalar is the mass-weight scaling by that
  scalar. Both send a generator of weight `w` to `c ^ w` times itself, and both are
  algebra maps. -/
lemma eval_massWeightPoly (c : ℂ) (x : ℂ ⊗[ℝ] JetAlgebra) :
    (massWeightPoly x).eval (algebraMap ℂ (ℂ ⊗[ℝ] JetAlgebra) c) = massWeightScale c x := by
  have h : (Polynomial.eval₂AlgHom (AlgHom.id ℂ (ℂ ⊗[ℝ] JetAlgebra))
      (algebraMap ℂ (ℂ ⊗[ℝ] JetAlgebra) c)
      (fun a => Commute.all a _)).comp massWeightPoly = massWeightScale c := by
    refine (AlgHom.liftEquiv ℝ ℂ JetAlgebra _).symm.injective ?_
    refine SymmetricAlgebra.algHom_ext
      (Module.Basis.ext JetComponentSpace.basis fun j => ?_)
    show (massWeightPoly ((1 : ℂ) ⊗ₜ[ℝ] ofGenerator j)).eval
        (algebraMap ℂ (ℂ ⊗[ℝ] JetAlgebra) c) =
      massWeightScale c ((1 : ℂ) ⊗ₜ[ℝ] ofGenerator j)
    rw [massWeightPoly_ofGenerator, massWeightScale_tmul_ofGenerator,
      Polynomial.eval_monomial, ← map_pow, ← Algebra.commutes, ← Algebra.smul_def]
  exact AlgHom.congr_fun h x

/-- Evaluating at a real scalar, where the scalar tower lets the same value be read either
  over `ℝ` or over `ℂ`. -/
lemma eval_massWeightPoly_ofReal (r : ℝ) (x : ℂ ⊗[ℝ] JetAlgebra) :
    (massWeightPoly x).eval (algebraMap ℝ (ℂ ⊗[ℝ] JetAlgebra) r) =
      massWeightScale (r : ℂ) x := by
  rw [IsScalarTower.algebraMap_apply ℝ ℂ (ℂ ⊗[ℝ] JetAlgebra) r, eval_massWeightPoly]
  rfl

/-!

## D. The mass weight of derivatives and of transformed elements

-/

open Matrix MatrixGroups

/-- The total derivative raises the mass weight by two: its mass-weight polynomial is
  `X ^ 2` times the coefficientwise total derivative. -/
lemma massWeightPoly_jetDeriv_baseChange (μ : Fin 1 ⊕ Fin 3) (x : ℂ ⊗[ℝ] JetAlgebra) :
    massWeightPoly (LinearMap.baseChange ℂ (jetDeriv μ) x) =
      Polynomial.X ^ 2 * Polynomial.mapCoeffs (LinearMap.baseChange ℂ (jetDeriv μ))
        (massWeightPoly x) := by
  refine Polynomial.ext_of_forall_eval_algebraMap (k := ℂ) fun c => ?_
  rw [eval_massWeightPoly, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_algebraMap_mapCoeffs, eval_massWeightPoly,
    massWeightScale_jetDeriv_baseChange, ← map_pow, ← Algebra.smul_def]

/-- The Lorentz action preserves mass weights: the mass-weight polynomial of a transformed
  element is the transform of its mass-weight polynomial. -/
lemma massWeightPoly_complexRepLorentzGroup (Λ : SL(2,ℂ)) (x : ℂ ⊗[ℝ] JetAlgebra) :
    massWeightPoly (complexRepLorentzGroup Λ x) =
      Polynomial.mapAlgHom (complexRepLorentzGroupAlgHom Λ) (massWeightPoly x) := by
  refine Polynomial.ext_of_forall_eval_algebraMap (k := ℝ) fun r => ?_
  have hmap : algebraMap ℝ (ℂ ⊗[ℝ] JetAlgebra) r =
      algebraMap ℂ (ℂ ⊗[ℝ] JetAlgebra) (r : ℂ) :=
    IsScalarTower.algebraMap_apply ℝ ℂ (ℂ ⊗[ℝ] JetAlgebra) r
  rw [hmap, eval_massWeightPoly, Polynomial.eval_algebraMap_mapAlgHom,
    eval_massWeightPoly, massWeightScale_ofReal_complexRepLorentzGroup]
  rfl

/-- Jets of constant gauge transformations act trivially on the B-boson factor, so they
  preserve the mass-weight polynomial outright. -/
lemma massWeightPoly_complexRepJetGaugeGroupI_ofConstant (g : GaugeGroupI)
    (x : ℂ ⊗[ℝ] JetAlgebra) :
    massWeightPoly (complexRepJetGaugeGroupI (JetGaugeGroupI.ofConstant g) x) =
      massWeightPoly x := by
  rw [complexRepJetGaugeGroupI_ofConstant]

TODO "Show invariance of the mass weights with repsect to the Lorentz group."

end JetAlgebra

end BBoson

end StandardModel
