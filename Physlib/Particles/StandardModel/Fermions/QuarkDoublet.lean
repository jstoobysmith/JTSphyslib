/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.Jet.Basic
public import Physlib.Particles.StandardModel.GaugeBosons.AlgebraValued.CovariantDeriv
public import Physlib.Relativity.Fermions.Weyl.LeftHanded
public import Physlib.Relativity.Fermions.Weyl.RightHanded
public import Physlib.Relativity.Fermions.Weyl.DualLeftHanded
public import Physlib.Relativity.Fermions.Weyl.DualRightHanded
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Analysis.Normed.Lp.Matrix
public import Mathlib.RingTheory.TensorProduct.Maps
/-!
# The type corresponding to quark doublets

In this module we define the type corresponding to
the target vector space of a quark field in the Standard Model.

On this type we define a representation of the Lorentz group, and a
representation of the Standard Model gauge group.

-/

@[expose] public section

namespace StandardModel

open TensorProduct

/-- The vector space of a quark field in the Standard Model.
  These live in the (3, 2)_{1} representation of the gauge group. -/
@[ext]
structure QuarkDoublet where
  /-- The underlying value of the quark field in the tensor product space. -/
  val : Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3) ⊗[ℂ] EuclideanSpace ℂ (Fin 2)

namespace QuarkDoublet

/-!

## Equivalence with the underlying tensor product space

-/

/-- The linear equivalence between `QuarkDoublet` and its underlying tensor product space. -/
def valEquiv : QuarkDoublet ≃
    Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3) ⊗[ℂ] EuclideanSpace ℂ (Fin 2) where
  toFun := val
  invFun := fun m => ⟨m⟩

/-!

## The structure of a module

The AddCommGroup and module instances are inherited from the underlying tensor product space.
-/

instance : AddCommGroup QuarkDoublet := Equiv.addCommGroup valEquiv

instance : Module ℂ QuarkDoublet := Equiv.module ℂ valEquiv

/-- The linear equivalence between `QuarkDoublet` and its underlying tensor product space. -/
def valLinEquiv : QuarkDoublet ≃ₗ[ℂ]
    Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3) ⊗[ℂ] EuclideanSpace ℂ (Fin 2) where
  toFun := val
  invFun := fun m => ⟨m⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp]
lemma valLinEquiv_apply (q : QuarkDoublet) : valLinEquiv q = q.val := rfl

lemma valLinEquiv_symm_apply
    (m : Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3) ⊗[ℂ] EuclideanSpace ℂ (Fin 2)) :
    valLinEquiv.symm m = ⟨m⟩ := rfl

@[simp]
lemma val_add (q1 q2 : QuarkDoublet) : (q1 + q2).val = q1.val + q2.val := rfl

@[simp]
lemma val_smul (r : ℂ) (q : QuarkDoublet) : (r • q).val = r • q.val := rfl


/-!

## The basis of the quark doublet space

-/

/-- A basis on the quark doublets. -/
noncomputable def basis : Module.Basis (Fin 2 × Fin 3 × Fin 2) ℂ QuarkDoublet :=
  ((((Fermion.LeftHandedWeyl.basis.tensorProduct
    (EuclideanSpace.basisFun (Fin 3) ℂ).toBasis).tensorProduct
    (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis).map valLinEquiv.symm).reindex
    (Equiv.prodAssoc (Fin 2) (Fin 3) (Fin 2)))

instance : Module.Finite ℂ QuarkDoublet := Module.Finite.of_basis basis

instance : Module.Free ℂ QuarkDoublet := Module.Free.of_basis basis

/-!

## Lorentz group representation

-/
open Matrix MatrixGroups

open Representation in
/-- The representation of the Lorentz group on the space of quark fields. -/
noncomputable def repLorentzGroup : Representation ℂ (SL(2,ℂ)) QuarkDoublet where
  toFun Λ :=  valLinEquiv.symm ∘ₗ
      TensorProduct.map
      (TensorProduct.map (Fermion.LeftHandedWeyl.rep Λ)
        (trivial ℂ (SL(2,ℂ)) (EuclideanSpace ℂ (Fin 3)) Λ))
        (trivial ℂ (SL(2,ℂ)) (EuclideanSpace ℂ (Fin 2)) Λ)
      ∘ₗ valLinEquiv
  map_one' := by
    ext q
    simp [Module.End.one_eq_id]
  map_mul' Λ1 Λ2 := by
    ext1 q
    simp [TensorProduct.map_map, ← TensorProduct.map_comp, Module.End.mul_eq_comp]

/-!

## The representation of the Standard Model gauge group

-/

/-- The action of the full Standard Model gauge group on quark fields. -/
noncomputable def repGaugeGroupI : Representation ℂ GaugeGroupI QuarkDoublet where
  toFun g := valLinEquiv.symm ∘ₗ
      TensorProduct.map
        (TensorProduct.map
        (LinearMap.id (M := Fermion.LeftHandedWeyl)) -- action on the Lorentz indices
        g.toSU3.1.toEuclideanLin) -- SU(3) action
        g.toSU2.1.toEuclideanLin  -- SU(2) action
      ∘ₗ LinearMap.lsmul ℂ _ (g.toU1 : ℂ) -- U(1) action
      ∘ₗ valLinEquiv
  map_one' := by
    ext q
    simp [valLinEquiv_symm_apply]
  map_mul' g1 g2 := by
    ext q
    simp [smul_smul, mul_comm, TensorProduct.map_map, ← TensorProduct.map_comp,
      valLinEquiv_symm_apply]

lemma repGaugeGroupI_tmul (g : GaugeGroupI) (ψ : Fermion.LeftHandedWeyl)
    (v : EuclideanSpace ℂ (Fin 3)) (w : EuclideanSpace ℂ (Fin 2)) :
    repGaugeGroupI g ⟨ψ ⊗ₜ v ⊗ₜ w⟩ = ⟨g.toU1 • ψ ⊗ₜ (g.toSU3.1.toEuclideanLin v) ⊗ₜ
      (g.toSU2.1.toEuclideanLin w)⟩ := rfl

open Fermion in
/-- The action of the full gauge group on a tensor product of basis elements, expanded as a
  sum over the columns of the `SU(3)` and `SU(2)` matrices. -/
lemma repGaugeGroupI_tmul_basis_eq_sum (g : GaugeGroupI) (k : Fin 2) (i : Fin 3) (j : Fin 2) :
    repGaugeGroupI g ⟨LeftHandedWeyl.basis k ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 3) ℂ i
      ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 2) ℂ j⟩ =
      ∑ i' : Fin 3, ∑ j' : Fin 2, (g.toU1.1 * g.toSU3.1 i' i * g.toSU2.1 j' j)
      • (⟨LeftHandedWeyl.basis k ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 3) ℂ i'
          ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 2) ℂ j'⟩ : QuarkDoublet) := by
  apply valLinEquiv.injective
  apply (((LeftHandedWeyl.basis).tensorProduct
    (EuclideanSpace.basisFun (Fin 3) ℂ).toBasis).tensorProduct
    (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis).repr.injective
  ext ⟨⟨k, l⟩, m⟩
  simp only [EuclideanSpace.basisFun_apply, repGaugeGroupI_tmul, Submonoid.smul_def,
    valLinEquiv_apply, map_smul, Finsupp.coe_smul, Pi.smul_apply,
    Module.Basis.tensorProduct_repr_tmul_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr, ofLp_toLpLin, PiLp.ofLp_single, toLin'_apply, mulVec_single,
    MulOpposite.op_one, col_apply, one_smul, Module.Basis.repr_self, smul_eq_mul, map_sum,
    Finsupp.coe_finsetSum, Finset.sum_apply, PiLp.single_apply, ite_mul, one_mul, zero_mul,
    mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
    Finset.sum_const_zero]
  ring

open Fermion in
lemma repGaugeGroupI_eq_iff_mul_eq {g1 g2 : GaugeGroupI} :
    repGaugeGroupI g1 = repGaugeGroupI g2 ↔ ∀ i i' j j',
    g1.toU1.1 * g1.toSU3.1 i' i * g1.toSU2.1 j' j =
    g2.toU1.1 * g2.toSU3.1 i' i * g2.toSU2.1 j' j := by
  let b := ((LeftHandedWeyl.basis).tensorProduct
      (EuclideanSpace.basisFun (Fin 3) ℂ).toBasis).tensorProduct
      (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis
  constructor
  · intro h i i' j j'
    have h' := congrFun (congrArg (fun f => f.1) h)
      ⟨LeftHandedWeyl.basis 0 ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 3) ℂ i
      ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 2) ℂ j⟩
    simp only [Fin.isValue, LinearMap.coe_toAddHom, repGaugeGroupI_tmul_basis_eq_sum] at h'
    replace h' := congrArg b.repr (congrArg valLinEquiv h')
    simpa [Module.Basis.tensorProduct_repr_tmul_apply, -Fin.sum_univ_two, b] using
      congrArg (fun f => f ((0, i'), j')) h'
  · intro h
    apply (valLinEquiv.symm.eq_comp_toLinearMap_iff (repGaugeGroupI g1) (repGaugeGroupI g2)).mp
    apply b.ext
    rintro ⟨⟨i, j⟩, k⟩
    have h1 := repGaugeGroupI_tmul_basis_eq_sum g1 i j k
    have h2 := repGaugeGroupI_tmul_basis_eq_sum g2 i j k
    simp only [EuclideanSpace.basisFun_apply, Fin.sum_univ_two, Fin.isValue] at h1 h2
    simp [valLinEquiv_symm_apply, h1, h2, b, h]

TODO "Improve the efficiency of `mem_repGaugeGroupI_ker_iff_eq` by removing the
  `grind`s and replacing them with a more direct argument."

lemma mem_repGaugeGroupI_ker_iff_eq {g : GaugeGroupI} :
    g ∈ repGaugeGroupI.ker ↔ ∃ a b : ℂ, g.toSU2.1 = a • 1 ∧ g.toSU3.1 = b • 1 ∧
      a * b * g.toU1.1 = 1 := by
  rw [MonoidHom.mem_ker, ← MonoidHom.map_one repGaugeGroupI, repGaugeGroupI_eq_iff_mul_eq]
  constructor; swap
  · rintro ⟨a, b, h1, h2, h3⟩ i i' j j'
    simp only [h2, Matrix.smul_apply, smul_eq_mul, h1, map_one, OneMemClass.coe_one, one_mul]
    linear_combination h3 * (1 : Matrix _ _ ℂ) i' i * (1 : Matrix  _ _ ℂ) j' j
  · intro h
    use g.toSU2.1 0 0, g.toSU3.1 0 0
    simp only [map_one, OneMemClass.coe_one, one_mul, Fin.forall_fin_succ, Fin.isValue,
      Fin.succ_zero_eq_one, IsEmpty.forall_iff, and_true, one_apply_eq, mul_one, ne_eq, one_ne_zero,
      not_false_eq_true, one_apply_ne, mul_zero, mul_eq_zero, zero_ne_one, Fin.succ_one_eq_two,
      Fin.reduceEq] at h
    refine ⟨?_, ?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp <;> grind
    · ext i j
      fin_cases i <;> fin_cases j <;> simp <;> grind (splits := 20)
    · grind

lemma gaugeGroup_subgroup_ℤ₆_le_ker_repGaugeGroupI :
    GaugeGroupQuot.subgroup .ℤ₆ ≤ repGaugeGroupI.ker := by
  simp only [SetLike.le_def, mem_repGaugeGroupI_ker_iff_eq,
    GaugeGroupQuot.subgroup, gaugeGroupℤ₆SubGroup, MonoidHom.mem_range,
    gaugeGroupℤ₆Hom_apply, Subtype.exists, exists_and_left, forall_exists_index]
  rintro g x hx ⟨rfl⟩
  use starRingEnd ℂ (x ^ 3)
  simp only [gaugeGroupℤ₆OfRoot_toSU2, gaugeGroupℤ₆SU2OfRoot_eq_mul_id, RCLike.star_def,
    Complex.conj_rootsOfUnity hx, Units.val_inv_eq_inv_val, inv_pow, map_pow,
    gaugeGroupℤ₆OfRoot_toSU3, gaugeGroupℤ₆SU3OfRoot_eq_mul_id, ne_eq, one_ne_zero,
    not_false_eq_true, smul_left_inj, gaugeGroupℤ₆OfRoot_toU1, gaugeGroupℤ₆UnitaryOfRoot_coe,
    exists_eq_left', true_and]
  field_simp

lemma gaugeGroup_subgroup_le_ker_repGaugeGroupI (Q : GaugeGroupQuot) :
    Q.subgroup ≤ repGaugeGroupI.ker := Q.subgroup_le_subgroup_ℤ₆.trans
  gaugeGroup_subgroup_ℤ₆_le_ker_repGaugeGroupI

/-- The action of the Standard Model gauge group, potentially quotiented by
  a discrete factor on quark fields. -/
noncomputable def repGaugeGroup : (Q : GaugeGroupQuot) →
    Representation ℂ (GaugeGroup Q) QuarkDoublet
  | .I => repGaugeGroupI
  | .ℤ₆ => QuotientGroup.lift _ repGaugeGroupI (gaugeGroup_subgroup_le_ker_repGaugeGroupI .ℤ₆)
  | .ℤ₂ => QuotientGroup.lift _ repGaugeGroupI (gaugeGroup_subgroup_le_ker_repGaugeGroupI .ℤ₂)
  | .ℤ₃ => QuotientGroup.lift _ repGaugeGroupI (gaugeGroup_subgroup_le_ker_repGaugeGroupI .ℤ₃)

/-!

## The representation of the jet gauge group

The colour and weak indices are combined into the single index `Fin 3 × Fin 2`, on which
the `SU(3)` and `SU(2)` power-series matrices of a jet of gauge transformations act
together through their Kronecker product, scaled by the hypercharge power series `u`.

-/

open Kronecker

/-- The colour and weak factors of the quark doublet combined into a single Euclidean
factor over `Fin 3 × Fin 2`. -/
noncomputable def colourWeakEquiv :
    EuclideanSpace ℂ (Fin 3) ⊗[ℂ] EuclideanSpace ℂ (Fin 2) ≃ₗ[ℂ] (Fin 3 × Fin 2 → ℂ) :=
  (TensorProduct.congr (WithLp.linearEquiv 2 ℂ (Fin 3 → ℂ))
      (WithLp.linearEquiv 2 ℂ (Fin 2 → ℂ))).trans <|
    (TensorProduct.piScalarRight ℂ ℂ (Fin 3 → ℂ) (Fin 2)).trans <|
      (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 3)).symm.trans <|
        LinearEquiv.piCongrLeft' ℂ (fun _ => ℂ) (Equiv.prodComm (Fin 2) (Fin 3))

@[simp]
lemma colourWeakEquiv_tmul (c : EuclideanSpace ℂ (Fin 3)) (w : EuclideanSpace ℂ (Fin 2))
    (p : Fin 3 × Fin 2) :
    colourWeakEquiv (c ⊗ₜ[ℂ] w) p = c.ofLp p.1 * w.ofLp p.2 := by
  simp [colourWeakEquiv, Function.uncurry, Algebra.algebraMap_eq_smul_one, mul_comm]

/-- Absorbs the jet ring into the combined colour–weak index: a jet of a quark doublet is
the same thing as a left-handed Weyl spinor tensored with a `JetRing`-valued
colour–weak vector,

  `JetRing ⊗[ℂ] QuarkDoublet ≃ LeftHandedWeyl ⊗[ℂ] EuclideanSpace JetRing (Fin 3 × Fin 2)`.

-/
noncomputable def jetValLinEquiv :
    JetRing ⊗[ℂ] QuarkDoublet ≃ₗ[ℂ]
      Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace JetRing (Fin 3 × Fin 2) :=
  (TensorProduct.congr (LinearEquiv.refl ℂ JetRing)
      (valLinEquiv.trans (TensorProduct.assoc ℂ Fermion.LeftHandedWeyl
        (EuclideanSpace ℂ (Fin 3)) (EuclideanSpace ℂ (Fin 2))))).trans <|
    (TensorProduct.leftComm ℂ JetRing Fermion.LeftHandedWeyl
        (EuclideanSpace ℂ (Fin 3) ⊗[ℂ] EuclideanSpace ℂ (Fin 2))).trans <|
      TensorProduct.congr (LinearEquiv.refl ℂ Fermion.LeftHandedWeyl) <|
        (TensorProduct.congr (LinearEquiv.refl ℂ JetRing) colourWeakEquiv).trans <|
          ((TensorProduct.piScalarRight ℂ JetRing JetRing (Fin 3 × Fin 2)).trans
            (WithLp.linearEquiv 2 JetRing (Fin 3 × Fin 2 → JetRing)).symm).restrictScalars ℂ

/-- The matrix of jets through which a jet of gauge transformations acts on the combined
colour–weak index of the quark doublet: the Kronecker product of the `SU(3)` and `SU(2)`
power-series matrices, scaled by the hypercharge power series `u`. -/
noncomputable def jetGaugeMatrix (U : JetGaugeGroupI) :
    Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) JetRing :=
  ((U.2.2 : unitary JetRing) : JetRing) •
    (((U.1 : specialUnitaryGroup (Fin 3) JetRing) : Matrix (Fin 3) (Fin 3) JetRing) ⊗ₖ
      ((U.2.1 : specialUnitaryGroup (Fin 2) JetRing) : Matrix (Fin 2) (Fin 2) JetRing))

lemma jetGaugeMatrix_one : jetGaugeMatrix 1 = 1 := by
  rw [jetGaugeMatrix,
    show (((1 : JetGaugeGroupI).2.2 : unitary JetRing) : JetRing) = 1 from rfl,
    show ((((1 : JetGaugeGroupI).1 : specialUnitaryGroup (Fin 3) JetRing)) :
      Matrix (Fin 3) (Fin 3) JetRing) = 1 from rfl,
    show ((((1 : JetGaugeGroupI).2.1 : specialUnitaryGroup (Fin 2) JetRing)) :
      Matrix (Fin 2) (Fin 2) JetRing) = 1 from rfl,
    Matrix.one_kronecker_one, one_smul]

lemma jetGaugeMatrix_mul (U₁ U₂ : JetGaugeGroupI) :
    jetGaugeMatrix (U₁ * U₂) = jetGaugeMatrix U₁ * jetGaugeMatrix U₂ := by
  rw [jetGaugeMatrix, jetGaugeMatrix, jetGaugeMatrix,
    show (((U₁ * U₂).2.2 : unitary JetRing) : JetRing) =
      ((U₁.2.2 : unitary JetRing) : JetRing) * ((U₂.2.2 : unitary JetRing) : JetRing) from rfl,
    show (((U₁ * U₂).1 : specialUnitaryGroup (Fin 3) JetRing) :
        Matrix (Fin 3) (Fin 3) JetRing) =
      ((U₁.1 : specialUnitaryGroup (Fin 3) JetRing) : Matrix (Fin 3) (Fin 3) JetRing) *
        ((U₂.1 : specialUnitaryGroup (Fin 3) JetRing) : Matrix (Fin 3) (Fin 3) JetRing)
      from rfl,
    show (((U₁ * U₂).2.1 : specialUnitaryGroup (Fin 2) JetRing) :
        Matrix (Fin 2) (Fin 2) JetRing) =
      ((U₁.2.1 : specialUnitaryGroup (Fin 2) JetRing) : Matrix (Fin 2) (Fin 2) JetRing) *
        ((U₂.2.1 : specialUnitaryGroup (Fin 2) JetRing) : Matrix (Fin 2) (Fin 2) JetRing)
      from rfl,
    Matrix.mul_kronecker_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

/-- The `(3, 2)_{1}` action of the jet gauge group on the jet space of the quark doublet.
Through `jetValLinEquiv` the Kronecker matrix of the gauge jet, carrying the hypercharge
phase `u`, acts `JetRing`-linearly on the combined colour–weak factor by matrix-vector
multiplication, while the Weyl factor is untouched. -/
noncomputable def repJetGaugeGroupI :
    Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] QuarkDoublet) where
  toFun U :=
    jetValLinEquiv.symm.toLinearMap ∘ₗ
      Module.End.lTensorAlgHom ℂ (EuclideanSpace JetRing (Fin 3 × Fin 2))
        Fermion.LeftHandedWeyl
        ((Matrix.toLpLinAlgEquiv 2 (jetGaugeMatrix U)).restrictScalars ℂ) ∘ₗ
      jetValLinEquiv.toLinearMap
  map_one' := by
    have hres : (1 : Module.End JetRing
        (EuclideanSpace JetRing (Fin 3 × Fin 2))).restrictScalars ℂ = 1 := rfl
    rw [jetGaugeMatrix_one, map_one, hres, map_one]
    ext d x
    simp [-valLinEquiv_apply]
  map_mul' U₁ U₂ := by
    have hres : ∀ f g : Module.End JetRing (EuclideanSpace JetRing (Fin 3 × Fin 2)),
        (f * g).restrictScalars ℂ = f.restrictScalars ℂ * g.restrictScalars ℂ :=
      fun _ _ => rfl
    rw [jetGaugeMatrix_mul, map_mul, hres, map_mul]
    ext d x
    simp

/-- The entries of the gauge matrix of a jet of a constant gauge transformation are the
constant power series with the global gauge coefficients. -/
lemma jetGaugeMatrix_ofConstant (g : GaugeGroupI) (p q : Fin 3 × Fin 2) :
    jetGaugeMatrix (JetGaugeGroupI.ofConstant g) p q =
      MvPowerSeries.C ((g.toU1.1 : ℂ) * (g.toSU3.1 p.1 q.1 * g.toSU2.1 p.2 q.2)) := by
  rw [jetGaugeMatrix, Matrix.smul_apply,
    show (((JetGaugeGroupI.ofConstant g).2.2 : unitary JetRing) : JetRing) =
      MvPowerSeries.C ((g.toU1.1 : ℂ)) from rfl]
  rw [Matrix.kroneckerMap_apply,
    show (((JetGaugeGroupI.ofConstant g).1 : specialUnitaryGroup (Fin 3) JetRing) :
        Matrix (Fin 3) (Fin 3) JetRing) p.1 q.1 =
      MvPowerSeries.C (g.toSU3.1 p.1 q.1) from rfl,
    show (((JetGaugeGroupI.ofConstant g).2.1 : specialUnitaryGroup (Fin 2) JetRing) :
        Matrix (Fin 2) (Fin 2) JetRing) p.2 q.2 =
      MvPowerSeries.C (g.toSU2.1 p.2 q.2) from rfl,
    smul_eq_mul, ← map_mul, ← map_mul]

/-- The identification of the jets of the quark doublet intertwines multiplication by a
scalar jet with the `JetRing`-scalar action on the colour–weak coordinates. -/
lemma jetValLinEquiv_smul (χ : JetRing) (z : JetRing ⊗[ℂ] QuarkDoublet) :
    jetValLinEquiv (χ • z)
      = Module.End.lTensorAlgHom ℂ (EuclideanSpace JetRing (Fin 3 × Fin 2))
          Fermion.LeftHandedWeyl
          ((LinearMap.lsmul JetRing
            (EuclideanSpace JetRing (Fin 3 × Fin 2)) χ).restrictScalars ℂ)
          (jetValLinEquiv z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [smul_add, map_add, ha, hb, map_add, map_add]
  | tmul f x =>
    obtain ⟨v⟩ := x
    induction v using TensorProduct.induction_on with
    | zero =>
      rw [show ({ val := 0 } : QuarkDoublet) = 0 from rfl, TensorProduct.tmul_zero,
        smul_zero, map_zero, map_zero]
    | tmul vc w =>
      induction vc using TensorProduct.induction_on with
      | zero =>
        rw [show ({ val := (0 : Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3))
            ⊗ₜ[ℂ] w } : QuarkDoublet) = 0 from by
          rw [TensorProduct.zero_tmul]; rfl, TensorProduct.tmul_zero, smul_zero,
          map_zero, map_zero]
      | tmul ψ c =>
        rw [TensorProduct.smul_tmul', smul_eq_mul,
          show jetValLinEquiv ((χ * f) ⊗ₜ[ℂ] (⟨ψ ⊗ₜ[ℂ] c ⊗ₜ[ℂ] w⟩ : QuarkDoublet))
            = ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun q =>
                colourWeakEquiv (c ⊗ₜ[ℂ] w) q • (χ * f)) from rfl,
          show jetValLinEquiv (f ⊗ₜ[ℂ] (⟨ψ ⊗ₜ[ℂ] c ⊗ₜ[ℂ] w⟩ : QuarkDoublet))
            = ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun q =>
                colourWeakEquiv (c ⊗ₜ[ℂ] w) q • f) from rfl,
          show Module.End.lTensorAlgHom ℂ (EuclideanSpace JetRing (Fin 3 × Fin 2))
              Fermion.LeftHandedWeyl
              ((LinearMap.lsmul JetRing
                (EuclideanSpace JetRing (Fin 3 × Fin 2)) χ).restrictScalars ℂ)
              (ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun q => colourWeakEquiv (c ⊗ₜ[ℂ] w) q • f))
            = ψ ⊗ₜ[ℂ] (χ • WithLp.toLp 2 fun q =>
                colourWeakEquiv (c ⊗ₜ[ℂ] w) q • f) from rfl]
        congr 1
        refine WithLp.ofLp_injective 2 ?_
        funext q
        show colourWeakEquiv (c ⊗ₜ[ℂ] w) q • (χ * f)
          = χ * (colourWeakEquiv (c ⊗ₜ[ℂ] w) q • f)
        rw [Algebra.mul_smul_comm]
      | add a b ha hb =>
        rw [show ({ val := (a + b) ⊗ₜ[ℂ] w } : QuarkDoublet)
            = ⟨a ⊗ₜ[ℂ] w⟩ + ⟨b ⊗ₜ[ℂ] w⟩ from by
          rw [show (⟨a ⊗ₜ[ℂ] w⟩ + ⟨b ⊗ₜ[ℂ] w⟩ : QuarkDoublet)
              = ⟨a ⊗ₜ[ℂ] w + b ⊗ₜ[ℂ] w⟩ from rfl, TensorProduct.add_tmul],
          TensorProduct.tmul_add, smul_add, map_add, ha, hb, map_add, map_add]
    | add a b ha hb =>
      rw [show ({ val := a + b } : QuarkDoublet) = ⟨a⟩ + ⟨b⟩ from rfl,
        TensorProduct.tmul_add, smul_add, map_add, ha, hb, map_add, map_add]

/-- **The jet gauge action on the jets of the quark doublet is fibrewise**: it commutes
with multiplication by scalar jets. -/
lemma repJetGaugeGroupI_smul (U : JetGaugeGroupI) (χ : JetRing)
    (z : JetRing ⊗[ℂ] QuarkDoublet) :
    repJetGaugeGroupI U (χ • z) = χ • repJetGaugeGroupI U z := by
  set S : Module.End JetRing (EuclideanSpace JetRing (Fin 3 × Fin 2)) :=
    LinearMap.lsmul JetRing (EuclideanSpace JetRing (Fin 3 × Fin 2)) χ with hS
  set M : Module.End JetRing (EuclideanSpace JetRing (Fin 3 × Fin 2)) :=
    (Matrix.toLpLinAlgEquiv 2 (jetGaugeMatrix U) :
      Module.End JetRing (EuclideanSpace JetRing (Fin 3 × Fin 2))) with hM
  have hMS : M * S = S * M := LinearMap.ext fun e => by
    simp only [Module.End.mul_apply, hS, LinearMap.lsmul_apply, map_smul]
  apply jetValLinEquiv.injective
  rw [show repJetGaugeGroupI U (χ • z)
      = jetValLinEquiv.symm (Module.End.lTensorAlgHom ℂ _ Fermion.LeftHandedWeyl
          (M.restrictScalars ℂ) (jetValLinEquiv (χ • z))) from rfl,
    LinearEquiv.apply_symm_apply, jetValLinEquiv_smul,
    show repJetGaugeGroupI U z
      = jetValLinEquiv.symm (Module.End.lTensorAlgHom ℂ _ Fermion.LeftHandedWeyl
          (M.restrictScalars ℂ) (jetValLinEquiv z)) from rfl,
    jetValLinEquiv_smul, LinearEquiv.apply_symm_apply, ← Module.End.mul_apply,
    ← Module.End.mul_apply, ← map_mul, ← map_mul,
    show M.restrictScalars ℂ * S.restrictScalars ℂ = (M * S).restrictScalars ℂ from rfl,
    show S.restrictScalars ℂ * M.restrictScalars ℂ = (S * M).restrictScalars ℂ from rfl,
    hMS]

/-- On jets of constant gauge transformations the jet action reduces to the global gauge
action on the fibre: the `(3, 2)_{1}` action on the quark-doublet factor, and the trivial
action on the jet ring. -/
lemma repJetGaugeGroupI_ofConstant (g : GaugeGroupI) :
    repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) =
      TensorProduct.map LinearMap.id (repGaugeGroupI g) := by
  ext d x
  obtain ⟨v⟩ := x
  induction v using TensorProduct.induction_on with
  | zero => simp [show ({ val := 0 } : QuarkDoublet) = 0 from rfl]
  | tmul vc w =>
      induction vc using TensorProduct.induction_on with
      | zero =>
          have h : ({ val := (0 : Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3))
              ⊗ₜ[ℂ] w } : QuarkDoublet) = 0 := by
            rw [TensorProduct.zero_tmul]
            rfl
          rw [h]
          simp
      | tmul psi c =>
          apply jetValLinEquiv.injective
          simp [repJetGaugeGroupI, jetValLinEquiv, repGaugeGroupI]
          have halg : ∀ A : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) JetRing,
              (Matrix.toLpLinAlgEquiv 2 A :
                  Module.End JetRing (EuclideanSpace JetRing (Fin 3 × Fin 2)))
                = Matrix.toLpLin 2 2 A := fun _ => rfl
          rw [TensorProduct.liftAux_tmul]
          simp only [LinearMap.compl₂_apply, TensorProduct.mk_apply, LinearMap.smul_apply,
            LinearMap.restrictScalars_apply, halg, Matrix.toLpLin_toLp]
          rw [← TensorProduct.tmul_smul]
          congr 1
          refine WithLp.ofLp_injective 2 ?_
          funext p
          simp only [WithLp.ofLp_smul, Pi.smul_apply, Matrix.toLin'_apply,
            Matrix.mulVec_apply_eq_sum, jetGaugeMatrix_ofConstant, Algebra.smul_def,
            MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self_apply]
          rw [Finset.sum_congr rfl fun q _ => by
            rw [show MvPowerSeries.C ((g.toU1.1 : ℂ) * (g.toSU3.1 p.1 q.1 * g.toSU2.1 p.2 q.2))
                  * (MvPowerSeries.C (c.ofLp q.1 * w.ofLp q.2) * d)
                = MvPowerSeries.C ((g.toU1.1 : ℂ) * (g.toSU3.1 p.1 q.1 * g.toSU2.1 p.2 q.2)
                    * (c.ofLp q.1 * w.ofLp q.2)) * d from by
              rw [← mul_assoc, ← map_mul]], ← Finset.sum_mul, ← map_sum]
          rw [← mul_assoc, ← map_mul]
          congr 1
          rw [Fintype.sum_prod_type,
            show (∑ j, g.toSU3.1 p.1 j * c.ofLp j) * (∑ j, g.toSU2.1 p.2 j * w.ofLp j)
                = ∑ i, ∑ j, (g.toSU3.1 p.1 i * c.ofLp i) * (g.toSU2.1 p.2 j * w.ofLp j) from
              Finset.sum_mul_sum _ _ _ _, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      | add a b ha hb =>
          simp only [show ({ val := (a + b) ⊗ₜ[ℂ] w } : QuarkDoublet)
              = ⟨a ⊗ₜ[ℂ] w⟩ + ⟨b ⊗ₜ[ℂ] w⟩ from by
            rw [show (⟨a ⊗ₜ[ℂ] w⟩ + ⟨b ⊗ₜ[ℂ] w⟩ : QuarkDoublet)
                = ⟨a ⊗ₜ[ℂ] w + b ⊗ₜ[ℂ] w⟩ from rfl, TensorProduct.add_tmul],
            map_add, ha, hb]
  | add a b ha hb =>
      simp only [show ({ val := a + b } : QuarkDoublet) = ⟨a⟩ + ⟨b⟩ from rfl,
        map_add, ha, hb]

end QuarkDoublet

end StandardModel
