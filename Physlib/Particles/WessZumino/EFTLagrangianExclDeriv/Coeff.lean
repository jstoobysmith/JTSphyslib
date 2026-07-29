/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Jinzheng Li, Nathaneal Sajan
-/
module

public import Physlib.Particles.WessZumino.EFTLagrangianExclDeriv.Basic
/-!

# The Wess-Zumino EFT Lagrangian without derivatives

## i. Overview

The Wess-Zumino theory is a simple field theory consisting
of a single left-handed Weyl fermion and a single complex scalar field.
Sometimes the complex scalar field is replaced by a pair of real scalar fields.

The theory is of physical interest, because it simple example of a theory
permitting a supersymmetry. In this file we don't consider the supersymmetric nature
of the theory.

-/

@[expose] public section

namespace WessZumino
namespace EFTLagrangianExclDeriv
noncomputable section

open Module Matrix
open MatrixGroups
open Complex
open TensorProduct
open CategoryTheory.MonoidalCategory
open Fermion

/-!

## The coefficent associated with a multiset of field generators



The below is AI slop, but it shows a useful way od defining the coefficent.

-/

def CoeffSubmodule (s : Multiset FieldGenerators) : Submodule ℂ EFTLagrangianExclDeriv :=
  Submodule.span ℂ (termOfList '' {l | Multiset.ofList l = s})

instance : SetLike.GradedMonoid CoeffSubmodule where
  one_mem := by simp [CoeffSubmodule, termOfList_nil]
  mul_mem s1 s2 V1 V2 hV1 hV2 := by
    have h := Submodule.mul_mem_mul hV1 hV2
    rw [CoeffSubmodule, CoeffSubmodule, Submodule.span_mul_span] at h
    refine Submodule.span_mono ?_ h
    rintro _ ⟨_, ⟨l1, hl1, rfl⟩, _, ⟨l2, hl2, rfl⟩, rfl⟩
    exact ⟨l1 ++ l2, by subst hl1; subst hl2; rfl, termOfList_append l1 l2⟩

open DirectSum

namespace CoeffSubmodule

/-- Transport `DirectSum.of` along an equality of degrees: two homogeneous components with
  equal degrees and equal underlying values are equal. -/
lemma of_eq {s t : Multiset FieldGenerators} (h : s = t)
    {x : CoeffSubmodule s} {y : CoeffSubmodule t}
    (hxy : (x : EFTLagrangianExclDeriv) = y) :
    DirectSum.of (fun u => CoeffSubmodule u) s x = DirectSum.of (fun u => CoeffSubmodule u) t y := by
  subst h
  exact congrArg _ (Subtype.ext hxy)

/-- The class of `termOfList l` in the direct sum of the coefficient submodules, placed
  in degree `↑l`. Note that the membership proof is definitional. -/
def ofList (l : List FieldGenerators) : ⨁ s, CoeffSubmodule s :=
  DirectSum.of (fun s => CoeffSubmodule s) ↑l
    ⟨termOfList l, Submodule.subset_span ⟨l, rfl, rfl⟩⟩

lemma ofList_nil : ofList [] = 1 := by
  simp [ofList, termOfList_nil]
  rfl

lemma ofList_append (l₁ l₂ : List FieldGenerators) :
     ofList (l₁ ++ l₂) = ofList l₁ * ofList l₂ := by
  rw [ofList, ofList, ofList, DirectSum.of_mul_of]
  exact of_eq rfl (by rw [SetLike.coe_gMul]; exact termOfList_append l₁ l₂)


/-- The image of a generator in the direct sum of the coefficient submodules,
  placed in degree `{g}`. -/
def ofGenerator (g : FieldGenerators) : ⨁ s, CoeffSubmodule s := ofList [g]

lemma ofGenerator_comm {g₁ g₂ : FieldGenerators} (h : [g₁]ₐ * [g₂]ₐ = [g₂]ₐ * [g₁]ₐ) :
    ofGenerator g₁ * ofGenerator g₂ = ofGenerator g₂ * ofGenerator g₁ := by
  rw [ofGenerator, ofGenerator, ← ofList_append, ← ofList_append]
  exact of_eq (Multiset.cons_swap g₁ g₂ 0) (by simp [termOfList, h])

lemma fermion_mul_fermion_add_swap (ψ₁ ψ₂ : FermionicGenerator) :
    [ψ₁]ₑ * [ψ₂]ₑ + [ψ₂]ₑ * [ψ₁]ₑ = 0 := by
  obtain ⟨x₁, h1⟩ := ofFieldGenerators_fermion_exists ψ₁
  obtain ⟨x₂, h2⟩ := ofFieldGenerators_fermion_exists ψ₂
  rw [h1, h2, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    ← TensorProduct.tmul_add]
  simp

lemma ofList_eq_zero {l : List FieldGenerators} (h : termOfList l = 0) : ofList l = 0 := by
  have hx : (⟨termOfList l, Submodule.subset_span ⟨l, rfl, rfl⟩⟩ : CoeffSubmodule ↑l) = 0 :=
    Subtype.ext h
  rw [ofList, hx, map_zero]

/-- Two `termOfList` classes with the same field content sum to zero as soon as the
  underlying terms do. -/
lemma ofList_add_ofList {l₁ l₂ : List FieldGenerators}
    (hp : (↑l₂ : Multiset FieldGenerators) = ↑l₁)
    (h : termOfList l₁ + termOfList l₂ = 0) : ofList l₁ + ofList l₂ = 0 := by
  have h2 : ofList l₂ = DirectSum.of (fun u => CoeffSubmodule u) ↑l₁
      ⟨termOfList l₂, Submodule.subset_span ⟨l₂, hp, rfl⟩⟩ := of_eq hp rfl
  have hsum : (⟨termOfList l₁, Submodule.subset_span ⟨l₁, rfl, rfl⟩⟩ +
      ⟨termOfList l₂, Submodule.subset_span ⟨l₂, hp, rfl⟩⟩ : CoeffSubmodule ↑l₁) = 0 :=
    Subtype.ext h
  rw [ofList, h2, ← map_add, hsum, map_zero]

lemma ofGenerator_fermion_sq (ψf : FermionicGenerator) :
    ofGenerator (.fermion ψf) * ofGenerator (.fermion ψf) = 0 := by
  rw [ofGenerator, ← ofList_append]
  exact ofList_eq_zero (by simp [termOfList])

lemma ofGenerator_fermion_add_swap (ψ₁ ψ₂ : FermionicGenerator) :
    ofGenerator (.fermion ψ₁) * ofGenerator (.fermion ψ₂) +
      ofGenerator (.fermion ψ₂) * ofGenerator (.fermion ψ₁) = 0 := by
  rw [ofGenerator, ofGenerator, ← ofList_append, ← ofList_append]
  exact ofList_add_ofList
    (by simpa using List.Perm.swap (FieldGenerators.fermion ψ₁) (.fermion ψ₂) [])
    (by simpa [termOfList] using fermion_mul_fermion_add_swap ψ₁ ψ₂)

/-- The decomposition map on the fermionic factor, sending each fermionic generator to
  its class in degree `{ψ}`. -/
noncomputable def decomposeExt : FermionicEFTExclDeriv →ₐ[ℂ] ⨁ s, CoeffSubmodule s :=
  ExteriorAlgebra.lift ℂ
    ⟨fermionicComponentBasis.constr ℂ (fun i => ofGenerator (.fermion i)), by
      intro m
      -- Generic ring/module lemmas restated locally so that their statements carry the
      -- direct sum's own instances; `rw` can then match where the library patterns cannot.
      have hexpand : ∀ f g : FermionicGenerator → ⨁ s, CoeffSubmodule s,
          (∑ i, f i) * ∑ j, g j = ∑ i, ∑ j, f i * g j := fun f g => Fintype.sum_mul_sum f g
      have hsmul : ∀ (a b : ℂ) (x y : ⨁ s, CoeffSubmodule s),
          (a • x) * (b • y) = (a * b) • (x * y) := fun a b x y => smul_mul_smul_comm a x b y
      have hcollect : ∀ (a : ℂ) (x y : ⨁ s, CoeffSubmodule s),
          a • x + a • y = a • (x + y) := fun a x y => (smul_add a x y).symm
      have hzero : ∀ a : ℂ, a • (0 : ⨁ s, CoeffSubmodule s) = 0 := fun a => smul_zero a
      rw [Basis.constr_apply_fintype, hexpand, ← Finset.sum_product']
      refine Finset.sum_involution (fun p _ => (p.2, p.1)) ?_ ?_
        (fun p _ => Finset.mem_univ _) (fun p _ => rfl)
      · intro p _
        rw [hsmul, hsmul, mul_comm (fermionicComponentBasis.equivFun m p.2)
          (fermionicComponentBasis.equivFun m p.1),
          hcollect, ofGenerator_fermion_add_swap, hzero]
      · intro p _ hne heq
        refine hne ?_
        have h1 : p.2 = p.1 := congrArg Prod.fst heq
        rw [hsmul, h1, ofGenerator_fermion_sq, hzero]⟩

/-- The subalgebra of the graded direct sum generated by the bosonic generator classes.
  It is commutative, which lets `SymmetricAlgebra.lift` target it. -/
noncomputable def bosonicAdjoin : Subalgebra ℂ (⨁ s, CoeffSubmodule s) :=
  Algebra.adjoin ℂ (Set.range fun g : ComplexScalarGenerator => ofGenerator (.cScalar g))

instance : IsMulCommutative bosonicAdjoin :=
  Algebra.isMulCommutative_adjoin ℂ (by
    rintro _ ⟨g, rfl⟩ _ ⟨g', rfl⟩
    exact ofGenerator_comm (cScalar_comm_cScalar g g'))

open scoped IsMulCommutative in
/-- The decomposition map on the bosonic factor. Since `SymmetricAlgebra.lift` requires a
  commutative target, we factor through `bosonicAdjoin`. -/
noncomputable def decomposeSym : ComplexScalarEFTExclDeriv →ₐ[ℂ] ⨁ s, CoeffSubmodule s :=
  bosonicAdjoin.val.comp <| SymmetricAlgebra.lift <|
    complexScalarComponentBasis.constr ℂ fun g =>
      (⟨ofGenerator (.cScalar g), Algebra.subset_adjoin (Set.mem_range_self g)⟩ : bosonicAdjoin)

lemma decomposeSym_mem_bosonicAdjoin (x : ComplexScalarEFTExclDeriv) :
    decomposeSym x ∈ bosonicAdjoin := by
  simp only [decomposeSym, AlgHom.coe_comp, Function.comp_apply, Subalgebra.coe_val]
  exact SetLike.coe_mem _

lemma decomposeExt_ι (v : FermionicComponentSpace) :
    decomposeExt (ExteriorAlgebra.ι ℂ v) =
      ∑ j, fermionicComponentBasis.equivFun v j • ofGenerator (.fermion j) := by
  rw [decomposeExt, ExteriorAlgebra.lift_ι_apply, Basis.constr_apply_fintype]

lemma commute_decomposeSym_decomposeExt
    (x : ComplexScalarEFTExclDeriv) (y : FermionicEFTExclDeriv) :
    Commute (decomposeSym x) (decomposeExt y) := by
  -- Every element of `bosonicAdjoin` commutes with the image of the fermionic factor;
  -- this avoids ever unfolding `decomposeSym`.
  have hgen : ∀ g : ComplexScalarGenerator,
      Commute (ofGenerator (.cScalar g)) (decomposeExt y) := by
    intro g
    induction y using ExteriorAlgebra.induction with
    | algebraMap c => rw [AlgHom.commutes]; exact (Algebra.commutes c _).symm
    | mul y₁ y₂ h₁ h₂ =>
      rw [map_mul]
      exact Commute.mul_right (a := ofGenerator (.cScalar g)) (b := decomposeExt y₁) h₁ h₂
    | add y₁ y₂ h₁ h₂ => rw [map_add]; exact h₁.add_right h₂
    | ι v =>
      rw [decomposeExt_ι]
      refine Commute.sum_right (b := ofGenerator (.cScalar g)) _ _ fun j _ => ?_
      refine Commute.smul_right (a := ofGenerator (.cScalar g)) ?_ _
      exact ofGenerator_comm (cScalar_comm_fermion g j)
  have hx := decomposeSym_mem_bosonicAdjoin x
  generalize decomposeSym x = a at hx ⊢
  induction hx using Algebra.adjoin_induction with
  | mem a ha => obtain ⟨g, rfl⟩ := ha; exact hgen g
  | algebraMap c => exact Algebra.commutes c _
  | add a b _ _ h₁ h₂ => exact h₁.add_left h₂
  | mul a b _ _ h₁ h₂ => exact Commute.mul_left (c := decomposeExt y) h₁ h₂

noncomputable def decompose' : EFTLagrangianExclDeriv →ₐ[ℂ] ⨁ s, CoeffSubmodule s :=
  Algebra.TensorProduct.lift decomposeSym decomposeExt commute_decomposeSym_decomposeExt

lemma decomposeSym_ι_basis (g : ComplexScalarGenerator) :
    decomposeSym (SymmetricAlgebra.ι ℂ _ (complexScalarComponentBasis g)) =
      ofGenerator (.cScalar g) := by
  simp only [decomposeSym, AlgHom.coe_comp, Function.comp_apply, SymmetricAlgebra.lift_ι_apply,
    Basis.constr_basis]
  rfl

lemma decomposeExt_ι_basis (g : FermionicGenerator) :
    decomposeExt (ExteriorAlgebra.ι ℂ (fermionicComponentBasis g)) =
      ofGenerator (.fermion g) := by
  rw [decomposeExt, ExteriorAlgebra.lift_ι_apply, Basis.constr_basis]

lemma decompose'_ofFieldGenerators (g : FieldGenerators) :
    decompose' [g]ₐ = ofGenerator g := by
  -- Local restatements of `mul_one`/`one_mul` carrying the direct sum's own instances.
  have hmul_one : ∀ x : ⨁ s, CoeffSubmodule s, x * 1 = x := fun x => mul_one x
  have hone_mul : ∀ x : ⨁ s, CoeffSubmodule s, 1 * x = x := fun x => one_mul x
  match g with
  | .cScalar g =>
    rw [decompose', show ([g]ₛ : EFTLagrangianExclDeriv) =
        SymmetricAlgebra.ι ℂ _ (complexScalarComponentBasis g) ⊗ₜ 1 from rfl,
      Algebra.TensorProduct.lift_tmul, map_one, hmul_one, decomposeSym_ι_basis]
  | .fermion g =>
    rw [decompose', show ([g]ₑ : EFTLagrangianExclDeriv) =
        1 ⊗ₜ ExteriorAlgebra.ι ℂ (fermionicComponentBasis g) from rfl,
      Algebra.TensorProduct.lift_tmul, map_one, hone_mul, decomposeExt_ι_basis]

lemma decompose'_termOfList (l : List FieldGenerators) :
    decompose' (termOfList l) = ofList l := by
  induction l with
  | nil => rw [termOfList_nil, map_one, ofList_nil]
  | cons g t ih =>
    rw [termOfList_cons, map_mul, ih, decompose'_ofFieldGenerators, ofGenerator,
      ← ofList_append, List.singleton_append]

lemma coeAlgHom_ofList (l : List FieldGenerators) :
    DirectSum.coeAlgHom CoeffSubmodule (ofList l) = termOfList l := by
  rw [ofList]
  exact DirectSum.coeAlgHom_of _ _ _

instance : GradedAlgebra CoeffSubmodule := by
  refine GradedAlgebra.ofAlgHom CoeffSubmodule decompose' ?_ ?_
  · refine AlgHom.ext fun x => ?_
    rw [AlgHom.comp_apply, AlgHom.id_apply]
    induction mem_termOfList_span x using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨l, rfl⟩ := ha
      rw [decompose'_termOfList]
      exact coeAlgHom_ofList l
    | zero => simp
    | add a b _ _ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
    | smul c a _ h₁ => rw [map_smul, map_smul, h₁]
  · intro s x
    obtain ⟨x, hx⟩ := x
    induction hx using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨l, hl, rfl⟩ := ha
      subst hl
      rw [decompose'_termOfList]
      rfl
    | zero => exact (map_zero (DirectSum.of (fun i => CoeffSubmodule i) s)).symm ▸ map_zero _
    | add a b ha hb h₁ h₂ => rw [map_add, h₁, h₂, ← map_add]; rfl
    | smul c a ha h₁ =>
      rw [map_smul, h₁, ← DirectSum.lof_eq_of ℂ, ← map_smul]; rfl


def coeff (s : Multiset FieldGenerators) : EFTLagrangianExclDeriv →ₗ[ℂ] EFTLagrangianExclDeriv:=
  GradedAlgebra.proj CoeffSubmodule s

end CoeffSubmodule

end EFTLagrangianExclDeriv
