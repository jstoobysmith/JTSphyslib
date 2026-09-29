/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Invariants.IsLeftRightWeyl
public import Physlib.Relativity.LorentzGroup.Invariants.RankTwo
public import Physlib.Relativity.PauliMatrices.ToTensor
public import Physlib.Relativity.LorentzGroup.Invariants.LorentzEquivariant
/-!
# Lorentz invariants of a four-vector index and a left-right Weyl pair

A family `T^{μ α α'}` carrying one four-vector index and one opposite-chirality Weyl pair is an
equivariant linear map `f : ℂT[.up, .upL, .upR] →ₗ[ℂ] B`, `IsVectorLeftRightWeyl` (A). Every
Lorentz invariant in the range of `f` is a multiple of `f σ^^^`, the image of the Pauli
matrices as a tensor, the shape of the fermion kinetic term `ψ̄_{α'} σ̄^{μ α' α} ∂_μ ψ_α`. That is
`IsVectorLeftRightWeyl.exists_smul_map_pauliMatrix_add_of_invariant`, stated modulo a
Lorentz-stable submodule `S`, and packaged as `IsVectorLeftRightWeyl.invariantReductionToSpan`
(D).

An opposite-chirality Weyl pair carries the `(1/2, 1/2)` representation, which is the
four-vector representation, so the three indices are two four-vector indices, and two of those
admit only the metric trace. The proof makes that literal. The components
`f (e_μ ⊗ e_α ⊗ e_α')` of `f` move as `T^{μ α α'}` (B); contracting their Weyl pair against the
covariant Pauli matrices `PauliMatrix.pauliLower`, which intertwine the two index laws
(`SL2C.sum_pauliLower_mul_sl2c`), gives a rank-two Lorentz family `vectorPair f`, whose span is
the range of `f` by Fierz completeness and whose metric contraction is `f σ^^^` (C); `RankTwo`
supplies the classification (D). A family of components is turned back into a map by
`ofVectorComponents` (E).

The Standard Model's fermion symbols are `Module.Dual`-valued, so their spinor indices carry
the dual laws `(g⁻¹)ᵀ` and `(g⁻¹)ᴴ` (F). Re-indexing the two spinor slots by the symplectic
form `ε`, `epsReindex`, converts them into the fundamental laws for the same
representation; no conjugation twist is needed, the mixed law already carrying one conjugate
factor and `ε` having real entries, and the vector slot keeps the plain Lorentz law. The image of
`σ^^^` under the map with the re-indexed components is the contraction `pauliBarContraction`
against the transposed Pauli matrices, with scalar `+1` (G, H). A dual pair with no vector index
has no invariant at all (H).
-/

@[expose] public section

namespace Lorentz

open TensorProduct Matrix MatrixGroups SL2C complexLorentzTensor

/-!

## A. Vector-Weyl families as equivariant maps

-/

/-- A family with a four-vector index and a left- and a right-handed Weyl index `T^{μ α α'}`:
  an equivariant linear map out of `ℂT[.up, .upL, .upR]`. -/
abbrev IsVectorLeftRightWeyl (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B) (f : ℂT[.up, .upL, .upR] →ₗ[ℂ] B) : Prop :=
  IsLorentzEquivariant ![.up, .upL, .upR] B repLorentz f

namespace IsVectorLeftRightWeyl

open PauliMatrix

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B} {f : ℂT[.up, .upL, .upR] →ₗ[ℂ] B}
  (hf : IsVectorLeftRightWeyl B repLorentz f)

/-!

## B. The components of an equivariant map

The components `f (e_μ ⊗ e_α ⊗ e_α')` of an equivariant map are moved by the Lorentz matrix on
the vector index, by the matrix of `g` on the left Weyl index and by its complex conjugate on
the right one.

-/

include hf in
/-- The components of an equivariant map are moved as `T^{μ α α'}`, the summed index first in
  each factor. -/
lemma repLorentz_map_indexBasis (g : SL(2,ℂ)) (d : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2) :
    repLorentz g (f (indexBasis d)) = ∑ e : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2,
      ((((SL2C.toLorentzGroup g).1 e.1 d.1 : ℝ) : ℂ)
        * (g.1 e.2.1 d.2.1 * star (g.1 e.2.2 d.2.2))) • f (indexBasis e) := by
  rw [indexBasis_apply, ← hf.equivariant, smul_basis_eq_sum, map_sum,
    ← indexEquiv.symm.sum_comp]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_smul, Fin.prod_univ_three, mul_assoc, indexBasis_apply]
  exact congrArg (· • _) (congrArg₂ (· * ·) (toMatrix_rep_up_apply g e.1 d.1)
    (congrArg₂ (· * ·) (congrFun (congrFun (toMatrix_rep_upL g) e.2.1) d.2.1)
      (congrFun (congrFun (toMatrix_rep_upR g) e.2.2) d.2.2)))

include hf in
/-- Moving a contraction of the Weyl pair at vector index `μ`: the vector index moves by the
  Lorentz matrix and the coefficient function by `IsLeftRightWeyl.act g`. -/
lemma repLorentz_sum_smul (g : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) (c : Fin 2 × Fin 2 → ℂ) :
    repLorentz g (∑ a : Fin 2 × Fin 2, c a • f (indexBasis (μ, a)))
      = ∑ ν : Fin 1 ⊕ Fin 3, (((SL2C.toLorentzGroup g).1 ν μ : ℝ) : ℂ)
        • ∑ q : Fin 2 × Fin 2, IsLeftRightWeyl.act g c q • f (indexBasis (ν, q)) := by
  rw [(repLorentz g).map_sum_smul_of_forall_eq (fun a => f (indexBasis (μ, a)))
    (fun e => f (indexBasis e))
    (fun e a => (((SL2C.toLorentzGroup g).1 e.1 μ : ℝ) : ℂ)
      * (g.1 e.2.1 a.1 * star (g.1 e.2.2 a.2)))
    (fun a => hf.repLorentz_map_indexBasis g (μ, a)) c, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [smul_smul, IsLeftRightWeyl.act, Finset.mul_sum]
  exact congrArg (· • f (indexBasis (ν, q))) (Finset.sum_congr rfl fun p _ => by ring)

/-!

## C. The reduction to a pair of four-vector indices

Contracting the Weyl pair of the components against the covariant Pauli matrices gives a
family `vectorPair f` of two four-vector indices, which is a rank-two Lorentz family. By Fierz
completeness the contraction is invertible, so its span is the range of `f`, and its metric
contraction is `f σ^^^`.

-/

/-- The family of two four-vector indices obtained by contracting the Weyl pair of the
  components of `f` against the covariant Pauli matrices. -/
noncomputable def vectorPair (f : ℂT[.up, .upL, .upR] →ₗ[ℂ] B) :
    (Fin 2 → Fin 1 ⊕ Fin 3) → B :=
  fun d => ∑ a : Fin 2 × Fin 2, PauliMatrix.pauliLower (d 1) a.1 a.2 • f (indexBasis (d 0, a))

include hf in
/-- The reduced family is a rank-two Lorentz family: the intertwining identity
  `SL2C.sum_pauliLower_mul_sl2c` carries the Weyl pair into a second vector index. -/
lemma isLorentzCovariant_vectorPair : IsLorentzCovariant 2 B repLorentz (vectorPair f) where
  repLorentz_T g l := by
    rw [vectorPair, hf.repLorentz_sum_smul, sum_pi_fin_two]
    refine Finset.sum_congr rfl fun ν _ => ?_
    simp only [IsLeftRightWeyl.act, sum_pauliLower_mul_sl2c]
    rw [Fintype.sum_sum_mul_smul
      (fun (q : Fin 2 × Fin 2) (ρ : Fin 1 ⊕ Fin 3) => PauliMatrix.pauliLower ρ q.1 q.2)
      (fun ρ => (((SL2C.toLorentzGroup g).1 ρ (l 1) : ℝ) : ℂ))
      (fun q => f (indexBasis (ν, q))), Finset.smul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    simp only [vectorPair, smul_smul, Fin.prod_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]

/-- The reduction is invertible: by the Fierz completeness relation each component of `f` is
  recovered from the reduced family. -/
lemma map_indexBasis_eq_sum_vectorPair (f : ℂT[.up, .upL, .upR] →ₗ[ℂ] B)
    (μ : Fin 1 ⊕ Fin 3) (b : Fin 2 × Fin 2) :
    f (indexBasis (μ, b)) = ∑ ρ : Fin 1 ⊕ Fin 3,
      ((2 : ℂ)⁻¹ * PauliMatrix.pauliLower ρ b.2 b.1) • vectorPair f ![μ, ρ] := by
  calc f (indexBasis (μ, b)) = ∑ a : Fin 2 × Fin 2,
        ((if a.1 = b.1 then (1 : ℂ) else 0) * (if a.2 = b.2 then 1 else 0))
          • f (indexBasis (μ, a)) := by
        rw [Fintype.sum_prod_type]
        simp [ite_smul, Finset.sum_ite_eq']
    _ = ∑ a : Fin 2 × Fin 2, (∑ ρ : Fin 1 ⊕ Fin 3,
          (2 : ℂ)⁻¹ * PauliMatrix.pauliLower ρ b.2 b.1 * PauliMatrix.pauliLower ρ a.1 a.2)
            • f (indexBasis (μ, a)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        congr 1
        rw [show (∑ ρ : Fin 1 ⊕ Fin 3,
              (2 : ℂ)⁻¹ * PauliMatrix.pauliLower ρ b.2 b.1 * PauliMatrix.pauliLower ρ a.1 a.2)
            = (2 : ℂ)⁻¹ * ∑ ρ : Fin 1 ⊕ Fin 3,
              PauliMatrix.pauliLower ρ b.2 b.1 * PauliMatrix.pauliLower ρ a.1 a.2 from by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun ρ _ => (mul_assoc _ _ _),
          PauliMatrix.sum_pauliLower_mul_pauliLower a.1 a.2 b.1 b.2]
        field_simp
    _ = _ := by
        simp only [vectorPair, Matrix.cons_val_zero, Matrix.cons_val_one,
          Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_smul

/-- The reduction does not change the span: the reduced family spans the range of `f`. -/
lemma span_range_vectorPair (f : ℂT[.up, .upL, .upR] →ₗ[ℂ] B) :
    Submodule.span ℂ (Set.range (vectorPair f)) = LinearMap.range f := by
  refine le_antisymm (Submodule.span_le.2 <| Set.range_subset_iff.2 fun d =>
    sum_mem fun a _ => Submodule.smul_mem _ _ (LinearMap.mem_range_self f _)) ?_
  rw [← Submodule.map_top, ← indexBasis.span_eq, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨⟨μ, b⟩, rfl⟩, rfl⟩
  rw [map_indexBasis_eq_sum_vectorPair]
  exact sum_mem fun ρ _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- The metric contraction of the reduced family is the image `f σ^^^` of the Pauli tensor: the
  two lowerings of the vector index cancel, so no sign and no scalar appear. -/
lemma metricContraction_vectorPair (f : ℂT[.up, .upL, .upR] →ₗ[ℂ] B) :
    RankTwo.metricContraction (T := vectorPair f) = f σ^^^ := by
  rw [RankTwo.metricContraction, sum_pi_fin_two, toTensor_eq_sum_indexBasis, map_sum,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.sum_eq_single ν (fun ρ _ hρ => ?_) (fun hν => absurd (Finset.mem_univ ν) hν)]
  · simp only [vectorPair, Matrix.cons_val_zero, Matrix.cons_val_one, Finset.smul_sum,
      smul_smul, map_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    rw [PauliMatrix.pauliLower_eq_smul, Matrix.smul_apply, smul_eq_mul, ← mul_assoc]
    rcases ν with ν | ν <;> fin_cases ν <;> norm_num [minkowskiMatrixZ]
  · rw [show minkowskiMatrixZ (![ν, ρ] 0) (![ν, ρ] 1) = 0 from by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      simp [minkowskiMatrixZ, Ne.symm hρ]]
    simp

/-!

## D. The classification of the Lorentz invariants

`RankTwo` classifies the invariants of `vectorPair f`, whose span is the range of `f` and whose
metric contraction is `f σ^^^`.

-/

include hf in
/-- The image `f σ^^^` of the Pauli tensor is Lorentz invariant. -/
lemma repLorentz_map_pauliMatrix (g : SL(2,ℂ)) : repLorentz g (f σ^^^) = f σ^^^ :=
  hf.repLorentz_map_of_invariant toTensor_smul_eq_self g

include hf in
/-- Every Lorentz invariant of `LinearMap.range f ⊔ S`, for `S` a Lorentz-stable submodule, is a
  multiple of the image `f σ^^^` of the Pauli tensor plus an element of `S`: the shape of the
  fermion kinetic term. -/
lemma exists_smul_map_pauliMatrix_add_of_invariant (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ LinearMap.range f ⊔ S) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, ∃ y ∈ S, x = a • f σ^^^ + y := by
  obtain ⟨a, y, hy, ha⟩ := RankTwo.exists_smul_metricContraction_of_invariant_subset
    hf.isLorentzCovariant_vectorPair S hS (by rwa [span_range_vectorPair]) hinv
  exact ⟨a, y, hy, by rwa [metricContraction_vectorPair] at ha⟩

include hf in
/-- The Lorentz invariants of the range of `f` reduce to the span of the image `f σ^^^` of the
  Pauli tensor. -/
noncomputable def invariantReductionToSpan :
    InvariantReductionToSpan (fun g : SL(2,ℂ) => repLorentz g) (LinearMap.range f) where
  spanningVector := f σ^^^
  stable := hf.isStableUnder_range
  spanningVector_fixed := hf.repLorentz_map_pauliMatrix
  reduce S hS _ hx hinv := hf.exists_smul_map_pauliMatrix_add_of_invariant S hS hx hinv

end IsVectorLeftRightWeyl

/-!

## E. Maps from components

A family `T (μ, α, α')` of vectors is the linear map `ofVectorComponents T` sending
`e_μ ⊗ e_α ⊗ e_α'` to `T (μ, α, α')`, and it is equivariant when the vectors are moved as the
basis tensors are.

-/

section VectorComponents

open PauliMatrix TensorSpecies

variable {B : Type*} [AddCommGroup B] [Module ℂ B]

/-- The linear map out of `ℂT[.up, .upL, .upR]` sending `e_μ ⊗ e_α ⊗ e_α'` to
  `T (μ, α, α')`. -/
noncomputable def ofVectorComponents (T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B) :
    ℂT[.up, .upL, .upR] →ₗ[ℂ] B :=
  indexBasis.constr ℂ T

@[simp]
lemma ofVectorComponents_indexBasis (T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B)
    (d : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2) : ofVectorComponents T (indexBasis d) = T d :=
  indexBasis.constr_basis ℂ T d

/-- The range of `ofVectorComponents T` is the span of the vectors `T d`. -/
lemma range_ofVectorComponents (T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B) :
    LinearMap.range (ofVectorComponents T) = Submodule.span ℂ (Set.range T) :=
  indexBasis.constr_range ℂ

/-- `ofVectorComponents T` is equivariant when `T (μ, α, α')` is moved as `T^{μ α α'}`: the
  vector index by the Lorentz matrix, the left index by the matrix of `g` and the right index by
  its complex conjugate, the summed index first in each factor. -/
lemma isVectorLeftRightWeyl_ofVectorComponents {repLorentz : Representation ℂ SL(2,ℂ) B}
    (T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B)
    (hT : ∀ (g : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2),
      repLorentz g (T (μ, l)) = ∑ (ν : Fin 1 ⊕ Fin 3), ∑ (a : Fin 2 × Fin 2),
        ((((SL2C.toLorentzGroup g).1 ν μ : ℝ) : ℂ)
          * (g.1 a.1 l.1 * star (g.1 a.2 l.2))) • T (ν, a)) :
    IsVectorLeftRightWeyl B repLorentz (ofVectorComponents T) := by
  have h : ofVectorComponents T
      = (Tensor.basis ![Color.up, Color.upL, Color.upR]).constr ℂ fun φ => T (indexEquiv φ) :=
    (Tensor.basis (S := complexLorentzTensor) _).ext fun φ => by
      rw [Module.Basis.constr_basis, ← indexEquiv.symm_apply_apply φ, ← indexBasis_apply,
        ofVectorComponents_indexBasis, Equiv.apply_symm_apply]
  rw [h]
  refine isLorentzEquivariant_constr _ fun g φ => ?_
  obtain ⟨⟨μ, l⟩, rfl⟩ := indexEquiv.symm.surjective φ
  rw [Equiv.apply_symm_apply, hT, ← indexEquiv.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun a _ => ?_
  rw [Equiv.apply_symm_apply, Fin.prod_univ_three, mul_assoc]
  exact congrArg (· • _) (congrArg₂ (· * ·) (toMatrix_rep_up_apply g ν μ)
    (congrArg₂ (· * ·) (congrFun (congrFun (toMatrix_rep_upL g) a.1) l.1)
      (congrFun (congrFun (toMatrix_rep_upR g) a.2) l.2))).symm

end VectorComponents

/-!

## F. Dual Weyl indices and the `ε` re-index

A `Module.Dual`-valued symbol carries the dual law on its spinor indices: `IsDualLeftRightWeyl`
for a Weyl pair alone, `IsVectorDualLeftRightWeyl` with a vector index alongside. The
symplectic identities of `Fermions.Weyl.Metric` convert those laws into the fundamental ones.

-/

/-- The `ε` re-index of a family indexed by two Weyl indices: both index slots are
  transported through the symplectic form. -/
noncomputable def epsReindex {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (T : Fin 2 × Fin 2 → B) : Fin 2 × Fin 2 → B :=
  fun l => ∑ k : Fin 2 × Fin 2, (epsilon.1 l.1 k.1 * epsilon.1 l.2 k.2) • T k

section Reindex

variable {B : Type*} [AddCommGroup B] [Module ℂ B] (T : Fin 2 × Fin 2 → B)

/-- The re-index written out on the diagonal component `(0, 0)`. -/
lemma epsReindex_zero_zero : epsReindex T (0, 0) = T (1, 1) := by
  simp [epsReindex, Fintype.sum_prod_type, Fin.sum_univ_two, SL2C.epsilon_coe]

/-- The re-index written out on the mixed component `(0, 1)`. -/
lemma epsReindex_zero_one : epsReindex T (0, 1) = - T (1, 0) := by
  simp [epsReindex, Fintype.sum_prod_type, Fin.sum_univ_two, SL2C.epsilon_coe]

/-- The re-index written out on the mixed component `(1, 0)`. -/
lemma epsReindex_one_zero : epsReindex T (1, 0) = - T (0, 1) := by
  simp [epsReindex, Fintype.sum_prod_type, Fin.sum_univ_two, SL2C.epsilon_coe]

/-- The re-index written out on the diagonal component `(1, 1)`. -/
lemma epsReindex_one_one : epsReindex T (1, 1) = T (0, 0) := by
  simp [epsReindex, Fintype.sum_prod_type, Fin.sum_univ_two, SL2C.epsilon_coe]

/-- The `ε` re-index is an involution, because `ε² = -1` on each index slot. -/
lemma epsReindex_epsReindex : epsReindex (epsReindex T) = T := by
  funext l
  obtain ⟨l₁, l₂⟩ := l
  fin_cases l₁ <;> fin_cases l₂ <;>
    simp [epsReindex_zero_zero, epsReindex_zero_one, epsReindex_one_zero,
      epsReindex_one_one]

/-- The re-index does not change the span of the components. -/
lemma span_range_epsReindex :
    Submodule.span ℂ (Set.range (epsReindex T)) = Submodule.span ℂ (Set.range T) := by
  refine Submodule.span_eq_span
    (Set.range_subset_iff.2 fun d => (Submodule.mem_span_range_iff_exists_fun ℂ).2 ⟨_, rfl⟩)
    (Set.range_subset_iff.2 fun d => ?_)
  have h : T d = epsReindex (epsReindex T) d := by rw [epsReindex_epsReindex]
  rw [h]
  exact (Submodule.mem_span_range_iff_exists_fun ℂ).2 ⟨_, rfl⟩

end Reindex

/-- A family `T` indexed by a dual left- and a dual right-handed Weyl index, moved as
  `T_{α α'}`: the undotted index by the inverse transpose `(g⁻¹)ᵀ`, the dotted one by the
  inverse conjugate transpose `(g⁻¹)ᴴ`. -/
structure IsDualLeftRightWeyl (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B)
    (T : Fin 2 × Fin 2 → B) : Prop where
  repLorentz_T : ∀ (g : SL(2,ℂ)) l,
    repLorentz g (T l) = ∑ (a : Fin 2 × Fin 2),
      ((g.1⁻¹)ᵀ a.1 l.1 * (g.1⁻¹)ᴴ a.2 l.2) • T a

/-- The same with a four-vector index alongside, moved as `T^μ{}_{α α'}`. The vector index
  keeps the plain Lorentz matrix: in the Standard Model it is a derivative slot, and only
  the value index of a symbol is dualised. -/
structure IsVectorDualLeftRightWeyl (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B)
    (T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B) : Prop where
  repLorentz_T : ∀ (g : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2),
    repLorentz g (T (μ, l)) = ∑ (ν : Fin 1 ⊕ Fin 3), ∑ (a : Fin 2 × Fin 2),
      ((((SL2C.toLorentzGroup g).1 ν μ : ℝ) : ℂ)
        * ((g.1⁻¹)ᵀ a.1 l.1 * (g.1⁻¹)ᴴ a.2 l.2)) • T (ν, a)

open Fermion in
/-- The tensor product of the two dual Weyl representations carries the mixed dual law on
  products of basis vectors. -/
lemma isDualLeftRightWeyl_dualWeyl :
    IsDualLeftRightWeyl (DualLeftHandedWeyl ⊗[ℂ] DualRightHandedWeyl)
      (DualLeftHandedWeyl.rep.tprod DualRightHandedWeyl.rep)
      (fun l => DualLeftHandedWeyl.basis l.1 ⊗ₜ[ℂ] DualRightHandedWeyl.basis l.2) where
  repLorentz_T g l := by
    rw [Representation.tprod_apply, TensorProduct.map_tmul,
      DualLeftHandedWeyl.rep_apply_basis, DualRightHandedWeyl.rep_apply_basis,
      TensorProduct.sum_tmul]
    simp only [TensorProduct.smul_tmul', TensorProduct.tmul_sum, TensorProduct.tmul_smul,
      smul_smul, Fintype.sum_prod_type, Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
      rw [mul_comm]

/-- The mixed two-slot form of the symplectic identities `sum_epsilon_mul_inv_transpose` and
  `sum_epsilon_mul_inv_conjTranspose`: moving `(g⁻¹)ᵀ` and `(g⁻¹)ᴴ` across `ε` turns them into
  `g` and its conjugate on the other slots. -/
lemma sum_mixedEpsilon_mul_inv (g : SL(2,ℂ)) (l a : Fin 2 × Fin 2) :
    ∑ k : Fin 2 × Fin 2, (epsilon.1 l.1 k.1 * epsilon.1 l.2 k.2)
        * ((g.1⁻¹)ᵀ a.1 k.1 * (g.1⁻¹)ᴴ a.2 k.2)
      = ∑ b : Fin 2 × Fin 2, (g.1 b.1 l.1 * star (g.1 b.2 l.2))
        * (epsilon.1 b.1 a.1 * epsilon.1 b.2 a.2) := by
  have hL : (∑ k₁, epsilon.1 l.1 k₁ * (g.1⁻¹)ᵀ a.1 k₁)
      * (∑ k₂, epsilon.1 l.2 k₂ * (g.1⁻¹)ᴴ a.2 k₂)
      = ∑ k : Fin 2 × Fin 2, (epsilon.1 l.1 k.1 * epsilon.1 l.2 k.2)
        * ((g.1⁻¹)ᵀ a.1 k.1 * (g.1⁻¹)ᴴ a.2 k.2) := by
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun k₁ _ => Finset.sum_congr rfl fun k₂ _ => by ring
  have hR : (∑ b₁, g.1 b₁ l.1 * epsilon.1 b₁ a.1)
      * (∑ b₂, star (g.1 b₂ l.2) * epsilon.1 b₂ a.2)
      = ∑ b : Fin 2 × Fin 2, (g.1 b.1 l.1 * star (g.1 b.2 l.2))
        * (epsilon.1 b.1 a.1 * epsilon.1 b.2 a.2) := by
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ => by ring
  rw [← hL, ← hR, sum_epsilon_mul_inv_transpose, sum_epsilon_mul_inv_conjTranspose]

/-- The `ε` re-index turns the mixed dual law into the mixed fundamental law for the same
  representation: the symplectic identity `sum_mixedEpsilon_mul_inv` is the only mathematical
  step. -/
lemma IsDualLeftRightWeyl.isLeftRightWeyl_epsReindex {B : Type*} [AddCommGroup B]
    [Module ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B} {T : Fin 2 × Fin 2 → B}
    (hT : IsDualLeftRightWeyl B repLorentz T) :
    IsLeftRightWeyl B repLorentz (epsReindex T) where
  repLorentz_T g l := by
    have h := (repLorentz g).map_sum_smul_of_forall_eq T T
      (fun a k => (g.1⁻¹)ᵀ a.1 k.1 * (g.1⁻¹)ᴴ a.2 k.2) (hT.repLorentz_T g)
      (fun k => epsilon.1 l.1 k.1 * epsilon.1 l.2 k.2)
    simp only [sum_mixedEpsilon_mul_inv] at h
    rw [Fintype.sum_sum_mul_smul (fun (a b : Fin 2 × Fin 2) =>
      epsilon.1 b.1 a.1 * epsilon.1 b.2 a.2)] at h
    exact h

/-!

## G. The `ε` re-index of a vector-Weyl family

Re-indexing both spinor slots by `ε` sends a family with the dual law to one with the
fundamental law, without touching the representation, and does not change the span. It
does move the contraction: the Pauli matrices go to their transposes.

-/

/-- The transposes `(σ_μ)ᵀ` of the covariant Pauli matrices, entrywise `(1, -σ₁, σ₂, -σ₃)`. -/
def pauliBar (μ : Fin 1 ⊕ Fin 3) : Matrix (Fin 2) (Fin 2) ℂ := (PauliMatrix.pauliLower μ)ᵀ

/-- Conjugating a Pauli matrix by the symplectic form on both spinor slots produces
  `pauliBar` of the same vector index. -/
lemma sum_pauliMatrix_mul_epsilon (μ : Fin 1 ⊕ Fin 3) (k₁ k₂ : Fin 2) :
    ∑ a : Fin 2 × Fin 2, PauliMatrix.pauliMatrix μ a.1 a.2
        * (epsilon.1 a.1 k₁ * epsilon.1 a.2 k₂) = pauliBar μ k₁ k₂ := by
  rcases μ with μ | μ <;> fin_cases μ <;> fin_cases k₁ <;> fin_cases k₂ <;>
    simp [Fintype.sum_prod_type, Fin.sum_univ_two, PauliMatrix.pauliMatrix,
      pauliBar, PauliMatrix.pauliLower, PauliMatrix.pauliSelfAdjoint', SL2C.epsilon_coe]

/-- The `ε` re-index of such a family: the vector index is left alone and both spinor slots
  are sent through the symplectic form. -/
noncomputable def vectorEpsReindex {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B) : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B :=
  fun d => ∑ k : Fin 2 × Fin 2, (epsilon.1 d.2.1 k.1 * epsilon.1 d.2.2 k.2) • T (d.1, k)

section VectorReindex

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  (T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B)

/-- At a fixed vector index the re-index is the `ε` re-index of the Weyl pair. -/
lemma vectorEpsReindex_eq_epsReindex (μ : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2) :
    vectorEpsReindex T (μ, l) = epsReindex (fun k => T (μ, k)) l := rfl

/-- The re-index is an involution, slot by slot. -/
lemma vectorEpsReindex_vectorEpsReindex :
    vectorEpsReindex (vectorEpsReindex T) = T := by
  funext d
  obtain ⟨μ, l⟩ := d
  have h : (fun k => vectorEpsReindex T (μ, k)) = epsReindex (fun k => T (μ, k)) := rfl
  rw [vectorEpsReindex_eq_epsReindex, h, epsReindex_epsReindex]

/-- The re-index does not change the span of the components. -/
lemma span_range_vectorEpsReindex :
    Submodule.span ℂ (Set.range (vectorEpsReindex T)) = Submodule.span ℂ (Set.range T) := by
  refine Submodule.span_eq_span (Set.range_subset_iff.2 fun d => ?_)
    (Set.range_subset_iff.2 fun d => ?_)
  · exact sum_mem fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨(d.1, k), rfl⟩)
  · have h : T d = vectorEpsReindex (vectorEpsReindex T) d := by
      rw [vectorEpsReindex_vectorEpsReindex]
    rw [h]
    exact sum_mem fun k _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨(d.1, k), rfl⟩)

end VectorReindex

namespace IsVectorDualLeftRightWeyl

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B}

/-- The contraction `∑ μ, ∑ a, pauliBar μ a₁ a₂ • T (μ, a)` against the transposed Pauli
  matrices, the invariant of a vector index against a dual Weyl pair. -/
noncomputable def pauliBarContraction : B :=
  ∑ μ : Fin 1 ⊕ Fin 3, ∑ a : Fin 2 × Fin 2, pauliBar μ a.1 a.2 • T (μ, a)

/-- The index law as one matrix on the product index. -/
lemma repLorentz_T' (hT : IsVectorDualLeftRightWeyl B repLorentz T) (g : SL(2,ℂ))
    (d : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2) :
    repLorentz g (T d) = ∑ e : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2,
      ((((SL2C.toLorentzGroup g).1 e.1 d.1 : ℝ) : ℂ)
        * ((g.1⁻¹)ᵀ e.2.1 d.2.1 * (g.1⁻¹)ᴴ e.2.2 d.2.2)) • T e := by
  rw [show d = (d.1, d.2) from rfl, hT.repLorentz_T, Fintype.sum_prod_type]

/-- The `ε` re-index turns the mixed dual law into the mixed fundamental law for the same
  representation, the vector slot untouched, so the map with the re-indexed components is
  equivariant: `sum_mixedEpsilon_mul_inv` is the only mathematical step. -/
lemma isVectorLeftRightWeyl_vectorEpsReindex
    (hT : IsVectorDualLeftRightWeyl B repLorentz T) :
    IsVectorLeftRightWeyl B repLorentz (ofVectorComponents (vectorEpsReindex T)) :=
  isVectorLeftRightWeyl_ofVectorComponents _ fun g μ l => by
    have h := (repLorentz g).map_sum_smul_of_forall_eq (fun k => T (μ, k)) T
      (fun e k => (((SL2C.toLorentzGroup g).1 e.1 μ : ℝ) : ℂ)
        * ((g.1⁻¹)ᵀ e.2.1 k.1 * (g.1⁻¹)ᴴ e.2.2 k.2)) (fun k => hT.repLorentz_T' g (μ, k))
      (fun k => epsilon.1 l.1 k.1 * epsilon.1 l.2 k.2)
    refine h.trans ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun ν _ => ?_
    have hinner : ∀ b : Fin 2 × Fin 2,
        (∑ k : Fin 2 × Fin 2, (epsilon.1 l.1 k.1 * epsilon.1 l.2 k.2)
          * ((((SL2C.toLorentzGroup g).1 ν μ : ℝ) : ℂ)
            * ((g.1⁻¹)ᵀ b.1 k.1 * (g.1⁻¹)ᴴ b.2 k.2)))
          = (((SL2C.toLorentzGroup g).1 ν μ : ℝ) : ℂ)
            * ∑ a : Fin 2 × Fin 2, (g.1 a.1 l.1 * star (g.1 a.2 l.2))
              * (epsilon.1 a.1 b.1 * epsilon.1 a.2 b.2) := fun b => by
      rw [← sum_mixedEpsilon_mul_inv g l b, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [hinner, mul_smul, ← Finset.smul_sum]
    rw [Fintype.sum_sum_mul_smul (fun (b a : Fin 2 × Fin 2) =>
      epsilon.1 a.1 b.1 * epsilon.1 a.2 b.2)
      (fun a => g.1 a.1 l.1 * star (g.1 a.2 l.2)) (fun b => T (ν, b))]
    simp only [← mul_smul]
    rfl

open PauliMatrix in
/-- The image of the Pauli tensor under the map with the re-indexed components is the
  `pauliBar` contraction of the original family, with no sign or scalar. -/
lemma ofVectorComponents_vectorEpsReindex_pauliMatrix :
    ofVectorComponents (vectorEpsReindex T) σ^^^ = pauliBarContraction (T := T) := by
  rw [toTensor_eq_sum_indexBasis, map_sum, Fintype.sum_prod_type, pauliBarContraction]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [map_smul, ofVectorComponents_indexBasis, vectorEpsReindex, Finset.smul_sum,
    smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_smul, ← sum_pauliMatrix_mul_epsilon μ k.1 k.2]

end IsVectorDualLeftRightWeyl

/-!

## H. The classification of the invariants of the dual families

Transporting section D along the re-index of section G: a dual Weyl pair with no vector index has
no invariant, and with a vector index every invariant is a multiple of the `pauliBar`
contraction.

-/

section DualClassification

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B}

/-- A dual left-handed and a dual right-handed Weyl index with no vector index between them
  have no Lorentz invariant in the span of their components but `0`: the mixed pair is the
  four-vector representation, whose invariants need a second vector index, as in
  `IsVectorDualLeftRightWeyl`. -/
theorem IsDualLeftRightWeyl.eq_zero_of_invariant {T : Fin 2 × Fin 2 → B}
    (hT : IsDualLeftRightWeyl B repLorentz T) {x : B} (hx : x ∈ Submodule.span ℂ (Set.range T))
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x = 0 :=
  hT.isLeftRightWeyl_epsReindex.eq_zero_of_invariant (by rwa [span_range_epsReindex]) hinv

/-- The same modulo a Lorentz-stable subspace `S`: such an invariant already lies in `S`. -/
theorem IsDualLeftRightWeyl.mem_of_invariant_of_mem_sup {T : Fin 2 × Fin 2 → B}
    (hT : IsDualLeftRightWeyl B repLorentz T) {x : B} (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S)
    (hx : x ∈ Submodule.span ℂ (Set.range T) ⊔ S)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S :=
  hT.isLeftRightWeyl_epsReindex.mem_of_invariant_of_mem_sup S hS
    (by rwa [span_range_epsReindex]) hinv

namespace IsVectorDualLeftRightWeyl

variable {T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B}

/-- The `pauliBar` contraction of a family with the mixed dual law is Lorentz invariant. -/
lemma repLorentz_pauliBarContraction (hT : IsVectorDualLeftRightWeyl B repLorentz T)
    (g : SL(2,ℂ)) :
    repLorentz g (pauliBarContraction (T := T)) = pauliBarContraction (T := T) := by
  have h := hT.isVectorLeftRightWeyl_vectorEpsReindex.repLorentz_map_pauliMatrix g
  rwa [ofVectorComponents_vectorEpsReindex_pauliMatrix] at h

/-- For the mixed dual law, every Lorentz invariant of `span (range T) ⊔ S`, for `S` a
  Lorentz-stable submodule, is a multiple of the `pauliBar` contraction plus an element of
  `S`. -/
lemma exists_smul_pauliBarContraction_of_invariant_subset
    (hT : IsVectorDualLeftRightWeyl B repLorentz T) {x : B} (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S)
    (hx : x ∈ Submodule.span ℂ (Set.range T) ⊔ S)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, ∃ y ∈ S, x = a • pauliBarContraction (T := T) + y := by
  obtain ⟨a, y, hy, ha⟩ :=
    hT.isVectorLeftRightWeyl_vectorEpsReindex.exists_smul_map_pauliMatrix_add_of_invariant S hS
      (by rwa [range_ofVectorComponents, span_range_vectorEpsReindex]) hinv
  exact ⟨a, y, hy, by rwa [ofVectorComponents_vectorEpsReindex_pauliMatrix] at ha⟩

/-- For the mixed dual law, every Lorentz invariant of the span is a multiple of the
  `pauliBar` contraction. This is the kinetic term of a Weyl fermion. -/
lemma exists_smul_pauliBarContraction_of_invariant
    (hT : IsVectorDualLeftRightWeyl B repLorentz T) {x : B}
    (hx : x ∈ Submodule.span ℂ (Set.range T))
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, x = a • pauliBarContraction (T := T) := by
  obtain ⟨a, y, hy, ha⟩ := hT.exists_smul_pauliBarContraction_of_invariant_subset ⊥
    (fun _ _ hy => by rw [Submodule.mem_bot] at hy ⊢; rw [hy, map_zero])
    (by rwa [sup_bot_eq]) hinv
  rw [Submodule.mem_bot] at hy
  exact ⟨a, by rw [ha, hy, add_zero]⟩

/-- For the mixed dual law, the Lorentz invariants of the component span reduce to the span
  of the `pauliBar` contraction. -/
noncomputable def invariantReductionToSpan (hT : IsVectorDualLeftRightWeyl B repLorentz T) :
    InvariantReductionToSpan (fun g : SL(2,ℂ) => repLorentz g)
      (Submodule.span ℂ (Set.range T)) where
  spanningVector := pauliBarContraction (T := T)
  stable := isStableUnder_span_range_of_sum fun g q => ⟨_, hT.repLorentz_T' g q⟩
  spanningVector_fixed := hT.repLorentz_pauliBarContraction
  reduce S hS _ hx hinv := hT.exists_smul_pauliBarContraction_of_invariant_subset S hS hx hinv

end IsVectorDualLeftRightWeyl

end DualClassification

end Lorentz
