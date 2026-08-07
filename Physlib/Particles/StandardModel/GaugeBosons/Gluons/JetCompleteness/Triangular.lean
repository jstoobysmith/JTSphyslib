/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.Particles.StandardModel.GaugeBosons.Gluons.JetCompleteness.HighestLayer

/-!
# Arbitrary-order triangular gluon coordinates

This file constructs an independent hook complement to `HighestLayer`'s fully symmetric translation
directions on `OrdinaryJets`'s unchanged ordinary carrier.  For a nonzero total multi-index `w`, the
distinguished supported direction is `layerDir w`; the other supported directions index the hook
differences.  The weighted symmetric average and those differences have an explicit inverse.

The second half replaces every linear hook difference by the corresponding symmetrized covariant
curvature derivative from `CovariantTower` and proves that this nonlinear substitution is
unitriangular in the
additive ordinary-derivative-degree filtration.
-/

open scoped BigOperators
open Finsupp MvPolynomial SymmetricAlgebra

@[expose] public section

namespace StandardModel
namespace SU3Jet

/-!
## A. An independent arbitrary-order hook index
-/

/-- Remove one occurrence of a supported direction from a derivative multi-index. -/
noncomputable def predAt (w : DIdx) (mu : Lor) : DIdx :=
  Finsupp.update w mu (w mu - 1)

lemma predAt_add_single {w : DIdx} {mu : Lor} (hmu : w mu ≠ 0) :
    predAt w mu + Finsupp.single mu 1 = w := by
  ext nu
  by_cases h : nu = mu
  · subst nu
    simpa [predAt, Finsupp.update] using
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hmu)
  · simp [predAt, h]

lemma lorDeg_predAt {w : DIdx} {mu : Lor} (hmu : w mu ≠ 0) :
    lorDeg (predAt w mu) + 1 = lorDeg w := by
  have h := congrArg lorDeg (predAt_add_single hmu)
  rwa [lorDeg_add, lorDeg_single] at h

/-- A nonzero fully symmetric total index. -/
abbrev SymIdx := {w : DIdx // w ≠ 0}

/-- The independent hook coordinates over `w`: one for each supported direction other than the
distinguished direction.  There are no quotient relations or redundant Bianchi coordinates. -/
structure AllHookIdx where
  w : DIdx
  mu : Lor
  w_ne_zero : w ≠ 0
  mu_supported : w mu ≠ 0
  mu_ne_dir : mu ≠ layerDir w

/-- The ordinary component with total index `w` and connection direction `mu`. -/
noncomputable def totalComponent (w : DIdx) (mu : Lor) (c : Col) : JetAlgebra :=
  ofGen (.dA (predAt w mu) mu c)

/-- The fully symmetric projection of the connection derivative with total index `w`. -/
noncomputable def symConn (w : DIdx) (c : Col) : JetAlgebra :=
  (lorDeg w : ℝ)⁻¹ • ∑ mu : Lor, (w mu : ℝ) • totalComponent w mu c

/-- The independent linear hook difference relative to `layerDir w`. -/
noncomputable def hookDiff (i : AllHookIdx) (c : Col) : JetAlgebra :=
  totalComponent i.w i.mu c - totalComponent i.w (layerDir i.w) c

/-- The weighted hook correction appearing in the inverse coordinate formula. -/
noncomputable def hookAverage (w : DIdx) (c : Col) : JetAlgebra :=
  (lorDeg w : ℝ)⁻¹ • ∑ mu : Lor,
    (w mu : ℝ) • (totalComponent w mu c - totalComponent w (layerDir w) c)

lemma symConn_eq_distinguished_add_hookAverage {w : DIdx} (hw : w ≠ 0) (c : Col) :
    symConn w c = totalComponent w (layerDir w) c + hookAverage w c := by
  rw [symConn, hookAverage]
  have hdeg : (lorDeg w : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt ((lorDeg_pos_iff w).2 hw))
  have hsum : ∑ mu : Lor, (w mu : ℝ) = lorDeg w := by
    norm_cast
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, smul_sub,
    inv_smul_smul₀ hdeg]
  module

lemma distinguished_eq_symConn_sub_hookAverage {w : DIdx} (hw : w ≠ 0) (c : Col) :
    totalComponent w (layerDir w) c = symConn w c - hookAverage w c := by
  rw [symConn_eq_distinguished_add_hookAverage hw]
  abel

lemma totalComponent_eq_symConn_add_hook_sub {w : DIdx} (hw : w ≠ 0)
    {mu : Lor} (_hmu : w mu ≠ 0) (c : Col) :
    totalComponent w mu c = symConn w c +
      (totalComponent w mu c - totalComponent w (layerDir w) c) - hookAverage w c := by
  rw [symConn_eq_distinguished_add_hookAverage hw]
  abel

/-!
## B. The additive ordinary-derivative-degree filtration

The weight of a product is the sum of the derivative multi-index degrees of its ordinary
generators.  Connection factors therefore have weight zero.  A total derivative raises the
weight by one, while multiplication by a connection does not; this is the filtration in which
covariant derivatives are triangular.
-/

/-- Ordinary derivative degree of a generator. -/
noncomputable def genDeg : JetGenerators → ℕ
  | .dA s _ _ => lorDeg s

@[simp]
lemma genDeg_dA (s : DIdx) (mu : Lor) (c : Col) : genDeg (.dA s mu c) = lorDeg s := rfl

lemma genDeg_shift (nu : Lor) (g : JetGenerators) :
    genDeg (JetGenerators.shift nu g) = genDeg g + 1 := by
  cases g with
  | dA s mu c => simp [genDeg, lorDeg_add, lorDeg_single]

/-- Monomial generators of derivative degree at most `d`. -/
def filtGen (d : ℕ) : Set JetAlgebra :=
  {P | ∃ l : List JetGenerators,
    (l.map genDeg).sum ≤ d ∧ P = (l.map ofGen).prod}

/-- Monomial generators of derivative degree strictly below `d`. -/
def sfiltGen (d : ℕ) : Set JetAlgebra :=
  {P | ∃ l : List JetGenerators,
    (l.map genDeg).sum < d ∧ P = (l.map ofGen).prod}

/-- The additive derivative-degree filtration. -/
noncomputable def filt (d : ℕ) : Submodule ℝ JetAlgebra := Submodule.span ℝ (filtGen d)

/-- The strict additive derivative-degree filtration. -/
noncomputable def sfilt (d : ℕ) : Submodule ℝ JetAlgebra := Submodule.span ℝ (sfiltGen d)

lemma filt_mono {d e : ℕ} (h : d ≤ e) : filt d ≤ filt e :=
  Submodule.span_mono fun P hP => by
    obtain ⟨l, hl, rfl⟩ := hP
    exact ⟨l, hl.trans h, rfl⟩

lemma sfilt_mono {d e : ℕ} (h : d ≤ e) : sfilt d ≤ sfilt e :=
  Submodule.span_mono fun P hP => by
    obtain ⟨l, hl, rfl⟩ := hP
    exact ⟨l, hl.trans_le h, rfl⟩

lemma sfilt_le_filt (d : ℕ) : sfilt d ≤ filt d :=
  Submodule.span_mono fun P hP => by
    obtain ⟨l, hl, rfl⟩ := hP
    exact ⟨l, hl.le, rfl⟩

lemma sfilt_zero : sfilt 0 = ⊥ := by
  rw [sfilt, show sfiltGen 0 = ∅ from Set.eq_empty_iff_forall_notMem.mpr (by
    rintro P ⟨l, hl, rfl⟩
    omega), Submodule.span_empty]

lemma sfilt_succ (d : ℕ) : sfilt (d + 1) = filt d := by
  rw [sfilt, filt, show sfiltGen (d + 1) = filtGen d from Set.ext fun P =>
    ⟨fun ⟨l, hl, hP⟩ => ⟨l, Nat.lt_succ_iff.mp hl, hP⟩,
      fun ⟨l, hl, hP⟩ => ⟨l, Nat.lt_succ_iff.mpr hl, hP⟩⟩]

lemma one_mem_filt_zero : (1 : JetAlgebra) ∈ filt 0 := by
  exact Submodule.subset_span ⟨[], by simp, by simp⟩

lemma ofGen_mem_filt (g : JetGenerators) : ofGen g ∈ filt (genDeg g) := by
  exact Submodule.subset_span ⟨[g], by simp, by simp⟩

lemma mul_mem_filt {a b : ℕ} {P Q : JetAlgebra} (hP : P ∈ filt a)
    (hQ : Q ∈ filt b) : P * Q ∈ filt (a + b) := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
      induction hQ using Submodule.span_induction with
      | mem Q hQ =>
          obtain ⟨l, hl, rfl⟩ := hP
          obtain ⟨k, hk, rfl⟩ := hQ
          refine Submodule.subset_span ⟨l ++ k, ?_, ?_⟩
          · simp only [List.map_append, List.sum_append]
            omega
          · simp [List.map_append, List.prod_append]
      | zero => simp
      | add x y _ _ hx hy => simpa [mul_add] using add_mem hx hy
      | smul r x _ hx => simpa [mul_smul_comm] using Submodule.smul_mem (filt (a + b)) r hx
  | zero => simp
  | add x y _ _ hx hy => simpa [add_mul] using add_mem hx hy
  | smul r x _ hx => simpa [smul_mul_assoc] using Submodule.smul_mem (filt (a + b)) r hx

lemma mul_mem_sfilt_left {a b : ℕ} {P Q : JetAlgebra} (hP : P ∈ sfilt a)
    (hQ : Q ∈ filt b) : P * Q ∈ sfilt (a + b) := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
      induction hQ using Submodule.span_induction with
      | mem Q hQ =>
          obtain ⟨l, hl, rfl⟩ := hP
          obtain ⟨k, hk, rfl⟩ := hQ
          refine Submodule.subset_span ⟨l ++ k, ?_, ?_⟩
          · simp only [List.map_append, List.sum_append]
            omega
          · simp [List.map_append, List.prod_append]
      | zero => simp
      | add x y _ _ hx hy => simpa [mul_add] using add_mem hx hy
      | smul r x _ hx => simpa [mul_smul_comm] using Submodule.smul_mem (sfilt (a + b)) r hx
  | zero => simp
  | add x y _ _ hx hy => simpa [add_mul] using add_mem hx hy
  | smul r x _ hx => simpa [smul_mul_assoc] using Submodule.smul_mem (sfilt (a + b)) r hx

lemma mul_mem_sfilt_right {a b : ℕ} {P Q : JetAlgebra} (hP : P ∈ filt a)
    (hQ : Q ∈ sfilt b) : P * Q ∈ sfilt (a + b) := by
  rw [mul_comm]
  simpa [add_comm] using mul_mem_sfilt_left hQ hP

private lemma jetDeriv_prod_mem_filt (nu : Lor) (l : List JetGenerators) :
    jetDeriv nu (l.map ofGen).prod ∈ filt ((l.map genDeg).sum + 1) := by
  induction l with
  | nil =>
      simp only [List.map_nil, List.prod_nil, List.sum_nil, jetDeriv_one]
      exact zero_mem _
  | cons g l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [jetDeriv_mul, jetDeriv_ofGen]
      refine add_mem ?_ ?_
      · have hg := ofGen_mem_filt (JetGenerators.shift nu g)
        rw [genDeg_shift] at hg
        have hl : (l.map ofGen).prod ∈ filt (l.map genDeg).sum :=
          Submodule.subset_span ⟨l, le_rfl, rfl⟩
        exact filt_mono (by omega) (mul_mem_filt hg hl)
      · exact filt_mono (by omega) (mul_mem_filt (ofGen_mem_filt g) ih)

lemma jetDeriv_mem_filt (nu : Lor) {d : ℕ} {P : JetAlgebra} (hP : P ∈ filt d) :
    jetDeriv nu P ∈ filt (d + 1) := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
      obtain ⟨l, hl, rfl⟩ := hP
      exact filt_mono (by omega) (jetDeriv_prod_mem_filt nu l)
  | zero => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | smul r x _ hx => simpa using Submodule.smul_mem (filt (d + 1)) r hx

lemma jetDeriv_mem_sfilt (nu : Lor) {d : ℕ} {P : JetAlgebra} (hP : P ∈ sfilt d) :
    jetDeriv nu P ∈ sfilt (d + 1) := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
      obtain ⟨l, hl, rfl⟩ := hP
      have h := jetDeriv_prod_mem_filt nu l
      rw [← sfilt_succ] at h
      exact sfilt_mono (by omega) h
  | zero => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | smul r x _ hx => simpa using Submodule.smul_mem (sfilt (d + 1)) r hx

lemma algebraMap_mem_filt_zero (r : ℝ) : algebraMap ℝ JetAlgebra r ∈ filt 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ _ one_mem_filt_zero

lemma brR_mem_filt {a b : ℕ} {p q : Col → JetAlgebra}
    (hp : ∀ c, p c ∈ filt a) (hq : ∀ c, q c ∈ filt b) (c : Col) :
    brR p q c ∈ filt (a + b) := by
  rw [brR]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have hpq := mul_mem_filt (hp i) (hq j)
  have hs := mul_mem_filt (algebraMap_mem_filt_zero (cstruct i j c)) hpq
  simpa using hs

lemma connVec_mem_filt_zero (mu : Lor) (c : Col) : connVec mu c ∈ filt 0 := by
  exact ofGen_mem_filt (.dA 0 mu c)

/-- The linear leading part of the field strength. -/
noncomputable def linCurv (nu mu : Lor) : Col → JetAlgebra :=
  fun c => jetDeriv nu (connVec mu c) - jetDeriv mu (connVec nu c)

lemma linCurv_mem_filt_one (nu mu : Lor) (c : Col) : linCurv nu mu c ∈ filt 1 := by
  rw [linCurv]
  exact sub_mem (by simpa using jetDeriv_mem_filt nu (connVec_mem_filt_zero mu c))
    (by simpa using jetDeriv_mem_filt mu (connVec_mem_filt_zero nu c))

lemma curvVec_mem_filt_one (nu mu : Lor) (c : Col) : curvVec nu mu c ∈ filt 1 := by
  rw [curvVec]
  refine add_mem (linCurv_mem_filt_one nu mu c) ?_
  exact filt_mono (by omega) (brR_mem_filt (connVec_mem_filt_zero nu)
    (connVec_mem_filt_zero mu) c)

lemma curvVec_sub_linCurv_mem_sfilt_one (nu mu : Lor) (c : Col) :
    curvVec nu mu c - linCurv nu mu c ∈ sfilt 1 := by
  rw [curvVec, linCurv]
  have h := brR_mem_filt (connVec_mem_filt_zero nu) (connVec_mem_filt_zero mu) c
  rw [← sfilt_succ] at h
  simpa using h

lemma covD_mem_filt (rho : Lor) {d : ℕ} {X : Col → JetAlgebra}
    (hX : ∀ c, X c ∈ filt d) (c : Col) : covD rho X c ∈ filt (d + 1) := by
  rw [covD]
  refine add_mem (jetDeriv_mem_filt rho (hX c)) ?_
  exact filt_mono (by omega) (brR_mem_filt (connVec_mem_filt_zero rho) hX c)

lemma covIter_mem_filt (n : ℕ) (t : Fin n → Lor) (nu mu : Lor) (c : Col) :
    covIter n t (curvVec nu mu) c ∈ filt (n + 1) := by
  induction n generalizing c with
  | zero => simpa using curvVec_mem_filt_one nu mu c
  | succ n ih =>
      rw [covIter_succ]
      exact covD_mem_filt (t 0) (fun c' => ih (t := fun i => t i.succ) (c := c')) c

/-- Ordered ordinary derivatives, used only to identify the leading term of the covariant tower. -/
noncomputable def plainIter : (n : ℕ) → (Fin n → Lor) →
    (Col → JetAlgebra) → (Col → JetAlgebra)
  | 0, _, X => X
  | n + 1, t, X => fun c => jetDeriv (t 0) (plainIter n (fun i => t i.succ) X c)

@[simp]
lemma plainIter_zero (t : Fin 0 → Lor) (X : Col → JetAlgebra) : plainIter 0 t X = X := rfl

@[simp]
lemma plainIter_succ (n : ℕ) (t : Fin (n + 1) → Lor) (X : Col → JetAlgebra) (c : Col) :
    plainIter (n + 1) t X c = jetDeriv (t 0) (plainIter n (fun i => t i.succ) X c) := rfl

lemma covIter_sub_plainIter_mem_sfilt (n : ℕ) (t : Fin n → Lor) (nu mu : Lor) (c : Col) :
    covIter n t (curvVec nu mu) c - plainIter n t (linCurv nu mu) c ∈ sfilt (n + 1) := by
  induction n generalizing c with
  | zero => simpa using curvVec_sub_linCurv_mem_sfilt_one nu mu c
  | succ n ih =>
      rw [covIter_succ, plainIter_succ, covD]
      have hder := jetDeriv_mem_sfilt (t 0)
        (ih (t := fun i => t i.succ) (c := c))
      rw [map_sub] at hder
      have hbr0 := brR_mem_filt (connVec_mem_filt_zero (t 0))
        (fun c' => covIter_mem_filt n (fun i => t i.succ) nu mu c') c
      have hbr : brR (connVec (t 0)) (covIter n (fun i => t i.succ) (curvVec nu mu)) c ∈
          sfilt (n + 2) := by
        rw [sfilt_succ]
        simpa using hbr0
      have hsum := add_mem hder hbr
      convert hsum using 1
      · abel

/-- The derivative multi-index represented by an ordered tuple. -/
noncomputable def tupleFinsupp {n : ℕ} (t : Fin n → Lor) : DIdx :=
  ∑ i, Finsupp.single (t i) 1

lemma tupleFinsupp_perm {n : ℕ} (t : Fin n → Lor) (sigma : Equiv.Perm (Fin n)) :
    tupleFinsupp (t ∘ sigma) = tupleFinsupp t := by
  rw [tupleFinsupp, tupleFinsupp]
  simpa [Function.comp_def] using
    sigma.sum_comp (Finset.univ : Finset (Fin n)) (fun i => Finsupp.single (t i) 1)

lemma plainIter_linCurv (n : ℕ) (t : Fin n → Lor) (nu mu : Lor) (c : Col) :
    plainIter n t (linCurv nu mu) c =
      ofGen (.dA (tupleFinsupp t + Finsupp.single nu 1) mu c) -
        ofGen (.dA (tupleFinsupp t + Finsupp.single mu 1) nu c) := by
  induction n with
  | zero =>
      simp [plainIter, linCurv, connVec, genVec, tupleFinsupp]
  | succ n ih =>
      rw [plainIter_succ, ih, map_sub, jetDeriv_ofGen, jetDeriv_ofGen]
      simp only [JetGenerators.shift_dA]
      congr 2 <;> simp [tupleFinsupp, Fin.sum_univ_succ, add_left_comm, add_comm]

lemma plainIter_linCurv_perm {n : ℕ} (t : Fin n → Lor) (sigma : Equiv.Perm (Fin n))
    (nu mu : Lor) (c : Col) :
    plainIter n (t ∘ sigma) (linCurv nu mu) c = plainIter n t (linCurv nu mu) c := by
  rw [plainIter_linCurv, plainIter_linCurv, tupleFinsupp_perm]

/-- The symmetrized leading ordinary derivative of the linear field strength. -/
noncomputable def symPlainCurv {n : ℕ} (t : Fin n → Lor) (nu mu : Lor) : Col → JetAlgebra :=
  fun c => (Nat.factorial n : ℝ)⁻¹ •
    ∑ sigma : Equiv.Perm (Fin n), plainIter n (t ∘ sigma) (linCurv nu mu) c

lemma covCurv_sub_symPlainCurv_mem_sfilt {n : ℕ} (t : Fin n → Lor)
    (nu mu : Lor) (c : Col) : covCurv t nu mu c - symPlainCurv t nu mu c ∈ sfilt (n + 1) := by
  have hsum : ∑ sigma : Equiv.Perm (Fin n),
      (covIter n (t ∘ sigma) (curvVec nu mu) c -
        plainIter n (t ∘ sigma) (linCurv nu mu) c) ∈ sfilt (n + 1) :=
    Submodule.sum_mem _ fun sigma _ => covIter_sub_plainIter_mem_sfilt n (t ∘ sigma) nu mu c
  have hsmul := Submodule.smul_mem (sfilt (n + 1)) (Nat.factorial n : ℝ)⁻¹ hsum
  rw [covCurv, symPlainCurv]
  convert hsmul using 1
  rw [Finset.sum_sub_distrib]
  module

lemma symPlainCurv_eq_plainIter {n : ℕ} (t : Fin n → Lor) (nu mu : Lor) (c : Col) :
    symPlainCurv t nu mu c = plainIter n t (linCurv nu mu) c := by
  rw [symPlainCurv, Finset.sum_congr rfl fun sigma _ => plainIter_linCurv_perm t sigma nu mu c,
    Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ]
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  exact inv_smul_smul₀ hfac (plainIter n t (linCurv nu mu) c)

/-- A deterministic list representing a derivative multi-index. -/
noncomputable def didxList (q : DIdx) : List Lor := (didxMultiset q).toList

/-- The deterministic ordered tuple associated to `q`. -/
noncomputable def didxTuple (q : DIdx) : Fin (didxList q).length → Lor :=
  fun i => (didxList q).get i

lemma didxList_length (q : DIdx) : (didxList q).length = lorDeg q := by
  rw [didxList, Multiset.length_toList, ← Multiset.toFinsupp_sum_eq]
  simp [didxMultiset, lorDeg, Finsupp.sum_fintype]

private lemma tupleFinsupp_get (l : List Lor) :
    tupleFinsupp (fun i : Fin l.length => l.get i) = (l : Multiset Lor).toFinsupp := by
  induction l with
  | nil => simp [tupleFinsupp]
  | cons a l ih =>
      simp only [tupleFinsupp, List.length_cons]
      rw [Fin.sum_univ_succ]
      rw [show (↑(a :: l) : Multiset Lor) = {a} + ↑l by rfl, map_add,
        Multiset.toFinsupp_singleton, ← ih]
      change Finsupp.single a 1 + ∑ i : Fin l.length, Finsupp.single (l.get i) 1 =
        Finsupp.single a 1 + tupleFinsupp (fun i : Fin l.length => l.get i)
      rfl

lemma tupleFinsupp_didxTuple (q : DIdx) : tupleFinsupp (didxTuple q) = q := by
  change tupleFinsupp (fun i : Fin (didxList q).length => (didxList q).get i) = q
  rw [tupleFinsupp_get, didxList, Multiset.coe_toList]
  simp [didxMultiset]

/-!
## C. Independent covariant hooks and their leading terms
-/

private lemma predAt_apply_of_ne (w : DIdx) {mu nu : Lor} (h : nu ≠ mu) :
    predAt w mu nu = w nu := by simp [predAt, h]

/-- The derivative multi-index left after reserving the curvature directions `layerDir w` and
`mu`. -/
noncomputable def hookRest (i : AllHookIdx) : DIdx :=
  predAt (predAt i.w i.mu) (layerDir i.w)

private lemma hook_dir_supported (i : AllHookIdx) :
    predAt i.w i.mu (layerDir i.w) ≠ 0 := by
  rw [predAt_apply_of_ne i.w (Ne.symm i.mu_ne_dir)]
  exact layerDir_coeff_ne_zero i.w_ne_zero

lemma hookRest_add_dir (i : AllHookIdx) :
    hookRest i + Finsupp.single (layerDir i.w) 1 = predAt i.w i.mu := by
  exact predAt_add_single (hook_dir_supported i)

lemma hookRest_add_mu (i : AllHookIdx) :
    hookRest i + Finsupp.single i.mu 1 = predAt i.w (layerDir i.w) := by
  apply add_right_cancel (b := Finsupp.single (layerDir i.w) 1)
  calc
    (hookRest i + Finsupp.single i.mu 1) + Finsupp.single (layerDir i.w) 1 =
        (hookRest i + Finsupp.single (layerDir i.w) 1) +
          Finsupp.single i.mu 1 := by ac_rfl
    _ = predAt i.w i.mu + Finsupp.single i.mu 1 := by rw [hookRest_add_dir]
    _ = i.w := predAt_add_single i.mu_supported
    _ = predAt i.w (layerDir i.w) + Finsupp.single (layerDir i.w) 1 :=
      (predAt_add_single (layerDir_coeff_ne_zero i.w_ne_zero)).symm

lemma lorDeg_hookRest (i : AllHookIdx) : lorDeg (hookRest i) + 2 = lorDeg i.w := by
  have hmu := lorDeg_predAt i.mu_supported
  have hdir := lorDeg_predAt (hook_dir_supported i)
  change lorDeg (hookRest i) + 1 = lorDeg (predAt i.w i.mu) at hdir
  omega

/-- The independent covariant hook: the symmetrized `D^(|w|-2) F_(layerDir w),mu` component. -/
noncomputable def covHook (i : AllHookIdx) (c : Col) : JetAlgebra :=
  covCurv (didxTuple (hookRest i)) (layerDir i.w) i.mu c

lemma symPlainHook_eq_hookDiff (i : AllHookIdx) (c : Col) :
    symPlainCurv (didxTuple (hookRest i)) (layerDir i.w) i.mu c = hookDiff i c := by
  rw [symPlainCurv_eq_plainIter, plainIter_linCurv, tupleFinsupp_didxTuple,
    hookRest_add_dir, hookRest_add_mu]
  rfl

/-- The covariant hook differs from its independent linear hook by terms of strictly smaller
additive derivative degree. -/
lemma covHook_sub_hookDiff_mem_sfilt (i : AllHookIdx) (c : Col) :
    covHook i c - hookDiff i c ∈ sfilt (lorDeg (predAt i.w i.mu)) := by
  have h := covCurv_sub_symPlainCurv_mem_sfilt (didxTuple (hookRest i))
    (layerDir i.w) i.mu c
  rw [symPlainHook_eq_hookDiff] at h
  have hlen := didxList_length (hookRest i)
  have hrest := lorDeg_hookRest i
  have hmu := lorDeg_predAt i.mu_supported
  have hdeg : (didxList (hookRest i)).length + 1 = lorDeg (predAt i.w i.mu) := by omega
  rw [hdeg] at h
  exact h

/-!
## D. The normalized triangular substitution

The map below fixes the symmetric weighted average and replaces every independent `hookDiff` by
`covHook`.  Written back in ordinary components, its correction is the hook correction minus its
weighted average, so every generator changes only by strict lower filtration terms.
-/

lemma total_add_single_apply_ne_zero (s : DIdx) (mu : Lor) :
    ((s + (Finsupp.single mu 1 : DIdx)) : DIdx) mu ≠ 0 := by simp

lemma total_add_single_ne_zero (s : DIdx) (mu : Lor) :
    s + Finsupp.single mu 1 ≠ 0 := by
  rw [← lorDeg_pos_iff, lorDeg_add, lorDeg_single]
  omega

lemma predAt_add_single_eq (s : DIdx) (mu : Lor) :
    predAt (s + Finsupp.single mu 1) mu = s := by
  apply add_right_cancel (b := Finsupp.single mu 1)
  exact predAt_add_single (total_add_single_apply_ne_zero s mu)

lemma totalComponent_add_single (s : DIdx) (mu : Lor) (c : Col) :
    totalComponent (s + Finsupp.single mu 1) mu c = ofGen (.dA s mu c) := by
  rw [totalComponent, predAt_add_single_eq]

/-- The nonlinear correction replacing a supported non-distinguished hook difference by the
matching covariant hook. -/
noncomputable def hookCorrection (w : DIdx) (mu : Lor) (c : Col) : JetAlgebra :=
  if hw : w ≠ 0 then
    if hmu : w mu ≠ 0 then
      if hne : mu ≠ layerDir w then
        let i : AllHookIdx := ⟨w, mu, hw, hmu, hne⟩
        covHook i c - hookDiff i c
      else 0
    else 0
  else 0

lemma hookCorrection_eq (i : AllHookIdx) (c : Col) :
    hookCorrection i.w i.mu c = covHook i c - hookDiff i c := by
  rw [hookCorrection, dif_pos i.w_ne_zero, dif_pos i.mu_supported, dif_pos i.mu_ne_dir]

lemma hookCorrection_dir (w : DIdx) (c : Col) :
    hookCorrection w (layerDir w) c = 0 := by
  by_cases hw : w ≠ 0 <;> simp [hookCorrection, hw]

lemma hookCorrection_mem_sfilt (w : DIdx) (mu : Lor) (c : Col) :
    hookCorrection w mu c ∈ sfilt (lorDeg w - 1) := by
  rw [hookCorrection]
  by_cases hw : w ≠ 0
  · rw [dif_pos hw]
    by_cases hmu : w mu ≠ 0
    · rw [dif_pos hmu]
      by_cases hne : mu ≠ layerDir w
      · rw [dif_pos hne]
        let i : AllHookIdx := ⟨w, mu, hw, hmu, hne⟩
        have hdeg := lorDeg_predAt hmu
        have heq : lorDeg (predAt w mu) = lorDeg w - 1 := by omega
        rw [← heq]
        exact covHook_sub_hookDiff_mem_sfilt i c
      · rw [dif_neg hne]
        exact zero_mem _
    · rw [dif_neg hmu]
      exact zero_mem _
  · rw [dif_neg hw]
    exact zero_mem _

/-- The weighted average of the nonlinear hook corrections over a total index. -/
noncomputable def correctionAverage (w : DIdx) (c : Col) : JetAlgebra :=
  (lorDeg w : ℝ)⁻¹ • ∑ mu : Lor, (w mu : ℝ) • hookCorrection w mu c

lemma correctionAverage_mem_sfilt (w : DIdx) (c : Col) :
    correctionAverage w c ∈ sfilt (lorDeg w - 1) := by
  rw [correctionAverage]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun mu _ =>
    Submodule.smul_mem _ _ (hookCorrection_mem_sfilt w mu c))

/-- Generator form of the normalized triangular substitution. -/
noncomputable def triangularGen : JetGenerators → JetAlgebra
  | .dA s mu c =>
      let w := s + Finsupp.single mu 1
      ofGen (.dA s mu c) + hookCorrection w mu c - correctionAverage w c

/-- The nonlinear triangular endomorphism of the unchanged `OrdinaryJets` ordinary carrier. -/
noncomputable def triangularSubst : JetAlgebra →ₐ[ℝ] JetAlgebra :=
  (MvPolynomial.aeval triangularGen).comp toPoly.toAlgHom

@[simp]
lemma triangularSubst_ofGen (g : JetGenerators) :
    triangularSubst (ofGen g) = triangularGen g := by
  rw [triangularSubst]
  change MvPolynomial.aeval triangularGen (toPoly (ofGen g)) = _
  rw [toPoly_ofGen, aeval_X]

lemma triangularGen_sub_self_mem_sfilt (g : JetGenerators) :
    triangularGen g - ofGen g ∈ sfilt (genDeg g) := by
  obtain ⟨s, mu, c⟩ := g
  rw [triangularGen, genDeg_dA]
  have hdeg : lorDeg (s + Finsupp.single mu 1) - 1 = lorDeg s := by
    rw [lorDeg_add, lorDeg_single]
    omega
  rw [show ofGen (.dA s mu c) + hookCorrection (s + Finsupp.single mu 1) mu c -
      correctionAverage (s + Finsupp.single mu 1) c - ofGen (.dA s mu c) =
      hookCorrection (s + Finsupp.single mu 1) mu c -
        correctionAverage (s + Finsupp.single mu 1) c by abel]
  rw [← hdeg]
  exact sub_mem (hookCorrection_mem_sfilt _ _ _) (correctionAverage_mem_sfilt _ _)

lemma triangularGen_mem_filt (g : JetGenerators) : triangularGen g ∈ filt (genDeg g) := by
  have hlow := sfilt_le_filt _ (triangularGen_sub_self_mem_sfilt g)
  have hgen := ofGen_mem_filt g
  have h := add_mem hgen hlow
  rwa [add_sub_cancel] at h

lemma prod_triangularGen_mem_filt (l : List JetGenerators) :
    (l.map triangularGen).prod ∈ filt (l.map genDeg).sum := by
  induction l with
  | nil => simpa using one_mem_filt_zero
  | cons g l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      exact mul_mem_filt (triangularGen_mem_filt g) ih

lemma prod_triangularGen_sub_mem_sfilt (l : List JetGenerators) :
    (l.map triangularGen).prod - (l.map ofGen).prod ∈ sfilt (l.map genDeg).sum := by
  induction l with
  | nil =>
      simp only [List.map_nil, List.prod_nil, List.sum_nil, sub_self]
      exact zero_mem _
  | cons g l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      have hkey : triangularGen g * (l.map triangularGen).prod -
          ofGen g * (l.map ofGen).prod =
          (triangularGen g - ofGen g) * (l.map triangularGen).prod +
            ofGen g * ((l.map triangularGen).prod - (l.map ofGen).prod) := by ring
      rw [hkey]
      exact add_mem
        (mul_mem_sfilt_left (triangularGen_sub_self_mem_sfilt g)
          (prod_triangularGen_mem_filt l))
        (mul_mem_sfilt_right (ofGen_mem_filt g) ih)

private lemma triangularSubst_prod_ofGen (l : List JetGenerators) :
    triangularSubst (l.map ofGen).prod = (l.map triangularGen).prod := by
  induction l with
  | nil => simp
  | cons g l ih =>
      simp only [List.map_cons, List.prod_cons, map_mul, triangularSubst_ofGen, ih]

/-- Unitriangularity on every filtered piece. -/
lemma triangularSubst_sub_self_mem_sfilt {d : ℕ} {P : JetAlgebra} (hP : P ∈ filt d) :
    triangularSubst P - P ∈ sfilt d := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
      obtain ⟨l, hl, rfl⟩ := hP
      have h := prod_triangularGen_sub_mem_sfilt l
      rw [triangularSubst_prod_ofGen]
      exact sfilt_mono hl h
  | zero =>
      rw [map_zero, sub_zero]
      exact zero_mem _
  | add P Q _ _ hP hQ =>
      rw [map_add, show triangularSubst P + triangularSubst Q - (P + Q) =
        (triangularSubst P - P) + (triangularSubst Q - Q) by abel]
      exact add_mem hP hQ
  | smul r P _ hP =>
      rw [map_smul, ← smul_sub]
      exact Submodule.smul_mem _ _ hP

/-- Every ordinary jet polynomial has bounded additive derivative degree. -/
lemma exists_mem_filt (P : JetAlgebra) : ∃ d, P ∈ filt d := by
  induction P using SymmetricAlgebra.induction with
  | algebraMap r => exact ⟨0, algebraMap_mem_filt_zero r⟩
  | ι v =>
      let r := JetComponentSpace.basis.repr v
      let d := r.support.sup genDeg
      refine ⟨d, ?_⟩
      have hv : SymmetricAlgebra.ι ℝ JetComponentSpace v =
          r.sum (fun g a => a • ofGen g) := by
        conv_lhs => rw [← JetComponentSpace.basis.linearCombination_repr v]
        rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [map_smul]
        rfl
      rw [hv, Finsupp.sum]
      refine Submodule.sum_mem (filt d) fun g hg => ?_
      exact Submodule.smul_mem _ _
        (filt_mono (show genDeg g ≤ d from Finset.le_sup hg) (ofGen_mem_filt g))
  | mul P Q hP hQ =>
      obtain ⟨d, hd⟩ := hP
      obtain ⟨e, he⟩ := hQ
      exact ⟨d + e, mul_mem_filt hd he⟩
  | add P Q hP hQ =>
      obtain ⟨d, hd⟩ := hP
      obtain ⟨e, he⟩ := hQ
      exact ⟨max d e, add_mem (filt_mono (le_max_left _ _) hd)
        (filt_mono (le_max_right _ _) he)⟩

private lemma eq_zero_of_triangularSubst_eq_zero {d : ℕ} :
    ∀ {P : JetAlgebra}, P ∈ filt d → triangularSubst P = 0 → P = 0 := by
  induction d with
  | zero =>
      intro P hP h0
      have h := triangularSubst_sub_self_mem_sfilt hP
      rw [h0, zero_sub, sfilt_zero, Submodule.mem_bot, neg_eq_zero] at h
      exact h
  | succ d ih =>
      intro P hP h0
      have h := triangularSubst_sub_self_mem_sfilt hP
      rw [h0, zero_sub, sfilt_succ] at h
      exact ih (neg_mem_iff.mp h) h0

lemma triangularSubst_injective : Function.Injective triangularSubst := by
  intro P Q hPQ
  obtain ⟨d, hd⟩ := exists_mem_filt (P - Q)
  have h0 : triangularSubst (P - Q) = 0 := by rw [map_sub, hPQ, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_triangularSubst_eq_zero hd h0)

private lemma exists_triangularSubst_eq {d : ℕ} :
    ∀ {P : JetAlgebra}, P ∈ filt d → ∃ Q, triangularSubst Q = P := by
  induction d with
  | zero =>
      intro P hP
      have h := triangularSubst_sub_self_mem_sfilt hP
      rw [sfilt_zero, Submodule.mem_bot, sub_eq_zero] at h
      exact ⟨P, h⟩
  | succ d ih =>
      intro P hP
      have h := triangularSubst_sub_self_mem_sfilt hP
      rw [sfilt_succ] at h
      obtain ⟨Q, hQ⟩ := ih h
      exact ⟨P - Q, by rw [map_sub, hQ, sub_sub_cancel]⟩

lemma triangularSubst_surjective : Function.Surjective triangularSubst := by
  intro P
  obtain ⟨d, hd⟩ := exists_mem_filt P
  exact exists_triangularSubst_eq hd

/-- **The arbitrary-order triangular coordinate equivalence.** -/
noncomputable def covariantEquiv : JetAlgebra ≃ₐ[ℝ] JetAlgebra :=
  AlgEquiv.ofBijective triangularSubst ⟨triangularSubst_injective, triangularSubst_surjective⟩

@[simp]
lemma covariantEquiv_apply (P : JetAlgebra) : covariantEquiv P = triangularSubst P := rfl

lemma triangularSubst_totalComponent {w : DIdx} {mu : Lor} (hmu : w mu ≠ 0) (c : Col) :
    triangularSubst (totalComponent w mu c) =
      totalComponent w mu c + hookCorrection w mu c - correctionAverage w c := by
  rw [totalComponent, triangularSubst_ofGen, triangularGen]
  rw [predAt_add_single hmu]

/-- Every independent linear hook is sent to the matching symmetrized covariant curvature
derivative. -/
lemma triangularSubst_hookDiff (i : AllHookIdx) (c : Col) :
    triangularSubst (hookDiff i c) = covHook i c := by
  rw [hookDiff, map_sub, triangularSubst_totalComponent i.mu_supported,
    triangularSubst_totalComponent (layerDir_coeff_ne_zero i.w_ne_zero),
    hookCorrection_dir, hookCorrection_eq]
  rw [hookDiff]
  abel

/-- The fully symmetric connection coordinate is fixed by the normalized substitution. -/
lemma triangularSubst_symConn {w : DIdx} (hw : w ≠ 0) (c : Col) :
    triangularSubst (symConn w c) = symConn w c := by
  rw [symConn, map_smul, map_sum]
  have hterm : ∀ mu : Lor,
      triangularSubst ((w mu : ℝ) • totalComponent w mu c) =
        (w mu : ℝ) • (totalComponent w mu c + hookCorrection w mu c -
          correctionAverage w c) := by
    intro mu
    by_cases hmu : w mu ≠ 0
    · rw [map_smul, triangularSubst_totalComponent hmu]
    · have hz : w mu = 0 := not_ne_iff.mp hmu
      simp [hz]
  rw [Finset.sum_congr rfl fun mu _ => hterm mu]
  have hdeg : (lorDeg w : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt ((lorDeg_pos_iff w).2 hw))
  have hsum : ∑ mu : Lor, (w mu : ℝ) = lorDeg w := by norm_cast
  simp_rw [smul_sub, smul_add]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_smul, hsum,
    correctionAverage, smul_smul, mul_inv_cancel₀ hdeg, one_smul]
  module

/-!
## E. The parametric triangular coordinate identity
-/

/-- The covariant hook component extended to every displayed supported direction; the
distinguished component is zero. -/
noncomputable def covHookAt (w : DIdx) (mu : Lor) (c : Col) : JetAlgebra :=
  totalComponent w mu c - totalComponent w (layerDir w) c + hookCorrection w mu c

/-- The weighted average of the displayed covariant hook components. -/
noncomputable def covHookAverage (w : DIdx) (c : Col) : JetAlgebra :=
  (lorDeg w : ℝ)⁻¹ • ∑ mu : Lor, (w mu : ℝ) • covHookAt w mu c

/-- The strict lower-order remainder in the inverse triangular coordinate formula. -/
noncomputable def triangularLower (w : DIdx) (mu : Lor) (c : Col) : JetAlgebra :=
  correctionAverage w c - hookCorrection w mu c

lemma covHookAt_eq_covHook (i : AllHookIdx) (c : Col) :
    covHookAt i.w i.mu c = covHook i c := by
  rw [covHookAt, hookCorrection_eq, hookDiff]
  abel

lemma covHookAt_dir (w : DIdx) (c : Col) : covHookAt w (layerDir w) c = 0 := by
  rw [covHookAt, hookCorrection_dir, sub_self, zero_add]

lemma covHookAverage_eq (w : DIdx) (c : Col) :
    covHookAverage w c = hookAverage w c + correctionAverage w c := by
  unfold covHookAverage hookAverage correctionAverage covHookAt
  simp_rw [smul_add]
  rw [Finset.sum_add_distrib, smul_add]

lemma triangularLower_mem_sfilt (w : DIdx) (mu : Lor) (c : Col) :
    triangularLower w mu c ∈ sfilt (lorDeg w - 1) := by
  exact sub_mem (correctionAverage_mem_sfilt w c) (hookCorrection_mem_sfilt w mu c)

/-- **The arbitrary-order Brandt triangular identity.**  Every ordinary component is the fully
symmetric connection coordinate plus its independent covariant hook component, minus the weighted
hook average needed by the explicit inverse, plus a term of strictly smaller additive derivative
degree.  For an `AllHookIdx`, `covHookAt_eq_covHook` identifies the displayed hook with the
symmetrized `D^(|w|-2) F` from `CovariantTower`. -/
lemma ordinary_eq_symmetric_add_covariant_hook {w : DIdx} (hw : w ≠ 0)
    {mu : Lor} (hmu : w mu ≠ 0) (c : Col) :
    totalComponent w mu c =
      symConn w c + covHookAt w mu c - covHookAverage w c + triangularLower w mu c := by
  rw [covHookAverage_eq, covHookAt, triangularLower]
  have h := totalComponent_eq_symConn_add_hook_sub hw hmu c
  rw [show totalComponent w mu c - totalComponent w (layerDir w) c =
      totalComponent w mu c - totalComponent w (layerDir w) c from rfl]
  linear_combination h

end SU3Jet
end StandardModel
