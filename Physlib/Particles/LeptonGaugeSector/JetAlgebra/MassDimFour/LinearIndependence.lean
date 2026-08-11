/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.FermionicBarKineticTerm.LinearIndependence
public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.GaugeDoubleDeriv.LinearIndependence
public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.CovariantAlgebra
/-!
# Independence of the four mass-dimension-four sectors

## i. Overview

The four sectors an invariant of mass dimension four decomposes into —

| sector | spanned by |
|---|---|
| `A` | `D̄_μ ψ̄_α ψ_β` |
| `B` | `ψ̄_α D_μ ψ_β` |
| `C` | `∂_ρ ∂_τ F_{μν}` |
| `D` | `F_{μν} F_{μ'ν'}` |

— are independent: `eq_zero_of_massDimFour_sum_eq_zero` says that if one element of each sums to
zero then all four are zero. Equivalently the sum `A ⊔ B ⊔ C ⊔ D` is direct.

## ii. Why it is wanted

Each sector has been cut down to its invariants separately, and those four results are combined
in `MassDimFour.Classification`. They do not compose without this file: membership of the join
gives a decomposition `x = a + b + c + d`, but every sector theorem needs *its own* summand to be
invariant, and invariance of `x` says nothing about the summands unless the decomposition is
unique. Independence is exactly that uniqueness.

Only one of the three splittings is genuinely delicate. Fermionic against bosonic is the lepton
exterior degree, `2` against `0`; `∂∂F` against `F F` is the gauge-field degree, `1` against `2`.
But `A` against `B` — whether the derivative sits on `ψ̄` or on `ψ` — is separated by no grading
at all: `D̄_μ ψ̄_α ψ_β = ∂_μ ψ̄_α ψ_β + 6 i B_μ ψ̄_α ψ_β` is inhomogeneous for every grading in
sight, the covariant derivative being what mixes them. It needs a dual family.

## iii. The dual families

Each sector file already carries a family of functionals dual to its own spanning set. What is
added here is that each family is blind to the other three sectors.

- `fermionDual` reads a coefficient of `ψ̄_α D_μ ψ_β`. Being an exterior *degree-two* functional
  it kills the two bosonic sectors outright; and on `D̄_μ ψ̄_α ψ_β` it vanishes because it looks
  for a derivative index on the unbarred factor, where there is none.
- `fermionBarDual` is the mirror image.
- `gaugeDerivDual'` reads a coefficient of a gauge-field generator. It is built here as the
  *linear part* of the gauge-field evaluation — `gaugeDerivDual` corrected by half the second
  polarization — so that, unlike `gaugeDerivDual` itself, it annihilates the photon pairs. The
  augmentation of the lepton factor it carries kills the two fermionic sectors.

## iv. Key results

- `JetAlgebra.gaugeDerivDual'` : the linear part of the gauge-field evaluation.
- `JetAlgebra.eq_zero_of_forall_fermionDual_eq_zero` and its two companions : each family
  separates its own sector.
- `JetAlgebra.eq_zero_of_massDimFour_sum_eq_zero` : **the four sectors are independent**.

## v. Table of contents

- A. The fermionic duals are blind to the other sectors
- B. The gauge duals are blind to the fermionic sectors
- C. The linear part of the gauge-field evaluation
- D. Each family separates its own sector
- E. Independence of the four sectors

-/

@[expose] public section

namespace LeptonGaugeSector
open TensorProduct StandardModel

namespace JetAlgebra

/-!

## A. The fermionic duals are blind to the other sectors

`fermionPairDual` is an exterior degree-two functional on the lepton factor, so it vanishes on
anything whose lepton factor is trivial — which is what the two bosonic sectors are. On the
opposite fermionic sector it vanishes for a different reason: `fermionDual` looks for a
derivative index on the unbarred factor, and in `D̄_μ ψ̄_α ψ_β` there is none.

-/

/-- The degree-two functional vanishes on the unit: the alternating family defining it is zero
  outside degree two. -/
@[simp]
lemma extPairDual_one {V : Type} [AddCommGroup V] [Module ℂ V]
    (φ ψ : Module.Dual ℂ V) : extPairDual φ ψ 1 = 0 := by
  rw [extPairDual, ExteriorAlgebra.liftAlternating_one]
  rfl

/-- The fermionic duals vanish on an element with trivial lepton factor. -/
@[simp]
lemma fermionPairDual_tmul_one (φ ψ : Module.Dual ℂ LeptonSinglet.JetComponentSpace)
    (a : ℂ ⊗[ℝ] BBoson.JetAlgebra) : fermionPairDual φ ψ (a ⊗ⱼ 1) = 0 := by
  rw [fermionPairDual_tmul, extPairDual_one, mul_zero]

/-- The fermionic duals vanish on a field-strength derivative. -/
@[simp]
lemma fermionPairDual_fieldStrengthDeriv (φ ψ : Module.Dual ℂ LeptonSinglet.JetComponentSpace)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) :
    fermionPairDual φ ψ (fieldStrengthDeriv s μ ν) = 0 :=
  fermionPairDual_tmul_one φ ψ _

/-- The fermionic duals vanish on a photon pair. -/
@[simp]
lemma fermionPairDual_fieldStrengthDeriv_mul
    (φ ψ : Module.Dual ℂ LeptonSinglet.JetComponentSpace)
    (s s' : Multiset (Fin 1 ⊕ Fin 3)) (μ ν μ' ν' : Fin 1 ⊕ Fin 3) :
    fermionPairDual φ ψ (fieldStrengthDeriv s μ ν * fieldStrengthDeriv s' μ' ν') = 0 := by
  rw [fieldStrengthDeriv, fieldStrengthDeriv, tmul_mul_tmul, mul_one, fermionPairDual_tmul_one]

/-- **`fermionDual` is blind to the conjugate kinetic sector.** It reads the coefficient of
  `ψ̄_α D_μ ψ_β`, where the derivative index sits on the unbarred factor; in `D̄_μ ψ̄_α ψ_β` it
  sits on the barred one, so neither term of the product matches. -/
@[simp]
lemma fermionDual_Dbarψ_singleton_mul_Dψ_nil (q : Fin 2 × (Fin 1 ⊕ Fin 3) × Fin 2)
    (α : Fin 2) (μ : Fin 1 ⊕ Fin 3) (β : Fin 2) :
    fermionDual q (Dbarψ [μ] α * Dψ [] β) = 0 := by
  obtain ⟨α₀, μ₀, β₀⟩ := q
  rw [Dbarψ_singleton, Dψ_nil, add_mul, smul_mul_assoc, mul_assoc]
  simp only [ofGenerator_dbarψ_eq, ofGenerator_dψ_eq, ofGenerator_B_eq,
    JetAlgebra.tmul_mul_tmul, one_mul, map_add, map_smul,
    fermionDual, fermionPairDual_tmul,
    LeptonSinglet.JetAlgebra.ofGenerator, extPairDual_ι_mul_ι]
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_apply, LeptonSinglet.JetGenerators.dbarψ.injEq,
    LeptonSinglet.JetGenerators.dψ.injEq, reduceCtorEq]
  simp

/-- **`fermionBarDual` is blind to the kinetic sector.** The mirror image of
  `fermionDual_Dbarψ_singleton_mul_Dψ_nil`. -/
@[simp]
lemma fermionBarDual_Dbarψ_nil_mul_Dψ_singleton (q : Fin 2 × (Fin 1 ⊕ Fin 3) × Fin 2)
    (α : Fin 2) (μ : Fin 1 ⊕ Fin 3) (β : Fin 2) :
    fermionBarDual q (Dbarψ [] α * Dψ [μ] β) = 0 := by
  obtain ⟨α₀, μ₀, β₀⟩ := q
  rw [Dbarψ_nil, Dψ_singleton, mul_sub, mul_smul_comm, ← mul_assoc]
  simp only [ofGenerator_dbarψ_eq, ofGenerator_dψ_eq, ofGenerator_B_eq,
    JetAlgebra.tmul_mul_tmul, mul_one, map_sub, map_smul,
    fermionBarDual, fermionPairDual_tmul,
    LeptonSinglet.JetAlgebra.ofGenerator, extPairDual_ι_mul_ι]
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_apply, LeptonSinglet.JetGenerators.dbarψ.injEq,
    LeptonSinglet.JetGenerators.dψ.injEq, reduceCtorEq]
  simp

/-!

## B. The gauge duals are blind to the fermionic sectors

Both gauge dual families are a functional on the B-boson factor tensored with the augmentation
`augL` of the lepton factor. The augmentation kills a single lepton component function, so such
a dual vanishes on a product of two linear-matter elements — which is what a fermion bilinear
is.

-/

/-- A functional on the B-boson factor, extended to the jet algebra by the augmentation of the
  lepton factor. Both `gaugeLinDual` and `gaugePairDual` are of this form. -/
noncomputable def augLDual (f : (ℂ ⊗[ℝ] BBoson.JetAlgebra) →ₗ[ℂ] ℂ) : JetAlgebra →ₗ[ℂ] ℂ :=
  TensorProduct.lift (((LinearMap.mul ℂ ℂ).comp f).compl₂ augL.toLinearMap)

@[simp]
lemma augLDual_tmul (f : (ℂ ⊗[ℝ] BBoson.JetAlgebra) →ₗ[ℂ] ℂ)
    (a : ℂ ⊗[ℝ] BBoson.JetAlgebra) (b : LeptonSinglet.JetAlgebra) :
    augLDual f (a ⊗ⱼ b) = f a * augL b := rfl

lemma gaugePairDual_eq (φ ψ : BBoson.JetComponentSpace →ₗ[ℝ] ℂ) :
    gaugePairDual φ ψ = augLDual (symPairDual φ ψ) := rfl

lemma gaugeLinDual_eq (φ : BBoson.JetComponentSpace →ₗ[ℝ] ℂ) :
    gaugeLinDual φ = augLDual (symLinDual φ) := rfl

/-- The augmentation kills a lepton component function. -/
@[simp]
lemma augL_ι (m : LeptonSinglet.JetComponentSpace) : augL (ExteriorAlgebra.ι ℂ m) = 0 := by
  rw [augL, ExteriorAlgebra.lift_ι_apply]
  rfl

/-- **The gauge duals vanish on a product of two linear-matter elements.** The lepton factor of
  such a product has exterior degree two, and the augmentation kills it. -/
lemma augLDual_mul_of_mem_LinearMatterSubmodule (f : (ℂ ⊗[ℝ] BBoson.JetAlgebra) →ₗ[ℂ] ℂ)
    {u v : JetAlgebra} (hu : u ∈ LinearMatterSubmodule) (hv : v ∈ LinearMatterSubmodule) :
    augLDual f (u * v) = 0 := by
  have hd₁ : ∀ a b c : JetAlgebra, (a + b) * c = a * c + b * c := distrib_add_mul
  have hd₂ : ∀ a b c : JetAlgebra, a * (b + c) = a * b + a * c := distrib_mul_add
  have hs₁ : ∀ (r : ℂ) (a b : JetAlgebra), (r • a) * b = r • (a * b) :=
    fun r a b => smul_mul_assoc r a b
  have hs₂ : ∀ (r : ℂ) (a b : JetAlgebra), a * (r • b) = r • (a * b) :=
    fun r a b => mul_smul_comm r a b
  induction hu using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨p, m, rfl⟩ := hz
    induction hv using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨q, n, rfl⟩ := hw
      rw [tmul_mul_tmul, augLDual_tmul, map_mul augL, augL_ι, zero_mul, mul_zero]
    | zero => rw [mul_zero, map_zero]
    | add a b _ _ ha hb => rw [hd₂, map_add, ha, hb, add_zero]
    | smul r a _ ha => rw [hs₂, map_smul, ha, smul_zero]
  | zero => rw [zero_mul, map_zero]
  | add a b _ _ ha hb => rw [hd₁, map_add, ha, hb, add_zero]
  | smul r a _ ha => rw [hs₁, map_smul, ha, smul_zero]

/-- The gauge duals vanish on a fermion bilinear. -/
lemma augLDual_Dbarψ_mul_Dψ (f : (ℂ ⊗[ℝ] BBoson.JetAlgebra) →ₗ[ℂ] ℂ)
    (l l' : List (Fin 1 ⊕ Fin 3)) (α β : Fin 2) :
    augLDual f (Dbarψ l α * Dψ l' β) = 0 :=
  augLDual_mul_of_mem_LinearMatterSubmodule f (Dbarψ_mem_LinearMatterSubmodule l α)
    (Dψ_mem_LinearMatterSubmodule l' β)

/-!

## C. The linear part of the gauge-field evaluation

`gaugeDerivDual` reads the coefficient of a gauge-field generator, but it is the *affine*
difference `symEval φ - symEval 0`, which on a degree-two monomial `g h` returns `φ g · φ h`
rather than zero. Subtracting half the second polarization, which returns `2 φ g · φ h` there
and vanishes in degree one, leaves the genuine linear part: `gaugeDerivDual'` still reads the
coefficient of a generator, and now annihilates the photon pairs as well.

-/

/-- The coordinate functional at the gauge-field generator `p`, valued in `ℂ`. -/
noncomputable def bCoord (p : Multiset (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)) :
    BBoson.JetComponentSpace →ₗ[ℝ] ℂ :=
  (BBoson.JetComponentSpace.basis.coord (BBoson.JetGenerators.dB p.1 p.2)).smulRight (1 : ℂ)

@[simp]
lemma bCoord_basis (p q : Multiset (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)) :
    bCoord p (BBoson.JetComponentSpace.basis (BBoson.JetGenerators.dB q.1 q.2)) =
      if q = p then 1 else 0 := by
  rw [bCoord, LinearMap.smulRight_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_apply]
  by_cases h : q = p
  · subst h
    simp
  · have hne : ¬ BBoson.JetGenerators.dB q.1 q.2 = BBoson.JetGenerators.dB p.1 p.2 := by
      rw [BBoson.JetGenerators.dB.injEq]
      exact fun hg => h (Prod.ext hg.1 hg.2)
    rw [if_neg hne, if_neg h, zero_smul]

/-- `gaugeDerivDual` is the affine difference at the coordinate functional. -/
lemma gaugeDerivDual_eq (p : Multiset (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)) :
    gaugeDerivDual p = gaugeLinDual (bCoord p) := rfl

/-- **The linear part of the gauge-field evaluation.** It reads the coefficient of the
  gauge-field generator `p`, and is blind to the degrees zero and two. -/
noncomputable def gaugeDerivDual' (p : Multiset (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)) :
    JetAlgebra →ₗ[ℂ] ℂ :=
  gaugeDerivDual p - (2⁻¹ : ℂ) • gaugePairDual (bCoord p) (bCoord p)

lemma gaugeDerivDual'_apply (p : Multiset (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)) (x : JetAlgebra) :
    gaugeDerivDual' p x =
      gaugeDerivDual p x - (2⁻¹ : ℂ) * gaugePairDual (bCoord p) (bCoord p) x := by
  rw [gaugeDerivDual', LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]

/-- On a field-strength derivative the correction term vanishes, and the linear part reads the
  same antisymmetric coefficient as `gaugeDerivDual`. -/
@[simp]
lemma gaugeDerivDual'_fieldStrengthDeriv (p : Multiset (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3))
    (s : Multiset (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) :
    gaugeDerivDual' p (fieldStrengthDeriv s μ ν) = fsDerivCoeff p s μ ν := by
  rw [gaugeDerivDual'_apply, gaugeDerivDual_fieldStrengthDeriv,
    gaugePairDual_fieldStrengthDeriv, mul_zero, sub_zero]

/-- The linear part reads the coefficient of a gauge-field generator. -/
@[simp]
lemma gaugeDerivDual'_ofGenerator (p q : Multiset (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)) :
    gaugeDerivDual' p (ofGenerator (JetGenerators.dB q.1 q.2)) = if q = p then 1 else 0 := by
  rw [gaugeDerivDual'_apply, gaugeDerivDual_eq, gaugeLinDual_ofGenerator,
    show gaugePairDual (bCoord p) (bCoord p) (ofGenerator (JetGenerators.dB q.1 q.2)) = 0 from by
      rw [ofGenerator_B_eq, gaugePairDual_tmul, symPairDual_tmul_ofGenerator_eq_zero, zero_mul],
    mul_zero, sub_zero, bCoord_basis]

/-- The affine difference on a degree-two monomial is the product of the two values. -/
lemma symLinDual_tmul_ofGenerator_mul (φ : BBoson.JetComponentSpace →ₗ[ℝ] ℂ)
    (g h : BBoson.JetGenerators) :
    symLinDual φ ((1 ⊗ₜ[ℝ] BBoson.JetAlgebra.ofGenerator g) *
        (1 ⊗ₜ[ℝ] BBoson.JetAlgebra.ofGenerator h)) =
      φ (BBoson.JetComponentSpace.basis g) * φ (BBoson.JetComponentSpace.basis h) := by
  simp only [symLinDual, LinearMap.sub_apply, AlgHom.toLinearMap_apply, map_mul,
    symEval_tmul_ofGenerator, LinearMap.zero_apply]
  ring

/-- **The linear part annihilates a product of two gauge-field generators.** The affine
  difference returns `φ g · φ h` there and half the second polarization returns the same. -/
lemma gaugeDerivDual'_ofGenerator_mul (p : Multiset (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3))
    (g h : BBoson.JetGenerators) :
    gaugeDerivDual' p (ofGenerator (JetGenerators.dB g.1 g.2) *
      ofGenerator (JetGenerators.dB h.1 h.2)) = 0 := by
  obtain ⟨s, μ⟩ := g
  obtain ⟨t, ν⟩ := h
  rw [gaugeDerivDual'_apply, gaugeDerivDual_eq, gaugeLinDual_eq, gaugePairDual_eq,
    ofGenerator_B_eq, ofGenerator_B_eq, tmul_mul_tmul, mul_one, augLDual_tmul, augLDual_tmul,
    map_one, mul_one, mul_one, symLinDual_tmul_ofGenerator_mul,
    symPairDual_tmul_ofGenerator_mul]
  ring

/-- The linear part annihilates a photon pair: each field strength is a difference of two
  gauge-field generators, so the product is a combination of degree-two monomials. -/
@[simp]
lemma gaugeDerivDual'_fieldStrengthDeriv_mul (p : Multiset (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3))
    (s s' : Multiset (Fin 1 ⊕ Fin 3)) (μ ν μ' ν' : Fin 1 ⊕ Fin 3) :
    gaugeDerivDual' p (fieldStrengthDeriv s μ ν * fieldStrengthDeriv s' μ' ν') = 0 := by
  have hg : ∀ (a b : Multiset (Fin 1 ⊕ Fin 3)) (σ τ : Fin 1 ⊕ Fin 3),
      gaugeDerivDual' p (ofGenerator (JetGenerators.dB a σ) *
        ofGenerator (JetGenerators.dB b τ)) = 0 :=
    fun a b σ τ => gaugeDerivDual'_ofGenerator_mul p
      (BBoson.JetGenerators.dB a σ) (BBoson.JetGenerators.dB b τ)
  rw [fieldStrengthDeriv_eq_sub, fieldStrengthDeriv_eq_sub, sub_mul, mul_sub, mul_sub,
    map_sub, map_sub, map_sub,
    hg (s + {μ}) (s' + {μ'}) ν ν', hg (s + {μ}) (s' + {ν'}) ν μ',
    hg (s + {ν}) (s' + {μ'}) μ ν', hg (s + {ν}) (s' + {ν'}) μ μ']
  ring

/-- The linear part annihilates a fermion bilinear: it carries the augmentation of the lepton
  factor. -/
@[simp]
lemma gaugeDerivDual'_Dbarψ_mul_Dψ (p : Multiset (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3))
    (l l' : List (Fin 1 ⊕ Fin 3)) (α β : Fin 2) :
    gaugeDerivDual' p (Dbarψ l α * Dψ l' β) = 0 := by
  rw [gaugeDerivDual'_apply, gaugeDerivDual_eq, gaugeLinDual_eq, gaugePairDual_eq,
    augLDual_Dbarψ_mul_Dψ, augLDual_Dbarψ_mul_Dψ, mul_zero, sub_zero]

/-!

## D. Each family separates its own sector

A functional vanishing on a spanning set vanishes on the span, so the cross-vanishing above
extends from the generators to the sectors. In the other direction each family is dual to its
own spanning set, so an element of that sector on which the whole family vanishes is zero.

-/

/-- A functional vanishing on a spanning set vanishes on the span. -/
lemma apply_eq_zero_of_mem_span {f : JetAlgebra →ₗ[ℂ] ℂ} {S : Set JetAlgebra}
    (hS : ∀ y ∈ S, f y = 0) {x : JetAlgebra} (hx : x ∈ Submodule.span ℂ S) : f x = 0 :=
  Submodule.span_le.mpr (fun y hy => LinearMap.mem_ker.mpr (hS y hy)) hx

/-- The kinetic sector, presented as the span of a family indexed by a finite type. -/
lemma span_Dbarψ_nil_mul_Dψ_singleton_eq :
    {y : JetAlgebra | ∃ α μ β, y = Dbarψ [] α * Dψ [μ] β} =
      Set.range fun p : Fin 2 × (Fin 1 ⊕ Fin 3) × Fin 2 => Dbarψ [] p.1 * Dψ [p.2.1] p.2.2 :=
  Set.ext fun _ => ⟨fun ⟨α, μ, β, h⟩ => ⟨(α, μ, β), h.symm⟩,
    fun ⟨p, h⟩ => ⟨p.1, p.2.1, p.2.2, h.symm⟩⟩

/-- The conjugate kinetic sector, presented as the span of a family indexed by a finite type. -/
lemma span_Dbarψ_singleton_mul_Dψ_nil_eq :
    {y : JetAlgebra | ∃ α μ β, y = Dbarψ [μ] α * Dψ [] β} =
      Set.range fun p : Fin 2 × (Fin 1 ⊕ Fin 3) × Fin 2 => Dbarψ [p.2.1] p.1 * Dψ [] p.2.2 :=
  Set.ext fun _ => ⟨fun ⟨α, μ, β, h⟩ => ⟨(α, μ, β), h.symm⟩,
    fun ⟨p, h⟩ => ⟨p.1, p.2.1, p.2.2, h.symm⟩⟩

/-- **`fermionDual` separates the kinetic sector.** -/
lemma eq_zero_of_forall_fermionDual_eq_zero {x : JetAlgebra}
    (hx : x ∈ Submodule.span ℂ {y : JetAlgebra | ∃ α μ β, y = Dbarψ [] α * Dψ [μ] β})
    (h : ∀ q, fermionDual q x = 0) : x = 0 := by
  rw [span_Dbarψ_nil_mul_Dψ_singleton_eq, Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, rfl⟩ := hx
  have hc : ∀ q, c q = 0 := by
    intro q
    have hq := h q
    rw [map_sum] at hq
    simp only [map_smul, smul_eq_mul, fermionDual_Dbarψ_mul_Dψ, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq' Finset.univ q c, Finset.mem_univ, if_true] at hq
    exact hq
  simp only [hc, zero_smul, Finset.sum_const_zero]

/-- **`fermionBarDual` separates the conjugate kinetic sector.** -/
lemma eq_zero_of_forall_fermionBarDual_eq_zero {x : JetAlgebra}
    (hx : x ∈ Submodule.span ℂ {y : JetAlgebra | ∃ α μ β, y = Dbarψ [μ] α * Dψ [] β})
    (h : ∀ q, fermionBarDual q x = 0) : x = 0 := by
  rw [span_Dbarψ_singleton_mul_Dψ_nil_eq, Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, rfl⟩ := hx
  have hc : ∀ q, c q = 0 := by
    intro q
    have hq := h q
    rw [map_sum] at hq
    simp only [map_smul, smul_eq_mul, fermionBarDual_Dbarψ_mul_Dψ, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq' Finset.univ q c, Finset.mem_univ, if_true] at hq
    exact hq
  simp only [hc, zero_smul, Finset.sum_const_zero]

/-- The span of the gauge-field generators: the elements linear in the gauge field. -/
noncomputable def gaugeGenSpan : Submodule ℂ JetAlgebra :=
  Submodule.span ℂ (Set.range fun p : Multiset (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) =>
    ofGenerator (JetGenerators.dB p.1 p.2))

/-- A gauge-field generator is linear in the gauge field. -/
lemma ofGenerator_dB_mem_gaugeGenSpan (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) :
    ofGenerator (JetGenerators.dB s μ) ∈ gaugeGenSpan :=
  Submodule.subset_span ⟨(s, μ), rfl⟩

/-- A field-strength derivative is linear in the gauge field. -/
lemma fieldStrengthDeriv_mem_gaugeGenSpan (s : Multiset (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) : fieldStrengthDeriv s μ ν ∈ gaugeGenSpan := by
  rw [fieldStrengthDeriv_eq_sub]
  exact sub_mem (ofGenerator_dB_mem_gaugeGenSpan _ _) (ofGenerator_dB_mem_gaugeGenSpan _ _)

/-- **The linear parts separate the elements linear in the gauge field.** -/
lemma eq_zero_of_mem_gaugeGenSpan_of_forall_gaugeDerivDual' {x : JetAlgebra}
    (hx : x ∈ gaugeGenSpan) (h : ∀ p, gaugeDerivDual' p x = 0) : x = 0 := by
  classical
  rw [gaugeGenSpan, Finsupp.mem_span_range_iff_exists_finsupp] at hx
  obtain ⟨c, rfl⟩ := hx
  have hc : ∀ p, c p = 0 := by
    intro p
    have hp := h p
    rw [Finsupp.sum, map_sum] at hp
    simp only [map_smul, smul_eq_mul, gaugeDerivDual'_ofGenerator, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq' c.support p c] at hp
    by_cases hs : p ∈ c.support
    · rwa [if_pos hs] at hp
    · exact Finsupp.notMem_support_iff.mp hs
  rw [show c = 0 from Finsupp.ext hc, Finsupp.sum_zero_index]

/-- **The linear parts separate the sector of second derivatives of the field strength.** -/
lemma eq_zero_of_forall_gaugeDerivDual'_eq_zero {x : JetAlgebra}
    (hx : x ∈ Submodule.span ℂ {y : JetAlgebra | ∃ ρ τ μ ν, y = fieldStrengthDeriv {ρ, τ} μ ν})
    (h : ∀ p, gaugeDerivDual' p x = 0) : x = 0 := by
  refine eq_zero_of_mem_gaugeGenSpan_of_forall_gaugeDerivDual' (Submodule.span_le.mpr ?_ hx) h
  rintro _ ⟨ρ, τ, μ, ν, rfl⟩
  exact fieldStrengthDeriv_mem_gaugeGenSpan {ρ, τ} μ ν

/-!

## E. Independence of the four sectors

Each family kills the three sectors that are not its own, so applying it to a vanishing sum of
four sector elements leaves only its own summand, which it then separates. The photon pairs are
reached last, by subtraction.

-/

/-- **The four mass-dimension-four sectors are independent.** If one element of each sums to
  zero then all four vanish; equivalently the join of the four sector spans is direct. This is
  what makes the sector components of an invariant well defined, and hence invariant. -/
theorem eq_zero_of_massDimFour_sum_eq_zero {a b c d : JetAlgebra}
    (ha : a ∈ Submodule.span ℂ {y : JetAlgebra | ∃ α μ β, y = Dbarψ [μ] α * Dψ [] β})
    (hb : b ∈ Submodule.span ℂ {y : JetAlgebra | ∃ α μ β, y = Dbarψ [] α * Dψ [μ] β})
    (hc : c ∈ Submodule.span ℂ {y : JetAlgebra | ∃ ρ τ μ ν, y = fieldStrengthDeriv {ρ, τ} μ ν})
    (hd : d ∈ Submodule.span ℂ {y : JetAlgebra | ∃ μ ν μ' ν',
      y = fieldStrengthDeriv {} μ ν * fieldStrengthDeriv {} μ' ν'})
    (h : a + b + c + d = 0) : a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have hb0 : b = 0 := by
    refine eq_zero_of_forall_fermionDual_eq_zero hb fun q => ?_
    have hqa : fermionDual q a = 0 :=
      apply_eq_zero_of_mem_span (by rintro _ ⟨α, μ, β, rfl⟩; exact
        fermionDual_Dbarψ_singleton_mul_Dψ_nil q α μ β) ha
    have hqc : fermionDual q c = 0 :=
      apply_eq_zero_of_mem_span (by rintro _ ⟨ρ, τ, μ, ν, rfl⟩; exact
        fermionPairDual_fieldStrengthDeriv _ _ _ _ _) hc
    have hqd : fermionDual q d = 0 :=
      apply_eq_zero_of_mem_span (by rintro _ ⟨μ, ν, μ', ν', rfl⟩; exact
        fermionPairDual_fieldStrengthDeriv_mul _ _ _ _ _ _ _ _) hd
    have hsum := congrArg (fermionDual q) h
    rw [map_add, map_add, map_add, map_zero, hqa, hqc, hqd] at hsum
    simpa using hsum
  have ha0 : a = 0 := by
    refine eq_zero_of_forall_fermionBarDual_eq_zero ha fun q => ?_
    have hqb : fermionBarDual q b = 0 :=
      apply_eq_zero_of_mem_span (by rintro _ ⟨α, μ, β, rfl⟩; exact
        fermionBarDual_Dbarψ_nil_mul_Dψ_singleton q α μ β) hb
    have hqc : fermionBarDual q c = 0 :=
      apply_eq_zero_of_mem_span (by rintro _ ⟨ρ, τ, μ, ν, rfl⟩; exact
        fermionPairDual_fieldStrengthDeriv _ _ _ _ _) hc
    have hqd : fermionBarDual q d = 0 :=
      apply_eq_zero_of_mem_span (by rintro _ ⟨μ, ν, μ', ν', rfl⟩; exact
        fermionPairDual_fieldStrengthDeriv_mul _ _ _ _ _ _ _ _) hd
    have hsum := congrArg (fermionBarDual q) h
    rw [map_add, map_add, map_add, map_zero, hqb, hqc, hqd] at hsum
    simpa using hsum
  have hc0 : c = 0 := by
    refine eq_zero_of_forall_gaugeDerivDual'_eq_zero hc fun p => ?_
    have hpd : gaugeDerivDual' p d = 0 :=
      apply_eq_zero_of_mem_span (by rintro _ ⟨μ, ν, μ', ν', rfl⟩; exact
        gaugeDerivDual'_fieldStrengthDeriv_mul _ _ _ _ _ _ _) hd
    have hcd : c + d = 0 := by rw [ha0, hb0, zero_add, zero_add] at h; exact h
    have hsum := congrArg (gaugeDerivDual' p) hcd
    rw [map_add, map_zero, hpd, add_zero] at hsum
    exact hsum
  refine ⟨ha0, hb0, hc0, ?_⟩
  rw [ha0, hb0, hc0, zero_add, zero_add, zero_add] at h
  exact h

end JetAlgebra

end LeptonGaugeSector

end
