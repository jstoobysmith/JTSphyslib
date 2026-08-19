/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.Jet.Basic
public import Physlib.Particles.StandardModel.GaugeAlgebra.JetGaugeAlgebra
public import Physlib.Particles.StandardModel.GaugeGroup.MaurerCartan.Basic
public import Physlib.Relativity.IsLorentzDeriv
public import Physlib.Relativity.Tensors.ComplexTensor.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Representation
public import Physlib.Relativity.SL2C.Basic
/-!
# Algebra valued gauge bosons

An algebra `B` (for instance a jet algebra of Lagrangian terms) may contain a family of
elements playing the role of the gauge-field symbols `[∂_s A_μ^a]`. This file defines
what it means for such a family to *be* a set of gauge bosons: the structure
`IsGaugeField` records the transformation laws that the physicists' gauge field
satisfies, with nothing postulated beyond them.

## The physics

Let `A_μ^a` be a gauge field for the gauge group `G`, with `μ` a spacetime (covector)
index and `a` an adjoint index. Under a gauge transformation `g` the field transforms as

  `A_μ ↦ Ad_g A_μ + mc(g)_μ`,

where `mc(g)_μ = i (∂_μ g) g⁻¹` is the Maurer–Cartan form. The symbols `[∂_s A_μ^a]`
are coordinate functions on the space of field configurations, so the induced (left)
action is the pullback along `g⁻¹`: one substitutes `g⁻¹` into the field law and
differentiates `s` times with the Leibniz rule:

  `g • [∂_s A_μ^a] = ∑_{x+y=s} C(x,y) (∂_x (Ad_{g⁻¹})^a_b)| [∂_y A_μ^b]`
  `                  + (∂_s mc(g⁻¹)_μ^a)|`,

where `C(x,y)` is the multinomial coefficient of the splitting and `|` denotes
evaluation at the base point. All the data on the right is carried by the *jet* of the
gauge transformation, which is why the gauge representation below is a representation
of `JetGaugeGroupI` and not merely of `GaugeGroupI`.

## The formalization dictionary

* `A μ φ` is the symbol `A_μ^a` contracted with a dual adjoint vector `φ`; the
  derivative symbols `[∂_s A_μ^a]` are its images `iteratedD D deriv_comm s (A μ φ)` under the
  total derivative `D`.
* `∂_x (Ad_{g⁻¹})^a_b|` acting on the dual index is `adjointDualCoeff g⁻¹ x φ`:
  include the constant algebra element into jets, act by the adjoint of `g⁻¹`,
  differentiate `x` times, evaluate at the base point, and pair with `φ`.
* The sum `∑_{x+y=s} C(x,y)` is the sum over `s.antidiagonal`: a splitting `(x, y)`
  occurs in the antidiagonal of the multiset `s` with multiplicity exactly `C(x,y)`.
* `(∂_s mc(g⁻¹)_μ)|` is `JetGaugeAlgebra.eval (iteratedDeriv s (maurerCartanForm g⁻¹ μ))`,
  a constant algebra element, paired with `φ` and embedded in `B` as a scalar.

-/

@[expose] public section

namespace StandardModel
open Matrix MatrixGroups TensorProduct
variable {B : Type} [Ring B] [Algebra ℂ B]


/-- The physicists' `∂_x (Ad_{U})^a_b|` acting on the dual adjoint index of a
  gauge-field symbol: precomposition of `φ` with the constant inclusion into jets,
  followed by the adjoint action of `U`, `x` formal derivatives, and evaluation at
  the base point. For `x = 0` this is the dual (contragredient) adjoint action of
  the value `U₀`; for `x ≠ 0` it sees the derivatives of the gauge transformation. -/
noncomputable def adjointDualCoeff (U : JetGaugeGroupI) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] Module.Dual ℝ GaugeAlgebra :=
  (JetGaugeAlgebra.eval.toLinearMap ∘ₗ JetGaugeAlgebra.iteratedDeriv x ∘ₗ
    JetGaugeAlgebra.adjointMap U ∘ₗ JetGaugeAlgebra.ofConstant).dualMap

/-- The family `A` of symbols in the algebra `B` is a gauge field for the total
  derivative `D`, the Lorentz representation `repLorentz` and the gauge representation
  `repGauge`, when it satisfies the transformation laws of the physicists' gauge field:

  * it presupposes (as arguments, not fields) that `D` is a Lorentz derivative — the
    instance `Lorentz.IsLorentzDeriv repLorentz D` — and that its components commute
    (`deriv_comm`), as total derivatives do;
  * the symbol `A_μ^a` carries one covector index, transforming through the columns of
    the Lorentz matrix (`lorentz_A`);
  * under a gauge jet `U` the derivative symbols `[∂_s A_μ^a]` transform by the
    Leibniz expansion of `A_μ ↦ Ad_{U⁻¹} A_μ + mc(U⁻¹)_μ` (`gauge_A`) — the adjoint
    convolution plus the inhomogeneous Maurer–Cartan shift. The inverse makes the
    action a left action, exactly as in `φ'(x) = φ(Λ⁻¹ x)`. -/
structure IsGaugeField (repLorentz : Representation ℂ SL(2,ℂ) B)
    (repGauge : Representation ℂ JetGaugeGroupI B)
    (A : (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (D : (Fin 1 ⊕ Fin 3) → B →ₗ[ℂ] B)
    [Lorentz.IsLorentzDeriv repLorentz D]
    (deriv_comm : ∀ μ ν, (D μ).comp (D ν) = (D ν).comp (D μ)) : Prop where
  /-- The gauge-field symbol carries one covector Lorentz index. -/
  lorentz_apply : ∀ (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra),
    repLorentz Λ (A μ φ) =
      ∑ a, (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) • A a φ
  /-- The gauge transformation of the derivative symbols `[∂_s A_μ^a]`: the Leibniz
    convolution of the dual adjoint action of `U⁻¹` against lower derivative symbols
    (the multiset antidiagonal carries the multinomial coefficients), plus the
    base-point value of the `s`-th derivative of the Maurer–Cartan form of `U⁻¹`. -/
  gauge_apply_deriv : ∀ (U : JetGaugeGroupI) (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℝ GaugeAlgebra),
    repGauge U (Lorentz.iteratedD D deriv_comm s (A μ φ)) =
      (s.antidiagonal.map fun p =>
        Lorentz.iteratedD D deriv_comm p.2 (A μ (adjointDualCoeff U⁻¹ p.1 φ))).sum
      + algebraMap ℂ B
          (φ (JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv s (maurerCartanForm U⁻¹ μ))))
  /-- The gauge action preserves products: gauge transformations act on the algebra of
    local expressions as algebra homomorphisms. -/
  gauge_mul : ∀ (U : JetGaugeGroupI) (b₁ b₂ : B),
    repGauge U (b₁ * b₂) = repGauge U b₁ * repGauge U b₂

namespace IsGaugeField

variable {repLorentz : Representation ℂ SL(2,ℂ) B}
variable {repGauge : Representation ℂ JetGaugeGroupI B}
variable {A : (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B}
variable {D : (Fin 1 ⊕ Fin 3) → B →ₗ[ℂ] B}
variable [Lorentz.IsLorentzDeriv repLorentz D]
variable {D_comm : ∀ μ ν, (D μ).comp (D ν) = (D ν).comp (D μ)}

/-- The canonical equivalence, through finite-dimensional duality, between
  algebra-valued fields `B ⊗ 𝔤` and their component families `φ ↦ A^φ`: the element
  `b ⊗ a` corresponds to the family `φ ↦ φ(a) b`. -/
noncomputable def dualPairEquiv :
    (B ⊗[ℝ] GaugeAlgebra) ≃ₗ[ℝ] (Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B) :=
  TensorProduct.comm ℝ B GaugeAlgebra ≪≫ₗ
    TensorProduct.congr (Module.evalEquiv ℝ GaugeAlgebra) (LinearEquiv.refl ℝ B) ≪≫ₗ
    dualTensorHomEquiv ℝ (Module.Dual ℝ GaugeAlgebra) B

/-- The bracket of two algebra-valued fields: multiplication in `B` on the first
  factors, the Lie bracket of the gauge algebra on the second, so that on pure
  tensors `⁅b₁ ⊗ a₁, b₂ ⊗ a₂⁆ = (b₁ b₂) ⊗ ⁅a₁, a₂⁆`. -/
noncomputable def tensorBracket :
    (B ⊗[ℝ] GaugeAlgebra) →ₗ[ℝ] (B ⊗[ℝ] GaugeAlgebra) →ₗ[ℝ] B ⊗[ℝ] GaugeAlgebra :=
  TensorProduct.curry
    ((TensorProduct.map (TensorProduct.lift (LinearMap.mul ℝ B))
        (TensorProduct.lift (LinearMap.mk₂ ℝ (fun a b => ⁅a, b⁆)
          (fun a a' b => add_lie a a' b) (fun t a b => smul_lie t a b)
          (fun a b b' => lie_add a b b') (fun t a b => lie_smul t a b)))) ∘ₗ
      (TensorProduct.tensorTensorTensorComm ℝ B GaugeAlgebra B GaugeAlgebra).toLinearMap)

/-- The commutator term `⁅A_μ, A_ν⁆` of the field strength, as a component family:
  the physicists' `f^a_{bc} A_μ^b A_ν^c` contracted with a dual adjoint vector, but
  basis-free — the two fields are assembled into `B ⊗ 𝔤` by `dualPairEquiv.symm`,
  bracketed there by `tensorBracket`, and read back out as components. -/
noncomputable def commutator (A : (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (μ ν : Fin 1 ⊕ Fin 3) : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B :=
  dualPairEquiv (tensorBracket (dualPairEquiv.symm (A μ)) (dualPairEquiv.symm (A ν)))

/-- The gauge transformation of the underived symbol `A_μ^φ`: the special case `s = 0`
  of `gauge_apply_deriv`, with no Leibniz convolution left over — the dual adjoint
  action of the value of `U⁻¹` plus the Maurer–Cartan shift. -/
lemma gauge_apply (hA : IsGaugeField repLorentz repGauge A D D_comm) (U : JetGaugeGroupI)
    (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra) :
    repGauge U (A μ φ) = A μ (adjointDualCoeff U⁻¹ ∅ φ) +
      algebraMap ℂ B (φ (JetGaugeAlgebra.eval (maurerCartanForm U⁻¹ μ))) := by
  simpa [Lorentz.iteratedD, show (∅ : Multiset (Fin 1 ⊕ Fin 3)) = 0 from rfl] using
    hA.gauge_apply_deriv U 0 μ φ

/-!

## Pure-tensor computations for `dualPairEquiv` and `tensorBracket`

-/

@[simp]
lemma dualPairEquiv_tmul (b : B) (a : GaugeAlgebra) (φ : Module.Dual ℝ GaugeAlgebra) :
    dualPairEquiv (b ⊗ₜ[ℝ] a) φ = φ a • b := by
  simp [dualPairEquiv, dualTensorHomEquiv, Module.evalEquiv_apply]

@[simp]
lemma tensorBracket_tmul (b₁ b₂ : B) (a₁ a₂ : GaugeAlgebra) :
    tensorBracket (b₁ ⊗ₜ[ℝ] a₁) (b₂ ⊗ₜ[ℝ] a₂) = (b₁ * b₂) ⊗ₜ[ℝ] ⁅a₁, a₂⁆ := by
  simp [tensorBracket, TensorProduct.tensorTensorTensorComm_tmul]

lemma dualPairEquiv_map_left (Φ : B →ₗ[ℝ] B) (t : B ⊗[ℝ] GaugeAlgebra)
    (φ : Module.Dual ℝ GaugeAlgebra) :
    dualPairEquiv ((TensorProduct.map Φ LinearMap.id) t) φ = Φ (dualPairEquiv t φ) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul b a => simp
  | add x y hx hy => simp [hx, hy]

lemma dualPairEquiv_map_right (T : GaugeAlgebra →ₗ[ℝ] GaugeAlgebra)
    (t : B ⊗[ℝ] GaugeAlgebra) (φ : Module.Dual ℝ GaugeAlgebra) :
    dualPairEquiv ((TensorProduct.map LinearMap.id T) t) φ =
      dualPairEquiv t (T.dualMap φ) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul b a => simp
  | add x y hx hy => simp [hx, hy]

lemma dualPairEquiv_one_tmul (c : GaugeAlgebra) (φ : Module.Dual ℝ GaugeAlgebra) :
    dualPairEquiv ((1 : B) ⊗ₜ[ℝ] c) φ = algebraMap ℂ B (φ c) := by
  rw [dualPairEquiv_tmul, Algebra.algebraMap_eq_smul_one,
    show ((φ c : ℝ) : ℂ) = algebraMap ℝ ℂ (φ c) from rfl, algebraMap_smul]

lemma symm_comp_left (Φ : B →ₗ[ℝ] B) (f : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B) :
    dualPairEquiv.symm (Φ ∘ₗ f) =
      (TensorProduct.map Φ LinearMap.id) (dualPairEquiv.symm f) := by
  apply dualPairEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  refine LinearMap.ext fun φ => ?_
  rw [dualPairEquiv_map_left, LinearEquiv.apply_symm_apply]
  rfl

lemma symm_comp_right (T : GaugeAlgebra →ₗ[ℝ] GaugeAlgebra)
    (f : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B) :
    dualPairEquiv.symm (f ∘ₗ T.dualMap) =
      (TensorProduct.map LinearMap.id T) (dualPairEquiv.symm f) := by
  apply dualPairEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  refine LinearMap.ext fun φ => ?_
  rw [dualPairEquiv_map_right, LinearEquiv.apply_symm_apply]
  rfl

lemma tensorBracket_map_left (Φ : B →ₗ[ℝ] B)
    (hΦ : ∀ b₁ b₂, Φ (b₁ * b₂) = Φ b₁ * Φ b₂) (s t : B ⊗[ℝ] GaugeAlgebra) :
    tensorBracket ((TensorProduct.map Φ LinearMap.id) s)
        ((TensorProduct.map Φ LinearMap.id) t) =
      (TensorProduct.map Φ LinearMap.id) (tensorBracket s t) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul b₁ a₁ =>
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul b₂ a₂ => simp [hΦ]
      | add x y hx hy =>
          simp only [map_add]
          rw [hx, hy]
  | add x y hx hy => simp [hx, hy]

lemma tensorBracket_map_right (T : GaugeAlgebra →ₗ[ℝ] GaugeAlgebra)
    (hT : ∀ a b, T ⁅a, b⁆ = ⁅T a, T b⁆) (s t : B ⊗[ℝ] GaugeAlgebra) :
    tensorBracket ((TensorProduct.map LinearMap.id T) s)
        ((TensorProduct.map LinearMap.id T) t) =
      (TensorProduct.map LinearMap.id T) (tensorBracket s t) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul b₁ a₁ =>
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul b₂ a₂ => simp [hT]
      | add x y hx hy =>
          simp only [map_add]
          rw [hx, hy]
  | add x y hx hy => simp [hx, hy]

lemma tensorBracket_one_right (c : GaugeAlgebra) (s : B ⊗[ℝ] GaugeAlgebra) :
    tensorBracket s ((1 : B) ⊗ₜ[ℝ] c) =
      -(TensorProduct.map LinearMap.id (LieAlgebra.ad ℝ GaugeAlgebra c)) s := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul b a =>
      rw [tensorBracket_tmul, mul_one, ← lie_skew, TensorProduct.tmul_neg]
      simp
  | add x y hx hy =>
      simp only [map_add, LinearMap.add_apply]
      rw [hx, hy]
      abel

lemma tensorBracket_one_left (c : GaugeAlgebra) (t : B ⊗[ℝ] GaugeAlgebra) :
    tensorBracket ((1 : B) ⊗ₜ[ℝ] c) t =
      (TensorProduct.map LinearMap.id (LieAlgebra.ad ℝ GaugeAlgebra c)) t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul b a => simp
  | add x y hx hy => simp [hx, hy]

/-!

## The gauge transformation of the commutator

-/

set_option maxHeartbeats 1000000 in
/-- The gauge transformation law of the commutator term: writing the field law as
  `A_μ ↦ Ad₀ A_μ + c_μ` with `Ad₀` the base-point adjoint of `U₀⁻¹` and
  `c_μ = mc(U⁻¹)_μ|₀` the constant Maurer–Cartan shift, bilinearity of the bracket
  gives

  `⁅A_μ, A_ν⁆ ↦ Ad₀ ⁅A_μ, A_ν⁆ + ⁅Ad₀ A_μ, c_ν⁆ + ⁅c_μ, Ad₀ A_ν⁆ + ⁅c_μ, c_ν⁆`:

  the adjoint-transported commutator, two cross terms linear in the field (the
  bracket against `c` acting on the dual index through `ad`), and the constant
  commutator of the two Maurer–Cartan shifts. Uses that the gauge action is by
  algebra homomorphisms (`gauge_mul`) and that the base-point adjoint transport is a
  morphism of Lie algebras. -/
lemma gauge_commutator (hA : IsGaugeField repLorentz repGauge A D D_comm)
    (U : JetGaugeGroupI) (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra) :
    repGauge U (commutator A μ ν φ) =
      commutator A μ ν (adjointDualCoeff U⁻¹ 0 φ)
      - A μ (adjointDualCoeff U⁻¹ 0 (φ ∘ₗ LieAlgebra.ad ℝ GaugeAlgebra
          (JetGaugeAlgebra.eval (maurerCartanForm U⁻¹ ν))))
      + A ν (adjointDualCoeff U⁻¹ 0 (φ ∘ₗ LieAlgebra.ad ℝ GaugeAlgebra
          (JetGaugeAlgebra.eval (maurerCartanForm U⁻¹ μ))))
      + algebraMap ℂ B (φ ⁅JetGaugeAlgebra.eval (maurerCartanForm U⁻¹ μ),
          JetGaugeAlgebra.eval (maurerCartanForm U⁻¹ ν)⁆) := by
  -- the linear maps and constants of the transformation law
  set Φ : B →ₗ[ℝ] B := (repGauge U).restrictScalars ℝ with hΦdef
  set T₀ : GaugeAlgebra →ₗ[ℝ] GaugeAlgebra :=
    JetGaugeAlgebra.eval.toLinearMap ∘ₗ JetGaugeAlgebra.iteratedDeriv 0 ∘ₗ
      JetGaugeAlgebra.adjointMap U⁻¹ ∘ₗ JetGaugeAlgebra.ofConstant with hT₀def
  set cμ : GaugeAlgebra := JetGaugeAlgebra.eval (maurerCartanForm U⁻¹ μ) with hcμ
  set cν : GaugeAlgebra := JetGaugeAlgebra.eval (maurerCartanForm U⁻¹ ν) with hcν
  set s : B ⊗[ℝ] GaugeAlgebra := dualPairEquiv.symm (A μ) with hs
  set t : B ⊗[ℝ] GaugeAlgebra := dualPairEquiv.symm (A ν) with ht
  have hcoeff : adjointDualCoeff U⁻¹ 0 = T₀.dualMap := by rw [hT₀def]; rfl
  -- the base-point adjoint transport is a Lie algebra morphism
  have hT₀lie : ∀ a b : GaugeAlgebra, T₀ ⁅a, b⁆ = ⁅T₀ a, T₀ b⁆ := by
    intro a b
    simp [hT₀def, JetGaugeAlgebra.ofConstant_lie, JetGaugeAlgebra.adjointMap_lie,
      LieHom.map_lie]
  -- the transformed component families in tensor form
  have hfam : ∀ (ρ : Fin 1 ⊕ Fin 3),
      Φ ∘ₗ A ρ = A ρ ∘ₗ T₀.dualMap +
        dualPairEquiv ((1 : B) ⊗ₜ[ℝ] JetGaugeAlgebra.eval (maurerCartanForm U⁻¹ ρ)) := by
    intro ρ
    refine LinearMap.ext fun ψ => ?_
    simp only [LinearMap.comp_apply, LinearMap.add_apply, hΦdef,
      LinearMap.restrictScalars_apply]
    rw [hA.gauge_apply U ρ ψ, dualPairEquiv_one_tmul, ← hcoeff]
    rfl
  have hsμ : (TensorProduct.map Φ LinearMap.id) s =
      (TensorProduct.map LinearMap.id T₀) s + (1 : B) ⊗ₜ[ℝ] cμ := by
    rw [hs, ← symm_comp_left, hfam μ, map_add, symm_comp_right,
      LinearEquiv.symm_apply_apply, hcμ]
  have htν : (TensorProduct.map Φ LinearMap.id) t =
      (TensorProduct.map LinearMap.id T₀) t + (1 : B) ⊗ₜ[ℝ] cν := by
    rw [ht, ← symm_comp_left, hfam ν, map_add, symm_comp_right,
      LinearEquiv.symm_apply_apply, hcν]
  -- record the pairing identities, then make the local definitions opaque
  have hcomm_pair : dualPairEquiv (tensorBracket s t) = commutator A μ ν := by
    rw [hs, ht]; rfl
  have hπs : dualPairEquiv s = A μ := by
    rw [hs]; exact dualPairEquiv.apply_symm_apply _
  have hπt : dualPairEquiv t = A ν := by
    rw [ht]; exact dualPairEquiv.apply_symm_apply _
  have hΦmul : ∀ b₁ b₂ : B, Φ (b₁ * b₂) = Φ b₁ * Φ b₂ := fun b₁ b₂ =>
    hA.gauge_mul U b₁ b₂
  clear_value Φ T₀ cμ cν s t
  -- the tensor-level transformation of the bracket
  have htensor : (TensorProduct.map Φ LinearMap.id) (tensorBracket s t) =
      (TensorProduct.map LinearMap.id T₀) (tensorBracket s t)
      - (TensorProduct.map LinearMap.id (LieAlgebra.ad ℝ GaugeAlgebra cν))
          ((TensorProduct.map LinearMap.id T₀) s)
      + (TensorProduct.map LinearMap.id (LieAlgebra.ad ℝ GaugeAlgebra cμ))
          ((TensorProduct.map LinearMap.id T₀) t)
      + (1 : B) ⊗ₜ[ℝ] ⁅cμ, cν⁆ := by
    refine (tensorBracket_map_left Φ hΦmul s t).symm.trans
      ((congrArg₂ (fun X Y => tensorBracket X Y) hsμ htν).trans ?_)
    simp only [map_add, LinearMap.add_apply]
    rw [tensorBracket_map_right T₀ hT₀lie, tensorBracket_one_right,
      tensorBracket_one_left, tensorBracket_tmul, one_mul]
    abel
  -- read the tensor identity back through the pairing
  have hread := congrArg (fun z => dualPairEquiv z φ) htensor
  simp only [map_add, map_sub, map_neg, LinearMap.add_apply, LinearMap.sub_apply,
    dualPairEquiv_map_left, dualPairEquiv_map_right,
    dualPairEquiv_one_tmul] at hread
  rw [show repGauge U (commutator A μ ν φ) = Φ (dualPairEquiv (tensorBracket s t) φ) from by
      rw [← hcomm_pair, hΦdef]; rfl,
    hread, hcoeff, hcomm_pair, hπs, hπt]
  rfl

end IsGaugeField

end StandardModel
