/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeBosons.AlgebraValued.Basic
public import Physlib.Particles.StandardModel.GaugeBosons.AlgebraValued.TransformsInAdjoint
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.Free
/-!

# Gauge tensors in a general representation

The adjoint story of `TransformsInAdjoint` generalizes to an arbitrary representation
of the jet gauge group: a matter field valued in a representation space `V` has
symbols `[∂_s ψ^i]` contracted against duals of `V`, and its transformation law is
the Leibniz convolution of the base-point Taylor coefficients of the representation.

Since the gauge transformations are jets, the representation must act on `V`-valued
jets `JetRing ⊗[ℂ] V` — the value of `rep U` at a constant vector is spacetime
dependent, and the derivative symbols see its Taylor coefficients. This file provides
the toolkit for `V`-valued jets:

* `jetOfConstant` — the inclusion of constants, `v ↦ 1 ⊗ v`;
* `jetDeriv`/`jetIteratedDeriv` — the formal derivative, acting on the jet factor;
* `jetEval` — evaluation at the base point, `f ⊗ v ↦ (constant coefficient of f) • v`;

and with them

* `repDualCoeff rep U x` — the physicists' `∂_x (rep U)^i_j|₀` transposed to the dual
  of `V`, the analogue of `adjointDualCoeff` for a general representation;
* `TransformsIn` — the generalization of `TransformsInAdjoint`: the derivative
  symbols of the family transform by the Leibniz convolution of `repDualCoeff`, with
  no inhomogeneous term.

## The covariant derivative

The covariant derivative `∇_ρ F = D_ρ F + (A_ρ acting on the value index)` requires
the *infinitesimal* action of the gauge algebra on the value space — physicists'
`i dρ(T^a)` — which cannot be extracted from the abstract group representation `rep`
(there is no differentiable structure to differentiate it). It is therefore taken as
data: an `ℝ`-bilinear action `act : GaugeAlgebra →ₗ[ℝ] W →ₗ[ℝ] W`. The layer is
built for an arbitrary finite-dimensional real value space `W`, so that the adjoint
case `act = adAction` (the bracket as a bilinear map) literally specializes:
`covDerivAction A adAction F D ρ = covDerivAdjoint A F D ρ` holds definitionally
(`covDerivAction_adAction`).

The compatibility between `rep` and `act` — the structure `IsInfinitesimalActionOf` —
and the theorem that under it the covariant derivative preserves the gauge tensors live
in `Physlib.Particles.StandardModel.Matter.JetComponentSpace.InfinitesimalAction`.

-/

@[expose] public section

namespace StandardModel
open Matrix MatrixGroups TensorProduct MvPowerSeries
variable {B : Type} [Ring B] [Algebra ℂ B]
variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-!

## `V`-valued jets

-/

/-- The constant-coefficient evaluation of a jet, as a `ℂ`-linear map. -/
noncomputable def _root_.JetRing.constantCoeffₗ : JetRing →ₗ[ℂ] ℂ where
  toFun := constantCoeff
  map_add' f g := by simp
  map_smul' c f := by simp [smul_eq_C_mul]

@[simp]
lemma _root_.JetRing.constantCoeffₗ_apply (f : JetRing) :
    JetRing.constantCoeffₗ f = constantCoeff f := rfl

/-- The inclusion of constants into `V`-valued jets: `v ↦ 1 ⊗ v`. -/
noncomputable def jetOfConstant : V →ₗ[ℂ] JetRing ⊗[ℂ] V :=
  TensorProduct.mk ℂ JetRing V 1

@[simp]
lemma jetOfConstant_apply (v : V) : jetOfConstant v = (1 : JetRing) ⊗ₜ[ℂ] v := rfl

/-- The formal derivative on `V`-valued jets in the direction `μ`, acting on the jet
  factor. -/
noncomputable def jetDeriv (μ : Fin 1 ⊕ Fin 3) :
    JetRing ⊗[ℂ] V →ₗ[ℂ] JetRing ⊗[ℂ] V :=
  LinearMap.rTensor V (pderiv ℂ μ).toLinearMap

@[simp]
lemma jetDeriv_tmul (μ : Fin 1 ⊕ Fin 3) (f : JetRing) (v : V) :
    jetDeriv μ (f ⊗ₜ[ℂ] v) = pderiv ℂ μ f ⊗ₜ[ℂ] v := rfl

/-- Formal derivatives on `V`-valued jets commute, since the partial derivatives of
  jets do. -/
lemma jetDeriv_comm (μ ν : Fin 1 ⊕ Fin 3) :
    (jetDeriv (V := V) μ).comp (jetDeriv ν) = (jetDeriv ν).comp (jetDeriv μ) := by
  rw [jetDeriv, jetDeriv, ← LinearMap.rTensor_comp, ← LinearMap.rTensor_comp]
  exact congrArg (LinearMap.rTensor V)
    (LinearMap.ext fun f => JetRing.pderiv_comm μ ν f)

/-- Post-composition with `jetDeriv` is right-commutative, which is what allows
  iterated derivatives to be indexed by a `Multiset` of directions. -/
instance : RightCommutative (fun (L : JetRing ⊗[ℂ] V →ₗ[ℂ] JetRing ⊗[ℂ] V)
    (μ : Fin 1 ⊕ Fin 3) => L.comp (jetDeriv μ)) where
  right_comm L μ ν := by
    refine LinearMap.ext fun x => ?_
    have h := LinearMap.congr_fun (jetDeriv_comm μ ν) x
    simp only [LinearMap.coe_comp, Function.comp_apply] at h ⊢
    exact congrArg L h

/-- The iterated formal derivative on `V`-valued jets, in the (unordered) directions
  given by the multiset `μs`. -/
noncomputable def jetIteratedDeriv (μs : Multiset (Fin 1 ⊕ Fin 3)) :
    JetRing ⊗[ℂ] V →ₗ[ℂ] JetRing ⊗[ℂ] V :=
  μs.foldl (fun L μ => L.comp (jetDeriv μ)) LinearMap.id

@[simp]
lemma jetIteratedDeriv_zero :
    jetIteratedDeriv (V := V) (0 : Multiset (Fin 1 ⊕ Fin 3)) = LinearMap.id := by
  simp [jetIteratedDeriv]

lemma jetIteratedDeriv_cons (μ : Fin 1 ⊕ Fin 3) (μs : Multiset (Fin 1 ⊕ Fin 3)) :
    jetIteratedDeriv (V := V) (μ ::ₘ μs) = (jetDeriv μ).comp (jetIteratedDeriv μs) := by
  have h : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (L : JetRing ⊗[ℂ] V →ₗ[ℂ] JetRing ⊗[ℂ] V),
      s.foldl (fun L μ => L.comp (jetDeriv μ)) L = L.comp (jetIteratedDeriv s) := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro L; simp [jetIteratedDeriv]
    | cons κ t ih =>
        intro L
        rw [jetIteratedDeriv, Multiset.foldl_cons, Multiset.foldl_cons, ih, ih]
        simp [LinearMap.comp_assoc]
  rw [jetIteratedDeriv, Multiset.foldl_cons, h]
  simp

/-- The iterated derivative is additive in the multiset of directions. -/
lemma jetIteratedDeriv_add (s t : Multiset (Fin 1 ⊕ Fin 3)) :
    jetIteratedDeriv (V := V) (s + t) =
      (jetIteratedDeriv s).comp (jetIteratedDeriv t) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons μ s ih =>
      rw [Multiset.cons_add, jetIteratedDeriv_cons, jetIteratedDeriv_cons, ih,
        LinearMap.comp_assoc]

@[simp]
lemma jetIteratedDeriv_singleton (μ : Fin 1 ⊕ Fin 3) :
    jetIteratedDeriv (V := V) ({μ} : Multiset (Fin 1 ⊕ Fin 3)) = jetDeriv μ := by
  rw [show ({μ} : Multiset (Fin 1 ⊕ Fin 3)) = μ ::ₘ 0 from rfl, jetIteratedDeriv_cons,
    jetIteratedDeriv_zero, LinearMap.comp_id]

/-- Evaluation of a `V`-valued jet at the base point:
  `f ⊗ v ↦ (constant coefficient of f) • v`. This is a retraction of
  `jetOfConstant`. -/
noncomputable def jetEval : JetRing ⊗[ℂ] V →ₗ[ℂ] V :=
  TensorProduct.lift ((LinearMap.lsmul ℂ V).comp JetRing.constantCoeffₗ)

@[simp]
lemma jetEval_tmul (f : JetRing) (v : V) :
    jetEval (f ⊗ₜ[ℂ] v) = constantCoeff f • v := rfl

@[simp]
lemma jetEval_jetOfConstant (v : V) : jetEval (jetOfConstant v) = v := by
  simp

namespace IsGaugeField

variable {repLorentz : Representation ℂ SL(2,ℂ) B}
variable {repGauge : Representation ℂ JetGaugeGroupI B}
variable {repLorentz : Representation ℂ SL(2,ℂ) B}
variable {repGauge : Representation ℂ JetGaugeGroupI B}
variable {A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B}

/-!

## The dual representation coefficients and gauge tensors in a representation

-/

/-- The base-point adjoint transport at `x` derivatives, un-dualized: the map on the
  gauge algebra whose transpose is `adjointDualCoeff`. -/
noncomputable def adjointCoeff (U : JetGaugeGroupI) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    GaugeAlgebra →ₗ[ℝ] GaugeAlgebra :=
  JetGaugeAlgebra.eval.toLinearMap ∘ₗ JetGaugeAlgebra.iteratedDeriv x ∘ₗ
    JetGaugeAlgebra.adjointMap U ∘ₗ JetGaugeAlgebra.ofConstant

lemma adjointDualCoeff_eq_dualMap (U : JetGaugeGroupI) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    adjointDualCoeff U x = (adjointCoeff U x).dualMap := rfl

/-- The physicists' `∂_x (rep U)^i_j|₀`, un-dualized: include the constant vector
  into `V`-valued jets, act by `rep U`, differentiate `x` times, evaluate at the base
  point — the base-point Taylor coefficient of the representation, as a real-linear
  map on the value space. -/
noncomputable def repCoeff (rep : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V))
    (U : JetGaugeGroupI) (x : Multiset (Fin 1 ⊕ Fin 3)) : V →ₗ[ℝ] V :=
  (jetEval ∘ₗ jetIteratedDeriv x ∘ₗ rep U ∘ₗ jetOfConstant).restrictScalars ℝ

/-- The physicists' `∂_x (rep U)^i_j|₀` acting on the dual index of a matter-field
  symbol: the transpose of `repCoeff`. This is the analogue of `adjointDualCoeff`
  for a general representation of the jet gauge group; for `x = 0` it is the dual
  (contragredient) action of the value of `U`, and for `x ≠ 0` it sees the
  derivatives of the gauge transformation. -/
noncomputable def repDualCoeff (rep : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V))
    (U : JetGaugeGroupI) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℝ V →ₗ[ℝ] Module.Dual ℝ V :=
  (repCoeff rep U x).dualMap

/-- A component family `F`, with values in `B` and index in the dual of the
  representation space `V`, *transforms in* the representation `rep` of the jet gauge
  group when each derivative symbol `[∂_s F^φ]` transforms by the Leibniz convolution
  of the dual representation coefficients against lower derivative symbols, with no
  inhomogeneous term — the generalization of `TransformsInAdjoint` from the adjoint
  representation to an arbitrary one. -/
def TransformsIn (rep : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V))
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ V →ₗ[ℝ] B) : Prop :=
  ∀ (U : JetGaugeGroupI) (φ : Module.Dual ℝ V) (s : Multiset (Fin 1 ⊕ Fin 3)),
    repGauge U (F s φ) = (s.antidiagonal.map fun p => (F p.2  (repDualCoeff rep U⁻¹ p.1 φ))).sum

/-!

## The covariant derivative through an infinitesimal action

-/

section Action

variable {W : Type} [AddCommGroup W] [Module ℝ W]

/-- The action of an adjoint-valued field on a `W`-valued field at the tensor level:
  multiplication in `B` on the first factors, the infinitesimal action `act` of the
  gauge algebra on `W` on the second, so that on pure tensors
  `(b₁ ⊗ c) · (b₂ ⊗ w) = (b₁ b₂) ⊗ act c w`. For `W` the gauge algebra and `act` the
  adjoint action this is `tensorBracket` (`tensorAction_ad`). -/
noncomputable def tensorAction (act : GaugeAlgebra →ₗ[ℝ] W →ₗ[ℝ] W) :
    (B ⊗[ℝ] GaugeAlgebra) →ₗ[ℝ] (B ⊗[ℝ] W) →ₗ[ℝ] B ⊗[ℝ] W :=
  TensorProduct.curry
    ((TensorProduct.map (TensorProduct.lift (LinearMap.mul ℝ B))
        (TensorProduct.lift act)) ∘ₗ
      (TensorProduct.tensorTensorTensorComm ℝ B GaugeAlgebra B W).toLinearMap)

@[simp]
lemma tensorAction_tmul (act : GaugeAlgebra →ₗ[ℝ] W →ₗ[ℝ] W) (b₁ b₂ : B)
    (c : GaugeAlgebra) (w : W) :
    tensorAction act (b₁ ⊗ₜ[ℝ] c) (b₂ ⊗ₜ[ℝ] w) = (b₁ * b₂) ⊗ₜ[ℝ] act c w := by
  simp [tensorAction, TensorProduct.tensorTensorTensorComm_tmul]

/-- The gauge-algebra bracket as a bilinear map — the infinitesimal adjoint
  action. -/
noncomputable def adAction : GaugeAlgebra →ₗ[ℝ] GaugeAlgebra →ₗ[ℝ] GaugeAlgebra :=
  LinearMap.mk₂ ℝ (fun a b => ⁅a, b⁆) (fun a a' b => add_lie a a' b)
    (fun t a b => smul_lie t a b) (fun a b b' => lie_add a b b')
    (fun t a b => lie_smul t a b)

@[simp]
lemma adAction_apply (a b : GaugeAlgebra) : adAction a b = ⁅a, b⁆ := rfl

/-- On the gauge algebra, the tensor action through the adjoint is the tensor
  bracket. -/
lemma tensorAction_adAction : tensorAction (B := B) adAction = tensorBracket := rfl

lemma tensorAction_map_left (act : GaugeAlgebra →ₗ[ℝ] W →ₗ[ℝ] W) (Φ : B →ₗ[ℝ] B)
    (hΦ : ∀ b₁ b₂, Φ (b₁ * b₂) = Φ b₁ * Φ b₂) (s : B ⊗[ℝ] GaugeAlgebra)
    (t : B ⊗[ℝ] W) :
    tensorAction act ((TensorProduct.map Φ LinearMap.id) s)
        ((TensorProduct.map Φ LinearMap.id) t) =
      (TensorProduct.map Φ LinearMap.id) (tensorAction act s t) := by
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

lemma tensorAction_one_left (act : GaugeAlgebra →ₗ[ℝ] W →ₗ[ℝ] W) (c : GaugeAlgebra)
    (t : B ⊗[ℝ] W) :
    tensorAction act ((1 : B) ⊗ₜ[ℝ] c) t =
      (TensorProduct.map LinearMap.id (act c)) t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul b a => simp
  | add x y hx hy => simp [hx, hy]

/-- `tensorAction` is a derivation in the algebra factor: for `Δ` satisfying the
  Leibniz rule on `B`, applying `Δ ⊗ id` distributes over the two arguments. -/
lemma tensorAction_map_left_derivation (act : GaugeAlgebra →ₗ[ℝ] W →ₗ[ℝ] W)
    (Δ : B →ₗ[ℝ] B) (hΔ : ∀ b₁ b₂, Δ (b₁ * b₂) = Δ b₁ * b₂ + b₁ * Δ b₂)
    (s : B ⊗[ℝ] GaugeAlgebra) (t : B ⊗[ℝ] W) :
    (TensorProduct.map Δ LinearMap.id) (tensorAction act s t) =
      tensorAction act ((TensorProduct.map Δ LinearMap.id) s) t +
      tensorAction act s ((TensorProduct.map Δ LinearMap.id) t) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul b₁ a₁ =>
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul b₂ a₂ => simp [hΔ, TensorProduct.add_tmul]
      | add x y hx hy =>
          simp only [map_add, hx, hy]
          abel
  | add x y hx hy =>
      simp only [map_add, LinearMap.add_apply, hx, hy]
      abel

/-- `tensorAction` under an antidiagonal pair of transport families: if the
  `W`-transports intertwine `act` with the `GaugeAlgebra`-transports as an
  antidiagonal convolution, so do `id ⊗ ·` over `tensorAction`. -/
lemma tensorAction_map_right_antidiagonal (act : GaugeAlgebra →ₗ[ℝ] W →ₗ[ℝ] W)
    (Tg : Multiset (Fin 1 ⊕ Fin 3) → GaugeAlgebra →ₗ[ℝ] GaugeAlgebra)
    (Tv : Multiset (Fin 1 ⊕ Fin 3) → W →ₗ[ℝ] W) (x : Multiset (Fin 1 ⊕ Fin 3))
    (hT : ∀ (c : GaugeAlgebra) (w : W), Tv x (act c w) =
      (x.antidiagonal.map fun p => act (Tg p.1 c) (Tv p.2 w)).sum)
    (s : B ⊗[ℝ] GaugeAlgebra) (t : B ⊗[ℝ] W) :
    (x.antidiagonal.map fun p =>
      tensorAction act ((TensorProduct.map LinearMap.id (Tg p.1)) s)
        ((TensorProduct.map LinearMap.id (Tv p.2)) t)).sum =
      (TensorProduct.map LinearMap.id (Tv x)) (tensorAction act s t) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul b₁ a₁ =>
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul b₂ a₂ =>
          simp only [tensorAction_tmul, TensorProduct.map_tmul, LinearMap.id_coe, id_eq]
          rw [hT, Multiset.tmul_sum, Multiset.map_map]
          exact congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => by
            simp)
      | add y z hy hz =>
          rw [Multiset.map_congr rfl (fun p hp => by rw [map_add, map_add]),
            Multiset.sum_map_add, hy, hz, ← map_add, ← map_add]
  | add y z hy hz =>
      rw [Multiset.map_congr rfl (fun p hp => by
          rw [map_add, map_add, LinearMap.add_apply]),
        Multiset.sum_map_add, hy, hz, ← map_add, ← LinearMap.add_apply, ← map_add]

variable [FiniteDimensional ℝ W]

/-- The canonical equivalence between `W`-valued fields `B ⊗ W` and their component
  families `φ ↦ F^φ` — `dualPairEquiv` for a general finite-dimensional value
  space. -/
noncomputable def dualPairEquivW : (B ⊗[ℝ] W) ≃ₗ[ℝ] (Module.Dual ℝ W →ₗ[ℝ] B) :=
  TensorProduct.comm ℝ B W ≪≫ₗ
    TensorProduct.congr (Module.evalEquiv ℝ W) (LinearEquiv.refl ℝ B) ≪≫ₗ
    dualTensorHomEquiv ℝ (Module.Dual ℝ W) B

@[simp]
lemma dualPairEquivW_tmul (b : B) (w : W) (φ : Module.Dual ℝ W) :
    dualPairEquivW (b ⊗ₜ[ℝ] w) φ = φ w • b := by
  simp [dualPairEquivW, dualTensorHomEquiv, Module.evalEquiv_apply]

/-- On the gauge algebra, `dualPairEquivW` is `dualPairEquiv`. -/
lemma dualPairEquivW_gaugeAlgebra :
    (dualPairEquivW : (B ⊗[ℝ] GaugeAlgebra) ≃ₗ[ℝ] _) = dualPairEquiv := rfl

lemma dualPairEquivW_map_left (Φ : B →ₗ[ℝ] B) (t : B ⊗[ℝ] W)
    (φ : Module.Dual ℝ W) :
    dualPairEquivW ((TensorProduct.map Φ LinearMap.id) t) φ =
      Φ (dualPairEquivW t φ) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul b w => simp
  | add x y hx hy => simp [hx, hy]

lemma dualPairEquivW_map_right (T : W →ₗ[ℝ] W) (t : B ⊗[ℝ] W)
    (φ : Module.Dual ℝ W) :
    dualPairEquivW ((TensorProduct.map LinearMap.id T) t) φ =
      dualPairEquivW t (T.dualMap φ) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul b w => simp
  | add x y hx hy => simp [hx, hy]

lemma symm_comp_left_W (Φ : B →ₗ[ℝ] B) (g : Module.Dual ℝ W →ₗ[ℝ] B) :
    dualPairEquivW.symm (Φ ∘ₗ g) =
      (TensorProduct.map Φ LinearMap.id) (dualPairEquivW.symm g) := by
  apply dualPairEquivW.injective
  rw [LinearEquiv.apply_symm_apply]
  refine LinearMap.ext fun φ => ?_
  rw [dualPairEquivW_map_left, LinearEquiv.apply_symm_apply]
  rfl

lemma symm_comp_right_W (T : W →ₗ[ℝ] W) (g : Module.Dual ℝ W →ₗ[ℝ] B) :
    dualPairEquivW.symm (g ∘ₗ T.dualMap) =
      (TensorProduct.map LinearMap.id T) (dualPairEquivW.symm g) := by
  apply dualPairEquivW.injective
  rw [LinearEquiv.apply_symm_apply]
  refine LinearMap.ext fun φ => ?_
  rw [dualPairEquivW_map_right, LinearEquiv.apply_symm_apply]
  rfl

/-- The action of an adjoint-indexed component family on a `W`-indexed one, through
  the infinitesimal action `act`: assemble both into fields, act by `tensorAction`,
  read back out as components. This is the physicists' `f^a (T_a)^i_j g^j` with
  `T = act`, basis-free; for the adjoint action it is `bracketFam`
  (`actionFam_ad`). -/
noncomputable def actionFam (act : GaugeAlgebra →ₗ[ℝ] W →ₗ[ℝ] W)
    (f : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B) (g : Module.Dual ℝ W →ₗ[ℝ] B) :
    Module.Dual ℝ W →ₗ[ℝ] B :=
  dualPairEquivW (tensorAction act (dualPairEquiv.symm f) (dualPairEquivW.symm g))

/-- On the gauge algebra, the action family through the adjoint is the bracket
  family. -/
lemma actionFam_adAction (f g : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B) :
    actionFam adAction f g = bracketFam f g := rfl

variable {act : GaugeAlgebra →ₗ[ℝ] W →ₗ[ℝ] W}

lemma actionFam_add_left (f₁ f₂ : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (g : Module.Dual ℝ W →ₗ[ℝ] B) :
    actionFam act (f₁ + f₂) g = actionFam act f₁ g + actionFam act f₂ g := by
  simp only [actionFam, map_add, LinearMap.add_apply]

lemma actionFam_add_right (f : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (g₁ g₂ : Module.Dual ℝ W →ₗ[ℝ] B) :
    actionFam act f (g₁ + g₂) = actionFam act f g₁ + actionFam act f g₂ := by
  simp only [actionFam, map_add]

lemma actionFam_zero_left (g : Module.Dual ℝ W →ₗ[ℝ] B) :
    actionFam act 0 g = 0 := by
  simp [actionFam]

lemma actionFam_zero_right (f : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B) :
    actionFam act f 0 = 0 := by
  simp [actionFam]

lemma actionFam_sum_left (S : Multiset (Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B))
    (g : Module.Dual ℝ W →ₗ[ℝ] B) :
    actionFam act S.sum g = (S.map fun f => actionFam act f g).sum := by
  induction S using Multiset.induction_on with
  | empty => simp [actionFam_zero_left]
  | cons f S ih => simp [actionFam_add_left, ih]

lemma actionFam_sum_right (f : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (S : Multiset (Module.Dual ℝ W →ₗ[ℝ] B)) :
    actionFam act f S.sum = (S.map fun g => actionFam act f g).sum := by
  induction S using Multiset.induction_on with
  | empty => simp [actionFam_zero_right]
  | cons g S ih => simp [actionFam_add_right, ih]

/-- **The derived action family** `A_ρ · F`: the `s`-derivative of the action of the
  gauge field on a matter family, given by the Leibniz convolution of the derivative
  symbols over the multiset antidiagonal — the matter analogue of `bracketFamConv`.
  With the derivative symbols as primitives this convolution is the definition of the
  derived action. -/
noncomputable def actionFamConv
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (act : GaugeAlgebra →ₗ[ℝ] W →ₗ[ℝ] W) (ρ : Fin 1 ⊕ Fin 3)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ W →ₗ[ℝ] B)
    (s : Multiset (Fin 1 ⊕ Fin 3)) : Module.Dual ℝ W →ₗ[ℝ] B :=
  (s.antidiagonal.map fun p => actionFam act (A p.1 ρ) (F p.2)).sum

/-- On the gauge algebra, the derived action family through the adjoint is the
  derived bracket family. -/
lemma actionFamConv_adAction
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (ρ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    actionFamConv A adAction ρ F s = bracketFamConv A ρ F s := rfl

set_option maxHeartbeats 1000000 in
/-- The gauge transformation of the action of an affinely-transforming
  adjoint-indexed family on a linearly-transforming `W`-indexed family: the action of
  the transformed families plus one `ad`-type cross term through `act`. This is
  `repGauge_bracketFam` with a homogeneous second slot and the bracket replaced by
  a general action. -/
lemma repGauge_actionFam (hA : IsGaugeField repLorentz repGauge A)
    (U : JetGaugeGroupI) {f f' : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B}
    {g g' : Module.Dual ℝ W →ₗ[ℝ] B} {cf : GaugeAlgebra}
    (hf : ∀ ψ : Module.Dual ℝ GaugeAlgebra,
      repGauge U (f ψ) = f' ψ + algebraMap ℂ B (ψ cf))
    (hg : ∀ ψ : Module.Dual ℝ W, repGauge U (g ψ) = g' ψ)
    (φ : Module.Dual ℝ W) :
    repGauge U (actionFam act f g φ) =
      actionFam act f' g' φ + g' (φ ∘ₗ act cf) := by
  set Φ : B →ₗ[ℝ] B := (repGauge U).restrictScalars ℝ with hΦdef
  have hΦmul : ∀ b₁ b₂ : B, Φ (b₁ * b₂) = Φ b₁ * Φ b₂ := fun b₁ b₂ =>
    hA.gauge_mul U b₁ b₂
  set s : B ⊗[ℝ] GaugeAlgebra := dualPairEquiv.symm f with hs
  set t : B ⊗[ℝ] W := dualPairEquivW.symm g with ht
  set s' : B ⊗[ℝ] GaugeAlgebra := dualPairEquiv.symm f' with hs'
  set t' : B ⊗[ℝ] W := dualPairEquivW.symm g' with ht'
  have hfm : (TensorProduct.map Φ LinearMap.id) s = s' + (1 : B) ⊗ₜ[ℝ] cf := by
    rw [hs, hs', ← symm_comp_left,
      show Φ ∘ₗ f = f' + dualPairEquiv ((1 : B) ⊗ₜ[ℝ] cf) from
        LinearMap.ext fun ψ => by
          simp only [LinearMap.comp_apply, LinearMap.add_apply, hΦdef,
            LinearMap.restrictScalars_apply]
          rw [hf ψ, dualPairEquiv_one_tmul],
      map_add, LinearEquiv.symm_apply_apply]
  have hgm : (TensorProduct.map Φ LinearMap.id) t = t' := by
    rw [ht, ht', ← symm_comp_left_W,
      show Φ ∘ₗ g = g' from LinearMap.ext fun ψ => by
        simp only [LinearMap.comp_apply, hΦdef, LinearMap.restrictScalars_apply]
        rw [hg ψ]]
  have hact : dualPairEquivW (tensorAction act s t) = actionFam act f g := by
    rw [hs, ht]; rfl
  have hact' : dualPairEquivW (tensorAction act s' t') = actionFam act f' g' := by
    rw [hs', ht']; rfl
  have hπt' : dualPairEquivW t' = g' := by
    rw [ht']; exact dualPairEquivW.apply_symm_apply _
  clear_value Φ s t s' t'
  have htensor : (TensorProduct.map Φ LinearMap.id) (tensorAction act s t) =
      tensorAction act s' t'
      + (TensorProduct.map LinearMap.id (act cf)) t' := by
    refine (tensorAction_map_left act Φ hΦmul s t).symm.trans
      ((congrArg₂ (fun X Y => tensorAction act X Y) hfm hgm).trans ?_)
    rw [map_add, LinearMap.add_apply, tensorAction_one_left]
  have hread := congrArg (fun z => dualPairEquivW z φ) htensor
  simp only [map_add, LinearMap.add_apply, dualPairEquivW_map_left,
    dualPairEquivW_map_right] at hread
  rw [show repGauge U (actionFam act f g φ) =
      Φ (dualPairEquivW (tensorAction act s t) φ) from by
      rw [hact, hΦdef]; rfl,
    hread, hact', hπt']
  rfl

/-- The covariant derivative of a `W`-indexed family of derivative symbols through
  the infinitesimal action `act` of the gauge algebra on `W`:

  `∇_ρ F = [∂_ρ F] + A_ρ · F`,

  the extra derivative on the symbol plus the derived action of the gauge field on
  the value index. With the physicists' factor of `i` absorbed into `act` (as it is
  in the gauge-algebra bracket), this is `∂_ρ F + i A_ρ^a T_a F` in the `D = ∂ + i A`
  convention. For the adjoint action it is `covDerivAdjoint`
  (`covDerivAction_adAction`). -/
noncomputable def covDerivAction
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (act : GaugeAlgebra →ₗ[ℝ] W →ₗ[ℝ] W)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ W →ₗ[ℝ] B)
    (ρ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) : Module.Dual ℝ W →ₗ[ℝ] B :=
  F (ρ ::ₘ s) + actionFamConv A act ρ F s

@[simp]
lemma covDerivAction_apply
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (act : GaugeAlgebra →ₗ[ℝ] W →ₗ[ℝ] W)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ W →ₗ[ℝ] B)
    (ρ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ W) :
    covDerivAction A act F ρ s φ = F (ρ ::ₘ s) φ + actionFamConv A act ρ F s φ := rfl

/-- Through the adjoint action, the general covariant derivative is the adjoint
  one. -/
lemma covDerivAction_adAction
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (ρ : Fin 1 ⊕ Fin 3) :
    covDerivAction A adAction F ρ = covDerivAdjoint A F ρ := rfl

/-!

## The span lemma

Replacing derivatives of a matter family by covariant derivatives does not change
the generated algebra of symbols: the correction terms are products of gauge-field
components with matter components. Note the statement is about generated
*subalgebras*, not linear spans — `∇_ρ F − ∂_ρ F` is a sum of products `A · F`,
which lies in the algebra generated by the symbols but not in their linear span.

-/

/-- Decomposition of an assembled family along a basis of the value space: the
  components against the dual basis, tensored with the basis vectors. -/
lemma dualPairEquivW_symm_eq_sum {ι : Type*} [Fintype ι] (bW : Module.Basis ι ℝ W)
    (g : Module.Dual ℝ W →ₗ[ℝ] B) :
    dualPairEquivW.symm g = ∑ i, g (bW.coord i) ⊗ₜ[ℝ] bW i := by
  apply dualPairEquivW.injective
  rw [LinearEquiv.apply_symm_apply]
  refine LinearMap.ext fun φ => ?_
  symm
  rw [map_sum, LinearMap.sum_apply]
  simp only [dualPairEquivW_tmul]
  have hdual : (∑ i, φ (bW i) • bW.coord i) = φ := by
    refine bW.ext fun j => ?_
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
      smul_eq_mul]
    rw [Finset.sum_eq_single j
      (fun i _ hij => by simp [Ne.symm hij])
      (fun h => absurd (Finset.mem_univ j) h)]
    simp
  calc ∑ i, φ (bW i) • g (bW.coord i)
      = g (∑ i, φ (bW i) • bW.coord i) := by rw [map_sum]; simp
    _ = g φ := by rw [hdual]

/-- The value of an action of families lies in any subalgebra containing the values
  of both families: the action is a finite sum of products of components. -/
lemma actionFam_apply_mem {act : GaugeAlgebra →ₗ[ℝ] W →ₗ[ℝ] W} {P : Subalgebra ℂ B}
    {f : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B} {g : Module.Dual ℝ W →ₗ[ℝ] B}
    (hf : ∀ ψ, f ψ ∈ P) (hg : ∀ χ, g χ ∈ P) (φ : Module.Dual ℝ W) :
    actionFam act f g φ ∈ P := by
  rw [actionFam,
    show dualPairEquiv.symm f = ∑ i,
        f ((Module.finBasis ℝ GaugeAlgebra).coord i) ⊗ₜ[ℝ]
          (Module.finBasis ℝ GaugeAlgebra) i from by
      rw [← dualPairEquivW_gaugeAlgebra]
      exact dualPairEquivW_symm_eq_sum (Module.finBasis ℝ GaugeAlgebra) f,
    dualPairEquivW_symm_eq_sum (Module.finBasis ℝ W) g]
  simp only [map_sum, LinearMap.sum_apply, tensorAction_tmul, dualPairEquivW_tmul]
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  rw [← algebraMap_smul ℂ]
  exact P.smul_mem (mul_mem (hf _) (hg _)) _

/-- Iterated covariant derivatives along a list of directions, as a family of
  derivative symbols. -/
noncomputable def covDerivIter
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (act : GaugeAlgebra →ₗ[ℝ] W →ₗ[ℝ] W)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ W →ₗ[ℝ] B)
    (l : List (Fin 1 ⊕ Fin 3)) :
    Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ W →ₗ[ℝ] B :=
  l.foldr (fun ρ G => covDerivAction A act G ρ) F

@[simp]
lemma covDerivIter_nil (act : GaugeAlgebra →ₗ[ℝ] W →ₗ[ℝ] W)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ W →ₗ[ℝ] B) :
    covDerivIter A act F [] = F := rfl

@[simp]
lemma covDerivIter_cons (act : GaugeAlgebra →ₗ[ℝ] W →ₗ[ℝ] W)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ W →ₗ[ℝ] B)
    (ρ : Fin 1 ⊕ Fin 3) (l : List (Fin 1 ⊕ Fin 3)) :
    covDerivIter A act F (ρ :: l) = covDerivAction A act (covDerivIter A act F l) ρ := rfl

/-- **Unitriangularity of the covariant matter tower**: the covariant and plain
  derivative symbols of a matter family differ by an element of the subalgebra
  generated by the gauge-field symbols and the strictly lower-order matter symbols.
  Stated at every derivative multiset `s`, as needed for the induction. -/
lemma covDerivIter_sub_mem (act : GaugeAlgebra →ₗ[ℝ] W →ₗ[ℝ] W)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ W →ₗ[ℝ] B)
    (l : List (Fin 1 ⊕ Fin 3)) (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ W) :
    covDerivIter A act F l s φ - F (Multiset.ofList l + s) φ ∈
      Algebra.adjoin ℂ
        ({b : B | ∃ (u : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A u μ ψ} ∪
          {b : B | ∃ (t : Multiset (Fin 1 ⊕ Fin 3)) (χ : Module.Dual ℝ W),
            t.card < l.length + s.card ∧ b = F t χ}) := by
  induction l generalizing s φ with
  | nil =>
      simp only [covDerivIter_nil,
        show (Multiset.ofList ([] : List (Fin 1 ⊕ Fin 3))) = 0 from rfl, zero_add,
        sub_self]
      exact zero_mem _
  | cons ρ l ih =>
      have hmono : ∀ {n m : ℕ}, n ≤ m →
          Algebra.adjoin ℂ
            ({b : B | ∃ u μ ψ, b = A u μ ψ} ∪
              {b : B | ∃ (t : Multiset (Fin 1 ⊕ Fin 3)) (χ : Module.Dual ℝ W),
                t.card < n ∧ b = F t χ}) ≤
          Algebra.adjoin ℂ
            ({b : B | ∃ u μ ψ, b = A u μ ψ} ∪
              {b : B | ∃ (t : Multiset (Fin 1 ⊕ Fin 3)) (χ : Module.Dual ℝ W),
                t.card < m ∧ b = F t χ}) := by
        intro n m hnm
        refine Algebra.adjoin_mono (Set.union_subset_union_right _ ?_)
        rintro b ⟨t, χ, ht, rfl⟩
        exact ⟨t, χ, by omega, rfl⟩
      have hms : Multiset.ofList (ρ :: l) + s = Multiset.ofList l + (ρ ::ₘ s) := by
        rw [show Multiset.ofList (ρ :: l) = ρ ::ₘ Multiset.ofList l from rfl,
          Multiset.cons_add, Multiset.add_cons]
      have hsplit : covDerivIter A act F (ρ :: l) s φ -
          F (Multiset.ofList (ρ :: l) + s) φ =
        (covDerivIter A act F l (ρ ::ₘ s) φ -
            F (Multiset.ofList l + (ρ ::ₘ s)) φ) +
          actionFamConv A act ρ (covDerivIter A act F l) s φ := by
        rw [show covDerivIter A act F (ρ :: l) s φ =
              covDerivIter A act F l (ρ ::ₘ s) φ +
                actionFamConv A act ρ (covDerivIter A act F l) s φ
            from rfl, hms]
        abel
      rw [hsplit]
      refine add_mem ?_ ?_
      · refine hmono ?_ (ih (ρ ::ₘ s) φ)
        simp only [List.length_cons, Multiset.card_cons]
        omega
      · rw [actionFamConv, Multiset.sum_linearMap_apply, Multiset.map_map]
        refine multiset_sum_mem _ fun x hx => ?_
        obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hx
        have hle := Multiset.mem_antidiagonal.mp hp
        have h2 : p.2.card ≤ s.card :=
          hle ▸ Multiset.card_le_card (Multiset.le_add_left _ _)
        refine actionFam_apply_mem (fun ψ => ?_) (fun χ => ?_) _
        · exact Algebra.subset_adjoin (Or.inl ⟨p.1, ρ, ψ, rfl⟩)
        · have h3 : covDerivIter A act F l p.2 χ =
              (covDerivIter A act F l p.2 χ - F (Multiset.ofList l + p.2) χ) +
              F (Multiset.ofList l + p.2) χ := by abel
          rw [h3]
          refine add_mem (hmono ?_ (ih p.2 χ)) ?_
          · simp only [List.length_cons]
            omega
          · refine Algebra.subset_adjoin (Or.inr ⟨Multiset.ofList l + p.2, χ, ?_, rfl⟩)
            simp only [Multiset.card_add, Multiset.coe_card, List.length_cons]
            omega

/-- **The span lemma**: the algebra of symbols generated by the gauge field together
  with a matter family's *derivative* symbols equals the one generated by the gauge
  field together with the matter family's *covariant* derivative tower. The
  correction `∇_ρ − ∂_ρ` is the derived action of the gauge field — a sum of products
  of symbols, absorbed by the algebra structure. -/
theorem adjoin_symbols_eq_adjoin_covDerivIter (act : GaugeAlgebra →ₗ[ℝ] W →ₗ[ℝ] W)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ W →ₗ[ℝ] B) :
    Algebra.adjoin ℂ
      ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
          (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
        {b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ W),
          b = F s φ}) =
    Algebra.adjoin ℂ
      ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
          (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
        {b : B | ∃ (l : List (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ W),
          b = covDerivIter A act F l 0 φ}) := by
  refine le_antisymm (Algebra.adjoin_le ?_) (Algebra.adjoin_le ?_)
  · rintro x (⟨s, μ, ψ, rfl⟩ | ⟨s, φ, rfl⟩)
    · exact Algebra.subset_adjoin (Or.inl ⟨s, μ, ψ, rfl⟩)
    · -- express a matter symbol through the covariant tower, by strong induction on
      -- the order
      have main : ∀ n, ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ W),
          s.card ≤ n →
          F s φ ∈ Algebra.adjoin ℂ
            ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
                (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
              {b : B | ∃ (l : List (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ W),
                b = covDerivIter A act F l 0 φ}) := by
        intro n
        induction n using Nat.strong_induction_on with
        | _ n ih =>
          intro s φ hs
          set l := s.toList with hl'
          have hl : Multiset.ofList l = s := Multiset.coe_toList _
          have hlen : l.length = s.card := by rw [← Multiset.coe_card, hl]
          rw [show F s φ = covDerivIter A act F l 0 φ -
              (covDerivIter A act F l 0 φ - F (Multiset.ofList l + 0) φ) from by
            rw [add_zero, hl]; abel]
          refine sub_mem (Algebra.subset_adjoin (Or.inr ⟨l, φ, rfl⟩)) ?_
          refine SetLike.le_def.mp (Algebra.adjoin_le ?_)
            (covDerivIter_sub_mem act F l 0 φ)
          rintro b (⟨u, μ, ψ, rfl⟩ | ⟨t, χ, htc, rfl⟩)
          · exact Algebra.subset_adjoin (Or.inl ⟨u, μ, ψ, rfl⟩)
          · have htn : t.card < n := by
              simp only [Multiset.card_zero] at htc
              omega
            exact ih t.card htn t χ (le_refl _)
      exact main s.card s φ (le_refl _)
  · rintro x (⟨s, μ, ψ, rfl⟩ | ⟨l, φ, rfl⟩)
    · exact Algebra.subset_adjoin (Or.inl ⟨s, μ, ψ, rfl⟩)
    · -- the covariant tower consists of symbol polynomials
      have main : ∀ (l : List (Fin 1 ⊕ Fin 3)) (s : Multiset (Fin 1 ⊕ Fin 3))
          (φ : Module.Dual ℝ W),
          covDerivIter A act F l s φ ∈ Algebra.adjoin ℂ
            ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
                (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
              {b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ W),
                b = F s φ}) := by
        intro l
        induction l with
        | nil => exact fun s φ => Algebra.subset_adjoin (Or.inr ⟨s, φ, rfl⟩)
        | cons ρ l ih =>
            intro s φ
            rw [covDerivIter_cons, covDerivAction_apply]
            refine add_mem (ih (ρ ::ₘ s) φ) ?_
            rw [actionFamConv, Multiset.sum_linearMap_apply, Multiset.map_map]
            refine multiset_sum_mem _ fun x hx => ?_
            obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hx
            refine actionFam_apply_mem (fun ψ' => ?_) (fun χ => ?_) _
            · exact Algebra.subset_adjoin (Or.inl ⟨p.1, ρ, ψ', rfl⟩)
            · exact ih p.2 χ
      exact main l 0 φ

end Action


end IsGaugeField

end StandardModel
