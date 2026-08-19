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

The compatibility between `rep` and `act` is the structure `IsInfinitesimalActionOf`:
its two fields are the Leibniz law of the representation coefficients in the
Maurer–Cartan form (`repCoeff_cons`, the analogue of `adjointDualCoeff_cons`) and
the intertwining of `act` by the transports (`repCoeff_act`, the analogue of
`adjointTransport_bracket`). Under it the covariant derivative preserves the gauge
tensors: `TransformsIn.covDerivAction`.

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
variable {A : (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B}
variable {D : (Fin 1 ⊕ Fin 3) → B →ₗ[ℂ] B}
variable [Lorentz.IsLorentzDeriv repLorentz D]
variable {D_comm : ∀ μ ν, (D μ).comp (D ν) = (D ν).comp (D μ)}

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
def TransformsIn (_hA : IsGaugeField repLorentz repGauge A D D_comm)
    (rep : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V))
    (F : Module.Dual ℝ V →ₗ[ℝ] B) : Prop :=
  ∀ (U : JetGaugeGroupI) (φ : Module.Dual ℝ V) (s : Multiset (Fin 1 ⊕ Fin 3)),
    repGauge U (Lorentz.iteratedD D D_comm s (F φ)) =
      (s.antidiagonal.map fun p =>
        Lorentz.iteratedD D D_comm p.2 (F (repDualCoeff rep U⁻¹ p.1 φ))).sum

/-!

## The infinitesimal action underlying a representation

-/

/-- `act` is the *infinitesimal action* of the gauge algebra underlying the
  representation `rep` of the jet gauge group, when the base-point Taylor
  coefficients of `rep` satisfy the two laws forced by `rep` being generated by
  `act`:

  * `repCoeff_cons` — the Leibniz rule in the Maurer–Cartan form: differentiating
    the representation once produces minus the action of the Maurer–Cartan form,
    with the remaining derivatives distributed over the antidiagonal (for the
    adjoint representation this is `adjointDualCoeff_cons`);
  * `repCoeff_act` — the transports of `rep` intertwine `act` with the adjoint
    transports, as an antidiagonal convolution (for the adjoint representation this
    is `adjointTransport_bracket`); at `x = 0` it is the classical equivariance
    `rep(U)|₀ ∘ act c = act (Ad(U) c)|₀ ∘ rep(U)|₀`.

  These are exactly the identities consumed by the proof that the covariant
  derivative `covDerivAction` preserves `TransformsIn`. -/
structure IsInfinitesimalActionOf (act : GaugeAlgebra →ₗ[ℝ] V →ₗ[ℝ] V)
    (rep : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V)) : Prop where
  repCoeff_cons : ∀ (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3)
      (x : Multiset (Fin 1 ⊕ Fin 3)),
    repCoeff rep U (μ ::ₘ x) =
      -((x.antidiagonal.map fun p =>
        act (JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv p.1
          (maurerCartanForm U μ))) ∘ₗ repCoeff rep U p.2).sum)
  repCoeff_act : ∀ (U : JetGaugeGroupI) (x : Multiset (Fin 1 ⊕ Fin 3))
      (c : GaugeAlgebra),
    repCoeff rep U x ∘ₗ act c =
      ((x.antidiagonal.map fun p =>
        act (adjointCoeff U p.1 c) ∘ₗ repCoeff rep U p.2).sum)

/-- The dual form of the Leibniz law: the once-more-derived dual coefficient is
  minus the antidiagonal convolution of dual coefficients against `act` of the
  derived Maurer–Cartan form — the analogue of `adjointDualCoeff_cons`. -/
lemma IsInfinitesimalActionOf.repDualCoeff_cons
    {act : GaugeAlgebra →ₗ[ℝ] V →ₗ[ℝ] V}
    {rep : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V)}
    (h : IsInfinitesimalActionOf act rep) (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3)
    (x : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ V) :
    repDualCoeff rep U (μ ::ₘ x) φ =
      -((x.antidiagonal.map fun p =>
        repDualCoeff rep U p.2 (φ ∘ₗ act (JetGaugeAlgebra.eval
          (JetGaugeAlgebra.iteratedDeriv p.1 (maurerCartanForm U μ))))).sum) := by
  refine LinearMap.ext fun v => ?_
  have h1 := LinearMap.congr_fun (h.repCoeff_cons U μ x) v
  simp only [LinearMap.neg_apply, Multiset.sum_linearMap_apply, Multiset.map_map,
    Function.comp_apply, LinearMap.coe_comp] at h1
  simp only [repDualCoeff, LinearMap.dualMap_apply, LinearMap.neg_apply,
    Multiset.sum_linearMap_apply, Multiset.map_map, Function.comp_apply,
    LinearMap.coe_comp]
  rw [h1, map_neg, map_multiset_sum, Multiset.map_map]
  exact congrArg Neg.neg (congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => rfl))

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

/-- With `D` a derivation, the one-step Leibniz rule for the action of families. -/
lemma deriv_actionFam (hD : ∀ (κ : Fin 1 ⊕ Fin 3) (b₁ b₂ : B),
      D κ (b₁ * b₂) = D κ b₁ * b₂ + b₁ * D κ b₂) (κ : Fin 1 ⊕ Fin 3)
    (f : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B) (g : Module.Dual ℝ W →ₗ[ℝ] B)
    (φ : Module.Dual ℝ W) :
    D κ (actionFam act f g φ) =
      actionFam act ((D κ).restrictScalars ℝ ∘ₗ f) g φ +
      actionFam act f ((D κ).restrictScalars ℝ ∘ₗ g) φ := by
  have h := congrArg (fun z => dualPairEquivW z φ)
    (tensorAction_map_left_derivation act ((D κ).restrictScalars ℝ)
      (fun b₁ b₂ => hD κ b₁ b₂) (dualPairEquiv.symm f) (dualPairEquivW.symm g))
  simp only [map_add, LinearMap.add_apply, dualPairEquivW_map_left] at h
  rw [← symm_comp_left, ← symm_comp_left_W] at h
  exact h

/-- The iterated Leibniz rule for the action of families: the iterated derivative of
  `A · F` is the antidiagonal convolution of derived actions. -/
lemma iteratedD_actionFam (hD : ∀ (κ : Fin 1 ⊕ Fin 3) (b₁ b₂ : B),
      D κ (b₁ * b₂) = D κ b₁ * b₂ + b₁ * D κ b₂) (s : Multiset (Fin 1 ⊕ Fin 3))
    (f : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B) (g : Module.Dual ℝ W →ₗ[ℝ] B)
    (φ : Module.Dual ℝ W) :
    Lorentz.iteratedD D D_comm s (actionFam act f g φ) =
      (s.antidiagonal.map fun p =>
        actionFam act ((Lorentz.iteratedD D D_comm p.1).restrictScalars ℝ ∘ₗ f)
          ((Lorentz.iteratedD D D_comm p.2).restrictScalars ℝ ∘ₗ g) φ).sum := by
  induction s using Multiset.induction_on generalizing f g with
  | empty =>
      simp [Lorentz.iteratedD_zero, Multiset.antidiagonal_zero,
        show (LinearMap.id : B →ₗ[ℂ] B).restrictScalars ℝ = LinearMap.id from rfl]
  | cons κ s ih =>
      rw [Lorentz.iteratedD_cons, LinearMap.comp_apply, ih f g, map_multiset_sum,
        Multiset.map_map,
        Multiset.map_congr rfl (fun p hp => by
          rw [Function.comp_apply, deriv_actionFam hD κ,
            show (D κ).restrictScalars ℝ ∘ₗ
                ((Lorentz.iteratedD D D_comm p.1).restrictScalars ℝ ∘ₗ f) =
              (Lorentz.iteratedD D D_comm (κ ::ₘ p.1)).restrictScalars ℝ ∘ₗ f from by
              rw [Lorentz.iteratedD_cons]; rfl,
            show (D κ).restrictScalars ℝ ∘ₗ
                ((Lorentz.iteratedD D D_comm p.2).restrictScalars ℝ ∘ₗ g) =
              (Lorentz.iteratedD D D_comm (κ ::ₘ p.2)).restrictScalars ℝ ∘ₗ g from by
              rw [Lorentz.iteratedD_cons]; rfl]),
        Multiset.sum_map_add]
      simp only [Multiset.antidiagonal_cons, Multiset.map_add, Multiset.sum_add,
        Multiset.map_map, Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
      abel

set_option maxHeartbeats 1000000 in
/-- The gauge transformation of the action of an affinely-transforming
  adjoint-indexed family on a linearly-transforming `W`-indexed family: the action of
  the transformed families plus one `ad`-type cross term through `act`. This is
  `repGauge_bracketFam` with a homogeneous second slot and the bracket replaced by
  a general action. -/
lemma repGauge_actionFam (hA : IsGaugeField repLorentz repGauge A D D_comm)
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

/-- The covariant derivative of a `W`-indexed component family through the
  infinitesimal action `act` of the gauge algebra on `W`:

  `∇_ρ F = D_ρ F + A_ρ · F`,

  the total derivative plus the action of the gauge field on the value index. With
  the physicists' factor of `i` absorbed into `act` (as it is in the gauge-algebra
  bracket), this is `∂_ρ F + i A_ρ^a T_a F` in the `D = ∂ + i A` convention. For the
  adjoint action it is `covDerivAdjoint` (`covDerivAction_ad`). -/
noncomputable def covDerivAction
    (A : (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (act : GaugeAlgebra →ₗ[ℝ] W →ₗ[ℝ] W) (F : Module.Dual ℝ W →ₗ[ℝ] B)
    (D : (Fin 1 ⊕ Fin 3) → B →ₗ[ℂ] B) (ρ : Fin 1 ⊕ Fin 3) :
    Module.Dual ℝ W →ₗ[ℝ] B :=
  (D ρ).restrictScalars ℝ ∘ₗ F + actionFam act (A ρ) F

@[simp]
lemma covDerivAction_apply (A : (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (act : GaugeAlgebra →ₗ[ℝ] W →ₗ[ℝ] W) (F : Module.Dual ℝ W →ₗ[ℝ] B)
    (D : (Fin 1 ⊕ Fin 3) → B →ₗ[ℂ] B) (ρ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ W) :
    covDerivAction A act F D ρ φ = D ρ (F φ) + actionFam act (A ρ) F φ := rfl

/-- Through the adjoint action, the general covariant derivative is the adjoint
  one. -/
lemma covDerivAction_adAction (F : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (ρ : Fin 1 ⊕ Fin 3) :
    covDerivAction A adAction F D ρ = covDerivAdjoint A F D ρ := rfl

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

/-- Iterated covariant derivatives along a list of directions. -/
noncomputable def covDerivIter (A : (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (act : GaugeAlgebra →ₗ[ℝ] W →ₗ[ℝ] W) (F : Module.Dual ℝ W →ₗ[ℝ] B)
    (D : (Fin 1 ⊕ Fin 3) → B →ₗ[ℂ] B) (l : List (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℝ W →ₗ[ℝ] B :=
  l.foldr (fun ρ G => covDerivAction A act G D ρ) F

@[simp]
lemma covDerivIter_nil (act : GaugeAlgebra →ₗ[ℝ] W →ₗ[ℝ] W)
    (F : Module.Dual ℝ W →ₗ[ℝ] B) : covDerivIter A act F D [] = F := rfl

@[simp]
lemma covDerivIter_cons (act : GaugeAlgebra →ₗ[ℝ] W →ₗ[ℝ] W)
    (F : Module.Dual ℝ W →ₗ[ℝ] B) (ρ : Fin 1 ⊕ Fin 3) (l : List (Fin 1 ⊕ Fin 3)) :
    covDerivIter A act F D (ρ :: l) =
      covDerivAction A act (covDerivIter A act F D l) D ρ := rfl

/-- With `D` a derivation, `D` kills the scalars. -/
lemma deriv_algebraMap_eq_zero (hD : ∀ (κ : Fin 1 ⊕ Fin 3) (b₁ b₂ : B),
      D κ (b₁ * b₂) = D κ b₁ * b₂ + b₁ * D κ b₂) (κ : Fin 1 ⊕ Fin 3) (c : ℂ) :
    D κ (algebraMap ℂ B c) = 0 := by
  have h1 : D κ (1 : B) = 0 := by
    have h := hD κ 1 1
    rw [one_mul, one_mul, mul_one] at h
    have h2 : D κ (1 : B) + 0 = D κ (1 : B) + D κ (1 : B) := by rw [add_zero]; exact h
    exact (add_left_cancel h2).symm
  rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero]

/-- A subalgebra generated by a `D`-stable set of generators is `D`-stable. -/
lemma adjoin_deriv_mem {S : Set B}
    (hD : ∀ (κ : Fin 1 ⊕ Fin 3) (b₁ b₂ : B),
      D κ (b₁ * b₂) = D κ b₁ * b₂ + b₁ * D κ b₂)
    (hS : ∀ (κ : Fin 1 ⊕ Fin 3), ∀ x ∈ S, D κ x ∈ Algebra.adjoin ℂ S)
    (κ : Fin 1 ⊕ Fin 3) {x : B} (hx : x ∈ Algebra.adjoin ℂ S) :
    D κ x ∈ Algebra.adjoin ℂ S := by
  induction hx using Algebra.adjoin_induction with
  | mem y hy => exact hS κ y hy
  | algebraMap c =>
      rw [deriv_algebraMap_eq_zero hD κ c]
      exact zero_mem _
  | add y z hy hz ihy ihz =>
      rw [map_add]
      exact add_mem ihy ihz
  | mul y z hy hz ihy ihz =>
      rw [hD κ y z]
      exact add_mem (mul_mem ihy hz) (mul_mem hy ihz)

/-- A subalgebra generated by a `D`-stable set of generators is stable under
  iterated derivatives. -/
lemma adjoin_iteratedD_mem {S : Set B}
    (hD : ∀ (κ : Fin 1 ⊕ Fin 3) (b₁ b₂ : B),
      D κ (b₁ * b₂) = D κ b₁ * b₂ + b₁ * D κ b₂)
    (hS : ∀ (κ : Fin 1 ⊕ Fin 3), ∀ x ∈ S, D κ x ∈ Algebra.adjoin ℂ S)
    (s : Multiset (Fin 1 ⊕ Fin 3)) {x : B} (hx : x ∈ Algebra.adjoin ℂ S) :
    Lorentz.iteratedD D D_comm s x ∈ Algebra.adjoin ℂ S := by
  induction s using Multiset.induction_on with
  | empty => rw [Lorentz.iteratedD_zero]; exact hx
  | cons κ t ih =>
      rw [Lorentz.iteratedD_cons, LinearMap.comp_apply]
      exact adjoin_deriv_mem hD hS κ ih

set_option maxHeartbeats 1000000 in
/-- **The span lemma**: the algebra of symbols generated by the gauge field with its
  derivatives together with a matter family with its *derivatives* equals the one
  generated by the gauge field with its derivatives together with the matter family
  with its *covariant* derivatives. The correction `∇_ρ − ∂_ρ` is the action of the
  gauge field — a sum of products of symbols, absorbed by the algebra structure. -/
theorem adjoin_iteratedD_eq_adjoin_covDerivIter
    (hD : ∀ (κ : Fin 1 ⊕ Fin 3) (b₁ b₂ : B),
      D κ (b₁ * b₂) = D κ b₁ * b₂ + b₁ * D κ b₂)
    (act : GaugeAlgebra →ₗ[ℝ] W →ₗ[ℝ] W) (F : Module.Dual ℝ W →ₗ[ℝ] B) :
    Algebra.adjoin ℂ
      ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
          (ψ : Module.Dual ℝ GaugeAlgebra), b = Lorentz.iteratedD D D_comm s (A μ ψ)} ∪
        {b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ W),
          b = Lorentz.iteratedD D D_comm s (F φ)}) =
    Algebra.adjoin ℂ
      ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
          (ψ : Module.Dual ℝ GaugeAlgebra), b = Lorentz.iteratedD D D_comm s (A μ ψ)} ∪
        {b : B | ∃ (l : List (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ W),
          b = covDerivIter A act F D l φ}) := by
  have hA0 : ∀ (μ : Fin 1 ⊕ Fin 3) (ψ : Module.Dual ℝ GaugeAlgebra),
      A μ ψ = Lorentz.iteratedD D D_comm 0 (A μ ψ) := fun μ ψ => by
    rw [Lorentz.iteratedD_zero]; rfl
  have hDA : ∀ (κ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) (y : B),
      D κ (Lorentz.iteratedD D D_comm s y) =
        Lorentz.iteratedD D D_comm (κ ::ₘ s) y := fun κ s y => by
    rw [Lorentz.iteratedD_cons]; rfl
  -- `D`-stability of the generators on the covariant side
  have hS₂ : ∀ (κ : Fin 1 ⊕ Fin 3), ∀ x ∈
      ({b : B | ∃ s μ ψ, b = Lorentz.iteratedD D D_comm s (A μ ψ)} ∪
        {b : B | ∃ l φ, b = covDerivIter A act F D l φ}),
      D κ x ∈ Algebra.adjoin ℂ
        ({b : B | ∃ s μ ψ, b = Lorentz.iteratedD D D_comm s (A μ ψ)} ∪
          {b : B | ∃ l φ, b = covDerivIter A act F D l φ}) := by
    rintro κ x (⟨s, μ, ψ, rfl⟩ | ⟨l, φ, rfl⟩)
    · exact Algebra.subset_adjoin (Set.mem_union_left _ ⟨κ ::ₘ s, μ, ψ, hDA κ s _⟩)
    · have hsplit : D κ (covDerivIter A act F D l φ) =
          covDerivIter A act F D (κ :: l) φ
          - actionFam act (A κ) (covDerivIter A act F D l) φ := by
        rw [covDerivIter_cons, covDerivAction_apply]
        abel
      rw [hsplit]
      have hmem₁ : covDerivIter A act F D (κ :: l) φ ∈
          ({b : B | ∃ s μ ψ, b = Lorentz.iteratedD D D_comm s (A μ ψ)} ∪
            {b : B | ∃ l φ, b = covDerivIter A act F D l φ}) :=
        Set.mem_union_right _ ⟨κ :: l, φ, rfl⟩
      have hmemA : ∀ ψ' : Module.Dual ℝ GaugeAlgebra, A κ ψ' ∈
          ({b : B | ∃ s μ ψ, b = Lorentz.iteratedD D D_comm s (A μ ψ)} ∪
            {b : B | ∃ l φ, b = covDerivIter A act F D l φ}) :=
        fun ψ' => Set.mem_union_left _ ⟨0, κ, ψ', hA0 κ ψ'⟩
      have hmemC : ∀ χ : Module.Dual ℝ W, covDerivIter A act F D l χ ∈
          ({b : B | ∃ s μ ψ, b = Lorentz.iteratedD D D_comm s (A μ ψ)} ∪
            {b : B | ∃ l φ, b = covDerivIter A act F D l φ}) :=
        fun χ => Set.mem_union_right _ ⟨l, χ, rfl⟩
      exact sub_mem (Algebra.subset_adjoin hmem₁)
        (actionFam_apply_mem (fun ψ' => Algebra.subset_adjoin (hmemA ψ'))
          (fun χ => Algebra.subset_adjoin (hmemC χ)) φ)
  -- `D`-stability of the generators on the derivative side
  have hS₁ : ∀ (κ : Fin 1 ⊕ Fin 3), ∀ x ∈
      ({b : B | ∃ s μ ψ, b = Lorentz.iteratedD D D_comm s (A μ ψ)} ∪
        {b : B | ∃ s φ, b = Lorentz.iteratedD D D_comm s (F φ)}),
      D κ x ∈ Algebra.adjoin ℂ
        ({b : B | ∃ s μ ψ, b = Lorentz.iteratedD D D_comm s (A μ ψ)} ∪
          {b : B | ∃ s φ, b = Lorentz.iteratedD D D_comm s (F φ)}) := by
    rintro κ x (⟨s, μ, ψ, rfl⟩ | ⟨s, φ, rfl⟩)
    · exact Algebra.subset_adjoin (Set.mem_union_left _ ⟨κ ::ₘ s, μ, ψ, hDA κ s _⟩)
    · exact Algebra.subset_adjoin (Set.mem_union_right _ ⟨κ ::ₘ s, φ, hDA κ s _⟩)
  refine le_antisymm (Algebra.adjoin_le ?_) (Algebra.adjoin_le ?_)
  · rintro x (⟨s, μ, ψ, rfl⟩ | ⟨s, φ, rfl⟩)
    · exact Algebra.subset_adjoin (Set.mem_union_left _ ⟨s, μ, ψ, rfl⟩)
    · refine adjoin_iteratedD_mem hD hS₂ s ?_
      have hmem : F φ ∈
          ({b : B | ∃ s μ ψ, b = Lorentz.iteratedD D D_comm s (A μ ψ)} ∪
            {b : B | ∃ l φ, b = covDerivIter A act F D l φ}) :=
        Set.mem_union_right _ ⟨[], φ, by rw [covDerivIter_nil]⟩
      exact Algebra.subset_adjoin hmem
  · rintro x (⟨s, μ, ψ, rfl⟩ | ⟨l, φ, rfl⟩)
    · exact Algebra.subset_adjoin (Set.mem_union_left _ ⟨s, μ, ψ, rfl⟩)
    · induction l generalizing φ with
      | nil =>
          have hmem : covDerivIter A act F D [] φ ∈
              ({b : B | ∃ s μ ψ, b = Lorentz.iteratedD D D_comm s (A μ ψ)} ∪
                {b : B | ∃ s φ, b = Lorentz.iteratedD D D_comm s (F φ)}) :=
            Set.mem_union_right _
              ⟨0, φ, by rw [Lorentz.iteratedD_zero, covDerivIter_nil]; rfl⟩
          exact Algebra.subset_adjoin hmem
      | cons κ l ih =>
          rw [covDerivIter_cons, covDerivAction_apply]
          have hmemA : ∀ ψ' : Module.Dual ℝ GaugeAlgebra, A κ ψ' ∈
              ({b : B | ∃ s μ ψ, b = Lorentz.iteratedD D D_comm s (A μ ψ)} ∪
                {b : B | ∃ s φ, b = Lorentz.iteratedD D D_comm s (F φ)}) :=
            fun ψ' => Set.mem_union_left _ ⟨0, κ, ψ', hA0 κ ψ'⟩
          exact add_mem (adjoin_deriv_mem hD hS₁ κ (ih φ))
            (actionFam_apply_mem (fun ψ' => Algebra.subset_adjoin (hmemA ψ'))
              (fun χ => ih χ) φ)

end Action

/-!

## The covariant derivative preserves `TransformsIn`

-/

section MatterCovariance

variable {rep : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V)}
variable {act : GaugeAlgebra →ₗ[ℝ] V →ₗ[ℝ] V}
variable [FiniteDimensional ℝ V]

/-- The action of families against the dual representation coefficients: the
  antidiagonal convolution mixing the adjoint transport on the field slot with the
  representation transport on the matter slot — the family-level form of
  `IsInfinitesimalActionOf.repCoeff_act`, and the analogue of
  `bracketFam_adjointDualCoeff`. -/
lemma IsInfinitesimalActionOf.actionFam_repDualCoeff
    (h : IsInfinitesimalActionOf act rep) (U : JetGaugeGroupI)
    (x : Multiset (Fin 1 ⊕ Fin 3)) (f : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (g : Module.Dual ℝ V →ₗ[ℝ] B) (φ : Module.Dual ℝ V) :
    actionFam act f g (repDualCoeff rep U x φ) =
      (x.antidiagonal.map fun p =>
        actionFam act (f ∘ₗ adjointDualCoeff U p.1)
          (g ∘ₗ repDualCoeff rep U p.2) φ).sum := by
  have hT : ∀ (c : GaugeAlgebra) (v : V), repCoeff rep U x (act c v) =
      (x.antidiagonal.map fun p =>
        act (adjointCoeff U p.1 c) (repCoeff rep U p.2 v)).sum := by
    intro c v
    have h1 := LinearMap.congr_fun (h.repCoeff_act U x c) v
    simpa [Multiset.sum_linearMap_apply, Multiset.map_map, LinearMap.coe_comp,
      Function.comp_apply] using h1
  rw [show repDualCoeff rep U x = (repCoeff rep U x).dualMap from rfl,
    show actionFam act f g ((repCoeff rep U x).dualMap φ) =
      dualPairEquivW ((TensorProduct.map LinearMap.id (repCoeff rep U x))
        (tensorAction act (dualPairEquiv.symm f) (dualPairEquivW.symm g))) φ from
      (dualPairEquivW_map_right (repCoeff rep U x) _ φ).symm,
    ← tensorAction_map_right_antidiagonal act (adjointCoeff U) (repCoeff rep U) x hT,
    map_multiset_sum, Multiset.map_map, Multiset.sum_linearMap_apply, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
  simp only [Function.comp_apply]
  rw [← symm_comp_right, ← symm_comp_right_W]
  rfl

omit [FiniteDimensional ℝ V] in
/-- If `F` transforms in `rep`, so do its `κ ::ₘ s`-derived symbols, with the extra
  derivative traced through `IsInfinitesimalActionOf.repDualCoeff_cons`: the Leibniz
  splittings where `κ` stays a derivative, minus the convolution where `κ` hits the
  representation — `act` of the derived Maurer–Cartan form. -/
lemma TransformsIn.repGauge_iteratedD_cons
    {hA : IsGaugeField repLorentz repGauge A D D_comm}
    {F : Module.Dual ℝ V →ₗ[ℝ] B} (hF : hA.TransformsIn rep F)
    (hact : IsInfinitesimalActionOf act rep)
    (U : JetGaugeGroupI) (κ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℝ V) :
    repGauge U (Lorentz.iteratedD D D_comm (κ ::ₘ s) (F φ)) =
      (s.antidiagonal.map fun p =>
        Lorentz.iteratedD D D_comm (κ ::ₘ p.2) (F (repDualCoeff rep U⁻¹ p.1 φ))).sum
      - (s.antidiagonal.map fun p =>
          (p.1.antidiagonal.map fun q =>
            Lorentz.iteratedD D D_comm p.2 (F (repDualCoeff rep U⁻¹ q.2
              (φ ∘ₗ act (JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv q.1
                (maurerCartanForm U⁻¹ κ))))))).sum).sum := by
  rw [hF U φ (κ ::ₘ s)]
  simp only [Multiset.antidiagonal_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
  have hsec : (Multiset.map (fun p => Lorentz.iteratedD D D_comm p.2
        (F (repDualCoeff rep U⁻¹ (κ ::ₘ p.1) φ))) s.antidiagonal).sum =
      -(s.antidiagonal.map fun p =>
          (p.1.antidiagonal.map fun q =>
            Lorentz.iteratedD D D_comm p.2 (F (repDualCoeff rep U⁻¹ q.2
              (φ ∘ₗ act (JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv q.1
                (maurerCartanForm U⁻¹ κ))))))).sum).sum := by
    rw [← Multiset.sum_map_neg'']
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [hact.repDualCoeff_cons U⁻¹ κ p.1 φ, map_neg, map_neg, map_multiset_sum,
      Multiset.map_map, map_multiset_sum, Multiset.map_map]
    exact congrArg Neg.neg (congrArg Multiset.sum (Multiset.map_congr rfl fun q hq => rfl))
  rw [hsec, sub_eq_add_neg]

set_option maxHeartbeats 2000000 in
/-- The all-orders gauge transformation of the derived action `A_ρ · F` for `F`
  transforming in `rep`: since `F` transforms homogeneously, only one cross-term
  convolution through `act` survives — the analogue of
  `repGauge_iteratedD_commutator` with a matter field in the second slot. -/
lemma TransformsIn.repGauge_iteratedD_action
    {hA : IsGaugeField repLorentz repGauge A D D_comm}
    (hD : ∀ (κ : Fin 1 ⊕ Fin 3) (b₁ b₂ : B), D κ (b₁ * b₂) = D κ b₁ * b₂ + b₁ * D κ b₂)
    {F : Module.Dual ℝ V →ₗ[ℝ] B} (hF : hA.TransformsIn rep F)
    (hact : IsInfinitesimalActionOf act rep)
    (U : JetGaugeGroupI) (s : Multiset (Fin 1 ⊕ Fin 3)) (ρ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ V) :
    repGauge U (Lorentz.iteratedD D D_comm s (actionFam act (A ρ) F φ)) =
      (s.antidiagonal.map fun p =>
        Lorentz.iteratedD D D_comm p.2 (actionFam act (A ρ) F
          (repDualCoeff rep U⁻¹ p.1 φ))).sum
      + (s.antidiagonal.map fun p =>
          (p.2.antidiagonal.map fun r =>
            Lorentz.iteratedD D D_comm r.2 (F (repDualCoeff rep U⁻¹ r.1
              (φ ∘ₗ act (JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv p.1
                (maurerCartanForm U⁻¹ ρ))))))).sum).sum := by
  have hAlaw : ∀ (u : Multiset (Fin 1 ⊕ Fin 3)) (ψ : Module.Dual ℝ GaugeAlgebra),
      repGauge U (((Lorentz.iteratedD D D_comm u).restrictScalars ℝ ∘ₗ A ρ) ψ) =
        ((u.antidiagonal.map fun q =>
          (Lorentz.iteratedD D D_comm q.2).restrictScalars ℝ ∘ₗ A ρ ∘ₗ
            adjointDualCoeff U⁻¹ q.1).sum) ψ
        + algebraMap ℂ B (ψ (JetGaugeAlgebra.eval
            (JetGaugeAlgebra.iteratedDeriv u (maurerCartanForm U⁻¹ ρ)))) := by
    intro u ψ
    show repGauge U (Lorentz.iteratedD D D_comm u (A ρ ψ)) = _
    rw [hA.gauge_apply_deriv U u ρ ψ, Multiset.sum_linearMap_apply, Multiset.map_map]
    congr 1
  have hFlaw : ∀ (u : Multiset (Fin 1 ⊕ Fin 3)) (ψ : Module.Dual ℝ V),
      repGauge U (((Lorentz.iteratedD D D_comm u).restrictScalars ℝ ∘ₗ F) ψ) =
        ((u.antidiagonal.map fun r =>
          (Lorentz.iteratedD D D_comm r.2).restrictScalars ℝ ∘ₗ F ∘ₗ
            repDualCoeff rep U⁻¹ r.1).sum) ψ := by
    intro u ψ
    show repGauge U (Lorentz.iteratedD D D_comm u (F ψ)) = _
    rw [hF U ψ u, Multiset.sum_linearMap_apply, Multiset.map_map]
    congr 1
  have hMa : (s.antidiagonal.map fun p =>
      actionFam act ((p.1.antidiagonal.map fun q =>
          (Lorentz.iteratedD D D_comm q.2).restrictScalars ℝ ∘ₗ A ρ ∘ₗ
            adjointDualCoeff U⁻¹ q.1).sum)
        ((p.2.antidiagonal.map fun r =>
          (Lorentz.iteratedD D D_comm r.2).restrictScalars ℝ ∘ₗ F ∘ₗ
            repDualCoeff rep U⁻¹ r.1).sum) φ).sum =
      (s.antidiagonal.map fun p =>
        (p.1.antidiagonal.map fun q =>
          (p.2.antidiagonal.map fun r =>
            actionFam act ((Lorentz.iteratedD D D_comm q.2).restrictScalars ℝ ∘ₗ A ρ ∘ₗ
                adjointDualCoeff U⁻¹ q.1)
              ((Lorentz.iteratedD D D_comm r.2).restrictScalars ℝ ∘ₗ F ∘ₗ
                repDualCoeff rep U⁻¹ r.1) φ).sum).sum).sum := by
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [actionFam_sum_left, Multiset.sum_linearMap_apply, Multiset.map_map,
      Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun q hq => ?_)
    simp only [Function.comp_apply]
    rw [actionFam_sum_right, Multiset.sum_linearMap_apply, Multiset.map_map,
      Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun r hr => ?_)
    simp only [Function.comp_apply]
  have hMc : (s.antidiagonal.map fun p =>
      Lorentz.iteratedD D D_comm p.2 (actionFam act (A ρ) F
        (repDualCoeff rep U⁻¹ p.1 φ))).sum =
      (s.antidiagonal.map fun p =>
        (p.1.antidiagonal.map fun q =>
          (p.2.antidiagonal.map fun r =>
            actionFam act ((Lorentz.iteratedD D D_comm r.1).restrictScalars ℝ ∘ₗ A ρ ∘ₗ
                adjointDualCoeff U⁻¹ q.1)
              ((Lorentz.iteratedD D D_comm r.2).restrictScalars ℝ ∘ₗ F ∘ₗ
                repDualCoeff rep U⁻¹ q.2) φ).sum).sum).sum := by
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [hact.actionFam_repDualCoeff U⁻¹ p.1 (A ρ) F φ, map_multiset_sum,
      Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun q hq => ?_)
    simp only [Function.comp_apply]
    rw [iteratedD_actionFam hD p.2 (A ρ ∘ₗ adjointDualCoeff U⁻¹ q.1)
      (F ∘ₗ repDualCoeff rep U⁻¹ q.2) φ]
  have hM := hMa.trans ((Multiset.sum_antidiagonal_exchange s fun a b c d =>
      actionFam act ((Lorentz.iteratedD D D_comm b).restrictScalars ℝ ∘ₗ A ρ ∘ₗ
          adjointDualCoeff U⁻¹ a)
        ((Lorentz.iteratedD D D_comm d).restrictScalars ℝ ∘ₗ F ∘ₗ
          repDualCoeff rep U⁻¹ c) φ).trans hMc.symm)
  have hCg : ∀ p : Multiset (Fin 1 ⊕ Fin 3) × Multiset (Fin 1 ⊕ Fin 3),
      ((p.2.antidiagonal.map fun r =>
        (Lorentz.iteratedD D D_comm r.2).restrictScalars ℝ ∘ₗ F ∘ₗ
          repDualCoeff rep U⁻¹ r.1).sum)
        (φ ∘ₗ act (JetGaugeAlgebra.eval
          (JetGaugeAlgebra.iteratedDeriv p.1 (maurerCartanForm U⁻¹ ρ)))) =
      (p.2.antidiagonal.map fun r =>
        Lorentz.iteratedD D D_comm r.2 (F (repDualCoeff rep U⁻¹ r.1
          (φ ∘ₗ act (JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv p.1
            (maurerCartanForm U⁻¹ ρ))))))).sum := by
    intro p
    rw [Multiset.sum_linearMap_apply, Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun r hr => ?_)
    simp only [Function.comp_apply, LinearMap.coe_comp, LinearMap.restrictScalars_apply]
  rw [iteratedD_actionFam hD s (A ρ) F φ, map_multiset_sum, Multiset.map_map,
    Multiset.map_congr rfl (fun p hp => by
      rw [Function.comp_apply, repGauge_actionFam hA U (hAlaw p.1) (hFlaw p.2) φ,
        hCg p]),
    Multiset.sum_map_add, hM]

set_option maxHeartbeats 2000000 in
/-- **The covariant derivative preserves `TransformsIn`**: if `F` transforms in the
  representation `rep` and `act` is the infinitesimal action underlying `rep`, then
  `∇_ρ F = D_ρ F + A_ρ · F` transforms in `rep`. The single inhomogeneous
  convolution of `∂_{ρ ::ₘ s} F` cancels the single `act` cross-term convolution of
  `A_ρ · F` through the coassociativity of the antidiagonal — the matter-field
  analogue of `TransformsInAdjoint.covDerivAdjoint`. -/
theorem TransformsIn.covDerivAction
    {hA : IsGaugeField repLorentz repGauge A D D_comm}
    (hD : ∀ (κ : Fin 1 ⊕ Fin 3) (b₁ b₂ : B), D κ (b₁ * b₂) = D κ b₁ * b₂ + b₁ * D κ b₂)
    {F : Module.Dual ℝ V →ₗ[ℝ] B} (hF : hA.TransformsIn rep F)
    (hact : IsInfinitesimalActionOf act rep) (ρ : Fin 1 ⊕ Fin 3) :
    hA.TransformsIn rep (covDerivAction A act F D ρ) := by
  intro U φ s
  have hDcomp : ∀ (κ : Fin 1 ⊕ Fin 3) (t : Multiset (Fin 1 ⊕ Fin 3)) (b : B),
      Lorentz.iteratedD D D_comm t (D κ b) = Lorentz.iteratedD D D_comm (κ ::ₘ t) b := by
    intro κ t b
    rw [show (κ ::ₘ t : Multiset (Fin 1 ⊕ Fin 3)) = t + {κ} from by
        rw [add_comm, Multiset.singleton_add],
      Lorentz.iteratedD_add, LinearMap.comp_apply]
    congr 1
  have hL : repGauge U (Lorentz.iteratedD D D_comm s
      (IsGaugeField.covDerivAction A act F D ρ φ)) =
      repGauge U (Lorentz.iteratedD D D_comm (ρ ::ₘ s) (F φ))
      + repGauge U (Lorentz.iteratedD D D_comm s (actionFam act (A ρ) F φ)) := by
    rw [covDerivAction_apply, map_add, hDcomp ρ s, map_add]
  have hR : (s.antidiagonal.map fun p =>
      Lorentz.iteratedD D D_comm p.2 (IsGaugeField.covDerivAction A act F D ρ
        (repDualCoeff rep U⁻¹ p.1 φ))).sum =
      (s.antidiagonal.map fun p =>
        Lorentz.iteratedD D D_comm (ρ ::ₘ p.2) (F (repDualCoeff rep U⁻¹ p.1 φ))).sum
      + (s.antidiagonal.map fun p =>
        Lorentz.iteratedD D D_comm p.2 (actionFam act (A ρ) F
          (repDualCoeff rep U⁻¹ p.1 φ))).sum := by
    rw [← Multiset.sum_map_add]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [covDerivAction_apply, map_add, hDcomp ρ p.2]
  have hcancel : (s.antidiagonal.map fun p =>
      (p.1.antidiagonal.map fun q =>
        Lorentz.iteratedD D D_comm p.2 (F (repDualCoeff rep U⁻¹ q.2
          (φ ∘ₗ act (JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv q.1
            (maurerCartanForm U⁻¹ ρ))))))).sum).sum =
    (s.antidiagonal.map fun p =>
      (p.2.antidiagonal.map fun r =>
        Lorentz.iteratedD D D_comm r.2 (F (repDualCoeff rep U⁻¹ r.1
          (φ ∘ₗ act (JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv p.1
            (maurerCartanForm U⁻¹ ρ))))))).sum).sum :=
    Multiset.sum_antidiagonal_assoc s (fun a b c =>
      Lorentz.iteratedD D D_comm c (F (repDualCoeff rep U⁻¹ b
        (φ ∘ₗ act (JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv a
          (maurerCartanForm U⁻¹ ρ)))))))
  rw [hL, hF.repGauge_iteratedD_cons hact U ρ s φ,
    hF.repGauge_iteratedD_action hD hact U s ρ φ, hR, hcancel]
  abel

end MatterCovariance

end IsGaugeField

end StandardModel
