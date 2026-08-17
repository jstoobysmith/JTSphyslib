# Outline of the full derivation

Basic rules of this outline:
- Everything should be bullet points.
- Each bullet point contain a single logical concept.
- The distance between two bullet points in locical jumps should be small.

## Goal

- The goal of this project is to formalize the form of the
  Standard Model Lagrangian at an implicit point `x₀`.
- The lagrangian depends only on the fields and their derivatives at `x₀`.
- In reality, the EFT lagrangian is a formal infinite sum of terms of all
  mass dimensions.
- However, the questions physicists ask are about truncations of this sum,
  for example: "what is the form of the SM lagrangian up to mass dimension `n`?".
- Such truncations are always finite polynomials in the fields and their
  derivatives, because at each mass dimension there are only finitely many
  independent terms.
- It therefore suffices to work with finite polynomials: classifying the
  invariant terms at each mass dimension answers every truncated question.
- If ever needed, the full infinite sum can be recovered as a formal series
  over mass dimensions (the graded completion), without changing the
  underlying algebra of finite polynomials.

## Jet ring

- Let `JetRing` be the ring of jets.
- For `φ : JetRing`, and `p : Multiset (Fin 1 ⊕ Fin 3)` we let `∂_p| φ` be the
   `p`-th Taylor coefficient of `φ` at the base point.

## Jet component spaces

- For a vector space `V`, the space `JetRing ⊗[ℂ] V` describes the jets of all functions `f : SpaceTime → V`.
- As an example, consider a theory for a field valued in `V`.
- A physicist writes the lagrangian as a polynomial in symbols such as
  `ψ_α`, `d_μ ψ_α`, `d_μ d_ν ψ_α`.
- To formalize the lagrangian, we must first say what kind of object a
  symbol `d_s ψ_α` is.
- The symbol `d_s ψ_α` is a machine which takes a field and returns a
  number: the `s`-th derivative of its `α`-th component at `x₀`.
- A field enters only through its jet, so `d_s ψ_α` is a linear functional
  on `JetRing ⊗[ℂ] V`: it sends the jet `f` to its Taylor coefficient
  `∂_s| f_α`.
- In other words, the symbols are the coordinate functions on the space of
  jets.
- When `V` is a complex vector space, the physicist also writes conjugate
  symbols `d_s ψ̄_α`, e.g. in the mass term `ψ̄ ψ`.
- These are genuinely new: a polynomial in the `d_s ψ_α` alone depends
  holomorphically on the field, and real terms like `ψ̄ ψ` are not
  holomorphic.
- The symbol `d_s ψ̄_α` sends the jet `f` to the complex conjugate of
  `∂_s| f_α`; it is conjugate-linear in `f`, i.e. a linear functional on
  the conjugate space of `JetRing ⊗[ℂ] V`.
- The physicists' practice of treating `ψ` and `ψ̄` as independent
  variables is exactly this: conjugation is not complex-linear, so the
  conjugate symbols cannot be built from the `d_s ψ_α` and enter as
  independent coordinate functions.
- We define the jet component space `JetComponentSpace` to be the span of
  the symbols `d_s ψ_α` and `d_s ψ̄_α` together; they form a basis, indexed
  by the pairs `(s, α)` with a bar/no-bar tag.
- This span is smaller than the full dual of `JetRing ⊗[ℂ] V`, which also
  contains non-local functionals — e.g. evaluation of the field at a point
  other than `x₀` — depending on infinitely many derivatives at once;
  locality is precisely the restriction to the span of the symbols.
- Formally, `JetComponentSpace = (DerivAlgebra ⊗[ℂ] Module.Dual ℂ V) ×
  (DerivAlgebra ⊗[ℂ] Module.Dual ℂ (ConjModule V))`, where `DerivAlgebra`
  is the span of the functionals `∂_s|` on `JetRing`, and the second factor
  is dropped when `V` is real (its conjugate is then not independent).
- The lagrangian — a polynomial in the symbols — is then an element of the
  symmetric (for bosons) or exterior (for fermions) algebra over
  `JetComponentSpace`.

### The group action on the symbols

- Let a group act on fields by `f ↦ ρ(U) f`.
- Because the symbols are functions of the field, their transformation is
  not extra data — it is inherited: the transformed symbol is the symbol
  evaluated on the transformed field.
- Evaluating on the transformed field gives
  `ψ_α(ρ(U) f) = ∑_β ρ(U)_{α β} ψ_β(f)` — exactly the physicists'
  substitution rule, now derived rather than postulated.
- As an operation on symbols this is precomposition, `φ ↦ φ ∘ ρ(U)`, which
  composes in reverse order: acting with `U` then `V` yields `ρ(U V)`, not
  `ρ(V U)` — a right action.
- A `Representation` is a left action, so one inverse must be inserted:
  `U · φ := φ ∘ ρ(U)⁻¹`.
- This inverse is the familiar one in `φ'(x) = φ(Λ⁻¹ x)` for a scalar
  field: a function transforms with the inverse of the transformation of
  its argument.
- The symbols therefore transform in the dual (contragredient)
  representation, opposite to the field itself.
- The conjugate symbols inherit their transformation the same way:
  `ψ̄_α(ρ(U) f) = ∑_β conj(ρ(U)_{α β}) ψ̄_β(f)` — the physicists' rule
  `ψ̄ ↦ ψ̄ U†` for a unitary representation.
- Invariance is unaffected: a lagrangian is invariant under all `U` if and
  only if it is invariant under all `U⁻¹`, so both conventions single out
  exactly the same invariant lagrangians.

## Jet gauge group

- Let`JetGaugeGroup` be a (matrix) jet gauge group

### The jet Lie algebra

- Let `JetLieAlgebra` be the Lie algebra of `JetGaugeGroup`.
- Let `κ : Type` be the indexing set of a basis `T_a` of `JetLieAlgebra`.
- We let `f : κ → κ → κ → ℂ` be the structure constants of the Lie algebra
    with respect to the basis `T_a`, so that:
    `[T_a, T_b] = i ∑_c f^c_{a b} · T_c`
- An element `X : JetLieAlgebra` has components `X^a : JetRing` with respect to the
    basis `T_a`.
- There is a derivative `∂ : Fin 1 ⊕ Fin 3 → JetLieAlgebra → JetLieAlgebra`, acting
    componentwise: `(∂_μ X)^a = ∂_μ (X^a)`.
- Each `∂_μ` is a derivation of the bracket: `∂_μ [X, Y] = [∂_μ X, Y] + [X, ∂_μ Y]`.
- Taylor coefficients act componentwise too: `∂_s| X` is the constant Lie algebra
    element with components `∂_s|(X^a) : ℂ`.

### Maurer-Cartan form

- There is a map `ω : JetGaugeGroup → (Fin 1 ⊕ Fin 3) → JetLieAlgebra`
  defined by `ω_μ(U) := i (∂_μ U) U†`. This mp is called the Maurer-Cartan form.
- We let `ω^a_μ(U)` for `a : κ` denote the component of `ω` with respect to the `a`th
    basis element.
- The adjoint action is the action of`JetGaugeGroup` on `JetLieAlgebra` by conjugation.
- We denote the components of this action as `Ad(U)^a_b` for `U : JetGaugeGroup`.
- The Maurer–Cartan form is a twisted cocycle: for `U V : JetGaugeGroup`,

    `ω_μ(U * V) = ω_μ(U) + U ω_μ(V) U†`.
- In components this reads as:
  `ω^a_μ(U * V) = ω^a_μ(U) + ∑_b Ad(U)^a_b ω^b_μ(V)`.
- Two consequences: `ω_μ(1) = 0`, and `ω_μ(U⁻¹) = − Ad(U⁻¹) ω_μ(U)`.
- The Maurer–Cartan form satisfies the structure equation: for any `U`,

    `∂_μ ω^a_ν(U) − ∂_ν ω^a_μ(U) = ∑_{b c} f^a_{b c} · ω^b_μ(U) · ω^c_ν(U)`

- Define `sym(∂_s| ω^a_μ(U)) := (1/(|s|+1)) ∑_{ν ∈ s+μ} ∂_{(s+μ)−ν}| ω^a_ν(U)`.
- We have that:
  `∂_s| ω^a_μ − sym(∂_s| ω^a_μ) ∈ ℂ-span{ ∂_{s'}|(∂_ν ω^a_λ − ∂_λ ω^a_ν) : s' + ν + λ = s + μ }`.

### Pure jet subgroup

- For `U : JetGaugeGroup` we write `U₀` for its base-point value, viewed as a
  constant jet.
- Let `PureJetGaugeGroup ⊆ JetGaugeGroup` be the subgroup of `U` with `U₀ = 1`.
- Every `U` factors uniquely as `U = (U U₀⁻¹) · U₀` with `U U₀⁻¹ : PureJetGaugeGroup`.
- Hence `JetGaugeGroup = PureJetGaugeGroup ⋊ G`, with `G` the subgroup of constant
  jets.

- By the structure equation and the multiplication rule, each spanning element equals
  `∑_{b c} f^a_{b c} ∑_{p + q = s'} C(s', p) · ∂_p| ω^b_ν · ∂_q| ω^c_λ`,
  in which every factor has order `≤ |s'| = |s| − 1`.
- Hence, by induction on order: for each `(s, μ, a)` there is a polynomial `P^a_{s μ}`
  over `ℂ`, in commuting variables `X^b_{r ν}` indexed by multisets `r` with `|r| ≤ |s|`,
  such that for every pure jet `U`:

    `∂_s| ω^a_μ(U) = P^a_{s μ}[ X^b_{r ν} := sym(∂_r| ω^b_ν(U)) ]`

- The point is that `P^a_{s μ}` does not depend on `U`: the same polynomial works for
  every pure jet.
- The recursion defining `P^a_{s μ}`: start from `X^a_{s μ}`, add the span-decomposition
  correction with each antisymmetrized pair replaced via the structure equation, and
  substitute lower-order `P`'s for the `∂_p| ω` factors that appear.
- A pure jet is recovered from its Maurer–Cartan form by the coefficient recursion
  `∂_{s+μ}| U = −i ∑_{p + q = s} C(s, p) ∂_p| ω_μ(U) · ∂_q| U`, with `∂_0| U = 1`.
- Injectivity: two pure jets with the same symmetric parts have the same `ω` (previous
  induction), hence the same recursion, hence are equal.
- Surjectivity: given a symmetric family, define the coefficients of `ω` order by
  order — symmetric parts as prescribed, the complement by the structure equation —
  and then define `U` by the recursion; the structure equation is exactly the
  consistency condition making both recursions well-defined.
- Note `sym(∂_s| ω^a_μ(U))` depends only on the combined multiset `r := s + μ`,
  so the symmetric data of `U` is a function of `(a, r)` with `r` nonempty.
- Define

    `symMC : PureJetGaugeGroup → κ → { r : Multiset (Fin 1 ⊕ Fin 3) // r ≠ 0 } → ℂ`

    `symMC U a r := (1/|r|) ∑_{ν ∈ r} ∂_{r − ν}| ω^a_ν(U)`

- Total symmetry is automatic: the codomain is indexed by the multiset `r`, so there
  is no symmetry side-condition to impose.
- Lemma (freeness): `Function.Bijective symMC`.
- Remark: this is the `sym(d_s A)` argument with the roles reversed — for `ω` the
  "field strength" vanishes identically (the structure equation), so nothing survives
  except the symmetric parts.

### Jet representations

- We define a representation of `JetGaugeGroup` as the following data:
  - a homomorphism `jρ : JetGaugeGroup → Matrix ι ι JetRing`
  - A map `dρ : κ → Matrix ι ι ℂ` such that:
    - `[dρ_a, dρ_b] = i ∑_c f^c_{a b} · dρ_c`.
    - Equivariance: `∂_0| jρ(U) · dρ_a · ∂_0| jρ(U)⁻¹ = ∑_b Ad(U₀⁻¹)^a_b · dρ_b`
  such that
  - `∂_μ jρ(U) = -i ∑_a ω^a_μ(U) · dρ_a · ∂_0| jρ(U)`
- We will denote a Jet representation as `jρ`, dropping the `dρ` dat for notational
  ease.
- The general derivatives of `jρ(U)` are then given by:
  `∂_{s + μ}|(jρ(U)) = -i ∑_{p + q = s} C(s, p) ∑_a ∂_p|(ω^a_μ(U)) · dρ_a · ∂_q|(jρ(U))`
- We let `ρ₀(U) := ∂_0|(jρ(U))`
## The algebra

- Let `B` be an algebra over `ℂ`.
- Let `JetGaugeGroup` act on `B` via algebra homomorphisms
- We write `U · x` for the action of `U : JetGaugeGroup` and `x : B`.

## Gauge bosons

- We say collection `A : Fin 1 ⊕ Fin 3 → κ → B` is a collection of gauge bosons
  if they transform as:
  -  `U · (d_s A^a_μ) = ∑_{p + q = s} C(s, p) ∑_b ∂_p|(Ad(U)_{a b}) · d_q A^b_μ + ∂_s(ω^a_μ(U)) · 1`

## Transforms under a rep

- We say a collection `ψ : ι → B` transforms under `jρ` if
  `U · (d_s ψ_i) = ∑_{p + q = s} C(s, p) ∑_j ∂_p|(jρ(U)_{i j}) · d_q ψ_j`
  which can be seen as the expansion of `d_s (∑_j jρ(U)_{i j} · ψ_j)`.
- In terms of `dρ` this is equivalent to: the base case

    `U · ψ_i = ∑_j ρ₀(U)_{i j} · ψ_j`

  together with the recursion

    `U · (d_{s + μ} ψ_i) = d_μ (U · (d_s ψ_i)) − i ∑_{p + q = s} C(s, p) ∑_a ∂_p|(ω^a_μ(U)) ∑_j (dρ_a)_{i j} · (U · (d_q ψ_j))`

  which determines the transformation of each derivative from those of lower order,
  with the admixture governed only by the Maurer–Cartan jets and `dρ`.
- At `s = 0` the recursion reads

    `U · (d_μ ψ_i) = d_μ (U · ψ_i) − i ∑_a ∂_0|(ω^a_μ(U)) ∑_j (dρ_a)_{i j} · (U · ψ_j)`

  i.e. the action fails to commute with `d_μ` exactly by the `dρ`-admixture at the
  base-point Maurer–Cartan coefficient.

## The covariant derivative

- For a representation `jρ` based on the indexing set `ι` we define the covariant
  derivative as a map `𝒟 : Fin 1 ⊕ Fin 3 → (ι → B) → (ι → B)` such that
  `(𝒟_μ ψ)_i = d_μ ψ_i + i ∑_a ∑_j (dρ_a)_{i j} · A^a_μ · ψ_j`.
- We and iterate `𝒟` to define the covariant tower
  `𝒟_l ψ` for lists `l`.

### The transformation of covariant dervatives

- Theorem: if `ψ` transforms under `jρ` then `𝒟_μ ψ` transforms under `jρ`.

### The unitriangularity of covariant derivatives

- Write `⟨A⟩ := adjoin({ d_p A^a_μ })` for the subalgebra of `B` generated by the
  gauge bosons and their derivatives.
- For `S ⊆ B`, the `⟨A⟩`-span of `S` is the left `⟨A⟩`-submodule
  `{ ∑_k P_k · x_k : P_k ∈ ⟨A⟩, x_k ∈ S }`.
- Lemma (unitriangularity): for every list `l`,

    `𝒟_s ψ_i − d_l ψ_i ∈ ⟨A⟩-span of { d_q ψ_j : |q| < |l|, j : ι }`

  i.e. the covariant derivative equals the ordinary one plus `⟨A⟩`-combinations of
  strictly lower-order derivatives.
- This is the whole content; the useful consequences follow by induction on order:
  - For every `n`, the families `{ d_q ψ_j : |q| ≤ n }` and `{ 𝒟_q ψ_j : |q| ≤ n }`
    span the same left `⟨A⟩`-module — the change of generators is invertible and
    triangular.
  - Hence for every `n`:

      `adjoin( ⟨A⟩ ∪ { d_q ψ_j : |q| ≤ n } ) = adjoin( ⟨A⟩ ∪ { 𝒟_q ψ_j : |q| ≤ n } )`

    and taking the union over all `n`, the two towers generate the same subalgebra of
    `B` relative to the connection.

## Field strengths

- We define the field strengths `F : κ → (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → B` as follows:
  `F^a_{μν} = d_μ A^a_ν − d_ν A^a_μ − ∑_{b c} f^a_{b c} · A^b_μ · A^c_ν`
- They transform with under to the (jet version) of the adjoint-representation.
- We thus have the covariant tower `𝒟_q F^a_{μν}`.

## Symmetrized indices of adjoints

- Define the symmetrized index
  `sym(d_s A^a_μ) := (1/(|s|+1)) ∑_{ν ∈ s+μ} d_{(s+μ)−ν} A^a_ν`
- Note that `d_s A^a_μ − sym(d_s A^a_μ) = (1/(|s|+1)) ∑_{ν ∈ s+μ} (d_s A^a_μ − d_{(s+μ)−ν} A^a_ν)`,
  and each summand is a pair of terms differing only in which index carries the `A`:
  moving the `A`-index from `ν` to `μ` gives `d_{s'}(d_ν A^a_μ − d_μ A^a_ν)` with
  `s' = (s + μ) − ν − μ`.
- Then
  `d_s A^a_μ − sym(d_s A^a_μ) ∈ ℂ-span{ d_{s'}(d_ν A^a_λ − d_λ A^a_ν) : s' + ν + λ = s + μ }`
- But we have:
  `d_{s'}(d_ν A^a_λ − d_λ A^a_ν) = d_{s'} F^a_{νλ} + ∑_{b c} f^a_{b c} · d_{s'}(A^b_ν · A^c_λ)`
- By the multiplication rule the last term expands as
  `d_{s'}(A^b_ν · A^c_λ) = ∑_{p + q = s'} C(s', p) · d_p A^b_ν · d_q A^c_λ`
  in which every factor has order `≤ |s'| = |s| − 1`.
- So:
  `d_{s'}(d_ν A^a_λ − d_λ A^a_ν) − d_{s'} F^a_{νλ} ∈ adjoin({ d_p A^b_ν : |p| < |s| })`.
- Since `F` transforms in the adjoint, the unitriangularity lemma applies to it:
  `d_{s'} F^a_{νλ} − 𝒟_{s'} F^a_{νλ} ∈ ⟨A⟩-span{ d_q F^a_{νλ} : |q| < |s'| }`
  and (inspecting the coefficients produced by iterating `𝒟`) everything on the
  right lies in `adjoin({ d_p A : |p| < |s| })`.
- Chaining the three memberships:
  `d_s A^a_μ ∈ ℂ-span{ sym(d_s A^a_μ) } + ℂ-span{ 𝒟_{s'} F^a_{νλ} : |s'| = |s| − 1 } + adjoin({ d_p A : |p| < |s| })`.
- By induction on order (base case: `A^a_μ = sym(A^a_μ)`):
  `adjoin({ d_p A : |p| ≤ n }) = adjoin({ sym(d_p A) : |p| ≤ n } ∪ { 𝒟_q F : |q| < n })`.

## Pure jets and the free action

- Let `N ⊆ JetGaugeGroup` be the subgroup of pure jets: those `U` with `U₀ = 1`.
- Every `U` factors as `U = (U U₀⁻¹) · U₀` with `U U₀⁻¹ ∈ N`, so
  `JetGaugeGroup = N ⋊ G` with `G` the constant jets.
- If an element of `B` transforms only through `U₀` — e.g. the covariant towers
  `𝒟_q ψ` and `𝒟_q F` — then `N` acts trivially on it.
- On a symmetric part, `U ∈ N` acts through the gauge boson law (applied to the
  ℂ-linear combination defining `sym`):

    `U · sym(d_s A^a_μ) = sym(d_s A^a_μ) + sym(∂_s| ω^a_μ(U)) + (terms in { d_p A^b_ν : |p| < |s| })`

  i.e. a shift by the symmetrized Maurer–Cartan jet, up to lower order (the
  lower-order terms carry `∂_p|(Ad(U))` coefficients with `p ≠ 0`).
- Lemma (freeness): the map

    `N → { totally symmetric families c^a_{s+μ} } : U ↦ ( sym(∂_s| ω^a_μ(U)) )_{s, μ, a}`

  is a bijection — the symmetrized Maurer–Cartan jets of a pure jet can be
  prescribed freely and independently, order by order.

## Invariants factor through the field strength

- Let `S ⊆ B` be a set of elements each transforming only through `U₀` — e.g. the
  covariant tower `{ 𝒟_q ψ_j }`.
- Theorem:

    `invariants of adjoin({ d_p A^a_μ } ∪ S) under JetGaugeGroup = invariants of adjoin({ 𝒟_q F^a_{μν} } ∪ S) under G`

- Easy direction (⊇): `𝒟_q F` lies in `adjoin({ d_p A } ∪ S)` by construction and
  transforms through `U₀` alone, so a `G`-invariant built from `{ 𝒟_q F } ∪ S` is
  `JetGaugeGroup`-invariant.
- Hard direction (⊆): let `x ∈ adjoin({ d_p A } ∪ S)` be `JetGaugeGroup`-invariant.
- By the change of generators, write `x` as a polynomial in the symmetric parts
  `sym(d_p A)` with coefficients in `adjoin({ 𝒟_q F } ∪ S)`.
- Act with `U ∈ N`: the coefficients are fixed, and each symmetric part is shifted
  by the free constant `sym(∂_p| ω(U))` of the lemma, up to lower-order symmetric
  parts — so work by downward induction on the top order appearing in `x`.
- Invariance under all of `N`, with the shifts freely prescribable, forces `x` to be
  constant in every symmetric variable: substitute the shift and compare
  coefficients — equivalently, evaluate on the "slice" where all symmetric parts are
  set to zero.
- Hence `x ∈ adjoin({ 𝒟_q F } ∪ S)`.
- Finally, by `JetGaugeGroup = N ⋊ G`, the remaining invariance is under the
  constant jets, which act through `U₀` — i.e. `x` is a `G`-invariant of
  `adjoin({ 𝒟_q F } ∪ S)`, completing the equality.


## SU(3)-invariants.
