# Tips for naming and notation

Names should describe conclusions in standard terminology.

## Contents

1. [Name theorems after their conclusion](#name-theorems-after-their-conclusion)
2. [Use standard physics terms](#use-standard-physics-terms)
3. [Match the name to the statement](#match-the-name-to-the-statement)
4. [Use the right namespace](#use-the-right-namespace)
5. [Introduce notation sparingly](#introduce-notation-sparingly)

<a id="name-theorems-after-their-conclusion"></a>

## 1. Name theorems after their conclusion

A theorem name describes its conclusion, read from the conclusion outward, in standard Mathlib terminology; see the [Mathlib naming conventions](https://leanprover-community.github.io/contribute/naming.html) and the conventions referred to in `docs/ReviewChecklist.md` (Level 4). Check the adjacent declarations first: consistency beats a theoretically better name.

<a id="use-standard-physics-terms"></a>

## 2. Use standard physics terms

Physics names should use the standard term from the physics literature (`kineticEnergy`, `lorentzForce`), not an ad hoc abbreviation. Where Mathlib and physics terminology differ, follow the convention of the surrounding Physlib files.

<a id="match-the-name-to-the-statement"></a>

## 3. Match the name to the statement

A name should not advertise a missing converse, uniqueness, or equality, as a lemma named `…_iff` that proves one direction does, or one named `…_eq` that proves only `≤`.

<a id="use-the-right-namespace"></a>

## 4. Use the right namespace

Physlib organizes material in topical namespaces (`ClassicalMechanics`, `Electromagnetism`, `Lorentz`, `Space`, …). A declaration whose first explicit argument has an existing Lean, Mathlib or Physlib type belongs in that type's namespace, so that `x.foo` dot notation works.

<a id="introduce-notation-sparingly"></a>

## 5. Introduce notation sparingly

Introduce notation sparingly and `scoped`, following the precedent and precedence of existing Mathlib and Physlib notation for the same object.
