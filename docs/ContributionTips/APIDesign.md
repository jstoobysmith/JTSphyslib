# Tips for API design

Expose a minimal public interface with a complete characteristic API.

## Contents

1. [Don't keep compatibility aliases](#dont-keep-compatibility-aliases)
2. [Don't hide general results as private](#dont-hide-general-results-as-private)
3. [Expose what later work needs](#expose-what-later-work-needs)
4. [Give definitions their characteristic API](#give-definitions-their-characteristic-api)
5. [Make bundled definitions extensional](#make-bundled-definitions-extensional)
6. [Add parallel forms only when both sides exist](#add-parallel-forms-only-when-both-sides-exist)
7. [Annotate normal forms](#annotate-normal-forms)

<a id="dont-keep-compatibility-aliases"></a>

## 1. Don't keep compatibility aliases

Design the interface as it should be after your PR. An old name or module path should not survive solely for compatibility unless the project asks for a deprecation, so remove aliases and wrapper declarations that only preserve an obsolete surface.

<a id="dont-hide-general-results-as-private"></a>

## 2. Don't hide general results as private

A declaration whose statement mentions only Mathlib types, and whose proof does not depend on the subject of its file, is general infrastructure. It belongs, public, in its canonical home, for example under `Physlib/Mathematics/` or in the relevant `Space` file. Generality is a reason to relocate and export, never a reason to hide: `private` is for a step genuinely specific to the surrounding argument.

<a id="expose-what-later-work-needs"></a>

## 3. Expose what later work needs

Expose what later developments need, and genuinely reusable general results. Keep an implementation helper `private` when it has no use outside the proof or file it serves. Don't expose definition bodies to make up for missing lemmas; add the missing lemma instead.

<a id="give-definitions-their-characteristic-api"></a>

## 4. Give definitions their characteristic API

A definition needs the API that characterizes it: introduction and elimination, the `*_def` and `mem_*_iff` restatements, its interaction with the operations in scope, and the universal property where there is one. For a physical quantity this includes how it behaves under the operations physicists apply to it, such as linearity, symmetries, Lorentz or rotation covariance, and units. Try using your new API without unfolding, and add any characteristic lemmas you find missing.

<a id="make-bundled-definitions-extensional"></a>

## 5. Make bundled definitions extensional

A bundled definition should expose no data its laws leave unconstrained. If a structure field or indexed family is left free on inputs that no operation or law uses, two terms that agree everywhere meaningful can still differ, so no `@[ext]` lemma holds and equality reasoning is blocked for every consumer. Constrain or drop the free data.

<a id="add-parallel-forms-only-when-both-sides-exist"></a>

## 6. Add parallel forms only when both sides exist

Add symmetric, dual, or parallel forms of a result only when the file already develops both sides.

<a id="annotate-normal-forms"></a>

## 7. Annotate normal forms

Tag normal-form lemmas `@[simp]`, and `@[grind]` where the surrounding files use `grind`. Make sure no annotation loops or fires wrongly.
