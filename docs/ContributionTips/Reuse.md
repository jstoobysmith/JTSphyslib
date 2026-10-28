# Tips for reuse

Don't duplicate material from Mathlib or Physlib, whether directly or via thin wrappers.

## Contents

1. [Search before you define](#search-before-you-define)
2. [Search for the steps of your proofs](#search-for-the-steps-of-your-proofs)
3. [Use library combinators](#use-library-combinators)
4. [Look for near-clones in Physlib](#look-for-near-clones-in-physlib)
5. [Avoid duplication within your PR](#avoid-duplication-within-your-pr)
6. [Physics restatements can earn their place](#physics-restatements-can-earn-their-place)

<a id="search-before-you-define"></a>

## 1. Search before you define

For each new declaration, search Mathlib (under `.lake/packages/mathlib`), `Physlib/`, `QuantumInfo/` and `PhyslibAlpha/` for an existing one with the same content. It may have a different name than you expect, or match yours up to renaming, definitional unfolding, symmetry or duality, or via an existing bridging lemma. `AGENTS.md` also asks you not to add lemmas that are trivial rewrites of existing Mathlib or Physlib results, unless they add genuine physics context.

<a id="search-for-the-steps-of-your-proofs"></a>

## 2. Search for the steps of your proofs

For each proof more than a few lines long, search for the goal and for its key intermediate steps. Standard plumbing, such as image and preimage computations, `Finset` sums, `Fin` case bashes, and inner-product and norm manipulations, almost always has a named lemma. Keep searching until you find it or are confident it is absent.

<a id="use-library-combinators"></a>

## 3. Use library combinators

If you are assembling a definition from raw pieces, check whether a library combinator already does the assembly.

<a id="look-for-near-clones-in-physlib"></a>

## 4. Look for near-clones in Physlib

Grep Physlib for the distinctive identifiers or proof shape of each new block of code. You may find near-clones that could be factored into a shared construction.

<a id="avoid-duplication-within-your-pr"></a>

## 5. Avoid duplication within your PR

Look out for private lemmas restating public ones up to defeq, composite lemmas that their component `@[simp]` lemmas already prove, and `∧`-bundles of existing lemmas. If your PR has overlapping public and private APIs, merge them.

<a id="physics-restatements-can-earn-their-place"></a>

## 6. Physics restatements can earn their place

Not every overlap is duplication. A restatement that adds genuine physics context, such as a physically named special case that readers will look for, is welcome. Mathlib itself keeps per-type restatements of generic lemmas, and a specialization with genuine consumers can earn its place.
