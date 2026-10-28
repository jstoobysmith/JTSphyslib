# Tips for correctness

A green proof can still state the wrong theorem.

## Contents

1. [Try to break your own statements](#try-to-break-your-own-statements)
2. [Check the statement says what you mean](#check-the-statement-says-what-you-mean)
3. [Keep the content out of the hypotheses](#keep-the-content-out-of-the-hypotheses)
4. [Avoid vacuous statements](#avoid-vacuous-statements)
5. [No placeholders](#no-placeholders)
6. [Exercise new predicates](#exercise-new-predicates)
7. [Avoid over-strong assumptions](#avoid-over-strong-assumptions)
8. [Build missing prerequisites first](#build-missing-prerequisites-first)

<a id="try-to-break-your-own-statements"></a>

## 1. Try to break your own statements

The kernel checks your proofs, and CI checks for `sorry` and axioms, but neither tells you whether a definition captures the intended mathematical or physical object, or whether a theorem states the intended result. Before opening a PR, try to show that each of your definitions and statements is wrong, vacuous, or weaker than it claims. Be confident in it only once you have tried and failed.

<a id="check-the-statement-says-what-you-mean"></a>

## 2. Check the statement says what you mean

Make sure the statement matches the mathematics and the physics. Check the quantifiers, the direction of implications, the objects, the units and sign conventions, and the edge cases: empty, zero, degenerate, massless, the trivial metric, a vanishing field.

<a id="keep-the-content-out-of-the-hypotheses"></a>

## 3. Keep the content out of the hypotheses

A statement whose hypotheses are too weak for the claim, or whose real content has been moved into its assumptions, does not prove what it appears to. Check whether a new structure turns downstream theorems into assumptions rather than consequences, and never use a hypothesis that assumes the conclusion or trivially entails it (`AGENTS.md`).

<a id="avoid-vacuous-statements"></a>

## 4. Avoid vacuous statements

Watch out for a statement that holds trivially, a definition defeq to `True` or to its own restatement, an existential of the form `∃ x, ..., True`, or a "definition" that relocates the difficulty instead of discharging it. Simple is not the same as vacuous: a simple correct lemma is perfectly faithful.

<a id="no-placeholders"></a>

## 5. No placeholders

Don't use `True` or any other trivial stand-in in a signature or as the type of a structure field. This includes a field with a plausible physical name that is really an assumption.

<a id="exercise-new-predicates"></a>

## 6. Exercise new predicates

If you add a new `Prop`-valued definition, class or hypothesis structure, give it either a theorem that consumes it or a nontrivial witness: a concrete instance where it holds non-degenerately. Until one exists, in your PR or already on `master`, nobody can check that the predicate is faithful.

<a id="avoid-over-strong-assumptions"></a>

## 7. Avoid over-strong assumptions

Typeclass and structural assumptions that are stronger than needed quietly narrow your claim. Make sure each one is genuinely required.

<a id="build-missing-prerequisites-first"></a>

## 8. Build missing prerequisites first

If your work needs something that does not exist yet, don't work around it by assuming it, bundling it as a hypothesis, or substituting a weaker stand-in. Build the real prerequisite first, as its own PR.
