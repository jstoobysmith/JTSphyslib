# Tips for generality

State material at its natural level.

## Contents

1. [Drop unused and over-strong assumptions](#drop-unused-and-over-strong-assumptions)
2. [Prove the general result first](#prove-the-general-result-first)
3. [Use the weakest hypothesis each step needs](#use-the-weakest-hypothesis-each-step-needs)
4. [Generalize to the natural form, not further](#generalize-to-the-natural-form-not-further)

<a id="drop-unused-and-over-strong-assumptions"></a>

## 1. Drop unused and over-strong assumptions

Remove assumptions that are unused, stronger than standard Mathlib convention, or superseded by a nearby more general theorem.

<a id="prove-the-general-result-first"></a>

## 2. Prove the general result first

Prove the general result first and derive special cases from it, rather than duplicating a proof for a special case you could readily prove in general. `AGENTS.md` asks you to extract the general statement and keep the specialization as a corollary.

<a id="use-the-weakest-hypothesis-each-step-needs"></a>

## 3. Use the weakest hypothesis each step needs

If part of a proof uses only a weaker form of a hypothesis, for example only continuity rather than smoothness, state that part as a lemma under the weaker assumption.

<a id="generalize-to-the-natural-form-not-further"></a>

## 4. Generalize to the natural form, not further

Avoid under-generalization, such as a result stated for `ℝ³` that holds in any dimension, or for a specific metric when any would do. Avoid speculative abstraction too, such as parameters that never specialize to anything in the library.
