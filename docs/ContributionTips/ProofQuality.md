# Tips for proof quality

Proofs should be short, robust and readable.

## Contents

1. [Prefer robust automation](#prefer-robust-automation)
2. [Avoid accidental definitional equality](#avoid-accidental-definitional-equality)
3. [Beware short but brittle proofs](#beware-short-but-brittle-proofs)
4. [Split long proofs](#split-long-proofs)
5. [Remove redundant hypotheses](#remove-redundant-hypotheses)

<a id="prefer-robust-automation"></a>

## 1. Prefer robust automation

Prefer robust automation (`simp`, `fun_prop`, `ring`, `linarith`, `omega`, `grind`) over long chains of named-lemma rewriting, which break on Mathlib renames. A single explicit `simp only` or `rw` step is fine; the brittle chain is not.

<a id="avoid-accidental-definitional-equality"></a>

## 2. Avoid accidental definitional equality

Add a comment to each `change` and `show` saying why the goal cannot be reached otherwise. Prefer a rewrite to `rfl` or `convert` where one is available, and don't rely on accidental definitional equality across wrappers or coercions; prove an explicit lemma instead.

<a id="beware-short-but-brittle-proofs"></a>

## 3. Beware short but brittle proofs

Terse is not the same as robust: a `simpa` that closes a non-obvious goal through unfolding-heavy context is fragile.

<a id="split-long-proofs"></a>

## 4. Split long proofs

Proofs should generally be under 50 lines. Following the "Proof structure" section of `AGENTS.md`, split a long proof:

- *by meaning*: further properties of existing definitions, `have`/`calc` steps with physics content or general mathematical value (an algebraic identity, an inequality, a differentiability side-goal), a general statement then instantiated, a part that uses only a weaker hypothesis, or a `let`/`set` object that deserves to be a `def` with lemmas;
- *by structure*: substantial `rcases`/`match` branches, the base case and step of a long induction, a long `calc` block, or a symmetric half that follows by symmetry.

When a long proof cannot be split, add comments explaining its structure.

<a id="remove-redundant-hypotheses"></a>

## 5. Remove redundant hypotheses

Remove redundant hypotheses, and any `revert` the rest of the proof does not need.
