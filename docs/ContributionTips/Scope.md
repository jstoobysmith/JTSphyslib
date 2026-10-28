# Tips for scope

A PR should add a single coherent concept.

## Contents

1. [One concept per PR](#one-concept-per-pr)
2. [Drop the periphery](#drop-the-periphery)
3. [Land large work in stages](#land-large-work-in-stages)
4. [Say what the concept is](#say-what-the-concept-is)
5. [When refactors and moves are fine](#when-refactors-and-moves-are-fine)

<a id="one-concept-per-pr"></a>

## 1. One concept per PR

`AGENTS.md` asks that a PR add a **single coherent concept**: every definition and lemma should either *be* that concept or supply the minimal API to state and prove it. Avoid bundling an opportunistic refactor of prerequisite material with new work, or several unrelated results at once. If your PR covers more than one topic, split it, and decide which declarations go in which part and in what order the parts should land.

<a id="drop-the-periphery"></a>

## 2. Drop the periphery

Declarations that neither are the concept nor are needed to state or prove it are periphery. Drop them, or move them to a follow-up PR.

<a id="land-large-work-in-stages"></a>

## 3. Land large work in stages

`docs/ReviewGuidelines.md` asks that a PR be concise, and gives rule-of-thumb PR lengths. If your PR is well beyond them, plan the stages in which it could land.

<a id="say-what-the-concept-is"></a>

## 4. Say what the concept is

The PR description should say what the concept is. A one-line statement of it is often enough.

<a id="when-refactors-and-moves-are-fine"></a>

## 5. When refactors and moves are fine

A single refactor that is itself the topic of the PR is fine, as are the file moves that correct placement calls for alongside new material. A refactor of already-merged code needs no fresh justification of its content.
