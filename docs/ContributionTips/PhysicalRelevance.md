# Tips for physical relevance

Physlib is a library of physics: a correct theorem about a well-formed definition can still fail to say anything a physicist would recognize or use.

## Contents

1. [Define physical objects](#define-physical-objects)
2. [State results a physicist would use](#state-results-a-physicist-would-use)
3. [Use physically meaningful hypotheses](#use-physically-meaningful-hypotheses)
4. [Stick to mainstream physics](#stick-to-mainstream-physics)
5. [Give supporting mathematics a physics use](#give-supporting-mathematics-a-physics-use)
6. [Make the physics visible](#make-the-physics-visible)

<a id="define-physical-objects"></a>

## 1. Define physical objects

New definitions should correspond to recognized physical concepts or quantities: a field, an observable, a state, an energy, a symmetry, a conserved current. A definition with no physical counterpart, and which is not needed for one, is worth questioning. `docs/ReviewChecklist.md` (Level 1) asks: is the content physics, and is it mainstream physics?

<a id="state-results-a-physicist-would-use"></a>

## 2. State results a physicist would use

Aim for results a physicist would recognize: a law, an identity, a conservation law, a limit, a standard textbook result, a property of a model. A mathematical fact with no stated bearing on the physics is much less useful here. Where a physically relevant special case exists, consider stating it as a corollary.

<a id="use-physically-meaningful-hypotheses"></a>

## 3. Use physically meaningful hypotheses

Assumptions should correspond to physical conditions, such as positivity of mass or temperature, a bounded potential, a timelike vector, or a closed system. Avoid artificial conditions added only to make a proof go through, and conditions that exclude the physically interesting cases, for example a result about oscillators that excludes every frequency of interest, or about fields that holds only when they vanish. Where you can, replace an artificial hypothesis by its physical counterpart.

<a id="stick-to-mainstream-physics"></a>

## 4. Stick to mainstream physics

Material should be part of established physics, with a standard reference such as a textbook, a review or a well-known paper. If you formalize a speculative or idiosyncratic model, state clearly where it comes from.

<a id="give-supporting-mathematics-a-physics-use"></a>

## 5. Give supporting mathematics a physics use

Material in `Physlib/Mathematics/`, `Physlib/SpaceAndTime/` or general API files does not need to be physics itself, but its physics use should be clear: a consumer in the PR or on `master`, or a stated physics application. If some material has no physics connection, explain where it is needed or move it to a more appropriate library.

<a id="make-the-physics-visible"></a>

## 6. Make the physics visible

Help the reader see the physics: put the informal physical statement, in standard notation, in the docstring, add a reference, and consider an example connecting the abstract result to a familiar system.
