# Tips for documentation

Linters check that documentation is present; make sure it is also useful and honest.

## Contents

1. [Write a full module docstring](#write-a-full-module-docstring)
2. [Document definitions and important results](#document-definitions-and-important-results)
3. [Explain the why, not the process](#explain-the-why-not-the-process)
4. [Don't overclaim](#dont-overclaim)

<a id="write-a-full-module-docstring"></a>

## 1. Write a full module docstring

Each new file opens with a module docstring in the Physlib format (`AGENTS.md`): a title, a one-line summary, `## i. Overview`, `## ii. Key results`, `## iii. Table of contents`, `## iv. References`, then numbered sections. See `Physlib/ClassicalMechanics/HarmonicOscillator/Basic.lean` for an example. The overview should explain what the file is about and why, the key results should list the results a reader will look for, and the table of contents should match the sections. When you add to an existing file, update these sections too.

<a id="document-definitions-and-important-results"></a>

## 2. Document definitions and important results

Every definition has a docstring, and important lemmas should have one; every `theorem` (reserved for results well known in the physics literature) must have one. Docstrings describe the object or result, not the proof. For physics, a short informal statement in standard notation, with the usual symbols (e.g. `F = m a`), helps readers recognize it.

<a id="explain-the-why-not-the-process"></a>

## 3. Explain the why, not the process

The "why" is mathematical and physical: what this material is for, what it feeds, and what a reader needs to use it. Narrative about the PR process does not belong in a docstring.

<a id="dont-overclaim"></a>

## 4. Don't overclaim

A docstring should not promise more than the statement delivers, even when the theorem is correct. Keep documentation accurate and up to date, and adapt any documentation you copy.
