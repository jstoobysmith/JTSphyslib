# Tips for placement and imports

A reader should be able to find each result from the file structure alone.

## Contents

1. [Find the canonical home](#find-the-canonical-home)
2. [Write ForMathlib material as for Mathlib](#write-formathlib-material-as-for-mathlib)
3. [Match the lemma to the file](#match-the-lemma-to-the-file)
4. [Name and place new files well](#name-and-place-new-files-well)
5. [Move rather than make private](#move-rather-than-make-private)
6. [Import new files](#import-new-files)
7. [Keep imports specific](#keep-imports-specific)

<a id="find-the-canonical-home"></a>

## 1. Find the canonical home

Each declaration belongs in the file whose topic, level, and dependencies fit it, near the definition or result it elaborates. `AGENTS.md` asks you to place results in the appropriate existing file and not to create new files without good reason: for example, a general result about derivatives on space needed for a classical mechanics proof belongs in `Space.Derivatives.Basic`, not in the classical mechanics file. If a declaration depends on no later theory and is broadly useful, move it to an earlier file, in `Physlib/Mathematics/`, `Physlib/SpaceAndTime/`, or the general file of its subject.

<a id="write-formathlib-material-as-for-mathlib"></a>

## 2. Write ForMathlib material as for Mathlib

Material in `Physlib/Mathematics/ForMathlib/` should be stated as it would be in Mathlib, and import only from within that directory.

<a id="match-the-lemma-to-the-file"></a>

## 3. Match the lemma to the file

Don't make a specialized lemma look reusable by putting it in a generic file, or hide a general lemma in a specialized one.

<a id="name-and-place-new-files-well"></a>

## 4. Name and place new files well

New files should join an existing topic subdirectory when one fits, and their names should let a reader guess their content.

<a id="move-rather-than-make-private"></a>

## 5. Move rather than make private

`private` is not a substitute for correct placement. If a declaration is in the wrong home, move it.

<a id="import-new-files"></a>

## 6. Import new files

New files need to be imported into `Physlib.lean`, `QuantumInfo.lean` or `PhyslibAlpha.lean`. CI checks this for you.

<a id="keep-imports-specific"></a>

## 7. Keep imports specific

Remove unused imports, and import specific modules rather than all of `Mathlib`. You don't need a direct import for something already available transitively.
