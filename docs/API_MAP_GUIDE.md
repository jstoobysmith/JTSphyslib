# Writing good API maps

## What is an API map

In Physlib an API map is a human-readable document which discusses the physics
in a given area, and links to the corresponding Lean declarations.

It can be thought of as a `Roadmap`, a `Blueprint`, or as a `Wiki`.

## The file format of an API map

An API map is a `.md` file. This allows it to easily be viewed and edited both in VSCode, and on GitHub.

## Structure

The API map should have the following structure:
- **Title**: A single `# ` heading with the API's name.
- **Abstract**: A single section titled with either `## Abstract` or `## Abstract (Alpha)`.

  The distinction between `## Abstract` and `## Abstract (Alpha)` is that the latter is used for API maps which have not gone under the stringent review process. Similar to the distinction between Physlib and PhyslibAlpha.

  The abstract should be a single paragraph.
- **Content**: A section titled `## Content`. This is a discussion of the concepts in a given area, with references to the corresponding Lean declarations.
- **Content (Alpha)**: A section titled `## Content (Alpha)`. Same as `## Content`, but for API maps which have not gone under the stringent review process. It should extend what is in `## Content`.

  An API map can have both `## Content` and `## Content (Alpha)` sections, or just one.
- **Lean References**: A section titled `## Lean References` linking concepts discussed in the content sections to their corresponding Lean declarations.

## Lean citations

The *Content* explains the API in words, as you would
explain it to a colleague who does not yet know the Lean names; the Lean
declarations are collected at the end, and the prose points at them with
numbered citations — `[1]`, `[2]` — in the manner of a paper's bibliography.
Any part of *Content* which has not yet been formalized in Lean is marked `[planned]`.

## Content first style

A content first style should be taken. For example:
```
A general gauge theory admits an arbitrary Lie group as its structure group. [planned] Its
gauge field takes values in the Lie algebra of that group. [planned] Matter fields carry a
gauge-covariant derivative with a defined transformation law. [planned] The non-abelian field.
```

Not the following (which is a RoadMap style)
```
The general non-abelian theory remains planned. It will allow an arbitrary Lie group as the structure group and define a gauge field valued in its Lie algebra. [planned] It will also define the gauge-covariant derivative on matter fields and its transformation law, along with the Yang–Mills curvature and its covariant transformation. [planned] The Yang–Mills action and its field equations, parallel transport and holonomy, and a formulation of gauge fields as connections on principal bundles are also planned. [planned]
```

## When to write one

Write an `API-map.md` for any API that groups a coherent body of definitions
and results, for example `Time`, `Space`, the Lorentz group, or the quantum
operators. If a directory holds an API worth documenting as a unit, it gets a
map. Requirements that are planned but not yet formalized still belong in the
map, marked `[planned]`, so the map doubles as the API's roadmap.

## File location

One `API-map.md` sits in the top directory of the API it describes:

    Physlib/SpaceAndTime/Time/API-map.md
    Physlib/Relativity/LorentzGroup/API-map.md
    Physlib/QuantumMechanics/HilbertSpaces/SpaceD/API-map.md

The map's own path is the API's directory; the reference entries at the end
then point at the specific `.lean` files under (or near) it.

## Writing a reference entry

Each entry of `## Lean References` is one file and the declarations in it
that the citing requirement is about:

    7. Physlib/SpaceAndTime/Time/Derivatives.lean — `Time.deriv`, `notation ∂ₜ`,
       `deriv_smul`, `deriv_const`

Rules:

- **Numbered from 1, in order**, with no gaps. Every entry must be cited by
  some requirement, and every citation must resolve to an entry.
- **Use the exact repo-relative file path**, ending in `.lean`, followed by an
  em dash and the declarations.
- **Each declaration in backticks**, comma-separated. Use the names as they
  appear in the source (`deriv_smul`, `Time.deriv`, `RigidBody.mass`). An
  entry may be long; wrap it over several lines, indented, as above.
- **Instance types** name a class applied to arguments rather than a single
  declaration: `` `AddCommGroup Time` ``, `` `Module ℝ Time` ``,
  `` `InnerProductSpace ℝ (Space d)` ``. These are fine and expected; write
  the type exactly. (The grep-tier linter cannot verify instance types and
  reports them as needing the Lean environment, rather than passing or failing
  them, so keep them precise.)
- **Typed declarations** may include the signature after a colon, e.g.
  `` `slice : Space d.succ ≃L[ℝ] ℝ × Space d` ``. The name before ` : ` is
  what gets checked, so keep it correct.
- **Notations** are written with the `notation ` prefix, e.g.
  `` `notation ∂ₜ` ``, `` `notation 𝐱` ``. A bare glyph with no spaces (e.g.
  `` `⨯ₑ₃` ``) is also read as a notation.
- One file per entry. Two requirements that touch the same file get two
  entries, each listing the declarations that requirement is about.

## Run the linter before opening a PR

The linter checks the document's shape (the title, the overview, the required
sections and their order), that citations and entries correspond, and, for every entry, that
the file exists and each declaration and notation named is present in it. It
needs no third-party packages.

Run it from the repository root, exactly as CI does:

    python scripts/lint/required/api_map_linter.py --repo .
    python scripts/lint/required/api_map_linter.py --repo . --verbose

A clean run reports every file as `ok` and no `MISSING_FILE` or `MISSING_NAME`
in the summary. `need_Lean_env` counts instance-type claims grep cannot verify,
and `lean_names_in_prose` counts requirement paragraphs still carrying
backticked names; neither is a failure. The linter exits non-zero on any real
failure (a malformed document, a missing section, an uncited or dangling
reference, a missing file, or a named declaration that is not in the file it
points to). Run it until green before opening a PR.

## The generated site index

`lake exe api_map_index` gathers every `API-map.md` into a single YAML data
file, `docs/_data/APIMap.yml`, in the same way `TODO_to_yml` builds
`docs/_data/TODO.yml` for the website's TODO list. The file records each map's
path, module context, title, overview, parents, further reading, requirements
and Lean declarations, with per-map and total completion counts, and the
website repository renders it. Each requirement also keeps a `location` field,
rebuilt from the entries it cites, so consumers that want the plain
`file (names)` form still have it. A plain run prints the YAML to standard
output; passing `mkFile` writes the file.
