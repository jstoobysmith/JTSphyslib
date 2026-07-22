# Physlib wiki (Verso)

This directory generates a static wiki website from Physlib source files,
in the style of a physics wiki: prose from the modules' documentation
comments, interleaved with the (syntax-highlighted, hoverable) Lean code,
with a navigation sidebar, per-page table of contents, search, KaTeX
math, and light/dark themes.

It is a self-contained Lake project that uses
[Verso](https://github.com/leanprover/verso)'s literate-programming site
generator. Pages are rendered **directly from the original `Physlib/`
source files** — there are no per-page files to write and no
post-processing step.

## What is included

[`literate.toml`](./literate.toml) currently targets the **whole
`Physlib` and `PhyslibAlpha` libraries**, so every module (and any new
module you add to them) gets a page automatically on the next build.
`PhyslibAlpha` pages carry an orange "Alpha content — not reviewed to
the same extent" notice, injected by `static/wiki.js`.

To give a page a human-readable title (instead of its module name), add:

```toml
[modules."Physlib.ClassicalMechanics.DampedHarmonicOscillator.Basic"]
title = "The damped harmonic oscillator"
```

To publish only a curated list of pages instead of whole libraries,
replace the `[[targets]] library = ...` entries with one `[[targets]]
module = "..."` entry per page. Modules can also be excluded with
`exclude = ["Physlib.Meta"]` (recursive).

`literate.toml` also supports excluding modules, ordering the sidebar,
choosing a landing page, hiding commands (e.g. `import`/`open` lines),
and more; see the "Literate Programming" chapter of the
[Verso users' guide](https://github.com/leanprover/verso).

## Building and viewing locally

From this `Verso/` directory:

```sh
lake query :wiki
```

The first run is slow (it compiles Verso itself and any Physlib modules
that aren't built yet); afterwards, rebuilds only re-render what changed.
On success the command prints the path of the generated site,
`.lake/build/literate-html`. Serve it locally:

```sh
python3 -m http.server 8000 --directory .lake/build/literate-html
```

and open <http://localhost:8000>.

> Opening `index.html` via `file://` mostly works, but search and some
> hover popups need an HTTP server, so prefer the command above.

## How it works

- `lakefile.lean` requires `verso` and the parent `Physlib` package (as a
  path dependency, sharing the parent's `.lake/packages` so nothing is
  built twice).
- It defines a `wiki` package facet — a copy of Verso's `literateHtml`
  facet, adapted to collect modules from the `Physlib` package while
  reading `literate.toml` from this directory and writing output to
  `Verso/.lake/build/literate-html`.
- For each listed module, Verso extracts code, docstrings, and module
  docstrings to JSON (`verso-literate`), plans the site (`verso-literate-plan`),
  and emits the HTML (`verso-literate-html`).

## Site behaviour (static/wiki.js)

- **Merged structure.** PhyslibAlpha modules are merged into the same
  sidebar tree and landing sections as Physlib; alpha rows carry an "α"
  marker, alpha cards an "Alpha" chip, and alpha pages an orange notice.
- **Math.** `$...$`, `$$...$$`, `\(...\)`, and `\[...\]` in module
  docstrings are rendered client-side with the KaTeX bundle Verso ships.
- **Suggest an edit.** Every prose block has a hover "✎" button that
  opens a modal with the current text; submitting opens a prefilled
  GitHub issue containing the diff between the suggestion and the
  current text. The target repository is the `GITHUB_REPO` constant at
  the top of `static/wiki.js` (currently `leanprover-community/physlib`).
  Diffs too long for a URL are copied to the clipboard instead.

## Styling

- Palette overrides live under `[theme]` in `literate.toml`.
- Finer-grained rules live in [`static/wiki.css`](./static/wiki.css),
  which is linked after Verso's own stylesheet on every page and uses
  Verso's CSS variables so dark mode keeps working.
