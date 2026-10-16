#!/usr/bin/env python3
"""Check the structure and source references in Physlib API maps.

An `API-map.md` is a prose document, described in `docs/API_MAP_GUIDE.md`: a
title; a single-paragraph `## Abstract` (or `## Abstract (Alpha)`) with no
citations; a `## Content` and/or a `## Content (Alpha)` section discussing the
physics, with Lean citations `[n]`, `[planned]` markers and literature
citations `{n}` in the prose; a numbered `## Lean References` list of the Lean
declarations the prose cites; and, optionally and directly after it, a numbered
`## References` list of the literature and other API maps the prose cites.
This script checks that the document has that shape, that citations and
references correspond, that links appear only in `## References`, and that
every cited declaration really is in the file it is attributed to.

The declaration check is deliberately a source-presence check. It verifies
named declarations and notation anchors in the Lean file named by a cited
reference. Claims about anonymous instances are reported as requiring a
Lean-environment check, not treated as passes.

No third-party packages are needed; the format is parsed directly.
"""

import argparse
import re
import sys
from pathlib import Path

TITLE = re.compile(r"^#\s+(\S.*)$")
HEADING = re.compile(r"^##\s+(\S.*)$")
SUBHEADING = re.compile(r"^#{3,}\s")
FENCE = re.compile(r"^\s*(```|~~~)")
REFERENCE_ENTRY = re.compile(r"^(\d+)\.\s+(\S+\.lean)\s*(?:[—-]\s*(.*))?$")
LITERATURE_ENTRY = re.compile(r"^(\d+)\.\s+(\S.*)$")
CITATION = re.compile(r"\[(\d+|planned)\]")
LITERATURE_CITATION = re.compile(r"\{(\d+)\}")
# A run of adjacent citations; literature citations may sit inside the run.
CITATION_RUN = re.compile(r"(?:(?:\[(?:\d+|planned)\]|\{\d+\})\s*)+")
GROUPED_CITATION = re.compile(r"\[\d+\s*,[\d\s,]*\]|\{\d+\s*,[\d\s,]*\}")
MARKDOWN_LINK = re.compile(r"\[[^\]]*\]\([^)]*\)")
RAW_LINK = re.compile(r"https?://|www\.")
MAP_PATH = re.compile(r"\S+/API-map\.md")
BACKTICKED = re.compile(r"`([^`]+)`")
IDENTIFIER = re.compile(r"^[A-Za-z_À-ɏͰ-Ͽ℀-⅏][\w'.À-ɏͰ-Ͽ℀-⅏]*$")

ABSTRACT_SECTIONS = ["Abstract", "Abstract (Alpha)"]
CONTENT_SECTIONS = ["Content", "Content (Alpha)"]
REFERENCES_SECTION = "Lean References"
LITERATURE_SECTION = "References"
# The rank of each section in the required order.
SECTION_ORDER = {
    "Abstract": 0, "Abstract (Alpha)": 0,
    "Content": 1, "Content (Alpha)": 2,
    REFERENCES_SECTION: 3, LITERATURE_SECTION: 4,
}
NO_DECLARATIONS = "*None yet.*"

COUNT_KEYS = ["claims", "done", "planned", "checked", "names_ok", "missing_file",
              "missing_name", "need_lean", "lean_in_prose"]


def split_sections(text):
    """The `# ` titles, the lines before the first section, and the `##`
    sections in order. Headings inside fenced code blocks are ignored."""
    titles, preamble, sections, current = [], [], [], None
    fenced = False
    for line in text.split("\n"):
        if FENCE.match(line):
            fenced = not fenced
        if not fenced:
            heading = HEADING.match(line)
            if heading is not None:
                current = (heading.group(1).strip(), [])
                sections.append(current)
                continue
            title = TITLE.match(line)
            if title is not None:
                titles.append(title.group(1).strip())
                continue
        (preamble if current is None else current[1]).append(line)
    return titles, preamble, sections


def paragraphs(lines):
    """Blank-line-separated paragraphs, each folded onto one line. Subheadings
    (`###` and deeper) close a paragraph and are not paragraphs themselves."""
    out, current = [], []
    for line in lines:
        if line.strip() == "" or SUBHEADING.match(line):
            if current:
                out.append(" ".join(current))
                current = []
        else:
            current.append(line.strip())
    if current:
        out.append(" ".join(current))
    return out


def citation_runs(paragraph):
    """Each run of adjacent Lean citations in a paragraph, as (numbers,
    planned). A run made only of literature citations is not a claim."""
    runs = []
    for run in CITATION_RUN.finditer(paragraph):
        groups = CITATION.findall(run.group(0))
        if groups:
            numbers = [int(group) for group in groups if group != "planned"]
            runs.append((numbers, "planned" in groups))
    return runs


def parse_literature(lines):
    """The numbered `## References` entries, as (number, text)."""
    entries, problems = [], []
    for line in logical_entries(lines):
        matched = LITERATURE_ENTRY.match(line)
        if matched is None:
            problems.append(f"LITERATURE: unreadable entry: {line!r}")
            continue
        entries.append((int(matched.group(1)), matched.group(2)))
    return entries, problems


def check_numbering(label, numbers):
    """Problems with the numbering of a reference list: it must run 1..n."""
    problems = []
    for number in set(numbers):
        if numbers.count(number) > 1:
            problems.append(f"{label}: duplicate entry [{number}]")
    for position, number in enumerate(numbers, start=1):
        if number != position:
            problems.append(f"{label}: entry [{number}] is in position {position}")
            break
    return problems


def logical_entries(lines):
    """The reference lines, with wrapped continuations folded back on."""
    folded = []
    for line in lines:
        line = line.strip()
        if line == "" or line == NO_DECLARATIONS:
            continue
        if folded and not re.match(r"^\d+\.\s", line):
            folded[-1] = folded[-1] + " " + line
        else:
            folded.append(line)
    return folded


def parse_references(lines):
    """The numbered Lean-reference entries, as (number, file, [claims])."""
    entries, problems = [], []
    for line in logical_entries(lines):
        matched = REFERENCE_ENTRY.match(line)
        if matched is None:
            problems.append(f"REFERENCES: unreadable entry: {line!r}")
            continue
        claims = BACKTICKED.findall(matched.group(3) or "")
        entries.append((int(matched.group(1)), matched.group(2), claims))
    return entries, problems


def classify_claim(claim):
    claim = claim.strip()
    if claim.startswith("notation "):
        return "notation", claim[len("notation "):].strip()
    if " : " in claim:
        return "name", claim.split(" : ", 1)[0].strip()
    if IDENTIFIER.match(claim):
        return "name", claim
    if " " not in claim:
        return "notation", claim
    return "instance", claim


def claim_is_present(source, kind, token):
    if kind == "notation":
        fragments = [part for part in re.split(r"[·⬝\s]", token) if part]
        return all(fragment in source for fragment in fragments)
    if token in source:
        return True
    return re.search(r"\b" + re.escape(token.split(".")[-1]) + r"\b", source) is not None


def check_structure(titles, preamble, sections):
    """Problems with the shape of the document."""
    problems = []
    if not titles:
        problems.append("STRUCTURE: no `# Title` heading")
    elif len(titles) > 1:
        problems.append("STRUCTURE: more than one `# ` heading")
    if any(line.strip() for line in preamble):
        problems.append(
            "STRUCTURE: text between the title and the first section; "
            "it belongs in `## Abstract`")
    names = [name for name, _ in sections]
    for name in names:
        if name not in SECTION_ORDER:
            problems.append(f"STRUCTURE: unknown section `## {name}`")
    for name in set(names):
        if names.count(name) > 1:
            problems.append(f"STRUCTURE: section `## {name}` appears more than once")
    abstracts = [name for name in names if name in ABSTRACT_SECTIONS]
    if not abstracts:
        problems.append("STRUCTURE: missing section `## Abstract` (or `## Abstract (Alpha)`)")
    elif len(abstracts) > 1:
        problems.append("STRUCTURE: only one of `## Abstract` and `## Abstract (Alpha)` is allowed")
    if not any(name in CONTENT_SECTIONS for name in names):
        problems.append("STRUCTURE: missing section `## Content` (or `## Content (Alpha)`)")
    if REFERENCES_SECTION not in names:
        problems.append(f"STRUCTURE: missing section `## {REFERENCES_SECTION}`")
    ranks = [SECTION_ORDER[name] for name in names if name in SECTION_ORDER]
    if ranks != sorted(ranks):
        problems.append(
            "STRUCTURE: sections must come in the order `## Abstract`, `## Content`, "
            f"`## Content (Alpha)`, `## {REFERENCES_SECTION}`, `## {LITERATURE_SECTION}`")
    for name, content in sections:
        if name in ABSTRACT_SECTIONS:
            count = len(paragraphs(content))
            if count != 1:
                problems.append(
                    f"STRUCTURE: `## {name}` must be a single paragraph (found {count})")
            for paragraph in paragraphs(content):
                if CITATION.search(paragraph) or LITERATURE_CITATION.search(paragraph):
                    problems.append(f"STRUCTURE: `## {name}` must not contain citations")
        elif name in CONTENT_SECTIONS and not paragraphs(content):
            problems.append(f"STRUCTURE: `## {name}` is empty")
        if name in ABSTRACT_SECTIONS + CONTENT_SECTIONS:
            for paragraph in paragraphs(content):
                for link in MARKDOWN_LINK.findall(paragraph):
                    problems.append(
                        f"LINK: `## {name}` contains the markdown link {link!r}; "
                        "cite it as `{n}` from `## References`")
                if RAW_LINK.search(MARKDOWN_LINK.sub("", paragraph)):
                    problems.append(
                        f"LINK: `## {name}` contains a raw link; "
                        "cite it as `{n}` from `## References`")
                for grouped in GROUPED_CITATION.findall(paragraph):
                    problems.append(
                        f"CITATION: {grouped!r} in `## {name}`; give each citation its own "
                        "bracket, e.g. `[1][2]` or `{1}{2}`")
    return problems


def lint_map(path, repository):
    """Returns (errors, notes, counts). Errors fail the run; notes are shown
    only with `--verbose`."""
    errors, notes = [], []
    counts = dict.fromkeys(COUNT_KEYS, 0)
    titles, preamble, sections = split_sections(path.read_text(encoding="utf-8"))
    errors.extend(check_structure(titles, preamble, sections))
    body = {name: content for name, content in sections}

    entries, reference_problems = parse_references(body.get(REFERENCES_SECTION, []))
    errors.extend(reference_problems)
    errors.extend(check_numbering("REFERENCES", [number for number, _, _ in entries]))
    by_number = {number: (lean_file, claims) for number, lean_file, claims in entries}

    literature, literature_problems = parse_literature(body.get(LITERATURE_SECTION, []))
    errors.extend(literature_problems)
    errors.extend(check_numbering("LITERATURE", [number for number, _ in literature]))
    literature_numbers = {number for number, _ in literature}
    for number, text in literature:
        for map_path in MAP_PATH.findall(text):
            if not (repository / map_path).is_file():
                errors.append(f"literature{{{number}}} MISSING API MAP: {map_path}")

    cited, cited_literature = set(), set()
    for name in ABSTRACT_SECTIONS + CONTENT_SECTIONS:
        for index, paragraph in enumerate(paragraphs(body.get(name, []))):
            where = f"{name}, paragraph {index + 1}"
            for numbers, planned in citation_runs(paragraph):
                counts["claims"] += 1
                counts["planned" if planned else "done"] += 1
                for number in numbers:
                    if number not in by_number:
                        errors.append(f"[{where}] DANGLING CITATION: [{number}]")
                    cited.add(number)
            for number in map(int, LITERATURE_CITATION.findall(paragraph)):
                if number not in literature_numbers:
                    errors.append(f"[{where}] DANGLING LITERATURE CITATION: {{{number}}}")
                cited_literature.add(number)
            if name in CONTENT_SECTIONS and BACKTICKED.search(paragraph):
                counts["lean_in_prose"] += 1
                notes.append(
                    f"[{where}] STYLE: Lean names belong in the references, not the prose")
    for number, _, _ in entries:
        if number not in cited:
            errors.append(f"REFERENCES: entry [{number}] is never cited")
    for number in sorted(literature_numbers - cited_literature):
        errors.append(f"LITERATURE: entry {{{number}}} is never cited")

    for number, relative_file, claims in entries:
        source_path = repository / relative_file
        if not source_path.is_file():
            counts["missing_file"] += 1
            errors.append(f"ref[{number}] MISSING FILE: {relative_file}")
            continue
        counts["checked"] += 1
        source = source_path.read_text(encoding="utf-8", errors="replace")
        if not claims:
            errors.append(f"ref[{number}] NO DECLARATIONS listed for {relative_file}")
        for claim in claims:
            kind, token = classify_claim(claim)
            if kind == "instance":
                counts["need_lean"] += 1
                notes.append(
                    f"ref[{number}] NEEDS LEAN ENVIRONMENT: {claim!r} in {relative_file}")
            elif claim_is_present(source, kind, token):
                counts["names_ok"] += 1
            else:
                counts["missing_name"] += 1
                errors.append(
                    f"ref[{number}] MISSING {kind.upper()}: {token!r} in {relative_file}")
    return errors, notes, counts


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", required=True, type=Path, help="physlib repository root")
    parser.add_argument("--verbose", action="store_true")
    args = parser.parse_args()
    maps = sorted(args.repo.rglob("API-map.md"))
    stale = sorted(args.repo.rglob("API-map.yaml"))
    if not maps:
        sys.exit(f"no API-map.md files under {args.repo}")
    total = dict.fromkeys(COUNT_KEYS, 0)
    failed = False
    for path in maps:
        errors, notes, counts = lint_map(path, args.repo)
        for key, value in counts.items():
            total[key] += value
        failed = failed or bool(errors)
        print(
            f"[{'FAIL' if errors else 'ok'}] {path.relative_to(args.repo)} "
            f"({counts['done']} done, {counts['planned']} planned, "
            f"{counts['names_ok']} names ok, {counts['need_lean']} need-Lean)"
        )
        for problem in errors + (notes if args.verbose else []):
            print(f"  {problem}")
    for path in stale:
        failed = True
        print(f"[FAIL] {path.relative_to(args.repo)}: API maps are now `API-map.md`")
    print("\n=== SUMMARY ===")
    print(
        f"files={len(maps)} claims={total['claims']} done={total['done']} "
        f"planned={total['planned']} files_checked={total['checked']} "
        f"names_ok={total['names_ok']} MISSING_FILE={total['missing_file']} "
        f"MISSING_NAME={total['missing_name']} need_Lean_env={total['need_lean']} "
        f"lean_names_in_prose={total['lean_in_prose']}"
    )
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
