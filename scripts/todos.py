#!/usr/bin/env python3
"""
todos.py -- list the TODOs this branch introduces, relative to its merge-base.

Scans two git refs with the same matcher and subtracts the sets, so the output
is "what this PR adds", not "every TODO in Physlib". Reads blobs straight out
of the object store: no checkout, no branch switching, working tree untouched.

  python scripts/todos.py                          # to the terminal
  python scripts/todos.py --md todos.md
  python scripts/todos.py --head origin/my-branch
"""

import argparse
import re
import subprocess
import sys
import textwrap

DEFAULT_HEAD = "HEAD"
DEFAULT_MASTER = "upstream/master"
DEFAULT_ROOT = "Physlib"

# Physlib/Meta/TODO/ implements the TODO command; it is *about* todos and would
# otherwise dominate the output. scripts/ likewise. QuantumInfo/ is a separate
# subproject with its own `--TODO` convention and is out of scope.
EXCLUDE = re.compile(r"(^|/)(Meta|scripts)/")

CMD_START = re.compile(r'^\s*TODO\s+"')          # TODO "..."  (Lean command)
DOC_LINE = re.compile(r"^\s*/-!\s*TODO:\s*")     # /-! TODO: ... -/
LOOSE = re.compile(r"todo", re.I)

# Matches `todo` but is not a work item: section headings, and identifiers that
# merely contain the word.
NOISE = re.compile(
    r"(^\s*#{1,6}\s*TODO\b)"          # '## TODO' section heading
    r"|(Physlib\.Meta\.TODO)"
    r"|(TODO_to_yml|FullTODO|todoExtension|todoInfo|allTODO)"
    # Prose *about* todos, mostly in module docstrings, not work items.
    r"|(collecting TODO items)|(contains only TODO items)"
    r"|(is a TODO to)|(Open TODO items)|(see the `TODO`)",
    re.I,
)


def git(repo, *args):
    out = subprocess.run(["git", "-C", repo, *args], capture_output=True, check=True)
    return out.stdout.decode("utf-8", "replace")


def list_files(repo, ref, root):
    paths = git(repo, "ls-tree", "-r", "--name-only", ref, "--", root).splitlines()
    return [p for p in paths if p.endswith(".lean") and not EXCLUDE.search(p)]


def read_blobs(repo, ref, paths):
    """Bulk-read many blobs in one subprocess. Returns {path: text}."""
    proc = subprocess.Popen(
        ["git", "-C", repo, "cat-file", "--batch"],
        stdin=subprocess.PIPE, stdout=subprocess.PIPE,
    )
    out, _ = proc.communicate("".join(f"{ref}:{p}\n" for p in paths).encode())

    blobs, pos = {}, 0
    for path in paths:
        nl = out.find(b"\n", pos)
        if nl == -1:
            break
        header = out[pos:nl].decode("utf-8", "replace")
        pos = nl + 1
        if header.endswith(("missing", "ambiguous")):
            continue
        size = int(header.rsplit(" ", 1)[1])
        blobs[path] = out[pos:pos + size].decode("utf-8", "replace")
        pos += size + 1  # trailing newline after the blob
    return blobs


def parse_file(path, text):
    """Yield (path, line, kind, content) items, coalescing wrapped ones."""
    lines = text.splitlines()
    items, unclassified = [], []
    i = 0
    while i < len(lines):
        line = lines[i]

        # --- TODO "..." command; the string may span several lines -----------
        if CMD_START.match(line):
            start = i
            body = line[line.index('"') + 1:]
            while '"' not in body.replace('\\"', ""):
                i += 1
                if i >= len(lines):
                    break
                body += " " + lines[i].strip()
            if '"' in body:
                body = body[:body.rindex('"')]
            items.append((path, start + 1, "cmd", " ".join(body.split())))
            i += 1
            continue

        # --- /-! TODO: ... -/ runs; capitalised first word starts a new item --
        if DOC_LINE.match(line):
            start = i
            body = DOC_LINE.sub("", line).replace("-/", "").strip()
            while i + 1 < len(lines) and DOC_LINE.match(lines[i + 1]):
                nxt = DOC_LINE.sub("", lines[i + 1]).replace("-/", "").strip()
                first = nxt.split(" ", 1)[0] if nxt else ""
                if first[:1].isupper():   # heuristic: new sentence, new item
                    break
                body += " " + nxt
                i += 1
            items.append((path, start + 1, "doc", " ".join(body.split())))
            i += 1
            continue

        if LOOSE.search(line) and not NOISE.search(line):
            unclassified.append((path, i + 1, "?", line.strip()))
        i += 1

    return items, unclassified


def scan(repo, ref, root):
    paths = list_files(repo, ref, root)
    items, unknown = [], []
    for path, text in read_blobs(repo, ref, paths).items():
        a, b = parse_file(path, text)
        items += a
        unknown += b
    return items, unknown, len(paths)


def key(content):
    """Identity of a TODO: its text, path-independent so moves aren't churn."""
    return " ".join(content.lower().split()).rstrip(".")


def group_by_dir(items):
    by_dir = {}
    for path, line, _, content in sorted(items):
        by_dir.setdefault(path.rsplit("/", 1)[0], []).append((path, line, content))
    return by_dir


def emit_terminal(items, unknown, meta, plain):
    print("# TODOs introduced by this branch")
    print(f"# base {meta['base'][:8]} -> head {meta['head'][:8]}  ({meta['date']})")
    print(f"# {meta['files']} files - {len(items)} new\n")

    for directory, group in sorted(group_by_dir(items).items()):
        if plain:
            for path, _, content in group:
                print(f"{path} | {content}")
            continue
        print(directory.replace("Physlib/", ""))
        for path, line, content in group:
            name = path.rsplit("/", 1)[1]
            head, *rest = textwrap.wrap(content, 62) or [""]
            label = f"{name}:{line}"
            print(f"  {label:<34} {head}")
            for cont in rest:
                print(f"  {'':<34} {cont}")
        print()

    if unknown:
        print(f"UNCLASSIFIED ({len(unknown)}) - matched /todo/i, no known form:")
        for path, line, _, content in sorted(unknown):
            print(f"  {path}:{line}  {content[:70]}")


def md_escape(text):
    """Brackets would terminate the link text early."""
    return text.replace("[", "\\[").replace("]", "\\]")


def emit_md(items, meta, repo_url, link_ref):
    out = [
        "# TODOs introduced by this branch",
        "",
        f"{len(items)} open &middot; as of `{meta['head'][:8]}` ({meta['date']})",
        "",
        "> Regenerate with `python scripts/todos.py --md todos.md` after adding or",
        "> resolving a TODO, and commit it in the same commit.",
        "",
    ]
    for directory, group in sorted(group_by_dir(items).items()):
        out += [f"### `{directory.replace('Physlib/', '')}`", ""]
        for path, line, content in group:
            name = path.rsplit("/", 1)[1]
            link = f"{repo_url}/blob/{link_ref}/{path}#L{line}"
            out.append(f"- {md_escape(content)} &nbsp;[`{name}:{line}`]({link})")
        out.append("")

    return "\n".join(out)


def main():
    # Lean sources are full of ℂ, ℝ, ψ; the Windows console defaults to cp1252.
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")

    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=".")
    ap.add_argument("--head", default=DEFAULT_HEAD)
    ap.add_argument("--base", default=None, help="defaults to merge-base with master")
    ap.add_argument("--master", default=DEFAULT_MASTER)
    ap.add_argument("--root", default=DEFAULT_ROOT)
    ap.add_argument("--plain", action="store_true", help="no line numbers; diff-friendly")
    ap.add_argument("--md")
    ap.add_argument("--repo-url", default="https://github.com/jstoobysmith/JTSphyslib")
    # Link against the branch, not the head SHA: a SHA in every URL would rewrite
    # every line of todos.md on each push, even when no TODO changed.
    ap.add_argument("--link-ref", default="AddPotentialAlgebra")
    args = ap.parse_args()

    head_sha = git(args.repo, "rev-parse", args.head).strip()
    date = git(args.repo, "log", "-1", "--format=%ad", "--date=short", args.head).strip()
    base = args.base or git(args.repo, "merge-base", args.master, args.head).strip()

    items, unknown, nfiles = scan(args.repo, args.head, args.root)
    base_items, _, _ = scan(args.repo, base, args.root)

    base_keys = {key(c) for *_, c in base_items}
    items = [it for it in items if key(it[3]) not in base_keys]

    meta = {"base": base, "head": head_sha, "date": date, "files": nfiles}

    emit_terminal(items, unknown, meta, args.plain)
    if args.md:
        with open(args.md, "w", encoding="utf-8") as fh:
            fh.write(emit_md(items, meta, args.repo_url, args.link_ref))


if __name__ == "__main__":
    main()
