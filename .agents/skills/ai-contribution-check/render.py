#!/usr/bin/env python3
"""
Helpers for the `ai-contribution-check` skill (see SKILL.md next to this file).

The passes of a check, one per file of contribution tips in `docs/ContributionTips/`, are run
by whatever AI agent the person running the skill uses; this script does the deterministic
parts, so that the report has the same format whatever the agent or model:

    tips      list the tip files, one `<name> <path>` per line, in the order they are shown
    extract   pull the JSON object that follows the one-time marker out of a pass's raw
              output, validate it against its tip file, and write it as
              <results-dir>/<name>.json
    render    turn <results-dir>/*.json into the Markdown of the report: a PR comment
              (`--pr`, `--sha`) or a report on local changes (`--local`)
    meta      print the hidden meta record of an existing PR comment, read from stdin, as
              JSON (or `null` if the text holds none)

Sample usage:

    $ python3 render.py tips
    $ python3 render.py extract <marker> raw/Naming.txt results/ --tips Naming
    $ python3 render.py render results/ --pr 1206 --sha <head sha> --model "<model>" > comment.md
    $ python3 render.py render results/ --local --model "<model>" > report.md
    $ gh api repos/leanprover-community/physlib/issues/comments/<id> --jq .body | python3 render.py meta

A PR comment starts with the `<!-- physlib-ai-contribution-check -->` marker, by which the skill
finds it again to edit it in place, and holds a `<!-- physlib-ai-contribution-check:meta {...} -->`
record of the head commit, the tip files checked and the scores, by which the skill sees whether
it is current. Only the standard library is used.
"""

import argparse
import datetime
import json
import os
import re
import subprocess
import sys

REPO = "leanprover-community/physlib"
MARKER = "<!-- physlib-ai-contribution-check -->"
META_PREFIX = "<!-- physlib-ai-contribution-check:meta "
META_RE = re.compile(r"<!-- physlib-ai-contribution-check:meta (\{.*?\}) -->", re.DOTALL)

HERE = os.path.dirname(os.path.abspath(__file__))
TIPS_DIR = os.path.normpath(os.path.join(HERE, "..", "..", "..", "docs", "ContributionTips"))
TIPS_PATH = "docs/ContributionTips"

# The order in which tip files are shown; a tip file not listed here comes after these, in
# alphabetical order, so that a new file in `docs/ContributionTips/` is checked automatically.
ORDER = [
    "Basic",
    "Correctness",
    "PhysicalRelevance",
    "Reuse",
    "Scope",
    "Attribution",
    "APIDesign",
    "Generality",
    "Placement",
    "Naming",
    "Documentation",
    "ProofQuality",
]

FINDING_FIELDS = ("file", "line", "tip", "observation", "suggestion", "evidence")

# GitHub refuses comments longer than 65536 characters; leave room for the meta record.
MAX_COMMENT = 60000

DISCLAIMER = ("This check is provided as a guide on how to make your {} as good as possible. "
              "However, the final review decision rests with humans, who may contradict or go "
              "against this check; their decision takes priority.")

ANCHOR_RE = re.compile(r'<a id="([^"]+)"></a>\s*\n\s*## (\d+)\. (.+)')


# ------------------------------------------------------------------------------------------
# Tip files

def tip_names():
    """The names of the tip files (without `.md`), in the order they are shown."""
    names = [f[:-3] for f in os.listdir(TIPS_DIR) if f.endswith(".md")]
    rank = {name: i for i, name in enumerate(ORDER)}
    return sorted(names, key=lambda n: (rank.get(n, len(ORDER)), n))


def load_tips(name):
    """The title of the tip file `name` and its tips, as `{anchor: (number, heading)}`."""
    with open(os.path.join(TIPS_DIR, f"{name}.md"), encoding="utf-8") as fh:
        text = fh.read()
    title = name
    for line in text.splitlines():
        if line.startswith("# "):
            title = line[2:].strip()
            if title.startswith("Tips for "):
                title = title[len("Tips for "):]
                title = title[:1].upper() + title[1:]
            break
    tips = {m.group(1): (int(m.group(2)), m.group(3).strip()) for m in ANCHOR_RE.finditer(text)}
    return title, tips


# ------------------------------------------------------------------------------------------
# Validation

def validate(obj, name, tips):
    """Check a pass's result against the schema of `protocol.md` and the anchors of its tip
    file. Returns a normalised copy, or raises `ValueError` saying what is wrong."""
    if not isinstance(obj, dict):
        raise ValueError("the result is not a JSON object")
    if obj.get("tips", name) != name:
        raise ValueError(f"the result is for tip file {obj.get('tips')!r}, not {name!r}")
    score = obj.get("score")
    if score is not None and (isinstance(score, bool) or not isinstance(score, int)
                              or not 0 <= score <= 5):
        raise ValueError(f"score {score!r} is not an integer from 0 to 5 or null")
    summary = obj.get("summary")
    if not isinstance(summary, str) or not summary.strip():
        raise ValueError("summary is missing")
    findings = obj.get("findings", [])
    if not isinstance(findings, list):
        raise ValueError("findings is not a list")
    out = []
    for i, f in enumerate(findings):
        if not isinstance(f, dict):
            raise ValueError(f"finding {i} is not an object")
        g = {k: f.get(k, "") for k in FINDING_FIELDS}
        try:
            g["line"] = int(g["line"] or 0)
        except (TypeError, ValueError):
            raise ValueError(f"finding {i} has a non-integer line {g['line']!r}")
        for k in ("file", "tip", "observation", "suggestion", "evidence"):
            if not isinstance(g[k], str):
                raise ValueError(f"finding {i} has a non-string {k}")
        if g["tip"] not in tips:
            raise ValueError(f"finding {i} names the tip {g['tip']!r}, which is not an anchor "
                             f"of {name}.md")
        if not g["suggestion"].strip():
            raise ValueError(f"finding {i} has no suggestion")
        out.append(g)
    return {"tips": name, "score": score, "summary": summary.strip(), "findings": out}


def extract(marker, text, name, tips):
    """The validated JSON object following the last occurrence of `marker` in `text`."""
    pos = text.rfind(marker)
    if pos < 0:
        raise ValueError("the marker does not occur in the output")
    rest = text[pos + len(marker):]
    start = rest.find("{")
    if start < 0:
        raise ValueError("no JSON object follows the marker")
    obj, _ = json.JSONDecoder().raw_decode(rest[start:])
    return validate(obj, name, tips)


# ------------------------------------------------------------------------------------------
# Rendering

def neutralise(text):
    """Agent text quotes the change, which is untrusted: make sure it cannot open an HTML
    comment (and so forge our markers) or close the `<details>` blocks it is shown in."""
    text = text.replace("<!--", "&lt;!--").replace("-->", "--&gt;")
    return re.sub(r"</?\s*(details|summary)\b", lambda m: m.group(0).replace("<", "&lt;"),
                  text, flags=re.IGNORECASE)


def flat(text):
    return neutralise(" ".join(text.split()))


def one_line(text):
    """Text for a table cell."""
    return flat(text).replace("|", "\\|")


def score_text(result):
    if result.get("error"):
        return "error"
    if result["score"] is None:
        return "n/a"
    return f"{result['score']}/5"


def tip_url(name, anchor, local):
    """A link to a tip file, or to one tip in it."""
    path = f"{TIPS_PATH}/{name}.md"
    url = path if local else f"https://github.com/{REPO}/blob/master/{path}"
    return f"{url}#{anchor}" if anchor else url


def location(f, sha, local):
    if not f["file"]:
        return "Whole change" if local else "PR-wide"
    label = f["file"] + (f":{f['line']}" if f["line"] > 0 else "")
    if local:
        return f"`{label}`"
    url = f"https://github.com/{REPO}/blob/{sha}/{f['file']}"
    if f["line"] > 0:
        url += f"#L{f['line']}"
    return f"[`{label}`]({url})"


def render_result(result, sha, local):
    name = result["tips"]
    title, tips = load_tips(name)
    lines = [f"<details><summary><b>{title}</b> — {score_text(result)}</summary>", ""]
    if result.get("error"):
        lines.append(f"These tips could not be checked: {neutralise(result['error'])}")
    else:
        lines.append(neutralise(result["summary"]))
        for f in result["findings"]:
            lines.append("")
            obs = flat(f["observation"])
            lines.append(f"- {location(f, sha, local)}: {obs}" if obs
                         else f"- {location(f, sha, local)}")
            lines.append(f"  **Suggestion:** {flat(f['suggestion'])}")
            number, heading = tips[f["tip"]]
            notes = [f"Tip: [{number}. {heading}]({tip_url(name, f['tip'], local)})"]
            if f["evidence"].strip():
                notes.append(f"Evidence: {flat(f['evidence'])}")
            lines.append(f"  <sub>{' · '.join(notes)}</sub>")
    lines += ["", "</details>"]
    return "\n".join(lines)


def tips_revision():
    """The last commit of this repository that changed the skill or the tips, if git knows
    it."""
    try:
        rev = subprocess.run(["git", "log", "-1", "--format=%h", "--", HERE, TIPS_DIR],
                             cwd=HERE, capture_output=True, text=True,
                             check=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        rev = ""
    return rev or "unknown"


def load_results(results_dir, names):
    results = []
    for name in names:
        path = os.path.join(results_dir, f"{name}.json")
        try:
            with open(path, encoding="utf-8") as fh:
                obj = json.load(fh)
            if isinstance(obj, dict) and obj.get("error"):
                results.append({"tips": name, "score": None, "error": str(obj["error"])})
            else:
                results.append(validate(obj, name, load_tips(name)[1]))
        except FileNotFoundError:
            results.append({"tips": name, "score": None, "error": "no result was produced"})
        except (ValueError, json.JSONDecodeError) as e:
            results.append({"tips": name, "score": None, "error": f"invalid result ({e})"})
    return results


def render(results, model, pr=None, sha=None, local=False, date=None, tips_rev=None):
    date = date or datetime.date.today().isoformat()
    model = flat(model)
    tips_rev = tips_rev or tips_revision()
    scores = [r["score"] for r in results if r["score"] is not None]
    mean = f"{sum(scores) / len(scores):.1f}/5" if scores else "n/a"

    if local:
        subject = "local changes" + (f" at `{sha[:7]}`" if sha else "")
        head = [f"## AI contribution check (advisory) — {subject}", ""]
    else:
        head = [MARKER, f"## AI contribution check (advisory) — `{sha[:7]}`", ""]
    head += [
        f"> {DISCLAIMER.format('change' if local else 'PR')}",
        "",
        "| tips | score | summary |",
        "| --- | --- | --- |",
    ]
    for r in results:
        summary = r["error"] if r.get("error") else r["summary"]
        title = load_tips(r["tips"])[0]
        link = f"[{title}]({tip_url(r['tips'], '', local)})"
        head.append(f"| {link} | {score_text(r)} | {one_line(summary)} |")
    head += [
        "",
        f"Mean of the scored tip files: **{mean}** (an indication only; the tip files are not "
        "weighted and the mean is not a threshold).",
        "",
        "### Suggestions by tip file",
        "",
    ]
    note = (f"Checked with {model} on {date}, against the contribution tips in "
            f"`{TIPS_PATH}/` at `{tips_rev}`.")
    if not local:
        note += (" Comment `ai-contribution-check` on its own line to request a new check "
                 "after further changes.")
    foot = ["", "---", f"<sub>{note}</sub>"]
    meta_line = ""
    if not local:
        meta = {
            "pr": pr,
            "sha": sha,
            "date": date,
            "model": model,
            "tips_revision": tips_rev,
            "scores": {r["tips"]: ("error" if r.get("error") else r["score"]) for r in results},
        }
        meta_line = META_PREFIX + json.dumps(meta, separators=(",", ":")) + " -->"

    body = []
    budget = MAX_COMMENT - sum(len(x) + 1 for x in head + foot) - len(meta_line)
    for i, r in enumerate(results):
        block = render_result(r, sha, local)
        if len(block) + 2 > budget:
            left = ", ".join(load_tips(x["tips"])[0] for x in results[i:])
            body.append(f"*The suggestions for {left} are omitted: the comment would exceed "
                        "GitHub's size limit.*")
            break
        body += [block, ""]
        budget -= len(block) + 2
    return "\n".join(head + body + foot + ([meta_line] if meta_line else [])) + "\n"


def read_meta(text):
    m = None
    for m in META_RE.finditer(text):
        pass
    if m is None:
        return None
    return json.loads(m.group(1))


# ------------------------------------------------------------------------------------------
# Command line

def main(argv=None):
    names = tip_names()
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = parser.add_subparsers(dest="command", required=True)

    sub.add_parser("tips", help="list the tip files, in the order they are shown")

    p = sub.add_parser("extract", help="extract and validate a pass's JSON result")
    p.add_argument("marker")
    p.add_argument("raw", help="the raw output of the pass")
    p.add_argument("results_dir")
    p.add_argument("--tips", required=True, choices=names)

    p = sub.add_parser("render", help="render the report from the results")
    p.add_argument("results_dir")
    p.add_argument("--pr", type=int, help="the PR number (for a PR comment)")
    p.add_argument("--sha", help="the full head commit of the change")
    p.add_argument("--local", action="store_true", help="a report on local changes")
    p.add_argument("--model", required=True, help="the model (and agent) that checked")
    p.add_argument("--only", nargs="+", choices=names, metavar="TIPS",
                   help="render only these tip files (default: all)")

    sub.add_parser("meta", help="print the meta record of a comment read from stdin")

    args = parser.parse_args(argv)
    if args.command == "tips":
        for name in names:
            print(name, f"{TIPS_PATH}/{name}.md")
    elif args.command == "extract":
        with open(args.raw, encoding="utf-8") as fh:
            text = fh.read()
        try:
            result = extract(args.marker, text, args.tips, load_tips(args.tips)[1])
        except (ValueError, json.JSONDecodeError) as e:
            print(f"{args.tips}: {e}", file=sys.stderr)
            return 1
        os.makedirs(args.results_dir, exist_ok=True)
        with open(os.path.join(args.results_dir, f"{args.tips}.json"), "w",
                  encoding="utf-8") as fh:
            json.dump(result, fh, indent=2, ensure_ascii=False)
            fh.write("\n")
        print(f"{args.tips}: score {score_text(result)}, {len(result['findings'])} findings")
    elif args.command == "render":
        if args.sha is not None and not re.fullmatch(r"[0-9a-f]{40}", args.sha):
            parser.error("--sha must be a full 40-character commit hash")
        if not args.local and (args.pr is None or args.sha is None):
            parser.error("a PR comment needs --pr and --sha; use --local for local changes")
        if args.local and args.pr is not None:
            parser.error("--local and --pr cannot be combined")
        results = load_results(args.results_dir, args.only or names)
        sys.stdout.write(render(results, args.model, pr=args.pr, sha=args.sha,
                                local=args.local))
    elif args.command == "meta":
        print(json.dumps(read_meta(sys.stdin.read())))
    return 0


if __name__ == "__main__":
    sys.exit(main())
