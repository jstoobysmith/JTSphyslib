/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Lean
/-!

# PR summary

A script summarising a pull-request for its reviewers: the files it changes and the declarations
it adds, removes, moves or restates.

## i. Overview

`lake exe pr_summary` prints, as Markdown, a summary of the changes a pull-request makes. It is
meant to be read by a reviewer before they look at the diff, and is posted as part of the comment
the [`PRMessage`](../../.github/workflows/PRMessage.yml) workflow leaves on a new pull-request.

The summary has two parts:

- the files the pull-request adds, removes, renames or modifies, with the number of lines added
  to and removed from each, read from `git diff --name-status` and `git diff --numstat`;
- the declarations it adds, removes, moves or restates, read from `git diff --unified=0`.

The declarations are found textually, in the spirit of the `declarations_diff.sh` script of
`mathlib-ci`: the lines of the diff which begin a declaration are extracted, their attributes and
modifiers are stripped, and their declaration identifiers are paired up between the removed and
the added lines. A name which is both removed and added is reported as *moved* if the two lines
agree and as *restated* otherwise; a name only added is *added*, and a name only removed is
*removed*. Since the search is textual, the summary is a guide and not a proof: in particular

- the keyword and the declaration identifier must be on the same line, so a line break between
  `lemma` and its name hides the declaration;
- a declaration must start at the beginning of its line;
- namespaces are not tracked, so the `foo` of `namespace A` and the `foo` of `namespace B` are
  the same name to the script;
- an `instance` whose name does not immediately follow the keyword (or a `(priority := …)`
  prefix) is treated as anonymous and recorded by its signature;
- a change to the proof of a lemma, or to the body of a definition, is invisible to the script,
  which is what makes the summary short.

Run it from the root of the repository, which needs the revisions it is given:

```
lake exe pr_summary                 -- summarise `origin/master...HEAD`
lake exe pr_summary <base>          -- summarise `<base>...HEAD`
lake exe pr_summary <base> <head>   -- summarise `<base>...<head>`
```

The Markdown goes to standard output and the progress messages to standard error, so
`lake exe pr_summary > summary.md` writes just the summary.

Each file and each declaration of the summary is a link to the line it is on, in whichever of
the two revisions it belongs to, so that a reviewer can read the table and jump straight to the
code. The links always point into `leanprover-community/physlib`, so one made from a commit
which is only in a clone or a fork does not resolve.

The following summarise recent pull-requests to Physlib. Each is given by the commit it was
merged as, which is on `master` and so is in every clone, and each shows a different shape of
change:

```
# The action of spacetime series on derivative symbols (#1776): a new file and two modified
# ones, with nine declarations added and nothing else touched.
lake exe pr_summary c3964f48db4b~1 c3964f48db4b

# The equality case of Robertson's relation (#1774): eleven declarations added to two existing
# files.
lake exe pr_summary 4a602d1c86de~1 4a602d1c86de

# Fix names (#1792): sixteen files renamed and one removed, with twenty-six declarations added
# under their new names, twenty-six removed under their old ones, twenty-seven moved between
# files and five restated.
lake exe pr_summary 0aeb3dc7e249~1 0aeb3dc7e249

# Crystals and unit cells (#1782): fourteen declarations added to three existing files.
lake exe pr_summary 5f2136528e88~1 5f2136528e88

# Remove a hypothesis from `normPowerSeries_tendsto` (#1788): one file, and one declaration
# whose statement changed, which is the smallest summary with anything in it.
lake exe pr_summary be0f21e5002d~1 be0f21e5002d
```

A pull-request which is still open is not in a clone until its head is fetched. For instance
#1793, which renames the tempered distributional electromagnetism API, adds two abbreviations,
removes two and restates nineteen declarations which mention them:

```
git fetch https://github.com/leanprover-community/physlib.git pull/1793/head
lake exe pr_summary c3964f48db4b FETCH_HEAD
```

## ii. Key results

- `PRSummary.parseNameStatus` reads the files changed from `git diff --name-status`.
- `PRSummary.parseNumstat` reads the lines added and removed from `git diff --numstat`.
- `PRSummary.declHeads` reads the declarations a line of source introduces.
- `PRSummary.parseDiff` reads the declaration lines of `git diff --unified=0`.
- `PRSummary.declDiff` pairs the removed declarations with the added ones.
- `PRSummary.Source.link` links a file or a line of either revision into the repository.
- `PRSummary.theoremCallout` calls out the results the pull-request writes with `theorem`.
- `PRSummary.summary` is the Markdown summary of a pull-request.

## iii. Table of contents

- A. Strings, Markdown and links
- B. Changes to files
  - B.1. Parsing `git diff --name-status`
  - B.2. Parsing `git diff --numstat`
  - B.3. The report of the files
- C. Changes to declarations
  - C.1. Normalising a line of source
  - C.2. The declarations a line introduces
  - C.3. The declaration lines of a diff
  - C.4. Pairing the removed and added declarations
  - C.5. The report of the declarations
- D. The summary
  - D.1. Results written with `theorem`
  - D.2. Putting the summary together
- E. Tests
  - E.1. Links
  - E.2. Normalising a line of source
  - E.3. The declarations a line introduces
  - E.4. Parsing `git diff --name-status`
  - E.5. Parsing `git diff --numstat`
  - E.6. The report of the files
  - E.7. The declaration lines of a diff
  - E.8. Pairing the removed and added declarations
  - E.9. The report of the declarations
  - E.10. Results written with `theorem`
  - E.11. The summary
- F. The executable

## iv. References

* The `scripts/pr_summary/declarations_diff.sh` script of
  [`mathlib-ci`](https://github.com/leanprover-community/mathlib-ci), which this script follows
  for the pairing of the removed and added declarations.

-/

namespace PRSummary

/-!

## A. Strings, Markdown and links

-/

/-- `s` without its first `n` characters. -/
def dropChars (s : String) (n : Nat) : String := String.ofList (s.toList.drop n)

/-- `s` without its last `n` characters. -/
def dropEndChars (s : String) (n : Nat) : String :=
  let cs := s.toList
  String.ofList (cs.take (cs.length - n))

/-- `s` without its leading whitespace. -/
def ltrim (s : String) : String := String.ofList (s.toList.dropWhile Char.isWhitespace)

/-- `s` without its trailing whitespace. -/
def rtrim (s : String) : String :=
  String.ofList (s.toList.reverse.dropWhile Char.isWhitespace).reverse

/-- `s` without its leading or trailing whitespace. -/
def trim (s : String) : String := ltrim (rtrim s)

/-- `n` followed by `noun`, pluralised by an `s` unless `n` is one. -/
def plural (n : Nat) (noun : String) : String :=
  if n == 1 then s!"{n} {noun}" else s!"{n} {noun}s"

/-- The counts of `items` which are not zero, each followed by its label, as in
`2 added, 1 removed`. Empty if every count is zero. -/
def tally (items : Array (Nat × String)) : String :=
  ", ".intercalate ((items.filter (·.1 > 0)).map (fun (n, label) => s!"{n} {label}")).toList

/-- The row of a Markdown table with the cells `cells`. -/
def row (cells : List String) : String := "| " ++ " | ".intercalate cells ++ " |"

/-- The header of a Markdown table with the columns `columns`, that is, its heading row
followed by its alignment row. -/
def header (columns : List String) : Array String :=
  #[row columns, row (columns.map fun _ => "-")]

/-- `s` in a Markdown code span, or an em dash if `s` is empty. -/
def code (s : String) : String := if s.isEmpty then "—" else s!"`{s}`"

/-- The first `limit` rows of `rows`, followed by a line saying how many rows were left out.
A pull-request touching hundreds of declarations would otherwise outgrow the comment it is
posted in, which GitHub caps at 65536 characters; a linked row is some 300 of them. -/
def truncate (rows : Array String) (limit : Nat) : Array String :=
  if rows.size ≤ limit then rows
  else rows.take limit ++
    #["", s!"*… and {plural (rows.size - limit) "further row"}, left out to keep this short.*"]

/-- The repository the summary links into. Physlib has one home, so this is not an option of
the executable; a link made from a commit which is only in a clone or a fork does not resolve
there, which is the price of the links always pointing at the project. -/
def repository : String := "leanprover-community/physlib"

/-- The two revisions the summary compares, which are the two a link can point into: a file or
a line of the base revision is linked at `base`, and one of the head revision at `head`, so
that a link to a declaration which is gone still reaches it. -/
structure Source where
  /-- The commit the removed lines belong to. -/
  base : String := ""
  /-- The commit the added lines belong to. -/
  head : String := ""
  deriving Repr, DecidableEq, Inhabited

/-- `text` as a Markdown link to the file `file` of `repository`, at its line `line` unless that
is zero, in the head revision of `src` if `added` and in its base revision otherwise. -/
def Source.link (src : Source) (text file : String) (added : Bool) (line : Nat := 0) : String :=
  let commit := if added then src.head else src.base
  let anchor := if line == 0 then "" else s!"#L{line}"
  s!"[{text}](https://github.com/{repository}/blob/{commit}/{file}{anchor})"

/-!

## B. Changes to files

-/

/-- How a file was changed by a pull-request, as `git diff --name-status` reports it. -/
inductive FileStatus where
  /-- The file is new. -/
  | added
  /-- The file was deleted. -/
  | removed
  /-- The file was changed in place. -/
  | modified
  /-- The file was moved, or renamed, from `oldPath`. -/
  | renamed (oldPath : String)
  /-- The file was copied from `oldPath`. -/
  | copied (oldPath : String)
  deriving Repr, DecidableEq, Inhabited

/-- The place of `status` in the order in which the files are reported. -/
def FileStatus.rank : FileStatus → Nat
  | .added => 0
  | .renamed .. => 1
  | .copied .. => 2
  | .modified => 3
  | .removed => 4

/-- Whether the file is still there at the head revision, which is the revision a link to it
should reach. -/
def FileStatus.atHead : FileStatus → Bool
  | .removed => false
  | _ => true

/-- How `status` is described in the report. -/
def FileStatus.label : FileStatus → String
  | .added => "added"
  | .removed => "removed"
  | .modified => "modified"
  | .renamed oldPath => s!"renamed from `{oldPath}`"
  | .copied oldPath => s!"copied from `{oldPath}`"

/-- A file changed by a pull-request. -/
structure FileChange where
  /-- The path of the file after the change, or, for a removed file, before it. -/
  path : String
  /-- How the file was changed. -/
  status : FileStatus
  /-- The number of lines added to the file, `none` for a binary file. -/
  insertions : Option Nat := none
  /-- The number of lines removed from the file, `none` for a binary file. -/
  deletions : Option Nat := none
  deriving Repr, DecidableEq, Inhabited

/-- The order of the files of the report: by how they were changed, then by path. -/
def FileChange.lt (c d : FileChange) : Bool :=
  c.status.rank < d.status.rank || c.status.rank == d.status.rank && c.path < d.path

/-!

### B.1. Parsing `git diff --name-status`

-/

/-- The file change a line of `git diff --name-status` records, `none` for a line which records
no change to a file. A line is a status letter followed by one path, or, for a rename or a copy,
by the old and the new path, separated by tabs. The status letter of a rename or a copy carries
a similarity score, as in `R100`. -/
def parseNameStatusLine (line : String) : Option FileChange :=
  match (line.splitOn "\t").map trim with
  | [status, path] =>
    match status.toList.head? with
    | some 'A' => some { path, status := .added }
    | some 'D' => some { path, status := .removed }
    -- `M` is a modification, and `T` a change of file type, which we report as one.
    | some 'M' | some 'T' => some { path, status := .modified }
    | _ => none
  | [status, oldPath, path] =>
    match status.toList.head? with
    | some 'R' => some { path, status := .renamed oldPath }
    | some 'C' => some { path, status := .copied oldPath }
    | _ => none
  | _ => none

/-- The files changed, read from the lines of `git diff --name-status`. -/
def parseNameStatus (lines : Array String) : Array FileChange :=
  lines.filterMap parseNameStatusLine

/-!

### B.2. Parsing `git diff --numstat`

-/

/-- The number of lines added to and removed from a file, and its path, as a line of
`git diff --numstat` records them. For a binary file the two counts are given as `-`. -/
def parseNumstatLine (line : String) : Option (String × Option Nat × Option Nat) :=
  match (line.splitOn "\t").map trim with
  | [insertions, deletions, path] => some (path, insertions.toNat?, deletions.toNat?)
  | _ => none

/-- The number of lines added to and removed from each file, read from the lines of
`git diff --numstat`. -/
def parseNumstat (lines : Array String) : Array (String × Option Nat × Option Nat) :=
  lines.filterMap parseNumstatLine

/-- The file changes `changes` with the line counts of `counts` filled in, matching them by
path. The counts are read from a `git diff --numstat --no-renames`, in which a rename appears as
the deletion of the old path and the addition of the new one, so a renamed file is given the
counts of its new path. -/
def withLineCounts (changes : Array FileChange)
    (counts : Array (String × Option Nat × Option Nat)) : Array FileChange :=
  changes.map fun c =>
    match counts.find? (·.1 == c.path) with
    | some (_, insertions, deletions) => { c with insertions, deletions }
    | none => c

/-!

### B.3. The report of the files

-/

/-- The lines added to and removed from a file, as in `+12 -3`, or `binary` for a binary
file. -/
def lineCounts (c : FileChange) : String :=
  match c.insertions, c.deletions with
  | some insertions, some deletions => s!"+{insertions} -{deletions}"
  | _, _ => "binary"

/-- The Markdown report of the files changed: how many were added, renamed, copied, modified and
removed, then a table of one row per file, each linked into `src`. At most `limit` files are
listed. -/
def fileReport (src : Source) (changes : Array FileChange) (limit : Nat := 40) : String :=
  if changes.isEmpty then "This PR changes no files." else
  let changes := changes.qsort FileChange.lt
  let counts := #[(.added, "added"), (.renamed "", "renamed"), (.copied "", "copied"),
    (.modified, "modified"), (.removed, "removed")].map
      fun (status, label) => ((changes.filter (·.status.rank == FileStatus.rank status)).size,
        label)
  let rows := changes.map fun c =>
    row [src.link (code c.path) c.path c.status.atHead, c.status.label, lineCounts c]
  "\n".intercalate (#[s!"**{plural changes.size "file"} changed**: {tally counts}.", ""] ++
    header ["File", "Change", "Lines"] ++ truncate rows limit).toList

/-!

## C. Changes to declarations

-/

/-!

### C.1. Normalising a line of source

-/

/-- The modifiers which may precede a declaration keyword. -/
def modifiers : Array String :=
  #["private", "protected", "public", "noncomputable", "nonrec", "partial", "unsafe", "scoped",
    "local", "mutual"]

/-- The brackets which open a group in which a `:=` is not top-level. -/
def openBrackets : List Char := ['(', '[', '{', '⟨', '⦃']

/-- The brackets which close a group in which a `:=` is not top-level. -/
def closeBrackets : List Char := [')', ']', '}', '⟩', '⦄']

/-- Drops the characters of `cs` up to and including the bracket closing the group which is
`depth` brackets deep, and returns the rest. `none` if the group is not closed in `cs`. -/
def afterCloseBracket (cs : List Char) (depth : Nat) : Option (List Char) :=
  match cs with
  | [] => none
  | c :: rest =>
    if openBrackets.contains c then afterCloseBracket rest (depth + 1)
    else if closeBrackets.contains c then
      if depth ≤ 1 then some rest else afterCloseBracket rest (depth - 1)
    else afterCloseBracket rest depth

/-- `s` without its leading bracketed group, if it starts with one which is closed. -/
def dropBalanced? (s : String) : Option String :=
  match s.toList with
  | c :: rest =>
    if openBrackets.contains c then (afterCloseBracket rest 1).map String.ofList else none
  | [] => none

/-- `s` without its leading attribute block `@[…]`, if it has one. -/
def dropAttribute? (s : String) : Option String :=
  if s.startsWith "@[" then dropBalanced? (dropChars s 1) else none

/-- `s` without its leading modifier, if it starts with one. -/
def dropModifier? (s : String) : Option String :=
  modifiers.findSome? fun m =>
    if s.startsWith (m ++ " ") then some (dropChars s (m.toList.length + 1)) else none

/-- `s` without its leading `open … in` or `set_option … in` prefix, if it has one. -/
def dropScopePrefix? (s : String) : Option String :=
  if s.startsWith "open " || s.startsWith "set_option " then
    match s.splitOn " in " with
    | _ :: rest@(_ :: _) => some (" in ".intercalate rest)
    | _ => none
  else none

/-- `s` with the attributes, modifiers and `open …`/`set_option … in` prefixes which may precede
a declaration keyword removed, and with its trailing whitespace dropped. -/
def normalise (s : String) : String := Id.run do
  let mut s := rtrim s
  -- Every step strictly shortens `s`, so the loop ends well before its bound.
  for _ in [0:s.toList.length] do
    match dropAttribute? s <|> dropModifier? s <|> dropScopePrefix? s with
    | some t => s := ltrim t
    | none => break
  return s

/-!

### C.2. The declarations a line introduces

-/

/-- The keywords which introduce a declaration the summary tracks. `remark`,
`informal_definition` and `informal_lemma` are Physlib's own. -/
def declKeywords : Array String :=
  #["theorem", "lemma", "def", "abbrev", "instance", "structure", "class", "inductive",
    "alias", "opaque", "axiom", "remark", "informal_definition", "informal_lemma"]

/-- The characters which end a declaration identifier. -/
def nameStop : List Char :=
  [' ', '\t', '(', ')', '[', ']', '{', '}', '⟨', '⟩', '⦃', '⦄', ':', '=', ',', '"']

/-- The leading run of characters of `s` which can belong to a declaration identifier. -/
def firstToken (s : String) : String :=
  String.ofList (s.toList.takeWhile fun c => !nameStop.contains c)

/-- Whether `s` can be a declaration identifier, that is, whether it starts with a character
which can start one. Identifiers of Physlib often start outside ASCII, as in `ψ_eq`, and the
characters which could start a signature instead, such as `⟨` or `{`, end a name and so never
start one. -/
def isIdentifier (s : String) : Bool :=
  match s.toList with
  | c :: _ => c.isAlpha || c == '_' || c.val > 127
  | [] => false

/-- The part of `s` which precedes its first `:=` outside any brackets. The brackets matter:
the `:=` of `instance (priority := 100) : Foo` is not the one which opens its body. -/
def beforeAssignment (s : String) : String := Id.run do
  let cs := s.toList
  let mut depth := 0
  let mut out : Array Char := #[]
  for (c, i) in cs.zipIdx do
    if openBrackets.contains c then depth := depth + 1
    else if closeBrackets.contains c then depth := depth - 1
    else if depth == 0 && c == ':' && cs[i + 1]? == some '=' then break
    out := out.push c
  return String.ofList out.toList

/-- The signature of a declaration, given the part of its line which follows its keyword: what
precedes its body, with a trailing `where` dropped. -/
def signature (s : String) : String :=
  let s := rtrim (beforeAssignment s)
  rtrim (if s.endsWith " where" then dropEndChars s 6 else s)

/-- A declaration a line of source introduces. -/
structure DeclHead where
  /-- The keyword the declaration is written with. -/
  keyword : String
  /-- The declaration identifier, or, for an anonymous `instance`, its signature. -/
  name : String
  /-- Whether the declaration is an anonymous `instance`, so that `name` is its signature and
  not an identifier. -/
  anonymous : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- How the declaration is shown in the report: its keyword followed by its identifier, or,
for an anonymous `instance`, by its signature. -/
def DeclHead.display (h : DeclHead) : String := s!"{h.keyword} {h.name}"

/-- The declarations the line `line` of source introduces: none for a line which does not start
one, one for most declarations, and two for `alias ⟨d₁, d₂⟩ := d`. A declaration is only found at
the beginning of a line, after its attributes and modifiers. -/
def declHeads (line : String) : Array DeclHead := Id.run do
  -- A declaration starts at the beginning of its line, so an indented line starts none.
  match line.toList with
  | c :: _ => if c.isWhitespace then return #[]
  | [] => return #[]
  let line := normalise line
  let some keyword := declKeywords.find? fun k => line.startsWith (k ++ " ") | return #[]
  let rest := ltrim (dropChars line (keyword.toList.length + 1))
  -- `class inductive` is two keywords, and the identifier follows the second.
  let (keyword, rest) :=
    if keyword == "class" && rest.startsWith "inductive " then
      ("class inductive", ltrim (dropChars rest 10))
    else (keyword, rest)
  if keyword == "alias" && rest.startsWith "⟨" then
    -- `alias ⟨d₁, d₂⟩ := d` declares `d₁` and `d₂`; a `_` stands for a direction left unnamed.
    let inner := ((dropChars rest 1).splitOn "⟩").headD ""
    return (inner.splitOn ",").toArray.filterMap fun name =>
      let name := trim name
      -- A lone `_` names no declaration.
      if isIdentifier name && name != "_" then some { keyword, name } else none
  -- The name of an `instance` may be preceded by its priority, as in `instance (priority := 100)
  -- foo : Bar`.
  let rest := if keyword == "instance" && rest.startsWith "(priority" then
      ltrim ((dropBalanced? rest).getD rest) else rest
  let name := firstToken rest
  if keyword == "instance" && !isIdentifier name then
    -- An anonymous `instance` has no identifier, so it is recorded by its signature.
    return #[{ keyword, name := signature rest, anonymous := true }]
  if isIdentifier name then return #[{ keyword, name }]
  return #[]

/-!

### C.3. The declaration lines of a diff

-/

/-- Where a line of a `git diff` is. Since a removed line belongs to the base revision of its
file and an added one to the head revision, `added` says which of the two the line number is
in. -/
structure Location where
  /-- The path of the file the line belongs to. -/
  file : String
  /-- The number of the line in that file, counting from one. -/
  line : Nat
  /-- Whether the line was added (`+`) rather than removed (`-`). -/
  added : Bool
  deriving Repr, DecidableEq, Inhabited

/-- A line of a `git diff` which starts a declaration. -/
structure DeclLine where
  /-- Where the line is. -/
  loc : Location
  /-- The declaration the line introduces. -/
  decl : DeclHead
  /-- The text of the line, without its `+` or `-`, used to tell a declaration which moved from
  one which was restated. -/
  text : String
  deriving Repr, DecidableEq, Inhabited

/-- The path a `---` or `+++` line of a `git diff` gives, without its `a/` or `b/` prefix. The
path of a file which did not exist on one side is `/dev/null`, which is left as it is. -/
def diffPath (s : String) : String :=
  let s := trim s
  if s.startsWith "a/" || s.startsWith "b/" then dropChars s 2 else s

/-- The lines at which a hunk of a `git diff` starts in the base and in the head revision of
its file, read from its `@@ -<base>,<n> +<head>,<m> @@` header, where a missing count means one
line. `none` for a line which is not a hunk header. -/
def parseHunkHeader (line : String) : Option (Nat × Nat) :=
  if !line.startsWith "@@ " then none else
  match (line.splitOn " ").drop 1 with
  | base :: head :: _ =>
    -- Each is `-<line>,<count>` or `+<line>,<count>`, with the count left out when it is one.
    match (((dropChars base 1).splitOn ",").head?.bind String.toNat?,
        ((dropChars head 1).splitOn ",").head?.bind String.toNat?) with
    | (some base, some head) => some (base, head)
    | _ => none
  | _ => none

/-- The declaration lines of the output of `git diff --unified=0`, given as its lines. The `---`
and `+++` lines of the header of each file give the file the lines of its hunks belong to, and
the `@@` header of each hunk gives the line its lines start at. A removed line is only a header
outside a hunk: inside one, the removed Lean comment `-- a/Foo` reads as `--- a/Foo`. -/
def parseDiff (lines : Array String) : Array DeclLine := Id.run do
  let mut removedFile := ""
  let mut addedFile := ""
  -- The line the next removed, respectively added, line of the current hunk is at.
  let mut removedLine := 0
  let mut addedLine := 0
  let mut inHunk := false
  let mut result : Array DeclLine := #[]
  for line in lines do
    if line.startsWith "diff --git " then
      inHunk := false
    else if let some (base, head) := parseHunkHeader line then
      inHunk := true
      removedLine := base
      addedLine := head
    -- These two must be tested before `-` and `+`, which they also start with.
    else if !inHunk && line.startsWith "--- " then
      removedFile := diffPath (dropChars line 4)
    else if !inHunk && line.startsWith "+++ " then
      addedFile := diffPath (dropChars line 4)
    else if line.startsWith "+" || line.startsWith "-" then
      let added := line.startsWith "+"
      let text := rtrim (dropChars line 1)
      let loc : Location :=
        { file := if added then addedFile else removedFile
          line := if added then addedLine else removedLine
          added }
      for decl in declHeads text do
        result := result.push { loc, decl, text }
      if added then addedLine := addedLine + 1 else removedLine := removedLine + 1
    else if line.startsWith " " then
      -- A context line, which is only there if the diff was made with context.
      removedLine := removedLine + 1
      addedLine := addedLine + 1
  return result

/-!

### C.4. Pairing the removed and added declarations

-/

/-- How a declaration was changed by a pull-request. -/
inductive DeclChange where
  /-- The declaration is new, at `loc`. -/
  | added (loc : Location)
  /-- Its statement changed; it is now at `loc`. -/
  | restated (loc : Location)
  /-- Its statement is unchanged, but it moved from `old` to `new`, which are in the same file
  if it only moved within it. -/
  | moved (old new : Location)
  /-- The declaration is gone from `loc`. -/
  | removed (loc : Location)
  deriving Repr, DecidableEq, Inhabited

/-- The place of `change` in the order in which the declarations are reported. -/
def DeclChange.rank : DeclChange → Nat
  | .added .. => 0
  | .restated .. => 1
  | .moved .. => 2
  | .removed .. => 3

/-- How `change` is described in the report. -/
def DeclChange.label : DeclChange → String
  | .added .. => "added"
  | .restated .. => "restated"
  | .moved .. => "moved"
  | .removed .. => "removed"

/-- Whether `change` leaves the declaration in the head revision with a statement it did not
have in the base revision, which is what makes it worth checking against the conventions. A
`lemma` which became a `theorem` is restated, not added, so both count. -/
def DeclChange.isNew : DeclChange → Bool
  | .added .. | .restated .. => true
  | .moved .. | .removed .. => false

/-- Where a reviewer should go to read the declaration after `change`: where it now is, or,
for one which is gone, where it was. -/
def DeclChange.target : DeclChange → Location
  | .added loc | .restated loc | .removed loc => loc
  | .moved _ new => new

/-- The file shown for `change`, which for a declaration which moved between two files names
both of them. -/
def DeclChange.file : DeclChange → String
  | .added loc | .restated loc | .removed loc => code loc.file
  | .moved old new =>
    if old.file == new.file then code old.file
    else s!"{code old.file} → {code new.file}"

/-- A declaration changed by a pull-request. -/
structure DeclDiff where
  /-- The declaration. -/
  decl : DeclHead
  /-- How it was changed. -/
  change : DeclChange
  deriving Repr, DecidableEq, Inhabited

/-- The order of the declarations of the report: by how they were changed, then by keyword,
then by name. -/
def DeclDiff.lt (c d : DeclDiff) : Bool :=
  c.change.rank < d.change.rank || c.change.rank == d.change.rank &&
    (c.decl.keyword < d.decl.keyword || c.decl.keyword == d.decl.keyword &&
      c.decl.name < d.decl.name)

/-- The declaration of `d` as a code span, linking into `src` at the line a reviewer should
read it on. -/
def DeclDiff.link (src : Source) (d : DeclDiff) : String :=
  let target := d.change.target
  src.link (code d.decl.display) target.file target.added target.line

/-- The declarations changed by a pull-request, read from the declaration lines of its diff.

The lines are grouped by declaration identifier, without regard for the namespace they are in.
A name which only appears on added lines was added, and one which only appears on removed lines
was removed. A name on both was either moved, if the added and the removed lines agree, or
restated. -/
def declDiff (lines : Array DeclLine) : Array DeclDiff := Id.run do
  -- The names in the order in which they first appear, so that the result does not depend on
  -- the order of a hash map.
  let mut names : Array String := #[]
  for l in lines do
    unless names.contains l.decl.name do names := names.push l.decl.name
  let mut result : Array DeclDiff := #[]
  for name in names do
    let group := lines.filter (·.decl.name == name)
    let added := group.filter (·.loc.added)
    let removed := group.filter (!·.loc.added)
    if removed.isEmpty then
      result := result ++ added.map fun l => { decl := l.decl, change := .added l.loc }
    else if added.isEmpty then
      result := result ++ removed.map fun l => { decl := l.decl, change := .removed l.loc }
    else if (added.map (·.text)).qsort (· < ·) == (removed.map (·.text)).qsort (· < ·) then
      result := result ++ (removed.zip added).map fun (r, a) =>
        { decl := a.decl, change := .moved r.loc a.loc }
    else
      result := result.push { decl := added[0]!.decl, change := .restated added[0]!.loc }
  return result

/-!

### C.5. The report of the declarations

-/

/-- The Markdown report of the declarations changed: how many were added, restated, moved and
removed, then a table of one row per declaration, each linked into `src` at the line it is on.
At most `limit` declarations are listed. -/
def declReport (src : Source) (decls : Array DeclDiff) (limit : Nat := 60) : String :=
  if decls.isEmpty then
    "This PR changes the statement of no declaration."
  else
  let decls := decls.qsort DeclDiff.lt
  let here : Location := default
  let counts := #[(.added here, "added"), (.restated here, "restated"),
    (.moved here here, "moved"), (.removed here, "removed")].map fun (change, label) =>
      ((decls.filter (·.change.rank == DeclChange.rank change)).size, label)
  let rows := decls.map fun d => row [d.link src, d.change.label, d.change.file]
  "\n".intercalate (#[s!"**{plural decls.size "declaration"} changed**: {tally counts}.", ""] ++
    header ["Declaration", "Change", "File"] ++ truncate rows limit).toList

/-!

## D. The summary

-/

/-!

### D.1. Results written with `theorem`

Physlib reserves `theorem` for the results which are significant in the physics literature, and
writes every other result with `lemma`. Each `theorem` must have a doc-string and must be listed,
under the section of its library, in the theorems file; `lake exe theorem_lint` checks both. A
pull-request which writes one is therefore asking the reviewer to agree that the result deserves
it, which is worth saying before the tables.

-/

/-- The file listing the results of each library written with `theorem`. -/
def theoremsFile : String := "scripts/lint/exemptions/Theorems.txt"

/-- The declarations of `decls` which the pull-request writes with `theorem`: those it adds, and
those it restates, since a `lemma` which became a `theorem` is restated and not added. -/
def newTheorems (decls : Array DeclDiff) : Array DeclDiff :=
  decls.filter fun d => d.decl.keyword == "theorem" && d.change.isNew

/-- The call-out about the results the pull-request writes with `theorem`, empty unless it writes
one. It says whether the pull-request also changes the theorems file, since a new `theorem` which
is not listed there fails `lake exe theorem_lint`. -/
def theoremCallout (src : Source) (files : Array FileChange) (decls : Array DeclDiff) : String :=
  let theorems := (newTheorems decls).qsort DeclDiff.lt
  if theorems.isEmpty then "" else
  let names := ", ".intercalate (theorems.map (·.link src)).toList
  let listed := if files.any (·.path == theoremsFile) then "which this PR also changes"
    else "**which this PR does not change**"
  -- Markdown joins the lines of a block quote into one paragraph, so the explanation is wrapped
  -- here rather than left as one very long line.
  "\n".intercalate [
    "> [!IMPORTANT]",
    s!"> This PR writes {plural theorems.size "result"} with `theorem`:",
    s!"> {names}.",
    ">",
    "> `theorem` is reserved for the results which are significant in the physics literature,",
    "> usually known by name; every other result is a `lemma`. Each one needs a doc-string and",
    s!"> a line under the section of its library in `{theoremsFile}`,",
    s!"> {listed}.",
    "> `lake exe theorem_lint` checks both."]

/-!

### D.2. Putting the summary together

-/

/-- What the summary says about how it was made, so that a reviewer knows how far to trust it. -/
def caveat : String :=
  "The declarations are found by reading the diff as text, so this table misses a declaration \
  whose keyword and name are on two lines, and it does not know about namespaces. A change to a \
  proof, or to the body of a definition, does not appear here. See \
  `scripts/github/pr_summary.lean`."

/-- The Markdown summary of the changes a pull-request makes, with the files and declarations
linked into `src`. The call-outs come first, and are left out when there is nothing to call
out. -/
def summary (src : Source) (files : Array FileChange) (decls : Array DeclDiff) : String :=
  let parts := #[theoremCallout src files decls, "### Files", fileReport src files,
    "### Declarations", declReport src decls, caveat]
  "\n\n".intercalate (parts.filter (!·.isEmpty)).toList

/-!

## E. Tests

These tests run when this file is compiled, so `lake exe pr_summary` fails to build if one of
them fails.

-/

/-- The two revisions the tests link into. A real revision is a commit; these stand in for two
so that the expected output stays short. -/
def testSource : Source := { base := "bsha", head := "hsha" }

/-- The report `s` with the `https://github.com/<repository>/blob/` of every link shortened to
`…/`, so that the expected output of a test fits on a line. The links themselves are checked in
E.1, where they are written out. -/
def shortLinks (s : String) : String :=
  "…/".intercalate (s.splitOn s!"https://github.com/{repository}/blob/")

/-! ### E.1. Links -/

/-- info: [`A.lean`](https://github.com/leanprover-community/physlib/blob/hsha/A.lean#L12) -/
#guard_msgs in
#eval IO.println (testSource.link (code "A.lean") "A.lean" true 12)

-- A removed line is linked in the base revision, and a file at no line in particular.
/-- info: [`A.lean`](https://github.com/leanprover-community/physlib/blob/bsha/A.lean) -/
#guard_msgs in
#eval IO.println (testSource.link (code "A.lean") "A.lean" false)

-- The shortening the tests below use leaves everything but the start of the link alone.
/-- info: [`A.lean`](…/hsha/A.lean#L12) -/
#guard_msgs in
#eval IO.println (shortLinks (testSource.link (code "A.lean") "A.lean" true 12))

/-! ### E.2. Normalising a line of source -/

/-- info: "lemma foo : True := trivial" -/
#guard_msgs in
#eval normalise "@[simp] lemma foo : True := trivial"

/-- info: "lemma foo : True := trivial" -/
#guard_msgs in
#eval normalise "@[simp, nolint docBlame] private lemma foo : True := trivial  "

/-- info: "def foo : Nat := 0" -/
#guard_msgs in
#eval normalise "@[simp] noncomputable def foo : Nat := 0"

/-- info: "instance : Foo X := bar" -/
#guard_msgs in
#eval normalise "local instance : Foo X := bar"

/-- info: "lemma foo : True := trivial" -/
#guard_msgs in
#eval normalise "set_option maxHeartbeats 400000 in lemma foo : True := trivial"

/-- info: "lemma foo : True := trivial" -/
#guard_msgs in
#eval normalise "open Finset in lemma foo : True := trivial"

-- An attribute which is not closed on the line is left alone, rather than swallowing the line.
/-- info: "@[simp, nolint" -/
#guard_msgs in
#eval normalise "@[simp, nolint"

/-! ### E.3. The declarations a line introduces -/

/-- Prints the declarations `declHeads` reads from the line `line`. -/
def printHeads (line : String) : IO Unit := IO.println (repr (declHeads line))

/-- info: #[{ keyword := "lemma", name := "foo", anonymous := false }] -/
#guard_msgs in
#eval printHeads "lemma foo : True := trivial"

/-- info: #[{ keyword := "theorem", name := "Foo.bar", anonymous := false }] -/
#guard_msgs in
#eval printHeads "@[simp] protected theorem Foo.bar (x : X) : P x := by simp"

/-- info: #[{ keyword := "def", name := "ψ_eq", anonymous := false }] -/
#guard_msgs in
#eval printHeads "noncomputable def ψ_eq : Nat := 0"

/-- info: #[{ keyword := "structure", name := "Foo", anonymous := false }] -/
#guard_msgs in
#eval printHeads "structure Foo extends Bar where"

/-- info: #[{ keyword := "class inductive", name := "Foo", anonymous := false }] -/
#guard_msgs in
#eval printHeads "class inductive Foo (n : Nat) : Type where"

/-- info: #[{ keyword := "instance", name := "instFoo", anonymous := false }] -/
#guard_msgs in
#eval printHeads "instance instFoo : Foo X := ⟨bar⟩"

-- The priority of an `instance` does not hide its name, and its `:=` does not end its
-- signature.
/-- info: #[{ keyword := "instance", name := "instInhabited", anonymous := false }] -/
#guard_msgs in
#eval printHeads "instance (priority := 100) instInhabited : Inhabited U where"

/-- info: #[{ keyword := "instance", name := ": Foo X", anonymous := true }] -/
#guard_msgs in
#eval printHeads "instance : Foo X := ⟨bar⟩"

/-- info: #[{ keyword := "instance", name := "{A : Type*} [Semigroup A] : IsAlternative A",
  anonymous := true }] -/
#guard_msgs (whitespace := lax) in
#eval printHeads "instance (priority := 100) {A : Type*} [Semigroup A] : IsAlternative A where"

/-- info: #[{ keyword := "alias", name := "foo_of_bar", anonymous := false },
  { keyword := "alias", name := "bar_of_foo", anonymous := false }] -/
#guard_msgs (whitespace := lax) in
#eval printHeads "alias ⟨foo_of_bar, bar_of_foo⟩ := foo_iff_bar"

-- A direction of an `alias` left unnamed declares nothing.
/-- info: #[{ keyword := "alias", name := "foo_of_bar", anonymous := false }] -/
#guard_msgs in
#eval printHeads "alias ⟨foo_of_bar, _⟩ := foo_iff_bar"

/-- info: #[{ keyword := "alias", name := "foo'", anonymous := false }] -/
#guard_msgs in
#eval printHeads "alias foo' := foo"

/-- info: #[{ keyword := "informal_lemma", name := "foo", anonymous := false }] -/
#guard_msgs in
#eval printHeads "informal_lemma foo where"

-- An indented declaration, a line which starts no declaration, and a keyword which is only the
-- start of an identifier are all passed over.
/-- info: #[] -/
#guard_msgs in
#eval printHeads "  lemma foo : True := trivial"

/-- info: #[] -/
#guard_msgs in
#eval printHeads "  exact foo"

/-- info: #[] -/
#guard_msgs in
#eval printHeads "definitely_not_a_declaration"

/-- info: #[] -/
#guard_msgs in
#eval printHeads ""

/-! ### E.4. Parsing `git diff --name-status` -/

/-- Prints the file changes `parseNameStatus` reads from the lines `lines`. -/
def printNameStatus (lines : Array String) : IO Unit :=
  IO.println (repr (parseNameStatus lines))

/--
info: #[{ path := "Physlib/A.lean", status := PRSummary.FileStatus.added,
          insertions := none, deletions := none },
        { path := "Physlib/B.lean", status := PRSummary.FileStatus.modified,
          insertions := none, deletions := none },
        { path := "Physlib/C.lean", status := PRSummary.FileStatus.removed,
          insertions := none, deletions := none },
        { path := "Physlib/E.lean", status := PRSummary.FileStatus.renamed "Physlib/D.lean",
          insertions := none, deletions := none }]
-/
#guard_msgs (whitespace := lax) in
#eval printNameStatus #["A\tPhyslib/A.lean", "M\tPhyslib/B.lean", "D\tPhyslib/C.lean",
  "R098\tPhyslib/D.lean\tPhyslib/E.lean"]

/-- info: #[] -/
#guard_msgs in
#eval printNameStatus #["", "not a status line"]

/-! ### E.5. Parsing `git diff --numstat` -/

/-- info: #[("Physlib/A.lean", some 40, some 0), ("Physlib/B.lean", none, none)] -/
#guard_msgs in
#eval IO.println (repr (parseNumstat #["40\t0\tPhyslib/A.lean", "-\t-\tPhyslib/B.lean"]))

/--
info: #[{ path := "Physlib/A.lean", status := PRSummary.FileStatus.added,
          insertions := some 40, deletions := some 0 }]
-/
#guard_msgs (whitespace := lax) in
#eval IO.println (repr (withLineCounts (parseNameStatus #["A\tPhyslib/A.lean"])
  (parseNumstat #["40\t0\tPhyslib/A.lean"])))

/-! ### E.6. The report of the files -/

-- A file still there at the head revision is linked there, and a removed one in the base
-- revision.
/--
info: **3 files changed**: 1 added, 1 modified, 1 removed.

| File | Change | Lines |
| - | - | - |
| [`A.lean`](…/hsha/A.lean) | added | +40 -0 |
| [`B.lean`](…/hsha/B.lean) | modified | +2 -1 |
| [`C.lean`](…/bsha/C.lean) | removed | +0 -9 |
-/
#guard_msgs in
#eval IO.println (shortLinks (fileReport testSource #[
  { path := "C.lean", status := .removed, insertions := some 0, deletions := some 9 },
  { path := "B.lean", status := .modified, insertions := some 2, deletions := some 1 },
  { path := "A.lean", status := .added, insertions := some 40, deletions := some 0 }]))

-- A binary file has no line counts.
/--
info: **1 file changed**: 1 added.

| File | Change | Lines |
| - | - | - |
| [`A.png`](…/hsha/A.png) | added | binary |
-/
#guard_msgs in
#eval IO.println (shortLinks (fileReport testSource
  #[{ path := "A.png", status := .added }]))

/-- info: This PR changes no files. -/
#guard_msgs in
#eval IO.println (fileReport testSource #[])

-- Only `limit` files are listed, and the rest are counted.
/--
info: **3 files changed**: 3 modified.

| File | Change | Lines |
| - | - | - |
| [`A.lean`](…/hsha/A.lean) | modified | +1 -0 |

*… and 2 further rows, left out to keep this short.*
-/
#guard_msgs in
#eval IO.println (shortLinks (fileReport (limit := 1) testSource #[
  { path := "A.lean", status := .modified, insertions := some 1, deletions := some 0 },
  { path := "B.lean", status := .modified, insertions := some 1, deletions := some 0 },
  { path := "C.lean", status := .modified, insertions := some 1, deletions := some 0 }]))

/-! ### E.7. The declaration lines of a diff -/

/-- info: some (10, 11) -/
#guard_msgs in
#eval parseHunkHeader "@@ -10,0 +11,2 @@"

-- A count left out means one line.
/-- info: some (3, 3) -/
#guard_msgs in
#eval parseHunkHeader "@@ -3 +3 @@ namespace Foo"

/-- info: none -/
#guard_msgs in
#eval parseHunkHeader "+lemma foo : True := trivial"

/-- The lines of a `git diff --unified=0` in which a lemma is added to one file and a definition
is renamed in another. The last hunk removes the Lean comment `-- a/Physlib/Z.lean`, which reads
as a `---` header but must not be taken for one. -/
def exampleDiff : Array String :=
  #["diff --git a/Physlib/A.lean b/Physlib/A.lean",
    "--- a/Physlib/A.lean",
    "+++ b/Physlib/A.lean",
    "@@ -10,0 +11,2 @@",
    "+lemma foo_eq_bar : foo = bar := rfl",
    "+  -- an indented line is not a declaration",
    "diff --git a/Physlib/B.lean b/Physlib/B.lean",
    "--- a/Physlib/B.lean",
    "+++ b/Physlib/B.lean",
    "@@ -3 +3 @@",
    "-def oldName : Nat := 0",
    "+def newName : Nat := 0",
    "@@ -20,2 +20,0 @@",
    "--- a/Physlib/Z.lean",
    "-def afterAComment : Nat := 0"]

/--
info: #[{ loc := { file := "Physlib/A.lean", line := 11, added := true },
          decl := { keyword := "lemma", name := "foo_eq_bar", anonymous := false },
          text := "lemma foo_eq_bar : foo = bar := rfl" },
        { loc := { file := "Physlib/B.lean", line := 3, added := false },
          decl := { keyword := "def", name := "oldName", anonymous := false },
          text := "def oldName : Nat := 0" },
        { loc := { file := "Physlib/B.lean", line := 3, added := true },
          decl := { keyword := "def", name := "newName", anonymous := false },
          text := "def newName : Nat := 0" },
        { loc := { file := "Physlib/B.lean", line := 21, added := false },
          decl := { keyword := "def", name := "afterAComment", anonymous := false },
          text := "def afterAComment : Nat := 0" }]
-/
#guard_msgs (whitespace := lax) in
#eval IO.println (repr (parseDiff exampleDiff))

/-! ### E.8. Pairing the removed and added declarations -/

/-- The declaration line `text` at the line `n` of `file`, added if `added`. -/
def mkLine (file : String) (n : Nat) (added : Bool) (text : String) : DeclLine :=
  { loc := { file, line := n, added }, decl := (declHeads text)[0]!, text }

/-- Prints how `declDiff` says the declarations of the lines `lines` changed. -/
def printDeclDiff (lines : Array DeclLine) : IO Unit := do
  for d in (declDiff lines).qsort DeclDiff.lt do
    IO.println s!"{d.change.label} {d.decl.display} in {d.change.file}"

-- A name which is only added was added, and one which is only removed was removed.
/--
info: added lemma foo in `Physlib/A.lean`
removed def bar in `Physlib/B.lean`
-/
#guard_msgs in
#eval printDeclDiff #[
  mkLine "Physlib/A.lean" 3 true "lemma foo : True := trivial",
  mkLine "Physlib/B.lean" 7 false "def bar : Nat := 0"]

-- The same line removed from one file and added to another is a declaration which moved.
/-- info: moved lemma foo in `Physlib/B.lean` → `Physlib/A.lean` -/
#guard_msgs in
#eval printDeclDiff #[
  mkLine "Physlib/B.lean" 7 false "lemma foo : True := trivial",
  mkLine "Physlib/A.lean" 3 true "lemma foo : True := trivial"]

-- A name removed and added on two different lines was restated.
/-- info: restated lemma foo in `Physlib/A.lean` -/
#guard_msgs in
#eval printDeclDiff #[
  mkLine "Physlib/A.lean" 3 false "lemma foo : True := trivial",
  mkLine "Physlib/A.lean" 3 true "lemma foo (n : Nat) : n = n := rfl"]

-- Gaining an attribute is a restatement, since the attribute is part of the line.
/-- info: restated lemma foo in `Physlib/A.lean` -/
#guard_msgs in
#eval printDeclDiff #[
  mkLine "Physlib/A.lean" 3 false "lemma foo : True := trivial",
  mkLine "Physlib/A.lean" 3 true "@[simp] lemma foo : True := trivial"]

-- A `lemma` which became a `theorem` keeps its name, so it was restated and not replaced.
/-- info: restated theorem foo in `Physlib/A.lean` -/
#guard_msgs in
#eval printDeclDiff #[
  mkLine "Physlib/A.lean" 3 false "lemma foo : True := trivial",
  mkLine "Physlib/A.lean" 3 true "theorem foo : True := trivial"]

-- A declaration which only moved within its file names that file once.
/-- info: moved lemma foo in `Physlib/A.lean` -/
#guard_msgs in
#eval printDeclDiff #[
  mkLine "Physlib/A.lean" 3 false "lemma foo : True := trivial",
  mkLine "Physlib/A.lean" 9 true "lemma foo : True := trivial"]

/-! ### E.9. The report of the declarations -/

-- A declaration is linked at the line it is on: an added one in the head revision, a removed
-- one in the base revision, and one which moved at where it now is.
/--
info: **3 declarations changed**: 1 added, 1 moved, 1 removed.

| Declaration | Change | File |
| - | - | - |
| [`lemma foo`](…/hsha/A.lean#L3) | added | `A.lean` |
| [`def baz`](…/hsha/A.lean#L9) | moved | `B.lean` → `A.lean` |
| [`def bar`](…/bsha/B.lean#L7) | removed | `B.lean` |
-/
#guard_msgs in
#eval IO.println (shortLinks (declReport testSource (declDiff #[
  mkLine "A.lean" 3 true "lemma foo : True := trivial",
  mkLine "B.lean" 7 false "def bar : Nat := 0",
  mkLine "B.lean" 2 false "def baz : Nat := 0",
  mkLine "A.lean" 9 true "def baz : Nat := 0"])))

/-- info: This PR changes the statement of no declaration. -/
#guard_msgs in
#eval IO.println (declReport testSource #[])

/-! ### E.10. Results written with `theorem` -/

/-- The declarations of a pull-request which writes one result with `theorem` and one with
`lemma`, and moves a third result which was already a `theorem`. -/
def exampleTheorems : Array DeclDiff :=
  declDiff #[
    mkLine "A.lean" 3 true "theorem foo : True := trivial",
    mkLine "A.lean" 9 true "lemma bar : True := trivial",
    mkLine "B.lean" 2 false "theorem baz : True := trivial",
    mkLine "A.lean" 20 true "theorem baz : True := trivial"]

-- Only the new `theorem` is called out: `bar` is a `lemma`, and `baz` only moved.
/-- info: theorem foo -/
#guard_msgs in
#eval IO.println ("\n".intercalate ((newTheorems exampleTheorems).toList.map (·.decl.display)))

/--
info: > [!IMPORTANT]
> This PR writes 1 result with `theorem`:
> [`theorem foo`](…/hsha/A.lean#L3).
>
> `theorem` is reserved for the results which are significant in the physics literature,
> usually known by name; every other result is a `lemma`. Each one needs a doc-string and
> a line under the section of its library in `scripts/lint/exemptions/Theorems.txt`,
> **which this PR does not change**.
> `lake exe theorem_lint` checks both.
-/
#guard_msgs in
#eval IO.println (shortLinks (theoremCallout testSource #[] exampleTheorems))

-- A pull-request which also changes the theorems file is told so, rather than warned.
/-- info: true -/
#guard_msgs in
#eval ((theoremCallout testSource #[{ path := theoremsFile, status := .modified }]
  exampleTheorems).splitOn "which this PR also changes").length == 2

-- Nothing is called out when the pull-request writes no `theorem`.
/-- info: "" -/
#guard_msgs in
#eval theoremCallout testSource #[] (declDiff #[
  mkLine "A.lean" 3 true "lemma bar : True := trivial"])

/-! ### E.11. The summary -/

/--
info: ### Files

**1 file changed**: 1 modified.

| File | Change | Lines |
| - | - | - |
| [`A.lean`](…/hsha/A.lean) | modified | +1 -0 |

### Declarations

**1 declaration changed**: 1 added.

| Declaration | Change | File |
| - | - | - |
| [`lemma foo`](…/hsha/A.lean#L3) | added | `A.lean` |

The declarations are found by reading the diff as text, so this table misses a declaration whose
keyword and name are on two lines, and it does not know about namespaces. A change to a proof, or
to the body of a definition, does not appear here. See `scripts/github/pr_summary.lean`.
-/
#guard_msgs (whitespace := lax) in
#eval IO.println (shortLinks (summary testSource
  #[{ path := "A.lean", status := .modified, insertions := some 1, deletions := some 0 }]
  (declDiff #[mkLine "A.lean" 3 true "lemma foo : True := trivial"])))

-- The call-out about the results written with `theorem` comes before the tables.
/-- info: true -/
#guard_msgs in
#eval (summary testSource #[] exampleTheorems).startsWith "> [!IMPORTANT]"

/-!

## F. The executable

-/

/-- Runs `git` with the arguments `args` in the current directory and returns its standard
output. Throws if `git` reports an error, for instance if a revision is unknown. -/
def git (args : Array String) : IO String := do
  let out ← IO.Process.output { cmd := "git", args }
  if out.exitCode ≠ 0 then
    throw <| IO.userError s!"`git {" ".intercalate args.toList}` exited with code \
      {out.exitCode}:\n{out.stderr.trimAscii}"
  return out.stdout

/-- The lines of the standard output of `git` with the arguments `args`, without its last,
empty, line. -/
def gitLines (args : Array String) : IO (Array String) := do
  let out := rtrim (← git args)
  return if out.isEmpty then #[] else (out.splitOn "\n").toArray

/-- The commit the revision `revision` names, which is what a link must use: a link to
`HEAD` would follow the branch rather than point at what was summarised. -/
def commitOf (revision : String) : IO String :=
  return rtrim (← git #["rev-parse", revision])

/-- The summary of the changes the revision `head` makes to `base`, as Markdown. -/
def gitSummary (base head : String) : IO String := do
  let range := s!"{base}...{head}"
  let src : Source := { base := ← commitOf base, head := ← commitOf head }
  let files := withLineCounts
    (parseNameStatus (← gitLines #["diff", "--name-status", "-M", range]))
    (parseNumstat (← gitLines #["diff", "--numstat", "--no-renames", range]))
  -- `-M` lets `git` see a renamed file as renamed, so the declarations of a file which only
  -- moved do not all show up as moved; the rename itself is reported among the files.
  let decls := declDiff (parseDiff (← gitLines #["diff", "--unified=0", "-M", range]))
  return summary src files decls

/-- The revisions to compare, read from the arguments of the executable: the base, which
defaults to `origin/master`, and the head, which defaults to `HEAD`. -/
def revisions : List String → Except String (String × String)
  | [] => .ok ("origin/master", "HEAD")
  | [base] => .ok (base, "HEAD")
  | [base, head] => .ok (base, head)
  | args => .error s!"Expected at most two revisions, got {args.length}."

/-- info: Except.ok ("origin/master", "HEAD") -/
#guard_msgs in
#eval revisions []

/-- info: Except.ok ("abc", "HEAD") -/
#guard_msgs in
#eval revisions ["abc"]

/-- info: Except.ok ("abc", "def") -/
#guard_msgs in
#eval revisions ["abc", "def"]

/-- info: Except.error "Expected at most two revisions, got 3." -/
#guard_msgs in
#eval revisions ["a", "b", "c"]

end PRSummary

open PRSummary in
def main (args : List String) : IO UInt32 := do
  let (base, head) ← match revisions args with
    | .ok revs => pure revs
    | .error e =>
      IO.eprintln s!"{e}\nUsage: lake exe pr_summary [<base> [<head>]]"
      return 1
  IO.eprintln s!"Summarising `git diff {base}...{head}`."
  try
    IO.println (← gitSummary base head)
  catch e =>
    IO.eprintln s!"Could not summarise the pull-request: {e}"
    return 1
  return 0
