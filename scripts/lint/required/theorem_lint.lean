/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Lean
/-!

# Theorem linter

Each of the libraries `Physlib`, `QuantumInfo` and `PhyslibAlpha` reserves the `theorem` keyword
for its conceptually important results; every other result is a `lemma`. The fully qualified
names of the important results of a library `L` are listed, one per line, in `L/Theorems.txt`.
This executable checks, for each library `L`, that:

- every declaration of `L` written with `theorem` is listed in `L/Theorems.txt`,
- every name listed in `L/Theorems.txt` is a declaration of `L` written with `theorem`,
- every declaration of `L` written with `theorem` has a doc-string.

`lemma` is Mathlib syntax which expands to `theorem`, so the environment does not record which
of the two keywords was written. The linter recovers it without a text search. For each theorem
of the imported environment it takes the declaration range Lean stored for it, and runs Lean's
own parser, with the token table of the environment, at the start of that range: first the
declaration modifiers (doc-string, attributes, `private`, ...), then the keyword, then the
declaration identifier. The identifier is checked against the fully qualified name of the
constant, accounting for the enclosing namespaces, `_root_` and `private`. This check discards
the theorems generated from a declaration (by `to_additive`, `simps`, equation lemmas, ...),
which share its declaration range but not its name.

Run from the root of the repository with `lake exe theorem_lint`, after building the three
libraries. `lake exe theorem_lint Physlib` lints only `Physlib` (and similarly for the others).

-/

open Lean Parser

namespace TheoremLint

/-!

## A. The theorems file

The theorems file lists one fully qualified name per line. Blank lines are ignored.

-/

/-- The libraries which are linted. -/
def libraries : Array Name := #[`Physlib, `QuantumInfo, `PhyslibAlpha]

/-- The file listing the theorems of `library`, relative to the root of the repository. -/
def theoremsFile (library : Name) : System.FilePath := library.toString / "Theorems.txt"

/-- The names listed in the theorems file of `library`, given as its lines, with the line of
each. -/
def parseNames (library : Name) (lines : Array String) : Except String (Array (Name × Nat)) := do
  let mut names := #[]
  for line in lines, lineNo in [1:lines.size + 1] do
    let text := line.trimAscii.toString
    if text.isEmpty then continue
    let some name := Syntax.decodeNameLit ("`" ++ text)
      | throw s!"{theoremsFile library}:{lineNo}: `{text}` is not a Lean name"
    names := names.push (name, lineNo)
  return names

/-!

## B. The keyword of a theorem

-/

/-- A theorem of the library together with how it is written in the source. -/
structure WrittenTheorem where
  /-- The constant, with `private` names given as the user wrote them. -/
  name : Name
  /-- The source file of the module declaring the constant. -/
  file : System.FilePath
  /-- The position of the keyword in `file`. -/
  pos : Position
  /-- The keyword the declaration is written with, `theorem` or `lemma`. -/
  keyword : String
  /-- Whether the declaration has a doc-string. -/
  hasDocString : Bool

/-- The source file of a module, relative to the root of the repository. -/
def moduleFile (module : Name) : System.FilePath :=
  (System.mkFilePath (module.components.map Name.toString)).addExtension "lean"

/-- Parses, with Lean's parser in the environment `env`, the declaration modifiers at `pos`
followed by two tokens, and returns these tokens. For a `theorem` or `lemma` declaration they
are its keyword and its declaration identifier. -/
def headTokens (env : Environment) (ictx : InputContext) (pos : String.Pos.Raw) :
    Option (Syntax × Syntax) :=
  let p := andthenFn (Command.declModifiers false).fn (andthenFn (tokenFn []) (tokenFn []))
  let s := p.run ictx { env, options := {} } (getTokenTable env)
    ((mkParserState ictx.inputString).setPos pos)
  if s.hasError then none
  else some (s.stxStack.get! (s.stxStack.size - 2), s.stxStack.back)

/-- Whether the declaration identifier `ident`, written in some namespace, declares the constant
`name`: `name` is `ident` prefixed by the namespace, or `ident` with `_root_` removed. -/
def declares (ident name : Name) : Bool :=
  let name := privateToUserName name
  if ident.getRoot == `_root_ then
    ident.replacePrefix `_root_ .anonymous == name
  else
    ident.isSuffixOf name

/-- The theorems declared in `module`, written with `theorem` or `lemma`. -/
def writtenTheorems (env : Environment) (module : Name) (constants : Array ConstantInfo) :
    CoreM (Array WrittenTheorem) := do
  let file := moduleFile module
  let ictx := mkInputContext (← IO.FS.readFile file) file.toString
  let mut result := #[]
  for c in constants do
    let .thmInfo _ := c | continue
    let some ranges ← findDeclarationRanges? c.name | continue
    let start := ictx.fileMap.ofPosition ranges.range.pos
    let some (keywordStx, ident) := headTokens env ictx start | continue
    let .atom _ keyword := keywordStx | continue
    unless keyword == "theorem" || keyword == "lemma" do continue
    let .ident _ _ ident _ := ident | continue
    unless declares ident c.name do continue
    let pos := ictx.fileMap.toPosition (keywordStx.getPos?.getD start)
    let hasDocString := (← findDocString? env c.name).isSome
    result := result.push { name := privateToUserName c.name, file, pos, keyword, hasDocString }
  return result

/-!

## C. The linter

-/

/-- An error of the linter, located in a source file. -/
structure LintError where
  /-- The file the error is located in. -/
  file : System.FilePath
  /-- The position of the error in `file`. -/
  pos : Position
  /-- The error message. -/
  message : String

instance : ToString LintError where
  toString e := s!"{e.file}:{e.pos.line}:{e.pos.column}: error: {e.message}"

/-- The order of errors: by file, then by position. -/
def LintError.lt (e f : LintError) : Bool :=
  e.file.toString < f.file.toString || e.file == f.file &&
    (e.pos.line < f.pos.line || e.pos.line == f.pos.line && e.pos.column < f.pos.column)

/-- The errors of the linter for `library`, whose theorems file lists `names`: theorems not
listed in the theorems file or without a doc-string, and listed names which are not theorems. -/
def lint (library : Name) (names : Array (Name × Nat)) : CoreM (Array LintError) := do
  let env ← getEnv
  let theoremsFile := theoremsFile library
  let mut errors := #[]
  -- The names listed in the theorems file, with their lines, and duplicates among them.
  let mut listed : NameMap Nat := {}
  for (name, line) in names do
    if let some first := listed.find? name then
      errors := errors.push ⟨theoremsFile, ⟨line, 0⟩,
        s!"`{name}` is already listed on line {first}."⟩
    listed := listed.insert name line
  -- The theorems of the library and their keywords.
  let mut written : NameMap WrittenTheorem := {}
  for module in env.header.moduleNames, data in env.header.moduleData do
    unless library.isPrefixOf module do continue
    for thm in ← writtenTheorems env module data.constants do
      written := written.insert thm.name thm
  for (name, thm) in written do
    if thm.keyword == "theorem" && !thm.hasDocString then
      errors := errors.push ⟨thm.file, thm.pos, s!"`{name}` is written with `theorem` but has \
        no doc-string."⟩
    match thm.keyword, listed.find? name with
    | "theorem", none =>
      errors := errors.push ⟨thm.file, thm.pos, s!"`{name}` is written with `theorem` but is \
        not listed in {theoremsFile}. Use `lemma`, or list it if it is a conceptually \
        important result."⟩
    | "lemma", some line =>
      errors := errors.push ⟨theoremsFile, ⟨line, 0⟩, s!"`{name}` is listed but is \
        written with `lemma` at {thm.file}:{thm.pos.line}:{thm.pos.column}. Use `theorem`."⟩
    | _, _ => pure ()
  for (name, line) in listed do
    if written.contains name then continue
    let error (message : String) : LintError := ⟨theoremsFile, ⟨line, 0⟩, message⟩
    match env.getModuleIdxFor? name with
    | none => errors := errors.push <| error s!"`{name}` is not a declaration. Give the fully \
        qualified name."
    | some idx =>
      let module := env.header.moduleNames[idx]!
      if !library.isPrefixOf module then
        errors := errors.push <| error s!"`{name}` is declared in `{module}`, which is not \
          part of {library}."
      else
        errors := errors.push <| error s!"`{name}` is not declared with `theorem`."
  return errors.qsort LintError.lt

end TheoremLint

open TheoremLint in
unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  Lean.enableInitializersExecution
  let toLint := if args.isEmpty then libraries else (args.map String.toName).toArray
  for library in toLint do
    unless libraries.contains library do
      IO.eprintln s!"Unknown library `{library}`, expected one of {libraries}."
      return 1
  let env ← importModules (loadExts := true) (toLint.map ({ module := · })) {} 0
  let ctx : Core.Context := { fileName := "", options := {}, fileMap := default }
  let mut failed := false
  for library in toLint do
    println! "Checking that `theorem` is used exactly for the results listed in \
      {theoremsFile library}, with doc-strings."
    let names ← match parseNames library (← IO.FS.lines (theoremsFile library)) with
      | .ok names => pure names
      | .error msg => IO.eprintln s!"{msg}"; failed := true; continue
    let (errors, _) ← (lint library names).toIO ctx { env }
    for error in errors do
      println! error
    if errors.isEmpty then
      println! "\x1b[32mThe theorems of {library} agree with {theoremsFile library}.\x1b[0m"
    else
      println! "\x1b[31m{errors.size} errors found in {library}.\x1b[0m"
      failed := true
  return if failed then 1 else 0
