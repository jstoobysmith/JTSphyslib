/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/

def main (args : List String) : IO UInt32 := do

  println! "\x1b[36m(1/8) Style lint \x1b[0m"
  println! "\x1b[2mThis linter is not checked by GitHub but if you have time please fix these errors.\x1b[0m"
  let styleLint ← IO.Process.output {cmd := "lake", args := #["exe", "style_lint"]}
  println! styleLint.stdout

  println! "\x1b[36m(2/8) Building \x1b[0m"
  let build ← IO.Process.output {cmd := "lake", args := #["build"]}
  let s1 := "Build completed successfully"
  let s2 := build.stdout
  if ¬ (s2.splitOn s1).length = 2  then
    println! "\x1b[31mError: Build failed. Run `lake build` to see the errors.\x1b[0m\n"
  else
    println! "\x1b[32mBuild is successful.\x1b[0m\n"

  println! "\x1b[36m(3/8) File imports \x1b[0m"
  let importCheck ← IO.Process.output {cmd := "lake", args := #["exe", "check_file_imports"]}
  println! importCheck.stdout

  println! "\x1b[36m(3/8) Illegal Imports\x1b[0m"
  let noAlphaImports ← IO.Process.output {cmd := "lake", args := #["exe", "noAlphaImports"]}
  println! noAlphaImports.stdout

  println! "\x1b[36m(3/8) Ensuring all PhyslibAlpha modules imported\x1b[0m"
  let alphaFileImports ← IO.Process.output {cmd := "lake", args := #["exe", "alphaFileImports"]}
  println! alphaFileImports.stdout

  println! "\x1b[36m(4/8) TODO tag duplicates \x1b[0m"
  let todoCheck ← IO.Process.output {cmd := "lake", args := #["exe", "check_dup_tags"]}
  println! todoCheck.stdout

  println! "\x1b[36m(5/8) Sorry and pseudo attribute linter \x1b[0m"
  let sorryPseudoCheck ← IO.Process.output {cmd := "lake", args := #["exe", "sorry_lint"]}
  println! sorryPseudoCheck.stdout
  println! sorryPseudoCheck.stderr

  println! "\x1b[36m(6/8) Module documentation linter \x1b[0m"
  let moduleDocCheck ← IO.Process.output {cmd := "lake", args := #["exe", "module_doc_lint"]}
  println! moduleDocCheck.stdout

  if ¬ "--fast" ∈ args then
    println! "\x1b[36m(7/8) Lean linter \x1b[0m"
    println! "\x1b[2mExpect this linter to take a while to run, it can be skipped with
      lake exe lint_all --fast"
    println! "You can manually perform this linter by placing `#lint` at the end of the files you have modified.\x1b[0m"
    let leanCheck ← IO.Process.output {cmd := "lake", args := #["exe", "runPhyslibLinters", "Physlib"]}
    println! leanCheck.stdout

    println! "\x1b[36m(8/8) Transitive imports \x1b[0m"
    println! "\x1b[2mExpect this linter to take a while to run, it can be skipped with
        lake exe lint_all --fast\x1b[0m"
    let redundentImports ← IO.Process.output {cmd := "lake", args := #["exe", "redundant_imports"]}
    println! redundentImports.stdout



  pure 0
