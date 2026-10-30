import Lean
import LeanChecker.Replay

open Lean

unsafe def main (paths : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let mut declarations : Std.HashMap Name ConstantInfo := {}
  let mut duplicates := 0
  for path in paths do
    let (data, _) ← readModuleData ⟨path⟩
    for ci in data.constants do
      if let some previous := declarations[ci.name]? then
        match previous, ci with
        | .thmInfo a, .thmInfo b =>
          unless a.type == b.type && a.value == b.value && a.levelParams == b.levelParams do
            throw (IO.userError s!"Inconsistent duplicate theorem: {ci.name}")
        | _, _ => throw (IO.userError s!"Unexpected duplicate declaration: {ci.name}")
        duplicates := duplicates + 1
        continue
      declarations := declarations.insert ci.name ci
  let skipped := declarations.toList.filterMap fun (n, ci) =>
    if ci.isUnsafe || ci.isPartial then some n.toString else none
  let axioms := declarations.toList.filterMap fun (n, ci) =>
    match ci with | .axiomInfo _ => some n.toString | _ => none
  IO.println (Json.mkObj [("modules", toJson paths.length), ("uniqueDeclarations", toJson declarations.size),
    ("eligibleDeclarations", toJson (declarations.size - skipped.length)),
    ("identicalDuplicateTheorems", toJson duplicates), ("skippedUnsafeOrPartial", toJson skipped),
    ("axiomDeclarations", toJson axioms)]).compress
  withImportModules #[{module := `Mathlib}, {module := `Lean}] {} fun base => do
    discard (base.replay' declarations)
  IO.println "PASS: eligible safe non-partial declarations accepted by the kernel over public Mathlib/Lean imports; axiom declarations are admitted as axioms"
