import Lean

open Lean

unsafe def main (args : List String) : IO Unit := do
  let [moduleString, target] := args | throw (IO.userError "Expected module and target name")
  initSearchPath (← findSysroot)
  let moduleName := moduleString.toName
  let (data, _) ← readModuleData (← findOLean moduleName)
  let names := data.constants.filterMap fun ci =>
    if ci.name.toString.startsWith "_private." then none
    else if target.isEmpty && (match ci with | .thmInfo _ => true | _ => false) then some ci.name
    else if !target.isEmpty && (ci.name.toString == target || ci.name.toString.endsWith ("." ++ target)) then some ci.name
    else none
  if names.isEmpty then throw (IO.userError s!"No target declarations in {moduleName} for {target}")
  withImportModules #[{module := moduleName}] {} fun env => do
    for name in names do
      let (_, state) := ((CollectAxioms.collect name).run env).run {}
      IO.println (Json.mkObj [("declaration", toJson name.toString),
        ("axioms", toJson (state.axioms.map Name.toString))]).compress
