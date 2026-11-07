import Lean

/-!
Check that every declaration named in the blueprint exists.

    lake build
    lake env lean --run scripts/CheckDecls.lean blueprint/lean_decls

`blueprint/lean_decls` is written by `leanblueprint web`. This does the job
of the `checkdecls` package without adding a dependency to the lakefile.
-/

open Lean

def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: CheckDecls <lean_decls>"; return 2
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Credibility }] {} (trustLevel := 1024)
  let names := (← IO.FS.lines path).map (·.trimAscii.toString) |>.filter (· ≠ "")
  let missing := names.filter fun n => !env.contains n.toName
  for n in missing do IO.eprintln s!"not a declaration: {n}"
  IO.println s!"{names.size - missing.size} / {names.size} blueprint declarations found"
  return if missing.isEmpty then 0 else 1
