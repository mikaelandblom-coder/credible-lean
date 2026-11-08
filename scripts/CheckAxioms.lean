import Lean

/-!
Axiom audit for the `Credibility` library.

    lake build
    python3 scripts/progress.py --proved > proved.txt
    lake env lean --run scripts/CheckAxioms.lean proved.txt

Fails if
* any declaration in `Credibility` uses an axiom other than `propext`,
  `Classical.choice`, `Quot.sound` (or `sorryAx`), or
* a theorem listed in `proved.txt` (the ones `PROGRESS.md` and the blueprint
  count as proved) depends on `sorryAx`, directly or through a lemma.

Open `sorry`s in theorems not yet counted as proved are expected on `main`
while a file is in progress, so they are listed but do not fail the check.
-/

open Lean

def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Axioms a constant depends on, memoised across calls (one shared traversal
instead of re-walking Mathlib for every theorem). Mirrors `Lean.collectAxioms`. -/
partial def axiomsOf (env : Environment) (n : Name) :
    StateM (Std.HashMap Name NameSet) NameSet := do
  if let some s := (← get)[n]? then return s
  modify (·.insert n {})  -- guards against cycles (inductives and their constructors)
  let deps : Array Name := match env.find? n with
    | some (.axiomInfo _) => #[]
    | some (.defnInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
    | some (.thmInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
    | some (.opaqueInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
    | some (.quotInfo _) => #[]
    | some (.ctorInfo v) => v.type.getUsedConstants
    | some (.recInfo v) => v.type.getUsedConstants
    | some (.inductInfo v) => v.type.getUsedConstants ++ v.ctors.toArray
    | none => #[]
  let mut s : NameSet := if (env.find? n).any (·.isAxiom) then ({} : NameSet).insert n else {}
  for d in deps do
    for a in (← axiomsOf env d) do s := s.insert a
  modify (·.insert n s)
  return s

def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: CheckAxioms <proved names>"; return 2
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Credibility }] {} (trustLevel := 1024)
  let proved := (← IO.FS.lines path).map (·.trimAscii.toString) |>.filter (· ≠ "")
  -- every declaration whose module is part of this library
  let ours := env.constants.toList.filterMap fun (n, _) =>
    match env.getModuleIdxFor? n with
    | some i =>
      if (`Credibility).isPrefixOf env.header.moduleNames[i.toNat]! && !n.isInternal
      then some n else none
    | none => none
  let mut cache : Std.HashMap Name NameSet := {}
  let mut bad := 0
  let mut openSorry := 0
  for n in ours do
    let (as, c) := (axiomsOf env n).run cache
    cache := c
    let extra := as.toList.filter fun a => a != ``sorryAx && !allowed.contains a
    if !extra.isEmpty then
      IO.eprintln s!"disallowed axioms in {n}: {extra}"
      bad := bad + 1
    if as.contains ``sorryAx then openSorry := openSorry + 1
  for s in proved do
    let n := s.toName
    unless env.contains n do
      IO.eprintln s!"not a declaration: {s}"
      bad := bad + 1
      continue
    let (as, c) := (axiomsOf env n).run cache
    cache := c
    if as.contains ``sorryAx then
      IO.eprintln s!"counted as proved but depends on sorry: {s}"
      bad := bad + 1
  IO.println s!"{ours.length} declarations audited, {proved.size} proved theorems sorry-free, \
    {openSorry} declarations still depend on sorry"
  return if bad == 0 then 0 else 1
