import Lean

/-!
Check that blueprint `\uses` edges between proofs are real: a theorem whose
blueprint proof `\uses` a result must refer to that result in its Lean proof.

    lake build
    python3 scripts/blueprint_check.py --uses > uses.txt
    lake env lean --run scripts/CheckUses.lean uses.txt

Each line of `uses.txt` is `thm₁|thm₂ label=name₁|name₂ …`, one line per
blueprint statement: the `thmᵢ` are its `\lean` names (proved ones only), and
for every `label` its proof `\uses`, the `nameⱼ` are that label's `\lean`
names. The check: some `thmᵢ` mentions some `nameⱼ` in its proof term (or in
the auxiliary `thmᵢ._proof_n` lemmas Lean generates for it). A statement with
several `\lean` names shares one blueprint proof, so one of them using the
result is enough. Only direct references count: going through some other
lemma does not.
-/

open Lean

/-- Constants the proof of `n` refers to directly, looking inside the
auxiliary declarations Lean generates for it (`n._proof_1`, `n.match_1`, …). -/
partial def directUses (env : Environment) (n : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := #[n]
  let mut out : NameSet := {}
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    let some info := env.find? c | continue
    let deps := info.type.getUsedConstants ++ ((info.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
    for d in deps do
      out := out.insert d
      if n.isPrefixOf d && d != n then todo := todo.push d
  return out

def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: CheckUses <uses.txt>"; return 2
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Credibility }] {} (trustLevel := 1024)
  let lines := (← IO.FS.lines path).map (·.trimAscii.toString) |>.filter (· ≠ "")
  let mut bad := 0
  let mut edges := 0
  for l in lines do
    let some thm := (l.splitOn " ").head? | continue
    let thms := thm.splitOn "|" |>.map (·.toName)
    let missing := thms.filter (!env.contains ·)
    unless missing.isEmpty do
      IO.eprintln s!"not a declaration: {missing}"
      bad := bad + 1
      continue
    let used : NameSet := thms.foldl (fun s n => (directUses env n).foldl (·.insert ·) s) {}
    for req in (l.splitOn " ").drop 1 |>.filter (· ≠ "") do
      edges := edges + 1
      let (label, alts) := match req.splitOn "=" with
        | [a, b] => (a, b.splitOn "|")
        | _ => (req, [req])
      unless alts.any (fun a => used.contains a.toName) do
        IO.eprintln s!"{thm}: blueprint proof \\uses {label} but the Lean proof does not use {" or ".intercalate alts}"
        bad := bad + 1
  IO.println s!"{edges} \\uses edges checked, {bad} not used in the Lean proof"
  return if bad == 0 then 0 else 1
