import VOA
open Lean Meta Elab Command

-- For every name listed in `headline_cands.txt` (short or qualified), find the matching
-- theorems in `VOA.*` modules and print, per theorem: its explicit Prop hypotheses
-- (binder types, pretty-printed) and its axiom closure.  Output: `headline_hyps.tsv`.
#eval show CommandElabM Unit from do
  let env ← getEnv
  let path := (← IO.getEnv "HEADLINE_CANDS").getD "headline_cands.txt"
  let cands := (← IO.FS.lines path).toList.filter (· ≠ "")
  let modOf : Name → Option Name := fun n =>
    (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!
  let isVOA : Name → Bool := fun n => match modOf n with
    | some m => m.getRoot == `VOA | none => false
  -- index VOA theorems by last component
  let mut byLast : Std.HashMap String (Array Name) := {}
  for (n, ci) in env.constants.toList do
    if ci.isThm && isVOA n && !n.isInternal then
      let k := n.componentsRev.head!.toString
      byLast := byLast.insert k ((byLast.getD k #[]).push n)
  let mut out : Array String := #[]
  for c in cands do
    let parts := c.splitOn "."
    let last := parts.getLast!
    for n in byLast.getD last #[] do
      if n.toString.endsWith c then
        let ci := env.find? n |>.get!
        let (hyps, axs) ← liftTermElabM do
          let hyps ← forallTelescope ci.type fun xs _ => do
            let mut hs : Array String := #[]
            for x in xs do
              let d ← x.fvarId!.getDecl
              if d.binderInfo.isExplicit && (← isProp d.type) then
                let s := toString (← ppExpr d.type)
                hs := hs.push ((s.replace "\n" " ").take 160)
            return hs
          let axs ← Lean.collectAxioms n
          return (hyps, axs)
        let axStr := ", ".intercalate (axs.toList.map toString)
        out := out.push s!"{n}\t{(modOf n).get!}\t{hyps.size}\t{axStr}\t{" ‖ ".intercalate hyps.toList}"
  IO.FS.writeFile "headline_hyps.tsv" ("\n".intercalate out.toList)
  logInfo s!"headline theorems analysed: {out.size}"
