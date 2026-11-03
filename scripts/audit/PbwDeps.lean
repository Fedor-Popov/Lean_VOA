import VOA
open Lean Elab Command

-- Dump the `VOA.pbw` dependency structure of every declaration in a `VOA.*` module
-- to `pbw_deps.tsv`: DIRECT users (with the field used), all transitive dependents, and roots.
#eval show CommandElabM Unit from do
  let env ← getEnv
  let modOf : Name → Option Name := fun n =>
    (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!
  let isVOA : Name → Bool := fun n => match modOf n with
    | some m => m.getRoot == `VOA | none => false
  let pbw := `VOA.pbw
  let fAV := `VOA.PBWPrinciple.affineVacuum
  let fIB := `VOA.PBWPrinciple.inducedBottom
  let mut usedBy : Std.HashMap Name (Array Name) := {}
  let mut direct : Array String := #[]
  let mut isUsed : Std.HashSet Name := {}
  for (n, ci) in env.constants.toList do
    if isVOA n then
      let mut cs := ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
      if cs.contains pbw then
        let f := (if cs.contains fAV then "AV " else "") ++ (if cs.contains fIB then "IB " else "")
        direct := direct.push s!"DIRECT\t{n}\t{(modOf n).get!}\t{f}"
      for c in cs do
        if c != n && (isVOA c || c == pbw) then
          usedBy := usedBy.insert c ((usedBy.getD c #[]).push n)
          isUsed := isUsed.insert c
  -- BFS over reverse edges from pbw
  let mut seen : Std.HashSet Name := {}
  let mut queue : Array Name := #[pbw]
  let mut i := 0
  while i < queue.size do
    let c := queue[i]!
    i := i + 1
    for u in usedBy.getD c #[] do
      if !seen.contains u then
        seen := seen.insert u; queue := queue.push u
  let mut lines := direct
  for n in seen.toList do
    let root := if isUsed.contains n then "inner" else "ROOT"
    lines := lines.push s!"DEP\t{n}\t{(modOf n).get!}\t{root}"
  IO.FS.writeFile "pbw_deps.tsv" (String.intercalate "\n" lines.toList)
  logInfo s!"pbw-dependent: {seen.size}; direct: {direct.size}"
