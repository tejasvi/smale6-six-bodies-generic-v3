import CC6Compose

open Lean Meta Elab Command

/-! The interface of the composition with the checks run by `native_decide` (run with
`lake env lean tools/NativeInterface.lean` in `Compose/`). From `CC6Compose.main_theorem`, walks the declarations of
this project (`CC6Full`, `CC6Compose`) that its proof uses, and lists, grouped by name pattern (digits replaced by
`#`), the constants of the certificate projects reached from them that depend on an auxiliary axiom of
`native_decide`, with some of the declarations that use them. Declarations of the composition that use
`native_decide` themselves (`open_specials`) are not listed. -/

run_cmd do
  let env ← getEnv
  let ours (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some i => let r := (env.header.moduleNames[i.toNat]!).getRoot; r == `CC6Compose || r == `CC6Full
    | none => true
  let valOf (n : Name) : Option Expr := match env.find? n with
    | some (.thmInfo t) => some t.value
    | some (.defnInfo d) => some d.value
    | some (.opaqueInfo o) => some o.value
    | _ => none
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := #[`CC6Compose.main_theorem]
  let mut leaves : Std.HashMap Name Name := {}
  while h : stack.size > 0 do
    let n := stack.back
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let cs := (ci.type.getUsedConstants ++ ((valOf n).map (·.getUsedConstants)).getD #[])
    for c in cs do
      if ours c then
        unless seen.contains c do stack := stack.push c
      else if !leaves.contains c then
        let axs ← liftCoreM (Lean.collectAxioms c)
        if axs.any fun a => (a.toString.splitOn "._native.native_decide.ax_").length > 1 then
          leaves := leaves.insert c n
  let mut fam : Std.HashMap String (Nat × Array Name) := {}
  for (c, u) in leaves.toList do
    let key := String.map (fun ch => if ch.isDigit then '#' else ch) c.toString
    let (k, us) := fam.getD key (0, #[])
    fam := fam.insert key (k + 1, us.push u)
  logInfo m!"declarations of this project in the cone: {seen.size}"
  for (key, (k, us)) in fam.toList do
    logInfo m!"{k} x {key}  <-  e.g. {(us.toList.map toString).eraseDups.take 2}"
