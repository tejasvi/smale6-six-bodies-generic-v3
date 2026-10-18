import L6Check.F1.Main

/-! Prints the class list `L6F1.classes6` as the Lean literal of `CC6Compose/ClassesLit.lean` (run with
`lake env lean gen/PrintClasses.lean` in `Compose/`). The printing runs compiled code; the literal is not trusted:
`open_specials_of_eq` takes its equality with `L6F1.classes6` as a hypothesis. -/

#eval show IO Unit from do
  let items := L6F1.classes6.map fun (d, k) => s!"(⟨{d.e}, {d.zc}, {d.wc}⟩, {k})"
  IO.println ("[" ++ ", ".intercalate items ++ "]")
