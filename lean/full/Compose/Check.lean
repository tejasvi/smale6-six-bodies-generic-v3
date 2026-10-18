import CC6Compose

/-! The axioms of Theorem 1.1 (run with `lake env lean Check.lean` in this directory). Allowed: `propext`,
`Classical.choice`, `Quot.sound`, and the auxiliary axioms that `native_decide` adds (named
`<theorem>._native.native_decide.ax_<i>_<j>`), each stating that compiled code evaluated a Boolean check to `true`. -/

#print axioms CC6Compose.main_theorem
