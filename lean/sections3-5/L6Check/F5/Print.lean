import L6F5
import L6Check.F5.Data

/-! Prints the census of Proposition 5.9 into the build log (not a check; the checks are in `L6Check.F5.Census`). -/

namespace L6F5

/-- The census as lines `class cells clique three four forced`, and the totals. -/
def censusLines : String :=
  match census Data.n6 Data.files with
  | none => "census: none"
  | some t =>
    let rows := (List.range t.length).zip t
    let body := rows.map fun (c, r) => s!"{c} {r.cells} {r.clique} {r.three} {r.four} {r.forced}"
    let sum (f : Tally → Nat) : Nat := (t.map f).sum
    "\n".intercalate body ++
      s!"\ntotal {sum (·.cells)} {sum (·.clique)} {sum (·.three)} {sum (·.four)} {sum (·.forced)}"

set_option profiler true in
#eval IO.println censusLines

set_option profiler true in
#eval IO.println (repr (openStatus Data.n6 Data.files Data.open43))

/-- The cells without a clique as in Corollary 5.8 (`none class cell`) and the cells with a clique of four bodies
(`four class cell`), one per line. -/
def cellLines : String :=
  match statuses Data.n6 Data.files with
  | none => "statuses: none"
  | some t =>
    let rows := ((List.range t.length).zip t).flatMap fun (c, a) =>
      ((List.range a.size).zip a.toList).flatMap fun (k, st) =>
        (if st.clique then [] else [s!"none {c} {k}"]) ++ (if st.four then [s!"four {c} {k}"] else [])
    "\n".intercalate rows

set_option profiler true in
#eval IO.println cellLines

/-- The ten cells whose cores rest on Singular alone (Section 9 of the paper). -/
def singularOnlyCells : List (Nat × Nat) :=
  [(3, 8722), (3, 13414), (3, 17222), (3, 24695), (3, 31349), (3, 41091), (3, 41143), (3, 41569), (14, 218), (30, 122)]

set_option profiler true in
#eval IO.println (repr (singularOnlyCells.map fun q => (q.1, q.2, cellStatus Data.n6 Data.files q.1 q.2)))

end L6F5
