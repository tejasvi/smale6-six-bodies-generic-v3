import L6Check.F2.All
import L6Check.F2.Trees
import L6Sound.F2.Oracle

/-! The statements, per-class counts and axioms of the F2 theorems (printed into the build log). -/

open L6.F2 L6.F2.Checks

#check @f2_all
#check @f2_totals
#check @f2_classes_with_cells
#check @tree_counts
#check @L6.F2.decideLP_discard

/- Per class: (class, cells, linear programs, prunes) of the checked chunks (the chunk theorems prove that the Lean
search produces exactly these numbers). -/
#eval (List.range 191).map fun k => let (c, l, p) := totals (chunksOf k); (k, c, l, p)

#print axioms f2_all
#print axioms f2_totals
#print axioms f2_classes_with_cells
#print axioms tree_counts
#print axioms L6.F2.decideLP_discard
#print axioms L6.F2.feasible_discard
