import L6F2.Trees

namespace L6.F2.Checks

/-- Without pruning, the insertions give 55,720 trees, pairwise distinct, of which 16,512 have a body on the leaf of
`O` (and 39,208 have seven leaves). -/
theorem tree_counts : L6.F2.treeCounts = (55720, 55720, 16512) := by
  native_decide

end L6.F2.Checks
