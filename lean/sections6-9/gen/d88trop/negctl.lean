import Lean6.Special.Comp.D88.Trop.RunN4
import Lean6.Special.Comp.D88.Trop.RunKC

/-! Negative controls for the covering checker (not part of the proof): changing one certificate token makes the
checker return `false`. (A split may use any hyperplane: changing one is not an error.) Run with `lake env lean gen/d88trop/negctl.lean`. -/

open Lean6.Special.Comp.D88.Trop

/-- Replace the token at position `k` by `t`. -/
def patch (s : String) (k : Nat) (t : String) : String :=
  " ".intercalate (((tokens s).set k t))

/-- The positions of the first tokens equal to `t`. -/
def firstPos (s : String) (t : String) (n : Nat) : List Nat :=
  (((tokens s).zipIdx.filter fun p => p.1 = t).map (·.2)).take n

-- the original trees pass
#eval chk 65521 GbN4 hypsN4 [] [] [] rootN4
#eval chk 65521 GbKC hypsKC [] [] [] rootKC
-- the certificate of the cell {0} changed (the first scale `k` of `N`)
#eval (firstPos treeKC "N" 1).map fun k => chk 65521 GbKC hypsKC [] [] [] (parseTree GbKC (patch treeKC (k + 1) "0"))
-- a leaf cofactor coefficient changed (the token after `L k pos t`)
#eval (firstPos treeN4 "L" 3).map fun k => chk 65521 GbN4 hypsN4 [] [] [] (parseTree GbN4 (patch treeN4 (k + 4) "12345"))
-- a strict face certificate scale changed to 0
#eval (firstPos treeKC "F" 3).map fun k => chk 65521 GbKC hypsKC [] [] [] (parseTree GbKC (patch treeKC (k + 1) "0"))
