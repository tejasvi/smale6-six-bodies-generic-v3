import Lean6.Special.Comp.K4.C4.Sys
import Lean6.Special.Comp.K4.C4.GB
/-! Print the chart equations of `Comp.C4.chartEqs` (integer coefficients, normalized) for the comparison with
the inputs of the d64 programs (`gen/c4/compare_d64.py`). Run: `lake env lean gen/c4/dump_eqs.lean`. -/
open Lean6.Special.Comp

def showPoly (f : Poly Int) : String :=
  String.intercalate ";" ((Poly.normalize intC f).map fun t =>
    toString t.1 ++ ":" ++ String.intercalate "," (((GB.pad 9 t.2).take 9).map toString))

def names : List String := ["s", "t", "p12", "p13", "p14", "p23", "p24", "p34", "c"]

#eval show IO Unit from do
  for μ in [[3, 5, 7, 11], [1, 1, 1, 1]] do
    for ch in C4.charts do
      let nm := names.getD ch.1 "?" ++ "_" ++ names.getD ch.2 "?"
      for f in C4.chartEqs μ ch do
        IO.println s!"{μ}|{nm}|{showPoly f}"
