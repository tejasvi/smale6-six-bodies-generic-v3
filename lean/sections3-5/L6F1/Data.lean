/-!
# The embedded class files

The files `data/f1/n4.json`, `data/f1/n5.json`, `data/f1/n6.json` (copies of the outputs of the enumeration program
of Proposition 3.1) and `data/f1/chang_chen_117.txt` (the 117 diagrams of Chang and Chen, converted from a
transcription by `scripts/f1/cc_convert.py`), embedded as strings. Their SHA-256 digests are checked in
`L6Check.F1.Sha` and `L6Check.F1.ChangChen`.
-/

namespace L6F1

/-- The classes of labelled diagrams on four bodies (`n4.json`). -/
def n4json : String := include_str "../data/f1/n4.json"

/-- The classes of labelled diagrams on five bodies (`n5.json`). -/
def n5json : String := include_str "../data/f1/n5.json"

/-- The classes of labelled diagrams on six bodies (`n6.json`). -/
def n6json : String := include_str "../data/f1/n6.json"

/-- The 117 diagrams of Chang and Chen (`chang_chen_117.txt`). -/
def ccData : String := include_str "../data/f1/chang_chen_117.txt"

end L6F1
