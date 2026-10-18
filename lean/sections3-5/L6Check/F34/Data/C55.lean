/-! F3/F4: the embedded files of class 55. -/

namespace L6.F34.Data

/-- `data/cells/c55.jsonl`. -/
def cells_55 : String := include_str "../../../data/cells/c55.jsonl"

/-- `data/f34/single/c55.txt`. -/
def single_55 : String := include_str "../../../data/f34/single/c55.txt"

/-- No cell of class 55 rests on a core. -/
def links_55 : String := ""

/-- `data/f34/pass/c55.txt`. -/
def pass_55 : String := include_str "../../../data/f34/pass/c55.txt"

end L6.F34.Data
