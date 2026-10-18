/-! F3/F4: the embedded files of class 127. -/

namespace L6.F34.Data

/-- `data/cells/c127.jsonl`. -/
def cells_127 : String := include_str "../../../data/cells/c127.jsonl"

/-- `data/f34/single/c127.txt`. -/
def single_127 : String := include_str "../../../data/f34/single/c127.txt"

/-- No cell of class 127 rests on a core. -/
def links_127 : String := ""

/-- `data/f34/pass/c127.txt`. -/
def pass_127 : String := include_str "../../../data/f34/pass/c127.txt"

end L6.F34.Data
