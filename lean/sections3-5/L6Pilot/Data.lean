/-! Pilot: parsing an embedded data string. -/
namespace L6

/-- Sum of all decimal integers in a string, scanning bytes. -/
def sumInts (s : String) : Nat := Id.run do
  let b := s.toUTF8
  let mut acc := 0
  let mut cur := 0
  let mut inNum := false
  for i in [0:b.size] do
    let c := b[i]!
    if c ≥ 48 && c ≤ 57 then
      cur := cur * 10 + (c.toNat - 48)
      inNum := true
    else
      if inNum then
        acc := acc + cur
      cur := 0
      inNum := false
  if inNum then acc := acc + cur
  return acc

end L6
