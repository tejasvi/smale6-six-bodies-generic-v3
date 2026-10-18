/-! Pilot: native code for `native_decide` through `precompileModules`. -/
namespace L6

/-- A loop of `n` steps of integer arithmetic. -/
def loopSum (n : Nat) : Nat := Id.run do
  let mut acc : Nat := 0
  for i in [0:n] do
    acc := (acc + i * i) % 1000000007
  return acc

/-- Insertion of a value into a sorted list. -/
def ins (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: ins x ys

/-- A list-heavy workload: insertion sorts of pseudo-random lists. -/
def listWork (rounds len : Nat) : Nat := Id.run do
  let mut acc := 0
  let mut seed := 12345
  for _ in [0:rounds] do
    let mut l : List Nat := []
    for _ in [0:len] do
      seed := (seed * 1103515245 + 12345) % 2147483648
      l := ins (seed % 1000) l
    acc := (acc + l.headD 0 + l.length) % 1000000007
  return acc

/-- A float workload. -/
def floatWork (n : Nat) : Nat := Id.run do
  let mut acc : Float := 0.0
  for i in [0:n] do
    acc := acc + Float.sqrt (i.toFloat) * 1.0000001
  return acc.toUInt64.toNat

end L6
