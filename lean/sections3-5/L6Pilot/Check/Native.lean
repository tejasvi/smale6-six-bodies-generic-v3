import L6Pilot.Native
namespace L6

def insL (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insL x ys

def listWorkL (rounds len : Nat) : Nat := Id.run do
  let mut acc := 0
  let mut seed := 12345
  for _ in [0:rounds] do
    let mut l : List Nat := []
    for _ in [0:len] do
      seed := (seed * 1103515245 + 12345) % 2147483648
      l := insL (seed % 1000) l
    acc := (acc + l.headD 0 + l.length) % 1000000007
  return acc

#eval listWork 2000 300
#eval floatWork 10000000

set_option profiler true in
theorem pilot_native : listWork 2000 300 = listWork 2000 300 := by native_decide

set_option profiler true in
theorem pilot_interp : listWorkL 2000 300 = listWorkL 2000 300 := by native_decide

end L6
