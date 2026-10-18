/-!
# Merge sort with explicit recursors, for the global comparisons of Proposition 3.1

`msort` (`L6K.F1.Sort`) is compiled with `brecOn`; on the 82,712 codes of the global comparison the kernel then needs
about 90 GB. `msortR` is the same merge sort written with the recursors themselves; `L6SoundK.F1.SortR` proves that
it permutes its input, which is all the global comparisons use.
-/

namespace L6K.F1

noncomputable section

/-- Merge of two lists (fuel: at least the total length): if `x ≤ y` then `x` first. -/
def mergeR : Nat → List Nat → List Nat → List Nat :=
  Nat.rec (motive := fun _ => List Nat → List Nat → List Nat)
    (fun a b => a ++ b)
    (fun _ ih a b =>
      List.rec (motive := fun _ => List Nat) b
        (fun x a' _ =>
          List.rec (motive := fun _ => List Nat) a
            (fun y b' _ => Bool.rec (y :: ih a b') (x :: ih a' b) (Nat.ble x y)) b)
        a)

/-- Merge sort with fuel `d` for the depth (`2^d` at least the length). -/
def msortR : Nat → List Nat → List Nat :=
  Nat.rec (motive := fun _ => List Nat → List Nat)
    (fun l => l)
    (fun _ ih l =>
      List.rec (motive := fun _ => List Nat) []
        (fun x t _ =>
          List.rec (motive := fun _ => List Nat) [x]
            (fun _ _ _ => mergeR l.length (ih (l.take (l.length / 2))) (ih (l.drop (l.length / 2)))) t)
        l)

end

end L6K.F1
