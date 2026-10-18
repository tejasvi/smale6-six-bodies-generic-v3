import L6K.F2S.Keep

/-!
# `keepK` with explicit recursors, for the kernel

`keepR T rows nv` decides like `keepK T (Array.mk rows) nv`, on a list of rows and with the recursors themselves:
the hash in one pass (`hashR`: the number of rows and the last row), and the certificate check `checkR` in one pass
over the rows, applying the entries of a certificate in increasing order of row index (`combR`; a certificate whose
indices do not increase is rejected). The check computes `lean6`'s `Farkas.combine` on lists.
-/

namespace L6K.F2S

open L6

noncomputable section

/-- The number of rows of a list and its last row. -/
def lenLastR : List Row → Nat × Option Row :=
  List.rec (motive := fun _ => Nat × Option Row) (0, none)
    (fun r _ ih => (ih.1 + 1, Option.rec (motive := fun _ => Option Row) (some r) (fun l => some l) ih.2))

/-- `rowsHash` of the rows (`L6K.F2S.Keep`). -/
def hashR : List Row → Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun r rest _ => mix (rowHash (rowHash ((lenLastR rest).1 + 1) r)
      (Option.rec (motive := fun _ => Row) r (fun l => l) (lenLastR rest).2)) 1)

/-- `v + y · a` coordinatewise, on the coordinates of `v` (missing entries of `a` read as `0`). -/
def axpyR (y : Int) : List Int → List Int → List Int :=
  List.rec (motive := fun _ => List Int → List Int) (fun _ => [])
    (fun v _ ih a => List.rec (motive := fun _ => List Int) (v :: ih []) (fun x a' _ => (v + y * x) :: ih a') a)

/-- One entry `(i, y)` of a certificate applied to the state `(Σ y a, Σ y c, Σ y b)` with the row `r`. -/
def stepR (r : Row) (y : Int) (acc : Option (List Int × Int × Int)) : Option (List Int × Int × Int) :=
  Option.rec (motive := fun _ => Option (List Int × Int × Int)) none
    (fun st =>
      if y = 0 then some st
      else if !r.monotone then none
      else Option.rec (motive := fun _ => Option (List Int × Int × Int)) none
        (fun bd => some (axpyR y st.1 r.a.toList, st.2.1 + y * r.c, st.2.2 + y * bd)) (r.bound? y)) acc

/-- The pass over the rows `i, i + 1, …` with the remaining entries `cs` (increasing indices). -/
def combR : List Row → Nat → List (Nat × Int) → Option (List Int × Int × Int) → Option (List Int × Int × Int) :=
  List.rec
    (motive := fun _ => Nat → List (Nat × Int) → Option (List Int × Int × Int) → Option (List Int × Int × Int))
    (fun _ cs acc => List.rec (motive := fun _ => Option (List Int × Int × Int)) acc (fun _ _ _ => none) cs)
    (fun r _ ih i cs acc =>
      List.rec (motive := fun _ => Option (List Int × Int × Int)) acc
        (fun e cs' _ => if e.1 = i then ih (i + 1) cs' (stepR r e.2 acc) else ih (i + 1) cs acc) cs)

/-- `Farkas.check` on a list of rows (entries in increasing order of index). -/
def checkR (n : Nat) (rows : List Row) (cert : List (Nat × Int)) : Bool :=
  Option.rec (motive := fun _ => Bool) false
    (fun st =>
      let gm := if st.2.1 < 0 then -st.2.1 else 0
      st.1.all (· == 0) && decide (st.2.2 + gm ≤ 0) && (decide (0 < st.2.1 + gm) || decide (st.2.2 + gm < 0)))
    (combR rows 0 cert (some (List.replicate n 0, 0, 0)))

/-- The certificates of a hash, tried one after the other. -/
def anyR (n : Nat) (rows : List Row) : List (List (Nat × Int)) → Bool :=
  List.rec (motive := fun _ => Bool) false (fun c _ ih => checkR n rows c || ih)

/-- **The decision from data**, on a list of rows. -/
def keepR (T : CTree) (rows : List Row) (nv : Nat) : Bool := !anyR nv rows (T.find (hashR rows))

end

end L6K.F2S
