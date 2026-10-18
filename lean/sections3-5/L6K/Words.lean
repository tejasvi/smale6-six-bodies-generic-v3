/-!
# Lists of machine words from one natural-number literal (for the kernel)

`words w c n`: the `c` words of `w` bits of `n`, lowest first, by binary splitting with shifts (linear-size pieces;
the kernel refuses `Nat.pow` results above its numeral limit, so no large powers are formed).
-/
namespace L6K

def wordsAux (w : Nat) : Nat → Nat → Nat → List Nat → List Nat
  | 0, _, _, acc => acc
  | d + 1, c, n, acc =>
    if c ≤ 4 then
      let rec seq : Nat → Nat → List Nat → List Nat
        | 0, _, acc => acc
        | k + 1, n, acc => (n % 2 ^ w) :: seq k (n >>> w) acc
      seq c n acc
    else
      let h := c / 2
      let hi := n >>> (w * h)
      wordsAux w d h (n - (hi <<< (w * h))) (wordsAux w d (c - h) hi acc)

/-- The `c` words of `w` bits of `n`, lowest first. -/
def words (w c n : Nat) : List Nat := wordsAux w 40 c n []

end L6K
