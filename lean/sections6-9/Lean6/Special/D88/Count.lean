import Lean6.Special.D88.Count.Main

/-!
# Lemma 6.19(b)

`Lean6.Special.D88.Count.count_KC` (dimension at most `4788` for KC′) and `count_S12` (at most `20,316` for S12), at
`μ₀ = (1, 2, 3, 30)` and `p = 65521`, with the systems of §6.7 (`KCprimeEqs`, `S12eqs`, module `Systems`): an F4 engine
in Lean (`Comp.Count.F4`, sound by construction: `f4_good`), the dimension check of the staircase (`dimCheck`,
`dimCheck_sound`), the degree reverse lexicographic order as a Mathlib `MonomialOrder` (`degRevLex`) and Mathlib's
division algorithm (`finrank_le_of_border`).
-/
