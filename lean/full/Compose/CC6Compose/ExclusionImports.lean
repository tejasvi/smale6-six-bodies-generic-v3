import CC6Compose.Cells
import L6Check.F34S.All

/-!
# Bridge: the imports of the exclusion of the cells (Proposition 5.3)

The certificate project's checks of Proposition 5.3 on the cells of the specification search
(`L6.F34S.Checks.f34s_excluded` and the chunk theorems `L6.F34S.Checks.F34S_c<class>_k<k>`), with the bridge of
Proposition 4.5 (`CC6Compose.Cells`).

These checks are used rather than those on the stored cells themselves (`L6.F34.Checks.F34_all_meaning`): the latter
read each stored line with a JSON parser applied to the whole line (`L6.F34.cellCtx`), while the key of the cell of a
germ (`L6.F2S.keyOfLine`, Proposition 4.5) is read from substrings of the line, and relating the two readings would
need facts about the parser. The checks of `L6F34S` read the trees of a line from the same substrings as
`L6.F2S.keyOfLine`, and state their meaning at every pair of trees with heights satisfying `Cond`.
-/
