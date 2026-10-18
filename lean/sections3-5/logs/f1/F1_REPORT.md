# F1: Proposition 3.1 (the diagrams) in Lean 4

Proposition 3.1: exactly 82,712 labelled diagrams on six bodies satisfy the combinatorial parts of the rules (E1)–(E6),
(C1)–(C4) of Lemma 2.11 in both colours, and up to relabelling and exchange of the colours they form 191 classes.
The proof's search leaves 932,677 kind assignments after (E2), (E3), (E6). The program's checks: 41 diagrams in 5
classes for four bodies, 1376 in 24 classes for five bodies.

All of this is proved in Lean 4 (toolchain v4.35.0-rc3, Mathlib as pinned in `lake-manifest.json`): the computations
are evaluated by `native_decide` as compiled code, and everything else is proved, without `sorry`.

## Files

| file | contents |
|---|---|
| `L6F1/Rules.lean` | labelled diagrams (`Diagram`: edge code, two circle masks), kinds, strokes, components, the rules `ruleE1`–`ruleE6`, `ruleC1`–`ruleC4` written from Lemma 2.11 with explicit quantifiers, `rulesZ` (one colour), `okRules` (both colours), colour exchange `swapE`, relabelling |
| `L6F1/Search.lean` | the search: edge stage (`edgeLeaves`), leaves (`search`), keys (`rawKey`, `rawKeyLex`, `canonKey`), permutations, orbits |
| `L6F1/Json.lean` | reading (`parseFile`) and writing (`renderFile`) of the class files |
| `L6F1/Check.lean` | `checkAll`: all checks of one number of bodies in one Boolean function |
| `L6F1/ChangChen.lean` | reading, writing and checks of the list of Chang and Chen |
| `L6F1/Data.lean` | the embedded files (`include_str`) |
| `L6Common/SHA256.lean` | SHA-256 |
| `L6Sound/F1/Basic.lean` | digits, kinds, sorted lists |
| `L6Sound/F1/Complete.lean` | completeness of the search (`mem_search`) |
| `L6Sound/F1/Orbit.lean` | relabelling, exchange, extensionality, symmetries `actP`, orbits, group law |
| `L6Sound/F1/Component.lean` | the components used in (C3) are the connected components |
| `L6Sound/F1/Classes.lean` | permutations, `canonKey` invariance, `classification_of_check` |
| `L6Check/F1/N6.lean`, `N5.lean`, `N4.lean` | `check_n6`, `check_n5`, `check_n4` (`native_decide`) |
| `L6Check/F1/Sha.lean` | SHA-256 of the embedded class files (`native_decide`) |
| `L6Check/F1/Main.lean` | `F1_main` and the corollaries |
| `L6Check/F1/ChangChen.lean` | `check_cc`, `ccData_sha256`, `F1_chang_chen` |
| `L6Check/F1/Axioms.lean` | prints the statements and the axioms into the build log |
| `data/f1/` | `n4.json`, `n5.json`, `n6.json` (copies of the program's outputs), `chang_chen_117.txt`, `SHA256SUMS` |
| `scripts/f1/` | `build.sh` (the build), `sha256_test.sh`/`.lean` (test against `sha256sum`), `sha256_constants.py`, `cc_convert.py` |

## The rules (`L6F1/Rules.lean`)

A labelled diagram on `n` bodies is a triple of natural numbers `(e, zc, wc)` with `e < 4^(n(n-1)/2)`,
`zc, wc < 2^n`: the digit of `e` in base 4 at the position of the pair `{a, b}` (order `01, 02, 12, 03, 13, 23, 04, …`)
is its kind (0 none, 1 `z`, 2 `w`, 3 `zw`), bit `k` of `zc` (`wc`) says that body `k` is `z`- (`w`-)circled.
`rulesZ n e c` is the conjunction of the ten rules in the colour `z`, each a `decide` of a statement with bounded
quantifiers over the bodies (e.g. (E6): for distinct `a, b, c, d < n`, if `ab, bc, cd, da` are edges then
`kind ab = kind cd` and `kind bc = kind da`); (E3) and (E6) are on the kinds. The component of (C3) is computed by
growth from `k` (`component`); `L6Sound.F1.Component.mem_component_iff` proves it is the set of bodies joined to `k`
by a walk of strokes. **Both colours**: `okRules n d = rulesZ n d.e d.zc && rulesZ n (swapE n d.e) d.wc`, the rules for
`d` and for the diagram with `z` and `w` exchanged. The search uses no tables: its checks are instances of these rule
definitions. Two `@[csimp]` lemmas (`digit_eq_digitShift`, `bit_eq_bitShift`, proved) let the compiled code extract
digits and bits by shifts.

## Theorems

| theorem | statement (in words) |
|---|---|
| `check_n6` | `checkAll 6 false n6json 932677 82712 191 = true` (`native_decide`): the edge stage has 932,677 leaves, distinct, each `< 4^15` satisfying (E2), (E3), (E6); the search lists 82,712 labelled diagrams, distinct, each in range and satisfying `okRules 6`; `perms 6` lists 720 distinct permutations; `n6.json` is parsed as `(6, 82712, cls)` with 191 classes and written back byte for byte; each representative is in range, its orbit (1440 images, deduplicated) has the listed size, and its `rawKey` is the least over the orbit; the keys increase strictly along the file; the orbits put together, sorted, equal the sorted codes of the search |
| `check_n5`, `check_n4` | the same for `n5.json` (18,918; 1376; 24) and `n4.json` (633; 41; 5), with `rawKeyLex` (the key of the program for four and five bodies) |
| `n6json_sha256`, `n5json_sha256`, `n4json_sha256` | the SHA-256 of the embedded strings is `0f2ae5d0…2ff4`, `48ff5f5c…7d9d`, `2f47a2dd…a00a` |
| `mem_search` | **completeness**: every labelled diagram on `n` bodies (any `n`) satisfying `okRules n` is listed by `search n` |
| `classification_of_check` | for `n ≤ 6`, `checkAll … = true` implies the statement below with the given numbers |
| **`F1_main`** | **Proposition 3.1**: `#{d ∈ allDiagrams 6 : okRules 6 d} = 82712`; `#{e < 4^15 : edgeRules 6 e} = 932677`; `parseFile n6json = some (6, 82712, classes6)`, `renderFile 6 82712 classes6 = n6json`, `classes6.length = 191`; `d ∈ allDiagrams 6 ∧ okRules 6 d ↔ ∃ x ∈ classes6, d ∈ orbit 6 x.1`; the orbits of the representatives are pairwise disjoint; `(orbit 6 x.1).ncard = x.2`; `rawKey 6 x.1 ≤ rawKey 6 d` for `d` in its orbit, and `canonKey 6 false x.1 = rawKey 6 x.1`; the keys increase strictly along the file. `orbit 6 d` is the set of the images of `d` under `actP 6 σ s` for all `σ : Equiv.Perm (Fin 6)` and `s : Bool` |
| `F1_one_representative` | each orbit of a labelled diagram on six bodies satisfying the rules contains exactly one representative of `n6.json` |
| `F1_reps_distinct_orbits` | the representatives lie in pairwise different orbits |
| `F1_canonKey_invariant` | `canonKey 6 false (actP 6 σ s d) = canonKey 6 false d` for every labelled diagram `d` (general `n ≤ 6`: `canonKey_actP`; group law: `actP_actP`) |
| `F1_n5`, `F1_n4` | Proposition-3.1-style statements for five bodies (1376 diagrams, 18,918 kind assignments, 24 classes of `n5.json`) and four bodies (41, 633, 5 classes of `n4.json`) |
| `F1_chang_chen` (optional claim) | the 117 diagrams of `data/f1/chang_chen_117.txt` (read back identically) satisfy `okRules 6`, and there is an injective map `f` from them to the classes of `n6.json` with each diagram in the orbit of the representative of its class: they lie in 117 distinct classes (`check_cc`: rules and pairwise distinct canonical keys; `ccData_sha256`: `f01acbf5…fe86`) |

The counts are in the statements printed by `L6Check/F1/Axioms.lean` into `logs/f1/build.log`: `F1_main` lines 179–190
(82712, 932677, 191), `F1_n5` lines 198–210 (1376, 18918, 24), `F1_n4` lines 211–223 (41, 633, 5), `F1_chang_chen`
lines 227–234 (117).

## Axioms (`logs/f1/axioms.log`)

Every theorem depends only on `propext`, `Quot.sound`, `Classical.choice` (all but the SHA and csimp lemmas) and the
auxiliary axioms `….native_decide.ax_1_1` of its `native_decide` theorems (`check_n6`, `check_n5`, `check_n4`,
`check_cc`, the SHA theorems). The proofs in `L6Sound/F1` (`mem_search`, `classification_of_check`, `canonKey_actP`,
`mem_component_iff`, …) use no `native_decide`. No `sorryAx`.

## SHA-256 (`logs/f1/sha256_test.log`)

`L6.SHA256.sha256HexBytes` agrees with `sha256sum` on 212 files: random files of every length 0–200 bytes and of
1000, 4095, 4096, 4097, 65535, 65536, 100000 and 1000000 bytes, and the three class files. The constants were computed
with integer roots (`scripts/f1/sha256_constants.py`).

## Rebuild

From the root of the Lake package, after `lake exe cache get`:

```
scripts/f1/build.sh            # or: lake build L6Common.SHA256 L6F1 L6Sound.F1.Classes L6Sound.F1.Component \
                               #     L6Check.F1.Main L6Check.F1.ChangChen L6Check.F1.Axioms
scripts/f1/sha256_test.sh
```

## Times (clean build of the F1 targets, `logs/f1/build.log`, Mathlib from the cache, 4 Lean threads)

| step | wall |
|---|---|
| `L6Common.SHA256`, `L6F1` (compiled to shared libraries) | 2.7 s |
| `L6Sound.F1.*` (five modules, 1.4–1.7 s each) | 6.1 s |
| `L6Check.F1.Sha`, `N4`, `N5`, `N6` | 26.3 s |
| `L6Check.F1.Main`, `ChangChen`, `Axioms` | 6.1 s |

`native_decide` evaluation: `check_n6` 25.4 s, `check_n5` 297 ms, `check_n4` 6 ms, `check_cc` 784 ms (profiler lines in
`build.log`; the `check_n6`/`check_n5` lines repeated under the last step are messages replayed from the cache).

## Not done

* The "Rule T" claim after Proposition 3.1 (eight of the 74 classes outside Chang and Chen's list violate only the
  triangle rule) needs an implementation of the further rules of Chang and Chen's §3; it is not checked here.
* `chang_chen_117.txt` is a conversion (`scripts/f1/cc_convert.py`) of a transcription of their figures (source SHA-256
  recorded in the file header); `F1_chang_chen` is relative to that transcription. Its ten diagrams of Table 1 agree
  with the paper.
