# F4: cofactor certificates for the cores of Proposition 5.3

Untrusted generators; Lean re-checks everything they produce.

* `certfmt.py`: exact parser of the stored core polynomials, the certificate format (below), and the exact
  check of a certificate file with python-flint (`fmpz_mpoly` products and sums, no Gröbner bases).
* `collect.py IN_DIR OUT_DIR [--replace REPL.jsonl]`: gathers every cell whose exclusion rests on a certified core,
  builds the integer generators, dedupes them, and writes `data/f4/cores.jsonl` (one record per distinct core: the
  generator block, F, V, G, number of cells, references), `data/f4/links/c<N>.txt`, `logs/f4/collect.json`.
* `lift.py RUN_DIR [options]`: one cofactor certificate per distinct core, `data/f4/certs/<certid>.txt` (or
  `.txt.gz`), one JSON record per attempt in `logs/f4/lift.jsonl`. Resumable: existing certificates are skipped
  (with `--force` they are recomputed and the smaller file is kept).
* `altcore.py SYSTEMS.jsonl RUN_DIR [options]`: for cells whose stored core resisted `lift.py`, other cores, i.e.
  other subsets of the cell's initial system (QuickXplain over the full initial system with several equation orders,
  unit-ideal test modulo 32003 at random masses, no saturation; the search only proposes candidates).
* `choose.py RUN_DIR HARDCELLS.txt`: per such cell, among the cores found by `altcore.py` (`logs/f4/altcore.jsonl`,
  with the cell's own names and polynomials), the certified one with the smallest file; writes
  `data/f4/replacements.jsonl`, which `collect.py --replace` applies (the replaced cells and their stored cores are
  listed in `logs/f4/replaced.jsonl`).
* `dropone.py RUN_DIR IDS.txt`: irredundancy test of cores: modulo 32003 at random masses, is the core the unit
  ideal, and is any core with one generator dropped?
* `prune.py RUN_DIR`: keeps in `data/f4/certs/` exactly one file per certificate referenced by a link.
* `check.py IN_DIR RUN_DIR [--replace REPL.jsonl --systems SYSTEMS.jsonl]`: second check by a separate code path:
  every link line against the engine data parsed with SymPy (generators, names, renaming), every (name, polynomial)
  pair of a replacement core against the cell's stored initial system, and every referenced certificate with
  `certfmt.verify_cert`; writes `logs/f4/check.json`.
* `summary.py RUN_DIR`: writes `logs/f4/SUMMARY.md`.

## Input (`IN_DIR`)

The engine data of the run (tag generic-v1), flattened to one directory:
`exact6/c<N>/cert.jsonl` and `exact6/c<N>/sec/p*.cores.jsonl` for every class that has them; the second-pass outputs
`alt_out.jsonl` and `alt3_out.jsonl`; the first-pass leftovers `uncertified.json`; the list of the 43 open cells
`GENERIC_OPEN.txt`; and `single_term.txt`, one line `class cell` per cell excluded by a single term (the records of
`exact6/c<N>/sec/p*.sec.jsonl` with the key `excluded_by`).

Selection, as in the engine:

* first pass (Lemma 5.2(a)): a record of `sec/p*.cores.jsonl` with `verified_modp` whose core hash (the engine's
  canonical hash of `core_sym`: the hash with saturation set if it occurs in `cert.jsonl`, else the hash of the
  equations alone) has `dim_Qm = -1` in the class's `cert.jsonl`, and whose cell is not a single-term cell;
* second pass (Lemma 5.2(b)): the records with `"certified": true` of `alt_out.jsonl` and `alt3_out.jsonl`; the
  fixed mass F is the mass of least index occurring in `core_sym`.

## Generators

Each core polynomial (a string of `core_sym`, masses `m0..m5`, cell variables `X<v>_<i>`, `Y<v>_<i>`, `D<k>_<l>`,
`E`) is parsed exactly over Q. It is multiplied by the lcm of the denominators of its coefficients (this is 2 for the
partial virials with coefficients 1/2 and 1 for all other identities; nothing else is scaled), and then, if F >= 0,
m_F is replaced by 1. The cell variables are renamed x0..x(V-1) in the order of their first appearance in the stored
core strings (generators in the stored order, each read left to right); only variables that occur in the resulting
generators are kept (in the stored data every variable of a string occurs). The generator block of the certificate
(below) is determined by V, F and the ordered generators; identical blocks are stored once.

## Certificates (`data/f4/certs/<certid>.txt`, `.txt.gz`)

The file starts with the *generator block*:

```
L6CERT 1
nmass 6 nvar V fixed F
ngens G
gen 0 T
<T term lines>
...
gen G-1 T
<T term lines>
```

followed by `cof 0 T` ... `cof G-1 T` and `h T`, each with its term lines. A term line is
`c e0 e1 e2 e3 e4 e5 k v1 a1 ... vk ak` (integer coefficient c != 0, exponents of m0..m5, then k pairs
variable index / exponent >= 1 with strictly increasing variable indices). Within each polynomial the terms are
distinct and sorted in decreasing lexicographic order of the exponent vector (e0..e5, a_x0..a_x(V-1)). No comment
lines are written. Every line, including the last, ends with a newline.

* `certid` = the first 16 hexadecimal digits (lower case) of the SHA-256 of the generator block, i.e. of the bytes
  of the file from its first byte up to and including the newline that ends the last term line of generator G-1.
* Claim (checked by `certfmt.verify_cert` on the written file, and to be checked by Lean):
  `sum_i cof_i * gen_i = h` in Z[m0..m5, x0..x(V-1)], `h` has no variable x_j, `h(3,5,7,11,13,17) != 0` with m_F
  replaced by 1 if F >= 0, and m_F occurs nowhere if F >= 0.
* Files whose text exceeds 10,000,000 bytes are stored gzipped as `<certid>.txt.gz` (gzip -6 of the same text);
  all others as plain `<certid>.txt`.

How the cofactors are computed (`lift.py`, Singular 4.4.1; no saturation and no extra variable in any method):

* `lift` (default): ring `(0,m0,...,m5),(x0,...,x(V-1)),dp` for F = -1 and `(0, the five masses other than m_F),
  (x...),dp` for F >= 0; `matrix T = lift(I, ideal(1))` for the ideal I of the generators;
* `liftstd`, `liftstd_slimgb`: the same rings; `liftstd(I, T)` (with the slimgb algorithm for the second); the
  standard basis is one nonzero constant c of Q(m), and the cofactors are the first column of T divided by c;
* `elim`, `elim_slimgb`: the masses (all six, or the five other than m_F) are ring variables, ordering
  `(dp(V),dp(#masses))`, so that the standard basis computed by `liftstd` contains elements of Q[m] (the ideal
  contains a nonzero h(m) because it is the unit ideal over Q(m)); the one with the fewest terms is taken, and its
  column of the transformation matrix gives the cofactors.

In all methods the cofactor vector is then multiplied by one common element of Q(m) that clears all denominators
(`cleardenom` of the vector), mapped (`imap`) to the ring `0,(x0,...,x(V-1),m0,...,m5),dp`, and there h is the sum
of the products, an element of Z[m]. Any remaining rational coefficients would be cleared by one common integer
(`int_scale` in the log; it was 1 in all runs). `--order` and `--varorder` select another monomial order or another
order of the ring variables (the certificate always uses the canonical indices).

## Replaced cores

For 35 cells the stored core resisted all methods within the time and memory limits (see `logs/f4/SUMMARY.md`).
Smaller subsets of these cores do not help: 33 of the 35 stored cores are irredundant modulo 32003 at random masses
(no generator can be dropped; `dropone.py`, `logs/f4/dropone_hard35.jsonl`), and for the other two the test did not
finish (records with null dimensions there). For these cells `altcore.py` searched other cores of the cell's initial system (from `exact6/c<N>/sec/p*.sec.jsonl`,
record `system`: `eqs_sym`, `names`), each candidate with F = -1 and with F = the least mass index occurring in it;
`choose.py` picks the certified candidate with the smallest file. Lemma 5.2 applies to any subset of the initial
system, so such a link is as good as one to the stored core; its names list is the new core's, in the order found.

## Links (`data/f4/links/c<N>.txt`)

One line per cell of class N whose exclusion rests on a core, sorted by cell:

```
<class> <cell> <certid> <F> <name_0> <name_1> ... <name_{G-1}> | <var_0> <var_1> ... <var_{V-1}>
```

* `class`: the engine class N; `cell`: the 0-based line number of the cell in `exact6/c<N>/cells.jsonl`.
* `certid`: the certificate `data/f4/certs/<certid>.txt[.gz]`; `F`: -1 if all six masses are parameters
  (Lemma 5.2(a); every first-pass core, and some replacement cores), 0..5 if m_F = 1 (Lemma 5.2(b)).
* `name_i`: the identity of generator i, in the stored order (= the order of the generators in the certificate):
  the engine's Python tuple with all spaces and quotes removed, e.g. `(D,1,3)` (distance equation of the pair 13),
  `(S,z,(1,3,4,5))`, `(z,S,(2,))`, `(D,z,1,2)`, `(V,(3,4))`, `(T,(0,2,3,4))`, `(U,)`, `(Ip,)`, `(I,)`, `(UI,)`.
  Tokens contain only letters, digits, commas and parentheses.
* After the separator `|`: the V cell variables; the j-th of them is renamed x_j.

Generator i of the certificate equals: (the initial form, on the cell, of the identity `name_i`, as a polynomial in
the masses and the cell variables over Q) times the lcm of its coefficient denominators, with the renaming applied
and, if F >= 0, m_F replaced by 1.

## Logs

* `logs/f4/collect.json`: the counts of `collect.py` (final, with the replacements); `logs/f4/collect_engine.json`:
  the same without the replacements; `logs/f4/replaced.jsonl`: the replaced cells, with their stored cores.
* `logs/f4/hardcells.txt`: the 35 cells (and their stored cores) for which replacements were searched;
  `logs/f4/hard_systems.jsonl`: their initial systems, as stored by the engine (input of `altcore.py` and
  `check.py --systems`); `data/f4/replacements.jsonl`: the chosen replacement cores (input of `collect.py`).
* `logs/f4/altcore.jsonl`: one record per QuickXplain try of `altcore.py`; `logs/f4/dropone_*.jsonl`: `dropone.py`.
* `logs/f4/check.json`: the result of `check.py`.
* `logs/f4/lift.jsonl`: one record per lift attempt: `certid`, `kind` (`a`: F = -1, `b`: F >= 0),
  `fixed`, `nvar`, `ngens`, `cells` (number of cells linked to the core), strategy (`order`, `varorder`, `method`,
  `timeout`, `tag`), `lift_s` (wall time of the Singular run), `lift_maxrss_mb`, `status` (`ok`; `ok_not_kept`: a
  verified certificate, not kept because a smaller file for the same core exists; `timeout`; `memkill`: stopped by
  the memory watchdog of `lift.py`; `singular_error`, `not_unit`, `verify_failed`, `exception`: none occurred), and
  for `ok`/`ok_not_kept`: `cert_bytes` (text size), `gz_bytes` (if gzipped), `parse_write_s`, `verify_s`, `verify`,
  `h_terms`, `cof_terms`, `int_scale`. The `*.out` files are the console logs of the runs.
* `logs/f4/SUMMARY.md`: counts, sizes, the largest certificates, the replaced cells, the attempts on the ten cores
  that rest on Singular alone, and the sequence of commands.

## Reproduce

See the end of `logs/f4/SUMMARY.md` for the sequence of commands (python-flint 0.9.0, SymPy 1.14, Singular 4.4.1 on
the path; run at nice 10). The certificates are content-addressed, so reruns that certify the same cores produce the
same file names; the cofactors themselves depend on the method that succeeded first or gave the smaller file.
