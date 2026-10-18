# F3, F4: single-term exclusions and the links of the cores to the cells (Proposition 5.3)

Untrusted generators; the Lean checks (`L6F34`, `L6Check/F34`) re-check everything they use.

## Inputs (shared, read-only)

* `data/cells/c<N>.jsonl`: the stored cell lists of the 191 classes (byte for byte the engine's `cells.jsonl`; cell
  index = line number, from 0), with `data/cells/SHA256SUMS`;
* `data/cells/open43.tsv`: the 43 cells of Proposition 5.3 left to Sections 6 and 7 (`class`, Chang–Chen number,
  `cell`);
* `data/f1/n6.json`: the class representatives;
* `data/f4/links/c<N>.txt` and the certificates `data/f4/certs/` (see `scripts/f4/README.md`), embedded through the
  shared modules `L6Check/Certs/C<certid>.lean` (made by `scripts/poly/gen_cert_modules.py`, from the plain texts
  that `scripts/poly/unpack_certs.sh` writes to `data/f4/certs_txt/`).

## Generated data

`single.py EXACT_COLLECT_DIR ALT_OUT ALT3_OUT LINKS_DIR data/f34 logs/f34/single_summary.json` reads the engine's
stored runs (`exact6/c<N>/sec/p*.sec.jsonl`, the second-pass outputs `alt_out.jsonl`, `alt3_out.jsonl`) and writes:

* `data/f34/single/c<N>.txt`: one line per cell excluded by a single term (Lemma 5.1), sorted by cell:
  `<cell> <identity> <term>`, the engine's tuples without spaces and quotes, e.g. `12 (T,(0,2,3)) (T1,0,5)`
  (from the records with the key `excluded_by`);
* `data/f34/pass/c<N>.txt`: one line per cell of `data/f4/links/c<N>.txt`: `<cell> <pass>`, pass `2` for the cells
  certified by the second pass (`certified: true` in `alt_out.jsonl`, `alt3_out.jsonl`), `1` otherwise. The pass tags
  only label the counts.

Counts written (`logs/f34/single_summary.json`): 52,432 single-term cells (in 25 classes), 37,808 pass-1 and 990
pass-2 core cells.

## Lean modules

`gen_checks.py [CHUNK]` (default 1,500 cells per chunk) writes:

* `L6Check/F34/Data/Common.lean`, `Data/C<N>.lean`: the embedded files (`include_str`);
* `L6Check/F34/C<N>K<k>.lean`: per chunk of consecutive cells, the theorem
  `F34_c<N>_k<k> : checkChunk N n6 cells_N single_N links_N pass_N open43 [(certid, L6.Certs.C<certid>), …] lo hi
  {single := …, core1 := …, core2 := …, opn := …} = true` (by `native_decide`; the counts are computed here from the
  same files and checked by Lean);
* `L6Check/F34/Cover.lean`: `F34_cover`, the number of cells of every class (all 191);
* `L6Check/F34/Sha.lean`: `F34_sha_cells`, `F34_sha_n6`, the SHA-256 of the embedded cell lists and of `n6.json`;
* `L6Check/F34/Main.lean`: the table of chunks, `F34_chunks_cover` (the chunks of each class are consecutive from 0 to
  its number of cells) and `F34_totals`;
* `L6Check/F34/Axioms.lean`: `#print axioms` of every theorem.

`negctl.sh` writes corrupted inputs to `data/f34/negctl/`; `L6Check/F34/NegCtl.lean` runs the checker on them (every
run must report an error). `L6Check/F34/Debug.lean` is a development runner (`runDebug cls lo hi` prints the first
failing cell with a reason, or the counts).

## Commands (from the package root, on a machine with the Mathlib cache)

```
bash scripts/poly/unpack_certs.sh
python3 scripts/poly/gen_cert_modules.py
python3 scripts/f34/gen_checks.py
lake build L6F34 L6Sound.F34.Meaning L6Check.F34.Main L6Check.F34.Axioms
bash scripts/f34/negctl.sh && lake build L6Check.F34.NegCtl
```
