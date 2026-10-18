import L6F5
import L6Common.SHA256
import L6Check.F5.Data

/-!
# The embedded files are the published ones

The SHA-256 digests of the embedded cell files (their UTF-8 bytes, which are the bytes of `data/cells/c<N>.jsonl`)
are those recorded in `data/cells/SHA256SUMS`, which has one line for each of the 191 classes; the digests of the
embedded `SHA256SUMS` and `open43.tsv` are those computed by `sha256sum`, and the digest of the embedded `n6.json` is
the published one (also checked by the family F1, `L6F1.n6json_sha256`).
-/

namespace L6F5

open Data L6.SHA256

/-- There are 191 cell files. -/
theorem files_length : files.length = 191 := by decide +kernel

set_option profiler true in
/-- **The digest of each embedded cell file `c<N>.jsonl` is the one recorded in `SHA256SUMS`.** -/
theorem cells_sha256 :
    (List.range 191).all (fun c => sumFor sums s!"c{c}.jsonl" == some (sha256Hex (files.getD c ""))) = true := by
  native_decide

/-- `SHA256SUMS` has 191 lines (and a final newline). -/
theorem sums_lines : (sums.splitOn "\n").length = 192 ∧ (sums.splitOn "\n").getLast? = some "" := by native_decide

/-- The digest of the embedded `SHA256SUMS` (as computed by `sha256sum`). -/
theorem sums_sha256 :
    sha256Hex sums = "deb001fef4cf445f53af88d9c06d20be0ee86dd333a050e50bd9d65fe458b895" := by native_decide

/-- The digest of the embedded `open43.tsv` (as computed by `sha256sum`). -/
theorem open43_sha256 :
    sha256Hex open43 = "bd7a5a9a5ab556b571fce5c533b9fecc7927c967c8f0cb31416a3f8de82da60f" := by native_decide

/-- The digest of the embedded `n6.json`. -/
theorem n6_sha256 :
    sha256Hex n6 = "0f2ae5d0e1e8619eeb680c12b04fb168faaa856e43d61b16074df50a874e2ff4" := by native_decide

end L6F5
