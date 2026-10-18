import L6F1.Data
import L6Common.SHA256

/-!
# The embedded class files are the published ones

The SHA-256 digests of the embedded strings `n4json`, `n5json`, `n6json` (their UTF-8 bytes, which are the bytes of
the files `data/f1/n4.json`, `data/f1/n5.json`, `data/f1/n6.json`) are those recorded in `data/f1/SHA256SUMS`.
-/

namespace L6F1

open L6.SHA256

theorem n6json_sha256 :
    sha256Hex n6json = "0f2ae5d0e1e8619eeb680c12b04fb168faaa856e43d61b16074df50a874e2ff4" := by native_decide

theorem n5json_sha256 :
    sha256Hex n5json = "48ff5f5c20e74fad036503ead82b7152719d7b581535deae2f898e7d21749d7d" := by native_decide

theorem n4json_sha256 :
    sha256Hex n4json = "2f47a2ddaf56c25336c2ce1dabeade3e3c643971073fc6bfa05b9356a53ba00a" := by native_decide

end L6F1
