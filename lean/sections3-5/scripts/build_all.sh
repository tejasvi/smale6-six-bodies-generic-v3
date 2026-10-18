#!/bin/bash
# Full build of the v1 checks, from the root of the Lake package, after `lake exe cache get` (Mathlib).
# Every `native_decide` theorem is evaluated when its module is built; the axioms of all main theorems are printed
# into the log by the modules `L6Check.*.Axioms` and `L6Check.Main`.
set -e
bash scripts/poly/unpack_certs.sh          # plain texts of the certificates (data/f4/certs_txt)
python3 scripts/poly/gen_cert_modules.py   # the modules L6Check/Certs/C<certid>.lean (unchanged if present)
lake build L6Sound L6Check 2>&1 | grep -v '^trace:'
