#!/bin/bash
# Prepares the data of these checks before `lake build` (run from the root of this package):
#  1. the stored cells: decompresses data/cells/c<N>.jsonl.xz and checks data/cells/SHA256SUMS (the files are those
#     of results/exact6/c<N>/cells.jsonl of the supplement);
#  2. the 1,928 cofactor certificates (1.2 GB): checks the archive parts against data/f4/certs_parts.sha256, unpacks
#     them into data/f4/certs/ and checks data/f4/certs/SHA256SUMS (scripts/poly/verify_certs.sh).
# Usage: bash scripts/fetch_data.sh [PARTS_DIR]
#   PARTS_DIR: a directory that holds the downloaded parts. Without it, the parts are downloaded from the supplement
#   (https://doi.org/10.5281/zenodo.23451291) into data/f4/parts/.
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT=$PWD
for f in data/cells/c*.jsonl.xz; do xz -dkf "$f"; done
(cd data/cells && sha256sum --quiet -c SHA256SUMS) && echo "cells: all $(wc -l < data/cells/SHA256SUMS) files match data/cells/SHA256SUMS"
DIR=${1:-data/f4/parts}
mkdir -p "$DIR"
DIR=$(cd "$DIR" && pwd)
if [ $# -eq 0 ]; then
  while read -r h name; do
    if [ -f "$DIR/$name" ] && [ "$(sha256sum < "$DIR/$name" | cut -d' ' -f1)" = "$h" ]; then continue; fi
    curl -fL --retry 5 -o "$DIR/$name" "https://zenodo.org/records/23451291/files/$name?download=1"
  done < data/f4/certs_parts.sha256
fi
(cd "$DIR" && sha256sum --quiet -c "$ROOT/data/f4/certs_parts.sha256") && echo "parts: all $(wc -l < data/f4/certs_parts.sha256) match data/f4/certs_parts.sha256"
cat $(awk -v d="$DIR" '{print d "/" $2}' data/f4/certs_parts.sha256) | xz -d | tar -x
bash scripts/poly/verify_certs.sh
