#!/bin/bash
# Restores the cofactor certificates of the kernel checks before `scripts/kern/build.sh` (run from the root of this
# package): checks the archive parts against data/kern/kcert_parts.sha256, unpacks them into data/kern/cert/
# (<name>.xz for each file of data/kern/SHA256SUMS) and checks that `xz -d` of each gives the digest that
# data/kern/SHA256SUMS lists.
# Usage: bash scripts/fetch_kern_certs.sh [PARTS_DIR]
#   PARTS_DIR: a directory that holds the downloaded parts. Without it, the parts are downloaded from the supplement
#   (https://doi.org/10.5281/zenodo.23451291) into data/kern/parts/.
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT=$PWD
DIR=${1:-data/kern/parts}
mkdir -p "$DIR"
DIR=$(cd "$DIR" && pwd)
if [ $# -eq 0 ]; then
  while read -r h name; do
    if [ -f "$DIR/$name" ] && [ "$(sha256sum < "$DIR/$name" | cut -d' ' -f1)" = "$h" ]; then continue; fi
    curl -fL --retry 5 -o "$DIR/$name" "https://zenodo.org/records/23451291/files/$name?download=1"
  done < data/kern/kcert_parts.sha256
fi
(cd "$DIR" && sha256sum --quiet -c "$ROOT/data/kern/kcert_parts.sha256") && echo "parts: all $(wc -l < data/kern/kcert_parts.sha256) match data/kern/kcert_parts.sha256"
cat $(awk -v d="$DIR" '{print d "/" $2}' data/kern/kcert_parts.sha256) | tar -x
while read -r h name; do
  [ "$(xz -dc "data/kern/cert/$name.xz" | sha256sum | cut -d' ' -f1)" = "$h" ] || { echo "kernel certificate $name: digest differs"; exit 1; }
done < data/kern/SHA256SUMS
echo "kernel certificates: all $(wc -l < data/kern/SHA256SUMS) match data/kern/SHA256SUMS"
