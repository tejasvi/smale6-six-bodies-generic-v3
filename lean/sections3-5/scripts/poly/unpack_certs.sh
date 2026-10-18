#!/bin/bash
# Writes data/f4/certs_txt/<certid>.txt (plain text) for every certificate in data/f4/certs (gunzip of .txt.gz,
# copy of .txt). Run from the package root before building the modules that embed the certificates.
set -e
mkdir -p data/f4/certs_txt
for f in data/f4/certs/*.txt data/f4/certs/*.txt.gz; do
  [ -e "$f" ] || continue
  b=$(basename "$f"); id=${b%%.*}
  out=data/f4/certs_txt/$id.txt
  [ -s "$out" ] && continue
  case "$f" in *.gz) gunzip -c "$f" > "$out.tmp" && mv "$out.tmp" "$out";; *) cp "$f" "$out";; esac
done
ls data/f4/certs_txt | wc -l
