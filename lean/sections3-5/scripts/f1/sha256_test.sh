#!/bin/bash
# Compares L6.SHA256 with sha256sum on test files of many lengths (0..200 bytes and larger, random bytes, covering
# every padding case) and on the data files. Run from the root of the Lake package: scripts/f1/sha256_test.sh
set -e
T=$(mktemp -d)
for n in $(seq 0 200) 1000 4095 4096 4097 65535 65536 100000 1000000; do
  head -c "$n" /dev/urandom > "$T/r$n.bin"
done
FILES="$T/*.bin data/f1/n4.json data/f1/n5.json data/f1/n6.json"
sha256sum $FILES | sed "s|$T/||" > "$T/ref.txt"
lake env lean --run scripts/f1/sha256_test.lean $FILES | sed "s|$T/||" > "$T/lean.txt"
echo "files: $(wc -l < "$T/ref.txt")"
if cmp -s "$T/ref.txt" "$T/lean.txt"; then echo "all digests agree with sha256sum"; else echo "MISMATCH"; diff "$T/ref.txt" "$T/lean.txt" | head; fi
grep json "$T/lean.txt"
rm -rf "$T"
