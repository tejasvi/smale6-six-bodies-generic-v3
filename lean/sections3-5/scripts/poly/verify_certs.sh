#!/bin/bash
# Checks the 1,928 certificate files in data/f4/certs against data/f4/certs/SHA256SUMS (run from the package root).
# The certificates are distributed separately (1.2 GB); place them in data/f4/certs/ first.
set -e
cd data/f4/certs
sha256sum --quiet -c SHA256SUMS
echo "all $(wc -l < SHA256SUMS) certificate files match SHA256SUMS"
