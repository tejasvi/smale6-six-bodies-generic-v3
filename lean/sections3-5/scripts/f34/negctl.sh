#!/bin/bash
# Negative controls of the F3/F4 checker (run from the package root after scripts/poly/unpack_certs.sh):
# writes corrupted copies of inputs of class 14 to data/f34/negctl/; L6Check/F34/NegCtl.lean runs the checker on them
# and every run must report an ERROR.
set -e
d=data/f34/negctl
mkdir -p $d/certs
# NC1: cell 0 is excluded by the term (SP,w,0) of (S,w,(0,2,3,4)); claim the term (SP,w,2) instead
sed '1s/(SP,w,0)$/(SP,w,2)/' data/f34/single/c14.txt > $d/single_c14_nc1.txt
# NC2: certificate f49e989c4ec0f718 (cell 1) with the first coefficient of generator 0 tripled
awk 'BEGIN{done=0} /^gen 0 /{print; getline; if(!done){$1=3*$1; done=1}; print; next} {print}' \
  data/f4/certs_txt/f49e989c4ec0f718.txt > $d/certs/f49e989c4ec0f718.txt
# NC4: cell 1 with its first two core names exchanged
awk '$2==1{t=$5; $5=$6; $6=t} {print}' data/f4/links/c14.txt > $d/links_c14_nc4.txt
diff <(head -1 data/f34/single/c14.txt) <(head -1 $d/single_c14_nc1.txt) || true
diff data/f4/certs_txt/f49e989c4ec0f718.txt $d/certs/f49e989c4ec0f718.txt | head -4 || true
diff data/f4/links/c14.txt $d/links_c14_nc4.txt | head -4 || true
