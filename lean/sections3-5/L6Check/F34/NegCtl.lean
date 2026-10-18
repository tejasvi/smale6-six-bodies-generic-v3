import L6Check.F34.Debug

/-! Negative controls of the F3/F4 checker (inputs made by `scripts/f34/negctl.sh`); every run must print ERROR,
and the control runs on the original inputs must not. -/

open L6.F34

-- original inputs (must pass)
#eval runDebugWith 14 14 0 2 "data/f34/single/c14.txt" "data/f4/links/c14.txt" "data/f4/certs_txt"
-- NC1: a single-term claim with a term that is not the least
#eval runDebugWith 14 14 0 1 "data/f34/negctl/single_c14_nc1.txt" "data/f4/links/c14.txt" "data/f4/certs_txt"
-- NC2: a certificate generator with a changed coefficient
#eval runDebugWith 14 14 1 2 "data/f34/single/c14.txt" "data/f4/links/c14.txt" "data/f34/negctl/certs"
-- NC3: the cells of class 14 against the diagram of class 15
#eval runDebugWith 14 15 0 40 "data/f34/single/c14.txt" "data/f4/links/c14.txt" "data/f4/certs_txt"
-- NC4: two core names exchanged
#eval runDebugWith 14 14 1 2 "data/f34/single/c14.txt" "data/f34/negctl/links_c14_nc4.txt" "data/f4/certs_txt"
-- run 093110
-- run 093630
