# Hand explanations of the 91,273 cells

The paper (Section 9) explains every nonpositive cell of the engine by hand mechanisms as well; the files here hold
the notes, the programs that check the hypotheses of their lemmas on the stored cells, and an independent check.

* `MECHANISMS.md` and `RESIDUAL.md`: the notes as the paper cites them (version 2). Each begins with the list of its
  changes from the refereed version: those required by the referee report and those found by the re-run of the
  programs before release.
* `refereed/MECHANISMS.md` and `refereed/RESIDUAL.md`: the versions that the referee report reviewed, unchanged.
* `mechanisms/` and `residual/`: the programs (`scripts/`), the Singular and SymPy checks of the algebra of the
  lemmas (`checks/`, with their outputs), and the outputs of the programs (`data/`). The paths of programs and data
  in each note are relative to its directory here.
* `independent/`: an independent re-implementation of the hypothesis checks and of the classification of all cells
  (`final_classification.jsonl`: one line per cell, with its tier, lemmas, template and diagram class), with
  `REFEREE_REPORT.md`, its programs and their outputs (`scripts/`) and its Singular checks (`sing/`).
* `inputs/`: files of the engine that the programs read (the labels of the certified cores and their types).
* `audit/`: the coverage of the cells by the lemmas of Section 9 from both classifications, compared cell by cell
  (Proposition 9.23 and the counts after it), the polynomials of Lemmas 9.13 and 9.14 in the 74 cells where they are
  needed, the classes with an isolated zw-triangle without circles, and the rerun of the independent checkers from a
  fresh copy (`rerun/`, compared with the stored outputs in `rerun_compare.txt`).

The commands that re-run everything, and the record of the re-run of 2026-10-17, are in `README.md` at the root of
the supplement (section "Hand explanations").
