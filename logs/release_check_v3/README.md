# Logs of the developers' release run of version 3

The release run checked the pinned commits (`lean/COMMITS`) from git archives: first the kernel stages of `lean6`
(`lean/sections3-5/`) and of `lean6_special` (`lean/sections6-9/`), then the release check `lean/full/check_v3.sh` with
`L6_STAGES` and `SP_STAGES` empty, on the kernel checks so built. `lean/full/README.md` (Building and checking, Version 3)
summarizes the times and the memory. In these copies, the absolute paths of the build directory are written
`<build-home>` and the user name `<user>`; nothing else is changed.

* `check_v3.log`, `check_v3.start`, `check_v3.end`: the release check (`./check.sh v3`), ending with `check_v3.sh: OK`.
* `sp_stages.log` (with `.start`, `.end`): the kernel stages of `lean6_special` (`scripts/kern/build.sh`).
  `lean6_special_runlogs/`: what this run appended to the files of its `logs/kern` (the committed content of those
  files comes first and is not repeated here).
* `stage2.log` (with `.start`, `.end`): the kernel stages of `lean6` from the libraries to the generator of the fused
  check F2-F4; the fused stage `f34k` was ended there and split over three machines. `f34k_part_box16.*`: the part of
  the first machine. `stage2f.log` (with `.start`, `.end`): the final `build.sh f34k` after the parts' outputs were
  gathered. `lean6_runlogs/`: this run's part of each file of `lean6`'s `logs/kern`, the schedulers of the two other
  machines (`box17/`, `box19/`), the time files of jobs that finished outside a scheduler when the run was split
  (`orphans/`), the split lists (`split/`) and the copy and gather records.
* `lean6_reuse_record.out`, `lean6_reuse_verify.out`: the record of `lean6`'s outputs after the stages (the SHA-256 of
  every file of `out/`) and the verification before the release check (sources against the commit, certificates,
  generated files against the committed lists, `out/` against the record; it ends with `l6reuse: VERIFIED`).
* `mem.log`: memory in use on the first machine, sampled during the run.
