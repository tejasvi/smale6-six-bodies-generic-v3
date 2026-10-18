# The 35 cells checked through a replacement core

F: the mass set to 1 (-1: all six masses are parameters). Attempts: Singular `lift`, `liftstd`, `liftstd` with slimgb, and the elimination method, with the time or memory limit each reached (from `logs/f4/lift.jsonl`); no attempt on a stored core produced a certificate. lift_v1: what the engine's own lift pipeline did with the same cell.

| class | cell | pass | stored core: certid, F, generators | certified core: certid, F, generators | attempts on the stored core | lift_v1 |
|---|---|---|---|---|---|---|
| 3 | 8722 | second | `554cf28bbe3c176c`, 2, 10 | `18a6212a7127e854`, -1, 6 | elim: memory limit (10 GB); lift: timeout 7,200 s, memory limit (10 GB); liftstd: timeout 3,600 s; liftstd_slimgb: memory limit (15 GB) | also replaced |
| 3 | 13414 | second | `3fb29ae96b879aab`, 0, 8 | `f14ef6ce4398650f`, -1, 6 | elim: timeout 1,800 s; lift: timeout 7,200 s, memory limit (9 GB); liftstd: memory limit (12 GB); liftstd_slimgb: timeout 1,800 s | also replaced |
| 3 | 17222 | second | `0c669317b45c3f18`, 1, 10 | `63440898f2dbec78`, 3, 6 | elim: memory limit (10 GB); lift: timeout 7,200 s; liftstd: timeout 3,600 s; liftstd_slimgb: timeout 1,800 s | also replaced |
| 3 | 24725 | second | `304bfbe73dccade5`, 3, 7 | `40e932c9efbff8ca`, 0, 7 | elim: timeout 1,800 s; liftstd_slimgb: memory limit (10 GB) | also replaced |
| 3 | 31232 | second | `12c2ebdf7446ded3`, 3, 7 | `a152f608aaf33d4a`, -1, 4 | elim: timeout 1,800 s; liftstd_slimgb: timeout 1,800 s | also replaced |
| 3 | 31274 | second | `5021f4b8aa02c581`, 3, 7 | `1ae7a9e75141fac8`, 3, 6 | elim: timeout 1,800 s; liftstd_slimgb: memory limit (11 GB) | also replaced |
| 3 | 31294 | second | `a96600ac093191b7`, 3, 7 | `a1d7c492700e0acb`, 0, 4 | elim: memory limit (16 GB); liftstd_slimgb: timeout 1,800 s | also replaced |
| 3 | 32603 | second | `5b64d70cf7765943`, 3, 7 | `5380c10c49621d0a`, 0, 7 | elim: timeout 1,800 s; liftstd_slimgb: timeout 1,800 s | also replaced |
| 3 | 33516 | second | `b7af1da5c9e8d214`, 3, 6 | `c4e4752dac82d237`, 3, 6 | elim: timeout 1,800 s; liftstd_slimgb: timeout 1,800 s | also replaced |
| 3 | 40246 | second | `27f49c33642245f5`, 3, 7 | `45b7edf950821bea`, -1, 4 | elim: memory limit (10 GB); liftstd_slimgb: timeout 1,800 s | also replaced |
| 3 | 41091 | second | `311de1ceb9499b5e`, 0, 8 | `ecbfe587eaa77e7f`, -1, 6 | elim: timeout 1,800 s; lift: timeout 7,200 s; liftstd: timeout 3,600 s; liftstd_slimgb: memory limit (9 GB) | also replaced |
| 3 | 41143 | second | `0b6e5f6afe4cc9bb`, 3, 7 | `840c82e8ce38adf2`, -1, 4 | elim: timeout 1,800 s; lift: timeout 7,200 s; liftstd: timeout 3,600 s; liftstd_slimgb: timeout 1,800 s | also replaced |
| 3 | 42702 | second | `6f90dce812c6e87c`, 3, 7 | `6c61163370247b04`, -1, 6 | elim: timeout 1,800 s; liftstd_slimgb: timeout 1,800 s | also replaced |
| 14 | 218 | second | `919069b72a23260d`, 0, 10 | `b76600618d698a5e`, -1, 4 | elim: memory limit (9 GB); elim_slimgb: memory limit (10 GB); lift: timeout 7,200 s; liftstd: timeout 3,600 s; liftstd_slimgb: timeout 3,600 s | also replaced |
| 14 | 235 | second | `1c7fd2dff66942f8`, 0, 9 | `f0a1d909bb386f2d`, 1, 4 | elim: memory limit (10 GB); liftstd_slimgb: timeout 1,800 s | also replaced |
| 14 | 246 | second | `76b37bbf10824e2d`, 0, 9 | `3f99b20d30c3b6e7`, -1, 4 | elim: memory limit (10 GB); liftstd_slimgb: timeout 1,800 s | also replaced |
| 14 | 258 | second | `f319bd17c47cb72d`, 0, 9 | `e95a3e69b6637b6a`, 1, 4 | elim: memory limit (10 GB); liftstd_slimgb: timeout 1,800 s | also replaced |
| 14 | 260 | second | `8b120e49ff1a484f`, 0, 9 | `f7aff496e481acdf`, 1, 4 | elim: memory limit (10 GB); liftstd_slimgb: timeout 1,800 s | also replaced |
| 14 | 377 | second | `4a818de2c5ea4f29`, 2, 7 | `29f9e03ae6c6af77`, 1, 4 | elim: timeout 1,800 s; liftstd_slimgb: timeout 1,800 s | also replaced |
| 29 | 601 | first | `e1dcf7d3509e5f00`, -1, 10 | `9918437f7b3a297d`, -1, 6 | elim: memory limit (11 GB); lift: memory limit (9 GB); liftstd_slimgb: memory limit (9 GB) | also replaced |
| 29 | 831 | second | `f5a95ac7805ac251`, 1, 12 | `e83ac031d183144d`, 1, 7 | elim: timeout 1,800 s; liftstd_slimgb: timeout 1,800 s | also replaced |
| 29 | 1444 | second | `7a1020554264b34a`, 0, 10 | `fbe4a25afe0be9a8`, -1, 6 | elim: memory limit (10 GB); liftstd_slimgb: timeout 1,800 s | also replaced |
| 29 | 1476 | second | `e0e6f901b35ebcb2`, 1, 7 | `e07ae38753a76d9e`, 2, 6 | elim: memory limit (9 GB); liftstd_slimgb: memory limit (16 GB) | also replaced |
| 29 | 1484 | second | `13aaedb3d5763636`, 0, 9 | `587c52351a8ffff2`, 2, 6 | elim: memory limit (10 GB); liftstd_slimgb: timeout 1,800 s | also replaced |
| 29 | 1508 | second | `e5235da7d0793e20`, 0, 9 | `a5ce291fd63b43b1`, -1, 6 | elim: memory limit (11 GB); liftstd_slimgb: timeout 1,800 s | also replaced |
| 29 | 1518 | second | `cf8ae9951ff9f143`, 0, 10 | `b328af070b6cb40b`, 2, 6 | elim: timeout 1,800 s; liftstd_slimgb: timeout 1,800 s | also replaced |
| 29 | 1542 | second | `86c713a305d6aa4d`, 0, 10 | `972e9014b176196b`, -1, 6 | elim: timeout 1,800 s; liftstd_slimgb: memory limit (13 GB) | also replaced |
| 29 | 1670 | second | `5b002379685d4787`, 0, 10 | `6dd7c8e608b7373e`, 2, 6 | elim: timeout 1,800 s; lift: memory limit (10 GB); liftstd_slimgb: memory limit (11 GB) | also replaced |
| 40 | 211 | second | `6076fa31bd11b1df`, 1, 7 | `c11c7d57d8674628`, 0, 4 | elim: timeout 1,800 s; liftstd_slimgb: memory limit (10 GB) | also replaced |
| 40 | 321 | second | `7d73c225527a05c5`, 1, 7 | `e22c0d46e77e8aed`, -1, 7 | elim: memory limit (16 GB); liftstd_slimgb: timeout 1,800 s | also replaced |
| 149 | 115 | second | `78cd8b78de08cf7d`, 0, 10 | `68c1a1002cc774a2`, -1, 7 | elim: timeout 1,800 s; liftstd_slimgb: memory limit (17 GB) | also replaced |
| 149 | 478 | second | `e425e26ac373ea0b`, 0, 9 | `22a4a3c90f34e0db`, 0, 7 | elim: timeout 1,800 s; liftstd_slimgb: memory limit (12 GB) | also replaced |
| 149 | 487 | second | `b2d7aa02be49da10`, 0, 13 | `75d8263ef29760f8`, 0, 13 | elim: timeout 1,800 s; lift: memory limit (25 GB); liftstd_slimgb: memory limit (16 GB) | also replaced |
| 149 | 613 | second | `b075a2e324a12cc1`, 0, 8 | `dd9300dbab7e39e2`, -1, 6 | elim: memory limit (10 GB); liftstd_slimgb: timeout 1,800 s | also replaced |
| 149 | 682 | second | `e8b905ff357bcdad`, 0, 14 | `de13238c8be61fb2`, -1, 7 | elim: timeout 1,800 s; liftstd_slimgb: timeout 1,800 s | also replaced |

## Names of the generators

* 3:8722: stored (V,(4,)) (V,(3,4,5)) (z,S,(3,)) (D,4,5) (D,0,2) (T,(0,1,3,4,5)) (D,2,4) (D,z,0,2) (D,2,5) (D,2,3); certified (S,z,(3,5)) (w,S,(4,)) (S,w,(4,5)) (U,) (D,3,4) (D,3,5)
* 3:13414: stored (D,w,0,2) (D,1,2) (z,S,(1,)) (D,w,1,2) (S,z,(0,2)) (T,(0,2)) (V,(0,1)) (V,(0,1,2)); certified (S,w,(3,5)) (T,(0,3,5)) (w,S,(5,)) (V,(3,4)) (V,(3,5)) (D,4,5)
* 3:17222: stored (w,S,(1,)) (V,(1,3,4,5)) (w,S,(5,)) (S,z,(3,5)) (z,S,(5,)) (D,1,3) (z,S,(1,)) (D,1,5) (D,3,5) (S,w,(1,3,4,5)); certified (D,w,0,4) (S,z,(3,4)) (S,w,(4,5)) (V,(1,3,4,5)) (D,3,5) (D,4,5)
* 3:24725: stored (S,z,(4,5)) (V,(5,)) (S,z,(3,4,5)) (w,S,(4,)) (D,3,5) (V,(3,4)) (V,(3,4,5)); certified (V,(2,)) (V,(0,2)) (w,S,(2,)) (D,1,2) (V,(1,)) (w,S,(0,)) (D,0,1)
* 3:31232: stored (D,z,4,5) (D,2,3) (S,w,(4,5)) (T,(0,4,5)) (V,(3,4,5)) (V,(3,4)) (D,3,5); certified (S,z,(0,1)) (D,0,2) (D,1,2) (S,z,(2,3,4,5))
* 3:31274: stored (w,S,(5,)) (D,z,3,5) (S,w,(3,4,5)) (V,(3,5)) (V,(3,)) (V,(3,4,5)) (D,4,5); certified (V,(3,4)) (z,S,(5,)) (D,w,0,5) (D,z,0,4) (D,4,5) (V,(3,4,5))
* 3:31294: stored (D,z,3,4) (w,S,(3,)) (V,(3,4,5)) (V,(5,)) (V,(4,)) (V,(4,5)) (D,3,5); certified (z,S,(1,)) (D,1,5) (D,1,2) (T,(0,2))
* 3:32603: stored (V,(4,)) (D,4,5) (T,(0,4,5)) (S,w,(3,5)) (D,z,3,4) (V,(3,4,5)) (V,(3,5)); certified (S,w,(1,2)) (T,(0,3,4,5)) (D,0,1) (D,0,5) (S,z,(0,1,2)) (V,(0,2)) (S,z,(0,1))
* 3:33516: stored (D,z,3,5) (w,S,(5,)) (w,S,(3,)) (V,(3,4,5)) (V,(3,4)) (D,4,5); certified (S,z,(3,5)) (w,S,(4,)) (z,S,(3,)) (V,(3,4)) (V,(3,4,5)) (D,4,5)
* 3:40246: stored (D,z,0,4) (V,(5,)) (T,(0,3)) (D,w,3,5) (V,(3,4,5)) (V,(3,4)) (D,3,5); certified (S,z,(1,2)) (D,0,1) (D,0,2) (S,z,(0,3,4,5))
* 3:41091: stored (V,(2,)) (T,(0,2)) (T,(0,)) (S,z,(0,2)) (S,w,(0,1,2)) (D,0,1) (D,0,2) (D,1,2); certified (S,w,(4,5)) (S,w,(3,4)) (S,z,(3,5)) (D,4,5) (U,) (V,(3,5))
* 3:41143: stored (z,S,(4,)) (V,(3,)) (V,(4,)) (S,z,(1,3,4,5)) (V,(4,5)) (V,(3,4,5)) (D,3,4); certified (S,w,(0,2)) (D,0,1) (D,1,2) (S,w,(1,3,4,5))
* 3:42702: stored (V,(3,)) (S,z,(3,5)) (T,(0,4)) (S,w,(0,3,4,5)) (V,(4,5)) (D,3,4) (V,(3,5)); certified (V,(4,)) (D,z,3,5) (V,(3,4,5)) (S,z,(3,4)) (V,(4,5)) (D,3,5)
* 14:218: stored (z,S,(3,)) (D,w,2,4) (S,w,(3,4)) (U,) (S,z,(0,2,3,4)) (D,0,2) (S,w,(2,3,4)) (D,3,4) (D,z,0,1) (D,0,4); certified (S,w,(1,5)) (D,0,1) (D,0,5) (T,(0,2,3,4))
* 14:235: stored (V,(2,3)) (V,(2,)) (D,0,4) (U,) (w,S,(0,)) (z,S,(0,)) (D,0,3) (D,2,3) (D,0,2); certified (w,S,(4,)) (S,w,(1,5)) (D,1,4) (D,4,5)
* 14:246: stored (V,(2,4)) (V,(2,)) (V,(0,)) (z,S,(0,)) (V,(2,3,4)) (D,2,3) (D,0,3) (D,0,4) (D,0,2); certified (S,w,(1,5)) (D,1,4) (D,4,5) (S,w,(2,3,4))
* 14:258: stored (z,S,(3,)) (z,S,(0,)) (D,z,0,4) (V,(0,)) (U,) (D,0,2) (D,2,4) (D,0,4) (D,0,3); certified (S,w,(1,5)) (D,4,5) (D,1,4) (S,w,(2,3,4))
* 14:260: stored (S,z,(3,4)) (T,(0,)) (S,z,(2,3,4)) (z,S,(4,)) (U,) (D,0,2) (D,2,3) (D,0,3) (D,0,4); certified (S,w,(1,5)) (D,4,5) (T,(0,2,3,4)) (D,1,4)
* 14:377: stored (V,(2,4)) (U,) (D,0,4) (V,(2,3)) (D,w,3,4) (D,3,4) (D,2,3); certified (S,w,(1,5)) (S,w,(2,3,4)) (D,2,5) (D,1,2)
* 29:601: stored (U,) (D,1,5) (D,2,5) (D,3,5) (z,S,(2,)) (z,S,(3,)) (w,S,(1,)) (w,S,(4,)) (I,) (D,2,3); certified (S,w,(1,4)) (V,(1,5)) (V,(1,)) (V,(4,5)) (S,w,(4,5)) (D,1,4)
* 29:831: stored (w,S,(4,)) (S,z,(2,5)) (w,S,(1,)) (V,(2,3,4,5)) (V,(3,5)) (D,3,5) (V,(1,2,3,5)) (V,(1,4)) (S,w,(2,3)) (D,2,3) (UI,) (D,w,2,3); certified (D,w,0,1) (S,w,(1,5)) (T,(0,1)) (V,(1,2,3,5)) (V,(2,3,4,5)) (V,(2,3,5)) (D,1,4)
* 29:1444: stored (w,S,(1,)) (z,S,(1,)) (D,z,1,4) (S,w,(1,4,5)) (V,(0,)) (D,0,1) (D,0,4) (U,) (D,1,4) (D,0,5); certified (D,1,5) (V,(1,2,3,4,5)) (S,w,(1,5)) (w,S,(5,)) (S,z,(1,4)) (D,4,5)
* 29:1476: stored (S,w,(1,4)) (V,(1,)) (S,z,(1,4)) (D,4,5) (z,S,(4,)) (D,1,5) (D,1,4); certified (z,S,(2,)) (D,z,0,5) (S,w,(2,3)) (D,3,5) (D,2,3) (D,2,5)
* 29:1484: stored (S,z,(2,5)) (T,(0,2)) (S,z,(2,3,5)) (D,3,5) (U,) (D,0,3) (D,0,2) (D,0,5) (V,(0,)); certified (z,S,(2,)) (z,S,(5,)) (w,S,(2,)) (U,) (D,2,3) (D,2,5)
* 29:1508: stored (S,z,(2,3,5)) (z,S,(5,)) (U,) (z,S,(3,)) (D,0,3) (V,(0,)) (D,0,5) (D,2,3) (D,0,2); certified (V,(1,2,3,4,5)) (z,S,(5,)) (w,S,(3,)) (z,S,(3,)) (D,2,3) (D,3,5)
* 29:1518: stored (D,w,0,3) (z,S,(3,)) (D,z,0,1) (w,S,(2,)) (D,0,2) (D,0,5) (w,S,(0,)) (S,z,(0,2,3,5)) (D,3,5) (D,2,5); certified (S,z,(2,3)) (D,2,5) (z,S,(3,)) (w,S,(3,)) (D,3,5) (D,2,3)
* 29:1542: stored (w,S,(5,)) (V,(2,3,4,5)) (T,(0,)) (z,S,(4,)) (D,1,4) (D,w,0,2) (D,0,4) (S,w,(0,1,4,5)) (D,1,5) (D,0,1); certified (S,z,(2,3)) (S,z,(2,5)) (D,2,3) (S,z,(2,3,5)) (D,2,5) (D,3,5)
* 29:1670: stored (V,(1,2,4,5)) (V,(2,)) (S,z,(2,3)) (T,(0,3)) (D,0,3) (z,S,(0,)) (D,0,2) (S,z,(0,2,3,5)) (w,S,(0,)) (D,3,5); certified (S,z,(3,5)) (S,z,(2,5)) (V,(2,3)) (D,3,5) (w,S,(2,)) (D,2,5)
* 40:211: stored (D,z,0,5) (w,S,(4,)) (V,(1,4,5)) (V,(4,5)) (S,w,(1,4,5)) (T,(0,1,4)) (D,1,4); certified (T,(0,1,4,5)) (D,0,1) (z,S,(0,)) (D,0,3)
* 40:321: stored (D,z,4,5) (V,(4,)) (V,(1,5)) (T,(0,1,5)) (V,(4,5)) (V,(1,4,5)) (D,1,5); certified (S,w,(1,4)) (T,(0,4,5)) (V,(1,4)) (V,(1,)) (D,1,5) (V,(5,)) (V,(1,4,5))
* 149:115: stored (D,2,3) (T,(0,2,4,5)) (z,S,(4,)) (T,(0,3,4,5)) (D,1,2) (D,z,1,3) (S,z,(1,2,3,5)) (z,S,(0,)) (S,w,(1,2)) (V,(1,2,3)); certified (V,(0,4,5)) (w,S,(0,)) (S,w,(0,5)) (S,z,(1,3,4,5)) (S,z,(1,3,5)) (D,0,4) (D,4,5)
* 149:478: stored (S,z,(0,1,3,5)) (D,w,0,4) (w,S,(5,)) (D,z,1,2) (S,z,(0,2,3,4)) (S,z,(2,4,5)) (V,(0,4)) (U,) (D,4,5); certified (T,(0,5)) (S,w,(0,5)) (V,(0,4)) (U,) (V,(5,)) (D,0,5) (D,w,0,4)
* 149:487: stored (T,(0,)) (w,S,(5,)) (S,z,(1,3,4)) (D,w,1,3) (S,w,(4,5)) (V,(4,)) (S,z,(0,3)) (D,z,0,1) (S,z,(0,2)) (T,(0,2,4,5)) (D,1,3) (D,2,3) (D,1,2); certified (S,w,(0,5)) (T,(0,3,4,5)) (T,(0,)) (T,(0,5)) (V,(5,)) (D,1,5) (S,z,(1,5)) (D,w,1,3) (D,1,2) (T,(0,4,5)) (D,w,1,2) (S,z,(3,4,5)) (D,1,3)
* 149:613: stored (D,w,0,1) (D,4,5) (T,(0,5)) (D,z,3,5) (V,(0,5)) (S,z,(3,4)) (V,(4,)) (V,(0,4)); certified (V,(0,4,5)) (w,S,(0,)) (z,S,(5,)) (V,(0,4)) (S,w,(0,4)) (D,0,5)
* 149:682: stored (V,(0,4)) (S,w,(1,2)) (D,w,2,3) (D,w,1,4) (S,z,(1,2,3,5)) (w,S,(0,)) (D,1,3) (D,2,5) (T,(0,5)) (V,(0,)) (S,z,(1,2,4)) (T,(0,3,4,5)) (V,(1,2)) (D,2,3); certified (w,S,(0,)) (S,w,(0,5)) (V,(4,)) (V,(5,)) (V,(0,4)) (U,) (D,4,5)
