## Residual cells: chosen lemma (every-mass lemmas preferred)

| class (CC) | diagram | cells | kind | engine label | chosen lemma | masses | other lemmas that apply |
|---|---|---|---|---|---|---|---|
| 4 (31) | 34:3 25:1 35:3 45:3 zc2345 | 8 | single | - | B0 | every positive | R1* (8), TD (8) |
| 23 (46) | 23:1 14:1 34:2 05:1 35:2 45:2 zc012345 | 6 | single | - | B0 | every positive | R1* (6), TD (6) |
| 25 (47) | 23:1 14:1 34:3 05:1 35:3 45:3 zc012345 | 6 | single | - | B0 | every positive | R1* (6), TD (6) |
| 64 (100) | 23:1 04:1 14:2 05:2 15:1 zc012345 wc0145 | 16 | single | - | B0 | every positive | TD (16) |
| 116 (101) | 13:1 23:2 14:2 24:1 05:1 25:2 35:2 zc012345 wc1234 | 2 | single | - | B0 | every positive | TD (2) |
| 4 (31) | 34:3 25:1 35:3 45:3 zc2345 | 4 | single | - | K | every positive | R1* (4), TD (4) |
| 16 (–) | 23:1 24:1 34:1 15:2 zc234 wc15 | 8 | core | L16:nolabel | L | every positive |  |
| 16 (–) | 23:1 24:1 34:1 15:2 zc234 wc15 | 4 | core | L21:none | L | every positive |  |
| 15 (82) | 23:1 24:1 34:1 15:2 zc34 wc15 | 1 | single | - | TD | every positive | EQ2 (1) |
| 4 (31) | 34:3 25:1 35:3 45:3 zc2345 | 2 | core | L3:pos | R1* | generic |  |
| 14 (14) | 23:1 24:1 34:1 15:2 wc15 | 12 | core | L17:pos | R1* | generic |  |
| 28 (86) | 23:1 14:1 24:1 34:1 05:2 zc1234 wc05 | 1 | core | L3:pos | R1* | generic |  |
| 30 (16) | 23:1 14:2 15:2 25:1 35:1 45:2 wc14 | 6 | core | L17:pos | R1* | generic | EQ2 (4) |
| 53 (95) | 23:1 14:3 05:2 15:3 45:3 zc23 wc0145 | 1 | core | L3:pos | R1* | generic |  |
| 62 (40) | 23:1 14:3 24:1 34:1 05:1 15:3 45:3 zc01345 | 14 | core | L17:pos | R1* | generic | EQ2 (4) |
| 63 (52) | 23:1 14:3 24:1 34:1 05:1 15:3 45:3 zc012345 | 7 | core | L17:pos | R1* | generic |  |
| 10 (36) | 24:1 34:3 15:1 35:3 45:3 zc12345 | 9 | core | L16:nolabel | W3 | generic |  |
| 25 (47) | 23:1 14:1 34:3 05:1 35:3 45:3 zc012345 | 4 | core | L16:nolabel | W3 | generic |  |
| 56 (50) | 23:1 14:3 34:1 05:1 15:3 45:3 zc012345 | 2 | core | L16:nolabel | W3 | generic |  |
| 15 (82) | 23:1 24:1 34:1 15:2 zc34 wc15 | 1 | core | L11:pos | EQ2 | generic |  |
| 0 (81) | 34:1 25:2 zc34 wc25 | 1 | core | L29:undec | TQ | generic |  |

Totals: B0 38, K 4, L 12, TD 1, R1* 43, W3 15, EQ2 1, TQ 1; every positive mass 55, generic 60.

## Mass conditions of the generic lemmas (per cell)

| class | cells | lemma | roles | degree | nonzero | positive sign change | engine label |
|---|---|---|---|---|---|---|---|
| 0 | 1 | TQ | `{"k": [0, 1], "l": [3, 4]}` | 16 | True | False | ours | label (gcd degree 16) |
| 4 | 2 | R1* | `{"MA": [3], "MB": [4], "a": 3, "b": 4, "s": 5}` | 18 | True | True | equal (gcd degree 18) |
| 10 | 9 | W3 | `{"shape": {"3": "-m1*m4 + m2*m5", "4": "m1*m3", "5": "-m2*m3"}, "tri": [3, 4, 5]}` | 24 | True | True | no engine label |
| 14 | 2 | R1* | `{"MA": [0, 2], "MB": [3], "a": 2, "b": 3, "s": 4}` | 18 | True | True | equal (gcd degree 18) |
| 14 | 2 | R1* | `{"MA": [0, 2], "MB": [4], "a": 2, "b": 4, "s": 3}` | 18 | True | True | equal (gcd degree 18) |
| 14 | 2 | R1* | `{"MA": [0, 3], "MB": [4], "a": 3, "b": 4, "s": 2}` | 18 | True | True | equal (gcd degree 18) |
| 14 | 2 | R1* | `{"MA": [2], "MB": [0, 3], "a": 2, "b": 3, "s": 4}` | 18 | True | True | equal (gcd degree 18) |
| 14 | 2 | R1* | `{"MA": [2], "MB": [0, 4], "a": 2, "b": 4, "s": 3}` | 18 | True | True | equal (gcd degree 18) |
| 14 | 2 | R1* | `{"MA": [3], "MB": [0, 4], "a": 3, "b": 4, "s": 2}` | 18 | True | True | equal (gcd degree 18) |
| 15 | 1 | EQ2 | `{"MA": [3], "MB": [4], "a": 3, "b": 4, "s": 2}` | 6 | True | True | label | ours (gcd degree 5) |
| 15 | 1 | EQ2 | `{"MA": [3], "MB": [4], "a": 3, "b": 4, "s": 2}` | 6 | True | True | no engine label |
| 16 | 4 | L | `{"a": 2, "b": 3, "s": 4}` | 18 | True | False | no engine label |
| 16 | 4 | L | `{"a": 2, "b": 4, "s": 3}` | 18 | True | False | no engine label |
| 16 | 4 | L | `{"a": 3, "b": 4, "s": 2}` | 18 | True | False | label | ours (gcd degree 14) |
| 25 | 1 | W3 | `{"shape": {"3": "m0*(m1 + m4)", "4": "-m0*m3 + m2*m5", "5": "-m2*(m1 + m4)"}, "tri": [3, 4, 5]}` | 24 | True | True | no engine label |
| 25 | 1 | W3 | `{"shape": {"3": "m0*m4 - m1*m5", "4": "-m0*(m2 + m3)", "5": "m1*(m2 + m3)"}, "tri": [3, 4, 5]}` | 24 | True | True | no engine label |
| 25 | 1 | W3 | `{"shape": {"3": "m0*m4 - m1*m5", "4": "-m0*m3 + m2*m5", "5": "m1*m3 - m2*m4"}, "tri": [3, 4, 5]}` | 24 | True | True | no engine label |
| 25 | 1 | W3 | `{"shape": {"3": "m1*(m0 + m5)", "4": "-m2*(m0 + m5)", "5": "-m1*m3 + m2*m4"}, "tri": [3, 4, 5]}` | 24 | True | True | no engine label |
| 28 | 1 | R1* | `{"MA": [2], "MB": [3], "a": 2, "b": 3, "s": 4}` | 18 | True | True | equal (gcd degree 18) |
| 30 | 3 | R1* | `{"MA": [0, 2], "MB": [3], "a": 2, "b": 3, "s": 5}` | 18 | True | True | equal (gcd degree 18) |
| 30 | 3 | R1* | `{"MA": [2], "MB": [0, 3], "a": 2, "b": 3, "s": 5}` | 18 | True | True | equal (gcd degree 18) |
| 53 | 1 | R1* | `{"MA": [1], "MB": [4], "a": 1, "b": 4, "s": 5}` | 18 | True | True | equal (gcd degree 18) |
| 56 | 2 | W3 | `{"shape": {"1": "-m0*m4 + m2*m5 + m3*m5", "4": "m0*m1", "5": "-m1*(m2 + m3)"}, "tri": [1, 4, 5]}` | 24 | True | True | no engine label |
| 62 | 14 | R1* | `{"MA": [1], "MB": [0, 5], "a": 1, "b": 5, "s": 4}` | 18 | True | True | equal (gcd degree 18) |
| 63 | 7 | R1* | `{"MA": [1], "MB": [0, 5], "a": 1, "b": 5, "s": 4}` | 18 | True | True | equal (gcd degree 18) |

## Global run (all 91,273 cells)

```
{
 "allmass_gain": 1910,
 "allmass_gain_B0": 254,
 "allmass_gain_K": 76,
 "allmass_gain_L": 1579,
 "allmass_gain_TD": 43,
 "allmass_gain_kind_core": 1579,
 "allmass_gain_kind_single": 331,
 "allmass_new": 70406,
 "allmass_old": 68496,
 "applies_B0": 7722,
 "applies_EQ2": 2654,
 "applies_K": 532,
 "applies_L": 2111,
 "applies_R1*": 79321,
 "applies_TD": 43,
 "applies_TQ": 1,
 "applies_W3": 650,
 "cells": 91273,
 "generic_new": 91273,
 "generic_old": 91158
}
```
