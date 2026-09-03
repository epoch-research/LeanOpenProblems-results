# A 34-row exact certificate at q=27

Delete infinity and orbits 4 and 5. Labels `c_j` denote full-orbit labels, not individual point labels.
Variables in row order: [0, 1, 2, 3, 6, 7, 8].

Define `L1,...,L7 = c1-c2, c2-c3, c2-c7, c2-c8, c3-c7, c3-c8, c7-c8`.
The identities below force every Li and every Li +/- Lj to be nonzero modulo 13.
Thus seven Li must occupy distinct nonzero negation orbits, but F13 has only six. Contradiction.
No tag normalization, UNSAT flag, or exhaustive tree is needed for this argument.
This is a sufficient core; no minimum or inclusion-minimal claim is made.

## The original multiset-triple inequalities

`Rj` is the indicated left tag sum minus right tag sum, using constant tags on each full orbit.
Every equality in the table is modulo 757; coherence requires `Rj != 0 mod 13`.
Repeated entries are intentional. All point entries are retained Singer bases.

| Row | Left base triple | Right base triple | Common base sum |
|---:|---|---|---:|
| 2 | (409, 445, 660) | (466, 470, 578) | 0 |
| 14 | (81, 310, 466) | (3, 409, 445) | 100 |
| 17 | (3, 404, 445) | (466, 470, 673) | 95 |
| 22 | (81, 310, 404) | (409, 470, 673) | 38 |
| 25 | (43, 310, 404) | (409, 445, 660) | 0 |
| 26 | (43, 310, 404) | (466, 470, 578) | 0 |
| 29 | (243, 243, 466) | (43, 404, 505) | 195 |
| 30 | (505, 660, 729) | (27, 43, 310) | 380 |
| 35 | (470, 505, 608) | (404, 519, 660) | 69 |
| 37 | (243, 660, 729) | (1, 404, 470) | 118 |
| 46 | (9, 310, 578) | (43, 409, 445) | 140 |
| 49 | (1, 243, 660) | (466, 466, 729) | 147 |
| 55 | (404, 505, 729) | (27, 409, 445) | 124 |
| 56 | (404, 505, 608) | (387, 470, 660) | 3 |
| 57 | (243, 243, 310) | (470, 505, 578) | 39 |
| 61 | (9, 27, 243) | (404, 660, 729) | 279 |
| 62 | (243, 243, 505) | (9, 404, 578) | 234 |
| 68 | (43, 243, 505) | (310, 578, 660) | 34 |
| 73 | (9, 243, 505) | (43, 310, 404) | 0 |
| 76 | (9, 243, 505) | (409, 445, 660) | 0 |
| 77 | (9, 243, 505) | (466, 470, 578) | 0 |
| 80 | (3, 387, 470) | (9, 243, 608) | 103 |
| 81 | (445, 470, 673) | (505, 505, 578) | 74 |
| 84 | (3, 43, 729) | (27, 243, 505) | 18 |
| 90 | (3, 243, 578) | (9, 310, 505) | 67 |
| 91 | (3, 404, 445) | (9, 43, 43) | 95 |
| 97 | (445, 466, 673) | (9, 409, 409) | 70 |
| 99 | (409, 505, 673) | (9, 243, 578) | 73 |
| 104 | (3, 404, 505) | (9, 243, 660) | 155 |
| 105 | (3, 43, 310) | (243, 404, 466) | 356 |
| 190 | (3, 81, 673) | (9, 243, 505) | 0 |
| 191 | (3, 81, 673) | (43, 310, 404) | 0 |
| 195 | (3, 81, 673) | (409, 445, 660) | 0 |
| 197 | (3, 81, 673) | (466, 470, 578) | 0 |

## Identities over F13

Coefficients are reduced modulo 13 (in particular, `3^(-1)=9=-4`).

| Form | Equal row expression |
|---|---|
| L1 | -4 R190 |
| L2 | -4 R73 |
| L3 | -4 R76 |
| L4 | -4 R77 |
| L5 | -4 R25 |
| L6 | -4 R26 |
| L7 | -4 R2 |

| Pair | Li - Lj | Li + Lj |
|---|---|---|
| 1, 2 | R84 | -4 R191 |
| 1, 3 | R81 | -4 R195 |
| 1, 4 | R80 | -4 R197 |
| 1, 5 | R91 | R104 |
| 1, 6 | R90 | R105 |
| 1, 7 | R97 | R99 |
| 2, 3 | 4 R25 | R61 |
| 2, 4 | 4 R26 | R62 |
| 2, 5 | R30 | -4 R76 |
| 2, 6 | R29 | -4 R77 |
| 2, 7 | R35 | R37 |
| 3, 4 | 4 R2 | R68 |
| 3, 5 | -4 R73 | R55 |
| 3, 6 | R35 | R56 |
| 3, 7 | R46 | -4 R77 |
| 4, 5 | R37 | R56 |
| 4, 6 | -4 R73 | R57 |
| 4, 7 | -4 R76 | R49 |
| 5, 6 | 4 R2 | R22 |
| 5, 7 | R14 | -4 R26 |
| 6, 7 | -4 R25 | R17 |

The last six forms are all six differences of the four tags `c2,c3,c7,c8`.
Their +/- values would already exhaust F13*, and the extra nonzero `c1-c2` is forbidden from all of them.
All 49 identities and all source triples are independently checked by `char3_invariant_tag_verify.py`.
