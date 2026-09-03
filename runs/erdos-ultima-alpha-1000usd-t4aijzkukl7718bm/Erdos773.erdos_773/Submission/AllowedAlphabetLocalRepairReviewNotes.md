# Exact allowed-alphabet local repair review

The original conjecture remains UNSETTLED. No new Lean theorem was produced
and Spec.lean was not changed. Its actual completed endpoint is still
M(N)>=N^(2/3) eventually, with the sole admission for 0<epsilon<1/3.

## Mathematical review

The exact carrier in AllowedAlphabetCandidate was reconsidered. The formal
Gaussian-Eisenstein theorem does not certify its integer evaluations. No
root bound or carry-energy inequality was found that proves its eventual
Sidonness. No histogram-only criterion was inferred from the fixed endpoint
digits. The single-swap restriction still does not handle arbitrary pairs
of permutations.

## Targeted exact search

Two new exploratory programs were used:

- Research/AllowedAlphabetAnneal.cpp
- Research/AllowedAlphabetAnnealWide.cpp

They use B=6h+7, n=3B(B-1), m=4n+1, and the exact Gaussian family

    (mU-nV, nU+mV, mU+nV, -nU+mV).

The norm identity is algebraic. Input digits are locally changed, and signed
integer carries are recomputed exactly. The objective penalizes invalid
output digits, incorrect leading digits, and repeated allowed digits. A
zero objective together with four distinct words would be a candidate to
check independently, not a trusted theorem.

This differs from the earlier prefix DFS: it begins with the known ramp and
allows repairs throughout the factor words. The second variant lowers the
invalid-digit penalty and permits full-range digit changes. Neither variant
is a complete search, and their nonzero objective scores are not comparable
mathematical bounds.

Completed runs, each with a 120-second cutoff:

| version | h | final best objective | iterations | exact carrier witness |
|---|---:|---:|---:|---|
| original | 255 | 144 | 50,200,576 | none |
| original | 1023 | 568 | 14,483,456 | none |
| wider moves | 127 | 113 | 84,738,048 | none |
| wider moves | 255 | 175 | 56,819,712 | none |

The original h=255 run reached four words with constant digit 6, leading
digit 1, and every interior digit in the allowed alphabet. Independent
Python integer evaluation confirmed both the factor equations and the norm
identity. However, the four words have respectively 33,38,39,34 repeated
allowed digits. They are NOT permutations of the complete alphabet and
are NOT a counterexample to AllowedAlphabetCandidate.

All four final outputs were independently checked against exact factor
values, square sums, endpoints, and the sorted target alphabet. None meets
the exact carrier conditions. No associated search process remains running.

A failed search or a nonzero objective is not an UNSAT certificate, is not
asymptotic evidence, and does not imply the carrier is Sidon. Even a finite
carrier collision would not negate the original conjecture.

Logs and exploratory data:

    /tmp/allowed-anneal-255.{json,log,exit}
    /tmp/allowed-anneal-1023.{json,log,exit}
    /tmp/allowed-anneal-wide-127.{json,log,exit}
    /tmp/allowed-anneal-wide-255.{json,log,exit}

## Remaining gap

The conditional Sidon hypothesis of
AllowedAlphabetCandidate.near_linear_of_eventually_sidon remains unproved.
No saving in the surviving collision count and no alternative near-linear
selector was obtained. No fixed-power upper bound for the unrestricted
Sidon maximum was proved either.

Spec.lean SHA-256 remains:

    257d2e55d464b8ea5a35ca7f1257dc2f59e682772c2f52fa771ee4bfdf9b8940

No incomplete main proof has been submitted as a settlement.
