# Fixed-factor transducer review and search

The original conjecture is still UNSETTLED. No Lean source was changed,
no new asymptotic bound was obtained, and no incomplete proof was submitted.
Spec.lean retains its sole admission for 0 < epsilon < 1/3, with the
completed endpoint eventual M(N) >= N^(2/3).

## Bounded-capacity review

The existing near-critical ordinary-integer counterexamples already rule
out generic near-linear conversion from a fixed positive-difference
capacity. They have the requisite fixed-capacity quantifier order and
near-square-root ambient density. No square-specific conversion was
obtained from primitivity, pairwise root coprimality, small codegrees, or
root-translation considerations. The existing counterexamples involving
coprime roots concern multiplicity, not a fixed-power upper bound on the
maximum Sidon subset.

## New exploratory program

`Research/AllowedAlphabetTransducer.cpp` uses exact small-integer arithmetic
to search a fixed Gaussian-factor family in the full allowed alphabet.
For h=63, B=6h+7=385, take

    n=3B(B-1), m=k*n+1,
    (x,y,z,w)=(m*u-n*v, n*u+m*v, m*u+n*v, -n*u+m*v).

These expressions satisfy the norm identity algebraically. Factor u and v
have constant digit 6 and h-2 free higher digits. At each column the two
x,z output digits depend only on the current u digit and the preceding
state; similarly y,w depend only on the current v digit. The program
uses this decoupling, small carry states, and separate used-label masks.

Every interior output digit is required to be one of
12,18,...,6(h+1), without repetition within a word. Leading digit 1 and
constant digit 6 are required. A completed word set is rejected if any
two words coincide. There is a conservative top-factor-digit interval
restriction and a necessary next-column modular filter. This remains a
restricted candidate search, not a completeness theorem for all carrier
collisions.

The new search does not use the older ramp or local affine-boundary-repair
restrictions. It does use randomized depth-first search with bounded
restarts and a wall-clock cutoff. It does not use floating-point numerical
norm tests. Any positive output would still need independent exact-integer
validation and a Lean certificate; no positive output was produced.

## Completed runs

Both runs used 120-second cutoffs and at most 200000 recursive nodes per
restart.

* k=4: 160432128 recursive nodes, 803 restarts, maximum entered column 55
  (54 of 63 interior columns assigned), no witness.
* k=5: 159973376 recursive nodes, 800 restarts, maximum entered column 56
  (55 of 63 interior columns assigned), no witness.

Logs:

    /tmp/allowed-transducer-63-4.log
    /tmp/allowed-transducer-63-5.log

The corresponding JSON output files are empty. Both processes have ended;
there is no associated search still running. These outcomes are neither
UNSAT certificates nor evidence establishing eventual Sidonness. Even an
actual collision in this carrier would not disprove the original conjecture,
and a single finite collision would not negate eventual carrier Sidonness.

## Main file

Unchanged SHA-256:

    257d2e55d464b8ea5a35ca7f1257dc2f59e682772c2f52fa771ee4bfdf9b8940

The original statement and sole import are unchanged.
Original theorem: line 17276. Sole admission: line 17287.
