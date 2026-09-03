# Further exact-alphabet repair tests: no settlement

The original conjecture remains unresolved. Spec.lean is unchanged, with its
sole sorry at line 17287 for 0 < epsilon < 1/3. No new Lean theorem or actual
Sidon exponent was obtained in this continuation.

## Corrected interpretation of factor coefficients

The old AllowedAlphabetAnneal.cpp allowed nonmultiples of six among canonical
factor coefficients. It therefore did NOT omit all factor values whose canonical
digits were not multiples of six. An initial suggestion to that effect in this
continuation was corrected after inspecting the move generator.

Research/AllowedAlphabetExpandedFactors.cpp permits lower input coefficients in
[0,6B), adds missing-output-digit-directed moves, and changes the penalty and
annealing schedule. This is an alternative noncanonical parametrization and
optimization landscape, not a proof that the old represented factor-value space
was incomplete. Both programs are incomplete exploratory searches.

## Completed 120-second tests

They started from the previous exact Gaussian-factor states and kept the identity

    (mU-nV)^2 + (nU+mV)^2 = (mU+nV)^2 + (-nU+mV)^2,
    n=3B(B-1), m=4n+1, B=6h+7.

* h=255: best objective 144, 57,737,216 iterations. No improvement over the old
  state. All interior digits are allowed, but the four words have 33,38,39,34
  repeated digits respectively. They are not complete alphabet permutations.
* h=1023: best objective 246 under the changed penalty (not comparable to the
  old program's objective 568), 19,005,440 iterations. Invalid interior digit
  counts are 5,6,5,6; repeated interior digit counts are 17,17,16,18. No word
  satisfies the exact full carrier condition.

Python arbitrary-precision arithmetic independently checked both outputs against
all four factor equations and the norm identity. Neither output is a carrier
counterexample, much less a disproof of the original conjecture.

Data and logs: /tmp/allowed-expanded-{255,1023}.{json,log,exit}.
Executable: /tmp/allowed-expanded-factors.

## Local exact constraint tests

Research/AllowedAlphabetLocalExactRepair.py holds all factor coefficients outside
one specified interval fixed. It also fixes incoming and outgoing carries, so all
output digits outside the affected interval must remain unchanged. New digits
must be allowed, pairwise distinct within each word, and unused outside the
interval. The script independently reconstructs every SAT model as exact integers.
No SAT model was obtained.

Starting from the h=1023 state:

* Factor indices 1..40, QF_LIA, 180-second budget: unknown, reason timeout.
  Log: /tmp/allowed-local-exact-1023-1-40-lia.log.
* Factor indices 875..930, qffd, 180-second budget: unknown, reason canceled.
  Log: /tmp/allowed-local-exact-1023-875-930-qffd.log.

Neither result is UNSAT, and even a local UNSAT result would not establish
Sidonness of the carrier. Both processes have finished. Do not repeat these tests
without a genuinely different constraint strategy or a mathematical idea.

## Mathematical review and remaining gap

Reviewed complementary permutation pairs, sparse-swap cube configurations, and
ramp/block encodings as possible systematic constructions or rigidity arguments.
No complete allowed-alphabet collision, eventual Sidonness proof, or useful
surviving-collision count resulted. Informal entropy estimates were not promoted
to theorems. A finite carrier collision would not by itself negate eventual
Sidonness of that carrier, nor would it negate the original conjecture.

The conditional hypothesis in AllowedAlphabetCandidate.near_linear_of_eventually_sidon
remains unproved. No incomplete main proof was submitted.

Spec.lean SHA-256 remains:
257d2e55d464b8ea5a35ca7f1257dc2f59e682772c2f52fa771ee4bfdf9b8940.
