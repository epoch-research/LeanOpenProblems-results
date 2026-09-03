# Adjacent-index quadratic reduction

This continuation does NOT settle Erdős 773. Spec.lean is unchanged and its
sole admission remains at line 2031 for 0<epsilon<=1/3. No original proof or
disproof was submitted.

## New verified module

`AdjacentQuadraticReduction.lean` imports the clean
`ShortTranslatedIntersection` and `SimultaneousAffineSquares` modules. It
never imports Spec.lean. The file compiles without errors, warnings, or
admissions; its olean is built. All five printed axiom audits use only
propext, Classical.choice, and Quot.sound.
Log: `/tmp/adjacent-quadratic-reduction.log`.

Define adjacent(C)=C union {n+1:n in C}. Use the previously defined
normalized quadratic

    quadratic(q,r,n)=q*n^2+2*r*n.

## Verified finite statements

* `normalize_union`: If q>0 and B union (B+q) subset A, select a residue
  class r modulo q and divide its roots by q. There are r<q and C with

      |B| <= q |C|,
      {q*n+r:n in adjacent(C)} subset A.

  The proof partitions B by residues, selects a maximum fiber, and proves
  injectivity of the quotient map on that fiber. No equidistribution is
  assumed.

* `normalized_sidon`: Sidonness of {(q*n+r)^2:n in C}, with q>0, implies
  Sidonness of {quadratic(q,r,n):n in C}. This uses the exact identity

      (q*n+r)^2=q*quadratic(q,r,n)+r^2

  and cancellation of the positive q.

* `indices_bound`: If all lifted adjacent indices are in [1,N], then
  C subset range(floor(N/q)). This does not assert that the interval is full.

* `extract_adjacent_quadratic`: If A subset [1,N] has Sidon squares and
  M=|A|>=8, there are q in [1,N], r<q, and C with

      C subset range(floor(N/q)),
      {q*n+r:n in adjacent(C)} subset A,
      q M <= 4N+M,
      M^2 <= 8N q |C|,
      {quadratic(q,r,n):n in adjacent(C)} Sidon.

* `power_scale_reduction`: If additionally M>=N^(1-eta), the extracted
  parameters can satisfy

      q <= 5 N^eta,
      N^(1-3eta) <= 40 |C|.

  The real-power cancellation is included in Lean, not just informal
  exponent bookkeeping. The supplied large original set is a hypothesis,
  not a construction established by this theorem.

## Why the existing full-fiber upper bound does not apply

The extracted C is arbitrary and potentially sparse. Its union with C+1
need not contain a full interval of index values. The full-fiber results
require every index in a specified prefix, not just a collection of adjacent
pairs. Moreover q need not be a prime power, and no unit-residue hypothesis
is supplied here. Even imposing these latter two conditions would not fix
the missing full-prefix hypothesis.

No uniform fixed-power upper bound for these sparse adjacent-index sets was
proved. Nor was a near-linear construction of such sets proved. The new
reduction does not discharge the universal-affine Sidon hypothesis either.
No actual original lower or upper exponent improved.

The strongest completed actual lower bound remains N^(2/3)/8192 eventually.
Spec.lean SHA-256 remains
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.
