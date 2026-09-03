# Additional work: digit histogram obstructions

This does not settle Erdős 773. `Spec.lean` still has exactly one `sorry`, in the
range 0 < epsilon <= 1/3. Its statement and import were left unchanged.

## Verified new scratch files

* `EisensteinHistogramObstacle.lean`: degree-994 base-81 words, monic, lower
  digits divisible by 3, constant digits 3 modulo 9. All four words have exactly
  the same complete digit histogram. Their square sums collide nontrivially;
  root gcd is 120. Digit sum 38440, squared-digit sum 2130202.
* `EisensteinPrimitiveHistogramObstacle.lean`: degree-2215 base-16 words, monic,
  lower digits even, constant digits 2 modulo 4. All four words have exactly the
  same complete digit histogram. Their square sums collide nontrivially;
  root gcd is exactly 2 (the forced common factor). Digit sum 15181,
  squared-digit sum 153265.

The base-16 file needs a larger Lean thread stack for its long literal lists:
`lake env lean -s 65536 Submission/EisensteinPrimitiveHistogramObstacle.lean`.
It compiles and its printed axiom audits are clean with this setting.

Both prove equality of every additive digit statistic, via `List.Perm.map`
followed by `List.Perm.sum_eq`. This concerns functions of the digit, not
position-dependent digit moments. Axiom audits use only allowed axioms.

These examples refute a blanket claim that monic Eisenstein digit words with
fixed digit sum and norm have Sidon squares. They do NOT show that every large
class with such restrictions is bad, nor that no more refined construction
could work. They also do not settle the original conjecture.

## How the examples were constructed

A rational rotation q*c = C*a + S*b, q*d = -S*a + C*b is tracked digitwise by
finite carry states. Digit-histogram differences are additive edge labels.
One seeks an integer flow from the constant-digit state to the monic-leading
state, with zero total histogram difference, then reconstructs an Euler path.
All final claims were checked by exact arithmetic and Lean, not solver trust.

Base 81 uses (q,C,S) = (89,80,39), 41 states, 3334 edges.
Base 16 uses (q,C,S) = (1973,1748,915), 1997 states, 31944 edges.

Direct MILP repeatedly timed out. Effective replacement:
1. Compute a Smith normal form on a small collection of columns or graph cycles.
2. Use an LLL-reduced integer kernel and high-precision Babai rounding to find
   small signed integer solutions.
3. Solve a positive real flow LP, round its network-flow part integrally, and
   correct histogram residuals using the small integer cycle basis.
4. Verify nonnegativity, exact conservation, exact statistics, and connectivity;
   extract the Euler path and check the resulting integers.

Scripts/results in `/tmp`:
* `carry_graph.json`, `carry_graph16.json`
* `carry_exact_flow.py` (base 81, direct small-column integer correction)
* `carry_cycle16.py` (base 16, spanning-tree cycle correction)
* `carry_extract.py`, `carry_extract16.py`
* `carry_histogram_result.json`, `carry_histogram16_result.json`
* `carry_histogram_integer_flow.json`, `carry_histogram16_integer_flow.json`

Lean note: `decide` did not reduce `List.mergeSort`; equality of finite digit
counts plus `List.perm_iff_count` worked. The concrete checks use ordinary
kernel-checked `decide`, not native_decide.

## Carry-free root addition does not repair the sphere argument

`CarryFreeSphereObstacle.lean` is a short additional verified example:
19804^2 + 28758^2 = 22716^2 + 26518^2 = 1219220980.
All four roots have ten base-3 digits with leading digit 1, exactly six 1s and
four 0s. Thus their digit sums and squared-digit sums agree, and every pair of
root words adds without carries. Their gcd is 2. This shows that controlling
carries in root addition does not control carries in squaring. The file compiles
with the standard Lean stack setting and has only the allowed axioms.
This example does not impose Eisenstein coefficient conditions, and it does not
show that every large digit class fails.

No change to `Spec.lean`; the conjecture remains unproved for 0 < epsilon <= 1/3.

## Later update

The much shorter family in `InertSmallSumObstacle.lean` additionally has total
digit sum smaller than the base and an unbounded primitive subfamily. See
`InertSmallSumResearchNotes.md`. These remain construction obstructions only,
not a disproof of Erdős 773.
