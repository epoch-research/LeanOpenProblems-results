# Exact integer constraints in the covering sieve

## Status

**Erdős 970 is not resolved here.** There is no proof of `H(k) = O(k²)`, and no
construction with `L/k² → ∞` satisfying all the abstract intersection constraints.
The proved deliverable is an exact, covering-specific integer cube-trade lemma,
its prime-sieve specialization, an exact integer feasibility characterization,
and finite covered examples with distinct primes. All are checked in Lean.

`Submission/Spec.lean` was not edited. The new Lean files do not import it.
Its SHA-256 is
`c961aa894dc05a671003b74cd770bf0efc120992bcaaa79466c418b03e1688e7`.

## 1. The exact integer feasibility problem

Let `P` be a finite set of distinct primes and `L > 0`. An incidence array has
one support `I_x ⊆ P` for each of its `L` rows. Write

- `x_T = #{x : I_x = T}`;
- `m_S = Σ_{T ⊇ S} x_T`;
- `d_S = ∏_{p∈S} p`, with `d_∅ = 1`.

Full covering means **`x_∅ = 0`**, not merely that the empty cell has small mass.

Set `F(z) = Σ_T x_T ∏_{p∈T} z_p`. Then

```
F(1+t) = Σ_S m_S ∏_{p∈S} t_p.
```

Take the baseline array with rows the prime-divisibility supports of `1,...,L`.
Let its histogram and polynomial be `b_T` and `B(z)`. For every subset `S`,
its intersection count is exactly `floor(L/d_S)`.

Consequently, **every** array satisfying the exact floor/ceiling constraints
has the unique representation

```
F(z) = B(z) + Σ_{∅≠R⊆P} e_R ∏_{p∈R} (z_p-1),
```

where

```
e_R ∈ {0,1},                  e_R = 0 whenever d_R divides L.
```

It is a covered integer array if and only if all the coefficients

```
x_T = b_T + Σ_{R⊇T} (-1)^(|R|-|T|) e_R
```

are nonnegative and the coefficient for `T=∅` is zero. The latter condition is

```
Σ_{|R| odd} e_R - Σ_{|R| even, R≠∅} e_R = b_∅.
```

This is an exact **integer** feasibility formulation, not a real-weighted or
truncated LP. Sufficiency follows by taking `x_T` copies of each pattern `T`:
evaluation at `z=1` gives exactly `L` rows. Necessity is Boolean Möbius inversion.
The full inversion and the covered-histogram equivalence are formalized as
`histogram_mobius_inversion` and `covered_histogram_iff`.

Boundary distinction: `|m_S-L/d_S| ≤ 1` alone permits extra possibilities when
`d_S | L`. The formulation above uses the stronger exact floor/ceiling
condition. The finite examples below satisfy that stronger condition.

## 2. Proved covering-specific odd-cube packing lemma

Choose a family `𝓕` of **distinct odd-cardinality** nonempty subsets of `P`.
For each pattern define its load

```
N_𝓕(T) = #{R∈𝓕 : T⊆R}.
```

Suppose:

1. `|𝓕| = b_∅`;
2. for every even-cardinality `T ⊆ P`, including `T=∅`,
   `N_𝓕(T) ≤ b_T`;
3. `d_R` does not divide `L` for every `R∈𝓕`.

Then

```
x_T = b_T - (-1)^|T| N_𝓕(T)
```

is a nonnegative integer histogram of exactly `L` covered rows, and **every**
intersection satisfies

```
m_S = floor(L/d_S) + 1_{S∈𝓕}.
```

Thus every intersection is precisely its floor or ceiling.

### Proof

Adding `∏_{p∈R}(z_p-1)` for odd `|R|` subtracts one from every even subpattern
of `R` and adds one to every odd subpattern. It removes one empty row.
After substitution `z=1+t`, it becomes just `∏_{p∈R} t_p`: it changes **only**
the intersection indexed by `R`, increasing it by one. The even-pattern
capacities give exactly nonnegativity; odd patterns only gain rows. The
family-size condition kills the empty pattern, and every nonempty cube
vanishes at `z=1`, preserving the number of rows. The divisibility exclusion
is exactly the available integer rounding slack.

This proof is formalized, not assumed:

- `oddCube_intersections`;
- `traded_nonneg_iff`;
- `odd_trade_cover`;
- `odd_trade_preserves_bounds`;
- `baseHistogram_intersections` (the exact arithmetic baseline);
- `prime_cube_packing_cover` (the complete prime-sieve specialization).

The general theorem is stated in histogram form. Its nonnegative integer
coefficients represent a finite array by replication. The examples below are
also explicitly represented as functions on `Fin L` in Lean.

**Important limitation:** existence of a large packing family `𝓕` is an explicit
hypothesis, not a proved asymptotic fact. Restricting to odd cubes is a
sufficient construction mechanism, not a without-loss-of-generality reduction:
the complete feasibility problem also allows even `e_R`.

There is already a useful exact obstruction to careless packing: if `T` is
even and `d_T > L`, then `b_T=0`, so no chosen odd top may contain `T`.
Other even-pattern capacities can also be small despite large singleton counts.

## 3. Explicit covered array: four distinct primes, nineteen rows

Take

```
P = {2,3,5,7},  L = 19,
𝓕 = {{2},{3},{5},{7},{2,3,5}}.
```

The baseline uncovered rows are `1,11,13,17,19`, so `b_∅=5`.
The cubic trade needs one row of each even pattern `{2,3}`, `{2,5}`, `{3,5}`;
the baseline has respectively `3`, `1`, `1` such rows. The singleton trades
need no nonempty even-pattern resources. None of the top products
`2,3,5,7,30` divides `19`.

The resulting nonzero pattern multiplicities are:

| Pattern | Multiplicity |
|---|---:|
| `{2}` | 6 |
| `{3}` | 4 |
| `{5}` | 3 |
| `{7}` | 2 |
| `{2,3}` | 2 |
| `{2,7}` | 1 |
| `{2,3,5}` | 1 |

Every row is covered; the multiplicities sum to `19`. Its intersection counts
are:

| Subset | Count |
|---|---:|
| `∅` | 19 |
| `{2}`, `{3}`, `{5}`, `{7}` | 10, 7, 4, 3 |
| `{2,3}`, `{2,5}`, `{2,7}` | 3, 1, 1 |
| `{3,5}`, `{3,7}`, `{5,7}` | 1, 0, 0 |
| `{2,3,5}` | 1 |
| other triples, and the four-element set | 0 |

All sixteen counts have been verified against their exact floor/ceiling
bounds. The capacities, slack, and equality between the trade-generated
histogram and the displayed rows are separately kernel-checked.

This has `19 > 4²`, so a constant-one abstract bound fails. It does **not**
refute a bound with some absolute constant, and cannot be extrapolated to
`L/k² → ∞`.

A second checked construction uses `P={2,3,5}`, `L=11`, and the three singleton
trades. Its histogram is `4·{2}, 3·{3}, 2·{5}, {2,3}, {2,5}`.

## 4. Numerical common-product bounds versus actual divisibility

### The numerical bound is redundant

For two distinct rows let `S=I_x∩I_y`. Then `m_S≥2`. If `d_S≥L`, however,
`ceil(L/d_S)≤1`, a contradiction. Therefore

```
∏_{p∈I_x∩I_y} p < L.
```

This is proved in Lean as `common_product_lt_length`. It requires only the
upper rounding bounds. For the weaker non-strict error condition, the analogous
argument gives `d_S≤L`; the distinction is at `d_S=L`.

Thus appending the numerical product bound to the exact intersection LP adds
no constraint at all. All pairs in the nineteen-row example satisfy it.

### Divisibility by the actual position difference is much stronger

If occurrences of a label `p` at positions `i,j` always satisfy `p | i-j`, then
all occurrences are in one residue class: choose any occurrence as a reference.
If every position has a label, these residue classes give a genuine cover of
the interval. In particular, common-product divisibility implies this
conclusion. No intersection-count or density assumptions are needed.

These implications are formalized as `column_residues_iff` and
`residue_cover_of_product_differences`. Enforcing full position-difference
divisibility retains the original arithmetic covering problem; it is not the
same as enforcing the numerical product bound.

## 5. A proved CRT rounding correlation missing from the abstract LP

Let `p,q>1` be coprime, and suppose `L ≡ 1 mod pq`. In the interval `[0,L)`,
if a residue modulo `p` occurs `floor(L/p)+1` times, that residue must be zero.
The same holds modulo `q`. Thus two maximal singleton counts force

```
joint count = floor(L/(pq))+1.
```

This general statement is proved in Lean as
`maximal_counts_force_maximal_pair`, using the exact formula for the number
of occurrences of a residue. It is not inferred from a search.

For the nineteen-row example, `19=3·6+1`. The counts `10` modulo 2 and `7`
modulo 3 would force joint count `4`, whereas the array has joint count `3`.
`no_residue_count_realization19` proves this incompatibility for all residue
choices.

In particular no reordering of the rows can satisfy full pair-difference
divisibility: that would place each column inside a residue class; the two
maximal singleton cardinalities force both columns to be the full classes,
contradicting the joint count. This last maximum-cardinality containment
argument is given here explicitly; the Lean example packages the count
incompatibility rather than a separate permutation/embedding theorem.

For the eleven-row example the maximal counts `6` and `4` likewise force joint
count `2`, but its joint count is `1`. This is checked separately over the six
residue pairs in Lean.

## 6. Files and verification

New files:

- `Submission/IntegerSieve.lean`: integer cube trades, capacities, exact
  Möbius inversion, covered-histogram equivalence, numerical pair-product
  implication, and reconstruction of residue columns from divisibility.
- `Submission/IntegerSieveArithmetic.lean`: exact baseline floor counts,
  `prime_cube_packing_cover`, and the general CRT rounding correlation.
- `Submission/IntegerSieveExamples.lean`: explicit arrays, all finite checks,
  a verified instantiation of the packing theorem, and arithmetic
  non-realizability of their counts.
- `Submission/verify_integer_sieve.py`: independent exact-integer verification
  of the two fixed constructions. It does not search for parameters or solve
  an LP.

Compilation commands, from `/workspace/leanproject`:

```sh
lake env lean -o .lake/build/lib/lean/Submission/IntegerSieve.olean \
  Submission/IntegerSieve.lean
lake env lean -o .lake/build/lib/lean/Submission/IntegerSieveArithmetic.olean \
  Submission/IntegerSieveArithmetic.lean
lake env lean Submission/IntegerSieveExamples.lean
python3 Submission/verify_integer_sieve.py
```

The successful output is saved in `Submission/IntegerSieveLeanCheck.log` and
`Submission/IntegerSieveFiniteCheck.log`. The main theorem roots have
`#print axioms` checks, which also check their dependencies. Their only axioms
are the standard `propext`, `Classical.choice`, and `Quot.sound` (some finite
checks use fewer). There is no `sorryAx` or conjectural assumption. Finite
checks use `decide`, not `native_decide`.

## 7. What remains unresolved

1. No family of these abstract arrays with unbounded `L/k²` has been constructed.
2. No upper bound `L≤Ck²` for all such abstract arrays has been proved.
3. In particular, no asymptotic existence theorem for the required odd-cube
   capacity packings has been proved. Treating that hypothesis as automatic
   would be a gap.
4. The general integer feasibility problem permits even rounding bits too;
   the odd-only packing criterion does not classify every possible cover.
5. Even an asymptotic abstract counterexample would only obstruct the
   intersection-count/numerical-product relaxation, not disprove Erdős 970.
6. Full difference divisibility remains arithmetic information not captured by
   those constraints. The CRT correlation above is one concrete missing
   condition, not a proof that all such conditions yield a quadratic bound.
7. No Lean proof or disproof of `Erdos970.erdos_970` has been supplied.

## Corpus evidence for the baseline status

- Costello–Watts, *A short note on Jacobsthal's function*, arXiv:1306.1064,
  `/corpus/src/1306.1064/1306.1064.tex`, introduction, lines 29–47: the uniform
  Iwaniec bound is stated as `g(n) ≤ X (k log k)²`.
- Banks–Ford–Tao, *Large prime gaps and probabilistic models*, arXiv:1908.08613,
  `/corpus/src/1908.08613/GAPS-MODEL-20190822b.tex`, lines 290–310 and 604–622:
  interval-sieve bounds and their relation to the primorial Jacobsthal gap
  `J(z)≪z²`. This is contextual evidence, not an assumption in any Lean proof.
