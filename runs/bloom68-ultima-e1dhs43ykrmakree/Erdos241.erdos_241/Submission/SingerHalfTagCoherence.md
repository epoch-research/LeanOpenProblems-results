# Singer half-tag coherence: an exact finite audit

## Results and scope

This is a **targeted solver for tags on subsets of a full Singer perfect
difference set**, not a search for arbitrary cyclic B3 sets. “Strong B3”
always includes repeated summands.

| Case | Exact outcome |
|---|---|
| `q=11`, `k=5`, retain `n=9` | **All 220 three-point deletions are UNSAT.** No deletion symmetry reduction was used. |
| Maximum retention at `q=11` | **Exactly 8** within this Singer/tag construction. A directly verified witness is below. This is not a claim about the maximum size of an arbitrary B3 subset of `Z/665`. |
| `q=17`, `k=8`, retain `n=15` | In one **298.013-second search phase**, 172 genuine Frobenius-orbit representatives were proved UNSAT, one timed out, and 103 were unattempted. |
| Original `q=17` deletion cases | The checked group symmetry transfers the results to **504 UNSAT, 3 timeout-equivalent, and 309 unattempted** cases out of 816. No SAT witness was found. **312 cases remain unresolved; maximum retention at `q=17` is not determined.** |

Every emitted UNSAT tree has been independently checked, not merely hashed.
The `q=11` maximum-retention SAT witness was checked by **all triple multisets
directly in the cyclic CRT group**. Four inclusion-minimal UNSAT cores were
also checked. One is a 12-inequality **D4 / negation-orbit obstruction**;
another useful certificate comes from sums of saturated signed fibers.

These are finite results. They prove neither asymptotic nonexistence of the
three-deletion construction nor the original asymptotic conjecture. A finite
SAT success would not by itself disprove that conjecture either.

`Submission/Spec.lean` was not changed. None of this work invokes the original
theorem, its proposed disproof, or any Lean axiom from that file.

## 1. The exact Singer sets and the cyclic group

For the two prime fields used here, work in

\[
 F=\mathbb F_q[X]/(f(X)),\qquad g=1+X,\qquad
 v=q^2+q+1,\quad k=(q-1)/2.
\]

The generator script deterministically finds an irreducible monic cubic and
a primitive element; the outcomes are:

| `q` | `f(X)` | order of `g` | `v` | `k` | `M=vk` |
|---|---|---:|---:|---:|---:|
| 11 | `X^3 + 4 X^2 + 1` | 1330 | 133 | 5 | 665 |
| 17 | `X^3 + 3 X^2 + 1` | 4912 | 307 | 8 | 2456 |

Take

\[
 S=\{i\in\{0,\ldots,v-1\}:\operatorname{Tr}_{F/\mathbb F_q}(g^i)=0\}.
\]

The resulting sorted sets, with **zero-based indices** throughout the audit,
are

```text
q=11:
S = [2, 15, 22, 23, 32, 80, 82, 86, 104, 109, 120, 123]

q=17:
S = [1, 17, 29, 54, 92, 142, 156, 173, 178,
     186, 196, 207, 256, 262, 263, 265, 289, 304]
```

The independent verifier uses a different polynomial-multiplication formula,
walks the **entire multiplicative cycle**, and recomputes trace-zero logs.
It checks that there are respectively 120 and 288 nonzero trace-zero field
elements, each residue of `S` occurring exactly `q-1` times in those logs.
It then counts all ordered differences:

\[
 \#\{(s,t)\in S^2:s\ne t,\ s-t=h\}=1
 \quad\text{for every }h\ne0\pmod v.
\]

Thus all 132 or 306 nonzero differences are checked **exactly once**, not by
sampling. Full difference-count arrays are in `construction.json`.

For completeness, the usual perfect-difference argument is elementary here.
The trace kernel is two-dimensional over `F_q`, so has `q+1` projective
points. For `beta=g^h` not in `F_q`, the functionals `Tr(y)` and
`Tr(beta*y)` are independent. Indeed, proportionality would give
`Tr((beta-lambda)*y)=0` for every `y`; taking
`y=(beta-lambda)^(-1)` contradicts `Tr(1)=3 != 0`. Their common kernel is
one-dimensional, yielding exactly one projective point, hence one ordered
Singer difference for each nonzero `h`.

The product group is genuinely cyclic:

\[
 \gcd(v,k)=1,
 \qquad vk=\frac{q^3-1}{2}.
\]

The gcd divides `gcd(q^2+q+1,q-1)=gcd(3,q-1)=1`, since `q=2 mod 3`.
All CRT checks use the full modulus `M`, not a noncyclic group of the same
order. Changing the primitive field generator gives a unit multiple of the
logarithmic set; translating a Singer line gives a translate. The finite
claims also apply to these group-affine equivalents. No classification of
arbitrary perfect difference sets or arbitrary point reparametrizations is
assumed.

## 2. Exact coherence constraints

For a deletion set `D`, let `T=(t_0,...,t_(n-1))` be the remaining points in
increasing order and let the tags `c_i` be completely arbitrary in `Z/k`.
The base perfect-difference property already makes

\[
 A=\{(t_i,c_i):0\le i<n\}
\]

a B2 set, for every labeling: a nontrivial equality of pair sums would
contradict uniqueness of ordered nonzero base differences.

The solver enumerates **every** `i <= j <= l`, groups these multisets by
`t_i+t_j+t_l mod v`, and compares every pair in each group. A comparison
produces precisely

\[
 \sum_i a_i c_i\ne0\pmod k,
 \qquad a_i\in\{-3,-2,-1,0,1,2,3\},\quad\sum_i a_i=0.
\]

The rows are deduplicated only by exact equality and sign, with the first
nonzero coefficient positive. No division by a possibly nonunit is used to
normalize constraints. The JSON audit contains all deletion indices, all
retained bases, row-input hashes, and search statistics; rows and their
original triple witnesses are reproducible from these data.

There are `binom(n+2,3)` triples: **165 at `n=9` and 680 at `n=15`**. In
particular, the `n=9` enumeration includes 9 all-equal triples, 72 two-equal
triples, and 84 triples with distinct entries.

### Safe normalization and complete propagation

Only `c_0=0` is fixed, using simultaneous translation of all tags. Every
constraint has coefficient sum zero, so this loses no solution. **No second
tag is fixed to 1.** Unit-multiplication symmetry is not used either. In the
8-point SAT witness below the first *two* tags are both zero.

For a row with one unassigned tag `x`, write it as `a*x+b != 0 mod k`.
Let `d=gcd(a,k)`. The forbidden roots are:

* none if `d` does not divide `b`;
* otherwise the **entire coset of `d` roots** of
  `x = -(b/d)*(a/d)^(-1) mod (k/d)`.

In particular, a coefficient `2` modulo 8 can forbid zero or two values,
not an incorrectly assumed single inverse root. Negative coefficients and
the zero-coefficient residue are handled as well. Root tables were checked
against direct enumeration for `k=2,...,32`, coefficients `-3,...,3`, and all
right-hand-side residues. The C++ search additionally passed 2,000 small
randomized comparisons with brute force.

Domains are rebuilt from the current partial assignment. A zero completed
row or an empty domain is a conflict. Otherwise a smallest-domain variable
is branched on, with a deterministic constraint-degree tie-breaker, and
**every remaining value** is visited. This is forward checking, not a
heuristic claim of infeasibility. A deadline or node limit returns `TIMEOUT`,
never `UNSAT`.

## 3. The complete `q=11` refutation audit

All `binom(12,3)=220` deletions were solved individually, including inequivalent
ones. The full systems have between 54 and 61 inequalities.

| Audit quantity | Value |
|---|---:|
| SAT / UNSAT / timeout | **0 / 220 / 0** |
| normalized assignments per deletion | `5^8 = 390625` |
| total normalized assignments covered | **85,937,500** |
| search-tree nodes | **190,581** |
| nodes per deletion, minimum / maximum | 511 / 1454 |
| accumulated C++ search time | 0.149359 seconds |
| whole generator/search/output phase | about 0.766 seconds |
| raw proof bytes, all 220 trees | 478,026 |
| compressed proof bytes, all 220 trees | 61,746 |

“Covered” does not mean every assignment was separately visited: conflicts
and forbidden roots certify entire subcubes. The independent checker proves
that these subcubes exhaust all `5^8` assignments for each deletion.

### The requested capacity precondition really passes

A reduced signed fiber consists of distinct vectors `e_a+e_b-e_c`, including
the singleton reductions `e_s`. For a B2 base its total number of vectors is

\[
 n^2(n-1)/2+n.
\]

Every one of the 220 deletions has largest signed fiber at most `k=5`:
171 have maximum 5 and 49 have maximum 4. The numbers of saturated fibers
are distributed as follows:

```text
number of saturated fibers:  0   1   2   3   4   5
number of deletions:        49  54  81  18  15   3
```

Thus the search is addressing **coherent labeling**, not rediscovering an
individual signed-fiber capacity obstruction.

## 4. Exact maximum retention at `q=11`: eight

Deleting the four points `{2,15,22,32}` (indices `{0,1,2,4}`) gives this
solution, in retained-base order:

| base `s` | tag `c_s mod 5` | CRT representative in `Z/665` |
|---:|---:|---:|
| 23 | 0 | 555 |
| 80 | 0 | 80 |
| 82 | 1 | 481 |
| 86 | 2 | 352 |
| 104 | 1 | 636 |
| 109 | 1 | 641 |
| 120 | 0 | 120 |
| 123 | 0 | 655 |

Equivalently the sorted cyclic set is

```text
[80, 120, 352, 481, 555, 636, 641, 655]  in Z/665.
```

The primary and independent CRT verifiers use opposite CRT formulas. Both
check the coordinates and directly enumerate all **120 triple multisets**;
all 120 sum residues are different. The 36 pair-sum residues are also
different.

Since every nine-point retained subset is UNSAT, heredity of B3 rules out
all retained sizes at least nine. This eight-point witness therefore proves
**maximum retention exactly eight**, not just a lower bound. The retention
phase tried two lexicographic four-point deletions: the first was UNSAT and
the second gave this witness. It did not claim all four-point deletions are
equivalent or enumerate their SAT counts.

## 5. Small cores and a structural identity without saturated fibers

Constraint deletion in eight deterministic orders, also starting from a
saturated-fiber certificate when available, produced these cores:

| deleted indices | deleted base points | core rows | rank over `F_5` |
|---|---|---:|---:|
| `{0,1,2}` | `{2,15,22}` | 22 | 6 |
| `{0,1,7}` | `{2,15,86}` | **12** | **4** |
| `{0,2,6}` | `{2,22,82}` | 23 | 7 |
| `{5,6,8}` | `{80,82,104}` | 32 | 8 |

Each core has a checked UNSAT tree. Removing **any one** of its rows has an
explicit satisfying tag vector, independently checked against every other
core row. These vectors certify *core minimality*, not a B3 labeling of the
full instance. The cores are **inclusion-minimal**; no minimum-cardinality
claim is made.

### A 12-row D4 certificate

For deletion `{2,15,86}`, the retained set is

```text
[22, 23, 32, 80, 82, 104, 109, 120, 123].
```

There is **no saturated signed fiber** in this instance: its maximum fiber
size is four. The following 12 constraints already contradict coherence.
The unused tag at 22 does not occur. Write

\[
 (a,b,c,d,e,f,g,h)=(c_{23},c_{32},c_{80},c_{82},c_{104},c_{109},c_{120},c_{123}).
\]

Let `R_j` be the tag sum on the left minus the tag sum on the right in this
table. The row numbers are the exact zero-based IDs in the full CSP.
All the displayed base equalities are modulo 133, and strong B3 requires
every `R_j != 0 mod 5`.

| row | left base triple | right base triple |
|---:|---|---|
| 2 | `(80,109,120)` | `(82,104,123)` |
| 9 | `(32,32,123)` | `(80,120,120)` |
| 10 | `(32,32,109)` | `(82,104,120)` |
| 12 | `(23,82,82)` | `(32,32,123)` |
| 14 | `(23,80,120)` | `(32,82,109)` |
| 17 | `(23,82,82)` | `(80,120,120)` |
| 19 | `(23,82,109)` | `(104,120,123)` |
| 20 | `(23,32,123)` | `(82,109,120)` |
| 21 | `(23,32,80)` | `(82,82,104)` |
| 22 | `(23,23,82)` | `(32,109,120)` |
| 23 | `(23,23,80)` | `(32,104,123)` |
| 26 | `(23,23,32)` | `(104,120,120)` |

Define four linear expressions over `F_5` by

\[
 2\begin{pmatrix}L_0\\L_1\\L_2\\L_3\end{pmatrix}
 =
 \begin{pmatrix}
  1&-2& 1& 1&-1& 1& 1&-2\\
 -1& 2& 1&-3&-1& 1& 1& 0\\
 -3& 0&-1& 1& 1& 1& 1& 0\\
 -1&-2& 1&-1& 1&-1& 3& 0
 \end{pmatrix}
 \begin{pmatrix}a\\b\\c\\d\\e\\f\\g\\h\end{pmatrix}.
\]

The following identities can be checked over the integers after multiplying
by 2; they do not depend on a numerical search:

| pair | `L_i+L_j` | `L_i-L_j` |
|---|---|---|
| `0,1` | `R_2` | `R_12` |
| `0,2` | `-R_20` | `R_23` |
| `0,3` | `-R_9` | `R_19` |
| `1,2` | `-R_22` | `R_21` |
| `1,3` | `-R_17` | `R_10` |
| `2,3` | `-R_26` | `-R_14` |

Consequently all `L_i +/- L_j` for `i<j` must be nonzero. The four `L_i`
would have to belong to distinct negation orbits of `Z/5`, but these orbits
are only

\[
 \{0\},\qquad\{1,4\},\qquad\{2,3\}.
\]

**Four values cannot occupy three orbits.** This proves the 12-row core
UNSAT directly. The repeated base triples in the table are essential
constraints, not optional diagonals.

This gives a potentially reusable obstruction: if a coherent-label system
forces `m` expressions to satisfy all inequalities `L_i +/- L_j != 0`, then

\[
 m\le \frac{k+\gcd(2,k)}2,
\]

the number of negation orbits in `Z/k`. For odd `k` this is `(k+1)/2`.
One would need a **growing** such arrangement to obtain an asymptotic
obstruction. The displayed D4 system alone only contradicts the small tag
capacity here. In particular, **halving these integer expressions modulo 8
would be invalid**; no conclusion for `q=17` is drawn from this D4 proof.

## 6. A second reusable identity: sums of saturated signed fibers

If two distinct reduced signed vectors in the same base fiber had the same
tag, cross-multiplying the negative summands would give two distinct triple
multisets with equal sums. Thus strong B3 requires the signed-fiber tag map
to be injective.

When a signed fiber `F_h` has exactly `k` vectors, its tags must therefore be
a permutation of `Z/k`. Necessarily

\[
 W_h(c):=\sum_{u\in F_h}u\cdot c
       =\sum_{r=0}^{k-1}r
       =\frac{k(k-1)}2\pmod k.\tag{1}
\]

This right-hand side is **zero for odd `k` and `k/2` for even `k`**. It must
not be treated as zero modulo 8. Equation (1) couples different fibers
through the same point labels, despite each fiber passing capacity alone.

For `q=11`, span tests of these linear identities alone force a forbidden
triple equality in **six** of the 220 deletions. They do not explain all 220;
49 cases have no saturated fiber at all.

Here is a fully explicit example. Delete `{2,22,82}` (indices `{0,2,6}`),
so

```text
T = [15, 23, 32, 80, 86, 104, 109, 120, 123].
```

Three saturated signed fibers, each with five entries, are:

| `h mod 133` | signed representatives `a+b-c` |
|---:|---|
| 4 | `32+120-15`, `80+80-23`, `123+123-109`, `23+104-123`, `15+109-120` |
| 52 | `80+120-15`, `104+104-23`, `86+86-120`, `23+109-80`, `15+123-86` |
| 128 | `23+120-15`, `80+80-32`, `104+104-80`, `109+123-104`, `32+86-123` |

Summing their tag expressions gives

\[
\begin{aligned}
 W_4&=c_{32}+2c_{80}+c_{104}+c_{123},\\
 W_{52}&=c_{86}+2c_{104}+c_{109}+c_{123},\\
 W_{128}&=-c_{15}+c_{23}+c_{80}+c_{86}+c_{104}+c_{109}+c_{120}.
\end{aligned}
\]

All three must vanish modulo 5 by (1), but

\[
 4W_4+W_{52}+4W_{128}
 =c_{15}+2c_{80}-c_{23}-c_{32}-c_{120}\pmod5.
\]

The expression on the right must be **nonzero**, since

\[
 15+80+80=23+32+120=175
\]

are distinct base triple multisets. This is a direct coherence contradiction.
The corresponding certificate uses 26 distinct inequalities before greedy
minimization; the extracted inclusion-minimal core has 23 rows.

## 7. The capped `q=17` experiment and its valid symmetry

Here `n=15`, `k=8`, `v=307`, `M=2456`. There are 816 three-point deletions.
For this phase only, use the explicitly verified automorphism

\[
 (s,c)\longmapsto(17s,c),
 \qquad x\longmapsto17x\pmod{2456}.
\]

It is valid because `17` is a unit modulo 2456, `17=1 mod 8`, and the trace
kernel is Frobenius-invariant. It has order three. The explicit permutation
of all 18 Singer indices and the **entire orbit partition** are in the data
and independently checked. There are 270 deletion orbits of size three and
six fixed deletion triples, hence **276 representatives**. This is not an
assumption that all deletion triples are equivalent and is not a PGL2
reparametrization.

The deterministic priority list includes anchor deletions, all six fixed
triples, extrema of the constraint and saturated-fiber counts, and
constraint-profile quantiles. Other representatives follow lexicographically.
Across all representatives the CSPs have 529–542 inequalities. Every signed
fiber has size at most eight; this capacity claim is checked even for the
unsearched representatives and then transferred by the same valid symmetry.

There is one total **300-second wall-clock search-phase cap**, including
construction, target selection, solver calls, input/output, and compressed
proof writing. Individual representatives receive at most five seconds.
Two seconds of shutdown headroom are reserved. Actual outcomes:

```text
search phase wall time:                  298.013097 seconds
accumulated C++ search time:              249.267057 seconds
representatives attempted:               173 / 276
  proved UNSAT:                          172
  TIMEOUT:                                 1
unattempted representatives:              103

original deletion cases via symmetry:
  proved UNSAT:                          504
  equivalent to timed-out representative:  3
  unattempted:                           309
  total:                                 816
```

The last representative, indices `{2,6,12}`, deletes points `{29,156,256}`.
It received only the remaining **222 ms** and timed out. Its orbit consists
of index triples

```text
{2,6,12}, {3,9,10}, {4,13,17}.
```

It is **not UNSAT** in the reported result. Nor are the 103 unattempted
representatives silently classified as UNSAT.

The 172 complete trees contain **22,184,909 nodes** and certify
`172 * 8^14 = 756,463,999,909,888` normalized assignments. The independent
checker validated them all. The single timeout's partial tree is not used
as a refutation. Full independent verification, including the `q=11` files,
took about 151.45 seconds **separately from the search**; it performs no new
tag-assignment search. No additional `q=17` solver runs were made after the
five-minute phase.

## 8. Reproduction and certificate format

All new files are under `Submission/`:

* `singer_half_tag_coherence.cpp` — exact forward-checking solver, forbidden-root
  arithmetic, brute-force self-tests, and refutation-tree output.
* `singer_half_tag_coherence.py` — exact finite-field construction, all constraints,
  targeted runs, retention search, and structural core extraction. The field
  implementation intentionally supports **prime** `q` here, including 11 and 17;
  it does not silently treat arbitrary prime powers as prime fields.
* `singer_half_tag_verify.py` — independent field/difference/constraint/CRT and
  certificate verifier. It does **not** import the generator or call the solver.
* `singer_half_tag_verify_tree.cpp` — independent fast tree checker for the larger
  `q=17` proofs; it enumerates roots rather than using modular division. The
  transparent Python tree checker remains available with `--python-trees`.
* `singer_half_tag_regression.py` — solver tests, agreement of both independent
  tree backends, rejection of malformed trees even with their hashes updated,
  and a **negative weak-only fixture** demonstrating why repeated triples matter.
  That fixture is explicitly not a strong-B3 success and runs no `q=17` tag search.
* `run_singer_half_tag_coherence.sh` — full regeneration and verification commands.
* `singer_half_tag_results/` — constructions, all instance results, four cores
  with criticality witnesses and structural identities, compressed proofs,
  search/verification logs, regression results, and a SHA-256 inventory.

Key result files are `q11_three_deletions.json`, `q11_retention.json`,
`q11_cores.json`, `q17_three_deletions.json`, and `verification.json`.

### Check the saved audit without rerunning the search

From `/workspace/leanproject`:

```bash
python3 Submission/singer_half_tag_verify.py
python3 Submission/singer_half_tag_regression.py
(cd Submission && sha256sum -c singer_half_tag_results/SHA256SUMS)
```

For just the complete, small `q=11` audit:

```bash
python3 Submission/singer_half_tag_verify.py \
  q11_three_deletions.json q11_retention.json q11_cores.json
```

The verifier reconstructs every constraint before checking the tree and
checks all SAT triple sums in the CRT group. It is not relying on the
search program's status strings or statistics. By default it only prints a
fresh verification report, leaving the saved audit and its inventory unchanged;
`--write-report` explicitly refreshes `verification.json`.

### Regenerate

Only Python 3, `g++` with C++17 support, and the standard libraries are required;
Sage, a SAT package, and Lean are not needed. The small `q=11` certificate check
uses Python alone.

```bash
bash Submission/run_singer_half_tag_coherence.sh
```

The individual generator phases are:

```bash
python3 Submission/singer_half_tag_coherence.py prepare
python3 Submission/singer_half_tag_coherence.py q11
python3 Submission/singer_half_tag_coherence.py retention
python3 Submission/singer_half_tag_coherence.py cores
python3 Submission/singer_half_tag_coherence.py q17
```

The `q=11` trees and core choices are deterministic. Timings and how many
`q=17` representatives fit under the wall-clock cap are machine-dependent;
a rerun must report its own timeouts and unattempted cases.

### What a refutation file certifies

An uncompressed proof starts with `SHTC1 n k m`. Tags start unassigned except
for the justified normalization `c_0=0`. The remaining tokens form a preorder
tree:

* `-1` means the independently recomputed constraints yield a completed zero
  row or an empty forward-checked domain;
* a nonnegative variable index branches on that unassigned variable, with
  one child for **every** allowed value in increasing order.

The checker recomputes all forbidden values from the original rows. It rejects
invalid leaves, missing children, extra children, assigned branch variables,
and a refutation reaching a satisfying assignment. At every node it verifies
coverage of the whole remaining assignment cube. Row-input hashes and proof
hashes bind the certificate to its recorded deletion, but **semantic tree
checking**, not those hashes, is the UNSAT evidence.

`Spec.lean` retained SHA-256:

```text
fa08ffd0daf6d26c138eb7da5a4186d0abd9155428d0c4528526a570b398d860
```

## 9. What remains mathematically open here

The complete finite conclusion is maximum retention eight at `q=11` for this
Singer/tag family. The `q=17` conclusion is only the capped partial audit
above. The original asymptotic problem is untouched.

If solutions with `n=q-2` existed for arbitrarily large admissible `q`, then

\[
 \frac{n}{M^{1/3}}
 =\frac{q-2}{((q^3-1)/2)^{1/3}}\longrightarrow2^{1/3}>1.
\]

A cyclic strong-B3 set gives an integer strong-B3 set by taking representatives
in an interval of length `M`. Thus an **unbounded family**, not an isolated
finite success, would supply the relevant fixed-excess mechanism. Conversely,
finite UNSAT at `q=11`, even combined with the partial `q=17` audit, proves no
asymptotic nonexistence.

The reusable insights found here are the **negation-orbit arrangement bound**
and the **saturated-fiber sum identity**. Establishing appropriately growing
instances of either mechanism for arbitrary Singer sets would require new
mathematics; this report does not assume that step.
