# Characteristic-three invariant Singer half-tags: exact q=27 audit

## Result and scope

**All 90 requested cases are UNSAT**, with independently checked exhaustive
refutation trees **and elementary, case-specific negation-orbit certificates**.
This is a targeted audit of **constant labels on full Frobenius orbits**, not
an unrestricted search for integer or cyclic B3 sets.

| Deleted from the 28-point Singer set | Retained n | Cases | Tag variables | Triple multisets per case | Distinct inequality rows | Result |
|---|---:|---:|---:|---:|---:|---|
| One full 3-orbit, infinity retained | 25 | 9 | 9 | 2,925 | 1,305–1,321 | All UNSAT |
| Infinity and one full 3-orbit | 24 | 9 | 8 | 2,600 | 965–975 | All UNSAT |
| Two full 3-orbits, infinity retained | 22 | 36 | 8 | 2,024 | 613–626 | All UNSAT |
| Infinity and two full 3-orbits | 21 | 36 | 7 | 1,771 | 435–449 | All UNSAT |

There were **no timeouts and no unattempted cases**. All cases were tested
individually, in the displayed order; no deletion equivalences were assumed.
The total new search charge, including structural-certificate discovery, was
**1.597622 seconds**, below the 300-second cap. Solver-process wall time was
0.385247 seconds; the solver's internal DFS time was 0.127496 seconds. Field
construction, model generation, compilation and independent verification are
not searches and are excluded from these search figures.

Since all seven-full-orbit subsets without infinity fail, heredity gives the
additional **upper bound n <= 19 for any Frobenius-invariant retained subset
with orbit-constant tags in this q=27 model**. Its size is 3r or 3r+1, and r >= 7
would contain an audited n=21 subset. **Attainment at n=19 was not tested**;
this is not an exact maximum. The requested comparison threshold is
`9841^(1/3) = 21.4295512779...`: even all requested n=21 cases fail.

These are finite, model-specific conclusions, **not an obstruction to arbitrary
pointwise labels, other q, or an infinite family**. An infinite family retaining
q-O(1) would have n^3/M tending to 2; a finite SAT result alone would not establish
one or disprove an asymptotic claim. No q=81 search was made. No Lean theorem is
asserted or changed. All 499 pre-existing non-cache files under `Submission/`
were hashed before this work and checked unchanged, including `Spec.lean`,
`Reductions.lean`, `SignedSums.lean`, and the existing audits.

## Field, Singer set, and actual cyclic coordinates

Use the explicit tower

    F27 = F3[u]/(u^3-u-1),
    a = 2u^2,     Tr_(F27/F3)(a) = 1,
    K = F27[theta]/(theta^3-theta-a),     g = theta.

Here `theta^27 = theta+1`, `theta^729 = theta+2`, and **g has order 19,682**.
The full multiplicative cycle is enumerated, not just a sample or a probable
primitive-element test. We have `g^757 = a`, a generator of F27*, and
`g^9841 = -1`. Define

    v = 757, k = 13, M = vk = 9841,
    S = { e mod v : Tr_(K/F27)(g^e) = 0 }.

There are exactly 728 nonzero trace-zero field elements, giving 28 projective
points, each appearing 26 times. All 756 nonzero ordered base differences
occur exactly once. Infinity is the identity projective point, with base 0.
The other points, with the zero-based orbit IDs used in every data file, are:

| Orbit | Bases in Z757 | Norm w = a+t^3-t, encoded in F27 |
|---:|---|---:|
| 0 | 1, 27, 729 | 18 |
| 1 | 3, 81, 673 | 23 |
| 2 | 9, 243, 505 | 26 |
| 3 | 43, 310, 404 | 21 |
| 4 | 129, 173, 455 | 24 |
| 5 | 220, 641, 653 | 20 |
| 6 | 387, 519, 608 | 19 |
| 7 | 409, 445, 660 | 22 |
| 8 | 466, 470, 578 | 25 |

F27 encoding is `b0+3b1+9b2` for `b0+b1*u+b2*u^2`; tower encoding is
`x0+27*x1+729*x2`. Each non-infinity projective point is represented uniquely
by `theta+t`. All 27 distinct t are checked and saved in point order.
Frobenius sends t to t+1, and the nine displayed w are **exactly the nine
trace-one elements of F27**, each identifying one 3-orbit. Thus arbitrary
invariant norm-label functions are allowed; they are not eliminated by an
assumed off-S fixed-fiber obstruction.

The variables c_j are **actual cyclic CRT tags**: for s in orbit j set

    A_s = s + 757 * (9*(c_j-s) mod 13)  in Z9841.

Infinity has its own independent variable when retained. Since `gcd(757,13)=1`
and **27 = 1 mod 13**, `(s,c) -> (27s,c)` is exactly multiplication by 27 in
Z9841. Orbit-constant tags therefore give genuine cyclic Frobenius invariance.
No point variables are assigned independently within an orbit.

For clarity about norm versus scalar labels: if `e_t = log_g(theta+t)`, then
`e_t mod 13 = log_a(w) mod 13`. Multiplying theta+t by `a^d` changes its cyclic
tag by `757d = 3d mod 13`. Hence any desired invariant tag c is obtained with
`d = 9*(c-log_a(w)) mod 13`, a function of w. This respects the new invariant
norm-label class rather than imposing a spurious constraint on it.

## Exact coherence and safe normalization

For **every multiset** `i <= j <= l` of retained points, compute its base sum
h in Z757. Compare every pair of distinct multisets in each h-fiber. If
N(U) is the vector of **orbit counts**, including multiplicity and the
independent infinity coordinate, impose

    (N(U)-N(W)) dot c != 0 mod 13.

This is necessary and sufficient for distinct triple-multiset sums in the
cyclic CRT group. All-equal, exactly-two-equal and all-distinct triples are
included. No zero count-difference row is silently dropped (none occurs in
these instances). Rows are deduplicated only by equality and sign. Every
saved row has its original two base triples as a witness.

Only **the first retained full-orbit tag is fixed to 0**, by simultaneous tag
translation; every row has coefficient sum zero. No second tag is fixed to 1,
and no unit-label normalization is used. All full-orbit triples have base sum
0, so they force `3(c_i-c_j) != 0`, hence distinct full-orbit labels. When
infinity is present, comparison with `(infinity,infinity,infinity)` also
forces `c_i != c_infinity`; this is derived, not imposed without a witness.

The generic solver and separate tree checker were copied byte-for-byte to
new prefixed files. The tree checker independently enumerates all forbidden
residues, checks every permitted branch, and checks complete weighted coverage
of `13^(r-1)` normalized assignments. It checked **14,130 nodes across all 90
refutations**. The uncompressed proofs total only 39,147 bytes (8,806 compressed).
A truncated tree, a surplus-node tree, and a false root-conflict tree were all
rejected as negative controls.

The Python verifier does **not import the generator or invoke the solver**.
It independently rebuilds the field instead as

    F3[X]/(X^9-X^6-X^4-X^2-X+1),
    theta=X, w=X^3-X, u=w^2+w,

walks the entire primitive cycle, and independently regenerates every repeated
triple and orbit-count constraint. Its SAT path uses the alternative CRT formula
`c+13*((s-c)*13^(-1) mod 757)` and checks all triple sums, all pair sums,
distinct parameters and actual cyclic Frobenius invariance. No audited case
was SAT; a fixed three-point orbit and a repeated-triple collision are only
positive/negative verifier controls, not additional searched deletion results.

## Elementary structural obstruction, not merely finite SAT refutation

For **each of the 90 cases**, the extraction code finds seven label-difference
forms L_1,...,L_7 and original triple inequalities certifying

    L_i != 0,     L_i-L_j != 0,     L_i+L_j != 0   (i<j)  in F13.

There are only six nonzero negation orbits:

    {1,12}, {2,11}, {3,10}, {4,9}, {5,8}, {6,7}.

Seven forms cannot occupy six such orbits. This proves UNSAT without trusting
a search tree. All **4,410 linear identities** linking these expressions to
nonzero multiples of original rows were independently checked. These
certificates use **34–49 original inequalities per case**; minimality is not
claimed. A separate redundant certificate for every case forces 14 linear
forms to be pairwise distinct in F13.

A particularly compact example deletes infinity and orbits 4 and 5. Write
c_j for the label on orbit j. The seven forms are

    c1-c2, c2-c3, c2-c7, c2-c8, c3-c7, c3-c8, c7-c8.

The last six are all differences of the four labels c2,c3,c7,c8: their +/-
values would already exhaust F13*, leaving no place for the extra nonzero
c1-c2. **34 original triple inequalities suffice.** For example, row 29 is

    (243,243,466) = (43,404,505) = 195 mod 757,

which forces `c2-2*c3+c8 != 0`; the repeated entries are essential.
The complete 34-row triple table and all 49 identities are in
`char3_invariant_tag_results/char3_invariant_tag_example_certificate.md`
and the companion `char3_invariant_tag_example_core.json`.
Some witnesses use other retained orbits whose tag counts cancel. Five active
labels in these forms do **not** imply an obstruction on just five full orbits.

## Artifacts and independent verification

All new files have the `char3_invariant_tag_` prefix. Python uses only the
standard library; the two native sources require a C++17 compiler. From
`/workspace/leanproject`:

```sh
# Main independent verification: field + all models + all trees + both
# structural certificates per case + 34-row example + negative controls.
python3 -B Submission/char3_invariant_tag_verify.py

# Optional integrity check (not a substitute for the verifier).
sha256sum -c Submission/char3_invariant_tag_SHA256SUMS
```

Expected result: `status: PASS`, all 90 UNSAT, 14,130 checked tree nodes,
90 checked negation certificates, and 499 pre-existing files unchanged.
`char3_invariant_tag_results/char3_invariant_tag_verification.json` is the
consolidated exact-result summary. The same directory stores the field,
all complete models/row witnesses, individual `.rows` inputs and `.tree.gz`
proofs, both structural-certificate collections, and the shared search ledger.
`char3_invariant_tag_results.json` records the original solver phase;
`char3_invariant_tag_search_ledger.json` also includes certificate discovery.

To replay in a **fresh** directory without replacing the saved audit:

```sh
out=$(mktemp -d /tmp/char3_invariant_tag_replay.XXXXXX)
python3 -B Submission/char3_invariant_tag_audit.py prepare --out "$out"
python3 -B Submission/char3_invariant_tag_audit.py run --out "$out"
python3 -B Submission/char3_invariant_tag_structure.py cliques --out "$out"
python3 -B Submission/char3_invariant_tag_structure.py negation --out "$out"
python3 -B Submission/char3_invariant_tag_structure.py example --out "$out"
python3 -B Submission/char3_invariant_tag_verify.py --out "$out"
```

The replay has its own persistent 300-second search ledger; timeout is never
reported as UNSAT. All 182 construction/model files were regenerated in a
separate directory and compared byte-for-byte with the saved audit, without
performing any further coherence search.
