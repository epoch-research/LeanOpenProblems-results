# Status: not settled

Neither `Erdos28.erdos_28` nor `Erdos28.erdos_28.disproof` has a complete proof. `Spec.lean` is byte-for-byte unchanged and still contains both original admissions. No proof claim has been submitted.

Verified original SHA-256:

```
f807f31afd224befa929b3178bb43020348a6e07d9c266933b5d171b4ba65b1a
```

## Kernel-verified partial results

`Reduction.lean` proves the relevant limsup/boundedness equivalences and finite-filling normalization. The outstanding mathematical assertion is exactly:

> For every natural number K, there is no set A of nonnegative integers with A+A=N and with every ordered two-term representation count at most K.

No proof of this assertion is present in the development.

`FiniteCertificate.lean` gives a sound finite decision-tree checker and the following checked obstructions:

| Global ordered cap | Required coverage of the initial interval |
|---|---|
| 2 | 0 through 5 |
| 3 | 0 through 11 |
| 4 | 0 through 46 |
| 5 | 0 through 60 |

In each row, coverage forces some representation count to exceed the indicated cap. The violating target need not lie within the covered interval. These are global-cap results, not a proof for arbitrary K or arbitrary eventual caps. The computation uses `decide +kernel`, not `native_decide`.

The two Lean files and the finite-certificate regression tests have been independently compiled. Axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.

An additional independently compiled elementary graph encoding is in `/tmp/et_ordered_graphs/GraphEncoding.lean`. It is not a proof of the conjecture.

## Latest mathematical investigations

The following directories contain mathematical arguments, scope audits, and exact checks. Their reports explicitly distinguish restricted results and relaxation models from a settlement.

- `/tmp/et_correlated_fibers/`: correlated finite-fiber fourth-order models and the missing recursive common-endpoint consistency.
- `/tmp/et_origin_rigidity_next/`: a coverage-preserving private-target surgery whose cap can increase, and an origin-rigid full-basis control with unbounded counts.
- `/tmp/et_flexible_geometry/`: restricted geometric design and differential-atlas obstructions; no general integer extension or exclusion.
- `/tmp/et_ordered_graphs/`: the obstruction to applying undirected common-neighbor bounds; a genuine bounded basis over nonnegative dyadic rationals, not over the integers.
- `/tmp/et_factorial_multitorus/` and `/tmp/et_factorial_audit/`: independently derived logarithmic difference-form growth, but explicit failures of the proposed higher-transpose and factorial-Hankel positivity steps. The bounded fiber models are not global additive-set constructions.
- `/tmp/et_causal_containers/`: exact full-prefix seed encodings and integer escape cuts, but no uniform obstruction. Feasibility is not hereditary in optional-seed coordinates.

The missing step remains a uniform argument retaining all three conditions at once: every integer deadline from the origin, exact common integer endpoints, and the pointwise cap. None of the partial results has been installed as a target proof or represented as one.


## Latest continuation: still no uniform proof

The positive-difference-closure (DC) work is in `/tmp/et_difference_closure/`, `/tmp/et_difference_closure_audit/`, and `/tmp/et_dc_joint_covers/`. Numerical prefixes inherit DC exactly, but no cap-dependent cardinality bound has been proved. The improved coordinate-growth bound remains compatible with the quadratic lower bound from bounded representations. `Foundation.lean` and `Controls.lean` in the first directory were independently compiled and axiom-audited; they contain elementary facts and controls, not the missing uniform theorem.

The addition-chain investigation in `/tmp/et_internal_chain_uniform/` also remains incomplete. It proves an explicit internally generated positive-integer set with ordered cap four and growth of order `log N * log log N`. Its higher-sum counts are unbounded. This is not an additive basis and not a counterexample to Erdős–Turán; it rules out promoting the two-sum cap to a higher-sum cap merely from internal generation. The proposed general `o(sqrt N)` bound for internally generated capped sets was not proved.

The final synthesis in `/tmp/et_uniform_final_synthesis/` retains actual endpoints in a legal-reassociation count. Writing `r(t)` for ordered sum counts and `q(t)` for positive-difference counts, its noncanonical merger statistic is

```
Λ(S) = sum_{t>0} r(t) q(t) (q(t)-1).
```

The pointwise cap gives only a quadratic upper bound for this statistic. No contradictory lower bound from full rooted coverage was obtained. DC already implies internal generation after shifting by one, so these are not independent hypotheses that can simply be combined to obtain a contradiction.

The parent independently read the relevant arguments and reran both sets of predetermined arithmetic identity checks. These are not Lean proofs of the conjecture or exhaustive searches. `Spec.lean` was again verified against its original SHA-256, with its original import, both theorem declarations, and both admissions unchanged. Formalization of a target and proof submission remain deferred for lack of a complete mathematical argument.


## All-shift and adjacent-channel continuation

No complete argument was obtained in this continuation either.

- `/tmp/et_all_integer_shifts/` keeps every initial root of `A+h`. A labelled binary-forest count bounds the number of higher representations that can be regrouped at a given shift while retaining actual intermediate members. Full coverage does not supply the missing regrouping guarantee. This is a necessary bound under the hypothetical capped-basis assumptions, not a contradiction.
- `/tmp/et_mixed_uniform_next/` gives an exact decomposition of adjacent-target representation counts into eroded complementary channels. Individual self-caps decrease, but only the union of channels is known to cover. A mandatory path-variation lower bound has no contradictory upper bound.
- `/tmp/et_adjacent_self_recursion/` sharpens the first-level mixed caps in the self-parent case. It also supplies actual common-parent examples showing why cross-label composition does not automatically yield another cap decrease. Those examples have explicitly missing initial targets and are not counterexamples to the conjecture.

The parent independently checked the counting arguments and reran the predetermined arithmetic audits in all three directories. The unresolved issue is still a uniform, coverage-preserving argument using the common integer endpoints. The original SHA-256 of `Spec.lean` was verified again; both original admissions remain, and no proof claim was submitted.
## Maximal-fiber and final full-coverage checks

These checks also produced no settlement.

- `/tmp/et_maxfiber_next/` proves exact rigidity of an actual saturated fiber and constructs uniformly capped extensions of arbitrary finite cores with remote saturated fibers and private cross-pairs. The extensions preserve supplied covered prefixes but retain the core's first gap; they are **not full bases**. Exact loss repair can reduce the selected fiber while increasing the global cap to `K * ceil(K/2)`. Full-basis minimality cannot be applied to these controls.
- `/tmp/et_final_full_coverage/REPORT.md` records the final independent check. Exact loss repair of a full basis does preserve every integer deadline. However, a single optional deletion `f` requires at least a half-cap bound on its private partners: if `U` is the private-partner set with `f` removed, the repaired count satisfies `r_R(t+f) >= 2*r_U(t)`. No bound sufficient for descent was obtained. The full coupled parity equations were checked, but no induction for general mixed multiplicity follows.

The parent checked the counting maps and the scope of the conclusions. `Spec.lean` was recompiled and verified against its original SHA-256; it still has both original admissions. The requested task is **not completed**. Target formalization and proof submission remain deferred because there is no complete mathematical proof or disproof.

## Consecutive-gap translate-cover continuation

`/tmp/et_gap_translate/REPORT.md` contains the next independent investigation and parent audit. Consecutive cuts around an actual member of A give exact common-rectangle representation identities. The total number of incidences using the middle row is at most `O_K(sqrt(M) * log(M))`, by a geometric doubling argument for each fixed other endpoint. The parent checked the proofs and ran the specified arithmetic regression checks.

This does not lower the cap on the covering common rectangle: the cap saving occurs only at the exceptional middle-row incidences. No full-coverage-sensitive linear lower bound for those incidences was proved. Counting one pair in two overlapping rectangles does not create two different representations. No complete proof or counterexample resulted; the target file and its two original admissions remain unchanged.

## Chronological escape continuation

`/tmp/et_chronological_final/REPORT.md` records a further independent check of the exact forced/optional recursion. Dead states have explicit certificates involving a strictly later sum; the parent checked the formula and 1,401 specified instances. No proof of termination for arbitrary K was obtained. Internal decompositions of optional members give triples, not new two-term representations without additional membership. The full basis `{0,1} union {2+3j:j>=0}` demonstrates this merger failure, but its representation counts are unbounded, so it is not a counterexample. Existing positive-history identities retain a growing budget and do not provide descent. The requested theorem remains unresolved.
