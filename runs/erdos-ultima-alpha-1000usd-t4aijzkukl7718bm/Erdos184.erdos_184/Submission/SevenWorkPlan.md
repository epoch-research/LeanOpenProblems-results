# Seven-color pipeline — auxiliary, NOT a proof of Erdős 184

Spec.lean is unchanged and unsolved. In particular, even a completed
`SevenGraphFamily.three_core_rigid` proves rigidity only at optimum three.
No reduction of arbitrary bad cores to this optimum has been obtained.

## Checked ingredients (at this checkpoint)

- ColoredKernelLocalBounds, CyclicRowLocalBounds, CanonicalColorLocalBounds.
  They transport all-color maximum and triple minimum conditions. The
  canonical/colored predicates require an explicit extensional bridge.
- CyclicRowActionComposition: identity, composition, sequences, equality
  of actions from their color and per-row maps.
- PureSixGoodLookup: 7284 all-single six-row keys, 13 good representatives.
- PureSevenRowModel, PureSevenRowExt, PureSevenProjectionNumbers.
- PureSevenGeneratorsBase, Check00..04, assembly: five adjacent color swaps.
- PureSevenGeneratorProjectionNumbers, PureSevenGeneratorProjection.
- PureSevenActionsBase.
- PureSevenMasksBase, MaskPull0..5, MaskGood00..28, Masks.
- PureSevenFactor (conditional on CompleteAt checks).
- SevenCanonicalCounts.

Principal axiom audits use only propext, Classical.choice, Quot.sound.

## Still pending

1. Six graph classification dependencies (five pattern4 retry, six
   projections, orbit lookup/certificates, graph transport).
2. PureSevenActionsCheck00..59, then PureSevenActions: compare generator
   words with the 720 original six actions and lift their action to seven.
3. PureSevenComplete00..12, PureSevenComplete, SevenRepresentativeRows.
4. SevenRows, SevenCanonicalRaw, SevenProjection0..6 Base/Theory.
5. SixContactUniformity, SevenProjectionCode0..6, SevenCaseCompatibility.
6. SevenKernelExclusion, SevenGraphFamily.

The 203125 prefix extensions have been checked independently in exact Python,
but that is not a Lean proof. Their Lean checks remain pending.

## Performance and preservation notes

- Direct `rfl` comparing nearly identical dependent seven-row functions caused
  enormous elaboration. PureSevenRowExt instead proves six individual
  `rows_at0..5` identities and compares via their common coordinate.
- PureSevenFactor.mask_last uses commonMask_congr explicitly. The final proof
  composes equalities instead of rewriting through commonMask.
- commonMask short-circuits as soon as its partial bitwise intersection is zero.
  Preserve this. After regenerating masks, run /tmp/refine_seven_common_mask.py.
- Current Factor/RowExt sources include repairs absent from the old generators.
- PureSevenComplete files were split on 2026-08-28 into 25 subchecks each,
  fixing e0 and e1 (625 assignments per check). The existing complete_caseN
  interface is unchanged. Generator /tmp/split_seven_complete_rows.py;
  its archived unsplit sources are /tmp/PureSevenCompleteNN.lean.unsplit.
- Pattern2 six actions were similarly split by color/row before they started.
  /tmp/split_six2_action_rows.py adds BaseValid and RowValid but preserves the
  original Valid definition and all valid_interval theorem types.
- PureSixOrbitLookup0 has an ADDITIONAL GoodCertificate predicate. Its Base and
  updated Check0000 passed; other updated blocks are pending. SixOrbitKernel0
  has unverified good_of_code and catalogue lemmas. Do not regenerate from
  the old orbit scripts, which lack these extensions and Numbers-only imports.

## Queues and memory

10 GiB cgroup memory limit. Six coverage and six actions are independent.
All new heavy jobs wait for six-action parent181737, then use
/tmp/graph-pure-heavy.lock. The graph five/six queues also use that lock.
The coverage queue and later six orbit-certificate queue remain separate.

- /tmp/build_pure_six_actions.sh: parent181737.
- /tmp/build_pure_six_coverage.sh: parent187559.
- /tmp/resume_graph_after_actions.sh: parent183410; runs more-five then six.
- /tmp/build_pure_six_orbit_certificates.sh: parent188508; waits for coverage.
- /tmp/build_pure_seven_actions.sh: parent203614.
- /tmp/build_seven_graph_bases.sh: parent211664.
- /tmp/build_pure_seven_complete.sh: parent212197.
- /tmp/build_seven_graph_final.sh: parent213322.

Check actual progress/failure logs and PIDs before treating this as live state.

## Update at 2026-08-28 19:26 UTC (supersedes earlier pending lists)

- SevenCanonicalRaw passed after refactoring, SevenRows and
  SevenRepresentativeRows passed.
- All sixty PureSevenActions checks and final assembly passed. The final
  lemma is matches_group (matches is reserved).
- PureSevenComplete00..07 passed;08 and later are still running/pending.
- SevenProjection0Base/Theory and SevenProjection1Base/Theory passed.
  SevenProjection2Base is next. All seven pairs have the row_apply color
  witness repair Fin(6-i); marker indices remain Fin5. The seven renderer
  now includes the arithmetic interpolation fix.
- Six coverage1 and orbit0 certificates continue, no current failure.
- FiveCertificates4 through006 passed on the50-record rechunking retry.
- Current seven-base parent242578; orbit parent237916. They use the main
  and secondary locks respectively. Three Lean jobs are scheduled, with
  cgroup usage around3-4GB at this checkpoint (10GiB limit).

The arbitrary-optimum gap remains open. No statement in Spec was changed.

## Completion update — 2026-08-28 22:59 UTC

ALL items formerly pending above now passed, including SevenGraphFamily and
its three_core_rigid theorem. See the bottom of LiveStatus.md for final logs.
No further seven-color build queue is active. The theorem covers optimum three
only, and does not settle the original conjecture.
