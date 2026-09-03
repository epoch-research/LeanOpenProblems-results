# Auxiliary rank-certificate completion — FINISHED, NOT Erdős 213

The previously external completeness of the 42-case normalized base list is
now kernel checked. All 2^21 old signings were enumerated by `decide +kernel`.
The full theorem

    AxisGlobalRankObstruction.normalized_rank_gt_six

covers all 2^28 finite-edge signings and proves normalized augmented rank > 6.
It assumes no external classification. `AxisRankGeometry` proves the actual
eight-point integral metric, all encoded magnitudes, infinity normalization,
alternation, and failure of NonTrilinear. Thus this is NOT a disproof of Erdős 213.
The formal rank conclusion is > 6, not an exact-rank-eight theorem.

All authoritative files and current oleans are complete. The final audit
`/tmp/axis_rank_final_audit.{log,exit}` exits 0; all twelve transitive axiom
audits use only propext, Classical.choice, Quot.sound. There are no pending jobs.

See the final section of Submission/Research.md for the complete file list,
proof architecture, successful artifact paths, and repaired development issues.
In particular `/tmp/axis_base_all.exit` is an OLD failed aggregation attempt;
`/tmp/axis_base_completion.exit` is the successful repaired build.

Spec.lean remains unchanged with the main sorry at line 187, SHA256
b05fe59512e4f9c3213f56bc17cbb4af5af25af385d8f547c7960ad013bf78bb.
No GP8, weak9, unbounded construction, or unrestricted general-position bound
was obtained. No incomplete proof was submitted as a settlement.
