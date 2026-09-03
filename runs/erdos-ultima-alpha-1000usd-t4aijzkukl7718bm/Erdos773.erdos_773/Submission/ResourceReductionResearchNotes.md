# Submission resource feedback and reduced main file

The conjecture is NOT settled. A submit_proof call on the old 17,291-line
Spec.lean received resource-limit feedback. It did not validate the admission.
No complete proof or disproof was obtained in the subsequent review.

## Main file changed, statement and import unchanged

Spec.lean now restores the elementary partial development from
SpecBeforeEndpoint.txt, with an explicit status note in its header:

* 2,037 lines, about 89 KiB;
* original theorem at line 2027;
* sole admission at line 2035;
* exact original quantified theorem statement unchanged;
* sole import remains `import FormalConjecturesUtil`;
* SHA-256:
  f019ff3791c89bbea24fd9b031eb92f7b676baa4b1ff9cebe9f2356121aa6ff0.

The smaller file proves the conjecture's epsilon>1/3 cases using the
previous elementary N^(2/3-o(1)) lower bound. Its admitted branch therefore
now includes epsilon=1/3, although that endpoint is independently proved
in the preserved auxiliary development. The true mathematical gap remains
0<epsilon<1/3. This is a checking-cost reduction, not an exponent advance.

Other proved main-file results include square_sidon_primorial_upper and
square_sidon_finite_log_lower. The latter is an explicit logarithmic-loss
lower bound, not the unit-coefficient endpoint. Their axiom audits, and the
audit of square_sidon_two_thirds, use only propext, Classical.choice,
Quot.sound. The original erdos_773 declaration still depends on sorryAx.

The current main olean is .lake/build/lib/lean/Submission/Spec.olean,
copied from its freshly checked /tmp/ElementarySpec-profile.olean.
Audit log: /tmp/spec-elementary-audit.log.

## Endpoint preservation

The entire prior final file is preserved exactly in
Submission/SpecEndpointBeforeResourceReduction.txt, with SHA-256
257d2e55d464b8ea5a35ca7f1257dc2f59e682772c2f52fa771ee4bfdf9b8940.

The independently checked endpoint remains in
Submission/GreedyBatchSquareEndpoint.lean and its built olean. It proves
M(N)>=N^(2/3) eventually, using only the permitted axioms. No work on that
endpoint needs to be redone. It is simply no longer consolidated into Spec.

## Local profiles

All profiles used `lake env lean -s 65536 -o ...` and standard kernel
checking. Maximum RSS is reported by Python resource.getrusage.

| Variant | Lines | Wall seconds | Maximum RSS KiB | Outcome |
|---|---:|---:|---:|---|
| Original consolidation | 17291 | 77.34 | 10387948 | checks, expected sorry warning |
| Sequential original | 17293 | 264.07 | 9941532 | checks, expected sorry warning |
| Dependency-pruned sequential | 12112 | 178.95 | 9479704 | checks, expected sorry warning |
| Restored elementary Spec | 2037 | 13.20 | 6910880 | checks, expected sorry warning |

An import-only control used 6,387,252 KiB and 4.44 seconds. Thus much of the
resident memory is the unchanged transitive Mathlib import.

JSON profiles:
/tmp/spec-profile-result.json
/tmp/spec-sequential-profile-result.json
/tmp/spec-pruned-profile-result.json
/tmp/spec-elementary-profile-result.json

## Dependency-pruning experiment

Research/Profile/Dependencies.lean traversed actual theorem dependencies
from the already clean auxiliary endpoint. It recorded 2694 project
constants, of which 1432 were in the kernel dependency closure. The data are
in /tmp/endpoint-declarations.json. This is tooling, not a proof axiom.

Research/Profile/prune_endpoint.py removed 439 unused source declarations
from the old consolidation. The final checked experiment is
Research/Profile/PrunedSpec.lean. A first draft omitted `inductive` from its
command matcher and left an unused Reach declaration referencing removed
definitions. That was fixed; the FINAL experiment checks and its endpoint
audit lists only the permitted axioms. It still has the original conjecture
admission and was NOT adopted as the final file because it remained costly.

No kernel or environment trust settings were weakened. Sequential
elaboration and linter settings in the profiling variants are only checking
configuration; current Spec does not add these settings.

## Mathematical review

Reviewed the public upper-bound types in the full-fiber, bounded-capacity,
Beatty, and reflection-symmetric modules. They still have explicit carrier
or unproved uniform-bound hypotheses. No unrestricted fixed-power upper
bound follows merely by applying them to a maximum square-Sidon set.

Reconsidered modular/checksum lifting, prime-factor selection, tensor codes,
and low-collision carriers without a valid subpower-loss amplification or
capacity-one selector. No original-conjecture exponent improved. The clean
PrimeAPFreeAlphabetCarry module from the preceding continuation remains an
auxiliary criterion obstruction only.

Do not resubmit the admitted theorem as though the resource reduction had
completed the mathematics. A genuine settlement must still remove sorryAx.
