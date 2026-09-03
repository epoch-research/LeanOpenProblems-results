# Structured host, two-sided reset, and exhaustive-schedule absorption

## Original conjecture status

The conjecture in `Spec.lean` remains unproved and undisproved. The file is
unchanged, and no proof has been submitted. Its SHA256 remains

    32d7caa914aad816045b3efa978ba8171e246a4dc01a8e77f192008b25ff41a0

The new absorption result concerns a particular reset procedure. It is NOT
a negation of the existential statement in `Spec.lean`.

## Structured high-coefficient host

`Erdos66StructuredHost.exists_structured_host` constructs one set A with:

* prefix discrepancy at most one from a profile p in [0,1];
* convolution(p,p)/log tending to 1024;
* every reciprocal-integer-tolerance coefficient-1024 power cost summable;
* eventual bounds 448 log n <= r_A(n) <= 1600 log n;
* arbitrarily small boundary coefficients, with
  (j+1)|boundary(A,hostCutoff(j),n)| <= 20 log(n+1);
* central triple counts <= tripleCap(h) for every fixed comparability
  factor and polynomial horizon.

The selection machinery is generalized to arbitrary probability profiles.
A shifted profile dominated by 32 times the harmonic profile supplies the
needed mean bounds. Polynomial index budgets retain boundary and triple
constraints in the SAME host.

Main production dependencies added in this continuation:

* GeneralPatternCostsExplore.lean
* GeneralPatternPowerExplore.lean
* DominatedScaledProfileExplore.lean
* HostPatternMeanExplore.lean
* HostPatternSelectionExplore.lean
* StructuredHostExplore.lean

## Finite two-sided logarithmic reset

`CentralEndpointResetExplore.lean` first proves the signed bound

    |r_C(z)-r_B(z)| <= 2 |hits(A,E,z)|

whenever B,C are subsets of A and agree outside E. The factor is 2, not 4,
because both counts lie within the same interval above their common core.

The central reset restores host endpoints and then clips upper endpoints.
Subject to boundary/capacity inequalities it gives q-1 <= r_C(n) <= q,
while retaining C subset A and limiting edits to central host endpoints.

`Erdos66HostLogarithmicReset.exists_host_logarithmic_resets` combines this
with the host. For every fixed g there are fixed d>=2 and N0 such that,
from EVERY B subset A and at EVERY n>=N0, one can reset to C subset A with

    floor(log n)-1 <= r_C(n) <= floor(log n)

and

    |r_C(z)-r_B(z)| <= 2 tripleCap(g+1)

for z<=n^g, z!=n. No cumulative bound follows from this assertion alone.

## Exact cumulative footprint

`ResetScheduleFootprintExplore.lean` defines the limiting eventual-membership
set and the union of all future edit supports, truncated below a target z.
It proves

    |r_limit(z)-r_(B_s)(z)| <= 2 |hits(A,tailFootprint(E,s,z),z)|.

Each potentially changed endpoint is charged only once. The estimate does
not need coordinate stabilization. If supports escape every fixed integer,
then membership is eventually constant. Central supports n/d^2 do escape
for positive d.

No sublogarithmic bound for these future footprints has been obtained.

## NEW: the canonical exhaustive schedule actually recovers the host

The restore-then-upper-delete recipe has an additional one-sided property:
for 2a<=n,

    a in C <-> a in B or a in endpoints(A,n/d^2,n).

`OneSidedResetExplore.lean` checks this along with the previous reset outputs.
At n=2a, every a in A is a central diagonal endpoint, and cannot be deleted
because the deletion set lies STRICTLY above n/2. Every subsequent reset
also preserves a, because 2a<=n thereafter.

Therefore, for ANY sequence using this recipe at every n>=N0,

    a in limitSet(B) <-> a in A       whenever N0<=2a.

`ResetAbsorptionExplore.lean` proves this and the uniform estimate

    |r_limit(z)-r_A(z)| <= 2 N0.

For the high-coefficient host, the limiting set cannot have coefficient 1.
This is an actual obstruction to the canonical exhaustive schedule, not
merely the absence of a collateral estimate.

## Checked counterexample to the moving-target diagonal inference

`Erdos66ResetScheduleCounterexample.exists_convergent_reset_schedule_with_wrong_limit`
constructs a genuine sequence B_n of subsets of one host such that:

* every sufficiently late step satisfies the logarithmic reset condition;
* B_n converges coordinatewise (indeed every coordinate is eventually fixed);
* r_(B_(n+1))(n)/log n tends to 1;
* the limiting set agrees with the host outside a finite prefix;
* r_limit(n)/log n does NOT tend to 1.

Thus coordinatewise convergence plus accuracy at the moving target is not
a valid argument for the conjecture. The fixed-coordinate representation
limits cannot be interchanged with the growing target without a new uniform
estimate. Choosing different deletion orientations is not ruled out, but
no successful such schedule has been constructed.

## Builds and axiom audits

All new production files compile and have oleans. `StructuredHostAudit.lean`
and `ResetScheduleAudit.lean` report only propext, Classical.choice, and
Quot.sound for their principal declarations. No production sorry was added.
`ResetChecks.lean` is only a name-search scratch file and has an intentionally
failed check; it is not a production dependency.

## Remaining global problem

A new simultaneous feasibility or compatibility principle is still needed.
The latest local host construction does not provide it, and the most direct
exhaustive implementation has now been checked to fail. This does not rule
out another choice of host or reset, finite-template scale compatibility,
or the original existential conjecture.
