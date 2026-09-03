# Finite-exchange rigidity is insufficient under a logarithmic cap

## Original task status

The conjecture in Submission/Spec.lean remains unproved and undisproved.
Its statement, import, and original sorry are unchanged. No proof was
submitted. The construction below excludes a proposed sufficient condition,
not existence of an arbitrary logarithmic-limit witness.

## Verified production files

* TailCapBlockingExplore.lean
* FiniteExchangeCapExplore.lean
* LogarithmicFiniteExchangeExplore.lean

All compile with current oleans. There are no placeholders or new axioms.

## Stronger infinite counterexample

For every c>0, write

    q_c(n) = floor(c log(n+2))+10.

`Erdos66LogarithmicFiniteExchange.exists_finitely_rigid_log_cap_without_limit`
constructs one A such that:

* r_A(n)<=q_c(n) at every target;
* for EVERY capped B, if A minus B is finite, then B is a subset of A;
* arbitrarily large targets have r_A(n)=0;
* arbitrarily large targets satisfy q_c(n)<=r_A(n)+1;
* r_A(n)/log n has no finite real limit.

The second assertion is substantially stronger than inclusion-maximality.
It allows an arbitrary finite deletion set and does not even require the
competitor's proposed insertion set to be finite. No previously omitted
point can be inserted into any capped competitor after only finitely many
old points are removed.

In particular, `exists_all_finite_exchanges_blocked` gives a bad capped A
for which, for every pair of finite sets D,F,

    capped((A minus D) union F)  =>  F is a subset of A.

All such competitors are subsets of A, so none can increase a representation
count or repair an existing hole. This is stronger than optimality for any
fixed bound on the size of a finite exchange.

## Tail-supported certificates

`Erdos66TailCapBlocking.exists_tail_blocking_extension` strengthens the old
finite extension without changing its original theorem. The same symmetric
Sidon packet and anchor construction supplies a finite certificate F with

    F subset B,
    every member of F is at least the old cutoff L,
    inserting the omitted x into F alone violates the cap.

The certificate does NOT rely on old core points. Its self-count at the
selected center N is exactly 2 floor(q(N)/2); the anchor N-x is present,
and inserting x adds two ordered representations. Off-center and old-prefix
cap estimates are the same as in the previous finite blocking construction.

## Infinite scheduling and stabilization

Use schedule(j)=(Nat.unpair j).1. Every natural x is scheduled arbitrarily
late: j=Nat.pair x K is at least K and schedules x.

At each step, if the scheduled point is absent, block it with a new tail
certificate. If it is already present, block the current absent cutoff to
keep creating a new hole and near-cap peak. All old membership is retained,
and membership below the previous cutoff stabilizes exactly as before.

For the final set A, every omitted x therefore has a finite blocking
certificate above EVERY cutoff K. The theorem is

    Erdos66FiniteExchangeCap.rigidSet_tail_certificate.

If a capped competitor B deletes only finitely many A-points, choose K
above all deletions. A certificate for any proposed x in B minus A above K
is entirely contained in B, contradicting its cap. This proves

    rigidSet_finite_deletion_rigidity.

The finite-locality arguments also transfer the frozen holes and peaks.
No moving-target limit exchange is used.

## Scope of the optimization test

This rules out sufficiency of finite-exchange stability in the INFINITE
fixed-cap class. It does NOT assert that the constructed finite prefixes
maximize cardinality among all finite capped sets at their cutoffs. Remote
blocking constraints cannot silently be discarded in such a claim.

It also does NOT exclude a global optimization principle that coordinates
infinitely many deletions, a carefully selected chain of finite cardinality
maximizers, or another construction. No such principle was completed here.
The main uniform construction/compatibility gap remains unresolved.

## Verification

FiniteExchangeCapAudit.lean audits all 21 lemma/theorem declarations in the
three production files. Its saved log lists only propext, Classical.choice,
and Quot.sound. FiniteExchangeChecks.lean is a name-search scratch file with
failed checks and is not a production dependency.
