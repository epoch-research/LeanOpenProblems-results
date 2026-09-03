# Fixed logarithmic-cap maximality does not force convergence

## Original task status

Erdős 66 remains unproved and undisproved. Submission/Spec.lean is unchanged
with its original import, statement, and sorry. No proof/disproof was
submitted. The result below disproves a proposed sufficient condition,
not the original existential conjecture.

## Verified production files

* PointwiseCapBlockingExplore.lean
* MaximalCapWithHolesExplore.lean
* LogarithmicMaximalCapExplore.lean

All three compile and have current oleans. MaximalLogCapAudit.lean audits
22 lemmas/theorems. MaximalLogCapAudit.log uses only propext,
Classical.choice, and Quot.sound. No production placeholders or new axioms
were introduced. LogMaximalChecks.lean and LogMaximalChecks2.lean are
name-search scratch files with intentional failed checks.

## Main logarithmic theorem

For every c>0, define the fixed natural-valued cap

    q_c(n) = floor(c log(n+2)) + 10.

The checked theorem

    Erdos66LogarithmicMaximalCap.exists_maximal_log_cap_without_limit

constructs one A such that:

* r_A(n)<=q_c(n) at EVERY n;
* for EVERY B containing A, if r_B(n)<=q_c(n) at every n, then B=A;
* there are arbitrarily large n with r_A(n)=0;
* there are arbitrarily large n with q_c(n)<=r_A(n)+1;
* r_A(n)/log n does not tend to ANY finite real number.

Maximality is in the FULL fixed-cap class, not just within the constructed
chain or a subclass required to retain the holes. The cap has the checked
asymptotic q_c(n)/log n -> c. This is stronger than the old observation that
the asymptotic-upper-bound class has no inclusion-maximal members.

## General cap theorem

The construction works for any q:Nat->Nat with

    q(n) -> infinity,
    q(n)^4 < n/12 eventually.

Monotonicity of q is not needed. The general output has the same maximality,
arbitrarily late holes, and arbitrarily late counts within one of the cap.
The logarithmic no-limit conclusion additionally uses q(n)/log n -> c>0.

## Finite blocking mechanism

Let C be a finite capped set below L, and let x not belong to C. Choose N
very large relative to L,x and the old cardinality. Set m=floor(q(N)/2).
The subquartic condition permits a Sidon set E of size m in

    [floor(N/3), floor(N/3)+floor(N/12)).

Its symmetric packet P=E union (N-E) has exactly 2m representations of N
and at most six of any other target. Add also the anchor a=N-x. All new
points lie at or above N/4. The anchor is outside C union P; its partner
at N would be x, which is absent. Therefore

    r_B(N)=2m,
    q(N)-1 <= r_B(N) <= q(N),

for B=C union P union {a}. Inserting x afterwards creates two new ordered
representations of N, exceeding q(N). This is a permanent blocking
certificate for every capped superset of B.

Below N/4, all old representation counts are unchanged. At other targets
apart from N, the new count is at most 2|C|+8. Taking N large makes the cap
at least that bound everywhere from N/4 onward. In particular B remains
capped at EVERY target, not just within a finite testing horizon.

The target 2L lies below N/4 and has zero representations. The finite
extension retains all old membership below L and all of its blocking
certificates.

## Infinite construction

At stage k, block x=k if k is absent. If k is already present, block the
current cutoff instead (which is necessarily absent). Thus every stage
also creates a new near-cap peak and a frozen hole.

The cutoff grows strictly, membership below it stabilizes, and the final
set agrees with each finite state on its frozen prefix. All upper bounds,
holes, and near-cap peaks pass to the limit by exact finite locality of
sumRep. For each natural k, it is either in the final set or has a finite
blocking certificate contained in that set. This proves full maximality.

Holes force any putative finite normalized limit to be zero; the near-cap
peaks and q(n)/log n -> c>0 exclude zero. No interchange of a moving-target
limit with coordinatewise convergence is used: both the hole and the peak
are frozen before the next stage.

## Remaining main problem

This does not show that every maximal capped set is bad, and does not
exclude non-maximal witnesses. It shows that maximality under a sharp
logarithmic cap alone cannot supply the missing all-target lower limit.
A stronger optimization principle, compatible infinite construction, or
universal obstruction is still required to settle Spec.lean.

## Subsequent finite-exchange strengthening

See FiniteExchangeCapProgress.md. Arbitrarily remote blocking certificates
now give a bad capped set A such that every capped B with A minus B finite
is a subset of A. Thus no finite deletion-and-insertion exchange can add a
new point or repair a hole. This is not a claim of finite-prefix cardinality
optimality and still does not settle the original conjecture.
