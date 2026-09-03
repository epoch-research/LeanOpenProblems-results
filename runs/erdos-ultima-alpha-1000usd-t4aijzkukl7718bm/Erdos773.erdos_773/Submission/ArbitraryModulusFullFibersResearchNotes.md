# Arbitrary-modulus full fibers: verified extension

This is NOT a settlement of Erdős 773. Spec.lean is unchanged and still has
its sole sorry in the range 0 < epsilon <= 1/3. No proof was submitted.

## Uniform short-interval units

UnitIntervalDensity.lean imports only FormalConjecturesUtil. It proves:

* q <= tau(q)*phi(q), for q>0;
* the Mobius coprimality indicator and totient ratio identities;
* the coprime count in {a+1,...,b} differs from (b-a)*phi(q)/q by at most tau(q);
* if L>=2*tau(q)^2, there is U subset [L,2L] of units modulo q such that

      L <= 2*tau(q)*|U|.

The discrepancy proof uses exact finite inclusion-exclusion and the fact
that the difference between two floor errors has absolute value at most one.
No asymptotic sieve or extra arithmetic hypothesis is used.

## Full-fiber capacity for every positive modulus

ArbitraryModulusFullFibers.lean extends ShiftedFullFiberCapacity. For a whole
Sidon square-value union of canonical fibers with arbitrary starts and common
index length H, all endpoints at most N:

    |R|*H^2 <= 2400*tau(q)^2*N.

For H<40*tau(q)^2 use |R|<=q and qH<=N. Otherwise take L=floor(H/10), use the
unit-gap lemma, and apply the existing location-aware scaled key capacity.

Truncation gives the same weak-square upper length tails for unequal full
fibers. FiniteTailCapacity then gives, writing M for the entire union size:

    M^2 <= 38400*tau(q)^2*N*|R|.

Assuming q<=N and modular square-pair matching of R, one also has
Mq<=2N|R| and |R|^2<=2q. Multiplication proves:

    M^3 <= 153600*tau(q)^2*N^2.

The existing uniform divisor subpower bound yields eventual_power_bound:
for every epsilon>0, eventually at each N, UNIFORMLY over all positive q<=N
and all qualifying starts/lengths/labels,

    M <= N^(2/3+epsilon).

All four main audits are clean. The two short-interval audits are clean.
Only propext, Classical.choice, Quot.sound occur. Both modules have oleans.

Logs:
    /tmp/unit-fourth.log
    /tmp/arbitrary-full-third.log

## Scope

Prime-power and unit-label restrictions are now absent. The following
restrictions remain and have NOT been removed:

* the union contains EVERY index of each prescribed full fiber;
* its entire square-value set is Sidon;
* the canonical labels have square-pair matching modulo q for the final cubic bound;
* q<=N (important when all lengths are zero).

The theorem does not bound an arbitrary Sidon subset of a nonsidon full-fiber
union. In particular the translated-intersection and adjacent-quadratic
reductions still produce sparse sets outside its hypotheses. It supplies no
near-linear partial selector and no upper bound disproving the conjecture.

Independent final checks:
    /tmp/unit-interval-final.log
    /tmp/arbitrary-modulus-final.log
    /tmp/spec-arbitrary-modulus-check.log

The main-file hash remains
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.

A subsequent review of sparse selection did not produce a valid exponent
improvement. In particular, sparse translated root cubes do not contain the
full collision endpoints used here; bounded difference multiplicity does not
supply a proved subpower-loss rounding; and formal Gaussian polynomial
Sidonness still lacks a carry-safe near-linear integer specialization.
