# Fixed-power amplification barrier

This is a verified auxiliary result, NOT a settlement of Erdős 773.
`Spec.lean` has not been changed and still has its admission for
0 < epsilon <= 1/3. No proof submission has been made.

## Statements

Let M(N) be the actual maximum Sidon-subset cardinality for the first N
positive squares, and f(N)=M(N)/N. In namespace `Erdos773.Amplification`,
`PowerAmplificationBarrier.lean` proves, for every fixed real theta<2:

    not exists c>0, eventually f(N^2) >= c*f(N)^theta.

Equivalently, it rules out the eventual cardinality amplification law

    M(N^2) >= c*N^(2-theta)*M(N)^theta.

For each c>0 and theta<2, strict failure occurs at arbitrarily large N.
The four main theorem names are:

* no_fixed_power_density_amplification
* frequently_small_power_density_gain
* no_fixed_power_cardinality_amplification
* frequently_small_power_cardinality_gain

Negative theta are included. The case 0<=theta<2 is proved first;
negative powers are then reduced to theta=0 using 0<f(N)<=1 for N>=1.
This extends the previously verified theta=1 obstruction.

## Proof

Fix B>=128 beyond the proposed recurrence threshold, and put

    g(m) = -log f(B^(2^m)).

The hypothetical gain implies g(m+1)<=theta*g(m)-log(c). For any
max(1,theta)<t<2, an elementary induction supplies D>0 such that

    g(m) <= D*t^m.

Write r=sqrt(3/4). Apply the existing primorial parametric bound with
n=2^m. If k is the number of sieve primes at that parameter, it gives

    f(B^(2^m)) <= 2*r^k,
    k*log(2^m) >= 2^m/8  (m>=7).

Since log(2)<=1, these imply the verified estimate

    (-log(r)/8)*2^m <= m*(g(m)+log(2)).

But m*(D*t^m+log(2))/2^m tends to zero for t<2, a contradiction.

## Verification and scope

The file imports the clean `AmplificationBarrier` and `PrimorialSquareSieve`
modules, not the admitted `Spec.lean`. It compiles with

    lake env lean -s 65536 Submission/PowerAmplificationBarrier.lean

All four printed axiom audits contain only propext, Classical.choice,
and Quot.sound. Log: `/tmp/power-amplification.log`.

This theorem is not the negation of the original conjecture. A near-linear
M(N) can have density loss whose logarithm is comparable to
log(N)/log(log(N)); such a loss is incompatible with these fixed-power,
constant-loss recurrences but compatible with N^(1-o(1)) growth.

The result does not rule out a suitably scale-dependent subpower loss,
nor a recurrence on selected scales only. No such positive amplification
construction has been obtained. Neither the lower exponent nor the
remaining range in the main theorem has improved in this continuation.
