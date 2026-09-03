# Linear-tail congruence criterion (verified; not a settlement)

`CongruentTailSeparation.lean` and `ClosePrimePairs.lean` compile, and their
oleans have been built. The principal axiom audits list only `propext`,
`Classical.choice`, and `Quot.sound`. These files do not settle Erdős 68.

## A separation lemma for integer tails

`no_close_small_returns` proves the following. Suppose C,a,L are naturals,

    2 C < L,
    (C+1)L+C < a,

and t is integer-valued with

    0 <= t_(a+i) <= C(a+i),             0 <= i <= L,
    t_a <= C,  t_(a+L) <= C,
    a+i divides t_(a+i+1)-t_(a+i)+1,   0 <= i < L.

Then these hypotheses are contradictory.

Write k_n=(t_(n+1)-t_n+1)/n, an integer. The identity

    1/n + t_(n+1)/(n(n+1))
       = t_n/n - t_(n+1)/(n+1) + k_n

sums over a,...,a+L-1. If D denotes its positive left-hand sum and z=sum k_n,
then

    D = t_a/a - t_(a+L)/(a+L) + z,
    L/(a+L) <= D <= (C+1)L/a.

The endpoint bounds and the size condition put the integer z strictly
between -1 and 1, so z=0. Consequently L/(a+L)<=C/a. But L>2C and L<a
make this impossible.

## Prime pairs from the divergent prime harmonic series

`prime_predecessor_pairs` proves that for any C and any lower cutoff M
there are a>=M and L with the two displayed inequalities such that both
a+1 and a+L+1 are prime.

If not, let p_n be the nth prime and m=2C+1. The strict increase of p_n
makes p_(n+m)-p_n>2C. The forbidden-pair assumption then forces, eventually,

    p_(n+m) >= (1+1/(2(C+1))) p_n.

Each residue class of prime indices modulo m would have geometrically
summable reciprocals. Their finite union would make the prime reciprocal
series summable, contradicting the imported, verified divergence theorem.

## Irrationality criterion

`irrational_of_linear_tails_prime_coefficients` proves this sufficient
condition for a factorial series with integer coefficients c_n. Put

    x = sum_(n>=0) c_n/n!,
    T_n = n! (x-sum_(k=0)^n c_k/k!).

If, eventually,

    n divides c_(n+1)-1,
    0 <= T_n <= C n,
    c_p=1 for every sufficiently large prime p,

then x is irrational. Here C is any fixed natural number.

Under rationality, T_n is an integer eventually. Its recurrence gives the
required congruence for successive tails. At c_(n+1)=1, the upper bound on
T_(n+1) forces the integer T_n<=C. The prime-pair lemma and the separation
lemma then give a contradiction. The intermediate theorem
`irrational_of_linear_tails_and_unit_pairs` uses suitable pairs of unit
coefficients directly, without requiring them at every prime.

## Missing application to the conjecture

This relaxes the earlier strict bound 0<T_n<n-1 to any fixed linear bound,
at the cost of requiring prime unit coefficients. It still does not apply
to either verified representation of the target:

* The original Lambert coefficients satisfy the congruence and the prime
  unit condition, but their tails grow far beyond a fixed linear bound.
* The rowwise coefficients have sublinear tails, but their congruence and
  prime unit conditions have not been proved; the original Lambert facts
  cannot be transferred to those different coefficients.

No carrying construction preserving all the needed properties has been
obtained. `Submission/Spec.lean` remains unchanged with its original sorry.
No proof or disproof has been submitted.

## Further exact transfer check

`Submission/RowPrimeCoefficientCheck.lean` now verifies

    rowFloor 6 = 902,
    rowFloor 7 = 6317,
    rowCoeff 7 = 6317-7*902 = 3,
    lambertCoeff 7 = 1.

Since 7 is prime, ordinary rowwise carrying does not preserve the Lambert
prime unit identity either. Its axiom audit uses only the permitted axioms.
This is a finite failure, not a proof that an eventual prime unit identity
fails, and not an irrationality conclusion.

The attempted row-by-row replacement by finite factorial expansions has
not supplied a uniform small-tail estimate. Clearing each rational row at
a sufficiently late factorial can preserve integrality, but moves positive
mass to late indices; convergence of the unscaled series does not control
the factorial-scaled tails. No compatible representation satisfying all the
hypotheses of the new criterion has been constructed.
