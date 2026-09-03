# Global size-dependent minorant — conjecture still unresolved

`Submission/Spec.lean` is unchanged and still contains the original `sorry`.
This development does not prove or disprove the conjecture.

## New verified arithmetic comparison

`GlobalTwoScaleMinorant.lean`, namespace `Erdos972GlobalTwoScaleMinorant`.
Write S_t(n)=smoothMangoldt(t,n) and x_t(n)=exp(-t log(n)/2). Define

    D_t(n) = (1+x_t(n))^2 S_t(n)/2 - S_(2t)(n),
    L_t(n) = D_t(n)/x_t(n).

For every t>0, with NO restriction on t log(n), the file proves:

* For n>1 not a prime power, the doubling Euler product is at least
  (1+x_t(n))^2. The proof uses two distinct prime factors and AM-GM.
* D_t(n)<=0 off prime powers, including the zero and unit conventions.
* D_t(n)<=x_t(n) Lambda(n), hence L_t(n)<=Lambda(n) globally.
* For genuine primes p, D_t(p)=x_t(p) S_t(p) and L_t(p)=S_t(p).

All four printed principal declarations compile and audit with only
`propext`, `Classical.choice`, and `Quot.sound`.

## Actual mean check

`GlobalTwoScaleMean.lean`, namespace `Erdos972GlobalTwoScaleMean`.
For alpha>=1 irrational, and FIXED s,t>0, the actual signed sum satisfies

    (1/N) sum_{n<=N} S_s(n) D_t(floor(alpha*n))
      -> A(s) [A(t)/2-A(2t)],

where A(t)=dampedMean(t)/t. The n-dependent correction terms vanish in
Cesaro mean because x_t(n)->0 and the smooth weights are bounded at each
fixed positive parameter. This uses the actual mixed smooth mean theorem.

On the diagonal s=t, this scalar mean tends to -1/2 as t->0+. Consequently,
for every sufficiently small fixed t>0, the displayed signed sum is less
than -N/4 for all sufficiently large N.

This negative-mean theorem concerns D_t, NOT the undamped weight L_t.
It also uses a smooth source weight, NOT a genuine prime-input weight.
No uniform moving-parameter mean or prime-weighted lower bound is claimed.

The three principal mean declarations compile and audit with only the
three permitted axioms. No new file contains a sorry declaration.

## Remaining gap

Removing the pointwise validity window does not itself supply the needed
positive signed correlation. No sufficient lower bound for a prime-pair
minorant, no prescribed-slope prime-pair infinitude theorem, and no
irrational counterexample was obtained. No incomplete proof was submitted.

## Follow-up: every fixed positive parameter, including the undamped weight

Two further files now compile and pass their printed axiom audits:

* `DampedMeanMonotonic.lean` proves that dampedMean(t)>0 for t>0 and
  dampedMean(s)<dampedMean(t) whenever 0<s<t. The strict comparison is
  obtained from a quantitative Euler-factor gain on all even inputs,
  followed by the already proved ordinary means.
* `GlobalTwoScaleAllParameters.lean` proves the benchmark
  A(s)[A(t)/2-A(2t)] is strictly negative for ALL s,t>0, not just near zero.

The second file also handles the actual UNdamped lower weight L_t. It proves

    L_t(n) <= D_t(n) + min(S_t(n), Lambda(n)).

The overlap on the right has zero ordinary mean at each fixed t. Its sum
along floor(alpha*n) also has zero normalized mean, by injectivity of the
floor map and the existing nonnegative prefix bound. Consequently, for
alpha>=1 irrational and every FIXED s,t>0, there exists c>0 such that

    sum_{n<=N} S_s(n) L_t(floor(alpha*n)) < -c*N

for all sufficiently large N. This is an actual signed-sum upper bound,
not merely a formal negative scalar calculation.

This closes the possible fixed-positive-parameter escape for this particular
smooth-source/global-minorant construction. It does not address moving
parameters or a genuine prime source weight, and it is not a disproof of
the original conjecture. Spec.lean remains unchanged and unresolved.
