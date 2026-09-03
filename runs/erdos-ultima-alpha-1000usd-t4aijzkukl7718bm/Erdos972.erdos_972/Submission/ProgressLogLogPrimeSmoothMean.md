# Log-log moving prime-input / smooth-output mean — verified

The original conjecture is not settled. Spec.lean is unchanged and retains
its original sorry. No irrational counterexample has been proved.

New files:

* DampedMeanTailBound.lean
* LogLogPrimeSmoothMean.lean

Both compile, and principal declarations audit with only propext,
Classical.choice, and Quot.sound.

## Explicit scalar tail

For every t>0 and D>0,

    |divisorMean(D,dampedCoefficient(t))-dampedMean(t)| <= D^(-t)/t.

The proof compares the finite reciprocal-weight tail to an integral of
x^(-1-t), and then passes to the already verified absolutely convergent
series. There is no uniform-limit assumption.

## Explicit moving parameter

Set L(u)=1+log u and

    t(u)=520*log(1+L(u))/L(u).

The file proves t(u)>0, t(u)->0 from the right, 1/t(u)<=L(u), and, whenever
u>0 and L(u)>=130,

    damping(t(u),root64(u)) <= L(u)^(-4).

The latter uses the existing root64 logarithmic bound; no stronger divisor
level is substituted. Consequently,

    damping/t(u)^2 <= 1/L(u)^2,
    damping*L(u)^2/t(u) <= 1/L(u).

The logarithmically weighted actual prime row error also tends to zero:

    root64(u)*L(u)*primeRowError(u)/u^6 -> 0.

This includes all proper-prime-power errors, with the explicit sqrt bound.

## Main result on actual irrational scales

For alpha>1 irrational, epsilon>0, and any B, there is u>B, u>0, with

    |mixedPrimeSmooth(t(u),alpha,u^6)/u^6 - 1| < epsilon.

In particular the mixed sum exceeds u^6/2 at arbitrarily large scales.
The input weight is the genuine prime weight, not a smoothed source.
The threshold making the complete error budget small is selected BEFORE
invoking the actual common-scale prefix-row existence theorem.

The error budget used is

    [root64(u)*primeRowError(u)/u^6]/t(u)
      +42*alpha/L(u)
      +|[psi(u^6)/u^6]*[divisorMean(root64(u),dampedCoefficient(t(u)))/t(u)]-1|.

Every term tends to zero. Thus this is a genuine moving-parameter result,
not an exchange of fixed-parameter limits or a diagonal chosen without a
quantified range.

## Remaining gap, explicitly checked

The file also proves

    t(u)*log(u^6) -> infinity.

Thus the improvement from fixed positive t to order log(log N)/log N does
NOT reach a bounded t*log N prime-detection window. The output weight still
has substantial composite support. No comparison proved so far converts
this positive mean to a positive prime-pair count.

The semiprime-sign review preceding this construction yielded no new
sufficient signed four-factor lower bound. Favorable semiprime products do
not control all mixed-sign terms or the actual mean-product subtraction.
No claim to such a bound was inserted into any file.
