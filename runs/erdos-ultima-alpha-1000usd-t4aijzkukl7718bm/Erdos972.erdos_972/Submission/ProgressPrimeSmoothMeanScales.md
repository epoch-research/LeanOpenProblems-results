# Fixed-parameter prime-input / smooth-output mean — verified

`PrimeSmoothMeanScales.lean` compiles. Its principal declarations audit with
only `propext`, `Classical.choice`, and `Quot.sound`.

For every irrational alpha>1, fixed t>0, epsilon>0 and B, there is u>B with

    |mixedPrimeSmooth(t,alpha,u^6)/u^6 - dampedMean(t)/t| < epsilon.

The scalar limit is strictly positive. In particular, arbitrarily large actual
common irrational good scales have mixed sum exceeding
`dampedMean(t)/(2*t) * u^6`. The input weight is genuinely prime-supported.
The output weight is not.

The normalized finite error budget is explicit:

    [root64(u)*primeRowError(u)/u^6
      +42*alpha*damping(t,root64(u))*(1+log u)^2]/t
      + |[psi(u^6)/u^6]*[divisorMean(root64(u),dampedCoefficient(t))/t]
          -dampedMean(t)/t|.

The threshold making this budget small is chosen BEFORE the common-scale
row theorem supplies u. There is no intersection of separately chosen good
scale sets.

This does not prove a prime-pair estimate in the moving prime-detection
window. When t*log N is bounded and D is a polynomial cutoff, exp(-t*log D)
does not tend to zero. No exchange of fixed-t and cutoff limits is valid here.
`Spec.lean` still has its original unresolved conjecture.
