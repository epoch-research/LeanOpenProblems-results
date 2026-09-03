# Higher-order smoothing coefficient tradeoff — no settlement

`Submission/Spec.lean` is unchanged and retains its original `sorry`.
No signed prime-pair lower bound or irrational counterexample was found.
No incomplete proof was submitted.

## Question investigated

Could a larger finite collection of damping parameters give a stronger
prime-detecting weight while retaining the small absolute divisor-tail
cost obtained from stronger damping?

The following finite tradeoff was verified. It restricts this particular
construction and cost; it is not an impossibility theorem for signed-tail
methods or for the conjecture.

## New verified file

`Submission/HigherSmoothingTradeoff.lean`
Namespace: `Erdos972HigherSmoothingTradeoff`.

Write

    E_s(n)=sum_{d|n} mu(d)*exp(-s*log d),
    damping(t,D)=exp(-t*log D).

For actual primes p<q and r>=p*q, the file proves

    0 <= E_s(r)-E_s(p*q) <= 2*exp(-s*log p)   (s>=0).

This is an actual prime-versus-semiprime comparison. The factors p,q are
distinct, so p*q is not mistakenly treated as a proper prime power.

Let I be ANY finite index set, let s_i>=t>=0, and put

    H(n)=sum_{i in I} a_i*E_{s_i}(n).

For 0<D<=p, `linear_combination_contrast` proves

    |H(r)-H(p*q)| <= 2*damping(t,D)*sum_{i in I}|a_i|.

Thus `detection_forces_coefficient_cost` proves that

    H(r)>=eta and H(p*q)<=0

imply

    eta/2 <= damping(t,D)*sum_{i in I}|a_i|.

The number of parameters, their values, and their signed coefficients
are arbitrary finite data. They may depend on a proposed finite scale.
Increasing the number of parameters does not remove this inequality.

## Exact scope

This is a lower bound on a COEFFICIENT-TIMES-DAMPING COST. It is NOT a
lower bound on an actual signed divisor tail or on its correlation. It
also does not assert that these test integers occur in a particular
prescribed floor relation or below an independently chosen cutoff.

The comparison shows why stronger damping alone cannot make this cost
vanish while preserving a fixed detection contrast on these integers.
It leaves open a proof using signed cancellation or some other estimate.
No sufficient signed estimate was obtained in this continuation.

## Verification

All three printed principal declarations compile and audit with only
`propext`, `Classical.choice`, and `Quot.sound`. The new file contains no
`sorry`. The original conjecture and its sole import were not changed.
