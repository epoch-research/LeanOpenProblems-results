# Signed complementary-divisor switching — verified, still no settlement

Spec.lean is unchanged with its original sorry. No proof of the conjecture,
no sufficient signed lower bound, and no irrational counterexample was
obtained in this continuation.

New file: SignedComplementaryDivisors.lean.
All principal declarations compile and audit with only propext,
Classical.choice, and Quot.sound.

## Exact identity

For n>0, D>0, n<=D*K, and ANY real coefficient function c,

    sum_{D<d<=2D, d|n} c(d)
      = sum_{0<k<=K, k|n, D*k<n<=2D*k} c(n/k).

The proof is the actual involutive divisor/cofactor bijection. It does
not replace signed coefficients by their absolute values.

The weighted mapped version is also proved. Taking g(p)=floor(alpha*p),
g(N)<=D*K, and c(d)=mu(d)*exp(-t*log d) gives, for every real t,

    sum_{D<d<=2D} c(d)*row((0,N],primeWeight,g,d)
      = sum_{0<k<=K} cofactorMoebiusPrimeBlock(t,alpha,D,k,N).

Here the summand on the right is EXACTLY

    sum_{p<=N} primeWeight(p)
      * 1_{k|g(p), D*k<g(p)<=2D*k}
      * mu(floor((alpha/k)*p))
      * exp(-t*log(floor((alpha/k)*p))).

The equality floor(alpha*p)/k = floor((alpha/k)*p) uses natural floor
division, including the zero convention; no reciprocal-floor/ceiling
substitution is made.

## Remaining gap

The switched coefficient is still evaluated at a genuine prime input.
Neither the scalar bound for sum mu(d)/d nor the small unweighted divisor
rows estimates this new signed correlation. In particular, having made
the cofactor k short does not make the Mobius argument short or independent
of p. No missing signed estimate is assumed in the file.

The earlier forward squarefree theorem still supplies absolute support,
not cancellation. This continuation does not provide a settlement and
no incomplete final proof was submitted.
