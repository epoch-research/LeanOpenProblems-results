# Signed terminal prime-input divisor tail — verified, no settlement

Spec.lean remains unchanged with the original sorry. The original
conjecture is still unresolved; no irrational counterexample has been
found and no incomplete proof has been submitted.

New file: TerminalPrimeDivisorTail.lean.
Namespace: Erdos972TerminalPrimeDivisorTail.
All four principal declarations compile and audit using only propext,
Classical.choice and Quot.sound.

## Exact terminal identity

For n<=2D, every divisor d of n with d>D equals n. Consequently, for EVERY
real t (not just positive t),

    expTail(t,D,n) = 1_{n>D} mu(n) exp(-t log n).

The zero and unit conventions are handled by the actual divisor definitions.

For alpha>=1 and floor(alpha*N)<=2D, summing with the actual prime weights
therefore gives

    primeExpSum(t,alpha,N)-primeTruncatedExpSum(t,alpha,D,N)
      = sum_{p<=N} primeWeight(p) 1_{floor(alpha*p)>D}
          mu(floor(alpha*p)) exp(-t log(floor(alpha*p))).

`terminalMoebiusPrimeSum` denotes exactly the expression on the right.
For t>0 this also gives

    t*mixedPrimeSmooth = primeTruncatedExpSum + terminalMoebiusPrimeSum.

No estimate of its sign is asserted.

## Improved absolute bound, only in this terminal range

For t>=0, the actual signed sum satisfies

    |terminalMoebiusPrimeSum| <= D^(-t) theta(N).

This follows directly from |mu|<=1, monotonicity of the damping, and the
exact total prime weight theta(N). It has no divisor-cardinality or extra
logarithmic loss. A comparison for the smooth Mangoldt sum still divides
this bound by t.

## Remaining distinction

The signed scalar cancellation theorem for sum mu(d)/d does NOT apply to
mu(floor(alpha*p)) with a prime-input weight. The new identity makes that
distinction explicit. Moreover the terminal cutoff D is of order N,
not within the already controlled small-divisor row range root64(u).
No sufficient estimate for the middle divisor range, nor the signed
terminal prime-input correlation, has been established.

This is a finite exact reduction and a valid absolute upper bound, not
a settlement of Erdos 972.
