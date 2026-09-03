# Forward squarefree support and terminal tail — verified, not a settlement

The original conjecture in Spec.lean is STILL UNSOLVED. Its statement and
original sorry are unchanged. No irrational counterexample has been found.
No completed proof has been submitted in this continuation.

## New files

* MappedSquarefreeDivisorExpansion.lean
* ForwardSquarefreeSupport.lean
* ForwardSquarefreeTerminalTail.lean

All three compile. Their printed principal declarations depend only on
propext, Classical.choice, and Quot.sound.

## Mapped square-divisor expansion

For a finite input set S, an injective map g:S -> (0,M], and weights
0 <= a(n) <= L, the full squarefree-support mean is approximated by the
square-divisor truncation with retained error L*M/D. If the actual mapped
rows at d^2, 0<d<=D, differ from X/d^2 by at most E, then

    |sum_{n in S} a(n)|mu(g(n))| - X*c_D| <= L*M/D + D*E,
    c_D = sum_{0<d<=D} mu(d)/d^2.

This is an injective-map version of the earlier identity-argument theorem.
The cap M bounds OUTPUTS, not the input cutoff. No factor alpha is dropped.

## Actual forward prime-input mean

Set

    g(p) = floor(alpha*p),
    Q(alpha,X) = sum_{p<=X} primeWeight(p)*|mu(g(p))|,
    c = 6/pi^2,
    N=u^6, W=growingCutoff(u), v=root64(u).

Using the actual common direct prefix rows, the file proves

    |Q(alpha,X)-c*psi(X)| <= Budget(alpha,u)*N   for EVERY X<=N,

where

    Budget = 6*alpha*(1+log u)/W
             + W*primeRowError(u)/u^6
             + 7*|c_W-c|.

Every term tends to zero. W^2<=v ensures all square-divisor rows are
eligible; the proper-prime-power error is included in primeRowError.
The threshold for the entire budget is selected BEFORE the actual
common-scale existence theorem supplies u.

Consequently, for irrational alpha>1, epsilon>0 and any B, there is u>B,
u>0, such that simultaneously for every X<=u^6,

    |Q(alpha,X)-c*psi(X)| <= epsilon*u^6.

PNT then gives arbitrarily large actual scales with

    |Q(alpha,u^6)/u^6-c| < epsilon.

This is the FORWARD orientation: inputs are genuinely prime, outputs
squarefree. It is distinct from the older result with prime outputs and
squarefree inputs.

## Exact terminal support

Let K=min(N,outputPrefix(alpha,D)), with the already verified ceiling
formula for outputPrefix. The terminal support is exactly

    Q(alpha,N)-Q(alpha,K).

For every t>=0, the actual signed terminal sum obeys

    |terminalMoebiusPrimeSum(t,alpha,D,N)|
      <= damping(t,D)*[Q(alpha,N)-Q(alpha,K)].

At arbitrarily large actual common scales N=u^6, the new theorem gives
SIMULTANEOUSLY for every D and every t>=0:

    |terminalMoebiusPrimeSum(t,alpha,D,N)|
      <= damping(t,D)*[c*(psi(N)-psi(K))+epsilon*N].

Thus both the precise terminal interval and the squarefree Euler factor
are retained. No signed asymptotic or cancellation is claimed.

The file also proves that Q(alpha,N)/N does NOT tend to zero for any
irrational alpha>1. Thus simply taking absolute values cannot yield an
o(N) bound, even with genuine prime inputs. This does not preclude signed
cancellation.

## Remaining gap

The prime-detecting smooth comparison still divides the divisor tail by t.
A constant-factor absolute-support improvement does not supply the
needed signed estimate in a bounded t*log(N) window. The middle divisor
range remains uncontrolled at the required strength. The forward
squarefree mean is not a lower bound for genuine prime pairs, and it does
not establish the conjecture or its negation.
