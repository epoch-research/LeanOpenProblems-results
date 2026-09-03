# Explicit finite logarithmic lower bound

This does NOT settle Erdős 773. The exact conjecture statement and sole import
in `Spec.lean` are unchanged. The main theorem still has one admission, for
0 < epsilon <= 1/3. The file has 2033 lines and its admission is at line 2031.

## New verified bounds

`AverageAPBound.lean` proves

    #squareAPs(N) <= 8*N*(1 + log(4*N)).

The proof normalizes the gap identity 2*y^2 = d*(2*a+d) using gcd(d,y).
Writing d=r*g, y=s*g, gcd(r,s)=1 gives r | 2*g. Set 2*g=r*k. Then

    4*a + k*r^2 = 2*k*s^2,
    4*b = k*(2*s^2 + 2*r*s + r^2),
    4*c = k*(2*s^2 + 4*r*s + r^2),
    k*max(r,s)^2 <= 4*N.

Covering the AP triples by these parameters and summing according to max(r,s)
gives 2*sum(r*(4*N/r^2)) <= 8*N*harmonic(4*N).

`FiniteLowerBound.lean` proves, for EVERY N >= 32,

    maxSidonSubsetCard(squaresBelow N)
      >= N / (8*(N*(1+log(4*N)))^(1/3)).

Both proofs are consolidated into `Spec.lean`, under names

    Erdos773.AverageAP.squareAPs_log_bound
    Erdos773.square_sidon_finite_log_lower

The lower bound uses L=1+log(4*N), R=(N*L)^(1/3), p=1/(4*R).
Since L<=4*N and N>=32, R<=N/2 and p*N>=1/2.
The AP deletion cost is at most 1/8, and the four-point deletion cost is at most
p*N/8. The remaining cardinality is therefore at least p*N/2=N/(8*R).

## Verification and limitations

`FiniteLowerAudit.lean` audits the new bounds and the previous asymptotic lower
and primorial upper bounds. All audited lemmas depend only on propext,
Classical.choice, and Quot.sound. The main theorem is NOT a completed proof.

Logs: /tmp/average-ap.log, /tmp/finite-lower.log,
/tmp/spec-finite-lower.log, /tmp/finite-lower-audit.log.

Backup before consolidation: `SpecLogEventualBackup.lean`.

This improvement makes the threshold explicit but does not improve the 2/3
exponent, and it does not establish even the epsilon=1/3 endpoint.
