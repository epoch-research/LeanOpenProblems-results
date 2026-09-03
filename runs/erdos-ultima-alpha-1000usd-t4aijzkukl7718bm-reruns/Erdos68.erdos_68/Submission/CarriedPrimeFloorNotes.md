# Explicit floor formula for prime-successor carries

This is verified auxiliary work, NOT a proof or disproof of Erdős 68.
Spec.lean is unchanged and still contains its original sorry. No settlement
has been obtained or submitted.

CarriedPrimeFloor.lean compiles without warnings, has a built olean, and
contains no proof holes. Its printed principal axiom audits use only
propext, Classical.choice, and Quot.sound.

## Formula

Use the exact carried representation from CongruencePreservingCarry.lean.
In original indices, write

    X_n=n!*sum_(k=2)^n 1/(k!-1),
    P_n=L_n+h_n,
    T_n=n!*alpha-P_n.

For every prime p>=5 the file verifies

    P_(p+1)=2+p*floor((X_(p+1)-2)/p).

Thus this carried prefix does not require knowledge of all the earlier
carries. Its value is determined directly by the original rational partial
sum. The Lean index r corresponds to p=r+4.

The proof uses two facts already supplied by the construction:

* the coefficient-one recurrence at p and the predecessor congruence at
  p+1 imply p divides P_(p+1)-2;
* the rational residual satisfies 0<=X_(p+1)-P_(p+1)<p.

Writing P_(p+1)=2+p*k, these inequalities uniquely identify k as the floor.

## A coarser factorial-grid approximant

Define

    Q_p = p*(floor((X_(p+1)-2)/p)+1)/(p+1)!
        = (floor((X_(p+1)-2)/p)+1)/((p+1)*(p-1)!).

The verified error identity is

    (p+1)!*(Q_p-alpha)=p-2-T_(p+1).

The reduced denominator of Q_p divides (p+1)*(p-1)! and is therefore coprime
to p. Under a hypothetical rational value alpha=q with q.den<=p-1, the
previously verified reset T_(p+1)=p-2 gives Q_p=q exactly.

Main theorem names:

* scaledPrefix_prime_successor
* primeGridApprox_grid
* primeGridApprox_den_dvd
* primeGridApprox_den_coprime
* primeGridApprox_error
* rational_primeGridApprox

## Limitation

This identity exposes the prime-successor condition as an ordinary rational
floor/approximation problem. It does not exclude eventual constancy of Q_p.
Coprimality with the moving prime p is compatible with a fixed rational
value: every sufficiently large p is already coprime to its denominator.

No new infinite nonconstancy theorem or contradiction with rationality was
obtained. The original conjecture remains unproved and undisproved here.
