# Unconditional square-congruence obstruction for the carried coefficients

This is auxiliary progress, not a settlement of Erdős 68. Spec.lean remains
unchanged with its original sorry. No proof or disproof has been submitted.

`CarriedSquareCongruenceBarrier.lean` compiles without warnings, has a built
olean, and its printed principal axiom audit uses only propext,
Classical.choice, and Quot.sound.

For the exact carried coefficients c from CongruencePreservingCarry, the file
proves that for every natural p>=7 with 2p-1 nonprime,

    p^2 does not divide c_(2p)-3.

Neither primality of p nor rationality of the target sum is required.

The coefficient recurrence and the positive scaled tails give, whenever
n>=5 and n-1 is nonprime,

    0<c_n<n(n-1).

Also n-1 divides c_n-1. At n=2p, suppose c_(2p)=3+p^2*k. The bounds force
0<=k<=3. Multiplying the predecessor congruence by four, and using
4p^2=(2p-1)(2p+1)+1, gives

    2p-1 divides k+8.

But 8<=k+8<=11<2p-1, a contradiction.

This rules out transferring a congruence modulo p^2 into this particular
small-tail carry representation at those indices. It does not resolve the
mod-p inheritance criterion: divisibility by p remains a strictly weaker
condition. No mod-p^2 congruence for the original Lambert coefficients is
asserted or used here. The irrationality conjecture remains unsettled.
