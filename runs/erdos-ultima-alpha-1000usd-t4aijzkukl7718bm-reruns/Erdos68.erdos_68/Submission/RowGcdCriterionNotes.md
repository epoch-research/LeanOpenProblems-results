# Row GCD criterion

`RowGcdCriterion.lean` is verified. It defines

    g(n) = gcd(F(n), n!),
    F(n) = sum_{k=2}^n floor(n!/(k!-1)).

For every rational q equal to the target sum, and every n,

    g(n) <= q.den * T(n),
    T(n) = n! * alpha - F(n) > 0.

Proof: the positive integer q.num*n! - q.den*F(n) equals
q.den*T(n), and is divisible by g(n). This works even before
q.den divides n!.

The already proved T(n)/n -> 0 then gives g(n)/n -> 0.
Consequently arbitrarily large n with g(n) >= n would prove
irrationality. No infinite occurrence result for those GCDs
has been proved. This file does not settle the conjecture.

Axiom audits for both main theorems list only propext,
Classical.choice, and Quot.sound.
