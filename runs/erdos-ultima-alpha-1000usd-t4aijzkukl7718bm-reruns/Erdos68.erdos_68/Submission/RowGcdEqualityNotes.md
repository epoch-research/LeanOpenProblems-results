# Exact GCD correction under rationality

`RowGcdEquality.lean` compiles and has a built olean. Its four principal
axiom audits list only propext, Classical.choice, and Quot.sound.
This is auxiliary progress, not a settlement of Spec.lean.

Write alpha for the target sum and

    F_n = sum_{k=2}^n floor(n!/(k!-1)),
    T_n = n!*alpha - F_n,
    g_n = gcd(F_n,n!),
    Q_n = (F_n+g_n)/n!.

## Verified results

If alpha=a/b is rational, then eventually T_n is a positive integer,
and both b*T_n<=n and b*g_n<=n. The former follows from T_n/n->0,
and the latter from the previously verified g_n/n->0 under rationality.

Since b*T_n and b*g_n are positive integers at most n, both divide n!.
Thus T_n and g_n both divide n!/b. From

    T_n = a*(n!/b)-F_n

and g_n|F_n we get g_n|T_n. Conversely T_n divides both F_n and n!,
so T_n|g_n. Therefore

    g_n = T_n eventually, and Q_n = alpha eventually.

The file also proves unconditionally that g_n/n! -> 0. For this it uses
Dirichlet approximation to choose integers a,b with |b*alpha-a| small.
Whenever b*F_n-a*n! is nonzero, gcd divisibility gives

    g_n/n! <= |b*(F_n/n!)-a|.

That integer form is eventually nonzero: if b*alpha-a != 0, use convergence;
if it is zero, use the strict inequality F_n/n!<alpha and b>0.
Consequently Q_n -> alpha unconditionally.

Combining the two directions gives the new exact criterion

    Irrational alpha iff not exists q in Q, Q_n=q eventually.

## What is still missing

No proof that Q_n fails to stabilize has been obtained.
The main conjecture is unchanged and still contains its original sorry.

An external Python calculation using exact integer division and reduced
fractions found Q_(n+1) != Q_n for n=1,...,999. This finite calculation is
not a Lean theorem and establishes no infinite non-stabilization result.
