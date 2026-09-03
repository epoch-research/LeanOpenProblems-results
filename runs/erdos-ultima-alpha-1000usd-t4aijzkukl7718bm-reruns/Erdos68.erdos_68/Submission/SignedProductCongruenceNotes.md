# Signed product congruences (verified auxiliary work)

This does not settle Erdős 68. Spec.lean retains its original sorry, and no
complete proof or disproof has been submitted.

`SignedProductCongruence.lean` compiles without warnings. The principal axiom
audits list only propext, Classical.choice, and Quot.sound.

Let

    E_n = product_(k=2)^(n+1) (1-k!),
    S_n = sum_(k=2)^(n+1) 1/(k!-1),
    P_n = E_n S_n in Z,
    C_n = P_n+n E_n.

The exact recurrences are

    E_(n+1)-E_n = -(n+2)! E_n,
    C_(n+1)-C_n = -(n+2)! (P_n+(n+1)E_n).

Consequently, if B<=N+2 and n>=N, then modulo B!,

    E_n = E_N,
    C_n = C_N.

For arbitrary integers p,q, define T_n=p E_n-q P_n. The verified theorem
`cleared_affine_congruence` states

    T_n = T_N+q(n-N)E_N  (mod B!).

The theorem `cleared_eq_scaled_tail` checks that under q*x=p,

    T_n = q E_n (x-S_n).

These are arithmetic identities, not a rationality contradiction. The affine
congruence holds for every candidate p,q. For x equal to the target series,
its positive unscaled tail is small, but multiplying by the full product E_n
makes its magnitude large. No additional restriction excluding rationality
has been established.
