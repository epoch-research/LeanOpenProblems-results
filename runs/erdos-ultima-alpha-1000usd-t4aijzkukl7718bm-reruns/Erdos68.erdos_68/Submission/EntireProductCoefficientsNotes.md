# Factorial-scaled pole-product coefficients and prime congruences

Verified auxiliary work, NOT a settlement of Erdős 68. Spec.lean retains
its original sorry. The earlier submission failed verification; no complete
proof or disproof has been obtained.

EntireProductCoefficients.lean compiles without warnings and has a current
olean. All eight printed principal axiom audits contain only propext,
Classical.choice, and Quot.sound (some need fewer).

## Finite products and coefficient arithmetic

Let

    H_K(z)=product_(d=2)^(K+1) (1-z^d/d!),
    K_0(z)=0,
    K_(K+1)(z)=(1-z^(K+2)/(K+2)!)*K_K(z)
                  +z^(K+2)/(K+2)!*H_K(z).

The file defines integer sequences productCoeff(K,n) and markedCoeff(K,n)
and proves they are exactly n! times the z^n coefficients of H_K and K_K.
Multiplication by z^d/d! acts in exponential normalization as

    u_n -> choose(n,d)*u_(n-d),  d<=n,

and as zero when d>n. All integrality here is proved, not inferred from
floating-point computations.

The coefficients stabilize once K>=n; call the stabilized coefficients h_n
and k_n. The file also proves the exact finite evaluation identity

    K_K(1)=H_K(1)*sum_(d=2)^(K+1) 1/(d!-1).

No infinite-product convergence theorem or complex growth estimate is asserted
by this new file. The analytic interpretation remains in EntireProductNotes.md.

## Prime coefficients

For every prime p,

    h_p == -1 (mod p),
    k_p ==  1 (mod p).

Before the degree-p factor is inserted, every change to coefficient p has
factor choose(p,d), with 0<d<p, and is therefore divisible by p. Inserting
the degree-p factor subtracts the constant coefficient 1 from h_p and adds
it to k_p. Later factors cannot affect coefficient p.

## Division by 1-z

For arbitrary integers a,b define

    g_0=-a,
    g_(n+1)=(n+1)*g_n+b*k_(n+1)-a*h_(n+1).

The formal power-series identity, in exponential normalization, is verified:

    (1-z)*G(z)=b*K(z)-a*H(z).

This identity and the integrality of g_n hold for EVERY a,b, without any
rationality assumption on the original sum. At primes the file proves

    g_p == a+b (mod p).

In particular 0<a+b<p implies g_p!=0.

Principal declarations:

* product_coeff
* marked_coeff
* product_eq_prod
* stable_coefficients
* marked_eval_one
* at_prime
* quotient_identity
* quotient_prime
* quotient_prime_ne_zero

## Remaining gap

These prime congruences have not been combined with an applicable smallness
bound. If the original sum were a/b, endpoint cancellation would make G
entire in the analytic interpretation. An entire function of order two can
have nonzero integer factorial-scaled coefficients at arbitrarily large
primes. Their nonvanishing is therefore not itself a contradiction.

No original-conjecture proof is awaiting formalization. Spec.lean has not been
changed, and no new submission has been made. No computation is running.
