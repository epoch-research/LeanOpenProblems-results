# Prime-block congruences for the exact Lambert coefficients

This is verified auxiliary progress, not a settlement of Erdős 68.
`Submission/Spec.lean` remains unchanged with its original `sorry`.

`LambertPrimeBlocks.lean` compiles without warnings, has a built olean, and
its three printed principal axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`. No external numerical computation is
used as a proof premise.

## Uniform multinomial digit splitting

Write

    U(d,k)=(d*k)!/(d!)^k.

For every prime p, every a,b with 0<=b<p, and every k, the file verifies

    U(p*a+b,k) = U(a,k)*U(b,k) (mod p),   if b*k<p,
    U(p*a+b,k) = 0 (mod p),              if b*k>=p.

There is no assumption k<p or a<p. The proof inducts through the product
of binomial coefficients defining the uniform multinomial. Lucas's theorem
splits a no-carry step into its two digits. At the first carry in the low
digit, a binomial coefficient vanishes modulo p; subsequent products remain
zero modulo p.

## Full prime blocks

Let the original Lambert coefficient be

    a_n=sum_(d|n,d>=2) n!/(d!)^(n/d),

and include singleton blocks by setting F_n=a_n+n! for n>0. Reindexing by
the number of equal blocks gives

    F_n=sum_(k|n) U(n/k,k).

For a prime p, m>0, and 0<=r<p, the verified block formula is

    a_(p*m+r) = sum_(k|gcd(m,r)) U(m/k,k)*U(r/k,k)  (mod p).

The same formula holds with F_(p*m+r) on the left. Since p<=p*m+r,
the singleton factorial term is zero modulo p. The proof identifies the
no-carry block counts exactly with the common divisors of m and r.
There is no restriction m<p.

In particular, if gcd(m,r)=1, then

    a_(p*m+r)=1 (mod p).

At r=0 the right side is F_m=a_m+m!, recovering the earlier scaling
congruence with its essential singleton correction. At m=1 it recovers
the earlier first-prime-band congruence.

Principal declarations:

* uniform_digit_split
* fullCoeff_blocks
* block_summand
* fullCoeff_prime_block
* lambertCoeff_prime_block
* lambertCoeff_prime_block_coprime

## Limitations

These congruences concern the exact original coefficients. They are NOT
asserted for the rowwise-floor coefficients, the congruence-preserving
small-tail carry, or any other carried representation. No inheritance
statement, quantitative nonvanishing estimate, or new bound on the original
large tails has been proved. The coprime special case alone is also subject
to the previously verified rational comparison preserving all coefficient-
to-one congruences.

The explicit-orbit review did not prove that its fractional parts escape
the rationality-forced interval infinitely often. Synchronization of rational
initial conditions under factorial multiplication does not supply a useful
bound on when synchronization occurs relative to the small-error range.
No theorem excluding the target's infinite modified-Engel multiplier pattern
was obtained either.

No complete proof or disproof has been obtained or submitted.
