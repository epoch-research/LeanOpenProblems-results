# Prime-factor descent — original conjecture unresolved

`Submission/Spec.lean` is unchanged and retains its original `sorry`. No proof
or irrational counterexample has been obtained. No incomplete proof was submitted.

New standalone file: `Submission/PrimeFactorDescent.lean`, importing only
`FormalConjecturesUtil`, namespace `Erdos972PrimeFactorDescent`.

Verified declarations:

- `prime_divisor_lt_of_nonprime`: if 0<n<2p, n is not prime, and r is a
  prime divisor of n, then r<p.
- `output_prime_factor_lt`: for 1<=alpha<2, if p is prime and floor(alpha*p)
  is not prime, every prime divisor of that output is smaller than p.
- `eventual_descending_factors`: applies this to an explicit eventual
  no-prime-pair hypothesis.

The file compiles. Both principal theorem axiom audits list only `propext`,
`Classical.choice`, and `Quot.sound`.

This restriction does not use irrationality. It gives decreasing prime-factor
chains beyond a hypothetical last prime pair, but no contradiction: chains can
terminate at finitely many small primes. No estimate showing that such finite-seed
factor decompositions cannot accommodate all large primes was proved. The
universal prime-pair infinitude assertion remains unresolved.
