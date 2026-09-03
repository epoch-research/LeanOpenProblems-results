# Lean-checked finite interior covering — original conjecture unresolved

`Submission/Spec.lean` is unchanged and retains its original `sorry`.
No proof or irrational counterexample has been obtained, and no incomplete
proof was submitted for verification.

## New verified file

`Submission/FiniteInteriorCover.lean`
Namespace: `Erdos972FiniteInteriorCover`.

- `coverCertificate` is a finite rational interval-chain certificate. Each
  entry consists of genuine primes p,q with B<p<=M. It covers the current
  lower endpoint by [q/p,(q+1)/p), then advances to that right endpoint.
- `coverCertificate_sound` proves that such a certificate supplies a prime
  pair for every real slope in the certified closed interval. Rational
  slopes are included; no irrationality hypothesis is needed here.
- `interiorChain` contains 105 explicit pairs, selected using exact rational
  arithmetic. All input primes are greater than 100 and at most 433.
- `interiorChain_certificate` is checked by `decide +kernel`, not by native
  computation or an external oracle.
- `prime_pair_beyond_100` proves:

      6/5 <= alpha <= 9/5
        => exists p, 100<p and p<=433 and Prime p and Prime floor(alpha*p).

Compilation succeeded with:

    lake env lean -o .lake/build/lib/lean/Submission/FiniteInteriorCover.olean \
      Submission/FiniteInteriorCover.lean

Axiom audits for the soundness theorem, the certificate, and the resulting
prime-pair theorem list only `propext`, `Classical.choice`, and `Quot.sound`.

## Limitation

This is a finite certificate with fixed lower bound 100. No construction of
certificates for arbitrary lower bounds was proved. Scaling the slope does
not turn these fixed prime inputs into arbitrary larger prime inputs.
Consequently this result is not a proof of infinitude and does not settle
Erdos 972. It should not be substituted for the missing universal estimate.
