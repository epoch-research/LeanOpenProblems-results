# Unit-residue refinement — still no settlement

Spec.lean is unchanged with the original sorry. No proof of the conjecture
or irrational counterexample has been found. No incomplete proof was
submitted.

New file: PrimeRowUnitInjection.lean.
Namespace: Erdos972PrimeRowUnitInjection.
All four principal declarations compile and audit with only propext,
Classical.choice, and Quot.sound.

## Verified refinement

Assume alpha>=1, d>alpha, M>0 and N<=d*M. The previous residue injection

    p -> (floor(alpha*p)/d) * p^(-1) in ZMod M

is restricted to prime inputs M<p<=N with d dividing the output.

If the cofactor floor(alpha*p)/d is coprime to M, the residue is a unit.
The injection then gives the bound phi(M), rather than M:

- `coprime_cofactor_row_card_le_totient`
- `coprime_output_row_card_le_totient`

The second theorem uses the stronger hypothesis that the whole output is
coprime to M. These are upper bounds. The modulus need not be prime.

Taking M=2 gives:

- `odd_output_row_card_le_one`: if N<=2d and d>alpha, at most one odd
  prime input up to N has an odd output divisible by d.
- `twice_common_odd_output_divisor_lt_max`: for distinct primes p,q>2
  with odd outputs, a common output divisor d>alpha satisfies

      2*d < max(p,q).

The exclusions p,q>2 and d>alpha are retained. No irrationality is used.

## Missing step

The refinement constrains shared divisors of composite outputs but provides
no positive lower bound for prime outputs at prime inputs. No sufficiently
small centered signed row-error estimate, nor the strict lower gap required
by the four-factor reduction, has been deduced. In particular, these bounds
do not contradict finiteness of the original prime-pair set.
