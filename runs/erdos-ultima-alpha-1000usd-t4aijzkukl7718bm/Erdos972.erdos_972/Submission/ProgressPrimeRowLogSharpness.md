# Actual prime-row logarithmic sharpness — no settlement

The original conjecture is unresolved. Spec.lean is unchanged with its
original sorry. No prime-pair lower bound or irrational counterexample
has been obtained.

New file: PrimeRowLogSharpness.lean.
Namespace: Erdos972PrimeRowLogSharpness.
All principal declarations compile and audit with only the permitted
axioms propext, Classical.choice and Quot.sound.

## Individual row sharpness

For alpha>=1 and a prime p>alpha, set N=p and d=floor(alpha*p). The proved
nonzero-determinant uniqueness gives EXACTLY

    row((0,p],primeWeight,floorMul alpha,d) = log p.

In particular d>=N and d>alpha. These full rows are unbounded as prime p
grows. Thus the existing bound M*log N cannot be replaced by C*M uniformly
throughout its full stated range: M=1 already gives a contradiction for
every fixed C.

## A terminal block lower bound

Define the actual centered energy

    terminalBlockEnergy(alpha,X)
      = sum_{floor(alpha*X)<d<=floor(alpha*2X)}
          [row((0,2X],primeWeight,floorMul alpha,d)-psi(2X)/d]^2.

For alpha>=1, X>0, log X>=28, the file proves

    (log X-28)*[theta(2X)-theta(X)] <= terminalBlockEnergy(alpha,X).

Proof: each prime X<p<=2X supplies its distinct full output divisor
floor(alpha*p). Its row is at least log p, its center is at most 14, and
its squared error is at least (log X-28)*log p. The output map is injective,
so these terms can all be retained in the energy. No off-diagonal prime
correlation or irrationality assumption is needed.

PNT on (X,2X] then proves

    terminalBlockEnergy(alpha,X)/(2X) -> infinity.

So an O(N) centered-energy bound UNIFORM across all large divisor blocks
is false, not merely absent from the current proofs. This does not assert
any contradiction with the earlier O(N log N) or larger upper budgets.

## Scope of the obstruction

The result concerns terminal blocks at divisors of size comparable to N.
It does NOT disprove a sharper averaged estimate in intermediate blocks
where N/d tends to infinity, and does NOT rule out an argument retaining
the actual Möbius signs rather than using the unsigned energy.

This is not a disproof of Erdos 972. It only rejects a proposed uniform
logarithm-free row/variance shortcut. The signed arithmetic remainder
needed for the original conjecture remains uncontrolled.
