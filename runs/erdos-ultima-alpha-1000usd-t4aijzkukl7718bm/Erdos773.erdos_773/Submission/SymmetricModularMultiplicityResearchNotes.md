# Polynomial modular multiplicity in growing symmetric square-Sidon sets

The original conjecture remains UNSETTLED. Spec.lean was not edited and
retains its single admission. No new unrestricted Sidon exponent or fixed-
power upper bound was obtained.

## Verified module

Submission/SymmetricModularMultiplicity.lean imports the clean
SymmetricSquareAlteration module, not Spec.lean. It builds without warnings,
errors, or admissions and has an olean. All five printed audits use only
propext, Classical.choice, and Quot.sound.

Namespace: Erdos773.SymmetricModularMultiplicity
Log: /tmp/symmetric-modular-multiplicity.log

## Main quantitative result

For every epsilon>0, at every sufficiently large PRIME p there is a root
set C subset [1,p], symmetric under a |-> p-a, whose integer square values
are Sidon, with

    |C| >= p^(2/3-epsilon/4).

Let R be the SET of square residues {a^2 mod p : a in C}. There is a residue
r for which

    #{(x,y) in R x R : x+y=r} >= p^(1/3-epsilon).

These count ordered pairs of RESIDUE VALUES, not root lifts; the multiplicity
is therefore not explained by merely having both a and p-a in C. Swapping
summands can contribute a factor at most two. Diagonal pairs are included.

APIs:

* eventual_prime_multiplicity: the above eventual statement;
* unbounded_prime_multiplicity: explicit prime witnesses above every given M;
* eventual_prime_nonsidon: for 0<epsilon<1/3, the growing multiplicity proves
  that R is not modular Sidon, while all preceding properties and the
  cardinality lower bound are retained.

## Finite estimates

For any prime p and C with every root below p:

    |C| <= 2 |R|,
    exists r, |R|^2 <= p * #{(x,y) in R x R : x+y=r}.

The first is two-to-one squaring in a field, after injectively casting the
root interval into ZMod p. The second counts all ordered pairs by their sum
and chooses a largest fiber. Consequently finite_modular_multiplicity gives

    |C|^2 <= 4p * #{(x,y) in R x R : x+y=r}.

For a positive symmetric root set C subset [1,p], every root is strictly
below p: including p would force the forbidden root zero. Thus the finite
bound applies to SymmetricSquareAlteration's actual witnesses.

Squaring the cardinality lower bound and using p^(epsilon/2)>=4 absorbs
the factor four. The exact exponent identity is

    (p^(2/3-epsilon/4))^2
      = p^(epsilon/2) * p * p^(1/3-epsilon).

The generic lemma sidon_ordered_capacity proves that every modular Sidon
set has at most two ordered representations of any sum. For epsilon<1/3,
the new lower bound eventually exceeds two.

## Scope

This strengthens the earlier six-root modular-matching counterexamples to
growing root sets, with an explicitly polynomial modular multiplicity.
Thus symmetry and integer square-Sidonness cannot imply uniformly bounded
or subpower modular sum multiplicity at the reflection prime.

It does NOT rule out all quantitative symmetric upper bounds with exponent
strictly between two thirds and one. It does not construct near-linear
Sidon roots, and does not negate the original conjecture. The conditional
symmetric power-upper transfer still has its unproved upper-bound hypothesis.

Spec.lean remains at SHA-256
f019ff3791c89bbea24fd9b031eb92f7b676baa4b1ff9cebe9f2356121aa6ff0,
with its sole sorry at line 2035. No incomplete proof was submitted.
