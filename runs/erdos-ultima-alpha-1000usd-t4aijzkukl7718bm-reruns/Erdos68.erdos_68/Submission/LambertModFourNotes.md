# Original Lambert coefficients modulo four

This is verified auxiliary arithmetic, NOT a settlement of Erdős 68.
Spec.lean is unchanged with its original sorry. No proof or disproof of
that conjecture has been submitted in this continuation.

LambertModFour.lean compiles without warnings and has a current olean.
Its five printed principal axiom audits contain only propext,
Classical.choice, and Quot.sound. There are no proof holes in this file.

## Residues by odd part

Let a_n be the ORIGINAL Lambert coefficients. The file proves:

* If m>=5 is odd, a_(2^r*m) == 1 modulo 4 for every r>=0.
* a_(2^(r+2)) == 3 modulo 4 for every r>=0.
* a_(3*2^(r+1)) == 3 modulo 4 for every r>=0.

The small original indices a_2=a_3=1 are outside the latter two formulas.
The new declarations are parameterized by r and the odd part m; they do
not require a separate uniqueness theorem for the odd-part decomposition.

Main declarations:

* coeff_mod_four_of_odd_part
* coeff_power_two_mod_four
* coeff_three_times_power_two_mod_four

## Elementary proof

Write U(d,k)=(dk)!/(d!)^k. The previously proved k! divisibility makes every
term with k>=4 vanish modulo four. Thus only block counts 1,2,3 remain.

The two-block term is the central binomial coefficient. For odd d>=3,

    d*C(2d,d)=2*(2d-1)*C(2d-2,d-1)

is divisible by four, because the smaller central binomial coefficient is
even. Since d is odd, C(2d,d) is itself divisible by four. The existing
prime-power lifting theorem also gives

    U(2d,2) == U(d,2) modulo four.

The three-block term is a multiple of the two-block term at the same block
size. These facts give residue one at m and 2m for every odd m>=5.
The already verified Dold relation a_(4m)==a_(2m) modulo four propagates
this to all powers of two. It likewise propagates the explicit base
residues a_4=7 and a_6=111 along the two exceptional families.

No experimental conjecture about binomial valuations is used in the proof.

## Consequence for the actual carry

Let h_n denote the carry at original index n. In the existing Lean code it
is CongruencePreservingCarry.carry (n-3). At n=4m the new file verifies

    c_(4m) == a_(4m)+h_(4m) modulo four.

The preceding carry term 4m*h_(4m-1) vanishes modulo four.
Combining this with the earlier rational necessary pattern gives exactly:

    alpha=q rational, m>=q.den+6, m odd
        ==> h_(4m) == 2 modulo four.

This is rational_carry_mod_four. The conditional theorem
irrational_of_frequent_carry_residue_failure states that arbitrarily late
failures of this single residue condition would prove irrationality.

THAT INFINITE-OCCURRENCE HYPOTHESIS IS NOT PROVED.
The sparse exceptional pattern for the original coefficients does not
control the real floors defining the carry. No congruence is transferred
without its explicit carry defect, and no equidistribution assertion is
made. There is no complete original-conjecture proof awaiting formalization.

No new numerical experiment was run in this continuation. All compilation
and axiom checks have completed; nothing remains pending.
