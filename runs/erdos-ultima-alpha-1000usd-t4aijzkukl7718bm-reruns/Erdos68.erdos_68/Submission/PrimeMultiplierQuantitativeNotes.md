# Uniform quantitative prime-row range

This is verified auxiliary arithmetic, NOT a proof or disproof of Erdős 68.
`Spec.lean` remains unchanged and retains its original `sorry`. No complete
solution or submission was obtained in this continuation.

## Verification

`PrimeMultiplierQuantitative.lean` compiles without warnings and has a built
olean. All five printed principal axiom audits list only `propext`,
`Classical.choice`, and `Quot.sound`. The file has no proof holes.

## Sharper numerator estimate

For the previously defined exact integer

    C(p,j) = p*(j*(p-1))!/(p!)^j,

with p prime and 0<j<=p, the new file proves

    C(p,j)*p^(j-1) = (j*(p-1))!/((p-1)!)^j,
    C(p,j) <= j^(j*(p-1)).

The quotient in the first identity is represented by the existing natural
`blockCoefficient`, whose exact factorial identity is already verified.

The word-count bound for this uniform multinomial is proved directly,
without trusting an external combinatorial calculation. Induction in k
bounds the next block of j consecutive factorial factors by
`(j*(k+1))^j`, giving

    (j*k)! <= j^(j*k)*(k!)^j.

This is stronger than the previous coarse exponential estimate in j^2.

## Explicit varying-multiplier range

The existing factorial-geometric-mean lower bound p/3 supplies

    3*a <= p  ==>  a^p <= p!.

For 0<j and 6*j^j<=p, this gives

    C(p,j) <= (j^j)^p,
    (2*j^j)^p <= p!,
    C(p,j) < p!-1,
    j < p.

Thus `row_formula_of_bound` proves, for prime p, positive even j, and
6*j^j<=p,

    fract((j*(p-1))!/(p!-1))
      = 1-1/p + (j*(p-1))!/[(p!)^j*(p!-1)].

`tail_gt_of_bound` proves the corresponding actual rowwise remainder bound

    T_(j*(p-1)) > 1-1/p.

Unlike the earlier eventual theorem for each fixed j, this condition is
explicit and uniform in both parameters; j may vary with p provided the
stated inequality is proved. No asymptotic claim about a particular growing
function j(p) is required by, or silently substituted into, these theorems.

Principal declarations:

* factorial_block_bound
* blockCoefficient_word_bound
* numerator_prime_power
* numerator_word_bound
* pow_le_factorial_of_three_mul_le
* multiplier_lt_prime
* numerator_small_of_bound
* row_formula_of_bound
* tail_gt_of_bound

## Unresolved arithmetic gap

Rationality of the original sum would make the actual rowwise remainders
positive integers eventually. The new lower bounds do not contradict that.
This file establishes neither simultaneous prime configurations nor an
infinite failure of integrality. In particular it is not an irrationality
proof, and nothing has been copied into the final conjecture file.

The preceding review also checked whether integer-valued binomial
normalization could improve the primitive pair of a polynomial form. That
scalar normalization was already covered by the earlier rising-product
work and does not change the primitive pair. No new useful aggregate gcd
bound or boundary-lattice nonvanishing estimate resulted from the review.

No numerical search was run. Compilation and axiom audits are complete;
no process or verification is pending.
