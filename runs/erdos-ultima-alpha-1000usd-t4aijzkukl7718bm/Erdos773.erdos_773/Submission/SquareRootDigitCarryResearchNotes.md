# Ordered two-moment carry collisions at square-root digit height

## Main conjecture remains unresolved

This is NOT a settlement of Erdős 773. `Submission/Spec.lean` was not edited.
Its sole admission remains at line 2035. No unrestricted exponent above 2/3,
no fixed-power upper bound below one, and no complete proof or disproof were
obtained. No proof was submitted.

Main-file SHA-256:

    f019ff3791c89bbea24fd9b031eb92f7b676baa4b1ff9cebe9f2356121aa6ff0

## New complete module

`Submission/SquareRootDigitCarry.lean` has 300 lines and imports only
`FormalConjecturesUtil`. Its namespace is `Erdos773.SquareRootDigitCarry`.
It compiles without errors, warnings, admissions, or additional axioms.
The built olean is available. All twelve printed audits use only propext,
Classical.choice, and Quot.sound (some use fewer).

Log: `/tmp/sqrt-digit-carry-final.log`.

The temporary `SquareRootDigitCheck.lean` was deleted after consolidation.

## Exact family and verified conditions

For every natural t set

    u=t+1000000,
    B=36u^2-1,
    H=150000u.

There are four fixed-length, 71-digit words depending affinely on t. Each has:

* Constant digit exactly 6 and leading digit exactly 1.
* Positive, strictly increasing LOWER digits, all divisible by 6.
  The final leading 1 is deliberately excluded from the order assertion.
* All digits at most H and strictly below B.
* Total digit sum strictly below B.
* The same digit sum and squared-digit sum as each of the other three words.
* A positive evaluated root below B^71.

The four evaluated roots are pairwise distinct, but their squares satisfy

    root(t,0)^2 + root(t,1)^2 = root(t,2)^2 + root(t,3)^2.

`not_sidon` proves actual failure of Sidonness. It is not merely a formal
polynomial computation or an identification of duplicate evaluated roots.

The common digit sum is

    2500470t + 2543002994701,

and the common squared-digit sum is

    241614608508t^2 + 487749350751730200t
      + 246178670991665724758521.

## Square-root bound and arbitrary powers above one half

`digit_square_bound` proves, uniformly for every digit of every word,

    digit^2 <= 625000000*(B+1).

In fact H^2 equals the right side exactly. Thus the digit height is
O(sqrt(B)), with a fixed constant and fixed word length.

`eventual_power_bound` proves that for EVERY fixed real alpha>1/2,
eventually in t, all the digits are at most B^alpha. The proof uses the
proved real-rpow limit, not a numerical asymptotic approximation.

`power_bounded_obstruction alpha h_alpha L` packages an example with B>L,
all the endpoint, order, divisibility, canonical-digit, power-bound,
small-total-sum, common-moment, root-injectivity, root-height, positivity,
and non-Sidon conclusions. Its moment assertion includes orders zero,
one, and two.

This is a fixed-dimension obstruction at arbitrarily large radices, not
only a construction in which the dimension grows with the radix.

## Algebraic construction

Let m=35 and, in Z[X], put

    a(X) = sum_{i=0}^{34} (6+600i) X^i,
    d(X) = sum_{i=0}^{34} (1+100i) X^i,
    f(X) = 6 X^7 (1-X)^6,
    g(X) = X^14 (1-X)^6,
    U = 6(t+1000000).

For sigma,tau in {+1,-1}, use

    F(sigma,tau) = X^70
      + U*(a+sigma*f+d+tau*g)*X^35
      + (X+1)*(a*d+sigma*f*d+tau*a*g-sigma*tau*f*g).

The four words are the coefficient lists for signs
(+,+), (-,-), (+,-), (-,+), respectively. The exact discrepancy is

    F(+,+)^2+F(-,-)^2-F(+,-)^2-F(-,+)^2
      = 48 X^91 (1-X)^12 (36(t+1000000)^2-X-1).

`discrepancy` verifies the corresponding identity at an ARBITRARY integer
radix, and `square_collision` specializes it at B. The discrepancy is not
formally zero: its specialization factor is essential.

The sixth finite differences were chosen because convolution with the
linear background has two short windows with four vanishing moments.
These windows, and the product-perturbation window, are disjoint and lie
where the background product coefficients are cubic functions of position.
This explains the matching first two digit-value moments. The actual Lean
certificate checks all resulting affine coefficient data and proves the
identities by `ring`; the symbolic derivation is not an external oracle.

## Lean implementation

The file stores separate constant slope and offset vectors and defines

    digit(t,j,i) = slope(j,i)*t + offset(j,i).

Finite kernel-checked facts about these vectors give adjacent order,
bounds, divisibility, endpoints, and the five affine moment coefficients.
Generic arithmetic then proves all parameter-dependent properties. This
avoids hundreds of duplicated parameter-dependent finite-case proofs.

The root-injectivity proof reads digits 7 and 14. Their pairs are

    (5518896,49375380),
    (5518884,49375368),
    (5518896,49375368),
    (5518884,49375380),

which are distinct. Canonical radix injectivity transfers word injectivity
to the actual roots.

## Important limitations

* Every radix here is COMPOSITE:
  B=(6u-1)(6u+1), with both factors greater than one.
  Do not combine this square-root digit bound with the prime-base result
  from `OrderedEisensteinOneModSix`; that earlier family has a different
  digit-height bound.
* The moments concern powers of digit VALUES, not positional moments.
  No moment order above two is asserted here.
* No common complete histogram, full allowed alphabet, root primality,
  or pairwise coprimality is asserted.
* These examples refute a universal sufficient digit criterion. They do
  not show that every relevant class fails or exclude a large Sidon
  subclass. They do not disprove the original conjecture.

The original small-epsilon gap is unchanged. A reviewed positive binary
candidate also failed: odd roots with no adjacent 1-bits contain the
collision 37^2+133^2=17^2+137^2. Adding a common Hamming weight does not
repair that criterion in general; an exact exploratory check found
1169^2+4233^2=549^2+4357^2, all four odd roots having four 1-bits and no
adjacent 1-bits. These exploratory binary checks were not promoted to
additional Lean modules or to any claim about the unrestricted maximum.
