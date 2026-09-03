# Aligned-block collisions and overlapping-window capacity

## Main problem remains unsettled

This continuation did NOT settle Erdős 773. Spec.lean is unchanged, with its
sole admission at line 2031 for 0 < epsilon <= 1/3. No actual lower exponent
or upper exponent improved. No proof submission was made.

The strongest completed actual lower bound remains eventually
M(N) >= N^(2/3)/500. The upper bound remains compatible with N^(1-o(1)).

## Three new verified modules

* AlignedBlockCollision.lean
* PrimitiveAlignedBlockExample.lean
* SlidingWindowCapacity.lean

All compile without warnings or admissions, have built oleans, and their
22 printed main audits use only propext, Classical.choice, and Quot.sound.
None imports the admitted Spec theorem.

## 1. Exact aligned-block propagation

`AlignedBlockCollision.mix_collision` proves that from

    a^2+b^2=c^2+d^2

one obtains, for arbitrary natural u,v,

    (a*u+d*v)^2+(b*u+c*v)^2
      =(c*u+b*v)^2+(d*u+a*v)^2.

The cross term on each side is exactly 2*(a*d+b*c)*u*v.

For a base-block radix W, define

    repeatWeight(W,k) = W * sum_{i<k} W^i,
    repeatedValue(x,W,k,j) = x_j + x_(3-j)*repeatWeight(W,k).

Thus the initial block has the original orientation, and the next k blocks
have the reversed orientation. `repeatedWord_value` proves that the actual
digit evaluation equals this value, including the exponent L*b+r at each
position. There is no formal-to-numerical specialization assumption.

`block_histogram` preserves every block's histogram. `aligned_statistics`
proves equality for EVERY additive digit statistic on EVERY finite union
of aligned whole blocks. The codomain can be any additive commutative monoid.
In particular all aligned dyadic unions of blocks have matching statistics.
These theorems do not assert equality on windows cutting through blocks.

Since repeatWeight is divisible by W, the new roots retain their distinct
original residues modulo W. `repeated_injective` and `repeated_not_sidon`
verify that the evaluated collisions remain genuinely nontrivial.

## 2. Pairwise coprimality can also be preserved

This resolves the coprimality gap in the preceding unformalized repetition
idea, for this specific mixed-orientation construction.

For a finite family x_i>1, pairwise coprime, and a fixed-point-free map r,
consider the affine forms

    x_i + v*x_(r(i)).

Their nonzero determinants are

    Delta_ij = x_i*x_(r(j)) - x_j*x_(r(i)).

`minor_ne_zero` proves nonvanishing using pairwise coprimality. Let S be the
finite union of prime divisors of the absolute determinants. Set

    K = product_{p in S} p*(p-1) > 0.

`exists_repeat_period` proves that for EVERY multiple k of K, every p in S
divides repeatWeight(W,k), for arbitrary W:

* if p divides W, the assertion is immediate;
* if W=1 modulo p, p divides k;
* otherwise Fermat and p-1 dividing k make the geometric sum zero modulo p.

If a prime divides two new affine forms, it divides their determinant, hence
belongs to S and divides v. It would then divide both original x_i and x_j,
contrary to coprimality. This is `exists_coprime_period`.

Taking r(j)=3-j yields `arbitrarily_long_coprime_repetitions`: k can be larger
than any prescribed natural, while all four new roots remain pairwise coprime,
distinct, and norm-colliding. No factorization of a huge concrete determinant
is required or trusted.

## 3. Concrete prime-base example, and important limitations

`PrimitiveAlignedBlockExample` instantiates the abstract theorem using the
already verified 28-digit words at prime base 372689 from
DistinctDigitCarryObstacle. The new roots have k+1 aligned blocks.

* Each block has constant digit 3 and leading digit 1.
* All digits are positive and less than half the base.
* Histograms and arbitrary additive digit statistics agree on every aligned
  union of blocks.
* For unbounded repetition lengths, the four full roots are pairwise coprime
  and their squared values are not Sidon.

DO NOT strengthen this to preservation of all the original digit conditions:

* The full long words have repeated digits.
* They do NOT retain the GLOBAL inert-prime Eisenstein condition. The original
  block's leading 1 becomes an interior digit. `interior_not_divisible` proves
  this explicit failure for every k>0.
* The total digit sum is exactly (k+1)*111799, proved by `total_digit_sum`.
  Thus the global digit sum is not below the fixed base for large k.
* Primality is asserted for the BASE, not the new roots.

Accordingly, this defeats the blanket aligned-histogram-plus-coprimality
criterion, NOT a criterion also imposing global Eisenstein conditions and
small total digit sum. It does not show that every block class is bad, or
bound its largest Sidon subclass, and it is not a conjecture disproof.

## 4. Sharp elementary capacity bound for all overlapping windows

`SlidingWindowCapacity` fixes a length-d word over a finite alphabet and
an injective integer-valued digit weight phi. Write

    window(w,L,i) = sum_{j<L} phi(w_(i+j)).

Zero padding simplifies indexing, but the fiber constraints only use actual
windows i+L<=d. The exact identity is

    window(i+1)+phi(w_i) = window(i)+phi(w_(i+L)).

`determined_by_prefix` shows that the first L letters and the window profile
determine the word. The stronger `determined_by_short_prefix` observes that
the first window sum also determines the last letter in that prefix.
Consequently, for 1<=L<=d, a fixed profile of ALL overlapping windows has

    at most |alphabet|^(L-1) words.

This is `fiber_card_le_pred`. The earlier weaker |alphabet|^L bound is also
available. Specializations prove the sharp bound B^(L-1) for ordinary digit
sums and squared-digit sums, since both weights are injective on Fin B.
Fixing complete sliding-window histograms is at least as restrictive.

Thus imposing every short overlapping window (L=o(d)) cannot by itself
leave a near-linear number of base-B words of length d. The bound alone
says nothing adverse when L is close to d, and it is NOT an upper bound on
arbitrary square-Sidon subsets.

## Mathematical scope of this continuation

The square-specific construction review produced no valid near-linear
selector or fixed-power upper bound. Generic greedy machinery remains on
the 2/3 exponent scale. The newly verified results test a proposed multiscale
digit approach; they are not being offered as a settlement.

The global-Eisenstein limitation in section 3 is a genuine remaining
qualification, not something to suppress in subsequent work. Any positive
construction still needs an actual integral Sidon subset, and any disproof
still needs the negation of the entire original quantified proposition.

## Verification logs

    /tmp/aligned-block-final.log
    /tmp/primitive-aligned-final.log
    /tmp/sliding-window-sharp-first.log

The final parallel checks and Spec check are recorded in:

    /tmp/aligned-block-recheck.log
    /tmp/primitive-aligned-recheck.log
    /tmp/sliding-window-recheck.log
    /tmp/spec-aligned-sliding-check.log

Spec SHA-256 remains
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.
