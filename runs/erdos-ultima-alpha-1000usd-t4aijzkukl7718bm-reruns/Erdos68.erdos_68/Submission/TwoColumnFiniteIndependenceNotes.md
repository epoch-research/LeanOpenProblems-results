# Finite independence of two factorial columns

This is verified auxiliary work, NOT a proof or disproof of Erdős 68.
Spec.lean retains its original sorry. The earlier submission check did not
pass verification; no completed proof has been obtained.

TwoColumnFiniteIndependence.lean compiles without warnings, has a current
olean, and its four principal axiom audits use only propext,
Classical.choice, and Quot.sound.

## Verified statement

For H,N natural, let a_i,b_i be integers, 0<=i<=N, with

    |a_i| <= H^2,   |b_i| <= H^2.

If both

    sum_i [a_i/(2H+2i)! + b_i/(2H+2i+1)!] = 0,
    sum_i a_i/((H+i)!)^2 = 0,

then every a_i and b_i is zero. These are rational finite sums; the
parentheses around the first summand are part of the statement.

The second identity first forces all a_i to vanish. Consecutive squared
factorial denominators have ratio (H+i+1)^2>H^2. The first identity then
contains only odd indices, whose consecutive denominator ratios are
(2H+2i+2)(2H+2i+3)>H^2.

The generic `chain_zero` proves the required finite digit uniqueness.
For d_(i+1)=r_i*d_i, the cleared prefix numerators obey

    A_0=c_0,  A_(i+1)=r_i*A_i+c_(i+1).

If A_N=0, the last coefficient is divisible by r_(N-1). Its strict
absolute bound makes it zero, so A_(N-1)=0, and induction finishes.

Principal declarations:

* chain_zero
* square_factorial_zero
* odd_factorial_zero
* two_column_zero

## Missing application and a window-cost caution

A relation for the full Lambert coefficients has NOT been shown to
annihilate these two columns individually. The lemma does not assert such
a transfer. The existing CombinedColumnModulus results give divisibility,
not equality to zero.

In a proposed boundary-window application, the common clearing index is
T=H+D-1+M, where D is the window length and M is the raw operator degree.
The earliest factorial-column error starts at H, not T. It is invalid to
estimate the clearing cost as if T were H+M while simultaneously taking
D comparable to H to obtain a small pigeonhole weight bound. That omitted
D term destroys the proposed small-integer transfer estimate. No compatible
choice supplying the missing transfer and nonvanishing has been proved.

For perspective, even the exact full Lambert coefficients admit the small
finite rational relation

    1*(7/24) + 2*(1/120) - 2*(111/720) = 0

at indices 4,5,6. Its first-column value is 1/18 and its second-column value
is 7/36; the third column contributes -1/4. Thus full-column cancellation
need not be columnwise cancellation. This numerical identity is an informal
illustration here, not a new assertion in the Lean file.

No new construction settling the original conjecture follows from this
lemma. No computation is running.
