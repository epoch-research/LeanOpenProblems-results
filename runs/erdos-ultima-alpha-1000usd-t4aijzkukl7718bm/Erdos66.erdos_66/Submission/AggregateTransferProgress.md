# Collective cyclic flatness and affine-label root counts

## Original task status

The conjecture in `Spec.lean` is still neither proved nor disproved.
The file is unchanged, retaining its original `sorry`. Nothing has been
submitted as a solution.

## Collective integer transfer

`AggregateBlockTransferExplore.lean`, namespace
`Erdos66AggregateBlockTransfer`, replaces pairwise mixed flatness by a weaker
condition on the sum at each coarse target. For colors C_i modulo M, set

    R_q(t) = sum_{i=0}^q r_cyclic(C_i,C_(q-i);t),
    L_q(t) = sum_{i=0}^q lower(C_i,C_(q-i);t).

The file proves 0<=L_q<=R_q and, for q>0, the exact identity for the integer
set obtained by K-fold outer repetition of each color:

    r_A(q M K + t.val + M r)
      = r R_q(t) + (K-r) R_(q-1)(t) + L_q(t)-L_(q-1)(t).

Here 0<=r<K. In particular, if both R_q(t) and R_(q-1)(t) differ from mu by
at most E, then the natural representation count differs from K mu by at
most

    K E + mu + E.

No nesting, scalar weights, or flatness of individual color pairs is
assumed. The carry remainder is bounded as a difference of nonnegative
aggregates, instead of summing all pairwise error bounds.

Principal declarations:

* `aggregate_block_formula`
* `aggregate_block_error`

## Affine parameters reduce all fine targets to one signed convolution

`AffineRootAggregateExplore.lean`, namespace `Erdos66AffineRootAggregate`,
works over any finite field F of odd characteristic. For labels u_i=a+i,
weights v_i, and one coarse sum q, assume all used u_i are nonzero and
2a+q is nonzero. The weighted root count is exactly

    sum_{i+j=q} v_i v_j
      + chi((2a+q)s-t^2)
        sum_{i+j=q} (v_i chi(a+i))(v_j chi(a+j)).

All labels are restricted to i,j<h. The absolute error is therefore bounded
by the absolute value of the SINGLE signed convolution, uniformly in every
fine target (t,s). There is no factor counting the fine targets in this
algebraic bound.

For v_i=1_D(i), the same expression is proved to be a sum of actual set-pair
counts for the colored curves

    C_i = {(x,x^2/(a+i)) : x in F} if i in D, else empty.

The separate coarse labels distinguish these curves; thus no origin
multiplicity correction is required. Assuming D is contained in [0,h),
the unsigned main term is EXACTLY r_D(q).

Principal declarations:

* `rootAggregate_identity`
* `rootAggregate_error`
* `singleton_parabola_pair_count`
* `coloredCurve_aggregate`
* `selectedWeight_fiber_eq_sumRep`
* `coloredCurve_aggregate_error`

## Completed field-plane to integer pipeline

Two more production files complete the conditional composition:

* `AggregateCyclicThickeningExplore.lean` tags the mixed fibers by their
  color-pair index and applies `two_fiber_error` to their disjoint union.
  Collective field-plane flatness with mean mu and error E becomes cyclic
  aggregate flatness with mean K^2 mu and error

      Ecyc = K^2 E + 2K(mu+E).

  There is no factor for the number of color pairs. An additional L-fold
  outer repetition gives natural counts with mean L K^2 mu and error

      (L+1) Ecyc + K^2 mu.

* `AffineAggregateIntegerTransferExplore.lean` proves `affine_integer_error`.
  Given finite D in [0,h), an admissible affine parameter a, and q>0 with
  q<h, assume at BOTH m=q and m=q-1:

      |r_D(m)-mu| <= E0,
      |sum_{i+j=m} 1_D(i)chi(a+i) 1_D(j)chi(a+j)| <= E1.

  Then the actual natural block set made from the individually selected
  curves, coordinate thickening K, and outer repetition L has its count
  at every fine target in the q-th macroblock within

      (L+1)[K^2(E0+E1)+2K(mu+E0+E1)] + K^2 mu

  of L K^2 mu. No origin repair, nesting, or pairwise flatness hypothesis
  is used. Parameters a+i for i<h and both 2a+m must be nonzero; odd
  characteristic is explicit.

`AffineRootAggregateExplore.lean` additionally provides `diagonal_sum` and
`coloredCurve_plane_error` to connect the double label sums to the
q-indexed form used by the carry formulas.

## Verification and remaining gap

All four production files compile and have built oleans.
`AggregateTransferAxiomCheck.lean` audits all main steps, including the
complete conditional integer theorem. Only propext, Classical.choice,
and Quot.sound occur.

The field-plane, cyclic, and integer steps are now composed, but the
root identity does not manufacture an unsigned coarse profile: it leaves
precisely r_D(q), together with the signed-convolution requirement.
The pipeline also does not compare old and new colors from different
fields or preserve an accurate natural-number prefix through a change of
period.

Thus collective control is a genuinely weaker sufficient condition than
pairwise palette flatness, but no compatible family satisfying it at all
necessary scales has been obtained. In particular these results do not
settle the original conjecture.

### Subsequent scalar construction

`BinarySignedProfileProgress.md` records a checked construction of the scalar
unsigned and signed profiles outside O(log^2 L) coarse exceptions, and its
composition with the integer transfer. Those exceptions are entire fine
blocks. Their repair and compatible changes of period remain unresolved.
