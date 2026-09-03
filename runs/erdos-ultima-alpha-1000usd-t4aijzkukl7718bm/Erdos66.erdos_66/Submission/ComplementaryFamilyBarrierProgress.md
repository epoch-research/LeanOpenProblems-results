# Exact mixed-complementary digit families

The original conjecture remains neither proved nor disproved. `Spec.lean`
is unchanged, with its original `sorry`.

## Investigated smoothing mechanism

One way to preserve density when replacing points by digit sets would use
sets B_i of cardinality k in a group of order k^2. Their average mixed count
is exactly one. If every distinct pair B_i,B_j represented every target
exactly once, different colors would introduce no representation error.
For this to be useful with many colors, the self-counts would also need to
remain small; otherwise same-color pairs introduce large spikes.

## Checked tradeoff

`ComplementaryFamilyBarrierExplore.lean` proves, for a nonempty finite family
of q such sets and k>=2, that

    q*(k-1) <= (k+1)*(C-1),

provided every distinct pair has mixed sum count exactly one at every target,
and every self sum count is bounded by C.

Thus C must grow at least linearly with q (for large k), rather than remain
bounded as the number of colors grows. The bound is sharp at the parameter
level for the k+1 lines in a plane over a field of order k: mixed counts are
one and self-count maxima are k. This sharpness example is not separately
formalized here.

## Proof

The centered autocorrelations v_i have:

- sum_z v_i(z)=0;
- v_i(0)=k-1;
- sum_z v_i(z)*v_j(z)=0 for distinct i,j, by the centered mixed-energy identity;
- sum_z v_i(z)^2 <= k^2*(C-1).

Apply the zero-mean coordinate bound to their sum:

    |G|*(sum_i v_i(0))^2
      <= (|G|-1)*sum_i sum_z v_i(z)^2.

Cancel the positive family size, k^2, and k-1 to get the stated inequality.
No Fourier analysis is used.

## Verification and scope

The source file compiles and has a current olean.
`ComplementaryFamilyBarrierAxiomCheck.lean` audits the principal theorem;
only propext, Classical.choice, and Quot.sound occur.

This rules out a uniformly bounded-self-count version of this specific
exact-complementarity averaging scheme. It is not an obstruction to all
approximate digit constructions and does not negate the conjecture.
