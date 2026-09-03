# Direct polarization collapses under positivity

Verified auxiliary work, NOT a proof or disproof of Erdos 68. Spec.lean
remains unchanged with its original sorry. No completed solution or
submission check resulted from this continuation.

PolarizedQuadraticKernel.lean compiles without warnings and has a built
olean. Its four printed principal axiom audits use only propext,
Classical.choice, and Quot.sound.

## Exact matrix statement

For real x and real vectors a,r on any index type, set

    M(i,j)=x*a_i*a_j-a_i*r_j-r_i*a_j.

The file proves

    M(i,i)*M(j,j)-M(i,j)*M(j,i)=-(a_i*r_j-a_j*r_i)^2.

Consequently every such two-coordinate determinant is nonpositive. If
all these determinants are also nonnegative, every wedge vanishes. If
some a_k is nonzero then r_i=(r_k/a_k)*a_i for every i, and

    M(i,j)=(x-2*r_k/a_k)*a_i*a_j.

If a is identically zero then M is zero. This is verified as
outer_product_or_zero. The theorem posSemidef_outer_product_or_zero obtains
the minor inequalities from Matrix.PosSemidef and gives the same result.
The theorem not_posDef_two rules out positive definiteness in dimension
two directly from the determinant identity.

## Connection and scope

The scalar quadratic physical-domain kernel has retained coefficient a^2
and boundary 2*a*(R(0)+R(1)). Directly polarizing this expression gives
exactly the matrix above, with r_i=R_i(0)+R_i(1). Thus this particular
polarization cannot yield positive-definite matrices of growing dimension.
The connection is explanatory; the new Lean statements are the exact
algebraic and positive-semidefinite matrix results displayed above.

This does NOT rule out full-rank retained coefficient matrices, higher
column-degree kernels, other Gram constructions, or other irrationality
methods. No such family with sufficiently small cleared determinants has
been constructed here. The earlier integer-matrix criterion still needs
smallness relative to matrix dimension, not merely a determinant tending
to zero.

## Other review

The exact factorial growth and shifted-divisibility conditions were
revisited. The rational comparison series either change the multipliers
or weaken the factorial congruence, and do not disprove the target. No
rational-orbit height descent, infinite carry violation, or useful
nonzero boundary-cleared form was obtained. There is no complete informal
proof awaiting formalization and no pending compilation or computation.
