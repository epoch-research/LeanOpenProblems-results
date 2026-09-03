# Finite kernel interpolation (verified; not a settlement)

`Submission/FiniteKernelInterpolation.lean` compiles. Its three principal
axiom audits list only `propext`, `Classical.choice`, and `Quot.sound`.
The original conjecture in `Submission/Spec.lean` remains unchanged and
unproved.

## Integer-valued interpolation

The file proves `exists_integerValued_interpolant`: any integer data on
0,...,N have a rational polynomial interpolant which is integer-valued on
all natural inputs. The construction uses the Newton basis

    choosePoly_k(X) = X(X-1)...(X-k+1)/k!,
    choosePoly_k(n) = choose(n,k).

Adding an integer multiple of choosePoly_(N+1) adjusts the next value
without changing the preceding values, and preserves integrality at all
natural inputs.

## Arbitrary boundary values are compatible with finite row zeros

Let A,B be integers, and assume m!-1 divides A for m=2,...,N+1.
Then `finite_rows_zero_arbitrary_boundary` supplies a rational polynomial H
such that

    H(n) is an integer for every natural n,
    H(1)=B,
    A-(1-1/m!)[m H(m-1)-H(m)] = 0,  m=2,...,N+1.

The node values are forced recursively by

    H(m)=m H(m-1) - (A/(m!-1))*m!.

They are integers by the divisibility assumption, so the interpolation
lemma applies. In particular, B is entirely arbitrary in this finite-zero
construction; these conditions alone do not make B/A close to alpha.

## Exact sum for rational-polynomial kernels

The file also verifies `hasSum_kernel`, extending the earlier one-column
identity to rational polynomials H:

    sum_(m>=2) [A-(1-1/m!)(m H(m-1)-H(m))]/(m!-1)
      = A*alpha-H(1).

Polynomial growth divided by factorial growth is summable. The correction
is exactly H(m-1)/(m-1)!-H(m)/m!, so it telescopes. Combining this identity
with the interpolation result gives A*alpha-B, regardless of how many
initial rows have been set to zero.

No estimate proves that the remaining rows have small total or a controlled
sign. Thus this is an explicit limitation of finite interpolation alone,
not a proof that every possible kernel construction fails. In particular,
no nonzero integer forms tending to zero have been obtained and no proof
or disproof of Erdős 68 has been submitted.
