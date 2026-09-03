# A rational shifted-divisibility chain with bounded multipliers

This is auxiliary work, not a settlement of Erdős 68. Spec.lean is unchanged
and still contains its original sorry. No proof or disproof has been submitted.

`BoundedMultiplierRational.lean` compiles without warnings and has a built
olean. Its two printed axiom audits list only propext, Classical.choice,
and Quot.sound. It imports only FormalConjecturesUtil.

## Verified statement

`exists_rational_bounded_chain` constructs positive natural denominators d_n
such that

    d_(n+1)+1 = q_n (d_n+1),       2 <= q_n <= 6,
    sum_(n>=0) 1/d_n = 1/16.

`shifted_chain` gives the corresponding divisibility assertion, and
`ratio_between_consecutive_integers` verifies

    q_n < d_(n+1)/d_n < q_n+1

for a multiplier q_n in {2,3,4,5,6}. The ratios here are rational numbers.
`state_growth` gives A_n >= 8*2^n, where d_n=A_(n+1)-1.

## Interval construction

Maintain A>=8 and a rational remainder

    1/(4A) <= r <= 1/A.

For q in {2,...,6} define

    L_q(A)=1/(qA-1)+1/(4qA),
    U_q(A)=1/(qA-1)+1/(qA).

The verified inequalities are

    L_6(A)<=1/(4A),  1/A<=U_2(A),  L_q(A)<=U_(q+1)(A) (q>=2).

For the overlap use qA>=16 to obtain

    L_q(A)<=4/(3qA)<=2/((q+1)A)<=U_(q+1)(A).

Thus the five intervals cover [1/(4A),1/A]. Choose q leaving

    A'=qA,   r'=r-1/(A'-1),   1/(4A')<=r'<=1/A'.

Start at (A,r)=(8,1/16). All remainders remain positive, A grows at least
geometrically, and r tends to zero. Telescoping proves the rational sum.

## Scope and remaining gap

This refutes a general irrationality criterion using only the shifted
chain and an upper bound on the multipliers: even uniformly bounded
multipliers permit a rational sum. It does NOT preserve the exact factorial
multipliers 3,4,5,..., nor does it assert that the multipliers tend to infinity.
The selection rule is NOT asserted to be the strict or ceiling modified
Engel rule. Thus it does not refute a theorem specifically about rational
orbits of either greedy rule.

It supplies no infinite nonvanishing result for the original series, no
integer descent for its exact multipliers, and no proof or disproof of the
conjecture in Spec.lean.
