# Cancellation-aware reduced denominator bounds for growing blocks

Verified auxiliary work, NOT a proof or disproof of Erdős 68.
Spec.lean is unchanged with its original sorry. No complete solution has
been obtained or submitted.

ReducedBlockDenominatorBound.lean compiles without warnings and has a current
olean. Its four printed principal axiom audits list only propext,
Classical.choice, and Quot.sound. No external calculation is used as a premise.

## General rational-sum arithmetic

For rationals x,y the file proves

    den(x)*den(y) divides den(x+y)*gcd(den(x),den(y))^2.

Indeed x=(x+y)-y implies den(x) divides den(x+y)*den(y), and similarly for y.
The gcd extraction lemma and the gcd-lcm identity give the displayed result.

For any finite rational sequence q_0,...,q_(n-1), put

    P=product_(j<i<n) gcd(den(q_i),den(q_j)).

Induction then proves

    product_(i<n) den(q_i) divides den(sum_(i<n) q_i)*P^2.

In the induction, the denominator of a prefix divides the product of its
individual denominators, so its gcd with the next denominator divides the
product of the new pairwise gcds. No pairwise coprimality is assumed, and
cancellation in the whole sum is allowed.

## Factorial-minus-one blocks

Set d_k=k!-1 and

    block(k,n)=sum_(i=0)^(n-1) 1/d_(k+i),   k>=2.

Using FactorialMinusOneLcmBound's established pairwise gcd estimates gives

    d_k^n <= den(block(k,n))*(k+n)^(2*n^3).

This bounds the actual reduced denominator, unlike a bound merely on the lcm
of the individual denominators.

For m>=9, choose k=8*m^2. The elementary factorial estimate and base bound

    d_(8*m^2)>=m^(8*m^2),   8*m^2+m<=m^3

give the explicit consequence

    den(block(8*m^2,m)) >= m^(2*m^3).

Write prefix(N)=sum_(k=2)^(N-1) 1/(k!-1). Since the block is the difference
of its two endpoint prefixes, its reduced denominator divides the product
of their reduced denominators. Hence at least one of

    den(prefix(8*m^2)), den(prefix(8*m^2+m))

is at least m^(m^3).

The Lean prefix includes indices zero and one as 1/(Nat.factorial k-1);
these two terms are zero, so the stated mathematical prefix agrees with it.

Principal declarations:

* product_den_dvd_sum_den_mul_pairGcd_square
* block_reduced_denominator_bound
* growing_block_reduced_height
* nearby_prefix_reduced_height

## Limitation

Large reduced denominators of partial sums do not imply an irrational limit.
An integer-linear-form proof would need suitably small UPPER bounds on the
clearing multiplier relative to a nonzero analytic error, or a different
arithmetic contradiction. These lower bounds do not supply that step and do
not prove infinite non-stabilization of the factorial-grid approximants.

Nothing is pending compilation or computation. The original conjecture
remains unsettled in this workspace.
