# Exponential graph / CRT review

## Status

The original conjecture remains unproved and undisproved. Spec.lean is unchanged.
No completed proof or exact-negation theorem has been submitted. This is an
informal mathematical review, not a new verified Lean theorem.

## Exact finite model considered

For an odd prime p, use the group F_p^units x F_p, with multiplication in the
first coordinate and addition in the second. Both factors are cyclic and their
orders p-1 and p are coprime, so the product is cyclic by CRT.

For u nonzero let C_u consist of (x,u*x), for x a nonzero field element. In
exponent coordinates x=g^k this is the graph (k,u*g^k). Distinct parameters give
disjoint curves. A mixed representation of (t,s), with t nonzero, satisfies

    x*y=t,  u*x+v*y=s,

and hence

    u*x^2-s*x+v*t=0.

The constant term is nonzero, so the quadratic's roots are automatically
nonzero. Its discriminant is s^2-4*u*v*t; the ordered mixed count is therefore

    1 + chi(s^2-4*u*v*t).

For a parameter set U, grouping the union count by w=u*v gives

    |U|^2 + sum_w m_U(w)*chi(s^2-4*w*t),

where m_U(w) is the number of ordered parameter products equal to w.
These coefficients are nonnegative and sum to |U|^2. Consequently the direct
L1 bound permits error |U|^2, the whole nominal main term. It does not inherit
the signed additive-fiber cancellation of the parabola construction.

This does not prove that exponential graphs cannot work by some other estimate.
In particular it is not an obstruction for arbitrary natural-number sets.

## Ordinary prefixes remain distinct

CRT removes a finite field-plane-to-cyclic mismatch, but a cyclic count still
combines the ordinary counts at n and n+p*(p-1), for representatives in one
period. No estimate separating those counts, controlling short prefixes at the
correct local mean, or comparing changing prime periods was obtained.

No sufficient fixed-coefficient finite-prefix construction or unrestricted
logarithmic fluctuation contradiction resulted from this review.
