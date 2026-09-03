# A rational factorial-rough series (not a settlement)

`NearFactorialRational.lean` constructs a different sequence of positive integer
reciprocal denominators. It is not a proof or disproof of Erdős 68, and
`Spec.lean` remains unchanged.

The Lean theorem `exists_rational_factorial_rough_series` proves that there is
`d : ℕ → ℕ` with, for every n >= 0,

    (n+1)! divides d_n+1,
    4 (n+2)! < d_n <= (16(n+3)+1) (n+1)!,
    sum_(n>=0) 1/d_n = 1/16.

Thus factorial congruences together with denominators within a linear factor
of that factorial still allow a rational sum. This does NOT preserve the exact
factorial denominators. Nor does it preserve the chain `(d_n+1)|(d_(n+1)+1)`.
The first three denominators, checked in Lean, are 20, 103, 443.

## Construction and estimates

Start with the rational remainder r_0=1/16. At step n, put

    A = (n+1)!,
    b = 1/[16 (n+3)!],
    k = floor((1/(r_n-b)+1)/A)+1,
    d_n = k A - 1,
    r_(n+1) = r_n - 1/d_n.

The floor bounds imply

    1/(r_n-b) < d_n <= 1/(r_n-b)+A,
    b < r_(n+1) <= b+A*r_n^2.

Induction, using `(n+3)! (n+1)! / ((n+2)!)^2 = (n+3)/(n+2)`, proves

    1/[16 (n+2)!] <= r_n <= 1/[4 (n+2)!].

In particular all steps are well-defined, all remainders and denominators are
positive, and r_n tends to zero. Telescoping gives the stated rational sum.

For the upper denominator bound, subtract the next baseline from the lower
remainder bound:

    r_n-b >= 1/[16 (n+3) (n+1)!].

For the lower bound use `r_n-b < 1/[4 (n+2)!]`. Inverting these inequalities
and applying the floor bounds gives exactly the displayed bounds on d_n.

## Verification status

The auxiliary file compiles with no holes. The axiom check for the existence
theorem lists only `propext`, `Classical.choice`, and `Quot.sound`.
The construction does not establish a precise asymptotic constant for d_n,
a growth theorem for strict Engel multipliers, or any conclusion about the
original series. A proof using the exact factorial structure is still missing.
