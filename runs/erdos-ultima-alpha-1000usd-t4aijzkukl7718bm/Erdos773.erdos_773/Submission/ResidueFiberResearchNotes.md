# Residue-fiber continuation

The main conjecture is NOT settled. `Spec.lean` was not changed and still has
its single admission for 0 < epsilon <= 1/3.

## Positive within-fiber result (verified)

`ResidueFibers.lean` proves, for natural q,r with q>0 and gcd(q,2*r)=1, that

    {(q*a+r)^2 : 0 <= a <= q}

is Sidon. The name is
`Erdos773.ResidueFibers.unit_progression_squares_sidon`.
For r>0 these are positive integer squares. This is a square-root-scale
construction, not a near-linear one.

Proof: a collision reduces, after cancellation, to

    q*(a^2+b^2-c^2-d^2) + 2*r*(a+b-c-d) = 0.

The coprimality condition makes the two index sums congruent modulo q.
If their difference were nonzero, its absolute value would be at least q.
For indices in [0,q], such a gap forces the squared-index sums to be ordered
in the same direction, contradicting the displayed equation. Thus the index
sums agree; the squared-index sums then agree, and the unordered pairs agree.

## Mixed-fiber check (verified)

The theorem `separate_fiber_conditions_do_not_suffice` checks all three
conditions at q=11:

* the r=10 fiber is Sidon;
* the r=9 fiber is Sidon;
* the coarse square residues {10^2,9^2}={1,4} in ZMod 11 are Sidon.

Nevertheless their union is not Sidon, because

    54^2 + 53^2 = 10^2 + 75^2 = 5725.

The roots 54 and 10 lie in the r=10 fiber; 53 and 75 lie in the r=9 fiber.
The example comes from the symbolic identity, also verified over integers,

    (5*q-1)^2+(5*q-2)^2 = (q-1)^2+(7*q-2)^2.

Only the q=11 instance of all the packaged fiber conditions is asserted by
the Lean theorem. No general-family conclusion beyond the displayed
polynomial identity is needed here.

## Remaining issue

When the low residues have been matched, the higher digits still satisfy

    2*r*(x-x') + 2*s*(y-y')
        + q*(x^2+y^2-x'^2-y'^2) = 0.

The within-fiber theorem does not settle this mixed equation. No selector
construction controlling all such equations with a subpower loss was found.
The explicit failure above is a failure of the proposed sufficient lifting
conditions, not a disproof of Erdős 773.

Both printed axiom audits contain only propext, Classical.choice, Quot.sound.
The file has no admissions and was verified with

    lake env lean -s 65536 Submission/ResidueFibers.lean

Log: /tmp/residue-fibers.log
