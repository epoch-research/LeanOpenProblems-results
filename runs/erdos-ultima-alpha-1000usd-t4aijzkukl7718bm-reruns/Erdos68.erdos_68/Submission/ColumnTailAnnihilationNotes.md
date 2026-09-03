# Exact finite column cancellation removes the retained endpoint

Verified auxiliary work, NOT a settlement of Erdős 68. Spec.lean remains
unchanged with its original sorry. No completed proof or disproof has been
obtained or submitted.

ColumnTailAnnihilation.lean compiles without warnings and has a built olean.
All three printed axiom audits use only propext, Classical.choice, and
Quot.sound.

## General statement

For a finite set of rational weights w_i and rational prefixes B_i, and an
irrational real x, the file proves

    sum_i w_i*(x-B_i)=0
      iff sum_i w_i=0 and sum_i w_i*B_i=0.

The proof separates the rational coefficient of x from the rational boundary.
A nonzero rational multiple of an irrational number cannot be rational.

## Factorial-power specialization

For any j>=1, arbitrary finitely many sample indices N_i, and arbitrary
rational weights, exact cancellation of

    sum_i w_i * (E_j - sum_(k=2)^(N_i+1) 1/(k!)^j)

forces sum_i w_i=0, using the previously verified irrationality of E_j.
There is no fixed-operator restriction: the weights and sample indices can
be chosen separately for each external parameter.

Reusing these weights with ANY other rational prefixes produces a form
independent of its real endpoint. In particular such exact column
annihilation cannot retain a nonzero coefficient of the original alpha.

Main declarations:

* annihilate_iff
* column_annihilate_iff
* endpoint_independent_of_column_annihilation

## Scope

This concerns finite rational weighted combinations of unscaled tails.
It does not forbid differential identities involving additional derivatives,
scaled-tail constructions with different leading coefficients, or approximate
rather than exact column cancellation. Such alternatives still need an
actual small, nonzero integer-form construction. None has been obtained here.

The renewed attempt to access the problem reference failed at DNS resolution.
No external literature update was retrieved. No computation is pending.
