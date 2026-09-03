# Variable-coefficient Lambert row annihilation

This is auxiliary work, not a settlement. Spec.lean is unchanged and still
contains its original sorry. No proof or disproof has been submitted.

`VariableRowAnnihilation.lean` compiles and has a built olean. All three
printed axiom audits list only propext, Classical.choice, and Quot.sound.

## Verified constraint

For any finite integer weights z_i, arbitrary nonnegative exponents e_i,
and nonzero integer a,

    sum_i z_i/a^(e_i) = 0  implies  a-1 divides sum_i z_i.

Multiply by a^M with M=max e_i. The resulting integer sum vanishes.
Reduction modulo a-1 replaces each power of a by 1, proving the result.
In particular a>=3 excludes sum_i z_i=1.

The factorial-row specialization states that, for d>=2 and arbitrary
selected indices n_i,

    sum_i z_i / ((d!)^floor(n_i/d)*(d!-1)) = 0

forces d!-1 to divide sum_i z_i. Thus it also applies to variable-coefficient
operators and nonconsecutive indices, not only the earlier commuting
constant-coefficient operators. Simultaneous integer-weighted annihilation
of several rows therefore retains each such divisibility requirement on
the coefficient of the constant sequence.

## Scope and remaining gap

This does not exclude all annihilator constructions. It proves no analytic
error lower bound, no nonvanishing result for a total form, and no useful
asymptotic lower bound on the lcm of the row denominators. It also must not
be applied directly to arbitrary rational weights just because their sum
or a total boundary is integral. Multiplying rational weights by a common
denominator gives the displayed condition on that scaled weight sum only.

The lower-order variable-coefficient proposal has not produced a sequence
of small, nonzero integer forms. The row-GCD non-stabilization criterion
likewise remains unproved. There is no running computation or complete
informal proof awaiting formalization.

## Subsequent quantitative common-multiple bound

FactorialMinusOneLcmBound.lean now supplies an explicit lcm lower bound:
for m>=5, the lcm of ((4m^2+j)!-1), 0<=j<m, is at least m^(m^3).
Consequently annihilation of those rows by integer weights with nonzero
sum A forces |A|>=m^(m^3). See FactorialMinusOneLcmBoundNotes.md.
This fills in a quantitative arithmetic estimate, but leaves the zero-sum
case and the total-form nonvanishing problem unresolved.
