# Relative coefficient norms and a height-independent detection threshold

Verified auxiliary progress, NOT a proof or disproof of Erdos 68.
`Spec.lean` remains unchanged with its original `sorry`.

`LambertRelativeCombinationBound.lean` has 323 lines, compiles without
warnings, has a built olean, and has no proof holes. All five printed
principal axiom audits list only `propext`, `Classical.choice`, and
`Quot.sound`.

## Improvement over the previous arbitrary-support detector

Let d>=12, lambda=(d!)^(1/d), and let w_0,...,w_M be integers, not all
zero, with |w_j|<=Q and 4Q<=d!. Let rawTail(d-2,n) be the existing
full-target raw operator cancelling rows 2,...,d-1.

The file proves that, if

    H >= (d+1)*(3*log2(d)+136),

then some H<=n<H+d satisfies

    sum_(j=0)^M w_j*rawTail(d-2,n+j) != 0.

The support length M is arbitrary. Unlike the previous verified threshold

    (d+1)*(log2(Q)+2*log2(d)+135),

the new threshold does not depend on Q. This is not necessarily numerically
smaller for very small Q, but it removes the height term when Q grows with d.

## Relative norm estimate

First suppose w_0!=0 and define the existing cyclic aggregate

    c_h=sum_(j congruent h modulo d) w_j/lambda^j.

The already verified digit-separation argument gives ||c||_infinity>=1/2.
The weighted absolute mass at j>=d is at most 2Q/d!<=1/2. For j<d, the
coefficient w_j/lambda^j differs from c_j only by terms in this late mass.
Thus each early coefficient has absolute value at most ||c||_infinity+1/2.
Splitting the complete mass into its early and late parts gives

    sum_(j=0)^M |w_j|/lambda^j
        <= 2*(d+1)*||c||_infinity.

This is `weighted_mass_bound`. It replaces the previous crude bound 2Q.

The first row is detected with normalized magnitude at least

    exp(-48)*||c||_infinity/(lambda+1).

The existing remaining-row estimate, with its budget parameter set to d+1,
and the new mass bound give an upper bound for the complete omitted-row
combination of

    exp(-48)*||c||_infinity/(2*d).

Since lambda+1<2*d and ||c||_infinity>0, it cannot cancel the detected row.
The explicit power budget is

    4*(d+1)*d^2 <= 2^(3*log2(d)+6).

Trimming to the earliest nonzero weight handles arbitrary nonzero vectors.
The shifted detecting window is then translated back, as in the previous
arbitrary-support proof. No final-degree bound is used.

Principal declarations:

* weighted_mass_bound
* relative_row_detection
* relative_raw_detection
* relative_raw_detection_nonzero
* relative_raw_detection_explicit

## Arithmetic application remains missing

These are raw rational-boundary forms, not integral-boundary forms. The
particular detected phase need not be the phase cleared by scalar
pigeonholing. The result does not give useful projected lattice minima.

An informal recheck of the existing simultaneous counting construction,
retaining the complete endpoint, still leaves a gap. In the previous
notation d=K+2, M=K(K+3)/2, D input samples, and d output phases,

    T=H+(D-1)+(d-1)+M,
    C=T!/product_(k=2)^(K+1) k!.

For D~b*K^2 and the new choice H=O(K log K), Stirling's formula gives

    log C=(2b+1/2)*K^2*log K+o(K^2 log K).

The uniform error logarithm is of smaller order at this H. Counting the
small integer output matrix under hypothetical rationality therefore still
requires, with these sufficient estimates, a weight-budget logarithm whose
leading size is

    (2+1/(2b))*K*log K,

whereas the detector permits only log Q<=K*log K+O(K). Removing the previous
height-dependent starting-index cost does not remove this remaining
factor-two gap. This calculation is informal, not an impossibility theorem
for alternative constructions or an additional Lean declaration.

No numerical search was run. No proof or disproof of the conjecture, nor a
complete informal argument awaiting formalization, has been obtained. No
submission check was made, and nothing remains pending compilation.
