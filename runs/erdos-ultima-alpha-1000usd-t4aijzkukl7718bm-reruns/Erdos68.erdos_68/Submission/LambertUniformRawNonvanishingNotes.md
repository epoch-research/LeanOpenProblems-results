# Uniform nonvanishing windows for the raw Lambert operators

This is verified auxiliary progress, NOT a proof or disproof of Erdos 68.
Spec.lean remains unchanged with its original sorry.

Both new files compile without warnings and have built oleans:

* LambertCyclicRowLowerBound.lean
* LambertUniformRawNonvanishing.lean

They contain no proof holes. Their five printed principal axiom audits use
only propext, Classical.choice, and Quot.sound.

## Main full-target result

Write

    lambda_d=(d!)^(1/d),
    Q_K(E)=product_(k=2)^(K+1)(k!*E^k-1),
    epsilon_K(n)=Q_K(E)(alpha-S_n),

where S_n is the existing rational Lambert prefix. K counts the cancelled
rows; the first uncancelled row is d=K+2.

For K>=10 and

    H >= (K+3)*(2*(log2(K+2)+1)+130),

raw_nonzero_in_every_window proves that some n satisfies

    H <= n < H+K+2,    epsilon_K(n) != 0.

Here log2 is the natural floor logarithm used by Lean. The explicit threshold
is verified; describing its order as K log K requires no new premise.

More precisely, raw_lower_in_every_window allows any L with d^2<=2^L and
H>=(d+1)*(L+130), and supplies an index in that window with

    exp(-48)/(2*lambda_d) < lambda_d^n * abs(epsilon_K(n)).

All omitted rows of the original target are retained. This is not merely
nonvanishing of one geometric row or of a finite truncation.

## Individual-row lower bound

For d>=12 and 2<=k<d, the file proves

    0 <= k!/lambda_d^k <= 3/4.

Together with the earlier sum bound <=12 and the elementary inequality
exp(-4t)<=1-t for 0<=t<=3/4, this gives

    product_(k=2)^(K+1)(1-k!/lambda_d^k) >= exp(-48)

whenever K+1<d.

Normalize a geometric row by lambda_d^n. It becomes a function on ZMod d.
The normalized raw factor is t_k*shift_k-I, where t_k=k!/lambda_d^k.
The reverse triangle inequality in the finite supremum norm gives

    norm((t_k*shift_k-I)f) >= (1-t_k)*norm(f).

The initial normalized row has norm at least 1/lambda_d. Iterating the
factors shows that in EVERY complete phase window there is an index n with

    lambda_d^n * abs(Q_K(E)r_d(n)) >= exp(-48)/lambda_d.

This is row_lower_in_every_window. It avoids using the very small lower
bound obtained by clearing the rational denominator of an individual row.
It asserts no fixed sign and does not identify a phase independent of H.

## Controlling the other rows

The rate comparison proves

    (lambda_d/lambda_(d+1))^(d+1) <= 1/2,    d>=6.

Split the remaining rows into d near rows and the infinite far tail. Their
weighted total is bounded by

    2*exp(12)*d*(lambda_d/lambda_(d+1))^n
      +4*exp(12)*d*(3/4)^n.

The near bound uses monotonicity of the rates. The far bound uses the existing
p-series estimate, lambda_j>=j/3, and lambda_d<=d/2. For the stated threshold
this is strictly below exp(-48)/(2*lambda_d). The first-row lower bound
therefore survives in the full infinite sum.

## Scope and remaining gap

These are RAW forms with rational boundaries. No boundary denominator is
cleared in the main theorem. Multiplication by a positive clearing integer
preserves nonvanishing, but the available estimates do not make the resulting
integer forms tend to zero.

Nor does this theorem establish nonvanishing after an arbitrary bounded
integer linear combination of samples. Such combinations are precisely
what the boundary-lattice construction uses; they can cancel the leading
row at the selected phase. The new result therefore must not be substituted
for the missing useful-minimum or nonzero-combination theorem.

The argument differs from the earlier prime-leading-coefficient detector:
it gives a norm lower bound for the specific raw cancelling operators in
every sufficiently late short window. It does not impose or evade any
boundary-integrality condition.

No complete informal proof or disproof of the original conjecture was
obtained. No numerical search or new submission check was run. Compilation
and axiom checks have completed; no process remains pending.
