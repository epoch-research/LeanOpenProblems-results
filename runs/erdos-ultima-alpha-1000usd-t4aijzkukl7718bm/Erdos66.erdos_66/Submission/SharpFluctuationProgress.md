# Removing the radial factor-two loss

## Status

The original conjecture remains neither proved nor disproved. `Spec.lean`
is unchanged with its original `sorry`. No proof has been submitted.

## New checked result

`SharpFluctuationExplore.lean` improves the earlier necessary squared-error
coefficient bound from c/2 to c.

If A is a witness with nonzero coefficient c, and f eventually bounds
`(r_A(n)-c H_(n+1))^2` above with `f(n)/log(n) -> d`, then c<=d.
No limit of the squared error itself is assumed.

Consequently, for every a>=0 with a^2<c, arbitrarily large n satisfy

    |r_A(n)-c log(n)| > a sqrt(log(n)).

The harmonic-centered version and frequent squared-error version also
compile. Principal declarations are audited by
`SharpFluctuationAxiomCheck.lean`; they use only propext, Classical.choice,
and Quot.sound.

## Method

Apply the existing weighted convolution-square stability theorem not to
f and g directly, but to f(n)*r^(k*n) and g(n)*r^(k*n). The resulting
squared-mass lower bound has radius r^(2k+2), while its error-energy upper
bound has radius r^(2k+1). The generating-function power-ratio limits give

    c/(2k+2) <= d/(2k+1)

for every natural k. Letting k grow removes the loss and yields c<=d.
The finite-prefix maximum-envelope argument and the bounded difference
between H_(n+1) and log(n) give the frequent log-centered consequence.

## Main declarations

Namespace `Erdos66SharpFluctuation`:

* `tilted_weighted_lower_bound`
* `normalized_indicator_power_limit`
* `normalized_profile_square_power_limit`
* `normalized_series_power_limit`
* `tilted_envelope_limit_bound`
* `sharp_error_envelope_limit_lower_bound`
* `sharp_eventual_squared_error_bound`
* `sharp_frequently_squared_error_gt`
* `sharp_frequently_abs_harmonic_error_gt`
* `sharp_frequently_abs_log_error_gt`
* `sharp_exists_large_log_fluctuation`

The adjective sharp here refers to removing this particular radial loss;
no theorem claiming optimality of the constant among all possible methods
has been proved.

## Remaining gap

Square-root-logarithmic fluctuations are compatible with o(log n), so this
cannot serve as a disproof. Reconsidered digit and finite-field tower
constructions still do not supply the required intermediate prefix profile
and controlled mixed counts. No infinite witness has been constructed.
