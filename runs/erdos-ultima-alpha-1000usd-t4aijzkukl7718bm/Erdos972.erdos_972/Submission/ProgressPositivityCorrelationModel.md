# Finite positivity obstruction — conjecture remains unresolved

`Submission/Spec.lean` is unchanged and still contains its original `sorry`.
No proof of the conjecture or irrational counterexample has been obtained.
The model below is explicitly NOT a model of actual primes or the floor map.

## New verified file

`Submission/PositivityCorrelationModel.lean`
Namespace: `Erdos972PositivityCorrelationModel`.

On twelve equally weighted points, define:

```
f = (6,0,0,6,0,0,0,0,0,0,0,0)
g = (0,6,0,0,0,0,6,0,0,0,0,0)
A = (6,6,6,6,6,6,-4,-4,-4,-4,-4,-4)
B = (6,6,6,-4,-4,-4,6,6,6,-4,-4,-4).
```

Write `E` for the normalized mean, `R=f-A`, `S=g-B`, and `a=max(A,0)`,
`b=max(B,0)`. The file proves all of the following:

- f,g are nonnegative, with f<=a and g<=b.
- On the positive support of f, A=f; on the positive support of g, B=g.
  Thus the respective remainders vanish there, not merely have the correct sign.
- E f = E g = E A = E B = 1.
- For EVERY pair of functions Phi,Psi on the reals,

      E[Phi(A) Psi(B)] = E[Phi(A)] E[Psi(B)].

- For EVERY function Phi or Psi,

      E[Phi(A) g] = E[Phi(A)],
      E[f Psi(B)] = E[Psi(B)].

- All three linear Type-I-style covariances vanish.
- The two mixed positive-remainder covariances and the covariance of the
  two positive remainders also vanish.
- E a = E b = 3.
- The simultaneous majorant-residual product is strictly positive:

      E[(a-f)(b-g)] = 3.

- Nonetheless, f*g=0 at EVERY point and Cov(R,S)=-1.

The main theorem `finite_positivity_obstruction` packages the principal
properties. This is a counterexample only to an inference from these
finite mean/profile/positivity properties to a positive pair correlation.
It does not refute any theorem about the actual arithmetic sequences.

The numerical cancellation is exact: the evaluated majorant baseline is
3+3-9=-3, while the positive residual product contributes precisely +3.
Thus even full nonlinear profile independence and a positive joint residual
mass do not alone give a strict gap.

## Verification

Compilation succeeded:

    lake env lean -o .lake/build/lib/lean/Submission/PositivityCorrelationModel.olean \
      Submission/PositivityCorrelationModel.lean

Axiom audits for `finite_positivity_obstruction`,
`nonlinear_covariances_zero`, and `profile_eq_on_positive_source` print only
`propext`, `Classical.choice`, and `Quot.sound`.

## Remaining task

A sufficient bound for the actual signed correlation, exploiting information
not contained in these profile identities, or an actual irrational
counterexample is still required. No incomplete proof was submitted.
