# Fixed-dimensional ordered-digit moment obstruction

The original Erdős 773 conjecture remains UNSETTLED. Spec.lean was not edited
and its sole admission remains at line 2035. This is a construction-specific
obstruction, not a disproof of the original proposition.

## Verified module

Submission/TensorMonotoneMomentCollision.lean imports only
FormalConjecturesUtil. It compiles without warnings or admissions, has a built
olean, and all five printed audits use only propext, Classical.choice,
Quot.sound. Log: /tmp/tensor-monotone-moment.log.

Namespace: Erdos773.TensorMonotoneMomentCollision.

For every radix B >= 40000, the following four words (low digits first) are
canonical, positive, strictly increasing digit vectors:

  [10199,10912,12219,20002,21376,23962,30399,32512,36419]
  [9799,11092,11779,20002,22616,24042,29599,33492,35579]
  [10001,10688,11981,20398,21824,24438,30201,32288,36181]
  [10001,11308,12021,19598,22184,23558,29801,33708,35821]

Each has digit sum 198000 and squared-digit sum 5111059036. Their four roots
are distinct, positive, and below B^9. Their squares satisfy

  root(B,0)^2 + root(B,1)^2 = root(B,2)^2 + root(B,3)^2.

The public theorem not_sidon proves non-Sidonness of the four actual square
values at every such B. Thus the obstruction holds with FIXED dimension nine
as the radix tends to infinity, unlike the earlier counting-based growing-
dimension obstruction.

## Algebraic source

For arbitrary a,f,d,g in a commutative ring, tensor_identity proves

 ((a+f)d+(a-f)g)^2 + ((a-f)d-(a+f)g)^2
   = ((a+f)d-(a-f)g)^2 + ((a-f)d+(a+f)g)^2.

Use coefficient vectors a=(100,110,120), f=(1,-2,1), d=(100,200,300),
g=(1,-2,1), with the d and g coordinates placed at exponents 0,3,6.
The relations sum(f)=sum(g)=a dot f=d dot g=0 give the common moments.
The large positive linear backgrounds make all four digit vectors strictly
increasing. The concrete identity is independently checked by ring in Lean;
no exploratory computation is trusted as a proof.

This is a FORMAL polynomial norm identity, not a nonzero polynomial that
vanishes only at one integer radix. Consequently it does not refute the
Gaussian-Eisenstein formal Sidon theorem: these words do not have its monic
leading digit and prescribed constant/low-coefficient conditions. The four
histograms are not equal. Strictly increasing words with the same histogram
would of course be identical.

## Scope

This rules out a blanket sufficient condition using only strict digit order
and common first and second digit moments. It does not rule out selecting a
special moment class or a large Sidon subclass. It gives no new unrestricted
Sidon lower exponent or fixed-power upper bound. The original epsilon gap
0<epsilon<1/3 remains, and the separately verified endpoint has not been
reconsolidated into the current smaller Spec.lean.

The endpoint/amplification review preceding this work found no overlooked
unconditional recurrence. Subpower amplification remains an equivalence,
not an independently proved hypothesis. No incomplete proof was submitted.

Spec.lean SHA-256:
f019ff3791c89bbea24fd9b031eb92f7b676baa4b1ff9cebe9f2356121aa6ff0
