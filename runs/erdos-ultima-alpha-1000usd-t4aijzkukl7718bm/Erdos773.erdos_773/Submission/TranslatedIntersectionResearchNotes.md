# Translated-intersection selection and a conditional upper-bound transfer

This continuation does NOT settle Erdős 773. Spec.lean is unchanged and its
sole admission remains at line 2031, for 0 < epsilon <= 1/3. No proof or
disproof has been submitted.

## New verified module

`TranslatedIntersectionSelection.lean` imports only FormalConjecturesUtil.
It compiles without errors, warnings, or admissions, and its built olean is
present. All six printed main axiom checks use only propext, Classical.choice,
and Quot.sound. Log: `/tmp/translated-intersection-selection.log`.

For A subset [1,N], define

    overlap(A,h) = {a in A : a+h in A}.

The module proves:

1. If every positive h<=N has overlap cardinality at most K, then

       |A| (|A|-1) <= 2 N K.

   Count increasing ordered pairs in A, partition by positive difference h,
   and inject each fiber into overlap(A,h). The two orientations cover all
   off-diagonal ordered pairs.

2. For N>0, some h in [1,N] has

       |A| (|A|-1) <= 2 N |overlap(A,h)|.

3. If the squares of A are Sidon, there are h in [1,N] and B such that

       B union (B+h) subset A,
       |A| (|A|-1) <= 2 N |B|,
       the squares of B union (B+h) are Sidon.

   Public theorem: `extract_sidon_union`.
   The weaker conclusion asserting Sidonness of each copy separately is
   also available as `extract_two_shifts`. Separate Sidonness is NOT used
   to infer Sidonness of the union; the latter follows from containment in A.

4. `uniform_union_bound_transfers` proves a conditional transfer: a uniform
   upper bound K on B for EVERY h in [1,N], with B union (B+h) inside [1,N]
   and Sidon in squares, implies |A|(|A|-1)<=2NK for every original Sidon-root
   set A. The analogous, stronger hypothesis requiring only separate
   Sidonness is handled by `uniform_two_shift_bound_transfers`.

## Scope and missing step

The shift h is selected existentially. It is not prescribed in advance.
The result does not provide one B that works for all shifts or affine maps.
Consequently it does not discharge the hypothesis of
UniversalAffineSidonBound.universal_affine_bound.

A uniform bound |B|<=C N^alpha for these Sidon unions, with fixed alpha<1,
would yield an original bound |A|=O(N^((1+alpha)/2)) and disprove the
conjecture. This exponent consequence is ordinary algebraic interpretation
of the verified finite inequality, not a newly proved upper estimate on B.
No such uniform upper bound on B has been obtained.

## Review of upper-bound iteration

The existing scalar modular cardinality inequalities were rechecked. Their
joint compatibility with near-linear integer cardinalities is already
proved in QuadraticResidueDensityLower. Repeating or optimizing these same
inequalities does not establish a fixed-power disproof. The new reduction
retains an actual translated-intersection set, rather than just its scalar
cardinality, but this additional structure has not yet yielded the missing
uniform union bound.

No actual lower or upper exponent for the original conjecture improved.
Spec.lean SHA-256 remains:
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.
