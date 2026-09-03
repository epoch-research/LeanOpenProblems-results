# Row-dependent faithful lifts: exact formulas and remaining gap

## Original conjecture status

Erdos66.erdos_66 remains unproved and undisproved. Submission/Spec.lean is
unchanged with its original import, statement, and sorry. No proof has
been submitted.

## Verified production files

* TaperedFaithfulLiftExplore.lean
* TaperedRowAverageExplore.lean
* TaperedNaturalMassExplore.lean
* SupportSensitiveFaithfulLiftExplore.lean

All four compile and have current oleans. TaperedLiftAudit.lean checks fifteen
principal declarations; TaperedLiftAudit.log reports only propext,
Classical.choice, and Quot.sound. No production sorries or new axioms occur.

## Exact membership and first row

Write row(U,a,y) for the horizontal row of faithfulLift(U,a), and assume
all a+u are nonzero for u in U. Then:

    x in row(U,a,y)
      iff x+a != 0,
          y+x+a != 0,
          (x+a)^2/(y+x+a)-a belongs to U.

Equivalently, x+a != 0 and there is u in U with

    (x+a)^2 = (y+x+a)(a+u).

This proves row(U,a,0)=U, including U empty. For arbitrary row-dependent
parameters U(y), define tapered(U,a) to use row(U(y),a,y) in each row.
Its first row is exactly U(0); no monotonicity hypothesis is needed.

## Exact natural carry formula

Encode the plane by x.val+p*y.val, and set C(k) equal to the kth tapered row
for k<p and empty otherwise. The encoded set equals blockSet(p,C), exactly.
For every q,t with t<p its representation count at qp+t is

    sum_(k<=q) lower(C(k),C(q-k),t)
      + sum_(k<q) upper(C(k),C(q-k-1),t).

Both the natural carry and the endpoint restriction are retained. The
formula does not replace these terms with complete field-plane counts.
Membership at every natural n<p agrees exactly with U(0).

## Exact first moment of row mass

safeRow is defined by the three membership conditions above even when a
zero parameter is present, and agrees with row at admissible translations.
The map

    (u,z) -> (a=z^2/(y+z)-u, x=z-a)

is a permutation of the full field plane, with inverse

    (a,x) -> ((x+a)^2/(y+x+a)-a, x+a).

Removing z=0 and z=-y therefore proves

    sum_a |safeRow(U,a,y)| = |U| (|F|-1)  if y=0,
                            |U| (|F|-2)  if y!=0.

These are sums over ALL translations, not conditional averages over the
admissible translations. The safe exclusion of zero parameters is essential.

The same identity gives the exact average of ordinary prefix counts of the
safe natural block set:

    sum_a count(A_a,Np)
      = sum_(k<N) |U_k| (p - [1 if k mod p=0, otherwise 2]).

This is a first-moment cardinality identity, not a concentration estimate
and not a representation-count identity.

## Parameter nesting is not spatial-row nesting

A checked example in F_5 uses the constant parameter set {1} and a=0.
The first row is {1}, whereas 3 belongs to row 1 and not row 0. Thus even
constant parameters do not make the rows antitone. The monotone-block
bracketing theorem cannot be applied merely from nesting of U(y).

## Support-sensitive complete-lift estimate

If U+U is contained in a finite S, the former full-field support factor can
be replaced by |S|. For h=|U|, 2h<|F|, and U nonempty, one admissible
translation a has the exact old first row and, at every nonexceptional
field-plane target,

    |r_faithfulLift(z)-h^2| <= sqrt(8|S|h^2)+3h+2.

The exceptional target is explicitly excluded after undoing the shear and
translation. This theorem is about the COMPLETE lift, not the tapered one.
Its proof combines the existing arbitrary-set translation energy selector
with the existing support-sensitive L1 character-fiber estimate.

## Mathematical review, not additional Lean claims

For old prefixes with count(A,L)^2 comparable to L log L, a prefix with h
points has sum support of size at most twice its cutoff. Consequently the
complete-lift relative error from the preceding estimate can shrink like
1/sqrt(log L). This is why using progressively shorter old prefixes is more
promising than selecting arbitrary thinnings of a large old parameter set.

However, the natural formula requires mixed counts of rows at different
heights, each with its own parameter prefix. Restricting the roots by their
spatial rows is not covered by complete quadratic-root counting. The
existing outer-repetition prefix balancing also does not preserve the
faithful first-row layout needed here. Neither the average row mass nor
parameter nesting supplies the missing restricted-root estimate.

No uniform sublogarithmic bound for these natural carry sums, changing-scale
compatible chain, or universal contradiction has been proved. This work
therefore does not settle the original conjecture.
