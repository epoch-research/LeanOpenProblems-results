# Batched profile amplification and isolated annular packets

## Original task status

Erdős 66 is still unresolved in this work. `Submission/Spec.lean` remains
unchanged, with its original `sorry`. No proof or disproof was submitted.

## Checked finite amplification

`TemplatePacketExplore.lean` defines

    tensor M P S = {p*M+s : p in P, s in S}.

If all low sums s+t are below M, it proves the exact identity

    r_tensor(q*M+t) = r_P(q)*r_S(t),  0<=t<M,

and cardinality |tensor|=|P|*|S|. There is no carry term under this hypothesis.

`exists_coarse_packet` extracts a Sidon F of size m from [0,m^4+1), and takes
P=F union (2(m^4+1)-F). Then

- |P|=2m;
- every point of P is at most C=2(m^4+1);
- r_P(C)=2m;
- r_P(q)<=6 for q!=C.

`exists_amplified_template` applies this with M=2W, S contained in [0,W):

- D has exactly 2m|S| points and lies below (C+1)2W;
- r_D(C*2W+t)=2m*r_S(t) for every t<2W;
- outside the coarse block with quotient C, r_D(n)<=6U if r_S<=U globally.

This amplifies an entire representation profile rather than one target.

## Checked logarithmic packet

`IsolatedAnnularPacketExplore.lean` combines the exact amplification with
`exists_upper_logarithmic_annulus`.

For c,epsilon>0 and R>=1 it selects m>=4 BEFORE any support lower bound N0.
Then it finds N>=N0 and a finite D supported above N0 such that, with

    M=2(RN+1), C=2(m^4+1),

- r_D(n)/log n < c+epsilon at every n;
- r_D(n)/log n < epsilon whenever floor(n/M)!=C;
- |r_D(CM+t)/log(CM+t)-c| < epsilon for N<=t<=RN.

For R>1 the accurate interval has positive length. Its fractional width is
fixed once m and R are chosen, not once N0 is chosen. The theorem does not
claim accuracy on the whole central block [CM,(C+1)M).

The low template has coefficient c/(2m); amplification restores c, while
the off-center factor remains at most six. Logarithms at t and CM+t are
uniformly equivalent on the stated interval as N grows.

All production files compile with built oleans. Principal statements pass
`TemplatePacketAxiomCheck.lean` and `IsolatedAnnularPacketAxiomCheck.lean`,
using only propext, Classical.choice, and Quot.sound.

## Mixed-count limitation

These are SELF-count statements. They do not show that D can be adjoined to
an arbitrary old set with negligible collateral. A reflected copy of the
low template in the old set can meet a translated copy in D in |S| points,
creating a large mixed representation peak even when the old template's
self-counts are small. Translating the same template does not remove this
issue: it merely translates the mixed peak.

The observation about reflected copies is a mathematical diagnostic here,
not a separately formalized universal mixed-count obstruction in these files.

A useful batched completion theorem would still need a suitable base and a
uniform estimate for its mixed counts with the selected templates. None has
been supplied. Nor do the isolated packets cover all sufficiently large
targets: their annuli remain separately selected, with uncontrolled gaps.
