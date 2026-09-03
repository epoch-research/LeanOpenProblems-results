# Translate-averaged radix lifts with actual carries

The original conjecture in `Spec.lean` remains unresolved. These are finite
cyclic results, not an infinite natural-number construction.

Production files (compiled, with current oleans):

* `TranslatedRadixCarryExplore.lean`
* `PatchedTranslatedRadixExplore.lean`
* `LogarithmicTranslatedRadixExplore.lean`

`TranslatedRadixAudit.lean` audits fourteen declarations; the saved log
reports only propext, Classical.choice and Quot.sound.

For the encoding `(a,z) -> a.val + L*z.val` modulo LM, the exact mixed
representation formula retains the low-digit borrow in the fine target:

    r_encoded(encode(t,s))
      = sum_{x in A, t-x in B} r_(P,Q)(s-borrow(t,x)).

Thus entrywise fine count error E gives error at most E*r_(A,B)(t).
Disjoint fine colors allow exact summation over every old color pair.
Taking ALL translates of the old set A gives the constant total weight
D=L*|A|^2 at every low target. If the fine counts are within delta*mu of mu,
then every actual cyclic count is within delta*mu*D of mu*D.

Replacing the initial block by A costs at most 2L in any cyclic count.
The patched set agrees with every old natural bit below L. All nonzero
high rows are unchanged. If A is nonempty and each fine color has a
nonzero point, every old residue is attained outside the retained prefix.

The logarithmically tuned endpoint constructs arbitrarily large M and
B modulo LM, preserving an arbitrary nonempty old prefix, with full
old-residue projection outside that prefix, and

    |r_B(z)/log(LM)-c| < epsilon

at every CYCLIC target z. Carries are controlled directly, rather than
inferring radix flatness from a product-group count. This still does not
control all ordinary natural targets or supply a compatible infinite chain.

## Entrywise-palette scale cost

`TranslatedRadixScaleCostExplore.lean` now compiles and has a current olean.
Its four lemmas are audited in `TranslatedRadixScaleCostAudit.lean`; only the
three permitted axioms occur.

If mu>0, delta<=1/2, and an integer fine count k satisfies

    |k-mu| <= delta*mu,

then k is positive, so k>=1 and mu>=2/3. Consequently the patched radix
construction above satisfies at every cyclic target

    r_patched >= L*|A|^2/3 - 2L.

A cap r_patched <= C log(LM) therefore forces

    L*|A|^2 <= 3C log(LM) + 6L.

For |A|>=3 and C>0 this implies

    exp(L/C) <= LM.

This is an explicit restriction on the ENTRYWISE-FLAT all-translates lift.
It does not constrain arbitrary sets or more general aggregate-kernel lifts.
In particular it cannot be used as a disproof of the conjecture.

## Whole-row cardinality obstruction

`TranslatedRadixRowMassExplore.lean` compiles without warnings and has a
current olean. `TranslatedRadixRowMassAudit.lean` audits ten declarations;
the saved log uses only the three permitted axioms.

The zero row is exactly A. Every nonzero row of the patched lift is either
empty or one translate of A, since the fine palettes are pairwise disjoint.
Consequently, for M>1, its periodic natural realization S satisfies

    count(S,L)=|A|,
    count(S,2L) in {|A|,2|A|}.

The same dichotomy holds for ANY natural set agreeing with this realization
below 2L. On the other hand, any hypothetical witness has, eventually,

    count(S,L) < count(S,2L) < 2 count(S,L),

by the already checked counting-ratio limit sqrt(2). The new theorem
`no_log_limit_of_frequent_row_mass_dichotomy` therefore rules out any set
with this dichotomy at unbounded cutoffs. This permits translations and
arbitrary rearrangements within a row: its cardinality, not literal copying
of individual positions, is decisive.

This rules out literal prefix-preserving iteration of the complete/empty
translated rows, independently of the entrywise-palette scale cost. A new
variant must allow genuinely different row sizes (for example thinning).
It is NOT a universal disproof of the original conjecture.

## Further review, not a new theorem

The existing full quadratic-root count factors into a signed parameter
convolution, making its complete-target error uniformly small. Restricting
a root to a spatial interval also depends on its location

    x = (u*t + y)/(u+v),  y^2=u*v*((u+v)*s-t^2).

That dependence is not constant on the parameter-sum fibers. The existing
signed-fiber L1 bound therefore does not control it. Adding a Fourier
expansion of the interval does not by itself supply a uniform error bound
independent of the field size. No such missing bound was proved in this
review. Thus the tapered faithful lift still lacks the required ordinary
transition-window estimates, and Spec.lean remains unresolved.
