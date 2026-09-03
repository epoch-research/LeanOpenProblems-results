# Finite logarithmic annuli

`Spec.lean` remains unchanged and unproved/undisproved.

Completed and compiled (all main results axiom-checked):

- `ConstantProfileExplore.lean`: central-binomial profile b, b*b=1,
  decreasing and tending to zero, partial-sum identity, square bound.
- `FiniteTaperExplore.lean`: floor levels H*b(k), error bounds for their
  convolution, transfer via mixed-flat cyclic blocks to finite integer sets.
  Its existential selects the prime p BEFORE the arbitrary thickness K.
- `LogTuningExplore.lean`: with K=floor(sqrt(log(p)/d)), the constant
  2*d*K^2 approximates log(n) uniformly on any fixed multiplicative interval
  [(pK)^2, (L+1)(pK)^2], as p tends to infinity.
- `AnnulusExplore.lean`: for every epsilon>0, R>=1, and N0, there are N>=N0
  and a finite A such that |r_A(n)/log(n)-1|<epsilon for N<=n<=R*N.
- `AnnulusExtensionExplore.lean`: the same conclusion with any prescribed
  finite prefix. Changing membership below L changes representation counts
  by at most 2L, which becomes negligible once log(n) is sufficiently large.

The annulus theorem is a finite INTEGER result, not just a cyclic result.
However, it does not provide a single set with the requested limit. The
starting threshold N depends on the chosen interval length, accuracy, and
prefix; there is no control of the gap between the prefix and the new annulus.
The compactness criterion needs a single threshold function fixed before all
finite cutoffs. This has not been established.

New good annuli can be inserted arbitrarily late without changing earlier
membership, but this by itself cannot exclude infinitely many bad gaps.

## Quantifier-gap diagnostic completed

`AnnulusBaireExplore.lean` proves that the annulus conditions and arbitrarily
late representation holes hold simultaneously for a dense set of Boolean
sequences (a Baire-category argument using prescribed-prefix extensions).
In particular, `exists_annular_nonconvergent` gives a SINGLE A with good
annuli at every prescribed accuracy, length, and lower bound, but with no
limit at any real constant. This is NOT a disproof of the conjecture: it
only shows that this annular property does not imply the requested limit.
All three main Baire results were checked in `AnnulusBaireAxiomCheck.lean`
and use only the permitted axioms.

Further scale-compatibility ideas considered, not established:
- Replacing prime fields by product rings introduces extra singular targets
  and a growing number of character terms.
- Tensoring finite flat sets multiplies representation means and retains
  early residue biases; simply nesting restrictions cannot yield a witness.
- Adding a new tensor factor while it is initially unrestricted does not
  automatically control the integer prefix before its full period.
None of these ideas has supplied a transition lemma.
