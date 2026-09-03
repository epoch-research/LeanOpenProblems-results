# Shifted taper and upper-envelope progress

The conjecture in `Spec.lean` remains unchanged, unproved, and undisproved.

## New checked pipeline

1. `UniformCyclicFamilyExplore.lean`: a prime can be chosen before the
   thickening parameter K, with one nested cyclic family and simultaneous
   mixed-count bounds for all indices up to T^2.
2. `ShiftedProfileExplore.lean`: shifting the binomial profile by s gives
   convolution between `1-2*s*b(q)` and 1, and an endpoint bounded by b(s)^2.
3. `ShiftedBlockExplore.lean`: corresponding integer-block upper/lower bounds,
   including the zeroth block and a uniform endpoint error.
4. `ShiftedFiniteExplore.lean`: finite truncated blocks have a constant
   global upper bound, as well as two-sided estimates on the useful range.
5. `TranslateExplore.lean`: exact translation formulas for sumRep, including
   vanishing below twice the translation.
6. `ShiftedUpperAnnulusExplore.lean`: for all c>0, epsilon>0, R>=1 and N0,
   there are N>=N0 and finite A supported above N0 such that
      r_A(n)/log(n) < c+epsilon          for every n,
      |r_A(n)/log(n)-c| < epsilon       for N<=n<=R*N.
7. `UpperExtensionExplore.lean`: if finite B already satisfies the global
   upper envelope `r_B(n)/log(n)<=c`, with c>0, it has finite supersets
   preserving any prescribed finite prefix, maintaining that exact global
   envelope, and attaining every requested accuracy on arbitrarily late
   multiplicative annuli.

All files compile and oleans were built. `ShiftedUpperAxiomCheck.lean`
and `UpperExtensionAxiomCheck.lean` show that the main theorems use only
propext, Classical.choice, and Quot.sound.

## Parameters of the upper-annulus proof

- delta=min(epsilon/(8*(c+1)),1/8).
- Choose s with b(s)^2<delta/4, then q0>=1 with 2*s*b(q0)<delta/4.
- L=R*(q0+2).
- T is large enough that T>=1, T^2*b(L+s)>=1, and
  `64*(2*L+4)<delta*T`.
- d=2*T^4/c; choose a sufficiently late admissible prime p.
- K=floor(sqrt(log(p)/d)), M=(p*K)^2, mu=4*K^2*T^4.
- Translate the finite shifted-profile block set by M.
- Its nonzero representations are supported between 2*M and (2*L+4)*M,
  where logarithmic tuning is uniform.
- N=(q0+2)*M is the starting point of the useful annulus.

## Remaining obstruction

The global *upper* estimate does not supply a lower estimate in the gaps.
Finite sets satisfying an upper envelope can always be truncated, leaving
arbitrarily late holes. The new prefix-extension theorem permits successive
good annuli but does not cover all sufficiently large targets.

Specifically, neither the common-period construction nor the new upper
extension gives controlled mixed representations across a transition to an
unrelated period while keeping the previous lower bounds. The compactness
criterion still needs one complete threshold function before the finite
cutoff is chosen.

## The upper envelope does not close the gap (now proved)

`UpperBaireExplore.lean` was subsequently completed and built. For every c>0,
`exists_upper_annuli_and_holes` constructs ONE infinite set A with:

- r_A(n)/log(n)<=c at every n;
- arbitrarily late, arbitrarily long multiplicative annuli of arbitrary
  two-sided accuracy to c;
- arbitrarily late n with r_A(n)=0.

The proof works in the closed compact subspace of Bool sequences satisfying
that upper envelope. Prefix-extension annuli are open dense there, and
representation holes are also open dense by truncation. Baire's theorem
realizes both families of conditions simultaneously.

`UpperBaireAxiomCheck.lean` verifies only the permitted axioms occur.
This result is NOT a disproof of Erdos 66: it concerns a constructed set,
not every candidate set. It shows precisely why the current construction,
even with a global upper bound, is insufficient to establish convergence.

The wrapper `exists_upper_annular_nonconvergent` also proves that these
constructed upper-bounded sets have no limit at ANY real constant. Its axiom
check passes. Its quantifier is existential in A, and it is therefore not the
negation of the original existential conjecture.
