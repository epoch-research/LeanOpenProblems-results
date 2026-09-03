# Finite-state digit obstruction

The original conjecture is still unresolved. Spec.lean is unchanged.

## New compiled result

`Erdos66DfaCounting.no_nonzero_log_limit` in DfaCountingExplore.lean
rules out a nonzero finite logarithmic representation limit for any set A
recognized by a finite DFA in any integer base b >= 2. Recognition is
formulated for every finite digit word (including zero-padded words), with
least-significant-digit-first encoding `Nat.ofDigits`.

This does NOT rule out arbitrary sets of naturals.

## Proof

1. DigitLoopPeakExplore.lean: two distinct equal-length digit blocks which
   may be freely concatenated in a common context give a binary cube. The
   complementary words produce at least 2^k representations at a target
   bounded by D*B^k. This is incompatible with any finite logarithmic limit.
2. DfaLoopCodeExplore.lean: therefore productive states in a digit automaton
   recognizing a candidate must have unique loops of each fixed length.
   The last visit time and exit letter at each state injectively encode
   each accepted word. For S states, length-k words number at most
   ((k+1)*(b+1))^S.
3. DfaCountingExplore.lean: padded digit expansions transfer this bound to
   |A intersect [0,b^k)|. A nonzero logarithmic limit makes A an eventual
   additive basis; summing representation counts gives
   b^k <= M + |A intersect [0,b^k)|^2. Exponential growth contradicts the
   polynomial bound above.

DfaObstructionAxiomCheck.lean audits the principal results: only propext,
Classical.choice, and Quot.sound occur. All three oleans have been built.

## Consequence for further construction work

Any digit-based witness would need genuinely unbounded memory or a
nonstationary mechanism avoiding repeatable branching loops. The result
supplies neither such a mechanism nor a universal obstruction.
