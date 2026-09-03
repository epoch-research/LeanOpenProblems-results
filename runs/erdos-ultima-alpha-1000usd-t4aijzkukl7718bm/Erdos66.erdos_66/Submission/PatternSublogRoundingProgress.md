# Countable sublogarithmic pattern rounding

The original conjecture remains unresolved; Spec.lean is unchanged.

Four production files compile and have current oleans:

* LogProfileLowerExplore.lean
* PurePatternBracketRoundingExplore.lean
* PatternSublogRoundingExplore.lean
* MatchingPatternSublogExplore.lean

PatternSublogRoundingAudit.lean audits their 12 theorem/lemma declarations;
all use only propext, Classical.choice, and Quot.sound.

The pure pattern compactness theorem retains all exact prefix brackets
without requiring a nonzero representation-cost coefficient. The supported
sublogarithmic theorem handles one countable family of exponential patterns
and forbids every zero-probability site. For disjoint-coordinate patterns
with coefficients in [1,2], a fractional mean o(log n) suffices to obtain a
single Boolean set whose pattern values are o(log n).

The mean estimate is an explicit hypothesis in these abstract theorems.
Its actual insertion-pattern instantiation and its proof for sparse rank
rows have now been completed. See SimultaneousRankRestorationProgress.md.
That continuation does not settle the original existential conjecture.
