# Status: conjecture not settled

`Spec.lean` is unchanged. Both admissions remain. No proof or disproof has been submitted.

## Verified Lean results

The development files are independent of the admitted original theorem:

- `Work.lean`: restriction/padding lemmas, triple-counting bounds, boundedness of the critical ratio, and characterization of a nonzero liminf by an eventual positive lower bound.
- `Flags.lean`: compactness equivalence between cubic-bounded restricted-B3 sequences of every finite length and an infinite such sequence.
- `FlagReduction.lean`: exact equivalence of the original assertion with
  ```lean
  ∀ K : ℕ, ∃ n : ℕ, ¬ Work.FiniteCubicFlag K n
  ```
  Its negation is equivalent to
  ```lean
  ∃ K : ℕ, ∀ n : ℕ, Work.FiniteCubicFlag K n
  ```
  **Neither of these alternatives has been proved.**
- `FlagExamples.lean`: an explicit length-10 flag and counterexamples to proposed stronger pair-difference exclusions.
- `ExtensionObstruction.lean`: the four-point padding obstruction.
- `BalancedDeadEnd.lean`: an explicit 18-point flag with constant 1 and no one-point extension preserving that constant. Every candidate from 5420 through 6859 is blocked by a kernel-checked triple-sum equality. This is a particular dead end, not extinction of all flags.

These results were compiled and their axioms checked; only `propext`, `Classical.choice`, and `Quot.sound` occur.

## Important scope limitations

The specification uses three-element finite subsets, not multisets. A finite dense construction or positive critical limsup does not establish the positive liminf needed for a disproof. Existence of flags with a constant depending on their length does not provide one fixed constant for all lengths.

The checked dead-end examples refute extension of arbitrary parents. They do not refute existence of other parents, a selected extendible class, or the original conjecture.

The source audits did not supply a result settling the exact assertion. In particular, exclusion of a regular asymptotic counting function does not exclude an oscillating positive liminf. The singular-spectrum moment-rigidity route remains unproved; standard Foias-Stratila hypotheses were not established. Bounded-representation constructions found in the sources have strictly subcritical exponents for fixed multiplicity, and bounded multiplicity alone does not imply density-preserving restricted-B3 extraction.

## Rechecking

From `/workspace/leanproject`, after the development dependencies have been built:

```sh
lake env lean Submission/BalancedDeadEnd.lean
lake env lean Submission/FlagReduction.lean
lake env lean Submission/Spec.lean
```

The last command still reports **two admitted declarations**; this is not a successful submission.

Unchanged `Spec.lean` SHA-256:
`fef4e36b8c1e956c193b1a98c325fab7317d26d3ddbe63fb37991f589df65d71`.
