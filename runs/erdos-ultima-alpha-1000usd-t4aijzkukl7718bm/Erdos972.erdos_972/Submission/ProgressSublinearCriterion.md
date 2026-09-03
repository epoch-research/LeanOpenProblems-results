# Weaker correlation certificates — conjecture still unresolved

`Spec.lean` is unchanged and still contains the original `sorry`.
No correlation lower bound or irrational counterexample has been proved.

## New file: SublinearCorrelationCriterion.lean

Namespace `Erdos972SublinearCorrelationCriterion`.

- `primeCorrelation_le_of_no_new_pairs`: if no pair occurs beyond B up to N,
  the prime correlation at N is at most its value at B.
- `prime_pair_beyond_of_correlation`: a finite certificate
  ```
  primePowerBudget alpha N + primeCorrelation alpha B
    < mangoldtCorrelation alpha N
  ```
  gives an input prime p in (B,N] with prime output.
- `primeCorrelation_explicit_upper`:
  ```
  primeCorrelation alpha B <= B * log B * log(alpha*B).
  ```
- `prime_pair_beyond_of_explicit_correlation`: the corresponding certificate
  using this explicit cutoff bound instead of the lower prime-pair sum.
- `infinite_primeSet_of_unbounded_excess`: unbounded excess of Mangoldt
  correlation over the explicit prime-power envelope suffices for infinitude.
- `finite_primeSet_bounds_excess`: a finite prime-pair set bounds that excess
  uniformly at all positive scales.
- `primePowerBudget_div_rpow_tendsto`: for every s>1/2 the prime-power budget
  divided by N^s tends to zero.
- `finite_primeSet_correlation_div_rpow_tendsto_zero`: a finite prime-pair set
  forces Mangoldt correlation to be o(N^s) for every s>1/2.
- `infinite_primeSet_of_frequently_rpow_lower`: if c>0, s>1/2, and
  ```
  c*N^s <= mangoldtCorrelation alpha N
  ```
  at arbitrarily large scales, the prime-pair set is infinite.

All the sufficient lower bounds above are EXPLICIT HYPOTHESES, not estimates
proved here. In particular, no N^s lower bound for a general fixed irrational
slope has been supplied. These certificates do not settle the original theorem.

The sharper budget used throughout is the existing bound
```
(log 4 + 12) * (log(alpha*N)*sqrt N + log N*sqrt(alpha*N)).
```

## Other investigation in this phase

Revisited finite counterexample constructions near rational slopes and a
possible factorization descent for slopes between one and two. No contradiction
or irrational construction resulted. Finite prime-free intervals near an integer
may converge only to that excluded rational slope; this does not provide a
counterexample. No change to the original conjecture or imports was made.
