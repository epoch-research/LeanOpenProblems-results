# Full two-scale window criterion — conjecture still unresolved

`Submission/Spec.lean` is unchanged and retains the original `sorry`.
This continuation supplies no proof of the conjecture or irrational
counterexample, and no incomplete proof was submitted.

## New verified file

`Submission/FullPairWindowCriterion.lean`
Namespace `Erdos972FullPairWindowCriterion`.

Write g(N)=floor(alpha*N), P(t,alpha,N)=pairMinorantSum(t,alpha,N),
and M(t)=pairMean(t). The validity window is

    t>0, t*log(g(N))<=1/4.

1. `window_uniform_mean_lower`:
   For alpha>=1 and every c<32/63, eventually every t in the validity
   window satisfies M(t)>c. This is uniform over the entire window, not
   merely a statement for a previously chosen parameter sequence. It
   concerns the scalar mean, not the actual correlation.

2. `finite_pairs_uniform_window_gap`:
   If the genuine prime-pair set at alpha>=1 is finite, then for every
   c<32/63, eventually every t in the validity window satisfies

       c*N < N*M(t)-P(t,alpha,N).

   This is an actual one-sided defect bound for the FULL pair minorant.
   Finiteness is essential to the proof: it supplies the o(N) Mangoldt
   correlation bound, while P is at most that correlation in the window.
   Unlike the earlier composite-only obstruction, this theorem does not
   assert an unconditional gap for the full sum.

3. `infinite_of_frequently_small_window_defect`:
   An upper defect bound

       N*M(t)-P(t,alpha,N) <= c*N,  c<32/63,

   at arbitrarily large cutoffs with some valid positive t at each cutoff
   implies genuine prime-pair infinitude. A full moving-parameter
   asymptotic is unnecessary. The upper defect estimate is an explicit
   UNPROVED hypothesis, not a consequence of the fixed-parameter mean.

4. `infinite_of_frequently_small_window_error`:
   The analogous absolute-error upper bound is also sufficient.

5. `prime_pair_beyond_of_minorant`:
   At a single positive valid cutoff, the finite certificate

       primePowerBudget(alpha,N)+primeCorrelation(alpha,B)
           < P(t,alpha,N)

   supplies a genuine prime pair with B<p<=N.

All five principal declarations compile and audit with only `propext`,
`Classical.choice`, and `Quot.sound`. The new Lean file contains no `sorry`.

## Remaining mathematical gap

No sufficient one-sided defect bound, positive full-window minorant lower
bound, signed four-factor lower gap, or irrational counterexample was
obtained. These new implications clarify the missing estimate; they do not
establish it. The target file has not been modified.
