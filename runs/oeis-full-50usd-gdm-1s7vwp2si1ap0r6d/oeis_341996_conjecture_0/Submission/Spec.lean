import FormalConjectures.Util.ProblemImports

open Nat Finset

/-- The arithmetic derivative $D(n)$, A003415 in OEIS.
$D(0) = 0$, $D(1) = 0$.
For $n > 1$ with prime factorization $n = \prod p_i^{e_i}$,
$D(n) = \sum_{i} e_i \cdot \frac{n}{p_i}$.
-/
def arithmetic_derivative (n : ℕ) : ℕ :=
  if n ≤ 1 then 0
  else
    (n.primeFactors).sum fun p =>
      (n.factorization p) * (n / p)

/--
A341996: $a(n) = 1$ if there is at least one such prime $p$ that $p^p$ divides the arithmetic derivative of $n$, $\text{A003415}(n)$; $a(0) = a(1) = 0$ by convention.
-/
def A341996 (n : ℕ) : ℕ :=
  if n ≤ 1 then 0
  else
    let d := arithmetic_derivative n
    -- We only need to check primes $p \le d+1$, since $p^p$ grows very fast.
    -- Using `range (d + 1)` is a heuristic upper bound for primes to check.
    let primes_to_check := (range (d + 2)).filter Nat.Prime -- checking up to d+1 (since p <= d+1 implies p <= d or p=d+1)

    -- Check for existence by filtering the set of primes and checking for non-emptiness.
    if (primes_to_check.filter fun p => (p ^ p) ∣ d).Nonempty then 1 else 0


open Set Filter

theorem hasDensity_squeeze {S A B : Set ℕ} {c : ℝ}
    (hA : A.HasDensity c) (hB : B.HasDensity c) (h1 : A ⊆ S) (h2 : S ⊆ B) :
    S.HasDensity c := by
  rw [HasDensity] at hA hB ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hA hB ?_ ?_
  · intro b
    unfold partialDensity
    simp only [Set.univ_inter, Set.inter_univ]
    by_cases hb : ((Set.Iio b).ncard : ℝ) = 0
    · rw [hb]
      simp
    · apply div_le_div_of_nonneg_right
      · exact mod_cast Set.ncard_le_ncard (Set.inter_subset_inter_left (Set.Iio b) h1)
      · exact Nat.cast_nonneg _
  · intro b
    unfold partialDensity
    simp only [Set.univ_inter, Set.inter_univ]
    by_cases hb : ((Set.Iio b).ncard : ℝ) = 0
    · rw [hb]
      simp
    · apply div_le_div_of_nonneg_right
      · exact mod_cast Set.ncard_le_ncard (Set.inter_subset_inter_left (Set.Iio b) h2)
      · exact Nat.cast_nonneg _


theorem partialDensity_nonneg (S : Set ℕ) (b : ℕ) : 0 ≤ S.partialDensity Set.univ b := by
  unfold partialDensity
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem bounded_le_partialDensity (S : Set ℕ) :
    IsBoundedUnder (· ≤ ·) (atTop (α := ℕ)) (fun b => S.partialDensity Set.univ b) := by
  use 1
  rw [eventually_map]
  filter_upwards [] with b
  exact Set.partialDensity_le_one S Set.univ b

theorem bounded_ge_partialDensity (S : Set ℕ) :
    IsBoundedUnder (· ≥ ·) (atTop (α := ℕ)) (fun b => S.partialDensity Set.univ b) := by
  use 0
  rw [eventually_map]
  filter_upwards [] with b
  exact partialDensity_nonneg S b

theorem hasDensity_of_equal_densities (S : Set ℕ) (h : lowerDensity S = upperDensity S) :
    S.HasDensity (lowerDensity S) := by
  unfold HasDensity lowerDensity upperDensity at *
  refine tendsto_of_liminf_eq_limsup rfl h.symm (bounded_le_partialDensity S) (bounded_ge_partialDensity S)

/--
Conjecture (OEIS A341996 Question): What is the asymptotic mean of this sequence and its complement A368915?
This formalizes the belief that the natural density (asymptotic mean) of the set of numbers $n$ for which $A341996(n)=1$ exists.
-/
theorem oeis_341996_conjecture_0 :
  ∃ c : ℝ, ({n : ℕ | A341996 n = 1} : Set ℕ).HasDensity c :=
by
  use lowerDensity {n : ℕ | A341996 n = 1}
  apply hasDensity_of_equal_densities
  sorry
