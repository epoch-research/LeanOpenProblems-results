import FormalConjectures.Util.ProblemImports

open Nat Rat Int

/--
A093818: $a(n) = \gcd(\mathrm{A001008}(n), n!)$.
$\mathrm{A001008}(n)$ is the numerator of the $n$-th harmonic number $H_n = \sum_{i=1}^n \frac{1}{i}$.
-/
def a (n : ℕ) : ℕ :=
  Nat.gcd ((harmonic n).num.natAbs) (n.factorial)

/-- Conjecture: every odd prime occurs as a term in the sequence. -/
theorem oeis_93818_conjecture_0 :
  ∀ (p : ℕ), Nat.Prime p → p ≠ 2 → ∃ (n : ℕ), 0 < n ∧ a n = p := by
  intro p hp hne
  rcases hp.eq_two_or_odd with rfl | h_odd
  · contradiction
  · by_cases h3 : p = 3
    · subst h3
      use 7
      refine ⟨by decide, ?_⟩
      unfold a harmonic
      norm_num
    · by_cases h5 : p = 5
      · subst h5
        use 20
        refine ⟨by decide, ?_⟩
        unfold a harmonic
        norm_num
      · by_cases h7 : p = 7
        · subst h7
          use 42
          refine ⟨by decide, ?_⟩
          unfold a harmonic
          norm_num
        · by_cases h11 : p = 11
          · subst h11
            use 77
            refine ⟨by decide, ?_⟩
            unfold a harmonic
            norm_num
          · by_cases h13 : p = 13
            · subst h13
              use 156
              refine ⟨by decide, ?_⟩
              unfold a harmonic
              norm_num
            · by_cases h17 : p = 17
              · subst h17
                use 272
                refine ⟨by decide, ?_⟩
                unfold a harmonic
                norm_num
              · by_cases h19 : p = 19
                · subst h19
                  use 342
                  refine ⟨by decide, ?_⟩
                  unfold a harmonic
                  norm_num
                · -- For p >= 23, we can use the classical choice or prove it.
                  sorry



