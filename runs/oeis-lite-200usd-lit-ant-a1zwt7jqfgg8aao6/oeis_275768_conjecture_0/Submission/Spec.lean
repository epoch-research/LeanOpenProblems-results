import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A275768: $a(n)$ is the number of ways to express $n = \frac{\operatorname{prime}(i) + \operatorname{prime}(j)}{2}$ when $\frac{|\operatorname{prime}(i) - \operatorname{prime}(j)|}{2}$ also is prime.
This is equivalent to counting the number of primes $q$ such that $n - q$ and $n + q$ are also prime.
-/
def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

/-- **Reduction lemma.** If `q` is counted in `a n` (so `q`, `n - q`, `n + q` are prime
with `q < n`) and `n` is not divisible by `6`, then `q ∈ {2, 3, n - 3}`. -/
theorem reduction (n q : ℕ) (hqr : q < n)
    (hq : Nat.Prime q) (hnq : Nat.Prime (n - q)) (hnpq : Nat.Prime (n + q))
    (h6 : ¬ (6 ∣ n)) : q = 2 ∨ q = 3 ∨ q = n - 3 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h2, h3, hn3⟩ := hcon
  have hq2le := hq.two_le
  have hqodd : ¬ 2 ∣ q := fun hd =>
    h2 ((hq.eq_one_or_self_of_dvd 2 hd).resolve_left (by norm_num)).symm
  have hq3d : ¬ 3 ∣ q := fun hd =>
    h3 ((hq.eq_one_or_self_of_dvd 3 hd).resolve_left (by norm_num)).symm
  by_cases h2n : 2 ∣ n
  · by_cases h3n : 3 ∣ n
    · exact h6 (by
        have := (show Nat.Coprime 2 3 by decide).mul_dvd_of_dvd_of_dvd h2n h3n
        simpa using this)
    · have hnm : n % 3 = 1 ∨ n % 3 = 2 := by omega
      have hqm : q % 3 = 1 ∨ q % 3 = 2 := by omega
      have hcase : 3 ∣ (n - q) ∨ 3 ∣ (n + q) := by
        rcases hnm with h | h <;> rcases hqm with h' | h' <;> omega
      rcases hcase with hd | hd
      · have h := (hnq.eq_one_or_self_of_dvd 3 hd).resolve_left (by norm_num)
        omega
      · have h := (hnpq.eq_one_or_self_of_dvd 3 hd).resolve_left (by norm_num)
        omega
  · have hd : 2 ∣ (n + q) := by omega
    have h := (hnpq.eq_one_or_self_of_dvd 2 hd).resolve_left (by norm_num)
    omega

/-- If `6 ∤ n` then `a n ≤ 3`: the counted set is contained in `{2, 3, n - 3}`. -/
theorem not_four_of_not_six (n : ℕ) (h6 : ¬ (6 ∣ n)) : a n ≤ 3 := by
  have hsub : (Finset.filter (fun q : ℕ =>
      Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)) (Finset.range n))
      ⊆ ({2, 3, n - 3} : Finset ℕ) := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_range] at hq
    obtain ⟨hqr, hqp, hnq, hnpq⟩ := hq
    have := reduction n q hqr hqp hnq hnpq h6
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hc := Finset.card_le_card hsub
  have h3 : ({2, 3, n - 3} : Finset ℕ).card ≤ 3 := by
    calc ({2, 3, n - 3} : Finset ℕ).card
        ≤ ({3, n - 3} : Finset ℕ).card + 1 := Finset.card_insert_le _ _
      _ ≤ (({n - 3} : Finset ℕ).card + 1) + 1 :=
          Nat.add_le_add_right (Finset.card_insert_le _ _) 1
      _ = 3 := by simp
  exact le_trans hc h3

/-- OEIS A275768 conjecture 0: Does a(n) = 4 occur for any n? -/
theorem oeis_275768_conjecture_0 : ¬ ∃ n : ℕ, a n = 4 := by
  rintro ⟨n, hn⟩
  by_cases h6 : 6 ∣ n
  · by_cases hlt : n < 24
    · -- finite check: for `6 ∣ n` with `n < 24`, i.e. `n ∈ {0,6,12,18}`, `a n ∈ {0,2,3}`.
      interval_cases n <;> first | omega | (revert hn; decide)
    · -- Residual case: `6 ∣ n`, `n ≥ 24` (i.e. `n = 6m`, `m ≥ 4`).  Here `q = 2` is never
      -- valid (`n - 2` is even `> 2`) and every valid `q` is coprime to `6`, so there is NO
      -- modular / covering obstruction: the count is unbounded (`a 60 = 10`, `a 120 = 16`).
      -- Empirically `a(6m) ∈ {0,2,3}` for `m ≤ 3` and `a(6m) ≥ 5` for `m ≥ 4`, so `4` is
      -- skipped as a growth-transition gap with NO elementary obstruction to the value `4`.
      -- Ruling out `4` requires `a n ≥ 5`, i.e. that the three linear forms in `q`,
      --   L₁(q) = q,   L₂(q) = n - q,   L₃(q) = n + q,
      -- are simultaneously prime for at least five primes `q`.  Even `a n ≥ 1` is a case of
      -- **Dickson's Conjecture** (Hardy–Littlewood k-tuple), which contains the twin-prime
      -- conjecture and is UNCONDITIONALLY OPEN: blocked by the sieve parity problem
      -- (dimension 3) and the circle-method binary barrier.  No proof exists to formalize.
      sorry
  · have := not_four_of_not_six n h6
    omega
