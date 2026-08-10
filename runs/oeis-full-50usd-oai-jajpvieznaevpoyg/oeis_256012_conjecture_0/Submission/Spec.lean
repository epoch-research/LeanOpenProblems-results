import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A256012: Number of partitions of $n$ into distinct parts that are not squarefree.
This is the number of finite subsets of positive integers $P$ such that $\sum_{k \in P} k = n$ and every element $k \in P$ is not squarefree.
-/
def A256012 (n : ℕ) : ℕ :=
  -- The parts must be $\le n$ to sum to $n$.
  -- This is $\{1, 2, \dots, n\}$
  let potential_parts : Finset ℕ := range (n + 1) \ {0}

  -- We count all subsets P of potential_parts that satisfy the sum and the property.
  card <| filter (fun P : Finset ℕ =>
    P.sum id = n ∧
    (∀ k ∈ P, ¬ Squarefree k)
  ) (powerset potential_parts)

private lemma not_squarefree_of_four_dvd {k : ℕ} (h : 4 ∣ k) : ¬ Squarefree k := by
  intro hk
  have hnot := (Nat.squarefree_iff_prime_squarefree.mp hk) 2 Nat.prime_two
  exact hnot (by simpa using h)

private lemma not_squarefree_of_nine_dvd {k : ℕ} (h : 9 ∣ k) : ¬ Squarefree k := by
  intro hk
  have hnot := (Nat.squarefree_iff_prime_squarefree.mp hk) 3 Nat.prime_three
  exact hnot (by simpa using h)

private lemma A256012_pos_of_witness {n : ℕ} {P : Finset ℕ}
    (hsum : P.sum id = n)
    (hsq : ∀ k ∈ P, ¬ Squarefree k)
    (hpos : ∀ k ∈ P, k ≠ 0)
    (hle : ∀ k ∈ P, k ≤ n) : A256012 n > 0 := by
  unfold A256012
  apply Finset.card_pos.mpr
  refine ⟨P, ?_⟩
  simp only [Finset.mem_filter]
  constructor
  · apply Finset.mem_powerset.mpr
    intro k hk
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton]
    exact ⟨Nat.lt_succ_of_le (hle k hk), hpos k hk⟩
  · exact ⟨hsum, hsq⟩

private lemma A256012_pos_mod0 (n : ℕ) (hn : n > 23) (hmod : n % 4 = 0) :
    A256012 n > 0 := by
  apply A256012_pos_of_witness (P := {n})
  · simp
  · intro k hk
    simp at hk
    subst k
    exact not_squarefree_of_four_dvd (Nat.dvd_of_mod_eq_zero hmod)
  · intro k hk
    simp at hk
    omega
  · intro k hk
    simp at hk
    omega

private lemma A256012_pos_mod1 (n : ℕ) (hn : n > 23) (hmod : n % 4 = 1) :
    A256012 n > 0 := by
  apply A256012_pos_of_witness (P := {9, n - 9})
  · have hn9 : 9 ≤ n := by omega
    have hne : 9 ≠ n - 9 := by omega
    rw [Finset.sum_pair hne]
    simp [id]
    omega
  · intro k hk
    simp at hk
    rcases hk with rfl | rfl
    · exact not_squarefree_of_nine_dvd (by decide)
    · apply not_squarefree_of_four_dvd
      apply Nat.dvd_of_mod_eq_zero
      omega
  · intro k hk
    simp at hk
    rcases hk with rfl | rfl <;> omega
  · intro k hk
    simp at hk
    rcases hk with rfl | rfl <;> omega

private lemma A256012_pos_mod2 (n : ℕ) (hn : n > 23) (hmod : n % 4 = 2) :
    A256012 n > 0 := by
  apply A256012_pos_of_witness (P := {18, n - 18})
  · have hn18 : 18 ≤ n := by omega
    have hne : 18 ≠ n - 18 := by omega
    rw [Finset.sum_pair hne]
    simp [id]
    omega
  · intro k hk
    simp at hk
    rcases hk with rfl | rfl
    · exact not_squarefree_of_nine_dvd (by decide)
    · apply not_squarefree_of_four_dvd
      apply Nat.dvd_of_mod_eq_zero
      omega
  · intro k hk
    simp at hk
    rcases hk with rfl | rfl <;> omega
  · intro k hk
    simp at hk
    rcases hk with rfl | rfl <;> omega

private lemma A256012_pos_mod3 (n : ℕ) (hn : n > 23) (hmod : n % 4 = 3) :
    A256012 n > 0 := by
  by_cases hn27 : n = 27
  · subst n
    apply A256012_pos_of_witness (P := {27})
    · simp
    · intro k hk
      simp at hk
      subst k
      exact not_squarefree_of_nine_dvd (by decide)
    · intro k hk
      simp at hk
      omega
    · intro k hk
      simp at hk
      omega
  · apply A256012_pos_of_witness (P := {27, n - 27})
    · have hn27le : 27 ≤ n := by omega
      have hne : 27 ≠ n - 27 := by omega
      rw [Finset.sum_pair hne]
      simp [id]
      omega
    · intro k hk
      simp at hk
      rcases hk with rfl | rfl
      · exact not_squarefree_of_nine_dvd (by decide)
      · apply not_squarefree_of_four_dvd
        apply Nat.dvd_of_mod_eq_zero
        omega
    · intro k hk
      simp at hk
      rcases hk with rfl | rfl <;> omega
    · intro k hk
      simp at hk
      rcases hk with rfl | rfl <;> omega

/--
Conjecture: a(n) > 0 for n > 23.
-/
theorem oeis_256012_conjecture_0 (n : ℕ) (hn : n > 23) : A256012 n > 0 := by
  have hlt : n % 4 < 4 := Nat.mod_lt n (by decide : 0 < 4)
  interval_cases h : n % 4
  · exact A256012_pos_mod0 n hn h
  · exact A256012_pos_mod1 n hn h
  · exact A256012_pos_mod2 n hn h
  · exact A256012_pos_mod3 n hn h
