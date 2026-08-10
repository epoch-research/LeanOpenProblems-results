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

/-- A number with a non-unit square divisor is not squarefree. -/
private lemma not_sqfree (m d : ℕ) (hd : ¬ IsUnit d) (hdvd : d * d ∣ m) : ¬ Squarefree m :=
  fun h => hd (h d hdvd)

private lemma not_unit_two : ¬ IsUnit (2 : ℕ) := by
  rw [Nat.isUnit_iff]; norm_num

private lemma not_unit_three : ¬ IsUnit (3 : ℕ) := by
  rw [Nat.isUnit_iff]; norm_num

/-- Any multiple of `4` is not squarefree. -/
private lemma not_sqfree_mul4 (k : ℕ) (hk : 4 ∣ k) : ¬ Squarefree k :=
  not_sqfree k 2 not_unit_two (by obtain ⟨c, rfl⟩ := hk; exact ⟨c, by ring⟩)

/-- A positive number `≤ n` is an admissible part. -/
private lemma mem_pp (n k : ℕ) (h1 : k ≤ n) (h2 : k ≠ 0) : k ∈ range (n + 1) \ {0} := by
  rw [mem_sdiff, mem_range, mem_singleton]; exact ⟨by omega, h2⟩

/--
Conjecture: a(n) > 0 for n > 23.

Proof: For every `n > 23` we exhibit an explicit partition of `n` into distinct
non-squarefree parts, depending on `n mod 4`:
* `n ≡ 0`: `{n}` (since `4 ∣ n`);
* `n ≡ 1`: `{9, n - 9}` (with `4 ∣ n - 9`);
* `n ≡ 2`: `{18, n - 18}` (with `4 ∣ n - 18`);
* `n ≡ 3`: `{27}` if `n = 27`, otherwise `{27, n - 27}` (with `4 ∣ n - 27`).
-/
theorem oeis_256012_conjecture_0 (n : ℕ) (hn : n > 23) : A256012 n > 0 := by
  rw [A256012, gt_iff_lt, Finset.card_pos]
  -- We produce an explicit partition depending on n mod 4.
  have key : ∃ P : Finset ℕ, P ⊆ range (n + 1) \ {0} ∧ P.sum id = n ∧
      ∀ k ∈ P, ¬ Squarefree k := by
    have hm : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    rcases hm with hm | hm | hm | hm
    · -- n ≡ 0 mod 4
      refine ⟨{n}, ?_, ?_, ?_⟩
      · intro k hk; rw [mem_singleton] at hk; rw [hk]
        exact mem_pp n n (le_refl n) (by omega)
      · simp
      · intro k hk; rw [mem_singleton] at hk; rw [hk]
        exact not_sqfree_mul4 n (by omega)
    · -- n ≡ 1 mod 4
      have hne : (9 : ℕ) ≠ n - 9 := by omega
      refine ⟨{9, n - 9}, ?_, ?_, ?_⟩
      · intro k hk; rw [mem_insert, mem_singleton] at hk
        rcases hk with rfl | rfl
        · exact mem_pp n 9 (by omega) (by omega)
        · exact mem_pp n (n - 9) (by omega) (by omega)
      · rw [Finset.sum_pair hne]; simp; omega
      · intro k hk; rw [mem_insert, mem_singleton] at hk
        rcases hk with rfl | rfl
        · exact not_sqfree 9 3 not_unit_three ⟨1, by norm_num⟩
        · exact not_sqfree_mul4 (n - 9) (by omega)
    · -- n ≡ 2 mod 4
      have hne : (18 : ℕ) ≠ n - 18 := by omega
      refine ⟨{18, n - 18}, ?_, ?_, ?_⟩
      · intro k hk; rw [mem_insert, mem_singleton] at hk
        rcases hk with rfl | rfl
        · exact mem_pp n 18 (by omega) (by omega)
        · exact mem_pp n (n - 18) (by omega) (by omega)
      · rw [Finset.sum_pair hne]; simp; omega
      · intro k hk; rw [mem_insert, mem_singleton] at hk
        rcases hk with rfl | rfl
        · exact not_sqfree 18 3 not_unit_three ⟨2, by norm_num⟩
        · exact not_sqfree_mul4 (n - 18) (by omega)
    · -- n ≡ 3 mod 4
      by_cases hn27 : n = 27
      · refine ⟨{27}, ?_, ?_, ?_⟩
        · intro k hk; rw [mem_singleton] at hk; rw [hk]
          exact mem_pp n 27 (by omega) (by omega)
        · simp [hn27]
        · intro k hk; rw [mem_singleton] at hk; rw [hk]
          exact not_sqfree 27 3 not_unit_three ⟨3, by norm_num⟩
      · have hne : (27 : ℕ) ≠ n - 27 := by omega
        refine ⟨{27, n - 27}, ?_, ?_, ?_⟩
        · intro k hk; rw [mem_insert, mem_singleton] at hk
          rcases hk with rfl | rfl
          · exact mem_pp n 27 (by omega) (by omega)
          · exact mem_pp n (n - 27) (by omega) (by omega)
        · rw [Finset.sum_pair hne]; simp; omega
        · intro k hk; rw [mem_insert, mem_singleton] at hk
          rcases hk with rfl | rfl
          · exact not_sqfree 27 3 not_unit_three ⟨3, by norm_num⟩
          · exact not_sqfree_mul4 (n - 27) (by omega)
  obtain ⟨P, hsub, hsum, hsqf⟩ := key
  exact ⟨P, mem_filter.mpr ⟨mem_powerset.mpr hsub, hsum, hsqf⟩⟩
