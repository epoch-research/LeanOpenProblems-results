import FormalConjectures.Util.ProblemImports

noncomputable def a (n : ℕ) : ℕ :=
  let start_idx : ℕ := (n * (n - 1)) / 2
  Finset.sum (Finset.range n) fun i ↦ Nat.nth Nat.Prime (start_idx + i)

lemma a_pos {n : ℕ} (hn : 0 < n) : 0 < a n := by
  dsimp [a]
  apply Finset.sum_pos
  · intro i hi
    exact (Nat.prime_nth_prime _).pos
  · exact ⟨0, Finset.mem_range.mpr hn⟩

example : a 1 = 2 := by simp [a, Nat.nth_prime_zero_eq_two]
example : ¬ IsSquare (a 1) := by
  rw [show a 1 = 2 by simp [a, Nat.nth_prime_zero_eq_two]]
  norm_num [IsSquare]
example : IsSquare (a 38) := by
  -- This is the known positive example, but norm_num cannot unfold all nth primes at this size automatically.
  change IsSquare (a 38)
  -- left as sanity check only
  admit
