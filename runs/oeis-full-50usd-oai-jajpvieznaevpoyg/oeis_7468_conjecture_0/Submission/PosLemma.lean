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

#check a_pos
