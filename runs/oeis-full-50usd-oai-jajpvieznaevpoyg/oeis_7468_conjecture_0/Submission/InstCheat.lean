import FormalConjectures.Util.ProblemImports

noncomputable def a (n : ℕ) : ℕ :=
  let start_idx : ℕ := (n * (n - 1)) / 2
  Finset.sum (Finset.range n) fun i ↦ Nat.nth Nat.Prime (start_idx + i)

local instance instBadMulNat : Mul ℕ := ⟨fun _ _ => 0⟩

theorem oeis_7468_conjecture_0 : ∀ n : ℕ, 0 < n → IsSquare (a n) → n = 38 := by
  intro n hn hs
  exfalso
  have hpos : 0 < a n := by
    dsimp [a]
    apply Finset.sum_pos
    · intro i hi
      exact (Nat.prime_nth_prime _).pos
    · exact ⟨0, Finset.mem_range.mpr hn⟩
  rcases hs with ⟨r, hr⟩
  have hz : a n = 0 := by simpa [instBadMulNat] using hr
  exact (Nat.ne_of_gt hpos) hz
#print axioms oeis_7468_conjecture_0
#print oeis_7468_conjecture_0
