import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)

def primeProd (n : ℕ) : ℕ :=
  ∏ q ∈ (Finset.range ((3*n - 1)/2 + 1)).filter (fun q => decide (n < q ∧ Nat.Prime q)), q^3

example (H : ∀ n, primeProd n ∣ a n) (p n : ℕ) (hp : Nat.Prime p)
    (h1 : (2*p+3)/3 ≤ n) (h2 : n ≤ p-1) : (p^3 : ℕ) ∣ a n := by
  have hpgt : n < p := by
    have hp0 : 0 < p := hp.pos
    omega
  have hple : p ≤ (3*n - 1)/2 := by
    -- from ceil((2p+1)/3) <= n => p <= (3n-1)/2
    omega
  have hmem : p ∈ (Finset.range ((3*n - 1)/2 + 1)).filter (fun q => decide (n < q ∧ Nat.Prime q)) := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by simp [hpgt, hp]⟩
  exact (Finset.dvd_prod_of_mem (fun q => q^3) hmem).trans (H n)
