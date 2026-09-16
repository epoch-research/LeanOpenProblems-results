import Submission.Spec

theorem oeis_a179524_sun_conjecture_2_proof :
  (∀ n : ℕ, n ≥ 1 → (n : ℤ) ∣ (Finset.range n).sum fun k : ℕ => (20 * k + 17) * a k) ∧
  (∀ p : ℕ, (hp : Nat.Prime p) → p ≠ 2 →
    haveI inst_prime : Fact (Nat.Prime p) := ⟨hp⟩
    let S : ℤ := (Finset.range p).sum fun k : ℕ => (20 * k + 17) * a k
    let L : ℤ := legendreSym p (-1)
    S ≡ (p : ℤ) * (10 * L + 7) [ZMOD (p : ℤ) ^ 2]
  ) := by
  aesop
