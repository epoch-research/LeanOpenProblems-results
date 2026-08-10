import FormalConjectures.Util.ProblemImports

open Nat Finset Int

def blocking_prime_by_idx (idx : ℕ) : ℕ := 3

lemma blocking_prime_by_idx_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx idx) := by
  unfold blocking_prime_by_idx; decide

lemma blocking_prime_by_idx_3mod4 (idx : ℕ) : blocking_prime_by_idx idx % 4 = 3 := by
  unfold blocking_prime_by_idx; decide

def N : ℕ := 10

def is_blocked_by_idx (idx : ℕ) : Bool :=
  let p := blocking_prime_by_idx idx
  let v := if idx = 6400 then 1 else 4^(idx / 40) * (10 * 16^(idx % 40) + 16 * 4^(idx % 40) + 10) / 9
  (N^2 - v) % p == 0 && (N^2 - v) % (p^2) != 0

theorem is_blocked_all : ∀ idx < 6401, is_blocked_by_idx idx = true := sorry

theorem test_6400 (h_blocked : is_blocked_by_idx 6400 = true) :
    (N^2 - 1) % (blocking_prime_by_idx 6400) = 0 ∧
    (N^2 - 1) % (blocking_prime_by_idx 6400)^2 ≠ 0 := by
  unfold is_blocked_by_idx at h_blocked
  -- split_ifs at h_blocked
  -- since 6400 = 6400 is true, it should simplify automatically
  dsimp only at h_blocked
  rw [Bool.and_eq_true] at h_blocked
  exact ⟨beq_iff_eq.mp h_blocked.1, bne_iff_ne.mp h_blocked.2⟩
