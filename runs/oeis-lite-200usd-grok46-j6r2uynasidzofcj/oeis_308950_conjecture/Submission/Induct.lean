import FormalConjectures.Util.ProblemImports

open Nat

def SunGood (n : ℕ) : Prop :=
  (∃ (a b : ℕ), 2 ^ a * 3 ^ b ≤ n ∧ Nat.Prime (6 * (n - 2 ^ a * 3 ^ b) + 1))
  ∨
  (∃ (a b : ℕ), 2 ^ a * 3 ^ b < n ∧ Nat.Prime (6 * (n - 2 ^ a * 3 ^ b) - 1))

lemma sunGood_two : SunGood 2 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩

lemma sunGood_of_add_smooth {n a b : ℕ} (hg : SunGood n)
    (h : ∃ a' b' k, n = 2 ^ a' * 3 ^ b' + k ∧
      (Nat.Prime (6 * k + 1) ∨ (0 < k ∧ Nat.Prime (6 * k - 1)))) :
    SunGood (n + 2 ^ a * 3 ^ b) := by
  -- If n = m + k with k good and m 3-smooth, then n + 2^a 3^b = (m * 2^a 3^b wait no)
  -- n + 2^a 3^b = (2^{a'} 3^{b'} + 2^a 3^b) + k, and the sum of two 3-smooths is
  -- 3-smooth only in special cases.
  sorry

-- Key observation: if k is good then every n = 3-smooth + k is SunGood.
lemma sunGood_of_good_k (k a b : ℕ) (hk : Nat.Prime (6 * k + 1)) :
    SunGood (2 ^ a * 3 ^ b + k) := by
  refine Or.inl ⟨a, b, ?_, ?_⟩
  · exact Nat.le_add_left _ _
  · simp [Nat.add_sub_cancel_left]
    exact hk

lemma sunGood_of_good_k_neg (k a b : ℕ) (hk0 : 0 < k) (hk : Nat.Prime (6 * k - 1)) :
    SunGood (2 ^ a * 3 ^ b + k) := by
  refine Or.inr ⟨a, b, ?_, ?_⟩
  · have : 0 < 2 ^ a * 3 ^ b := by positivity
    omega
  · have hle : 2 ^ a * 3 ^ b ≤ 2 ^ a * 3 ^ b + k := Nat.le_add_right _ _
    rw [Nat.add_sub_cancel_left]
    exact hk

-- So the conjecture is: every n > 1 is 3-smooth + good k.
-- Equivalently the good k form an additive complement to the 3-smooths.

-- Good k include all k=1..19 except we listed them.
-- First missing is 20.

-- For the inductive step n → n+1:
-- n = m + k, n+1 = m + (k+1) or (m+1) + k.
-- m+1 is 3-smooth only if m=1,2,3,8 (Catalan/Mihailescu + known list).
-- k+1 is good only sometimes.

lemma next_of_smooth_succ {a b : ℕ} :
    (∃ a' b', 2 ^ a' * 3 ^ b' = 2 ^ a * 3 ^ b + 1) ↔
      (a, b) = (0, 0) ∨ (a, b) = (1, 0) ∨ (a, b) = (0, 1) ∨ (a, b) = (3, 0) := by
  -- 1+1=2, 2+1=3, 3+1=4, 8+1=9
  sorry
