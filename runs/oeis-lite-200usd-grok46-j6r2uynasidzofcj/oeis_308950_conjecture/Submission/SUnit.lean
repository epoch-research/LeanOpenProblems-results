import FormalConjectures.Util.ProblemImports

open Nat

def threeSmooth (m : ℕ) : Prop := ∃ a b : ℕ, m = 2 ^ a * 3 ^ b

lemma threeSmooth_one : threeSmooth 1 := ⟨0, 0, by simp⟩

lemma threeSmooth_mul {m n : ℕ} (hm : threeSmooth m) (hn : threeSmooth n) :
    threeSmooth (m * n) := by
  obtain ⟨a, b, rfl⟩ := hm
  obtain ⟨c, d, rfl⟩ := hn
  refine ⟨a + c, b + d, ?_⟩
  rw [pow_add, pow_add]
  ring

lemma three_pow_mod_eight (b : ℕ) : 3 ^ b % 8 = 1 ∨ 3 ^ b % 8 = 3 := by
  induction b with
  | zero => simp
  | succ b ih =>
      rw [pow_succ]
      have : (3 ^ b * 3) % 8 = ((3 ^ b % 8) * (3 % 8)) % 8 := Nat.mul_mod _ _ _
      rw [this]
      rcases ih with h | h
      · rw [h]; norm_num
      · rw [h]; norm_num

lemma two_pow_ge_three (k : ℕ) : 8 ≤ 2 ^ (k + 3) := by
  have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 3 ≤ k + 3)
  simpa using this

lemma two_pow_mod_eight_of_ge_three (k : ℕ) : 2 ^ (k + 3) % 8 = 0 := by
  have : 8 ∣ 2 ^ (k + 3) := by
    have : 2 ^ 3 ∣ 2 ^ (k + 3) := pow_dvd_pow 2 (by omega)
    simpa using this
  exact Nat.mod_eq_zero_of_dvd this

/-- `2^a - 1 = 3^b` has only the solutions `(1,0)` and `(2,1)`. -/
lemma pow2_sub_one_eq_pow3 {a b : ℕ} (h : 2 ^ a - 1 = 3 ^ b) :
    (a, b) = (1, 0) ∨ (a, b) = (2, 1) := by
  match a with
  | 0 =>
      have : 0 = 3 ^ b := by simpa using h
      have : 1 ≤ 3 ^ b := Nat.one_le_pow b 3 (by norm_num)
      omega
  | 1 =>
      have : 1 = 3 ^ b := by simpa using h
      cases b with
      | zero => exact Or.inl rfl
      | succ b =>
          have : 1 < 3 ^ (b + 1) :=
            Nat.one_lt_pow (n := b + 1) (a := 3) (by omega) (by norm_num)
          omega
  | 2 =>
      have : 3 = 3 ^ b := by simpa using h
      cases b with
      | zero => simp at this
      | succ b =>
          cases b with
          | zero => exact Or.inr rfl
          | succ b =>
              have hge : 9 ≤ 3 ^ (b + 2) := by
                have := Nat.pow_le_pow_right (by norm_num : 0 < 3)
                  (by omega : 2 ≤ b + 2)
                simpa using this
              omega
  | k + 3 =>
      have hL : (2 ^ (k + 3) - 1) % 8 = 7 := by
        have h8 : 2 ^ (k + 3) % 8 = 0 := two_pow_mod_eight_of_ge_three k
        have hge : 8 ≤ 2 ^ (k + 3) := two_pow_ge_three k
        omega
      have hR := three_pow_mod_eight b
      have heq : (2 ^ (k + 3) - 1) % 8 = 3 ^ b % 8 := by
        rw [h]
      have : 3 ^ b % 8 = 7 := by omega
      omega
