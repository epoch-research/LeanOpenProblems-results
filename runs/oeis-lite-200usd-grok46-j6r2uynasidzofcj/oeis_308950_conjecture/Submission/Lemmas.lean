import FormalConjectures.Util.ProblemImports

open Nat

/-! Structural lemmas toward Sun's OEIS A308950 (weak OR) conjecture. -/

def SunGood (n : ℕ) : Prop :=
  (∃ (a b : ℕ), 2 ^ a * 3 ^ b ≤ n ∧ Nat.Prime (6 * (n - 2 ^ a * 3 ^ b) + 1))
  ∨
  (∃ (a b : ℕ), 2 ^ a * 3 ^ b < n ∧ Nat.Prime (6 * (n - 2 ^ a * 3 ^ b) - 1))

lemma sunGood_of_pow23 (n a b : ℕ) (hle : 2 ^ a * 3 ^ b ≤ n)
    (hp : Nat.Prime (6 * (n - 2 ^ a * 3 ^ b) + 1)) : SunGood n :=
  Or.inl ⟨a, b, hle, hp⟩

lemma sunGood_of_pow23_neg (n a b : ℕ) (hlt : 2 ^ a * 3 ^ b < n)
    (hp : Nat.Prime (6 * (n - 2 ^ a * 3 ^ b) - 1)) : SunGood n :=
  Or.inr ⟨a, b, hlt, hp⟩

/-- `m = 1 = 2^0 3^0`. -/
lemma sunGood_of_prime_six_n_sub_five {n : ℕ} (hn : 1 < n)
    (hp : Nat.Prime (6 * n - 5)) : SunGood n := by
  refine Or.inl ⟨0, 0, ?_, ?_⟩
  · simp; omega
  · convert hp using 1
    have : n - 1 + 1 = n := by omega
    have hle : 1 ≤ n := by omega
    calc
      6 * (n - 2 ^ 0 * 3 ^ 0) + 1 = 6 * (n - 1) + 1 := by simp
      _ = 6 * n - 6 + 1 := by
        have := Nat.mul_sub_left_distrib 6 n 1
        simp at this
        omega
      _ = 6 * n - 5 := by omega

lemma sunGood_of_prime_six_n_sub_seven {n : ℕ} (hn : 1 < n)
    (hp : Nat.Prime (6 * n - 7)) : SunGood n := by
  refine Or.inr ⟨0, 0, ?_, ?_⟩
  · simp; omega
  · convert hp using 1
    have : 1 < n := hn
    calc
      6 * (n - 2 ^ 0 * 3 ^ 0) - 1 = 6 * (n - 1) - 1 := by simp
      _ = 6 * n - 6 - 1 := by
        have := Nat.mul_sub_left_distrib 6 n 1
        omega
      _ = 6 * n - 7 := by omega

/-- If `n - k` is 3-smooth and `6k+1` is prime, we are done. -/
lemma sunGood_of_sub_smooth_pos {n k a b : ℕ}
    (h : n - k = 2 ^ a * 3 ^ b) (hk : k ≤ n)
    (hp : Nat.Prime (6 * k + 1)) : SunGood n := by
  have hnk : n - 2 ^ a * 3 ^ b = k := by
    rw [← h, Nat.sub_sub_self hk]
  refine Or.inl ⟨a, b, ?_, ?_⟩
  · rw [← h]; exact Nat.sub_le n k
  · rwa [hnk]

lemma sunGood_of_sub_smooth_neg {n k a b : ℕ}
    (h : n - k = 2 ^ a * 3 ^ b) (hk : k < n) (hk0 : 0 < k)
    (hp : Nat.Prime (6 * k - 1)) : SunGood n := by
  have hle : k ≤ n := Nat.le_of_lt hk
  have hnk : n - 2 ^ a * 3 ^ b = k := by
    rw [← h, Nat.sub_sub_self hle]
  refine Or.inr ⟨a, b, ?_, ?_⟩
  · rw [← h]; exact Nat.sub_lt (Nat.zero_lt_of_lt hk) hk0
  · rwa [hnk]

-- k = 1, ..., 19 are all good (6k±1 has a prime).
lemma goodk1 : Nat.Prime (6 * 1 + 1) := by norm_num
lemma goodk2 : Nat.Prime (6 * 2 + 1) := by norm_num
lemma goodk3 : Nat.Prime (6 * 3 + 1) := by norm_num
lemma goodk4 : Nat.Prime (6 * 4 - 1) := by norm_num
lemma goodk5 : Nat.Prime (6 * 5 + 1) := by norm_num
lemma goodk6 : Nat.Prime (6 * 6 + 1) := by norm_num
lemma goodk7 : Nat.Prime (6 * 7 + 1) := by norm_num
lemma goodk8 : Nat.Prime (6 * 8 - 1) := by norm_num
lemma goodk9 : Nat.Prime (6 * 9 - 1) := by norm_num
lemma goodk10 : Nat.Prime (6 * 10 + 1) := by norm_num
lemma goodk11 : Nat.Prime (6 * 11 + 1) := by norm_num
lemma goodk12 : Nat.Prime (6 * 12 + 1) := by norm_num
lemma goodk13 : Nat.Prime (6 * 13 + 1) := by norm_num
lemma goodk14 : Nat.Prime (6 * 14 - 1) := by norm_num
lemma goodk15 : Nat.Prime (6 * 15 - 1) := by norm_num
lemma goodk16 : Nat.Prime (6 * 16 + 1) := by norm_num
lemma goodk17 : Nat.Prime (6 * 17 + 1) := by norm_num
lemma goodk18 : Nat.Prime (6 * 18 + 1) := by norm_num
lemma goodk19 : Nat.Prime (6 * 19 - 1) := by norm_num

/-- If `n` lies at distance `k ∈ {1,...,19}` from a 3-smooth number, then `SunGood n`. -/
lemma sunGood_of_near_smooth {n a b k : ℕ}
    (hk : k ∈ Finset.Icc 1 19) (h : n = 2 ^ a * 3 ^ b + k) : SunGood n := by
  have hkpos : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hk19 : k ≤ 19 := (Finset.mem_Icc.mp hk).2
  have hsmooth_pos : 0 < 2 ^ a * 3 ^ b := by positivity
  have hkn : k ≤ n := by omega
  -- dispatch on k
  interval_cases k
  · -- k=1, 6*1+1=7
    refine sunGood_of_sub_smooth_pos (n := n) (k := 1) (a := a) (b := b) ?_ ?_ goodk1
    · omega
    · exact hkn
  · refine sunGood_of_sub_smooth_pos (k := 2) (a := a) (b := b) ?_ (by omega) goodk2
    · omega
  · refine sunGood_of_sub_smooth_pos (k := 3) (a := a) (b := b) ?_ (by omega) goodk3
    · omega
  · refine sunGood_of_sub_smooth_neg (k := 4) (a := a) (b := b) ?_ (by omega) (by omega) goodk4
    · omega
  · refine sunGood_of_sub_smooth_pos (k := 5) (a := a) (b := b) ?_ (by omega) goodk5
    · omega
  · refine sunGood_of_sub_smooth_pos (k := 6) (a := a) (b := b) ?_ (by omega) goodk6
    · omega
  · refine sunGood_of_sub_smooth_pos (k := 7) (a := a) (b := b) ?_ (by omega) goodk7
    · omega
  · refine sunGood_of_sub_smooth_neg (k := 8) (a := a) (b := b) ?_ (by omega) (by omega) goodk8
    · omega
  · refine sunGood_of_sub_smooth_neg (k := 9) (a := a) (b := b) ?_ (by omega) (by omega) goodk9
    · omega
  · refine sunGood_of_sub_smooth_pos (k := 10) (a := a) (b := b) ?_ (by omega) goodk10
    · omega
  · refine sunGood_of_sub_smooth_pos (k := 11) (a := a) (b := b) ?_ (by omega) goodk11
    · omega
  · refine sunGood_of_sub_smooth_pos (k := 12) (a := a) (b := b) ?_ (by omega) goodk12
    · omega
  · refine sunGood_of_sub_smooth_pos (k := 13) (a := a) (b := b) ?_ (by omega) goodk13
    · omega
  · refine sunGood_of_sub_smooth_neg (k := 14) (a := a) (b := b) ?_ (by omega) (by omega) goodk14
    · omega
  · refine sunGood_of_sub_smooth_neg (k := 15) (a := a) (b := b) ?_ (by omega) (by omega) goodk15
    · omega
  · refine sunGood_of_sub_smooth_pos (k := 16) (a := a) (b := b) ?_ (by omega) goodk16
    · omega
  · refine sunGood_of_sub_smooth_pos (k := 17) (a := a) (b := b) ?_ (by omega) goodk17
    · omega
  · refine sunGood_of_sub_smooth_pos (k := 18) (a := a) (b := b) ?_ (by omega) goodk18
    · omega
  · refine sunGood_of_sub_smooth_neg (k := 19) (a := a) (b := b) ?_ (by omega) (by omega) goodk19
    · omega

