import Mathlib

def S (n : ℕ) : ℕ := (Nat.digits 10 n).sum
def f (k C : ℕ) : ℕ := (k + 1) ^ C

lemma S_10 (q d : ℕ) (hd : d < 10) : S (10 * q + d) = S q + d := by
  by_cases hq : q = 0
  · simp [hq, S]
    cases d with
    | zero => simp
    | succ d =>
      have : d + 1 < 10 := hd
      rw [Nat.digits_of_lt _ _ (by omega) (by omega)]
      simp
  · have h1 : 10 * q + d > 0 := by omega
    have h2 : 1 < 10 := by decide
    unfold S
    rw [Nat.digits_def' h2 h1]
    have h3 : (10 * q + d) % 10 = d := by omega
    have h4 : (10 * q + d) / 10 = q := by omega
    rw [h3, h4]
    simp [add_comm]

lemma S_add_pow (k j i : ℕ) (hj : j < 10) (hi : i < 10^k) :
  S (10^k * j + i) = j + S i := by
  induction k generalizing i with
  | zero =>
    have : i = 0 := by omega
    rw [this]
    simp
    have eqj : S j = S (10 * 0 + j) := by congr 1; omega
    rw [eqj, S_10 0 j hj]
    simp [S]
  | succ k ih =>
    have eq : 10^(k+1) * j + i = 10 * (10^k * j + i / 10) + i % 10 := by
      have h1 : 10^(k+1) = 10 * 10^k := by ring
      rw [h1]
      have h2 : i = 10 * (i / 10) + i % 10 := Nat.div_add_mod i 10 |>.symm
      have h3 : 10 * 10^k * j = 10 * (10^k * j) := by ring
      rw [h3]
      nth_rw 1 [h2]
      ring
    rw [eq]
    rw [S_10 _ (i % 10) (by omega)]
    have h_Si : S i = S (10 * (i / 10) + i % 10) := by congr 1; omega
    rw [h_Si]
    rw [S_10 (i / 10) (i % 10) (by omega)]
    have h_div : i / 10 < 10^k := by
      have h1 : 10^(k+1) = 10 * 10^k := by ring
      have h2 : i < 10 * 10^k := by omega
      exact (Nat.div_lt_iff_lt_mul (by decide)).mpr (by omega)
    rw [ih (i / 10) h_div]
    omega

lemma countP_range_mul (n m : ℕ) (p : ℕ → Bool) :
  (List.range (n * m)).countP p =
    ∑ i ∈ Finset.range n, (List.range m).countP (fun j => p (i * m + j)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, List.range_add, List.countP_append]
    rw [ih, Finset.sum_range_succ]
    congr 1
    rw [List.countP_map]
    rfl

def f (k C : ℕ) : ℕ := (k + 1) ^ C

lemma poly_sum_bound (k C : ℕ) : ∑ d ∈ Finset.range (C + 1), f k (C - d) ≤ f (k + 1) C := by
  unfold f
  induction C with
  | zero => simp
  | succ C ih =>
    have : ∑ d ∈ Finset.range (C + 1 + 1), (k + 1) ^ (C + 1 - d) =
           (k + 1) ^ (C + 1) + ∑ d ∈ Finset.range (C + 1), (k + 1) ^ (C - d) := by
      rw [Finset.sum_range_succ']
      have h0 : (k + 1) ^ (C + 1 - 0) = (k + 1) ^ (C + 1) := by rfl
      rw [h0]
      have h1 : ∑ i ∈ Finset.range (C + 1), (k + 1) ^ (C + 1 - (i + 1)) = ∑ d ∈ Finset.range (C + 1), (k + 1) ^ (C - d) := by
        apply Finset.sum_congr rfl
        intro x hx
        congr 1
        omega
      rw [h1]
      apply add_comm
    rw [this]
    have h1 : (k + 1) ^ (C + 1) + ∑ d ∈ Finset.range (C + 1), (k + 1) ^ (C - d) ≤
              (k + 1) ^ (C + 1) + (k + 2) ^ C := Nat.add_le_add_left ih _
    have h2 : (k + 1) ^ (C + 1) + (k + 2) ^ C ≤ (k + 2) ^ (C + 1) := by
      calc (k + 1) ^ (C + 1) + (k + 2) ^ C
        _ = (k + 1) ^ C * (k + 1) + (k + 2) ^ C := by ring
        _ ≤ (k + 2) ^ C * (k + 1) + (k + 2) ^ C := by
            apply Nat.add_le_add_right
            apply Nat.mul_le_mul_right
            exact Nat.pow_le_pow_left (by omega) _
        _ = (k + 2) ^ C * (k + 2) := by ring
        _ = (k + 2) ^ (C + 1) := by ring
    exact h1.trans h2

lemma W_bound_pow (k C : ℕ) : (List.range (10^k)).countP (fun q => S q ≤ C) ≤ f k C := by
  induction k generalizing C with
  | zero =>
    simp [f]
    split <;> omega
  | succ k ih =>
    have : 10 ^ (k + 1) = 10 * 10 ^ k := by ring
    rw [this]
    rw [countP_range_mul 10 (10^k)]
    have h_sum : ∑ j ∈ Finset.range 10, (List.range (10^k)).countP (fun i => S (j * 10^k + i) ≤ C) =
                 ∑ j ∈ Finset.range 10, (List.range (10^k)).countP (fun i => j + S i ≤ C) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj_lt : j < 10 := by simpa using hj
      apply List.countP_congr
      intro i hi
      simp only [List.mem_range] at hi
      have : S (10^k * j + i) = j + S i := S_add_pow k j i hj_lt hi
      have eq : S (j * 10^k + i) = S (10^k * j + i) := by congr 1; ring
      rw [eq, this]
    rw [h_sum]
    have h_le : ∑ j ∈ Finset.range 10, (List.range (10^k)).countP (fun i => j + S i ≤ C) ≤
                ∑ j ∈ Finset.range (C + 1), (List.range (10^k)).countP (fun i => S i ≤ C - j) := by
      -- just drop terms where j > C, and for j <= C, j + S i <= C is S i <= C - j.
      sorry
    -- and then apply ih and poly_sum_bound
    sorry
