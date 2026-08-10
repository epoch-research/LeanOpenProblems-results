import FormalConjectures.Util.ProblemImports
open Finset

lemma my_sum_range_reflect (n : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ range n, f (n - 1 - i) = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h_sub_eq : ∀ i ∈ range (n + 1), n + 1 - 1 - i = n - i := by
      intro i hi
      omega
    have h_rw : ∑ i ∈ range (n + 1), f (n + 1 - 1 - i) = ∑ i ∈ range (n + 1), f (n - i) := by
      apply sum_congr rfl
      intro i hi
      rw [h_sub_eq i hi]
    rw [h_rw]
    rw [sum_range_succ']
    have h_sub_eq2 : ∀ k ∈ range n, n - (k + 1) = n - 1 - k := by
      intro k hk
      have : k < n := mem_range.mp hk
      omega
    have h_rw2 : ∑ k ∈ range n, f (n - (k + 1)) = ∑ k ∈ range n, f (n - 1 - k) := by
      apply sum_congr rfl
      intro k hk
      rw [h_sub_eq2 k hk]
    rw [h_rw2, ih, sum_range_succ]
    rw [Nat.sub_zero]


lemma sum_range_even_odd (H : ℕ) (f : ℕ → ℕ) :
    ∑ k ∈ range (2 * H), f k = (∑ j ∈ range H, f (2 * j)) + ∑ j ∈ range H, f (2 * j + 1) := by
  induction H with
  | zero => simp
  | succ H ih =>
    have h_eq : 2 * (H + 1) = 2 * H + 2 := by ring
    rw [h_eq, sum_range_succ, sum_range_succ]
    rw [ih]
    rw [sum_range_succ, sum_range_succ]
    ring


def A048153 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

lemma even_term_mod_eq (H j : ℕ) : (2 * j) ^ 2 % (4 * H) = 4 * (j ^ 2 % H) := by
  have h1 : (2 * j) ^ 2 = 4 * j ^ 2 := by ring
  have h2 : 4 * H = 4 * H := rfl
  rw [h1, h2]
  exact Nat.mul_mod_mul_left 4 (j ^ 2) H


lemma odd_terms_sum_bound (H : ℕ) (hH : 1 ≤ H) :
    ∑ j ∈ range H, (2 * j + 1) ^ 2 % (4 * H) ≤ 4 * H ^ 2 := by
  have h_term : ∀ j ∈ range H, (2 * j + 1) ^ 2 % (4 * H) ≤ 4 * H := by
    intro j hj
    have h_pos : 0 < 4 * H := by omega
    have h_lt := Nat.mod_lt ((2 * j + 1) ^ 2) h_pos
    omega
  have h_sum := sum_le_sum h_term
  rw [sum_const, card_range, nsmul_eq_mul] at h_sum
  nlinarith


lemma sum_mod_four_H_bound (H : ℕ) (hH : 1 ≤ H) :
    ∑ k ∈ range (2 * H), k ^ 2 % (4 * H) ≤ 4 * A048153 H + 4 * H ^ 2 := by
  rw [sum_range_even_odd H (fun k => k ^ 2 % (4 * H))]
  have h_even : ∑ j ∈ range H, (2 * j) ^ 2 % (4 * H) = 4 * A048153 H := by
    unfold A048153
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    exact even_term_mod_eq H j
  rw [h_even]
  have h_odd := odd_terms_sum_bound H hH
  nlinarith

lemma div_add_div_le (A B H : ℕ) (hH : 0 < H) : A / H + B / H ≤ (A + B) / H := by
  rw [Nat.le_div_iff_mul_le hH]
  have hA := Nat.div_add_mod A H
  have hB := Nat.div_add_mod B H
  rw [add_mul]
  rw [mul_comm (A / H) H, mul_comm (B / H) H]
  omega

lemma sum_div_le_div_sum (H : ℕ) (hH : 0 < H) (f : ℕ → ℕ) (n : ℕ) :
    ∑ k ∈ range n, (f k / H) ≤ (∑ k ∈ range n, f k) / H := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ]
    have h_le := div_add_div_le (∑ k ∈ range n, f k) (f n) H hH
    omega


lemma div_mod_relation (H X : ℕ) (hH : 0 < H) :
    4 * (X / (4 * H)) + (X / H) % 4 = X / H := by
  have h_div : X / (4 * H) = (X / H) / 4 := by
    have : 4 * H = H * 4 := by ring
    rw [this, Nat.div_div_eq_div_mul]
  rw [h_div]
  exact Nat.div_add_mod (X / H) 4

lemma div_mod_four_eq_mod_div_four (H X : ℕ) (hH : 0 < H) :
    (X / H) % 4 = (X % (4 * H)) / H := by
  have h_id : X = H * 4 * (X / (4 * H)) + X % (4 * H) := by
    have h1 := Nat.div_add_mod X (4 * H)
    have h2 : 4 * H * (X / (4 * H)) = H * 4 * (X / (4 * H)) := by ring
    rw [h2] at h1
    exact h1.symm
  have h_div_H : X / H = 4 * (X / (4 * H)) + (X % (4 * H)) / H := by
    conv_lhs => rw [h_id]
    rw [Nat.add_comm]
    have h_mul_comm : H * 4 * (X / (4 * H)) = H * (4 * (X / (4 * H))) := by ring
    rw [h_mul_comm]
    rw [Nat.add_mul_div_left _ _ hH]
    omega
  have h_relation := div_mod_relation H X hH
  omega


lemma mod_two_m_identity (m X : ℕ) (hm : 0 < m) :
    X % (2 * m) = X % m + m * ((X / m) % 2) := by
  have h_div : X / m = 2 * ((X / m) / 2) + (X / m) % 2 := (Nat.div_add_mod (X / m) 2).symm
  have h_mul : 2 * m = m * 2 := by ring
  have h_id : X = 2 * m * (X / (2 * m)) + X % (2 * m) := (Nat.div_add_mod X (2 * m)).symm
  have h_id2 : X = m * (X / m) + X % m := (Nat.div_add_mod X m).symm
  have h_div_eq : X / (2 * m) = (X / m) / 2 := by
    rw [h_mul, Nat.div_div_eq_div_mul]
  have h_calc : X = 2 * m * (X / (2 * m)) + m * ((X / m) % 2) + X % m := by
    have h_rw1 : m * (X / m) = m * (2 * ((X / m) / 2) + (X / m) % 2) := congr_arg (fun x => m * x) h_div
    have h_rw2 : m * (2 * ((X / m) / 2) + (X / m) % 2) = 2 * m * ((X / m) / 2) + m * ((X / m) % 2) := by ring
    nth_rw 1 [h_id2]
    rw [h_rw1, h_rw2, ← h_div_eq]
  omega

lemma sum_split_even_odd (H : ℕ) (f : ℕ → ℕ) :
    ∑ k ∈ range (2 * H + 1), f k = f 0 + ∑ k ∈ range H, f (k + 1) + ∑ k ∈ range H, f (2 * H - k) := by
  have h1 : ∑ k ∈ range (2 * H + 1), f k = f 0 + ∑ k ∈ range (2 * H), f (k + 1) := by
    rw [sum_range_succ', add_comm]
  rw [h1]
  have h2 : ∑ k ∈ range (2 * H), f (k + 1) = (∑ k ∈ range H, f (k + 1)) + ∑ k ∈ range H, f (H + k + 1) := by
    have h_eq : 2 * H = H + H := by ring
    nth_rw 1 [h_eq]
    exact Finset.sum_range_add (fun k => f (k + 1)) H H
  rw [h2]
  have h_reflect : ∑ k ∈ range H, f (H + k + 1) = ∑ k ∈ range H, f (2 * H - k) := by
    have h_reflect_lemma := my_sum_range_reflect H (fun k => f (H + k + 1))
    have h_eq : ∀ k ∈ range H, H + (H - 1 - k) + 1 = 2 * H - k := by
      intro k hk
      have : k < H := mem_range.mp hk
      omega
    have h_congr : ∑ k ∈ range H, f (H + (H - 1 - k) + 1) = ∑ k ∈ range H, f (2 * H - k) := by
      apply sum_congr rfl
      intro k hk
      rw [h_eq k hk]
    rw [h_congr] at h_reflect_lemma
    exact h_reflect_lemma.symm
  rw [h_reflect]
  omega

lemma mod_sq_sub_self (n k : ℕ) (hk : k < n) : (n - k) ^ 2 % n = k ^ 2 % n := by
  have h_le : k ≤ n := Nat.le_of_lt hk
  set d := n - k
  have h_eq : n = d + k := (Nat.sub_add_cancel h_le).symm
  have h_id : d ^ 2 + (d + k) * k = k ^ 2 + (d + k) * d := by
    ring
  have h_mod : (d ^ 2 + (d + k) * k) % (d + k) = (k ^ 2 + (d + k) * d) % (d + k) := by
    rw [h_id]
  rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left] at h_mod
  rw [← h_eq] at h_mod
  exact h_mod

lemma pair_sum_odd (H k : ℕ) (hk : 2 * k ≤ 2 * H + 1) :
    (k ^ 2 / (2 * H + 1)) % 2 + ((2 * H + 1 - k) ^ 2 / (2 * H + 1)) % 2 = 1 := sorry

lemma remainder_odd_exact (H : ℕ) :
    ∑ k ∈ range (2 * H + 1), k ^ 2 % (4 * H + 2) = A048153 (2 * H + 1) + H * (2 * H + 1) := by
  have h_split1 := sum_split_even_odd H (fun k => k ^ 2 % (4 * H + 2))
  have h_split2 := sum_split_even_odd H (fun k => k ^ 2 % (2 * H + 1))
  have h0 : (0 ^ 2 % (4 * H + 2)) = 0 := by simp
  have h0' : (0 ^ 2 % (2 * H + 1)) = 0 := by simp
  have h_term_eq : ∀ k ∈ range H, (2 * H - k) ^ 2 % (2 * H + 1) = (k + 1) ^ 2 % (2 * H + 1) := by
    intro k hk
    have : k < H := mem_range.mp hk
    have h_eq : 2 * H - k = 2 * H + 1 - (k + 1) := by omega
    rw [h_eq]
    exact mod_sq_sub_self (2 * H + 1) (k + 1) (by omega)
  have h_congr_split2 : ∑ k ∈ range H, (2 * H - k) ^ 2 % (2 * H + 1) = ∑ k ∈ range H, (k + 1) ^ 2 % (2 * H + 1) := by
    apply sum_congr rfl h_term_eq
  have h_A_eq : A048153 (2 * H + 1) = 2 * ∑ k ∈ range H, (k + 1) ^ 2 % (2 * H + 1) := by
    unfold A048153
    rw [h_split2]
    rw [h0', zero_add, h_congr_split2]
    ring
  rw [h_split1]
  rw [h0, zero_add]
  have h_pair : ∀ k ∈ range H, (k + 1) ^ 2 % (4 * H + 2) + (2 * H - k) ^ 2 % (4 * H + 2) =
      2 * ((k + 1) ^ 2 % (2 * H + 1)) + (2 * H + 1) := by
    intro k hk
    have : k < H := mem_range.mp hk
    have h_eq : 2 * H - k = 2 * H + 1 - (k + 1) := by omega
    have h_eq_mul : 4 * H + 2 = 2 * (2 * H + 1) := by ring
    rw [h_eq_mul, h_eq]
    have h_id := mod_two_m_identity (2 * H + 1) ((k + 1) ^ 2) (by omega)
    have h_id2 := mod_two_m_identity (2 * H + 1) ((2 * H + 1 - (k + 1)) ^ 2) (by omega)
    have h_mod_eq : (2 * H + 1 - (k + 1)) ^ 2 % (2 * H + 1) = (k + 1) ^ 2 % (2 * H + 1) := mod_sq_sub_self (2 * H + 1) (k + 1) (by omega)
    have h_sum_mod : ((k + 1) ^ 2 / (2 * H + 1)) % 2 + ((2 * H + 1 - (k + 1)) ^ 2 / (2 * H + 1)) % 2 = 1 := pair_sum_odd H (k + 1) (by omega)
    rw [h_id, h_id2, h_mod_eq]
    rw [show (k + 1) ^ 2 % (2 * H + 1) + (2 * H + 1) * ((k + 1) ^ 2 / (2 * H + 1) % 2) + ((k + 1) ^ 2 % (2 * H + 1) + (2 * H + 1) * ((2 * H + 1 - (k + 1)) ^ 2 / (2 * H + 1) % 2)) =
              2 * ((k + 1) ^ 2 % (2 * H + 1)) + (2 * H + 1) * (((k + 1) ^ 2 / (2 * H + 1)) % 2 + ((2 * H + 1 - (k + 1)) ^ 2 / (2 * H + 1)) % 2) by ring]
    rw [h_sum_mod]
    ring
  have h_sum : ∑ k ∈ range H, ((k + 1) ^ 2 % (4 * H + 2) + (2 * H - k) ^ 2 % (4 * H + 2)) =
      ∑ k ∈ range H, (2 * ((k + 1) ^ 2 % (2 * H + 1)) + (2 * H + 1)) := sum_congr rfl h_pair
  rw [← sum_add_distrib]
  rw [h_sum]
  rw [h_A_eq]
  rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
  rw [← mul_sum]
  rfl
