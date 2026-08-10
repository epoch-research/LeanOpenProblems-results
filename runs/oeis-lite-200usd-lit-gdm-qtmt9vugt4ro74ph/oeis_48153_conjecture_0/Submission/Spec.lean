import FormalConjectures.Util.ProblemImports
open Finset


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

lemma div_sq_sub_self (n k : ℕ) (hn : 0 < n) (hk : 2 * k ≤ n) : (n - k) ^ 2 / n = n - 2 * k + k ^ 2 / n := by
  have h_le : k ≤ n := by omega
  have h_mod : (n - k) ^ 2 % n = k ^ 2 % n := mod_sq_sub_self n k (by omega)
  have h_div_1 : (n - k) ^ 2 = (n - k) ^ 2 / n * n + (n - k) ^ 2 % n := by
    nth_rw 1 [mul_comm]
    exact (Nat.div_add_mod ((n - k) ^ 2) n).symm
  have h_div_2 : k ^ 2 = k ^ 2 / n * n + k ^ 2 % n := by
    nth_rw 1 [mul_comm]
    exact (Nat.div_add_mod (k ^ 2) n).symm
  have h_id : (n - k) ^ 2 + 2 * n * k = n ^ 2 + k ^ 2 := by
    set d := n - k
    have h_eq : n = d + k := (Nat.sub_add_cancel h_le).symm
    rw [h_eq]
    ring
  have h_combined : ((n - k) ^ 2 / n * n + (n - k) ^ 2 % n) + 2 * n * k = n ^ 2 + (k ^ 2 / n * n + k ^ 2 % n) := by
    rw [← h_div_1, ← h_div_2, h_id]
  have h_sub : ((n - k) ^ 2 / n * n) + 2 * n * k = n ^ 2 + (k ^ 2 / n * n) := by
    omega
  have h_factor : ((n - k) ^ 2 / n + 2 * k) * n = (n + k ^ 2 / n) * n := by
    calc
      ((n - k) ^ 2 / n + 2 * k) * n = (n - k) ^ 2 / n * n + 2 * n * k := by ring
      _ = n ^ 2 + k ^ 2 / n * n := h_sub
      _ = (n + k ^ 2 / n) * n := by ring
  have h_cancel : (n - k) ^ 2 / n + 2 * k = n + k ^ 2 / n := Nat.eq_of_mul_eq_mul_right hn h_factor
  omega


lemma mod_sum_identity (n k : ℕ) :
    k ^ 2 % n + (n - k) ^ 2 % n = k ^ 2 + (n - k) ^ 2 - (k ^ 2 / n + (n - k) ^ 2 / n) * n := by
  have h_div_1 : (n - k) ^ 2 = (n - k) ^ 2 / n * n + (n - k) ^ 2 % n := by
    nth_rw 1 [mul_comm]
    exact (Nat.div_add_mod ((n - k) ^ 2) n).symm
  have h_div_2 : k ^ 2 = k ^ 2 / n * n + k ^ 2 % n := by
    nth_rw 1 [mul_comm]
    exact (Nat.div_add_mod (k ^ 2) n).symm
  rw [add_mul]
  omega





lemma le_bound (n : ℕ) (h : 1 ≤ n) : n * (n - 1) / 2 ≤ (n ^ 2 - 1) / 2 := by
  have h_eq : n * (n - 1) = n ^ 2 - n := by
    rw [Nat.mul_sub_left_distrib, mul_one, ← pow_two]
  rw [h_eq]
  omega


lemma sum_range_sq_subtraction_free (m : ℕ) :
    6 * (∑ k ∈ range (m + 1), k ^ 2) = m * (m + 1) * (2 * m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, mul_add, ih]
    ring

def A048153 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

lemma a048153_identity (n : ℕ) :
    A048153 n + n * (∑ k ∈ range n, k ^ 2 / n) = ∑ k ∈ range n, k ^ 2 := by
  unfold A048153
  rw [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro k hk
  rw [add_comm]
  exact Nat.div_add_mod (k ^ 2) n


lemma div_ge_mul (m i : ℕ) (hm : 0 < m) (hi : i ≤ m) : 2 * i ≤ (m + i) ^ 2 / (2 * m) := by
  have hm' : 0 < 2 * m := by omega
  rw [Nat.le_div_iff_mul_le hm']
  have h_id : (m + i) ^ 2 = (m - i) ^ 2 + 4 * m * i := by
    zify [hi]
    ring
  rw [h_id]
  have h_mul : 2 * i * (2 * m) = 4 * m * i := by ring
  rw [h_mul]
  omega


lemma div_ge_mul_odd (m i : ℕ) (hi : i ≤ m) : 2 * i ≤ (m + i) ^ 2 / (2 * m + 1) + 1 := by
  by_cases hi0 : i = 0
  · subst hi0; simp
  have hi_pos : 0 < i := Nat.pos_of_ne_zero hi0
  have h_le : 2 * i - 1 ≤ (m + i) ^ 2 / (2 * m + 1) := by
    have hm : 0 < 2 * m + 1 := by omega
    rw [Nat.le_div_iff_mul_le hm]
    have h_i1 : 1 ≤ 2 * i := by omega
    have h_id : (m + i) ^ 2 = (m - i + 1) ^ 2 + (2 * i - 1) * (2 * m + 1) := by
      zify [hi, h_i1]
      ring
    rw [h_id]
    omega
  omega

lemma div_ge_mul_lower (m k : ℕ) (hk : k < m) (hm : 2 ≤ m) : 4 * k ≤ 2 * (k ^ 2 / (2 * m)) + 3 * m := by
  by_cases h_cases : 4 * k ≤ 3 * m
  · omega
  push_neg at h_cases
  have hm0 : 0 < 2 * m := by omega
  have h_sub_cast : ((m - k : ℕ) : ℤ) = (m : ℤ) - (k : ℤ) := by omega
  have h_sq : 4 * m * k + m ≤ k ^ 2 + 3 * m ^ 2 := by
    have h_id_z : (((k ^ 2 + 3 * m ^ 2 : ℕ) : ℤ)) = (((m - k) ^ 2 + 2 * m ^ 2 + 2 * m * k : ℕ) : ℤ) := by
      push_cast
      rw [h_sub_cast]
      ring
    have h_id : k ^ 2 + 3 * m ^ 2 = (m - k) ^ 2 + 2 * m ^ 2 + 2 * m * k := by exact_mod_cast h_id_z
    rw [h_id]
    have h_m2 : 2 * m * k + m ≤ 2 * m ^ 2 := by
      have : 2 * k + 1 ≤ 2 * m := by omega
      calc
        2 * m * k + m = (2 * k + 1) * m := by ring
        _ ≤ (2 * m) * m := Nat.mul_le_mul_right m this
        _ = 2 * m ^ 2 := by ring
    calc
      4 * m * k + m = 2 * m * k + (2 * m * k + m) := by ring
      _ ≤ 2 * m * k + 2 * m ^ 2 := Nat.add_le_add_left h_m2 _
      _ = 2 * m ^ 2 + 2 * m * k := by ring
      _ ≤ (m - k) ^ 2 + 2 * m ^ 2 + 2 * m * k := by omega
  have h_le : (4 * k - 3 * m + 1) / 2 ≤ k ^ 2 / (2 * m) := by
    rw [Nat.le_div_iff_mul_le hm0]
    have h_div : (4 * k - 3 * m + 1) / 2 * (2 * m) ≤ (4 * k - 3 * m + 1) * m := by
      have h_div_le : (4 * k - 3 * m + 1) / 2 * 2 ≤ 4 * k - 3 * m + 1 := Nat.div_mul_le_self _ 2
      calc
        (4 * k - 3 * m + 1) / 2 * (2 * m) = (4 * k - 3 * m + 1) / 2 * 2 * m := by ring
        _ ≤ (4 * k - 3 * m + 1) * m := Nat.mul_le_mul_right m h_div_le
    have h_trans : (4 * k - 3 * m + 1) * m ≤ k ^ 2 := by
      have h_sub_cast2 : ((4 * k - 3 * m : ℕ) : ℤ) = 4 * (k : ℤ) - 3 * (m : ℤ) := by omega
      have h_sq_z : 4 * (m : ℤ) * (k : ℤ) + (m : ℤ) ≤ (k : ℤ) ^ 2 + 3 * (m : ℤ) ^ 2 := by
        exact_mod_cast h_sq
      have h_trans_z : (((4 * k - 3 * m + 1) * m : ℕ) : ℤ) ≤ ((k ^ 2 : ℕ) : ℤ) := by
        push_cast
        rw [h_sub_cast2]
        linarith
      exact_mod_cast h_trans_z
    omega
  have h_final : 4 * k - 3 * m ≤ 2 * (k ^ 2 / (2 * m)) := by
    have h_div2 : (4 * k - 3 * m + 1) / 2 * 2 ≤ k ^ 2 / (2 * m) * 2 := Nat.mul_le_mul_right 2 h_le
    rw [mul_comm (k ^ 2 / (2 * m)) 2] at h_div2
    have h_div3 : 4 * k - 3 * m ≤ (4 * k - 3 * m + 1) / 2 * 2 := by omega
    omega
  omega




lemma Q_bound_implies_A048153_bound (n : ℕ) (h_n : 2 ≤ n)
    (h_Q : (n - 1) * (n - 2) ≤ 3 * (∑ k ∈ range n, k ^ 2 / n)) :
    A048153 n ≤ n * (n - 1) / 2 := by
  have h_n1 : n = n - 1 + 1 := (Nat.sub_add_cancel (by omega)).symm
  have h_sum := a048153_identity n
  have h_sum6 : 6 * A048153 n + 6 * (n * (∑ k ∈ range n, k ^ 2 / n)) = 6 * (∑ k ∈ range n, k ^ 2) := by
    omega
  have h_sum_range : 6 * (∑ k ∈ range n, k ^ 2) = (n - 1) * n * (2 * n - 1) := by
    have h_eq : ∑ k ∈ range n, k ^ 2 = ∑ k ∈ range (n - 1 + 1), k ^ 2 := congrArg (fun x => ∑ k ∈ range x, k ^ 2) h_n1
    rw [h_eq, sum_range_sq_subtraction_free (n - 1)]
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 + m := Nat.exists_eq_add_of_le h_n
    have h1 : 2 + m - 1 = m + 1 := by omega
    have h2 : 2 * (2 + m) - 1 = 2 * m + 3 := by omega
    rw [h1, h2]
    ring
  have h_sum6_eq : 6 * A048153 n + 2 * n * (3 * (∑ k ∈ range n, k ^ 2 / n)) = (n - 1) * n * (2 * n - 1) := by
    calc
      6 * A048153 n + 2 * n * (3 * (∑ k ∈ range n, k ^ 2 / n)) = 6 * A048153 n + 6 * (n * (∑ k ∈ range n, k ^ 2 / n)) := by ring
      _ = 6 * (∑ k ∈ range n, k ^ 2) := h_sum6
      _ = (n - 1) * n * (2 * n - 1) := h_sum_range
  have h_D_le_B : 2 * n * ((n - 1) * (n - 2)) ≤ 2 * n * (3 * (∑ k ∈ range n, k ^ 2 / n)) := by
    gcongr
  have h_C_eq_E_D : (n - 1) * n * (2 * n - 1) = 3 * n * (n - 1) + 2 * n * ((n - 1) * (n - 2)) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 + m := Nat.exists_eq_add_of_le h_n
    have h1 : 2 + m - 1 = m + 1 := by omega
    have h2 : 2 * (2 + m) - 1 = 2 * m + 3 := by omega
    have h3 : 2 + m - 2 = m := by omega
    rw [h1, h2, h3]
    ring
  have h_6A_le : 6 * A048153 n ≤ 3 * n * (n - 1) := by
    omega
  have h_div : (6 * A048153 n) / 6 ≤ (3 * n * (n - 1)) / 6 := Nat.div_le_div_right h_6A_le
  have h_cancel1 : (6 * A048153 n) / 6 = A048153 n := Nat.mul_div_cancel_left _ (by decide)
  have h_cancel2 : (3 * n * (n - 1)) / 6 = n * (n - 1) / 2 := by
    have h_even : ∃ m, n * (n - 1) = 2 * m := by
      rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
      · use k * (n - 1)
        have hk2 : n = 2 * k := by omega
        rw [hk2]
        rw [mul_assoc]
      · use n * k
        have hk2 : n = 2 * k + 1 := by omega
        rw [hk2]
        have h_sub : 2 * k + 1 - 1 = 2 * k := by omega
        rw [h_sub]
        ring
    rcases h_even with ⟨m, hm⟩
    have h1 : 3 * n * (n - 1) = 6 * m := by
      calc
        3 * n * (n - 1) = 3 * (n * (n - 1)) := by ring
        _ = 3 * (2 * m) := by rw [hm]
        _ = 6 * m := by ring
    have h2 : n * (n - 1) = 2 * m := hm
    rw [h1, h2]
    have h3 : 6 * m / 6 = m := Nat.mul_div_cancel_left m (by decide)
    have h4 : 2 * m / 2 = m := Nat.mul_div_cancel_left m (by decide)
    rw [h3, h4]
  rw [h_cancel1, h_cancel2] at h_div
  exact h_div



lemma pointwise_bound_general (a : ℕ) (n k : ℕ) (hk : k < n) (ha : 2 ≤ a) :
    a * k * n ≤ k ^ 2 + (a - 1) * n ^ 2 := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  have hb : 1 ≤ b := by omega
  have h_sub_eq : b + 1 - 1 = b := by omega
  rw [h_sub_eq]
  have hd : ∃ d, n = k + d := ⟨n - k, by omega⟩
  rcases hd with ⟨d, rfl⟩
  have hd0 : 0 < d := by omega
  have h_mul : (b + 1) * k * (k + d) = (b + 1) * k ^ 2 + (b + 1) * k * d := by ring
  have h_sq : k ^ 2 + b * (k + d) ^ 2 = (b + 1) * k ^ 2 + b * (2 * k * d) + b * d ^ 2 := by ring
  rw [h_mul, h_sq]
  have h_le : (b + 1) * k * d ≤ b * (2 * k * d) := by
    calc
      (b + 1) * k * d = (b + 1) * k * d := by ring
      _ ≤ (2 * b) * k * d := by
        gcongr
        omega
      _ = b * (2 * k * d) := by ring
  omega

lemma mod_sq_le_half (n k : ℕ) (hk : k < n) :
    k ^ 2 % n ≤ if k < (n + 1) / 2 then k ^ 2 else (n - k) ^ 2 := by
  split_ifs with h
  · exact Nat.mod_le _ _
  · have h_eq := mod_sq_sub_self n k hk
    rw [← h_eq]
    exact Nat.mod_le _ _


lemma sum_range_id_mul_two (m : ℕ) : 2 * (∑ i ∈ range m, i) = m * (m - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, mul_add, ih]
    rcases m with _ | m
    · simp
    · have h_eq1 : m + 1 - 1 = m := by omega
      have h_eq2 : m + 2 - 1 = m + 1 := by omega
      rw [h_eq1, h_eq2]
      ring


set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
lemma spec_cases_1 : ∀ n, 1 ≤ n → n ≤ 200 → A048153 n ≤ (n ^ 2 - 1) / 2 := by
  decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
lemma spec_cases_2 : ∀ n, 201 ≤ n → n ≤ 400 → A048153 n ≤ (n ^ 2 - 1) / 2 := by
  decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
lemma spec_cases_3 : ∀ n, 401 ≤ n → n ≤ 600 → A048153 n ≤ (n ^ 2 - 1) / 2 := by
  decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
lemma spec_cases_4 : ∀ n, 601 ≤ n → n ≤ 800 → A048153 n ≤ (n ^ 2 - 1) / 2 := by
  decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
lemma spec_cases_5 : ∀ n, 801 ≤ n → n ≤ 1000 → A048153 n ≤ (n ^ 2 - 1) / 2 := by
  decide

lemma spec_cases_all : ∀ n, 1 ≤ n → n ≤ 1000 → A048153 n ≤ (n ^ 2 - 1) / 2 := by
  intro n h1 h2
  rcases lt_or_ge n 201 with hn | hn
  · exact spec_cases_1 n h1 (by omega)
  · rcases lt_or_ge n 401 with hn2 | hn2
    · exact spec_cases_2 n hn (by omega)
    · rcases lt_or_ge n 601 with hn3 | hn3
      · exact spec_cases_3 n hn2 (by omega)
      · rcases lt_or_ge n 801 with hn4 | hn4
        · exact spec_cases_4 n hn3 (by omega)
        · exact spec_cases_5 n hn4 (by omega)



lemma m_sq_div_two_m (m : ℕ) : m ^ 2 / (2 * m) = m / 2 := by
  rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · -- m = k + k
    by_cases hk : k = 0
    · subst hk; simp
    · have h_pos : 0 < k + k := by omega
      have h_pos2 : 0 < 2 * (k + k) := by omega
      have h_eq : (k + k) ^ 2 = k * (2 * (k + k)) := by ring
      rw [h_eq]
      rw [Nat.mul_div_cancel k h_pos2]
      have : (k + k) / 2 = k := by omega
      rw [this]
  · -- m = 2 * k + 1
    have h_pos : 0 < 2 * (2 * k + 1) := by omega
    have h_eq1 : (2 * k + 1) ^ 2 = (2 * k + 1) + k * (2 * (2 * k + 1)) := by ring
    have h_eq2 : (2 * k + 1) / 2 = k := by omega
    rw [h_eq1]
    rw [Nat.add_mul_div_right _ _ h_pos]
    have h_zero : (2 * k + 1) / (2 * (2 * k + 1)) = 0 := by
      apply Nat.div_eq_of_lt
      omega
    rw [h_zero, zero_add, h_eq2]

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

lemma sum_second_half_eq (m : ℕ) (hm : 1 ≤ m) :
    ∑ k ∈ range m, (m + k) ^ 2 / (2 * m) = m * (m - 1) + m / 2 + ∑ k ∈ range (m - 1), (k + 1) ^ 2 / (2 * m) := by
  have hm0 : 0 < m := hm
  have h_m1 : m = m - 1 + 1 := (Nat.sub_add_cancel hm).symm
  nth_rw 1 [h_m1]
  rw [sum_range_succ']
  have h_m0 : (m + 0) ^ 2 / (2 * m) = m / 2 := by
    rw [add_zero]
    exact m_sq_div_two_m m
  rw [h_m0]
  have h_terms : ∀ k ∈ range (m - 1), (m + (k + 1)) ^ 2 / (2 * m) = 2 * (k + 1) + (m - (k + 1)) ^ 2 / (2 * m) := by
    intro k hk
    have hk_lt : k < m - 1 := mem_range.mp hk
    have hk1_lt : k + 1 < m := by omega
    have hj : m - (k + 1) ≤ m := by omega
    have hj_le : 2 * (m - (k + 1)) ≤ 2 * m := by omega
    have h_sub := div_sq_sub_self (2 * m) (m - (k + 1)) (by omega) hj_le
    have h_eq1 : 2 * m - (m - (k + 1)) = m + (k + 1) := by omega
    have h_eq2 : 2 * m - 2 * (m - (k + 1)) = 2 * (k + 1) := by omega
    rw [h_eq1, h_eq2] at h_sub
    exact h_sub
  have h_sum : ∑ k ∈ range (m - 1), (m + (k + 1)) ^ 2 / (2 * m) = ∑ k ∈ range (m - 1), (2 * (k + 1) + (m - (k + 1)) ^ 2 / (2 * m)) := by
    apply sum_congr rfl
    intro k hk
    exact h_terms k hk
  rw [h_sum]
  rw [sum_add_distrib]
  have h_sum_2k : ∑ k ∈ range (m - 1), 2 * (k + 1) = m * (m - 1) := by
    have h1 := sum_range_succ' (fun k => 2 * k) (m - 1)
    have h_eq : m - 1 + 1 = m := by omega
    rw [h_eq] at h1
    simp only [mul_zero, add_zero] at h1
    rw [← h1]
    rw [← mul_sum]
    rw [_root_.sum_range_id_mul_two]
  rw [h_sum_2k]
  have h_reflect : ∑ k ∈ range (m - 1), (m - (k + 1)) ^ 2 / (2 * m) = ∑ k ∈ range (m - 1), (k + 1) ^ 2 / (2 * m) := by
    have h_reflect_lemma := my_sum_range_reflect (m - 1) (fun k => (k + 1) ^ 2 / (2 * m))
    have h_eq : ∀ k ∈ range (m - 1), m - 1 - 1 - k + 1 = m - (k + 1) := by
      intro k hk
      have : k < m - 1 := mem_range.mp hk
      omega
    have h_congr : ∑ k ∈ range (m - 1), (m - 1 - 1 - k + 1) ^ 2 / (2 * m) = ∑ k ∈ range (m - 1), (m - (k + 1)) ^ 2 / (2 * m) := by
      apply sum_congr rfl
      intro k hk
      rw [h_eq k hk]
    rw [← h_congr]
    exact h_reflect_lemma
  rw [h_reflect]
  generalize h_S : ∑ k ∈ range (m - 1), (k + 1) ^ 2 / (2 * m) = S
  omega





lemma div_ge_linear_even (H k : ℕ) (hH : 0 < H) : 2 * k - 2 * H ≤ 2 * (k ^ 2 / (4 * H)) := by
  rcases lt_or_ge k (2 * H) with hk2 | hk2
  · -- k < 2 * H
    by_cases hk1 : k < H
    · have : 2 * k ≤ 2 * H := by omega
      have : 2 * k - 2 * H = 0 := Nat.sub_eq_zero_of_le this
      rw [this]
      exact Nat.zero_le _
    · push_neg at hk1
      obtain ⟨d, rfl⟩ : ∃ d, k = H + d := Nat.exists_eq_add_of_le hk1
      have hd : d < H := by omega
      have h_sq : 2 * H * d ≤ H ^ 2 + d ^ 2 := by
        have : (2 * H * d : ℤ) ≤ H ^ 2 + d ^ 2 := by
          have : 0 ≤ ((H : ℤ) - (d : ℤ)) ^ 2 := sq_nonneg _
          linarith
        exact_mod_cast this
      have h_mul_le : d * (4 * H) ≤ (H + d) ^ 2 := by
        calc
          d * (4 * H) = 4 * H * d := by ring
          _ = 2 * H * d + 2 * H * d := by ring
          _ ≤ 2 * H * d + (H ^ 2 + d ^ 2) := Nat.add_le_add_left h_sq _
          _ = (H + d) ^ 2 := by ring
      have h_div : d ≤ (H + d) ^ 2 / (4 * H) := by
        rw [Nat.le_div_iff_mul_le (by omega)]
        exact h_mul_le
      omega
  · obtain ⟨d, rfl⟩ : ∃ d, k = 2 * H + d := Nat.exists_eq_add_of_le hk2
    have h_sq_eq : (2 * H + d) ^ 2 = 4 * H * (H + d) + d ^ 2 := by ring
    have h_mod : (2 * H + d) ^ 2 % (4 * H) = d ^ 2 % (4 * H) := by
      rw [h_sq_eq, add_comm]
      exact Nat.add_mul_mod_self_left (d ^ 2) (4 * H) (H + d)
    have h_div_mul : (2 * H + d) ^ 2 / (4 * H) * (4 * H) = (2 * H + d) ^ 2 - (2 * H + d) ^ 2 % (4 * H) := by
      generalize h_div : (2 * H + d) ^ 2 / (4 * H) * (4 * H) = Q_var
      generalize h_mod : (2 * H + d) ^ 2 % (4 * H) = R_var
      have h_div_add := Nat.div_add_mod ((2 * H + d) ^ 2) (4 * H)
      rw [mul_comm (4 * H)] at h_div_add
      rw [h_div, h_mod] at h_div_add
      omega
    have h_le : (2 * (2 * H + d) - 2 * H) * (2 * H) ≤ 2 * ((2 * H + d) ^ 2 / (4 * H)) * (2 * H) := by
      have h_lhs : (2 * (2 * H + d) - 2 * H) * (2 * H) = 4 * H ^ 2 + 4 * H * d := by
        have : 2 * (2 * H + d) - 2 * H = 2 * H + 2 * d := by omega
        rw [this]
        ring
      have h_rhs : 2 * ((2 * H + d) ^ 2 / (4 * H)) * (2 * H) = (2 * H + d) ^ 2 / (4 * H) * (4 * H) := by ring
      have h_sq_eq2 : 4 * H * (H + d) + d ^ 2 = 4 * H ^ 2 + 4 * H * d + d ^ 2 := by ring
      rw [h_lhs, h_rhs, h_div_mul, h_mod, h_sq_eq, h_sq_eq2]
      have h_mod_le : d ^ 2 % (4 * H) ≤ d ^ 2 := Nat.mod_le _ _
      omega
    exact Nat.le_of_mul_le_mul_right h_le (by omega)

lemma mod_sq_shift (H k : ℕ) : (2 * H + k) ^ 2 % (4 * H) = k ^ 2 % (4 * H) := by
  have h_eq : (2 * H + k) ^ 2 = 4 * H * (H + k) + k ^ 2 := by ring
  rw [h_eq, add_comm]
  exact Nat.add_mul_mod_self_left (k ^ 2) (4 * H) (H + k)

lemma a048153_even_identity (H : ℕ) :
    A048153 (4 * H) + 8 * H * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) = 2 * (∑ k ∈ range (2 * H), k ^ 2) := by
  unfold A048153
  have h_split := Finset.sum_range_add (fun k => k ^ 2 % (4 * H)) (2 * H) (2 * H)
  have h_eq : 4 * H = 2 * H + 2 * H := by ring
  rw [← h_eq] at h_split
  rw [h_split]
  have h_second : ∑ k ∈ range (2 * H), (2 * H + k) ^ 2 % (4 * H) = ∑ k ∈ range (2 * H), k ^ 2 % (4 * H) := by
    apply sum_congr rfl
    intro k hk
    exact mod_sq_shift H k
  rw [h_second]
  have h_two_sum : ∑ k ∈ range (2 * H), k ^ 2 % (4 * H) + ∑ k ∈ range (2 * H), k ^ 2 % (4 * H) = 2 * ∑ k ∈ range (2 * H), k ^ 2 % (4 * H) := by omega
  rw [h_two_sum]
  have h_8H : 8 * H * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) = 2 * (4 * H * ∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) := by ring
  rw [h_8H]
  rw [← mul_add]
  have h_sum_eq : ∑ k ∈ range (2 * H), k ^ 2 % (4 * H) + (4 * H) * ∑ k ∈ range (2 * H), k ^ 2 / (4 * H) = ∑ k ∈ range (2 * H), k ^ 2 := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro k hk
    rw [mul_comm]
    exact Nat.mod_add_div (k ^ 2) (H * 4)
  rw [h_sum_eq]

lemma div_ge_linear_odd (H k : ℕ) (hH : 0 < H) : 2 * k - (2 * H + 2) ≤ 2 * (k ^ 2 / (4 * H + 2)) := by
  by_cases hk : k < H + 1
  · have : 2 * k ≤ 2 * H + 2 := by omega
    have : 2 * k - (2 * H + 2) = 0 := Nat.sub_eq_zero_of_le this
    rw [this]
    exact Nat.zero_le _
  · push_neg at hk
    have hm2 : 0 < 4 * H + 2 := by omega
    have h_le_div : k - (H + 1) ≤ k ^ 2 / (4 * H + 2) := by
      rw [Nat.le_div_iff_mul_le hm2]
      have h_le : (k - (H + 1)) * (4 * H + 2) ≤ k ^ 2 := by
        have : ( ((k - (H + 1)) * (4 * H + 2) : ℕ) : ℤ ) ≤ (k : ℤ) ^ 2 := by
          have h_sub_cast : ((k - (H + 1) : ℕ) : ℤ) = (k : ℤ) - ((H : ℤ) + 1) := by omega
          push_cast
          rw [h_sub_cast]
          have : 0 ≤ ( (k : ℤ) - (2 * H + 1) ) ^ 2 := sq_nonneg _
          linarith
        exact_mod_cast this
      exact h_le
    have h_mul_two : 2 * (k - (H + 1)) = 2 * k - (2 * H + 2) := by omega
    rw [← h_mul_two]
    gcongr

lemma S_even_bound (H : ℕ) (hH : 2 ≤ H) :
    (2 * H) * (2 * H - 1) ≤ 12 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) := by
  have hH_pos : 0 < H := by omega
  have h_sum_le : ∑ k ∈ range (2 * H), (2 * k - 2 * H) ≤ 2 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) := by
    rw [mul_sum]
    apply sum_le_sum
    intro k hk
    exact div_ge_linear_even H k hH_pos
  have h_split : ∑ k ∈ range (2 * H), (2 * k - 2 * H) = H * (H - 1) := by
    have h_split2 := Finset.sum_range_add (fun k => 2 * k - 2 * H) H H
    have h_eq : 2 * H = H + H := by ring
    rw [← h_eq] at h_split2
    rw [h_split2]
    have h_first : ∑ k ∈ range H, (2 * k - 2 * H) = 0 := by
      apply sum_eq_zero
      intro k hk
      have : k < H := mem_range.mp hk
      have : 2 * k ≤ 2 * H := by omega
      exact Nat.sub_eq_zero_of_le this
    have h_second : ∑ k ∈ range H, (2 * (H + k) - 2 * H) = H * (H - 1) := by
      have h_eq2 : ∀ k ∈ range H, 2 * (H + k) - 2 * H = 2 * k := by
        intro k hk
        omega
      have h_congr : ∑ k ∈ range H, (2 * (H + k) - 2 * H) = ∑ k ∈ range H, 2 * k := by
        apply sum_congr rfl
        intro k hk
        exact h_eq2 k hk
      rw [h_congr]
      rw [← mul_sum]
      exact _root_.sum_range_id_mul_two H
    omega
  have h_trans : (2 * H) * (2 * H - 1) ≤ 6 * (∑ k ∈ range (2 * H), (2 * k - 2 * H)) := by
    rw [h_split]
    have h1 : 1 ≤ H := by omega
    have h2 : 1 ≤ 2 * H := by omega
    zify [h1, h2]
    have : 2 ≤ (H : ℤ) := by exact_mod_cast hH
    nlinarith
  calc
    (2 * H) * (2 * H - 1) ≤ 6 * (∑ k ∈ range (2 * H), (2 * k - 2 * H)) := h_trans
    _ ≤ 6 * (2 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H))) := by gcongr
    _ = 12 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) := by ring

lemma S_odd_bound (H : ℕ) (hH : 4 ≤ H) :
    (2 * H + 1) * (2 * H) ≤ 12 * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2)) := by
  have hH_pos : 0 < H := by omega
  have h_sum_le : ∑ k ∈ range (2 * H + 1), (2 * k - (2 * H + 2)) ≤ 2 * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2)) := by
    rw [mul_sum]
    apply sum_le_sum
    intro k hk
    exact div_ge_linear_odd H k hH_pos
  have h_split : ∑ k ∈ range (2 * H + 1), (2 * k - (2 * H + 2)) = H * (H - 1) := by
    have h_split2 := Finset.sum_range_add (fun k => 2 * k - (2 * H + 2)) (H + 1) H
    have h_eq : 2 * H + 1 = H + 1 + H := by ring
    rw [← h_eq] at h_split2
    rw [h_split2]
    have h_first : ∑ k ∈ range (H + 1), (2 * k - (2 * H + 2)) = 0 := by
      apply sum_eq_zero
      intro k hk
      have : k < H + 1 := mem_range.mp hk
      have : 2 * k ≤ 2 * H + 2 := by omega
      exact Nat.sub_eq_zero_of_le this
    have h_second : ∑ k ∈ range H, (2 * (H + 1 + k) - (2 * H + 2)) = H * (H - 1) := by
      have h_eq2 : ∀ k ∈ range H, 2 * (H + 1 + k) - (2 * H + 2) = 2 * k := by
        intro k hk
        omega
      have h_congr : ∑ k ∈ range H, (2 * (H + 1 + k) - (2 * H + 2)) = ∑ k ∈ range H, 2 * k := by
        apply sum_congr rfl
        intro k hk
        exact h_eq2 k hk
      rw [h_congr]
      rw [← mul_sum]
      exact _root_.sum_range_id_mul_two H
    omega
  have h_trans : (2 * H + 1) * (2 * H) ≤ 6 * (∑ k ∈ range (2 * H + 1), (2 * k - (2 * H + 2))) := by
    rw [h_split]
    have h1 : 1 ≤ H := by omega
    zify [h1]
    have : 4 ≤ (H : ℤ) := by exact_mod_cast hH
    nlinarith
  calc
    (2 * H + 1) * (2 * H) ≤ 6 * (∑ k ∈ range (2 * H + 1), (2 * k - (2 * H + 2))) := h_trans
    _ ≤ 6 * (2 * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2))) := by gcongr
    _ = 12 * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2)) := by ring



lemma div_relation (H k : ℕ) : 2 * (k ^ 2 / (4 * H)) + 1 ≥ k ^ 2 / (2 * H) := by
  by_cases hH : H = 0
  · subst hH; simp
  have h_eq : 4 * H = 2 * H * 2 := by ring
  have h_div : k ^ 2 / (4 * H) = (k ^ 2 / (2 * H)) / 2 := by
    rw [h_eq]
    exact (Nat.div_div_eq_div_mul (k ^ 2) (2 * H) 2).symm
  rw [h_div]
  generalize h_x : k ^ 2 / (2 * H) = x
  have h1 : 2 * (x / 2) + x % 2 = x := Nat.div_add_mod x 2
  have h2 : x % 2 < 2 := Nat.mod_lt x (by decide)
  omega

lemma sum_first_half_shift (H : ℕ) :
    ∑ k ∈ range (2 * H), k ^ 2 / (4 * H) = ∑ k ∈ range (2 * H - 1), (k + 1) ^ 2 / (4 * H) := by
  by_cases hH : H = 0
  · subst hH; simp
  have h_eq : 2 * H = 2 * H - 1 + 1 := by omega
  nth_rw 1 [h_eq]
  rw [sum_range_succ']
  simp

lemma Q_even_exact (H : ℕ) (hH : 1 ≤ H) :
    ∑ k ∈ range (4 * H), k ^ 2 / (4 * H) = 2 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + 4 * H ^ 2 - H := by
  have h_split : ∑ k ∈ range (4 * H), k ^ 2 / (4 * H) = ∑ k ∈ range (2 * H), k ^ 2 / (4 * H) + ∑ k ∈ range (2 * H), (2 * H + k) ^ 2 / (4 * H) := by
    have h_eq : 4 * H = 2 * H + 2 * H := by ring
    nth_rw 1 [h_eq]
    exact Finset.sum_range_add (fun k => k ^ 2 / (4 * H)) (2 * H) (2 * H)
  rw [h_split]
  have h_second := sum_second_half_eq (2 * H) (by omega)
  have h_eq2 : 2 * (2 * H) = 4 * H := by ring
  rw [h_eq2] at h_second
  have h_shift := sum_first_half_shift H
  rw [← h_shift] at h_second
  have h_div_two : 2 * H / 2 = H := by omega
  rw [h_div_two] at h_second
  have h_alg : (2 * H) * (2 * H - 1) + H = 4 * H ^ 2 - H := by
    rcases H with _ | H
    · omega
    · have h_sub1 : 2 * (H + 1) - 1 = 2 * H + 1 := by omega
      rw [h_sub1]
      have h_ring : (2 * (H + 1)) * (2 * H + 1) + (H + 1) + (H + 1) = 4 * (H + 1) ^ 2 := by ring
      omega
  rw [h_alg] at h_second
  rw [h_second]
  generalize h_SQ : H ^ 2 = SQ
  generalize (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) = S
  omega


lemma Q_even_odd_exact (H : ℕ) :
    ∑ k ∈ range (4 * H + 2), k ^ 2 / (4 * H + 2) = 2 * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2)) + 4 * H ^ 2 + 3 * H := by
  have h_split : ∑ k ∈ range (4 * H + 2), k ^ 2 / (4 * H + 2) = ∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2) + ∑ k ∈ range (2 * H + 1), (2 * H + 1 + k) ^ 2 / (4 * H + 2) := by
    have h_eq : 4 * H + 2 = 2 * H + 1 + (2 * H + 1) := by omega
    nth_rw 1 [h_eq]
    exact Finset.sum_range_add (fun k => k ^ 2 / (4 * H + 2)) (2 * H + 1) (2 * H + 1)
  rw [h_split]
  have h_second := sum_second_half_eq (2 * H + 1) (by omega)
  have h_eq2 : 2 * (2 * H + 1) = 4 * H + 2 := by ring
  rw [h_eq2] at h_second
  have h_shift : ∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2) = ∑ k ∈ range (2 * H), (k + 1) ^ 2 / (4 * H + 2) := by
    rw [sum_range_succ']
    simp
  have h_sub : 2 * H + 1 - 1 = 2 * H := rfl
  rw [h_sub] at h_second
  rw [← h_shift] at h_second
  have h_div_two : (2 * H + 1) / 2 = H := by omega
  rw [h_div_two] at h_second
  have h_alg : (2 * H + 1) * (2 * H) + H = 4 * H ^ 2 + 3 * H := by ring
  rw [h_alg] at h_second
  rw [h_second]
  ring

lemma Q_relation (H : ℕ) (hH : 1 ≤ H) :
    3 * (∑ k ∈ range (4 * H), k ^ 2 / (4 * H)) ≥ 3 * (∑ k ∈ range (2 * H), k ^ 2 / (2 * H)) + 12 * H ^ 2 - 9 * H := by
  have h_eq : ∑ k ∈ range (4 * H), k ^ 2 / (4 * H) = 2 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + 4 * H ^ 2 - H := Q_even_exact H hH
  have h_div_rel : ∀ k ∈ range (2 * H), 2 * (k ^ 2 / (4 * H)) + 1 ≥ k ^ 2 / (2 * H) := by
    intro k hk
    exact div_relation H k
  have h_sum_le : ∑ k ∈ range (2 * H), (2 * (k ^ 2 / (4 * H)) + 1) ≥ ∑ k ∈ range (2 * H), k ^ 2 / (2 * H) := sum_le_sum h_div_rel
  rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, mul_one] at h_sum_le
  rw [← mul_sum] at h_sum_le
  have h_le3 : 3 * (∑ k ∈ range (2 * H), k ^ 2 / (2 * H)) ≤ 3 * (2 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + 2 * H) := by
    gcongr
    exact h_sum_le
  have h_alg : 3 * (2 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + 2 * H) = 6 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + 6 * H := by ring
  rw [h_alg] at h_le3
  rw [h_eq]
  generalize h_S1 : ∑ k ∈ range (2 * H), k ^ 2 / (4 * H) = S1
  generalize h_S2 : ∑ k ∈ range (2 * H), k ^ 2 / (2 * H) = S2
  generalize h_SQ : H ^ 2 = SQ
  omega

lemma div_ge_linear_simple (n k : ℕ) (hn : 0 < n) (hk : k < n) : 2 * k ≤ k ^ 2 / n + n := by
  have h_mod_eq : k ^ 2 % n = (n - k) ^ 2 % n := (mod_sq_sub_self n k hk).symm
  have h_mod_le : (n - k) ^ 2 % n ≤ (n - k) ^ 2 := Nat.mod_le _ _
  have h_mod_bound : k ^ 2 % n ≤ (n - k) ^ 2 := by omega
  have h_div : (k ^ 2 / n) * n + k ^ 2 % n = k ^ 2 := by
    rw [mul_comm]
    exact Nat.div_add_mod (k ^ 2) n
  have h_le : 2 * k * n ≤ (k ^ 2 / n + n) * n := by
    have h_sq : 2 * k * n + (n - k) ^ 2 = k ^ 2 + n ^ 2 := by
      set d := n - k
      have : n = d + k := (Nat.sub_add_cancel (by omega)).symm
      rw [this]
      ring
    have h_rw : (k ^ 2 / n + n) * n = (k ^ 2 / n) * n + n ^ 2 := by ring
    rw [h_rw]
    omega
  exact Nat.le_of_mul_le_mul_right h_le hn


lemma Q_odd_exact (H : ℕ) :
    ∑ k ∈ range (2 * H + 1), k ^ 2 / (2 * H + 1) = 2 * (∑ k ∈ range (H + 1), k ^ 2 / (2 * H + 1)) + H ^ 2 := by
  have h_split : ∑ k ∈ range (2 * H + 1), k ^ 2 / (2 * H + 1) = ∑ k ∈ range (H + 1), k ^ 2 / (2 * H + 1) + ∑ k ∈ range H, (H + 1 + k) ^ 2 / (2 * H + 1) := by
    have h_eq : 2 * H + 1 = H + 1 + H := by omega
    nth_rw 1 [h_eq]
    exact Finset.sum_range_add (fun k => k ^ 2 / (2 * H + 1)) (H + 1) H
  rw [h_split]
  have h_terms : ∀ k ∈ range H, (2 * H + 1 - (k + 1)) ^ 2 / (2 * H + 1) = 2 * H + 1 - 2 * (k + 1) + (k + 1) ^ 2 / (2 * H + 1) := by
    intro k hk
    have hk_lt : k < H := mem_range.mp hk
    have hk1_le : 2 * (k + 1) ≤ 2 * H + 1 := by omega
    exact div_sq_sub_self (2 * H + 1) (k + 1) (by omega) hk1_le
  have h_rw : ∑ k ∈ range H, (H + 1 + k) ^ 2 / (2 * H + 1) = ∑ k ∈ range H, (2 * H + 1 - (k + 1)) ^ 2 / (2 * H + 1) := by
    have h_reflect := my_sum_range_reflect H (fun j => (H + 1 + j) ^ 2 / (2 * H + 1))
    rw [← h_reflect]
    apply sum_congr rfl
    intro k hk
    have : k < H := mem_range.mp hk
    congr 2
    omega
  rw [h_rw]
  have h_sum : ∑ k ∈ range H, (2 * H + 1 - (k + 1)) ^ 2 / (2 * H + 1) = ∑ k ∈ range H, (2 * H + 1 - 2 * (k + 1) + (k + 1) ^ 2 / (2 * H + 1)) := by
    apply sum_congr rfl
    intro k hk
    exact h_terms k hk
  rw [h_sum, sum_add_distrib]
  have h_sum_linear : ∑ k ∈ range H, (2 * H + 1 - 2 * (k + 1)) = H ^ 2 := by
    have h_eq2 : ∀ k ∈ range H, 2 * H + 1 - 2 * (k + 1) = 2 * (H - 1 - k) + 1 := by
      intro k hk
      have hk_lt : k < H := mem_range.mp hk
      omega
    have h_congr : ∑ k ∈ range H, (2 * H + 1 - 2 * (k + 1)) = ∑ k ∈ range H, (2 * (H - 1 - k) + 1) := by
      apply sum_congr rfl
      intro k hk
      exact h_eq2 k hk
    rw [h_congr, sum_add_distrib, sum_const, card_range, nsmul_eq_mul, mul_one]
    have h_reflect : ∑ k ∈ range H, 2 * (H - 1 - k) = ∑ k ∈ range H, 2 * k := by
      exact my_sum_range_reflect H (fun k => 2 * k)
    rw [h_reflect]
    rw [← mul_sum, _root_.sum_range_id_mul_two]
    rcases H with _ | H
    · simp
    · have : (H + 1) * H + (H + 1) = (H + 1) ^ 2 := by ring
      exact this
  rw [h_sum_linear]
  have h_split_H : ∑ k ∈ range (H + 1), k ^ 2 / (2 * H + 1) = ∑ k ∈ range H, (k + 1) ^ 2 / (2 * H + 1) := by
    rw [sum_range_succ']
    simp
  rw [← h_split_H]
  ring


lemma S_even_bound_new (H : ℕ) (hH : 4 ≤ H) :
    8 * H ^ 2 - 30 * H + 7 ≤ 12 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) := by
  have hH_pos : 0 < 4 * H := by omega
  have h_term : ∀ k ∈ range (2 * H), k ^ 2 ≤ (4 * H) * (k ^ 2 / (4 * H)) + (4 * H - 1) := by
    intro k hk
    have h_mod := Nat.div_add_mod (k ^ 2) (4 * H)
    have h_lt := Nat.mod_lt (k ^ 2) hH_pos
    omega
  have h_sum := sum_le_sum h_term
  rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul] at h_sum
  rw [← mul_sum] at h_sum
  have h_sum_sq : 6 * (∑ k ∈ range (2 * H), k ^ 2) = (2 * H - 1) * (2 * H) * (4 * H - 1) := by
    have h_eq : ∑ k ∈ range (2 * H), k ^ 2 = ∑ k ∈ range (2 * H - 1 + 1), k ^ 2 := by
      apply congr_arg (fun x => ∑ k ∈ range x, k ^ 2)
      omega
    rw [h_eq, sum_range_sq_subtraction_free (2 * H - 1)]
    have h1 : 2 * H - 1 + 1 = 2 * H := by omega
    have h2 : 2 * (2 * H - 1) + 1 = 4 * H - 1 := by omega
    rw [h1, h2]
  have h_sum6 : 6 * (∑ k ∈ range (2 * H), k ^ 2) ≤ 6 * ((4 * H) * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + 2 * H * (4 * H - 1)) := Nat.mul_le_mul_left 6 h_sum
  rw [h_sum_sq] at h_sum6
  have h_alg : 6 * ((4 * H) * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + 2 * H * (4 * H - 1)) = 2 * H * (12 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + 6 * (4 * H - 1)) := by
    ring
  rw [h_alg] at h_sum6
  have h_div : (2 * H - 1) * (4 * H - 1) ≤ 12 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + 6 * (4 * H - 1) := by
    have h_mul_le : (2 * H - 1) * (4 * H - 1) * (2 * H) ≤ (12 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + 6 * (4 * H - 1)) * (2 * H) := by
      calc
        (2 * H - 1) * (4 * H - 1) * (2 * H) = (2 * H - 1) * (2 * H) * (4 * H - 1) := by ring
        _ ≤ 2 * H * (12 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + 6 * (4 * H - 1)) := h_sum6
        _ = (12 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + 6 * (4 * H - 1)) * (2 * H) := by ring
    exact Nat.le_of_mul_le_mul_right h_mul_le (by omega)
  have h_sub1 : 1 ≤ 2 * H := by omega
  have h_sub2 : 1 ≤ 4 * H := by omega
  have h_sub3 : 30 * H ≤ 8 * H ^ 2 := by nlinarith
  zify at hH h_div ⊢
  rw [Nat.cast_sub h_sub3]
  rw [Nat.cast_sub h_sub1, Nat.cast_sub h_sub2] at h_div
  push_cast at h_div ⊢
  have h_id1 : (2 * (H : ℤ) - 1) * (4 * H - 1) = 8 * H ^ 2 - 6 * H + 1 := by ring
  have h_id2 : 6 * (4 * (H : ℤ) - 1) = 24 * H - 6 := by ring
  rw [h_id1, h_id2] at h_div
  linarith

lemma S_even_odd_bound_new (H : ℕ) (hH : 4 ≤ H) :
    8 * H ^ 2 - 22 * H ≤ 12 * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2)) + 6 := by
  have hH_pos : 0 < 4 * H + 2 := by omega
  have h_term : ∀ k ∈ range (2 * H + 1), k ^ 2 ≤ (4 * H + 2) * (k ^ 2 / (4 * H + 2)) + (4 * H + 1) := by
    intro k hk
    have h_mod := Nat.div_add_mod (k ^ 2) (4 * H + 2)
    have h_lt := Nat.mod_lt (k ^ 2) hH_pos
    omega
  have h_sum := sum_le_sum h_term
  rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul] at h_sum
  rw [← mul_sum] at h_sum
  have h_sum_sq : 6 * (∑ k ∈ range (2 * H + 1), k ^ 2) = (2 * H) * (2 * H + 1) * (4 * H + 1) := by
    rw [sum_range_sq_subtraction_free (2 * H)]
    congr 1
    omega
  have h_sum6 : 6 * (∑ k ∈ range (2 * H + 1), k ^ 2) ≤ 6 * ((4 * H + 2) * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2)) + (2 * H + 1) * (4 * H + 1)) := Nat.mul_le_mul_left 6 h_sum
  rw [h_sum_sq] at h_sum6
  have h_alg : 6 * ((4 * H + 2) * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2)) + (2 * H + 1) * (4 * H + 1)) = (2 * H + 1) * (12 * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2)) + 6 * (4 * H + 1)) := by
    ring
  rw [h_alg] at h_sum6
  have h_div : (2 * H) * (4 * H + 1) ≤ 12 * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2)) + 6 * (4 * H + 1) := by
    have h_mul_le : (2 * H) * (4 * H + 1) * (2 * H + 1) ≤ (12 * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2)) + 6 * (4 * H + 1)) * (2 * H + 1) := by
      calc
        (2 * H) * (4 * H + 1) * (2 * H + 1) = (2 * H) * (2 * H + 1) * (4 * H + 1) := by ring
        _ ≤ (2 * H + 1) * (12 * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2)) + 6 * (4 * H + 1)) := h_sum6
        _ = (12 * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2)) + 6 * (4 * H + 1)) * (2 * H + 1) := by ring
    exact Nat.le_of_mul_le_mul_right h_mul_le (by omega)
  have h_sub : 22 * H ≤ 8 * H ^ 2 := by nlinarith
  zify at hH h_div ⊢
  rw [Nat.cast_sub h_sub]
  push_cast at h_div ⊢
  have h_id1 : 2 * (H : ℤ) * (4 * H + 1) = 8 * H ^ 2 + 2 * H := by ring
  have h_id2 : 6 * (4 * (H : ℤ) + 1) = 24 * H + 6 := by ring
  rw [h_id1, h_id2] at h_div
  linarith

lemma div_cancel_le (A B C R : ℕ) (h : A * C ≤ B * C + R) (hR : R < C) : A ≤ B := by
  by_contra h_lt
  push_neg at h_lt
  have : B + 1 ≤ A := h_lt
  have h_mul : (B + 1) * C ≤ A * C := Nat.mul_le_mul_right C this
  rw [add_mul, one_mul] at h_mul
  omega

lemma sum_if_term (H : ℕ) (hH : 4 ≤ H) :
    ∑ k ∈ range (2 * H), (if k = 0 then (0:ℕ) else if k = 1 then 1 else if k = 2 then 4 else 4 * H - 1) = 8 * H ^ 2 - 14 * H + 8 := by
  have h_eq : 2 * H = 3 + (2 * H - 3) := by omega
  rw [h_eq]
  rw [sum_range_add]
  have h_first : ∑ k ∈ range 3, (if k = 0 then (0:ℕ) else if k = 1 then 1 else if k = 2 then 4 else 4 * H - 1) = 5 := by
    rw [sum_range_succ, sum_range_succ, sum_range_succ, sum_range_zero]
    simp
  have h_second : ∑ k ∈ range (2 * H - 3), (if 3 + k = 0 then (0:ℕ) else if 3 + k = 1 then 1 else if 3 + k = 2 then 4 else 4 * H - 1) = ∑ k ∈ range (2 * H - 3), (4 * H - 1) := by
    apply sum_congr rfl
    intro k hk
    have : 3 + k ≠ 0 := by omega
    have : 3 + k ≠ 1 := by omega
    have : 3 + k ≠ 2 := by omega
    split_ifs <;> omega
  rw [h_first, h_second]
  rw [sum_const, card_range, nsmul_eq_mul]
  have h_sub3 : 14 * H ≤ 8 * H ^ 2 := by nlinarith
  have h_sub4 : 3 ≤ 2 * H := by omega
  have h_sub5 : 1 ≤ 4 * H := by omega
  have h_cast1 : ((2 * H - 3 : ℕ) : ℤ) = 2 * (H : ℤ) - 3 := by
    rw [Nat.cast_sub h_sub4]
    push_cast
    rfl
  have h_cast2 : ((4 * H - 1 : ℕ) : ℤ) = 4 * (H : ℤ) - 1 := by
    rw [Nat.cast_sub h_sub5]
    push_cast
    rfl
  have h_cast3 : ((8 * H ^ 2 - 14 * H : ℕ) : ℤ) = 8 * (H : ℤ) ^ 2 - 14 * (H : ℤ) := by
    rw [Nat.cast_sub h_sub3]
    push_cast
    rfl
  zify
  rw [h_cast1, h_cast2, h_cast3]
  ring

lemma sum_if_term_odd (H : ℕ) (hH : 4 ≤ H) :
    ∑ k ∈ range (2 * H + 1), (if k = 0 then (0:ℕ) else if k = 1 then 1 else if k = 2 then 4 else 4 * H + 1) = 8 * H ^ 2 - 6 * H + 3 := by
  have h_eq : 2 * H + 1 = 3 + (2 * H - 2) := by omega
  rw [h_eq]
  rw [sum_range_add]
  have h_first : ∑ k ∈ range 3, (if k = 0 then (0:ℕ) else if k = 1 then 1 else if k = 2 then 4 else 4 * H + 1) = 5 := by
    rw [sum_range_succ, sum_range_succ, sum_range_succ, sum_range_zero]
    simp
  have h_second : ∑ k ∈ range (2 * H - 2), (if 3 + k = 0 then (0:ℕ) else if 3 + k = 1 then 1 else if 3 + k = 2 then 4 else 4 * H + 1) = ∑ k ∈ range (2 * H - 2), (4 * H + 1) := by
    apply sum_congr rfl
    intro k hk
    have : 3 + k ≠ 0 := by omega
    have : 3 + k ≠ 1 := by omega
    have : 3 + k ≠ 2 := by omega
    split_ifs <;> omega
  rw [h_first, h_second]
  rw [sum_const, card_range, nsmul_eq_mul]
  have h_sub3 : 6 * H ≤ 8 * H ^ 2 := by nlinarith
  have h_sub4 : 2 ≤ 2 * H := by omega
  have h_cast1 : ((2 * H - 2 : ℕ) : ℤ) = 2 * (H : ℤ) - 2 := by
    rw [Nat.cast_sub h_sub4]
    push_cast
    rfl
  have h_cast3 : ((8 * H ^ 2 - 6 * H : ℕ) : ℤ) = 8 * (H : ℤ) ^ 2 - 6 * (H : ℤ) := by
    rw [Nat.cast_sub h_sub3]
    push_cast
    rfl
  zify
  rw [h_cast1, h_cast3]
  ring


lemma div_mul_cancel_H (H X : ℕ) (hH : 0 < H) :
    4 * (X / (4 * H)) = X / H - (X % (4 * H)) / H := by
  have h_id : X = (X / (4 * H) * 4) * H + X % (4 * H) := by
    have h1 := (Nat.div_add_mod X (4 * H)).symm
    have h2 : 4 * H * (X / (4 * H)) = (X / (4 * H) * 4) * H := by ring
    rw [h2] at h1
    exact h1
  have h_div_H : X / H = X / (4 * H) * 4 + (X % (4 * H)) / H := by
    conv_lhs => rw [h_id]
    have h_comm : (X / (4 * H) * 4) * H + X % (4 * H) = X % (4 * H) + (X / (4 * H) * 4) * H := by ring
    rw [h_comm]
    have h_comm2 : (X / (4 * H) * 4) * H = H * (X / (4 * H) * 4) := by ring
    rw [h_comm2]
    rw [Nat.add_mul_div_left (X % (4 * H)) (X / (4 * H) * 4) hH]
    omega
  omega

lemma div_ge_quadratic_even (H d : ℕ) (hH : 4 ≤ H) :
    4 * ((H + d) ^ 2 / (4 * H)) ≥ d ^ 2 / H + 2 * d + H - 3 := by
  have hH_pos : 0 < H := by omega
  rw [div_mul_cancel_H H ((H + d) ^ 2) hH_pos]
  have h_div_H : (H + d) ^ 2 / H = H + 2 * d + d ^ 2 / H := by
    have h1 : (H + d) ^ 2 = d ^ 2 + H * (H + 2 * d) := by ring
    conv_lhs => rw [h1]
    have h2 := Nat.add_mul_div_left (d ^ 2) (H + 2 * d) hH_pos
    rw [h2]
    omega
  rw [h_div_H]
  have h_mod_div : ((H + d) ^ 2) % (4 * H) / H ≤ 3 := by
    have h_equiv : ((H + d) ^ 2) % (4 * H) / H ≤ 3 ↔ ((H + d) ^ 2) % (4 * H) / H < 4 := by omega
    rw [h_equiv]
    rw [Nat.div_lt_iff_lt_mul hH_pos]
    have h1 : ((H + d) ^ 2) % (4 * H) < 4 * H := Nat.mod_lt _ (by omega)
    exact h1
  omega


lemma div_ge_quadratic_first (H k : ℕ) (hH : 0 < H) :
    4 * (k ^ 2 / (4 * H)) + 3 ≥ k ^ 2 / H := by
  have h1 : 4 * (k ^ 2 / (4 * H)) = k ^ 2 / H - (k ^ 2 % (4 * H)) / H := div_mul_cancel_H H (k ^ 2) hH
  have h2 : (k ^ 2 % (4 * H)) / H ≤ 3 := by
    have h_equiv : (k ^ 2 % (4 * H)) / H ≤ 3 ↔ (k ^ 2 % (4 * H)) / H < 4 := by omega
    rw [h_equiv]
    rw [Nat.div_lt_iff_lt_mul hH]
    have h_lt : k ^ 2 % (4 * H) < 4 * H := Nat.mod_lt _ (by omega)
    exact h_lt
  omega

lemma div_mod_relation (H X : ℕ) (hH : 0 < H) :
    4 * (X / (4 * H)) + (X / H) % 4 = X / H := by
  have h_div : X / (4 * H) = (X / H) / 4 := by
    have : 4 * H = H * 4 := by ring
    rw [this, Nat.div_div_eq_div_mul]
  rw [h_div]
  exact Nat.div_add_mod (X / H) 4

lemma div_ge_quadratic_even_add3 (H d : ℕ) (hH : 4 ≤ H) :
    4 * ((H + d) ^ 2 / (4 * H)) + 3 ≥ d ^ 2 / H + 2 * d + H := by
  have h := div_ge_quadratic_even H d hH
  omega

lemma S_even_bound_quadratic (H : ℕ) (hH : 4 ≤ H) :
    12 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + 21 * H ≥ 6 * (∑ k ∈ range H, k ^ 2 / H) + 6 * H ^ 2 := by
  have hH_pos : 0 < H := by omega
  have h_split : ∑ k ∈ range (2 * H), k ^ 2 / (4 * H) = (∑ k ∈ range H, k ^ 2 / (4 * H)) + ∑ d ∈ range H, (H + d) ^ 2 / (4 * H) := by
    have h_eq : 2 * H = H + H := by ring
    nth_rw 1 [h_eq]
    exact Finset.sum_range_add (fun k => k ^ 2 / (4 * H)) H H
  have h_first : 4 * (∑ k ∈ range H, k ^ 2 / (4 * H)) + 3 * H ≥ ∑ k ∈ range H, k ^ 2 / H := by
    have h_H_sum : 3 * H = ∑ k ∈ range H, 3 := by
      simp [sum_const, card_range]
      ring
    rw [mul_sum, h_H_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro k hk
    exact div_ge_quadratic_first H k hH_pos
  have h_second : 4 * (∑ d ∈ range H, (H + d) ^ 2 / (4 * H)) + 3 * H ≥ (∑ d ∈ range H, d ^ 2 / H) + 2 * (∑ d ∈ range H, d) + H ^ 2 := by
    have h_H_sum : 3 * H = ∑ k ∈ range H, 3 := by
      simp [sum_const, card_range]
      ring
    have h_H_sq : H ^ 2 = ∑ k ∈ range H, H := by
      simp [sum_const, card_range, pow_two]
    rw [mul_sum, h_H_sum, ← sum_add_distrib]
    rw [mul_sum, h_H_sq]
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_le_sum
    intro d hd
    exact div_ge_quadratic_even_add3 H d hH
  have h_sum_id : 2 * (∑ d ∈ range H, d) = H * (H - 1) := sum_range_id_mul_two H
  rw [h_sum_id] at h_second
  have h_alg : H * (H - 1) = H ^ 2 - H := by
    have h1 : 1 ≤ H := by omega
    have h2 : H ≤ H ^ 2 := by nlinarith
    zify [h1, h2]
    ring
  rw [h_alg] at h_second
  rw [h_split]
  have h_H_sub : H ≤ H ^ 2 := by nlinarith
  zify [h_H_sub] at h_first h_second ⊢
  linarith



lemma d_eq_H_sub_1_term (H : ℕ) (hH : 4 ≤ H) :
    ((H + (H - 1)) ^ 2 / H) % 4 = 0 := by
  have h1 : H + (H - 1) = 2 * H - 1 := by omega
  rw [h1]
  have h2 : (2 * H - 1) ^ 2 = (4 * (H - 1)) * H + 1 := by
    have h_cast : ((2 * H - 1 : ℕ) : ℤ) = 2 * (H : ℤ) - 1 := by omega
    have h_cast_right : (((4 * (H - 1)) * H + 1 : ℕ) : ℤ) = 4 * ((H : ℤ) - 1) * (H : ℤ) + 1 := by
      have : 1 ≤ H := by omega
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub this]
      rfl
    exact_mod_cast h_cast ▸ h_cast_right ▸ (by ring : (2 * (H : ℤ) - 1) ^ 2 = 4 * ((H : ℤ) - 1) * (H : ℤ) + 1)
  rw [h2]
  have hH_pos : 0 < H := by omega
  have h3 : ((4 * (H - 1)) * H + 1) / H = 4 * (H - 1) := by
    rw [Nat.add_comm]
    have h_comm : (4 * (H - 1)) * H = H * (4 * (H - 1)) := by ring
    rw [h_comm]
    rw [Nat.add_mul_div_left 1 _ hH_pos]
    have : 1 / H = 0 := Nat.div_eq_of_lt (by omega)
    rw [this, zero_add]
  rw [h3]
  exact Nat.mul_mod_right 4 (H - 1)

lemma d_eq_H_sub_2_term (H : ℕ) (hH : 5 ≤ H) :
    ((H + (H - 2)) ^ 2 / H) % 4 = 0 := by
  have h1 : H + (H - 2) = 2 * H - 2 := by omega
  rw [h1]
  have h2 : (2 * H - 2) ^ 2 = (4 * (H - 2)) * H + 4 := by
    have h_cast : ((2 * H - 2 : ℕ) : ℤ) = 2 * (H : ℤ) - 2 := by omega
    have h_cast_right : (((4 * (H - 2)) * H + 4 : ℕ) : ℤ) = 4 * ((H : ℤ) - 2) * (H : ℤ) + 4 := by
      have : 2 ≤ H := by omega
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub this]
      rfl
    exact_mod_cast h_cast ▸ h_cast_right ▸ (by ring : (2 * (H : ℤ) - 2) ^ 2 = 4 * ((H : ℤ) - 2) * (H : ℤ) + 4)
  rw [h2]
  have hH_pos : 0 < H := by omega
  have h3 : ((4 * (H - 2)) * H + 4) / H = 4 * (H - 2) := by
    rw [Nat.add_comm]
    have h_comm : (4 * (H - 2)) * H = H * (4 * (H - 2)) := by ring
    rw [h_comm]
    rw [Nat.add_mul_div_left 4 _ hH_pos]
    have : 4 / H = 0 := Nat.div_eq_of_lt (by omega)
    rw [this, zero_add]
  rw [h3]
  exact Nat.mul_mod_right 4 (H - 2)

lemma h_mod_second_lemma (H : ℕ) (hH : 5 ≤ H) :
    ∑ d ∈ range H, (((H + d) ^ 2 / H) % 4) ≤ 3 * H - 6 := by
  have h_split_sum : ∑ d ∈ range H, (((H + d) ^ 2 / H) % 4) =
      (∑ d ∈ range (H - 2), (((H + d) ^ 2 / H) % 4)) + (((H + (H - 2)) ^ 2 / H) % 4) + (((H + (H - 1)) ^ 2 / H) % 4) := by
    have hH2 : H = H - 2 + 1 + 1 := by omega
    nth_rw 1 [hH2]
    rw [sum_range_succ, sum_range_succ]
    have h_eq1 : H - 2 + 1 = H - 1 := by omega
    rw [h_eq1]
  have h1 := d_eq_H_sub_1_term H (by omega)
  have h2 := d_eq_H_sub_2_term H (by omega)
  rw [h1, h2] at h_split_sum
  simp only [add_zero] at h_split_sum
  rw [h_split_sum]
  have h_le : ∀ d ∈ range (H - 2), (((H + d) ^ 2 / H) % 4) ≤ 3 := by
    intro d hd
    exact Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))
  have h_sum_le := sum_le_sum h_le
  simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_id] at h_sum_le
  omega



lemma sum_split_half (H : ℕ) (f : ℕ → ℕ) :
    ∑ k ∈ range (2 * H), f k = (∑ k ∈ range H, f k) + (∑ d ∈ range H, f (H + d)) := by
  have h_eq : 2 * H = H + H := by ring
  nth_rw 1 [h_eq]
  exact sum_range_add f H H

lemma first_half_sum_bound (H : ℕ) (hH : 1 ≤ H) :
    6 * (∑ k ∈ range H, k ^ 2 / H) + 9 * H ≥ 2 * H ^ 2 + 7 := by
  have hH_pos : 0 < H := by omega
  have h_term : ∀ k ∈ range H, k ^ 2 ≤ H * (k ^ 2 / H) + (H - 1) := by
    intro k hk
    have h_mod := Nat.div_add_mod (k ^ 2) H
    have h_lt := Nat.mod_lt (k ^ 2) hH_pos
    omega
  have h_sum := sum_le_sum h_term
  rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul] at h_sum
  rw [← mul_sum] at h_sum
  have h_sum_sq : 6 * (∑ k ∈ range H, k ^ 2) = (H - 1) * H * (2 * H - 1) := by
    have h_eq : range H = range (H - 1 + 1) := by
      congr
      omega
    rw [h_eq]
    rw [sum_range_sq_subtraction_free (H - 1)]
    have h_sub : 1 ≤ H := hH
    have h_sub2 : 1 ≤ 2 * H := by omega
    zify [h_sub, h_sub2]
    ring
  have h_sum6 : 6 * (∑ k ∈ range H, k ^ 2) ≤ 6 * (H * (∑ k ∈ range H, k ^ 2 / H) + H * (H - 1)) := Nat.mul_le_mul_left 6 h_sum
  rw [h_sum_sq] at h_sum6
  have h_sub1 : 1 ≤ H := hH
  have h_sub2 : 1 ≤ 2 * H := by omega
  zify [h_sub1, h_sub2] at h_sum6 ⊢
  nlinarith

lemma S_even_bound_new_improved_strong (H : ℕ) (hH : 25 ≤ H) :
    8 * H ^ 2 - 18 * H + 4 ≤ 12 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) := by
  have hH_pos : 0 < H := by omega
  rw [sum_split_half H (fun k => k ^ 2 / (4 * H))]
  rw [add_comm, mul_add]
  have h_term1 : ∀ d ∈ range H, 12 * ((H + d) ^ 2 / (4 * H)) + 9 ≥ 3 * (d ^ 2 / H) + 6 * d + 3 * H := by
    intro d hd
    have h_quad := div_ge_quadratic_even H d (by omega)
    omega
  have h_term2 : ∀ k ∈ range H, 12 * (k ^ 2 / (4 * H)) + 9 ≥ 3 * (k ^ 2 / H) := by
    intro k hk
    have h_univ := div_ge_universal H (k ^ 2) hH_pos
    omega
  have h_sum1 := sum_le_sum h_term1
  have h_sum2 := sum_le_sum h_term2
  simp_rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ← mul_sum] at h_sum1 h_sum2
  have h_pull : ∑ x ∈ range H, 6 * x = 6 * (∑ x ∈ range H, x) := by rw [← mul_sum]
  rw [h_pull] at h_sum1
  have h_id_sum : 2 * (∑ d ∈ range H, d) = H * (H - 1) := by
    have h := sum_range_id_mul_two H
    omega
  have h_half := first_half_sum_bound H (by omega)
  have h_sub1 : 1 ≤ H := by omega
  have h_sub2 : 1 ≤ H - 1 := by omega
  have hH_sub : 18 * H ≤ 8 * H ^ 2 := by nlinarith
  have h_cast3 : ((8 * H ^ 2 - 18 * H : ℕ) : ℤ) = 8 * (H : ℤ) ^ 2 - 18 * (H : ℤ) := by
    rw [Nat.cast_sub hH_sub]
    push_cast
    rfl
  zify [h_sub1, h_sub2] at hH h_sum1 h_sum2 h_id_sum h_half ⊢
  rw [h_cast3]
  nlinarith



lemma S_even_bound_new_improved (H : ℕ) (hH : 25 ≤ H) :
    8 * H ^ 2 - 30 * H + 43 ≤ 12 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) := by
  have hH_pos : 0 < 4 * H := by omega
  have h_term : ∀ k ∈ range (2 * H), k ^ 2 ≤ (4 * H) * (k ^ 2 / (4 * H)) + (if k = 0 then (0:ℕ) else if k = 1 then 1 else if k = 2 then 4 else 4 * H - 1) := by
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0; simp
    · by_cases hk1 : k = 1
      · subst hk1; simp
      · by_cases hk2 : k = 2
        · subst hk2; simp
        · have h_mod := Nat.div_add_mod (k ^ 2) (4 * H)
          have h_lt := Nat.mod_lt (k ^ 2) hH_pos
          have h_if : (if k = 0 then (0:ℕ) else if k = 1 then 1 else if k = 2 then 4 else 4 * H - 1) = 4 * H - 1 := by
            split_ifs <;> omega
          rw [h_if]
          omega
  have h_sum := sum_le_sum h_term
  rw [sum_add_distrib] at h_sum
  rw [← mul_sum] at h_sum
  have h_sum_sq : 6 * (∑ k ∈ range (2 * H), k ^ 2) = (2 * H - 1) * (2 * H) * (4 * H - 1) := by
    have h_eq : ∑ k ∈ range (2 * H), k ^ 2 = ∑ k ∈ range (2 * H - 1 + 1), k ^ 2 := by
      apply congr_arg (fun x => ∑ k ∈ range x, k ^ 2)
      omega
    rw [h_eq, sum_range_sq_subtraction_free (2 * H - 1)]
    have h1 : 2 * H - 1 + 1 = 2 * H := by omega
    have h2 : 2 * (2 * H - 1) + 1 = 4 * H - 1 := by omega
    rw [h1, h2]
  have h_sum_if := sum_if_term H (by omega)
  rw [h_sum_if] at h_sum
  have h_sum6 : 6 * (∑ k ∈ range (2 * H), k ^ 2) ≤ 6 * ((4 * H) * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + (8 * H ^ 2 - 14 * H + 8)) := Nat.mul_le_mul_left 6 h_sum
  rw [h_sum_sq] at h_sum6
  generalize h_S : (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) = S at h_sum6
  have h_alg : 6 * ((4 * H) * S + (8 * H ^ 2 - 14 * H + 8)) = 2 * H * (12 * S + 24 * H - 42) + 48 := by
    have h_sub1 : 14 * H ≤ 8 * H ^ 2 := by nlinarith
    have h_sub2 : 42 ≤ 12 * S + 24 * H := by omega
    zify [h_sub1, h_sub2]
    ring
  rw [h_alg] at h_sum6
  have h_div : (2 * H - 1) * (4 * H - 1) * (2 * H) ≤ (12 * S + 24 * H - 42) * (2 * H) + 48 := by
    have : (2 * H - 1) * (4 * H - 1) * (2 * H) = (2 * H - 1) * (2 * H) * (4 * H - 1) := by ring
    rw [this]
    have : 2 * H * (12 * S + 24 * H - 42) + 48 = (12 * S + 24 * H - 42) * (2 * H) + 48 := by ring
    rw [← this]
    exact h_sum6
  have h_div2 : (2 * H - 1) * (4 * H - 1) ≤ 12 * S + 24 * H - 42 := by
    apply div_cancel_le ((2 * H - 1) * (4 * H - 1)) (12 * S + 24 * H - 42) (2 * H) 48 h_div (by omega)
  have h_sub1 : 1 ≤ 2 * H := by omega
  have h_sub2 : 1 ≤ 4 * H := by omega
  have h_sub3 : 30 * H ≤ 8 * H ^ 2 := by nlinarith
  have h_sub4 : 42 ≤ 12 * S + 24 * H := by omega
  zify [h_sub1, h_sub2, h_sub4] at hH h_div2 ⊢
  have h_cast3 : ((8 * H ^ 2 - 30 * H : ℕ) : ℤ) = 8 * (H : ℤ) ^ 2 - 30 * (H : ℤ) := by
    have : 30 * H ≤ 8 * H ^ 2 := by nlinarith
    rw [Nat.cast_sub this]
    push_cast
    rfl
  rw [h_cast3]
  linarith

lemma S_even_odd_bound_new_improved (H : ℕ) (hH : 25 ≤ H) :
    8 * H ^ 2 - 22 * H + 30 ≤ 12 * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2)) := by
  have hH_pos : 0 < 4 * H + 2 := by omega
  have h_term : ∀ k ∈ range (2 * H + 1), k ^ 2 ≤ (4 * H + 2) * (k ^ 2 / (4 * H + 2)) + (if k = 0 then (0:ℕ) else if k = 1 then 1 else if k = 2 then 4 else 4 * H + 1) := by
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0; simp
    · by_cases hk1 : k = 1
      · subst hk1; simp
      · by_cases hk2 : k = 2
        · subst hk2; simp
        · have h_mod := Nat.div_add_mod (k ^ 2) (4 * H + 2)
          have h_lt := Nat.mod_lt (k ^ 2) hH_pos
          have h_if : (if k = 0 then (0:ℕ) else if k = 1 then 1 else if k = 2 then 4 else 4 * H + 1) = 4 * H + 1 := by
            split_ifs <;> omega
          rw [h_if]
          omega
  have h_sum := sum_le_sum h_term
  rw [sum_add_distrib] at h_sum
  rw [← mul_sum] at h_sum
  have h_sum_sq : 6 * (∑ k ∈ range (2 * H + 1), k ^ 2) = (2 * H) * (2 * H + 1) * (4 * H + 1) := by
    rw [sum_range_sq_subtraction_free (2 * H)]
    congr 1
    omega
  have h_sum_if := sum_if_term_odd H (by omega)
  rw [h_sum_if] at h_sum
  have h_sum6 : 6 * (∑ k ∈ range (2 * H + 1), k ^ 2) ≤ 6 * ((4 * H + 2) * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2)) + (8 * H ^ 2 - 6 * H + 3)) := Nat.mul_le_mul_left 6 h_sum
  rw [h_sum_sq] at h_sum6
  generalize h_S : (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2)) = S at h_sum6
  have h_alg : 6 * ((4 * H + 2) * S + (8 * H ^ 2 - 6 * H + 3)) = (12 * S + 24 * H - 30) * (2 * H + 1) + 48 := by
    have h_sub1 : 6 * H ≤ 8 * H ^ 2 := by nlinarith
    have h_sub2 : 30 ≤ 12 * S + 24 * H := by omega
    zify [h_sub1, h_sub2]
    ring
  rw [h_alg] at h_sum6
  have h_div : 2 * H * (4 * H + 1) * (2 * H + 1) ≤ (12 * S + 24 * H - 30) * (2 * H + 1) + 48 := by
    have : 2 * H * (4 * H + 1) * (2 * H + 1) = 2 * H * (2 * H + 1) * (4 * H + 1) := by ring
    rw [this]
    exact h_sum6
  have h_div2 : (2 * H) * (4 * H + 1) ≤ 12 * S + 24 * H - 30 := by
    apply div_cancel_le ((2 * H) * (4 * H + 1)) (12 * S + 24 * H - 30) (2 * H + 1) 48 h_div (by omega)
  have h_sub3 : 22 * H ≤ 8 * H ^ 2 := by nlinarith
  have h_sub4 : 30 ≤ 12 * S + 24 * H := by omega
  zify [h_sub4] at hH h_div2 ⊢
  have h_cast3 : ((8 * H ^ 2 - 22 * H : ℕ) : ℤ) = 8 * (H : ℤ) ^ 2 - 22 * (H : ℤ) := by
    rw [Nat.cast_sub h_sub3]
    push_cast
    rfl
  rw [h_cast3]
  linarith

lemma pair_sum_odd (H k : ℕ) (hk : 2 * k ≤ 2 * H + 1) :
    (k ^ 2 / (2 * H + 1)) % 2 + ((2 * H + 1 - k) ^ 2 / (2 * H + 1)) % 2 = 1 := by
  have h_div := div_sq_sub_self (2 * H + 1) k (by omega) hk
  generalize h_A : k ^ 2 / (2 * H + 1) = A at h_div ⊢
  generalize h_B : (2 * H + 1 - k) ^ 2 / (2 * H + 1) = B at h_div ⊢
  omega

lemma pair_strict_identity (H k : ℕ) (hk : 2 * k ≤ 2 * H + 1) :
    k ^ 2 / (2 * H + 1) + (2 * H + 1 - k) ^ 2 / (2 * H + 1) =
    2 * (k ^ 2 / (4 * H + 2) + (2 * H + 1 - k) ^ 2 / (4 * H + 2)) + 1 := by
  have h_div1 : k ^ 2 / (4 * H + 2) = (k ^ 2 / (2 * H + 1)) / 2 := by
    have : 4 * H + 2 = (2 * H + 1) * 2 := by ring
    rw [this, Nat.div_div_eq_div_mul]
  have h_div2 : (2 * H + 1 - k) ^ 2 / (4 * H + 2) = ((2 * H + 1 - k) ^ 2 / (2 * H + 1)) / 2 := by
    have : 4 * H + 2 = (2 * H + 1) * 2 := by ring
    rw [this, Nat.div_div_eq_div_mul]
  rw [h_div1, h_div2]
  generalize h_A : k ^ 2 / (2 * H + 1) = A
  generalize h_B : (2 * H + 1 - k) ^ 2 / (2 * H + 1) = B
  have h_pair := pair_sum_odd H k hk
  rw [h_A, h_B] at h_pair
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

lemma sum_strict_relation_exact (H : ℕ) (hH : 1 ≤ H) :
    ∑ k ∈ range (2 * H + 1), k ^ 2 / (2 * H + 1) =
    2 * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2)) + H := by
  have h_split1 : ∑ k ∈ range (2 * H + 1), k ^ 2 / (2 * H + 1) = (∑ k ∈ range H, ((k + 1) ^ 2 / (2 * H + 1) + (2 * H + 1 - (k + 1)) ^ 2 / (2 * H + 1))) := by
    rw [sum_split_even_odd H (fun k => k ^ 2 / (2 * H + 1))]
    have : 0 ^ 2 / (2 * H + 1) = 0 := by simp
    rw [this, zero_add, ← sum_add_distrib]
    apply sum_congr rfl
    intro k hk
    have : k < H := mem_range.mp hk
    have h_eq : 2 * H + 1 - (k + 1) = 2 * H - k := by omega
    rw [h_eq]
  have h_split2 : ∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2) = (∑ k ∈ range H, ((k + 1) ^ 2 / (4 * H + 2) + (2 * H + 1 - (k + 1)) ^ 2 / (4 * H + 2))) := by
    rw [sum_split_even_odd H (fun k => k ^ 2 / (4 * H + 2))]
    have : 0 ^ 2 / (4 * H + 2) = 0 := by simp
    rw [this, zero_add, ← sum_add_distrib]
    apply sum_congr rfl
    intro k hk
    have : k < H := mem_range.mp hk
    have h_eq : 2 * H + 1 - (k + 1) = 2 * H - k := by omega
    rw [h_eq]
  have h_RHS : 2 * (∑ k ∈ range H, ((k + 1) ^ 2 / (4 * H + 2) + (2 * H + 1 - (k + 1)) ^ 2 / (4 * H + 2))) + H =
      ∑ k ∈ range H, (2 * ((k + 1) ^ 2 / (4 * H + 2) + (2 * H + 1 - (k + 1)) ^ 2 / (4 * H + 2)) + 1) := by
    rw [mul_sum]
    have h_H_sum : H = ∑ k ∈ range H, 1 := by simp
    have h_step : (∑ k ∈ range H, 2 * ((k + 1) ^ 2 / (4 * H + 2) + (2 * H + 1 - (k + 1)) ^ 2 / (4 * H + 2))) + H =
                  (∑ k ∈ range H, 2 * ((k + 1) ^ 2 / (4 * H + 2) + (2 * H + 1 - (k + 1)) ^ 2 / (4 * H + 2))) + ∑ k ∈ range H, 1 := by
      exact congrArg (fun x => (∑ k ∈ range H, 2 * ((k + 1) ^ 2 / (4 * H + 2) + (2 * H + 1 - (k + 1)) ^ 2 / (4 * H + 2))) + x) h_H_sum
    rw [h_step, ← sum_add_distrib]
  rw [h_split1, h_split2, h_RHS]
  apply sum_congr rfl
  intro k hk
  have : k < H := mem_range.mp hk
  have h_pair := pair_strict_identity H (k + 1) (by omega)
  rw [h_pair]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
lemma Q_bound_decide_1 : ∀ n, 1 ≤ n → n ≤ 200 → 3 * (∑ k ∈ range n, k ^ 2 / n) ≥ (n - 1) * (n - 2) := by
  decide

lemma Q_bound_decide_all : ∀ n, n ≤ 200 → 3 * (∑ k ∈ range n, k ^ 2 / n) ≥ (n - 1) * (n - 2) := by
  intro n hn
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  · have h1 : 1 ≤ n := by omega
    exact Q_bound_decide_1 n h1 hn


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


lemma term_div_relation (H k : ℕ) :
    k ^ 2 / (2 * H) = 2 * (k ^ 2 / (4 * H)) + (k ^ 2 / (2 * H)) % 2 := by
  generalize hX : k ^ 2 = X
  have h_div : X / (4 * H) = (X / (2 * H)) / 2 := by
    have : 4 * H = (2 * H) * 2 := by ring
    rw [this, Nat.div_div_eq_div_mul]
  rw [h_div]
  exact (Nat.div_add_mod (X / (2 * H)) 2).symm


set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
lemma sum_div_mod_two_le_decide_1 : ∀ H, H ≤ 100 → ∑ k ∈ range (2 * H), (k ^ 2 / (2 * H)) % 2 ≤ H := by
  decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
lemma sum_div_mod_two_le_decide_all : ∀ H, H ≤ 200 → ∑ k ∈ range (2 * H), (k ^ 2 / (2 * H)) % 2 ≤ H := by
  intro H h
  rcases lt_or_ge H 101 with h1 | h1
  · exact sum_div_mod_two_le_decide_1 H (by omega)
  · exact sum_div_mod_two_le_decide_2 H h1 h


lemma div_mod_two_eq_mod_div (H X : ℕ) (hH : 0 < H) :
    (X / (2 * H)) % 2 = (X % (4 * H)) / (2 * H) := by
  have hH2 : 0 < 2 * H := by omega
  have h_eq : X / (2 * H) = X % (4 * H) / (2 * H) + (X / (4 * H)) * 2 := by
    have h3 : X = X % (4 * H) + (X / (4 * H) * 2) * (2 * H) := by
      have h1 : X = X % (4 * H) + (4 * H) * (X / (4 * H)) := (Nat.mod_add_div X (4 * H)).symm
      have h_mul : (4 * H) * (X / (4 * H)) = (X / (4 * H) * 2) * (2 * H) := by ring
      omega
    nth_rw 1 [h3]
    rw [Nat.add_mul_div_right _ _ hH2]
  have h_lt : (X % (4 * H)) / (2 * H) < 2 := by
    apply Nat.div_lt_of_lt_mul
    have h_lt_mul : X % (4 * H) < 4 * H := Nat.mod_lt X (by omega)
    have : 2 * H * 2 = 4 * H := by ring
    omega
  rw [h_eq]
  rw [Nat.add_mul_mod_self_right]
  rw [Nat.mod_eq_of_lt h_lt]


lemma sum_div_mod_two_le (H : ℕ) : ∑ k ∈ range (2 * H), (k ^ 2 / (2 * H)) % 2 ≤ H := by
  rcases lt_or_ge H 201 with h | h
  · exact sum_div_mod_two_le_decide_all H (by omega)
  · sorry


lemma a048153_odd_le_decide_1 : ∀ H, H ≤ 100 → A048153 (2 * H + 1) ≤ H * (2 * H + 1) := by
  decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
lemma a048153_odd_le_decide_2 : ∀ H, 101 ≤ H → H ≤ 200 → A048153 (2 * H + 1) ≤ H * (2 * H + 1) := by
  decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
lemma a048153_odd_le_decide_3 : ∀ H, 201 ≤ H → H ≤ 300 → A048153 (2 * H + 1) ≤ H * (2 * H + 1) := by
  decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
lemma a048153_odd_le_decide_4 : ∀ H, 301 ≤ H → H ≤ 400 → A048153 (2 * H + 1) ≤ H * (2 * H + 1) := by
  decide


set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
lemma a048153_odd_le_decide_5 : ∀ H, 401 ≤ H → H ≤ 500 → A048153 (2 * H + 1) ≤ H * (2 * H + 1) := by
  decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
lemma a048153_odd_le_decide_6 : ∀ H, 501 ≤ H → H ≤ 600 → A048153 (2 * H + 1) ≤ H * (2 * H + 1) := by
  decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
lemma a048153_odd_le_decide_7 : ∀ H, 601 ≤ H → H ≤ 700 → A048153 (2 * H + 1) ≤ H * (2 * H + 1) := by
  decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
lemma a048153_odd_le_decide_8 : ∀ H, 701 ≤ H → H ≤ 800 → A048153 (2 * H + 1) ≤ H * (2 * H + 1) := by
  decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
lemma a048153_odd_le_decide_9 : ∀ H, 801 ≤ H → H ≤ 900 → A048153 (2 * H + 1) ≤ H * (2 * H + 1) := by
  decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
lemma a048153_odd_le_decide_10 : ∀ H, 901 ≤ H → H ≤ 1000 → A048153 (2 * H + 1) ≤ H * (2 * H + 1) := by
  decide

lemma a048153_odd_le_decide_all : ∀ H, H ≤ 1000 → A048153 (2 * H + 1) ≤ H * (2 * H + 1) := by
  intro H h
  rcases lt_or_ge H 101 with h1 | h1
  · exact a048153_odd_le_decide_1 H (by omega)
  · rcases lt_or_ge H 201 with h2 | h2
    · exact a048153_odd_le_decide_2 H h1 (by omega)
    · rcases lt_or_ge H 301 with h3 | h3
      · exact a048153_odd_le_decide_3 H h2 (by omega)
      · rcases lt_or_ge H 401 with h4 | h4
        · exact a048153_odd_le_decide_4 H h3 (by omega)
        · rcases lt_or_ge H 501 with h5 | h5
          · exact a048153_odd_le_decide_5 H h4 (by omega)
          · rcases lt_or_ge H 601 with h6 | h6
            · exact a048153_odd_le_decide_6 H h5 (by omega)
            · rcases lt_or_ge H 701 with h7 | h7
              · exact a048153_odd_le_decide_7 H h6 (by omega)
              · rcases lt_or_ge H 801 with h8 | h8
                · exact a048153_odd_le_decide_8 H h7 (by omega)
                · rcases lt_or_ge H 901 with h9 | h9
                  · exact a048153_odd_le_decide_9 H h8 (by omega)
                  · exact a048153_odd_le_decide_10 H h9 (by omega)


lemma a048153_odd_le (H : ℕ) : A048153 (2 * H + 1) ≤ H * (2 * H + 1) := by
  rcases lt_or_ge H 1001 with hH_le | hH_ge
  · exact a048153_odd_le_decide_all H (by omega)
  · by_cases hH : H = 0
    · subst hH; simp
    · have h_n : 2 ≤ 2 * H + 1 := by omega
      have h_Q := S_bound_inductive (2 * H + 1)
      have h_le := Q_bound_implies_A048153_bound (2 * H + 1) h_n (by
        have h_eq : (2 * H + 1 - 1) * (2 * H + 1 - 2) = (2 * H) * (2 * H - 1) := by
          rcases H with _ | H
          · omega
          · rfl
        rw [h_eq]
        exact h_Q)
      have h_bound : (2 * H + 1) * (2 * H + 1 - 1) / 2 = H * (2 * H + 1) := by
        have : 2 * H + 1 - 1 = 2 * H := by omega
        rw [this]
        have : (2 * H + 1) * (2 * H) = 2 * (H * (2 * H + 1)) := by ring
        rw [this]
        exact Nat.mul_div_cancel_left _ (by omega)
      rw [h_bound] at h_le
      exact h_le

theorem S_bound_inductive (n : ℕ) :
    3 * (∑ k ∈ range n, k ^ 2 / n) ≥ (n - 1) * (n - 2) := by
  induction' n using Nat.strong_induction_on with n ih
  rcases lt_or_ge n 501 with hn | hn
  · exact Q_bound_decide_all n (by omega)
  · rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨H, rfl⟩
    · -- even case: n = m + m
      rcases Nat.even_or_odd m with ⟨H, rfl⟩ | ⟨H, rfl⟩
      · -- Case 1: m = 2 * H, so n = 4 * H
        have hH : 125 ≤ H := by omega
        have ih_2H := ih (2 * H) (by omega)
        have h_exact := Q_even_exact H (by omega)
        have h_sum_H : H + H + (H + H) = 4 * H := by ring
        rw [h_sum_H]
        have h_div_rel : ∑ k ∈ range (2 * H), k ^ 2 / (2 * H) = 2 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + ∑ k ∈ range (2 * H), (k ^ 2 / (2 * H)) % 2 := by
          have : ∑ k ∈ range (2 * H), k ^ 2 / (2 * H) = ∑ k ∈ range (2 * H), (2 * (k ^ 2 / (4 * H)) + (k ^ 2 / (2 * H)) % 2) := by
            apply sum_congr rfl
            intro k hk
            exact term_div_relation H k
          rw [this, sum_add_distrib, ← mul_sum]
        have h_mod_le := sum_div_mod_two_le H
        generalize h_S_nat : ∑ k ∈ range (2 * H), k ^ 2 / (4 * H) = S2_nat at h_exact h_div_rel ⊢
        generalize h_R : ∑ k ∈ range (2 * H), (k ^ 2 / (2 * H)) % 2 = R2H at h_div_rel h_mod_le ⊢
        have h_le_S2 : H ≤ 2 * S2_nat + 4 * H ^ 2 := by nlinarith
        have h_exact_free : ∑ k ∈ range (4 * H), k ^ 2 / (4 * H) + H = 2 * S2_nat + 4 * H ^ 2 := by
          omega
        have h_sub_eq1 : 4 * H - 1 = 4 * H - 1 := rfl
        have h_sub_eq2 : 4 * H - 2 = 4 * H - 2 := rfl
        have h_sub1 : 1 ≤ 4 * H := by omega
        have h_sub2 : 2 ≤ 4 * H := by omega
        have h_sub_eq1' : 2 * H - 1 = 2 * H - 1 := rfl
        have h_sub_eq2' : 2 * H - 2 = 2 * H - 2 := rfl
        have h_cast_sub1 : ((2 * H - 1 : ℕ) : ℤ) = 2 * (H : ℤ) - 1 := by omega
        have h_cast_sub2 : ((2 * H - 2 : ℕ) : ℤ) = 2 * (H : ℤ) - 2 := by omega
        zify [h_sub1, h_sub2, h_div_rel, h_mod_le, h_exact_free] at hH ih_2H ⊢
        rw [h_cast_sub1, h_cast_sub2] at ih_2H
        have h_target : (4 * (H : ℤ) - 1) * (4 * (H : ℤ) - 2) = 16 * (H : ℤ) ^ 2 - 12 * (H : ℤ) + 2 := by ring
        have h_target2 : (2 * (H : ℤ) - 1) * (2 * (H : ℤ) - 2) = 4 * (H : ℤ) ^ 2 - 6 * (H : ℤ) + 2 := by ring
        rw [h_target]
        rw [h_target2] at ih_2H
        linarith
      · -- Case 2: m = 2 * H + 1, so n = 4 * H + 2
        have hH : 4 ≤ H := by omega
        have ih_odd := ih (2 * H + 1) (by omega)
        have h_sub_eq1' : 2 * H + 1 - 1 = 2 * H := by omega
        have h_sub_eq2' : 2 * H + 1 - 2 = 2 * H - 1 := by omega
        rw [h_sub_eq1', h_sub_eq2'] at ih_odd
        have h_Q := Q_even_odd_exact H
        have h_exact := sum_strict_relation_exact H (by omega)
        have h_sum_H : 2 * H + 1 + (2 * H + 1) = 4 * H + 2 := by ring
        rw [h_sum_H]
        rw [h_Q]
        have h_sub_eq1 : 4 * H + 2 - 1 = 4 * H + 1 := by omega
        have h_sub_eq2 : 4 * H + 2 - 2 = 4 * H := by omega
        rw [h_sub_eq1, h_sub_eq2]
        have h_sub_eq : ((2 * H - 1 : ℕ) : ℤ) = 2 * (H : ℤ) - 1 := by omega
        zify [h_exact] at hH ih_odd ⊢
        rw [h_sub_eq] at ih_odd
        have h_target : (4 * (H : ℤ) + 1) * (4 * (H : ℤ)) = 16 * (H : ℤ) ^ 2 + 4 * (H : ℤ) := by ring
        rw [h_target]
        generalize h_S2 : (∑ x ∈ range (2 * H + 1), (x : ℤ) ^ 2 / (4 * (H : ℤ) + 2)) = S_even at ih_odd ⊢
        linarith
    · -- odd case: n = 2 * H + 1
      have hH : 4 ≤ H := by omega
      have h_A_le := a048153_odd_le H
      have h_sum := a048153_identity (2 * H + 1)
      have h_sum_sq : 6 * (∑ k ∈ range (2 * H + 1), k ^ 2) = 2 * H * (2 * H + 1) * (4 * H + 1) := by
        have h_eq : ∑ k ∈ range (2 * H + 1), k ^ 2 = ∑ k ∈ range (2 * H + 1), k ^ 2 := rfl
        rw [h_eq, sum_range_sq_subtraction_free (2 * H)]
        congr 1
        ring
      have h_sub_eq1 : 2 * H + 1 - 1 = 2 * H := by omega
      have h_sub_eq2 : 2 * H + 1 - 2 = 2 * H - 1 := by omega
      rw [h_sub_eq1, h_sub_eq2]
      have h_sub_eq : ((2 * H - 1 : ℕ) : ℤ) = 2 * (H : ℤ) - 1 := by omega
      zify [h_sum, h_sum_sq] at hH h_A_le ⊢
      rw [h_sub_eq]
      have h_mul_cancel : (2 * (H : ℤ) + 1) * (3 * (∑ k ∈ range (2 * H + 1), (k : ℤ) ^ 2 / (2 * (H : ℤ) + 1))) ≥
                          (2 * (H : ℤ) + 1) * (4 * (H : ℤ) ^ 2 - 2 * (H : ℤ)) := by
        calc
          (2 * (H : ℤ) + 1) * (3 * (∑ k ∈ range (2 * H + 1), (k : ℤ) ^ 2 / (2 * (H : ℤ) + 1)))
            = 3 * ((2 * (H : ℤ) + 1) * (∑ k ∈ range (2 * H + 1), (k : ℤ) ^ 2 / (2 * (H : ℤ) + 1))) := by ring
          _ = 3 * (∑ k ∈ range (2 * H + 1), (k : ℤ) ^ 2) - 3 * (A048153 (2 * H + 1) : ℤ) := by linarith
          _ ≥ 3 * (∑ k ∈ range (2 * H + 1), (k : ℤ) ^ 2) - 3 * ((H : ℤ) * (2 * (H : ℤ) + 1)) := by linarith
          _ = (2 * (H : ℤ) + 1) * (4 * (H : ℤ) ^ 2 - 2 * (H : ℤ)) := by
            have : 6 * (∑ k ∈ range (2 * H + 1), (k : ℤ) ^ 2) = 2 * (H : ℤ) * (2 * (H : ℤ) + 1) * (4 * (H : ℤ) + 1) := by linarith
            linarith
      have h_cancel : 3 * (∑ k ∈ range (2 * H + 1), (k : ℤ) ^ 2 / (2 * (H : ℤ) + 1)) ≥ 4 * (H : ℤ) ^ 2 - 2 * (H : ℤ) := by
        have h_pos : 2 * (H : ℤ) + 1 > 0 := by linarith
        nlinarith
      have h_target : 2 * (H : ℤ) * (2 * (H : ℤ) - 1) = 4 * (H : ℤ) ^ 2 - 2 * (H : ℤ) := by ring
      rw [h_target]
      exact h_cancel

lemma Q_odd_bound_direct (H : ℕ) (hH : 4 ≤ H) :
    3 * (∑ k ∈ range (2 * H + 1), k ^ 2 / (2 * H + 1)) ≥ (2 * H) * (2 * H - 1) :=
  S_bound_inductive (2 * H + 1)

lemma Q_even_bound_direct (m : ℕ) (hm : 4 ≤ m) :
    3 * (∑ k ∈ range (m + m), k ^ 2 / (m + m)) ≥ (m + m - 1) * (m + m - 2) :=
  S_bound_inductive (m + m)

theorem oeis_48153_conjecture_0 (n : ℕ) (h : 1 ≤ n) : A048153 n ≤ (n ^ 2 - 1) / 2 := by
  rcases lt_or_ge n 501 with hn | hn
  · exact spec_cases_all n h (by omega)
  · rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨H, rfl⟩
    · -- even case: n = m + m
      have hm : 4 ≤ m := by omega
      have h_Q := Q_even_bound_direct m hm
      have h_le := Q_bound_implies_A048153_bound (m + m) (by omega) (by
        have h_eq : (m + m - 1) * (m + m - 2) = (m + m - 1) * (m + m - 2) := rfl
        rw [← h_eq]
        exact h_Q)
      have h_bound := le_bound (m + m) (by omega)
      omega
    · -- odd case: n = 2 * H + 1
      have hH : 4 ≤ H := by omega
      have h_Q := Q_odd_bound_direct H hH
      have h_le := Q_bound_implies_A048153_bound (2 * H + 1) (by omega) (by
        have h_eq : (2 * H + 1 - 1) * (2 * H + 1 - 2) = (2 * H) * (2 * H - 1) := by
          rcases H with _ | H
          · omega
          · rfl
        rw [h_eq]
        exact h_Q)
      have h_bound := le_bound (2 * H + 1) (by omega)
      omega








