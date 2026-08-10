import FormalConjectures.Util.ProblemImports

open Nat Finset

def triangular (x : ℕ) : ℕ := x * (x + 1) / 2

lemma triangular_even (x : ℕ) : 2 ∣ x * (x + 1) := by
  rcases Nat.even_or_odd x with h | h
  · obtain ⟨k, hk⟩ := h
    use k * (x + 1)
    rw [hk]
    ring
  · obtain ⟨k, hk⟩ := h
    use x * (k + 1)
    rw [hk]
    ring

lemma triangular_diff (x : ℕ) : triangular (x + 1) = triangular x + (x + 1) := by
  unfold triangular
  have h1 : 2 ∣ x * (x + 1) := triangular_even x
  have h2 : 2 ∣ (x + 1) * (x + 2) := triangular_even (x + 1)
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  rw [hk1, hk2]
  rw [Nat.mul_div_cancel_left _ (by decide)]
  rw [Nat.mul_div_cancel_left _ (by decide)]
  have h3 : 2 * k2 = 2 * (k1 + (x + 1)) := by
    calc
      2 * k2 = (x + 1) * (x + 2) := hk2.symm
      _ = x * (x + 1) + 2 * (x + 1) := by ring
      _ = 2 * k1 + 2 * (x + 1) := by rw [hk1]
      _ = 2 * (k1 + x + 1) := by ring
  omega

lemma div_add_lt (A k m : ℕ) (hm : m > 0) (hk : k < m) : (A + k) / m ≤ A / m + 1 := by
  have h1 : A + k ≤ A + m := by omega
  have h2 := Nat.div_le_div_right h1 (c := m)
  have h3 : (A + m) / m = A / m + 1 := Nat.add_div_right A hm
  omega

lemma gap_le_one (m : ℕ) (hm : m ≥ 2) (x : ℕ) (hx : x < m - 1) :
    triangular (x + 1) / m ≤ triangular x / m + 1 := by
  rw [triangular_diff]
  apply div_add_lt
  · omega
  · omega

lemma triangular_zero : triangular 0 = 0 := by
  unfold triangular
  rfl

lemma triangular_div_range_filling_helper (m : ℕ) (hm : m ≥ 2) (B : ℕ) (hB : B < m) :
    ∀ v, v ≤ triangular B / m → ∃ x, x ≤ B ∧ triangular x / m = v := by
  induction B with
  | zero =>
    intro v hv
    use 0
    rw [triangular_zero] at hv
    have h_zero : 0 / m = 0 := Nat.zero_div m
    rw [h_zero] at hv
    have hv_zero : v = 0 := by omega
    refine ⟨by omega, ?_⟩
    rw [triangular_zero, h_zero, hv_zero]
  | succ B ih =>
    have hB_succ : B < m := by omega
    intro v hv
    by_cases h : v ≤ triangular B / m
    · obtain ⟨x, hx_le, hx_eq⟩ := ih hB_succ v h
      use x
      refine ⟨by omega, hx_eq⟩
    · use B + 1
      refine ⟨by omega, ?_⟩
      have h_gap := gap_le_one m hm B (by omega)
      omega

lemma triangular_div_self (m : ℕ) (hm : m ≥ 2) :
    triangular (m - 1) / m = (m - 1) / 2 := by
  unfold triangular
  have h_m : m - 1 + 1 = m := by omega
  rw [h_m]
  rw [Nat.div_div_eq_div_mul]
  have h_comm : 2 * m = m * 2 := by ring
  rw [h_comm]
  have hm0 : m > 0 := by omega
  rw [Nat.mul_comm (m - 1) m]
  rw [Nat.mul_div_mul_left (m - 1) 2 hm0]

lemma triangular_m_div (m : ℕ) (hm : m ≥ 2) :
    triangular m / m = triangular (m - 1) / m + 1 := by
  have h1 : triangular m = triangular (m - 1) + m := by
    have h_eq : m - 1 + 1 = m := by omega
    have h_diff := triangular_diff (m - 1)
    rw [h_eq] at h_diff
    exact h_diff
  rw [h1]
  apply Nat.add_div_right
  omega

lemma triangular_mono (a b : ℕ) (h : a ≤ b) : triangular a ≤ triangular b := by
  unfold triangular
  apply Nat.div_le_div_right
  nlinarith

lemma gap_fill (m : ℕ) (hm : m ≥ 2) (x : ℕ) (hx : x ≤ m - 1) :
    ∃ x' : ℕ, x' ≤ m ∧ triangular x' / m = triangular x / m + 1 := by
  let v := triangular x / m + 1
  have h_tx : triangular x ≤ triangular (m - 1) := triangular_mono x (m - 1) hx
  have h_div : triangular x / m ≤ triangular (m - 1) / m := Nat.div_le_div_right h_tx
  have h_v_bound : v ≤ triangular (m - 1) / m + 1 := by omega
  by_cases hv : v = triangular (m - 1) / m + 1
  · use m
    refine ⟨by omega, ?_⟩
    change triangular m / m = v
    rw [hv]
    exact triangular_m_div m hm
  · have h_lt : v < triangular (m - 1) / m + 1 := lt_of_le_of_ne h_v_bound hv
    have h_le_m1 : v ≤ triangular (m - 1) / m := by omega
    obtain ⟨x', hx'_le, hx'_eq⟩ := triangular_div_range_filling_helper m hm (m - 1) (by omega) v h_le_m1
    use x'
    refine ⟨by omega, hx'_eq⟩


lemma sq_mod_eight (x : ℕ) : (x ^ 2) % 8 = 0 ∨ (x ^ 2) % 8 = 1 ∨ (x ^ 2) % 8 = 4 := by
  have h : x % 8 < 8 := Nat.mod_lt x (by decide)
  interval_cases h_mod : x % 8
  · have : x = 8 * (x / 8) := by omega
    rw [this]
    ring_nf
    omega
  · have : x = 8 * (x / 8) + 1 := by omega
    rw [this]
    ring_nf
    omega
  · have : x = 8 * (x / 8) + 2 := by omega
    rw [this]
    ring_nf
    omega
  · have : x = 8 * (x / 8) + 3 := by omega
    rw [this]
    ring_nf
    omega
  · have : x = 8 * (x / 8) + 4 := by omega
    rw [this]
    ring_nf
    omega
  · have : x = 8 * (x / 8) + 5 := by omega
    rw [this]
    ring_nf
    omega
  · have : x = 8 * (x / 8) + 6 := by omega
    rw [this]
    ring_nf
    omega
  · have : x = 8 * (x / 8) + 7 := by omega
    rw [this]
    ring_nf
    omega



lemma mod_eight_expand (k r : ℕ) : ((8 * k + r) ^ 2) % 8 = (r ^ 2) % 8 := by
  have h1 : (8 * k + r) ^ 2 = 8 * (8 * k ^ 2 + 2 * k * r) + r ^ 2 := by ring
  omega

lemma odd_of_sq_mod_eight_one (x : ℕ) (h : (x ^ 2) % 8 = 1) : ∃ k, x = 2 * k + 1 := by
  have h_mod : x % 8 < 8 := Nat.mod_lt x (by decide)
  interval_cases h_x : x % 8
  · have : x = 8 * (x / 8) := by omega
    rw [this] at h
    have h2 : (8 * (x / 8)) ^ 2 = (8 * (x / 8) + 0) ^ 2 := by ring
    rw [h2, mod_eight_expand] at h
    omega
  · use 4 * (x / 8)
    omega
  · have : x = 8 * (x / 8) + 2 := by omega
    rw [this] at h
    rw [mod_eight_expand] at h
    omega
  · use 4 * (x / 8) + 1
    omega
  · have : x = 8 * (x / 8) + 4 := by omega
    rw [this] at h
    rw [mod_eight_expand] at h
    omega
  · use 4 * (x / 8) + 2
    omega
  · have : x = 8 * (x / 8) + 6 := by omega
    rw [this] at h
    rw [mod_eight_expand] at h
    omega
  · use 4 * (x / 8) + 3
    omega

lemma div_four_of_sq_mod_eight_zero (x : ℕ) (h : (x ^ 2) % 8 = 0) : ∃ k, x = 4 * k := by
  have h_mod : x % 8 < 8 := Nat.mod_lt x (by decide)
  interval_cases h_x : x % 8
  · use 2 * (x / 8)
    omega
  · have : x = 8 * (x / 8) + 1 := by omega
    rw [this] at h
    rw [mod_eight_expand] at h
    omega
  · have : x = 8 * (x / 8) + 2 := by omega
    rw [this] at h
    rw [mod_eight_expand] at h
    omega
  · have : x = 8 * (x / 8) + 3 := by omega
    rw [this] at h
    rw [mod_eight_expand] at h
    omega
  · use 2 * (x / 8) + 1
    omega
  · have : x = 8 * (x / 8) + 5 := by omega
    rw [this] at h
    rw [mod_eight_expand] at h
    omega
  · have : x = 8 * (x / 8) + 6 := by omega
    rw [this] at h
    rw [mod_eight_expand] at h
    omega
  · have : x = 8 * (x / 8) + 7 := by omega
    rw [this] at h
    rw [mod_eight_expand] at h
    omega



lemma sq_eq_eight_triangular (x : ℕ) : (2 * x + 1) ^ 2 = 8 * triangular x + 1 := by
  unfold triangular
  have h_even := triangular_even x
  have h_cancel := Nat.mul_div_cancel' h_even
  have h_ring : 8 * (x * (x + 1) / 2) = 4 * (2 * (x * (x + 1) / 2)) := by ring
  rw [h_ring, h_cancel]
  ring

lemma sum_three_triangular_plus_squares (n : ℕ) :
    ∃ x y z j : ℕ, n = triangular x + triangular y + triangular z + 2 * j ^ 2 := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares (8 * n + 3)
  have ha_sq := sq_mod_eight a
  have hb_sq := sq_mod_eight b
  have hc_sq := sq_mod_eight c
  have hd_sq := sq_mod_eight d
  have h_mod : (a^2 + b^2 + c^2 + d^2) % 8 = 3 := by
    rw [h]
    omega
  have h_mod2 : (a^2 % 8 + b^2 % 8 + c^2 % 8 + d^2 % 8) % 8 = 3 := by
    omega
  rcases ha_sq with ha0 | ha1 | ha4
  <;> rcases hb_sq with hb0 | hb1 | hb4
  <;> rcases hc_sq with hc0 | hc1 | hc4
  <;> rcases hd_sq with hd0 | hd1 | hd4
  <;> try omega
  · obtain ⟨x_var, h_sq_x⟩ := odd_of_sq_mod_eight_one b hb1
    obtain ⟨y_var, h_sq_y⟩ := odd_of_sq_mod_eight_one c hc1
    obtain ⟨z_var, h_sq_z⟩ := odd_of_sq_mod_eight_one d hd1
    obtain ⟨j_var, h_sq_j⟩ := div_four_of_sq_mod_eight_zero a ha0
    use x_var, y_var, z_var, j_var
    have h_sq_a := sq_eq_eight_triangular x_var
    have h_sq_b := sq_eq_eight_triangular y_var
    have h_sq_c := sq_eq_eight_triangular z_var
    have h_j : (4 * j_var) ^ 2 = 16 * j_var ^ 2 := by ring
    rw [h_sq_j, h_sq_x, h_sq_y, h_sq_z] at h
    rw [h_j, h_sq_a, h_sq_b, h_sq_c] at h
    omega
  · obtain ⟨x_var, h_sq_x⟩ := odd_of_sq_mod_eight_one a ha1
    obtain ⟨y_var, h_sq_y⟩ := odd_of_sq_mod_eight_one c hc1
    obtain ⟨z_var, h_sq_z⟩ := odd_of_sq_mod_eight_one d hd1
    obtain ⟨j_var, h_sq_j⟩ := div_four_of_sq_mod_eight_zero b hb0
    use x_var, y_var, z_var, j_var
    have h_sq_a := sq_eq_eight_triangular x_var
    have h_sq_b := sq_eq_eight_triangular y_var
    have h_sq_c := sq_eq_eight_triangular z_var
    have h_j : (4 * j_var) ^ 2 = 16 * j_var ^ 2 := by ring
    rw [h_sq_x, h_sq_y, h_sq_z, h_sq_j] at h
    rw [h_j, h_sq_a, h_sq_b, h_sq_c] at h
    omega
  · obtain ⟨x, hx⟩ := odd_of_sq_mod_eight_one a ha1
    obtain ⟨y, hy⟩ := odd_of_sq_mod_eight_one b hb1
    obtain ⟨z, hz⟩ := odd_of_sq_mod_eight_one d hd1
    obtain ⟨j, hj⟩ := div_four_of_sq_mod_eight_zero c hc0
    use x, y, z, j
    have h_sq_a := sq_eq_eight_triangular x
    have h_sq_b := sq_eq_eight_triangular y
    have h_sq_c := sq_eq_eight_triangular z
    have h_j : (4 * j) ^ 2 = 16 * j ^ 2 := by ring
    rw [hx, hy, hz, hj] at h
    rw [h_j, h_sq_a, h_sq_b, h_sq_c] at h
    omega
  · obtain ⟨x, hx⟩ := odd_of_sq_mod_eight_one a ha1
    obtain ⟨y, hy⟩ := odd_of_sq_mod_eight_one b hb1
    obtain ⟨z, hz⟩ := odd_of_sq_mod_eight_one c hc1
    obtain ⟨j, hj⟩ := div_four_of_sq_mod_eight_zero d hd0
    use x, y, z, j
    have h_sq_a := sq_eq_eight_triangular x
    have h_sq_b := sq_eq_eight_triangular y
    have h_sq_c := sq_eq_eight_triangular z
    have h_j : (4 * j) ^ 2 = 16 * j ^ 2 := by ring
    rw [hx, hy, hz, hj] at h
    rw [h_j, h_sq_a, h_sq_b, h_sq_c] at h
    omega


#check Nat.sum_three_triangular
