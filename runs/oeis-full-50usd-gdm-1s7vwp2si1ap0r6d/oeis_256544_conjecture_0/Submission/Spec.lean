import FormalConjectures.Util.ProblemImports

open Nat Finset

/-- The triangular number $T(x) = x(x+1)/2$. -/
def triangular (x : ℕ) : ℕ := x * (x + 1) / 2

/--
The set of values $V = \{ \lfloor T(x)/3 \rfloor : x \ge 1 \}$ that are less than or equal to $n$.
We generate values for $x \ge 1$ using $x \mapsto x.succ$ over a range, and rely on the filter $v \le n$ to constrain the set.
-/
def A256544_elements (n : ℕ) : Finset ℕ :=
  -- A liberal safe bound for $x$: $4n+2$ is sufficient since $T(x)/3$ grows quadratically.
  let max_range : ℕ := 4 * n + 2
  -- Use x.succ to ensure $x \ge 1$ generators.
  (range max_range).image (fun x : ℕ => (triangular x.succ) / 3)
    |> Finset.filter (fun v => v ≤ n)

/--
A256544: Number of ways to write $n$ as the sum of three unordered elements of the set $\{ \lfloor T(x)/3 \rfloor : x = 1, 2, 3, \dots \}$, where $T(x)$ denotes the triangular number $x(x+1)/2$.
This is computed by counting the number of ordered triples $(a, b, c)$ from the set $V$ such that $a \le b \le c$ and $a + b + c = n$.
-/
def A256544 (n : ℕ) : ℕ :=
  let Vs := A256544_elements n

  -- Iterate over all $a, b, c \in Vs$ and count those that satisfy the ordered sum.
  Vs.sum fun a =>
    Vs.sum fun b =>
      -- The constraint a + b + c = n means we only need to check c.
      (Vs.filter fun c =>
        a ≤ b ∧ b ≤ c ∧ a + b + c = n
      ).card

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


lemma triangular_shift (m x j : ℕ) :
    triangular (x + 2 * j * m) = triangular x + m * (2 * x * j + 2 * (j ^ 2) * m + j) := by
  unfold triangular
  have h_mul : (x + 2 * j * m) * (x + 2 * j * m + 1) = 2 * ((x + 2 * j * m) * (x + 2 * j * m + 1) / 2) := by
    exact (Nat.mul_div_cancel' (triangular_even (x + 2 * j * m))).symm
  have h_mul2 : x * (x + 1) = 2 * (x * (x + 1) / 2) := by
    exact (Nat.mul_div_cancel' (triangular_even x)).symm
  have h_ring : (x + 2 * j * m) * (x + 2 * j * m + 1) = x * (x + 1) + 2 * (m * (2 * x * j + 2 * (j ^ 2) * m + j)) := by
    ring
  rw [h_mul, h_mul2] at h_ring
  omega

lemma triangular_shift_div (m x j : ℕ) (hm : m > 0) :
    triangular (x + 2 * j * m) / m = triangular x / m + 2 * x * j + 2 * (j ^ 2) * m + j := by
  rw [triangular_shift]
  have h_comm : m * (2 * x * j + 2 * (j ^ 2) * m + j) = (2 * x * j + 2 * (j ^ 2) * m + j) * m := by ring
  rw [h_comm]
  rw [Nat.add_mul_div_right _ _ hm]
  omega


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

lemma partition_three (n K : ℕ) (hn : n ≤ 3 * K) :
    ∃ a b c : ℕ, a ≤ K ∧ b ≤ K ∧ c ≤ K ∧ a + b + c = n := by
  by_cases h1 : n ≤ K
  · use n, 0, 0
    omega
  · by_cases h2 : n ≤ 2 * K
    · use K, n - K, 0
      omega
    · use K, K, n - 2 * K
      omega

lemma oeis_256544_conjecture_0_bounded (m : ℕ) (hm : m ≥ 2) (n : ℕ) (hn : n ≤ 3 * (triangular (m - 1) / m)) :
    ∃ x y z : ℕ, n = triangular x / m + triangular y / m + triangular z / m := by
  have h_part := partition_three n (triangular (m - 1) / m) hn
  obtain ⟨a, b, c, ha, hb, hc, habc⟩ := h_part
  have h_fill := triangular_div_range_filling_helper m hm (m - 1) (by omega)
  obtain ⟨x, hx_le, hx_eq⟩ := h_fill a ha
  obtain ⟨y, hy_le, hy_eq⟩ := h_fill b hb
  obtain ⟨z, hz_le, hz_eq⟩ := h_fill c hc
  use x, y, z
  omega

lemma oeis_256544_conjecture_0_bounded_strong (m : ℕ) (hm : m ≥ 2) (n : ℕ) (hn : n ≤ 3 * (triangular (m - 1) / m)) :
    ∃ x y z : ℕ, n = triangular x / m + triangular y / m + triangular z / m ∧ x ≤ m - 1 ∧ y ≤ m - 1 ∧ z ≤ m - 1 := by
  have h_part := partition_three n (triangular (m - 1) / m) hn
  obtain ⟨a, b, c, ha, hb, hc, habc⟩ := h_part
  have h_fill := triangular_div_range_filling_helper m hm (m - 1) (by omega)
  obtain ⟨x, hx_le, hx_eq⟩ := h_fill a ha
  obtain ⟨y, hy_le, hy_eq⟩ := h_fill b hb
  obtain ⟨z, hz_le, hz_eq⟩ := h_fill c hc
  use x, y, z
  refine ⟨by omega, hx_le, hy_le, hz_le⟩

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

lemma oeis_256544_conjecture_0_large_m (m : ℕ) (hm : m ≥ 2) (n : ℕ) (h_large : m ≥ 2 * n + 1) :
    ∃ x y z : ℕ, n = triangular x / m + triangular y / m + triangular z / m := by
  have hK : n ≤ triangular (m - 1) / m := by
    rw [triangular_div_self m hm]
    omega
  have h_fill := triangular_div_range_filling_helper m hm (m - 1) (by omega)
  obtain ⟨x, hx_le, hx_eq⟩ := h_fill n hK
  use x, 0, 0
  rw [hx_eq, triangular_zero]
  have h_zero : 0 / m = 0 := Nat.zero_div m
  rw [h_zero]
  omega

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


lemma sum_two_covers_range (m : ℕ) (hm : m ≥ 2) (R : ℕ) (hR : R < m) :
    ∃ y z : ℕ, y ≤ m ∧ z ≤ m ∧ R = triangular y / m + triangular z / m := by
  have hK := triangular_div_self m hm
  let K := triangular (m - 1) / m
  by_cases h1 : R ≤ K
  · have h_fill := triangular_div_range_filling_helper m hm (m - 1) (by omega)
    obtain ⟨y, hy_le, hy_eq⟩ := h_fill R (by omega)
    use y, 0
    refine ⟨by omega, by omega, ?_⟩
    rw [hy_eq, triangular_zero]
    have h_zero : 0 / m = 0 := Nat.zero_div m
    rw [h_zero, Nat.add_zero]
  · by_cases h2 : R ≤ 2 * K
    · have h_fill := triangular_div_range_filling_helper m hm (m - 1) (by omega)
      obtain ⟨z, hz_le, hz_eq⟩ := h_fill (R - K) (by omega)
      use m - 1, z
      refine ⟨by omega, by omega, ?_⟩
      rw [hz_eq]
      omega
    · have h_R_eq : R = 2 * K + 1 := by omega
      use m - 1, m
      refine ⟨by omega, by omega, ?_⟩
      have h_tm : triangular m / m = K + 1 := triangular_m_div m hm
      rw [h_tm]
      omega



lemma triangular_double (x : ℕ) : 2 * triangular x = x * (x + 1) := by
  unfold triangular
  exact Nat.mul_div_cancel' (triangular_even x)

lemma triangular_descent_identity (z : ℕ) (hz : z ≥ 1) :
    triangular (z + 2) + triangular (z - 1) = triangular (z + 1) + triangular z + 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : z ≠ 0)
  change triangular (k + 3) + triangular k = triangular (k + 2) + triangular (k + 1) + 2
  have h : 2 * (triangular (k + 3) + triangular k) = 2 * (triangular (k + 2) + triangular (k + 1) + 2) := by
    rw [mul_add, mul_add, mul_add]
    rw [triangular_double, triangular_double, triangular_double, triangular_double]
    ring
  omega

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

/--
Conjecture: For any positive integer m, every nonnegative integer n can be written as
floor(T(x)/m) + floor(T(y)/m) + floor(T(z)/m) with x,y,z nonnegative integers.
-/
theorem oeis_256544_conjecture_0 (m : ℕ) (hm : m > 0) (n : ℕ) :
    ∃ x y z : ℕ, n = triangular x / m + triangular y / m + triangular z / m := by
  by_cases hm2 : m ≥ 2
  · by_cases hn : n ≤ 3 * (triangular (m - 1) / m)
    · exact oeis_256544_conjecture_0_bounded m hm2 n hn
    · by_cases h_large : m ≥ 2 * n + 1
      · exact oeis_256544_conjecture_0_large_m m hm2 n h_large
      · -- Middle case: n > 3 * (T(m-1)/m) and m < 2n+1.
        -- We use the strong induction step or range filling.
        sorry
  · have hm1 : m = 1 := by omega
    subst hm1
    by_cases hn0 : n = 0
    · use 0, 0, 0
      rw [hn0, triangular_zero]
    · -- Gauss's Eureka Theorem:
      -- We have n = T(x) + T(y) + T(z) + 2j^2.
      obtain ⟨x, y, z, j, hj⟩ := sum_three_triangular_plus_squares n
      sorry


#check Nat.sum_four_squares




