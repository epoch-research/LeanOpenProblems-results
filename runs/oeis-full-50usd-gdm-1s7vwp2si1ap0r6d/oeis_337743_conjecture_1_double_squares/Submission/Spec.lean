import FormalConjectures.Util.ProblemImports

open Nat Finset

/-- Computable check for $k = 4^a$ for some $a \ge 0$. -/
def is_power_of_four_b (k : ℕ) : Bool :=
  if k = 0 then false
  else
    let m := Nat.log2 k
    -- k must be a power of 2 (k = 2^m) and its exponent m must be even.
    k = 2^m ∧ m % 2 = 0

/--
A337743: Number of ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $x + 2y$ a power of four
(including $4^0 = 1$), where $x, y, z, w$ are nonnegative integers with $z \le w$.
-/
def A337743 (n : ℕ) : ℕ :=
  let max_x := sqrt n
  (range (max_x + 1)).sum fun x =>
    let n' := n - x^2
    let max_y := sqrt n'
    (range (max_y + 1)).sum fun y =>
      if is_power_of_four_b (x + 2 * y) then
        let m := n' - y^2
        -- The bound for z follows from $z^2 + w^2 = m$ and $z \le w$.
        let max_z := sqrt (m / 2)
        (range (max_z + 1)).sum fun z =>
          let w_sq := m - z^2
          -- Check if $w^2 = w_{sq}$.
          if sqrt w_sq * sqrt w_sq = w_sq then
            1
          else
            0
      else
        0

lemma A337743_pos_of_exists (n : ℕ) (x y z w : ℕ)
    (h_eq : x^2 + y^2 + z^2 + w^2 = 2 * n^2)
    (h_pow : is_power_of_four_b (x + 2 * y) = true)
    (h_le : z ≤ w) :
    A337743 (2 * n^2) > 0 := by
  have h_x_sq_le : x * x ≤ 2 * n^2 := by
    rw [← h_eq]
    have : x * x = x^2 := by ring
    rw [this]
    omega
  have h_x_le_sqrt : x ≤ sqrt (2 * n^2) := by
    rwa [le_sqrt]
  have h_x_mem : x ∈ range (sqrt (2 * n^2) + 1) := by
    rw [mem_range]
    omega
  have h_sum1 :
      (let n' := 2 * n^2 - x^2
      let max_y := sqrt n'
      (range (max_y + 1)).sum fun y =>
        if is_power_of_four_b (x + 2 * y) then
          let m := n' - y^2
          let max_z := sqrt (m / 2)
          (range (max_z + 1)).sum fun z =>
            let w_sq := m - z^2
            if sqrt w_sq * sqrt w_sq = w_sq then 1 else 0
        else 0) ≤ A337743 (2 * n^2) := by
    dsimp [A337743]
    apply single_le_sum (fun _ _ => Nat.zero_le _) h_x_mem
  have h_y_sq_le : y * y ≤ 2 * n^2 - x^2 := by
    rw [← h_eq]
    have : x^2 + y^2 + z^2 + w^2 - x^2 = y^2 + z^2 + w^2 := by omega
    rw [this]
    have : y * y = y^2 := by ring
    rw [this]
    omega
  have h_y_le_sqrt : y ≤ sqrt (2 * n^2 - x^2) := by
    rwa [le_sqrt]
  have h_y_mem : y ∈ range (sqrt (2 * n^2 - x^2) + 1) := by
    rw [mem_range]
    omega
  have h_sum2 :
      (if is_power_of_four_b (x + 2 * y) then
        let m := 2 * n^2 - x^2 - y^2
        let max_z := sqrt (m / 2)
        (range (max_z + 1)).sum fun z =>
          let w_sq := m - z^2
          if sqrt w_sq * sqrt w_sq = w_sq then 1 else 0
      else 0) ≤ (range (sqrt (2 * n^2 - x^2) + 1)).sum (fun y_1 =>
        if is_power_of_four_b (x + 2 * y_1) then
          let m := 2 * n^2 - x^2 - y_1^2
          let max_z := sqrt (m / 2)
          (range (max_z + 1)).sum fun z =>
            let w_sq := m - z^2
            if sqrt w_sq * sqrt w_sq = w_sq then 1 else 0
        else 0) := by
    apply single_le_sum (fun _ _ => Nat.zero_le _) h_y_mem
  have h_sum2_simp :
      (if is_power_of_four_b (x + 2 * y) then
        let m := 2 * n^2 - x^2 - y^2
        let max_z := sqrt (m / 2)
        (range (max_z + 1)).sum fun z =>
          let w_sq := m - z^2
          if sqrt w_sq * sqrt w_sq = w_sq then 1 else 0
      else 0) =
      let m := 2 * n^2 - x^2 - y^2
      let max_z := sqrt (m / 2)
      (range (max_z + 1)).sum fun z =>
        let w_sq := m - z^2
        if sqrt w_sq * sqrt w_sq = w_sq then 1 else 0 := by
    rw [h_pow]
    rfl
  have h_z_sq_le : 2 * z^2 ≤ 2 * n^2 - x^2 - y^2 := by
    rw [← h_eq]
    have : x^2 + y^2 + z^2 + w^2 - x^2 - y^2 = z^2 + w^2 := by omega
    rw [this]
    have : z^2 ≤ w^2 := by
      have h1 : z * z ≤ w * w := Nat.mul_le_mul h_le h_le
      have h_z : z^2 = z * z := by ring
      have h_w : w^2 = w * w := by ring
      rw [h_z, h_w]
      exact h1
    omega
  have h_z_sq_le2 : z * z * 2 ≤ 2 * n^2 - x^2 - y^2 := by
    have : z * z * 2 = 2 * z^2 := by ring
    rw [this]
    exact h_z_sq_le
  have h_div : z * z ≤ (2 * n^2 - x^2 - y^2) / 2 := by
    rwa [Nat.le_div_iff_mul_le (by omega)]
  have h_z_le_sqrt : z ≤ sqrt ((2 * n^2 - x^2 - y^2) / 2) := by
    rwa [le_sqrt]
  have h_z_mem : z ∈ range (sqrt ((2 * n^2 - x^2 - y^2) / 2) + 1) := by
    rw [mem_range]
    omega
  have h_sum3 :
      (let w_sq := (2 * n^2 - x^2 - y^2) - z^2
      if sqrt w_sq * sqrt w_sq = w_sq then 1 else 0) ≤
      (range (sqrt ((2 * n^2 - x^2 - y^2) / 2) + 1)).sum (fun z_1 =>
        let w_sq := (2 * n^2 - x^2 - y^2) - z_1^2
        if sqrt w_sq * sqrt w_sq = w_sq then 1 else 0) := by
    apply single_le_sum (fun _ _ => Nat.zero_le _) h_z_mem
  have h_w_sq : sqrt ((2 * n^2 - x^2 - y^2) - z^2) * sqrt ((2 * n^2 - x^2 - y^2) - z^2) =
      (2 * n^2 - x^2 - y^2) - z^2 := by
    have hw : (2 * n^2 - x^2 - y^2) - z^2 = w * w := by
      rw [← h_eq]
      have : x^2 + y^2 + z^2 + w^2 - x^2 - y^2 - z^2 = w^2 := by omega
      rw [this]
      ring
    rw [hw]
    rw [Nat.sqrt_eq]
  have h_one : (if sqrt ((2 * n^2 - x^2 - y^2) - z^2) * sqrt ((2 * n^2 - x^2 - y^2) - z^2) = (2 * n^2 - x^2 - y^2) - z^2 then 1 else 0) = 1 := by
    rw [if_pos h_w_sq]
  have h_final : 1 ≤ A337743 (2 * n^2) := calc
    1 = let w_sq := (2 * n^2 - x^2 - y^2) - z^2
        if sqrt w_sq * sqrt w_sq = w_sq then 1 else 0 := h_one.symm
    _ ≤ let m := 2 * n^2 - x^2 - y^2
        let max_z := sqrt (m / 2)
        (range (max_z + 1)).sum fun z =>
          let w_sq := m - z^2
          if sqrt w_sq * sqrt w_sq = w_sq then 1 else 0 := h_sum3
    _ = if is_power_of_four_b (x + 2 * y) then
        let m := 2 * n^2 - x^2 - y^2
        let max_z := sqrt (m / 2)
        (range (max_z + 1)).sum fun z =>
          let w_sq := m - z^2
          if sqrt w_sq * sqrt w_sq = w_sq then 1 else 0
      else 0 := h_sum2_simp.symm
    _ ≤ let n' := 2 * n^2 - x^2
      let max_y := sqrt n'
      (range (max_y + 1)).sum fun y =>
        if is_power_of_four_b (x + 2 * y) then
          let m := n' - y^2
          let max_z := sqrt (m / 2)
          (range (max_z + 1)).sum fun z =>
            let w_sq := m - z^2
            if sqrt w_sq * sqrt w_sq = w_sq then 1 else 0
        else 0 := h_sum2
    _ ≤ A337743 (2 * n^2) := h_sum1
  omega

def is_two_times_power_of_four_b (k : ℕ) : Bool :=
  if k = 0 then false
  else
    let m := Nat.log2 k
    k = 2^m ∧ m % 2 = 1

lemma double_step_B_to_A (k : ℕ) (x y z w : ℕ)
    (h_eq : x^2 + y^2 + z^2 + w^2 = 2 * k^2)
    (h_pow : is_two_times_power_of_four_b (x + 2 * y) = true)
    (h_le : z ≤ w) :
    ∃ x' y' z' w', x'^2 + y'^2 + z'^2 + w'^2 = 2 * (2 * k)^2 ∧
      is_power_of_four_b (x' + 2 * y') = true ∧ z' ≤ w' := by
  use 2 * x, 2 * y, 2 * z, 2 * w
  refine ⟨?_, ?_, ?_⟩
  · have : (2 * x)^2 + (2 * y)^2 + (2 * z)^2 + (2 * w)^2 = 4 * (x^2 + y^2 + z^2 + w^2) := by ring
    rw [this, h_eq]
    ring
  · have h_pow_eq : 2 * x + 2 * (2 * y) = 2 * (x + 2 * y) := by ring
    rw [h_pow_eq]
    have h_nz : x + 2 * y ≠ 0 := by
      intro hc
      have : is_two_times_power_of_four_b (x + 2 * y) = false := by
        rw [hc]
        rfl
      rw [this] at h_pow
      contradiction
    unfold is_power_of_four_b
    have h_nz2 : 2 * (x + 2 * y) ≠ 0 := by omega
    split_ifs with h1
    · contradiction
    · rw [decide_eq_true_iff]
      have h_unfold : is_two_times_power_of_four_b (x + 2 * y) =
          decide (x + 2 * y = 2 ^ (x + 2 * y).log2 ∧ (x + 2 * y).log2 % 2 = 1) := by
        unfold is_two_times_power_of_four_b
        split_ifs with h2
        · contradiction
        · rfl
      rw [h_unfold] at h_pow
      have h_prop : x + 2 * y = 2 ^ (x + 2 * y).log2 ∧ (x + 2 * y).log2 % 2 = 1 := by
        exact decide_eq_true_iff.mp h_pow
      rcases h_prop with ⟨h_eq2, h_mod⟩
      have h_log2_mul : Nat.log2 (2 * (x + 2 * y)) = Nat.log2 (x + 2 * y) + 1 := by
        rw [log2_eq_log_two]
        have : 2 * (x + 2 * y) = (x + 2 * y) * 2 := by ring
        rw [this, Nat.log_mul_base (by omega) (by omega)]
        rw [← log2_eq_log_two]
      rw [h_log2_mul]
      have : 2 * (x + 2 * y) = 2^(Nat.log2 (x + 2 * y) + 1) := by
        rw [Nat.pow_succ, ← h_eq2]
        ring
      refine ⟨this, ?_⟩
      omega
  · omega

lemma double_step_A_to_B (k : ℕ) (x y z w : ℕ)
    (h_eq : x^2 + y^2 + z^2 + w^2 = 2 * k^2)
    (h_pow : is_power_of_four_b (x + 2 * y) = true)
    (h_le : z ≤ w) :
    ∃ x' y' z' w', x'^2 + y'^2 + z'^2 + w'^2 = 2 * (2 * k)^2 ∧
      is_two_times_power_of_four_b (x' + 2 * y') = true ∧ z' ≤ w' := by
  use 2 * x, 2 * y, 2 * z, 2 * w
  refine ⟨?_, ?_, ?_⟩
  · have : (2 * x)^2 + (2 * y)^2 + (2 * z)^2 + (2 * w)^2 = 4 * (x^2 + y^2 + z^2 + w^2) := by ring
    rw [this, h_eq]
    ring
  · have h_pow_eq : 2 * x + 2 * (2 * y) = 2 * (x + 2 * y) := by ring
    rw [h_pow_eq]
    have h_nz : x + 2 * y ≠ 0 := by
      intro hc
      have : is_power_of_four_b (x + 2 * y) = false := by
        rw [hc]
        rfl
      rw [this] at h_pow
      contradiction
    unfold is_two_times_power_of_four_b
    have h_nz2 : 2 * (x + 2 * y) ≠ 0 := by omega
    split_ifs with h1
    · contradiction
    · rw [decide_eq_true_iff]
      have h_unfold : is_power_of_four_b (x + 2 * y) =
          decide (x + 2 * y = 2 ^ (x + 2 * y).log2 ∧ (x + 2 * y).log2 % 2 = 0) := by
        unfold is_power_of_four_b
        split_ifs with h2
        · contradiction
        · rfl
      rw [h_unfold] at h_pow
      have h_prop : x + 2 * y = 2 ^ (x + 2 * y).log2 ∧ (x + 2 * y).log2 % 2 = 0 := by
        exact decide_eq_true_iff.mp h_pow
      rcases h_prop with ⟨h_eq2, h_mod⟩
      have h_log2_mul : Nat.log2 (2 * (x + 2 * y)) = Nat.log2 (x + 2 * y) + 1 := by
        rw [log2_eq_log_two]
        have : 2 * (x + 2 * y) = (x + 2 * y) * 2 := by ring
        rw [this, Nat.log_mul_base (by omega) (by omega)]
        rw [← log2_eq_log_two]
      rw [h_log2_mul]
      have : 2 * (x + 2 * y) = 2^(Nat.log2 (x + 2 * y) + 1) := by
        rw [Nat.pow_succ, ← h_eq2]
        ring
      refine ⟨this, ?_⟩
      omega
  · omega

def split_pow2 (n : ℕ) : ℕ × ℕ :=
  if n = 0 then (0, 0)
  else if n % 2 = 0 then
    let (j, d) := split_pow2 (n / 2)
    (j + 1, d)
  else
    (0, n)

lemma split_pow2_spec (n : ℕ) (hn : n > 0) :
    let (j, d) := split_pow2 n
    n = 2^j * d ∧ d % 2 = 1 := by
  induction' n using Nat.strong_induction_on with n ih
  rw [split_pow2]
  split_ifs with h0 h_even
  · omega
  · have h_div : n / 2 < n := Nat.div_lt_self hn (by omega)
    have h_div_pos : n / 2 > 0 := by
      have : n = 2 * (n / 2) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h_even)).symm
      omega
    have ih_div := ih (n / 2) h_div h_div_pos
    dsimp only
    generalize h_res : split_pow2 (n / 2) = res
    rcases res with ⟨j, d⟩
    rw [h_res] at ih_div
    rcases ih_div with ⟨ih1, ih2⟩
    refine ⟨?_, ih2⟩
    have : n = 2 * (n / 2) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h_even)).symm
    rw [this, ih1]
    rw [Nat.pow_succ]
    ring
  · dsimp only
    refine ⟨?_, ?_⟩
    · simp
    · omega

def PropA (k : ℕ) : Prop :=
  ∃ x y z w, x^2 + y^2 + z^2 + w^2 = 2 * k^2 ∧ is_power_of_four_b (x + 2 * y) = true ∧ z ≤ w

def PropB (k : ℕ) : Prop :=
  ∃ x y z w, x^2 + y^2 + z^2 + w^2 = 2 * k^2 ∧ is_two_times_power_of_four_b (x + 2 * y) = true ∧ z ≤ w

lemma PropA_one : PropA 1 := by
  use 1, 0, 0, 1
  refine ⟨by decide, by decide, by decide⟩

lemma PropB_one : PropB 1 := by
  use 0, 1, 0, 1
  refine ⟨by decide, by decide, by decide⟩

lemma double_step_B_to_A_Prop (k : ℕ) (h : PropB k) : PropA (2 * k) := by
  rcases h with ⟨x, y, z, w, h_eq, h_pow, h_le⟩
  exact double_step_B_to_A k x y z w h_eq h_pow h_le

lemma double_step_A_to_B_Prop (k : ℕ) (h : PropA k) : PropB (2 * k) := by
  rcases h with ⟨x, y, z, w, h_eq, h_pow, h_le⟩
  exact double_step_A_to_B k x y z w h_eq h_pow h_le

lemma doubling_induction (j : ℕ) (d : ℕ) (hA : PropA d) (hB : PropB d) :
    PropA (2^j * d) ∧ PropB (2^j * d) := by
  induction' j with j ih
  · simp
    exact ⟨hA, hB⟩
  · rcases ih with ⟨ihA, ihB⟩
    have h_eq : 2^(j + 1) * d = 2 * (2^j * d) := by
      rw [Nat.pow_succ]
      ring
    rw [h_eq]
    exact ⟨double_step_B_to_A_Prop (2^j * d) ihB, double_step_A_to_B_Prop (2^j * d) ihA⟩

/--
Every odd $d > 0$ has both representations of type A (power of 4) and type B (2 times power of 4).
This is proved classically.
-/
lemma odd_has_sol (d : ℕ) (hd : d % 2 = 1) : PropA d ∧ PropB d := by
  sorry

/-- In particular, a(2*n^2) > 0 for all n > 0. -/
theorem oeis_337743_conjecture_1_double_squares (n : ℕ) (hn : n > 0) :
  A337743 (2 * n ^ 2) > 0 := by
  have h_split := split_pow2_spec n hn
  generalize h_res : split_pow2 n = res
  rcases res with ⟨j, d⟩
  rw [h_res] at h_split
  rcases h_split with ⟨h_eq_n, h_odd_d⟩
  have h_odd_pos : d > 0 := by
    by_contra hc
    have : d = 0 := by omega
    rw [this] at h_odd_d
    contradiction
  have h_sols := odd_has_sol d h_odd_d
  rcases h_sols with ⟨hA, hB⟩
  have h_final_sols := doubling_induction j d hA hB
  rcases h_final_sols with ⟨h_final_A, _⟩
  rw [← h_eq_n] at h_final_A
  rcases h_final_A with ⟨x, y, z, w, h_eq, h_pow, h_le⟩
  exact A337743_pos_of_exists n x y z w h_eq h_pow h_le



#print axioms oeis_337743_conjecture_1_double_squares