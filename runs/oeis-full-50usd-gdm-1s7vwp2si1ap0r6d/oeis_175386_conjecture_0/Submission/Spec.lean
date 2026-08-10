import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 1500000


open scoped BigOperators

/--
A175386: $a(n)$ is the denominator of the sum
$$\sum_{i=1}^n \frac{1}{i} \binom{2n-i-1}{i-1}$$
-/
def a (n : ℕ) : ℕ :=
  (Finset.sum (Finset.Icc 1 n) fun i : ℕ =>
    -- The upper index is $2n - i - 1$, which is equivalent to $2n - (i+1)$ in $\mathbb{N}$ for $i \le n$.
    -- The lower index $i-1$ is standard subtraction in $\mathbb{N}$.
    let num : ℕ := Nat.choose (2 * n - (i + 1)) (i - 1)
    (num : ℚ) / (i : ℚ)
  ).den

/-- The sum which A175386 $a(n)$ is the denominator of. -/
def S (n : ℕ) : ℚ :=
  Finset.sum (Finset.Icc 1 n) fun i : ℕ =>
    let num : ℕ := Nat.choose (2 * n - (i + 1)) (i - 1)
    (num : ℚ) / (i : ℚ)

def H (n : ℕ) : ℕ :=
  Finset.sum (Finset.Icc 1 n) fun i : ℕ =>
    Nat.choose (2 * n - i) i + Nat.choose (2 * n - i - 1) (i - 1)

theorem term_identity (n i : ℕ) (hn : 1 < n) (hi : i ∈ Finset.Icc 1 n) :
    2 * n * Nat.choose (2 * n - i - 1) (i - 1) =
    i * (Nat.choose (2 * n - i) i + Nat.choose (2 * n - i - 1) (i - 1)) := by
  have h_icc : 1 ≤ i ∧ i ≤ n := by
    rwa [Finset.mem_Icc] at hi
  have h1 : 1 ≤ i := h_icc.1
  have h2 : i ≤ n := h_icc.2
  have h3 : i < 2 * n := by
    omega
  have h4 : 2 * n - i - 1 + 1 = 2 * n - i := by
    omega
  have h5 : i - 1 + 1 = i := by
    omega
  have habs := Nat.add_one_mul_choose_eq (2 * n - i - 1) (i - 1)
  rw [h4, h5] at habs
  have h_sub_add : 2 * n - i + i = 2 * n := by
    omega
  have h_rhs : i * (Nat.choose (2 * n - i) i + Nat.choose (2 * n - i - 1) (i - 1)) =
               (Nat.choose (2 * n - i) i * i) + i * Nat.choose (2 * n - i - 1) (i - 1) := by
    ring
  rw [h_rhs]
  rw [← habs]
  have h_factor : (2 * n - i) * Nat.choose (2 * n - i - 1) (i - 1) + i * Nat.choose (2 * n - i - 1) (i - 1) =
                  (2 * n - i + i) * Nat.choose (2 * n - i - 1) (i - 1) := by
    ring
  rw [h_factor]
  rw [h_sub_add]

theorem H_eq_S (n : ℕ) (hn : 1 < n) : (2 * n : ℚ) * S n = (H n : ℚ) := by
  unfold S H
  rw [Finset.mul_sum]
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have h_icc : 1 ≤ i ∧ i ≤ n := by
    rwa [Finset.mem_Icc] at hi
  have h_i_gt : (i : ℚ) > 0 := by
    have : i > 0 := by omega
    positivity
  have hi_nz : (i : ℚ) ≠ 0 := by positivity
  rw [← mul_div_assoc]
  rw [div_eq_iff hi_nz]
  have h_sub : 2 * n - (i + 1) = 2 * n - i - 1 := by omega
  have h_id := term_identity n i hn hi
  rw [h_sub]
  rw [mul_comm _ (i : ℚ)]
  exact_mod_cast h_id

theorem a_eq_one_iff (n : ℕ) (hn : 1 < n) : a n = 1 ↔ (2 * n) ∣ H n := by
  have h_nz : (2 * n : ℚ) ≠ 0 := by
    have : 2 * n > 0 := by omega
    positivity
  have h_div : S n = (H n : ℚ) / (2 * n : ℚ) := by
    rw [← H_eq_S n hn]
    rw [mul_div_cancel_left₀ (S n) h_nz]
  have h_a_eq : a n = (S n).den := rfl
  rw [h_a_eq, h_div]
  have h_nz_nat : 2 * n ≠ 0 := by omega
  have h_cast : (2 * n : ℚ) = ((2 * n : ℕ) : ℚ) := by norm_cast
  rw [h_cast]
  exact Rat.den_div_natCast_eq_one_iff (H n) (2 * n) h_nz_nat

theorem test_fib_sum (n : ℕ) : Nat.fib (n + 1) = ∑ k ∈ Finset.range (n + 1), Nat.choose k (n - k) := by
  rw [Nat.fib_succ_eq_sum_choose]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ]

theorem test_reflect (n : ℕ) : ∑ i ∈ Finset.range (2 * n + 1), Nat.choose (2 * n - i) i = ∑ i ∈ Finset.range (2 * n + 1), Nat.choose i (2 * n - i) := by
  have h1 := Finset.sum_range_reflect (fun i => Nat.choose i (2 * n - i)) (2 * n + 1)
  have h2 : ∑ i ∈ Finset.range (2 * n + 1), Nat.choose (2 * n + 1 - 1 - i) (2 * n - (2 * n + 1 - 1 - i)) =
            ∑ i ∈ Finset.range (2 * n + 1), Nat.choose (2 * n - i) i := by
    apply Finset.sum_congr rfl
    intro i hi
    have : i < 2 * n + 1 := Finset.mem_range.1 hi
    have h_eq1 : 2 * n + 1 - 1 - i = 2 * n - i := by omega
    have h_eq2 : 2 * n - (2 * n - i) = i := by omega
    rw [h_eq1, h_eq2]
  rw [h2] at h1
  exact h1

theorem test_split (n : ℕ) (f : ℕ → ℕ) : ∑ i ∈ Finset.range (2 * n + 1), f i = ∑ i ∈ Finset.range (n + 1), f i + ∑ i ∈ Finset.range n, f (n + 1 + i) := by
  have h_add : 2 * n + 1 = (n + 1) + n := by omega
  rw [h_add]
  exact Finset.sum_range_add f (n + 1) n

theorem sum_choose_zero (n : ℕ) : ∑ i ∈ Finset.range n, Nat.choose (2 * n - (n + 1 + i)) (n + 1 + i) = 0 := by
  apply Finset.sum_eq_zero
  intro i _hi
  have : 2 * n - (n + 1 + i) < n + 1 + i := by omega
  exact Nat.choose_eq_zero_of_lt this

theorem sum_choose_eq_fib (n : ℕ) : ∑ i ∈ Finset.range (n + 1), Nat.choose (2 * n - i) i = Nat.fib (2 * n + 1) := by
  have h1 : ∑ i ∈ Finset.range (2 * n + 1), Nat.choose (2 * n - i) i = Nat.fib (2 * n + 1) := by
    rw [test_reflect]
    exact (test_fib_sum (2 * n)).symm
  have h2 : ∑ i ∈ Finset.range (2 * n + 1), Nat.choose (2 * n - i) i =
            ∑ i ∈ Finset.range (n + 1), Nat.choose (2 * n - i) i +
            ∑ i ∈ Finset.range n, Nat.choose (2 * n - (n + 1 + i)) (n + 1 + i) := by
    exact test_split n (fun i => Nat.choose (2 * n - i) i)
  rw [sum_choose_zero, add_zero] at h2
  rw [← h2]
  exact h1

theorem sum_Icc_to_sum_range (n : ℕ) (f : ℕ → ℕ) : ∑ i ∈ Finset.Icc 1 n, f (i - 1) = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h_insert : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have h_not : n + 1 ∉ Finset.Icc 1 n := by
      simp only [Finset.mem_Icc, not_and]
      intro _
      omega
    rw [h_insert, Finset.sum_insert h_not]
    rw [Finset.sum_range_succ]
    have h_sub : n + 1 - 1 = n := by omega
    rw [h_sub, ih]
    rw [add_comm]

theorem sum_choose_sub_eq_fib (n : ℕ) (hn : 1 ≤ n) : ∑ i ∈ Finset.Icc 1 n, Nat.choose (2 * n - i - 1) (i - 1) = Nat.fib (2 * n - 1) := by
  have h_eq : ∑ i ∈ Finset.Icc 1 n, Nat.choose (2 * n - i - 1) (i - 1) =
              ∑ i ∈ Finset.Icc 1 n, Nat.choose (2 * n - 2 - (i - 1)) (i - 1) := by
    apply Finset.sum_congr rfl
    intro i hi
    have h_icc : 1 ≤ i ∧ i ≤ n := by rwa [Finset.mem_Icc] at hi
    have h_sub : 2 * n - i - 1 = 2 * n - 2 - (i - 1) := by omega
    rw [h_sub]
  rw [h_eq]
  rw [sum_Icc_to_sum_range n (fun j => Nat.choose (2 * n - 2 - j) j)]
  have h_sub : 2 * n - 2 = 2 * (n - 1) := by omega
  rw [h_sub]
  have h_fib := sum_choose_eq_fib (n - 1)
  have h_range : Finset.range n = Finset.range (n - 1 + 1) := by
    congr 1
    omega
  rw [h_range]
  rw [h_fib]
  have h_fib_eq : 2 * (n - 1) + 1 = 2 * n - 1 := by omega
  rw [h_fib_eq]

theorem H_eq_fib (n : ℕ) (hn : 1 ≤ n) : H n = Nat.fib (2 * n + 1) + Nat.fib (2 * n - 1) - 1 := by
  unfold H
  rw [Finset.sum_add_distrib]
  have h_range : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have h_not : 0 ∉ Finset.Icc 1 n := by
    simp only [Finset.mem_Icc, not_and]
    omega
  have h_sum1 := sum_choose_eq_fib n
  rw [h_range, Finset.sum_insert h_not] at h_sum1
  have h_choose_0 : Nat.choose (2 * n - 0) 0 = 1 := by simp
  rw [h_choose_0] at h_sum1
  rw [sum_choose_sub_eq_fib n hn]
  omega



theorem fib_identity (n : ℕ) : Nat.fib (n + 4) + Nat.fib n = 3 * Nat.fib (n + 2) := by
  have h1 : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := by
    have : n + 4 = n + 2 + 2 := by omega
    rw [this, Nat.fib_add_two]
  have h2 : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := by
    have : n + 3 = n + 1 + 2 := by omega
    rw [this, Nat.fib_add_two]
  have h3 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := by
    rw [Nat.fib_add_two]
  omega

theorem H_recurrence (n : ℕ) (hn : 1 ≤ n) : H (n + 2) + H n = 3 * H (n + 1) + 1 := by
  have h_n2 := H_eq_fib (n + 2) (by omega)
  have h_n1 := H_eq_fib (n + 1) (by omega)
  have h_n := H_eq_fib n hn
  have h_fib1 := fib_identity (2 * n + 1)
  have h_fib2 : Nat.fib (2 * n - 1 + 4) + Nat.fib (2 * n - 1) = 3 * Nat.fib (2 * n - 1 + 2) := fib_identity (2 * n - 1)
  have h_idx1 : 2 * n + 1 + 4 = 2 * n + 5 := by omega
  have h_idx2 : 2 * n + 1 + 2 = 2 * n + 3 := by omega
  have h_idx3 : 2 * n - 1 + 4 = 2 * n + 3 := by omega
  have h_idx4 : 2 * n - 1 + 2 = 2 * n + 1 := by omega
  rw [h_idx1, h_idx2] at h_fib1
  rw [h_idx3, h_idx4] at h_fib2
  have h_idx_a : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
  have h_idx_b : 2 * (n + 2) - 1 = 2 * n + 3 := by omega
  have h_idx_c : 2 * (n + 1) + 1 = 2 * n + 3 := by omega
  have h_idx_d : 2 * (n + 2) + 1 = 2 * n + 5 := by omega
  rw [h_idx_a, h_idx_c] at h_n1
  rw [h_idx_b, h_idx_d] at h_n2
  have h_fib_pos1 : 0 < Nat.fib (2 * n - 1) := by simp; omega
  have h_fib_pos4 : 0 < Nat.fib (2 * n + 1) := by simp
  have h_fib_pos5 : 0 < Nat.fib (2 * n + 3) := by simp
  have h_fib_pos6 : 0 < Nat.fib (2 * n + 5) := by simp
  omega

def H_mod_prop (n : ℕ) : Prop :=
  H (n + 1) % 4 = (if 3 ∣ (n + 1) then 1 else 2) ∧
  H (n + 2) % 4 = (if 3 ∣ (n + 2) then 1 else 2)

theorem H_mod_prop_zero : H_mod_prop 0 := by
  unfold H_mod_prop
  decide

theorem H_mod_prop_succ (n : ℕ) (ih : H_mod_prop n) : H_mod_prop (n + 1) := by
  unfold H_mod_prop at *
  rcases ih with ⟨ih1, ih2⟩
  have h_add1 : n + 1 + 1 = n + 2 := by omega
  have h_add2 : n + 1 + 2 = n + 3 := by omega
  rw [h_add1, h_add2]
  refine ⟨ih2, ?_⟩
  have h_rec := H_recurrence (n + 1) (by omega)
  rw [h_add1, h_add2] at h_rec
  have h_mod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h_mod with h0 | h1 | h2
  · have h_div1 : ¬ 3 ∣ n + 1 := by omega
    have h_div2 : ¬ 3 ∣ n + 2 := by omega
    have h_div3 : 3 ∣ n + 3 := by omega
    rw [if_neg h_div1] at ih1
    rw [if_neg h_div2] at ih2
    rw [if_pos h_div3]
    omega
  · have h_div1 : ¬ 3 ∣ n + 1 := by omega
    have h_div2 : 3 ∣ n + 2 := by omega
    have h_div3 : ¬ 3 ∣ n + 3 := by omega
    rw [if_neg h_div1] at ih1
    rw [if_pos h_div2] at ih2
    rw [if_neg h_div3]
    omega
  · have h_div1 : 3 ∣ n + 1 := by omega
    have h_div2 : ¬ 3 ∣ n + 2 := by omega
    have h_div3 : ¬ 3 ∣ n + 3 := by omega
    rw [if_pos h_div1] at ih1
    rw [if_neg h_div2] at ih2
    rw [if_neg h_div3]
    omega

theorem H_mod_4 (n : ℕ) : H n % 4 = (if 3 ∣ n then 1 else 2) ∨ n = 0 := by
  cases n with
  | zero => simp
  | succ n =>
    have h_prop : H_mod_prop n := by
      induction n with
      | zero => exact H_mod_prop_zero
      | succ n ih => exact H_mod_prop_succ n ih
    unfold H_mod_prop at h_prop
    left
    exact h_prop.1

theorem H_odd_of_3_dvd (n : ℕ) (hn : 1 < n) (h3 : 3 ∣ n) : H n % 2 = 1 := by
  have h4 := H_mod_4 n
  rcases h4 with h_mod | h_zero
  · rw [if_pos h3] at h_mod
    omega
  · omega

theorem H_mod_4_eq_2_of_not_3_dvd (n : ℕ) (hn : 1 < n) (h3 : ¬ 3 ∣ n) : H n % 4 = 2 := by
  have h4 := H_mod_4 n
  rcases h4 with h_mod | h_zero
  · rw [if_neg h3] at h_mod
    exact h_mod
  · omega

theorem not_dvd_of_3_dvd (n : ℕ) (hn : 1 < n) (h3 : 3 ∣ n) : ¬ (2 * n) ∣ H n := by
  intro hdvd
  have h_even : 2 ∣ H n := by
    have : 2 ∣ 2 * n := dvd_mul_right 2 n
    exact dvd_trans this hdvd
  have h_odd := H_odd_of_3_dvd n hn h3
  have : H n % 2 = 0 := Nat.mod_eq_zero_of_dvd h_even
  omega

theorem not_dvd_of_not_3_dvd_even (n : ℕ) (hn : 1 < n) (h3 : ¬ 3 ∣ n) (heven : n % 2 = 0) : ¬ (2 * n) ∣ H n := by
  intro hdvd
  have h_4_dvd : 4 ∣ 2 * n := by
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero heven
    use k
    omega
  have h_4 : 4 ∣ H n := dvd_trans h_4_dvd hdvd
  have h_mod := H_mod_4_eq_2_of_not_3_dvd n hn h3
  have : H n % 4 = 0 := Nat.mod_eq_zero_of_dvd h_4
  omega


theorem cassini (k : ℕ) :
    Nat.fib (k + 1) ^ 2 + (if k % 2 = 1 then 1 else 0) =
    Nat.fib (k + 2) * Nat.fib k + (if k % 2 = 0 then 1 else 0) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h_mod : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases h_mod with hk | hk
    · rw [if_neg (by omega), if_pos hk] at ih
      rw [if_pos (by omega), if_neg (by omega)]
      rw [Nat.fib_add_two (n := k + 1)]
      have h_add : k + 1 + 1 = k + 2 := rfl
      rw [h_add]
      simp only [add_zero] at *
      have h_alg : (Nat.fib (k + 1) + Nat.fib (k + 2)) * Nat.fib (k + 1) =
                   Nat.fib (k + 1) ^ 2 + Nat.fib (k + 2) * Nat.fib (k + 1) := by ring
      rw [h_alg, ih]
      have h_factor : Nat.fib (k + 2) * Nat.fib k + 1 + Nat.fib (k + 2) * Nat.fib (k + 1) =
                      Nat.fib (k + 2) * (Nat.fib k + Nat.fib (k + 1)) + 1 := by ring
      rw [h_factor]
      rw [← Nat.fib_add_two (n := k)]
      ring
    · rw [if_pos hk, if_neg (by omega)] at ih
      rw [if_neg (by omega), if_pos (by omega)]
      rw [Nat.fib_add_two (n := k + 1)]
      have h_add : k + 1 + 1 = k + 2 := rfl
      rw [h_add]
      simp only [add_zero] at *
      have h_alg : (Nat.fib (k + 1) + Nat.fib (k + 2)) * Nat.fib (k + 1) + 1 =
                   (Nat.fib (k + 1) ^ 2 + 1) + Nat.fib (k + 2) * Nat.fib (k + 1) := by ring
      rw [h_alg, ih]
      have h_factor : Nat.fib (k + 2) * Nat.fib k + Nat.fib (k + 2) * Nat.fib (k + 1) =
                      Nat.fib (k + 2) * (Nat.fib k + Nat.fib (k + 1)) := by ring
      rw [h_factor]
      rw [← Nat.fib_add_two (n := k)]
      ring


theorem H_mod_5 (k : ℕ) :
    H (2 * k + 1) % 5 = 2 ∧ H (2 * k + 2) % 5 = 1 := by
  induction k with
  | zero =>
    have h_idx1 : 2 * 0 + 1 = 1 := rfl
    have h_idx2 : 2 * 0 + 2 = 2 := rfl
    have h1 : H 1 = 2 := rfl
    have h2 : H 2 = 6 := rfl
    rw [h_idx1, h_idx2]
    rw [h1, h2]
    decide
  | succ k ih =>
    rcases ih with ⟨ih1, ih2⟩
    have h_rec1 := H_recurrence (2 * k + 1) (by omega)
    have h_rec2 := H_recurrence (2 * k + 2) (by omega)
    have h_add1 : 2 * k + 1 + 2 = 2 * k + 3 := by omega
    have h_add2 : 2 * k + 1 + 1 = 2 * k + 2 := by omega
    have h_add3 : 2 * k + 2 + 2 = 2 * k + 4 := by omega
    have h_add4 : 2 * k + 2 + 1 = 2 * k + 3 := by omega
    rw [h_add1, h_add2] at h_rec1
    rw [h_add3, h_add4] at h_rec2
    have h_add5 : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
    have h_add6 : 2 * (k + 1) + 2 = 2 * k + 4 := by omega
    rw [h_add5, h_add6]
    omega

theorem fib_odd_identity (n : ℕ) (h_odd : n % 2 = 1) (h_gt : 1 ≤ n) :
    Nat.fib (2 * n + 1) + Nat.fib (2 * n - 1) = (Nat.fib (n + 1) + Nat.fib (n - 1)) ^ 2 + 2 := by
  have h1 := Nat.fib_two_mul_add_one n
  have h_sub : 2 * n - 1 = 2 * (n - 1) + 1 := by omega
  have h2 := Nat.fib_two_mul_add_one (n - 1)
  rw [← h_sub] at h2
  have h_sub_var : n - 1 + 1 = n := by omega
  rw [h_sub_var] at h2
  have h_sum : Nat.fib (2 * n + 1) + Nat.fib (2 * n - 1) =
               Nat.fib (n + 1) ^ 2 + 2 * Nat.fib n ^ 2 + Nat.fib (n - 1) ^ 2 := by omega
  rw [h_sum]
  have h_cas := cassini (n - 1)
  have h_mod : (n - 1) % 2 = 0 := by omega
  rw [if_pos h_mod, if_neg (by omega)] at h_cas
  have h_sub_var2 : n - 1 + 1 = n := by omega
  have h_sub_var3 : n - 1 + 2 = n + 1 := by omega
  rw [h_sub_var2, h_sub_var3] at h_cas
  simp only [add_zero] at h_cas
  rw [h_cas]
  ring

theorem H_odd_eq_sq_add_one (n : ℕ) (hn : 1 < n) (h_odd : n % 2 = 1) :
    H n = (Nat.fib (n + 1) + Nat.fib (n - 1)) ^ 2 + 1 := by
  have h_le : 1 ≤ n := by omega
  have h_H := H_eq_fib n h_le
  rw [h_H]
  have h_id := fib_odd_identity n h_odd h_le
  omega

theorem not_dvd_of_prime_three_mod_four (n : ℕ) (hn : 1 < n) (h_odd : n % 2 = 1)
    (p : ℕ) (hp : Nat.Prime p) (hp3 : p % 4 = 3) (h_div : p ∣ n) (hdvd : (2 * n) ∣ H n) : False := by
  have h_p_dvd_H : p ∣ H n := by
    have : p ∣ 2 * n := dvd_mul_of_dvd_right h_div 2
    exact dvd_trans this hdvd
  rw [H_odd_eq_sq_add_one n hn h_odd] at h_p_dvd_H
  have h_mod : ((Nat.fib (n + 1) + Nat.fib (n - 1)) ^ 2 + 1) % p = 0 := Nat.mod_eq_zero_of_dvd h_p_dvd_H
  have : Fact (Nat.Prime p) := ⟨hp⟩
  have hy : ((Nat.fib (n + 1) + Nat.fib (n - 1) : ℕ) : ZMod p) ^ 2 = -1 := by
    have h_cast : (((Nat.fib (n + 1) + Nat.fib (n - 1)) ^ 2 + 1 : ℕ) : ZMod p) = 0 := by
      rw [CharP.cast_eq_zero_iff (ZMod p) p]
      exact h_p_dvd_H
    push_cast
    push_cast at h_cast
    linear_combination h_cast
  have h_ne3 := ZMod.mod_four_ne_three_of_sq_eq_neg_one hy
  contradiction

theorem not_dvd_of_odd_five (n : ℕ) (hn : 1 < n) (h_odd : n % 2 = 1) (h_five : 5 ∣ n) (hdvd : (2 * n) ∣ H n) : False := by
  have h_5_dvd : 5 ∣ 2 * n := by
    obtain ⟨k, hk⟩ := h_five
    use 2 * k
    omega
  have h_5 : 5 ∣ H n := dvd_trans h_5_dvd hdvd
  obtain ⟨k, hk⟩ : ∃ k, n = 2 * k + 1 := by
    use n / 2
    omega
  have h_mod := (H_mod_5 k).1
  rw [← hk] at h_mod
  have : H n % 5 = 0 := Nat.mod_eq_zero_of_dvd h_5
  omega



theorem fib_identity_1_k (k : ℕ) :
    (Nat.fib (2 * k + 3) + Nat.fib (2 * k + 1)) ^ 2 = 5 * Nat.fib (2 * k + 2) ^ 2 + 4 := by
  have h_fib : Nat.fib (2 * k + 3) = Nat.fib (2 * k + 1) + Nat.fib (2 * k + 2) := by
    have : 2 * k + 3 = 2 * k + 1 + 2 := by omega
    rw [this, Nat.fib_add_two]
  have h_cas := cassini (2 * k + 1)
  have h_mod1 : (2 * k + 1) % 2 = 1 := by omega
  rw [if_pos h_mod1, if_neg (by omega)] at h_cas
  simp only [add_zero] at h_cas
  set A := Nat.fib (2 * k + 1)
  set B := Nat.fib (2 * k + 2)
  set C := Nat.fib (2 * k + 3)
  change (C + A) ^ 2 = 5 * B ^ 2 + 4
  have h_cas_cast : B ^ 2 + 1 = C * A := h_cas
  rw [h_fib] at h_cas_cast
  rw [h_fib]
  have h_eq : (A + B + A) ^ 2 = 4 * (A ^ 2 + A * B) + B ^ 2 := by ring
  rw [h_eq]
  have h_eq2 : A ^ 2 + A * B = B ^ 2 + 1 := by
    have : (A + B) * A = A ^ 2 + A * B := by ring
    rw [← this, ← h_cas_cast]
  rw [h_eq2]
  ring

theorem fib_identity_2 (n : ℕ) (hn : 1 ≤ n) :
    Nat.fib (6 * n) = Nat.fib (2 * n) * (5 * Nat.fib (2 * n) ^ 2 + 3) := by
  have h_three := Nat.fib_add (4 * n - 1) (2 * n)
  have h_idx1 : 4 * n - 1 + 2 * n + 1 = 6 * n := by omega
  have h_idx2 : 4 * n - 1 + 1 = 4 * n := by omega
  rw [h_idx1, h_idx2] at h_three
  -- h_three : Nat.fib (6 * n) = Nat.fib (4 * n - 1) * Nat.fib (2 * n) + Nat.fib (4 * n) * Nat.fib (2 * n + 1)
  have h_4n := Nat.fib_two_mul (2 * n)
  have h_idx3 : 2 * (2 * n) = 4 * n := by omega
  rw [h_idx3] at h_4n
  -- h_4n : Nat.fib (4 * n) = Nat.fib (2 * n) * (2 * Nat.fib (2 * n + 1) - Nat.fib (2 * n))
  have h_4n_sub := Nat.fib_two_mul_add_one (2 * n - 1)
  have h_idx4 : 2 * (2 * n - 1) + 1 = 4 * n - 1 := by omega
  have h_idx5 : 2 * n - 1 + 1 = 2 * n := by omega
  rw [h_idx4, h_idx5] at h_4n_sub
  -- h_4n_sub : Nat.fib (4 * n - 1) = Nat.fib (2 * n) ^ 2 + Nat.fib (2 * n - 1) ^ 2
  have h_cas := cassini (2 * n - 1)
  have h_mod1 : (2 * n - 1) % 2 = 1 := by omega
  rw [if_pos h_mod1, if_neg (by omega)] at h_cas
  simp only [add_zero] at h_cas
  have h_sub_cas1 : 2 * n - 1 + 1 = 2 * n := by omega
  have h_sub_cas2 : 2 * n - 1 + 2 = 2 * n + 1 := by omega
  rw [h_sub_cas1, h_sub_cas2] at h_cas
  -- h_cas : Nat.fib (2 * n) ^ 2 + 1 = Nat.fib (2 * n + 1) * Nat.fib (2 * n - 1)
  have h_fib_rec : Nat.fib (2 * n + 1) = Nat.fib (2 * n - 1) + Nat.fib (2 * n) := by
    have : 2 * n + 1 = 2 * n - 1 + 2 := by omega
    rw [this, Nat.fib_add_two]
    have h_sub : 2 * n - 1 + 1 = 2 * n := by omega
    rw [h_sub]
  set A := Nat.fib (2 * n - 1)
  set B := Nat.fib (2 * n)
  set C := Nat.fib (2 * n + 1)
  set D := Nat.fib (4 * n - 1)
  set E := Nat.fib (4 * n)
  have h_sub_val : 2 * C ≥ B := by
    rw [h_fib_rec]
    omega
  have h_4n_eq : E = B * (2 * C - B) := h_4n
  have h_4n_sub_eq : D = B ^ 2 + A ^ 2 := h_4n_sub
  have h_cas_cast : B ^ 2 + 1 = C * A := h_cas
  set a : ℤ := (Nat.fib (2 * n - 1) : ℤ)
  set b : ℤ := (Nat.fib (2 * n) : ℤ)
  set c : ℤ := (Nat.fib (2 * n + 1) : ℤ)
  set d : ℤ := (Nat.fib (4 * n - 1) : ℤ)
  set e : ℤ := (Nat.fib (4 * n) : ℤ)
  have h_fib_rec_z : c = a + b := by
    dsimp [a, b, c]
    norm_cast
  have h_4n_eq_z : e = b * (2 * c - b) := by
    have : e = ((E : ℕ) : ℤ) := rfl
    rw [this, h_4n_eq]
    push_cast
    have h_sub_eq : ((2 * C - B : ℕ) : ℤ) = 2 * c - b := by
      dsimp [b, c]
      push_cast
      omega
    rw [h_sub_eq]
  have h_4n_sub_eq_z : d = b ^ 2 + a ^ 2 := by
    dsimp [a, b, d]
    norm_cast
  have h_three_z : ((Nat.fib (6 * n) : ℕ) : ℤ) = d * b + e * c := by
    dsimp [b, c, d, e]
    norm_cast
  have h_cas_cast_z : b ^ 2 + 1 = c * a := by
    dsimp [a, b, c]
    norm_cast
  have h_final_z : ((Nat.fib (6 * n) : ℕ) : ℤ) = b * (5 * b ^ 2 + 3) := by
    rw [h_three_z, h_4n_eq_z, h_4n_sub_eq_z, h_fib_rec_z]
    have h_cas_cast_ab : b ^ 2 + 1 = (a + b) * a := by
      rw [h_fib_rec_z] at h_cas_cast_z
      exact h_cas_cast_z
    linear_combination -3 * b * h_cas_cast_ab
  dsimp [b] at h_final_z
  exact_mod_cast h_final_z

theorem prime_dvd_fib_six (n : ℕ) (hn : 1 < n) (h_odd : n % 2 = 1) (p : ℕ) (hp : Nat.Prime p)
    (h_p_dvd : p ∣ H n) : p ∣ Nat.fib (6 * n) := by
  have h_le : 1 ≤ n := by omega
  have h_sum_sq : (Nat.fib (2 * n + 1) + Nat.fib (2 * n - 1)) ^ 2 = 5 * Nat.fib (2 * n) ^ 2 + 4 := by
    obtain ⟨k, hk⟩ : ∃ k, n = 2 * k + 1 := by
      use n / 2
      omega
    have h_id := fib_identity_1_k (2 * k)
    have h_idx1 : 2 * (2 * k) + 3 = 2 * n + 1 := by omega
    have h_idx2 : 2 * (2 * k) + 1 = 2 * n - 1 := by omega
    have h_idx3 : 2 * (2 * k) + 2 = 2 * n := by omega
    rw [h_idx1, h_idx2, h_idx3] at h_id
    exact h_id
  have h_H_eq : Nat.fib (2 * n + 1) + Nat.fib (2 * n - 1) = H n + 1 := by
    have h_fib := H_eq_fib n h_le
    have h_pos : Nat.fib (2 * n + 1) ≥ 2 := by
      have : 2 * n + 1 ≥ 3 := by omega
      have h_fib_mono := Nat.fib_mono this
      exact h_fib_mono
    omega
  have h_sq : (H n + 1) ^ 2 = 5 * Nat.fib (2 * n) ^ 2 + 4 := by
    rw [← h_H_eq, h_sum_sq]
  have h_alg_sq : (H n + 1) ^ 2 = H n * (H n + 2) + 1 := by ring
  rw [h_alg_sq] at h_sq
  have h_div_eq2 : H n * (H n + 2) = 5 * Nat.fib (2 * n) ^ 2 + 3 := by
    have h_add : H n * (H n + 2) + 1 = 5 * Nat.fib (2 * n) ^ 2 + 3 + 1 := by
      omega
    exact Nat.add_right_cancel h_add
  have h_p_dvd_rhs : p ∣ 5 * Nat.fib (2 * n) ^ 2 + 3 := by
    rw [← h_div_eq2]
    exact dvd_mul_of_dvd_left h_p_dvd (H n + 2)
  have h_fib6 := fib_identity_2 n h_le
  rw [h_fib6]
  exact dvd_mul_of_dvd_right h_p_dvd_rhs _


theorem H_ge_two (n : ℕ) (hn : 1 ≤ n) : H n ≥ 2 := by
  rw [H_eq_fib n hn]
  have h1 : Nat.fib (2 * n + 1) ≥ 2 := by
    have h_idx : 2 * n + 1 ≥ 3 := by omega
    have h_fib := Nat.fib_mono h_idx
    exact h_fib
  have h2 : Nat.fib (2 * n - 1) ≥ 1 := by
    have h_idx : 2 * n - 1 ≥ 1 := by omega
    have h_fib := Nat.fib_mono h_idx
    exact h_fib
  omega

theorem H_mono_step (x : ℕ) (hx : 1 ≤ x) : H (x + 1) ≥ H x := by
  rw [H_eq_fib (x + 1) (by omega), H_eq_fib x hx]
  have h1 : Nat.fib (2 * (x + 1) + 1) ≥ Nat.fib (2 * x + 1) := by
    apply Nat.fib_mono
    omega
  have h2 : Nat.fib (2 * (x + 1) - 1) ≥ Nat.fib (2 * x - 1) := by
    apply Nat.fib_mono
    omega
  omega

theorem H_mod_13_step (a b c va vb vc : ℕ)
    (h_rec : c + a = 3 * b + 1)
    (h_le : a ≤ 3 * b + 1)
    (ha : a % 13 = va)
    (hb : b % 13 = vb)
    (h_goal : (3 * vb + 13 + 1 - va) % 13 = vc) :
    c % 13 = vc := by
  omega

theorem H_mod_17_step (a b c va vb vc : ℕ)
    (h_rec : c + a = 3 * b + 1)
    (h_le : a ≤ 3 * b + 1)
    (ha : a % 17 = va)
    (hb : b % 17 = vb)
    (h_goal : (3 * vb + 17 + 1 - va) % 17 = vc) :
    c % 17 = vc := by
  omega


def H_mod_13_prop (k : ℕ) : Prop :=
  H (14 * k + 1) % 13 = 2 ∧
  H (14 * k + 2) % 13 = 6 ∧
  H (14 * k + 3) % 13 = 4 ∧
  H (14 * k + 4) % 13 = 7 ∧
  H (14 * k + 5) % 13 = 5 ∧
  H (14 * k + 6) % 13 = 9 ∧
  H (14 * k + 7) % 13 = 10 ∧
  H (14 * k + 8) % 13 = 9 ∧
  H (14 * k + 9) % 13 = 5 ∧
  H (14 * k + 10) % 13 = 7 ∧
  H (14 * k + 11) % 13 = 4 ∧
  H (14 * k + 12) % 13 = 6 ∧
  H (14 * k + 13) % 13 = 2 ∧
  H (14 * k + 14) % 13 = 1

theorem H_mod_13_prop_zero : H_mod_13_prop 0 := by
  unfold H_mod_13_prop
  decide


theorem H_mod_13_proj1 (k : ℕ) (ih : H_mod_13_prop k) : H (14 * k + 1) % 13 = 2 := by rcases ih with ⟨h, _⟩; exact h
theorem H_mod_13_proj2 (k : ℕ) (ih : H_mod_13_prop k) : H (14 * k + 2) % 13 = 6 := by rcases ih with ⟨_, h, _⟩; exact h
theorem H_mod_13_proj3 (k : ℕ) (ih : H_mod_13_prop k) : H (14 * k + 3) % 13 = 4 := by rcases ih with ⟨_, _, h, _⟩; exact h
theorem H_mod_13_proj4 (k : ℕ) (ih : H_mod_13_prop k) : H (14 * k + 4) % 13 = 7 := by rcases ih with ⟨_, _, _, h, _⟩; exact h
theorem H_mod_13_proj5 (k : ℕ) (ih : H_mod_13_prop k) : H (14 * k + 5) % 13 = 5 := by rcases ih with ⟨_, _, _, _, h, _⟩; exact h
theorem H_mod_13_proj6 (k : ℕ) (ih : H_mod_13_prop k) : H (14 * k + 6) % 13 = 9 := by rcases ih with ⟨_, _, _, _, _, h, _⟩; exact h
theorem H_mod_13_proj7 (k : ℕ) (ih : H_mod_13_prop k) : H (14 * k + 7) % 13 = 10 := by rcases ih with ⟨_, _, _, _, _, _, h, _⟩; exact h
theorem H_mod_13_proj8 (k : ℕ) (ih : H_mod_13_prop k) : H (14 * k + 8) % 13 = 9 := by rcases ih with ⟨_, _, _, _, _, _, _, h, _⟩; exact h
theorem H_mod_13_proj9 (k : ℕ) (ih : H_mod_13_prop k) : H (14 * k + 9) % 13 = 5 := by rcases ih with ⟨_, _, _, _, _, _, _, _, h, _⟩; exact h
theorem H_mod_13_proj10 (k : ℕ) (ih : H_mod_13_prop k) : H (14 * k + 10) % 13 = 7 := by rcases ih with ⟨_, _, _, _, _, _, _, _, _, h, _⟩; exact h
theorem H_mod_13_proj11 (k : ℕ) (ih : H_mod_13_prop k) : H (14 * k + 11) % 13 = 4 := by rcases ih with ⟨_, _, _, _, _, _, _, _, _, _, h, _⟩; exact h
theorem H_mod_13_proj12 (k : ℕ) (ih : H_mod_13_prop k) : H (14 * k + 12) % 13 = 6 := by rcases ih with ⟨_, _, _, _, _, _, _, _, _, _, _, h, _⟩; exact h
theorem H_mod_13_proj13 (k : ℕ) (ih : H_mod_13_prop k) : H (14 * k + 13) % 13 = 2 := by rcases ih with ⟨_, _, _, _, _, _, _, _, _, _, _, _, h, _⟩; exact h
theorem H_mod_13_proj14 (k : ℕ) (ih : H_mod_13_prop k) : H (14 * k + 14) % 13 = 1 := by rcases ih with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h⟩; exact h

theorem H_mod_13_step_1 (k : ℕ) (ha : H (14 * k + 13) % 13 = 2) (hb : H (14 * k + 14) % 13 = 1) : H (14 * k + 15) % 13 = 2 := by
  have r : H (14 * k + 15) + H (14 * k + 13) = 3 * H (14 * k + 14) + 1 := by
    have := H_recurrence (14 * k + 13) (by omega)
    omega
  have m : H (14 * k + 13) ≤ 3 * H (14 * k + 14) + 1 := by omega
  exact H_mod_13_step (H (14 * k + 13)) (H (14 * k + 14)) (H (14 * k + 15)) 2 1 2 r m ha hb (by decide)

theorem H_mod_13_step_2 (k : ℕ) (ha : H (14 * k + 14) % 13 = 1) (hb : H (14 * k + 15) % 13 = 2) : H (14 * k + 16) % 13 = 6 := by
  have r : H (14 * k + 16) + H (14 * k + 14) = 3 * H (14 * k + 15) + 1 := by
    have := H_recurrence (14 * k + 14) (by omega)
    omega
  have m : H (14 * k + 14) ≤ 3 * H (14 * k + 15) + 1 := by omega
  exact H_mod_13_step (H (14 * k + 14)) (H (14 * k + 15)) (H (14 * k + 16)) 1 2 6 r m ha hb (by decide)

theorem H_mod_13_step_3 (k : ℕ) (ha : H (14 * k + 15) % 13 = 2) (hb : H (14 * k + 16) % 13 = 6) : H (14 * k + 17) % 13 = 4 := by
  have r : H (14 * k + 17) + H (14 * k + 15) = 3 * H (14 * k + 16) + 1 := by
    have := H_recurrence (14 * k + 15) (by omega)
    omega
  have m : H (14 * k + 15) ≤ 3 * H (14 * k + 16) + 1 := by omega
  exact H_mod_13_step (H (14 * k + 15)) (H (14 * k + 16)) (H (14 * k + 17)) 2 6 4 r m ha hb (by decide)

theorem H_mod_13_step_4 (k : ℕ) (ha : H (14 * k + 16) % 13 = 6) (hb : H (14 * k + 17) % 13 = 4) : H (14 * k + 18) % 13 = 7 := by
  have r : H (14 * k + 18) + H (14 * k + 16) = 3 * H (14 * k + 17) + 1 := by
    have := H_recurrence (14 * k + 16) (by omega)
    omega
  have m : H (14 * k + 16) ≤ 3 * H (14 * k + 17) + 1 := by omega
  exact H_mod_13_step (H (14 * k + 16)) (H (14 * k + 17)) (H (14 * k + 18)) 6 4 7 r m ha hb (by decide)

theorem H_mod_13_step_5 (k : ℕ) (ha : H (14 * k + 17) % 13 = 4) (hb : H (14 * k + 18) % 13 = 7) : H (14 * k + 19) % 13 = 5 := by
  have r : H (14 * k + 19) + H (14 * k + 17) = 3 * H (14 * k + 18) + 1 := by
    have := H_recurrence (14 * k + 17) (by omega)
    omega
  have m : H (14 * k + 17) ≤ 3 * H (14 * k + 18) + 1 := by omega
  exact H_mod_13_step (H (14 * k + 17)) (H (14 * k + 18)) (H (14 * k + 19)) 4 7 5 r m ha hb (by decide)

theorem H_mod_13_step_6 (k : ℕ) (ha : H (14 * k + 18) % 13 = 7) (hb : H (14 * k + 19) % 13 = 5) : H (14 * k + 20) % 13 = 9 := by
  have r : H (14 * k + 20) + H (14 * k + 18) = 3 * H (14 * k + 19) + 1 := by
    have := H_recurrence (14 * k + 18) (by omega)
    omega
  have m : H (14 * k + 18) ≤ 3 * H (14 * k + 19) + 1 := by omega
  exact H_mod_13_step (H (14 * k + 18)) (H (14 * k + 19)) (H (14 * k + 20)) 7 5 9 r m ha hb (by decide)

theorem H_mod_13_step_7 (k : ℕ) (ha : H (14 * k + 19) % 13 = 5) (hb : H (14 * k + 20) % 13 = 9) : H (14 * k + 21) % 13 = 10 := by
  have r : H (14 * k + 21) + H (14 * k + 19) = 3 * H (14 * k + 20) + 1 := by
    have := H_recurrence (14 * k + 19) (by omega)
    omega
  have m : H (14 * k + 19) ≤ 3 * H (14 * k + 20) + 1 := by omega
  exact H_mod_13_step (H (14 * k + 19)) (H (14 * k + 20)) (H (14 * k + 21)) 5 9 10 r m ha hb (by decide)

theorem H_mod_13_step_8 (k : ℕ) (ha : H (14 * k + 20) % 13 = 9) (hb : H (14 * k + 21) % 13 = 10) : H (14 * k + 22) % 13 = 9 := by
  have r : H (14 * k + 22) + H (14 * k + 20) = 3 * H (14 * k + 21) + 1 := by
    have := H_recurrence (14 * k + 20) (by omega)
    omega
  have m : H (14 * k + 20) ≤ 3 * H (14 * k + 21) + 1 := by omega
  exact H_mod_13_step (H (14 * k + 20)) (H (14 * k + 21)) (H (14 * k + 22)) 9 10 9 r m ha hb (by decide)

theorem H_mod_13_step_9 (k : ℕ) (ha : H (14 * k + 21) % 13 = 10) (hb : H (14 * k + 22) % 13 = 9) : H (14 * k + 23) % 13 = 5 := by
  have r : H (14 * k + 23) + H (14 * k + 21) = 3 * H (14 * k + 22) + 1 := by
    have := H_recurrence (14 * k + 21) (by omega)
    omega
  have m : H (14 * k + 21) ≤ 3 * H (14 * k + 22) + 1 := by omega
  exact H_mod_13_step (H (14 * k + 21)) (H (14 * k + 22)) (H (14 * k + 23)) 10 9 5 r m ha hb (by decide)

theorem H_mod_13_step_10 (k : ℕ) (ha : H (14 * k + 22) % 13 = 9) (hb : H (14 * k + 23) % 13 = 5) : H (14 * k + 24) % 13 = 7 := by
  have r : H (14 * k + 24) + H (14 * k + 22) = 3 * H (14 * k + 23) + 1 := by
    have := H_recurrence (14 * k + 22) (by omega)
    omega
  have m : H (14 * k + 22) ≤ 3 * H (14 * k + 23) + 1 := by omega
  exact H_mod_13_step (H (14 * k + 22)) (H (14 * k + 23)) (H (14 * k + 24)) 9 5 7 r m ha hb (by decide)

theorem H_mod_13_step_11 (k : ℕ) (ha : H (14 * k + 23) % 13 = 5) (hb : H (14 * k + 24) % 13 = 7) : H (14 * k + 25) % 13 = 4 := by
  have r : H (14 * k + 25) + H (14 * k + 23) = 3 * H (14 * k + 24) + 1 := by
    have := H_recurrence (14 * k + 23) (by omega)
    omega
  have m : H (14 * k + 23) ≤ 3 * H (14 * k + 24) + 1 := by omega
  exact H_mod_13_step (H (14 * k + 23)) (H (14 * k + 24)) (H (14 * k + 25)) 5 7 4 r m ha hb (by decide)

theorem H_mod_13_step_12 (k : ℕ) (ha : H (14 * k + 24) % 13 = 7) (hb : H (14 * k + 25) % 13 = 4) : H (14 * k + 26) % 13 = 6 := by
  have r : H (14 * k + 26) + H (14 * k + 24) = 3 * H (14 * k + 25) + 1 := by
    have := H_recurrence (14 * k + 24) (by omega)
    omega
  have m : H (14 * k + 24) ≤ 3 * H (14 * k + 25) + 1 := by omega
  exact H_mod_13_step (H (14 * k + 24)) (H (14 * k + 25)) (H (14 * k + 26)) 7 4 6 r m ha hb (by decide)

theorem H_mod_13_step_13 (k : ℕ) (ha : H (14 * k + 25) % 13 = 4) (hb : H (14 * k + 26) % 13 = 6) : H (14 * k + 27) % 13 = 2 := by
  have r : H (14 * k + 27) + H (14 * k + 25) = 3 * H (14 * k + 26) + 1 := by
    have := H_recurrence (14 * k + 25) (by omega)
    omega
  have m : H (14 * k + 25) ≤ 3 * H (14 * k + 26) + 1 := by omega
  exact H_mod_13_step (H (14 * k + 25)) (H (14 * k + 26)) (H (14 * k + 27)) 4 6 2 r m ha hb (by decide)

theorem H_mod_13_step_14 (k : ℕ) (ha : H (14 * k + 26) % 13 = 6) (hb : H (14 * k + 27) % 13 = 2) : H (14 * k + 28) % 13 = 1 := by
  have r : H (14 * k + 28) + H (14 * k + 26) = 3 * H (14 * k + 27) + 1 := by
    have := H_recurrence (14 * k + 26) (by omega)
    omega
  have m : H (14 * k + 26) ≤ 3 * H (14 * k + 27) + 1 := by omega
  exact H_mod_13_step (H (14 * k + 26)) (H (14 * k + 27)) (H (14 * k + 28)) 6 2 1 r m ha hb (by decide)

theorem H_mod_13_prop_succ (k : ℕ) (ih : H_mod_13_prop k) : H_mod_13_prop (k + 1) := by
  have ih13 := H_mod_13_proj13 k ih
  have ih14 := H_mod_13_proj14 k ih
  have s1 := H_mod_13_step_1 k ih13 ih14
  have s2 := H_mod_13_step_2 k ih14 s1
  have s3 := H_mod_13_step_3 k s1 s2
  have s4 := H_mod_13_step_4 k s2 s3
  have s5 := H_mod_13_step_5 k s3 s4
  have s6 := H_mod_13_step_6 k s4 s5
  have s7 := H_mod_13_step_7 k s5 s6
  have s8 := H_mod_13_step_8 k s6 s7
  have s9 := H_mod_13_step_9 k s7 s8
  have s10 := H_mod_13_step_10 k s8 s9
  have s11 := H_mod_13_step_11 k s9 s10
  have s12 := H_mod_13_step_12 k s10 s11
  have s13 := H_mod_13_step_13 k s11 s12
  have s14 := H_mod_13_step_14 k s12 s13
  have h_idx1 : 14 * (k + 1) + 1 = 14 * k + 15 := by omega
  have h_idx2 : 14 * (k + 1) + 2 = 14 * k + 16 := by omega
  have h_idx3 : 14 * (k + 1) + 3 = 14 * k + 17 := by omega
  have h_idx4 : 14 * (k + 1) + 4 = 14 * k + 18 := by omega
  have h_idx5 : 14 * (k + 1) + 5 = 14 * k + 19 := by omega
  have h_idx6 : 14 * (k + 1) + 6 = 14 * k + 20 := by omega
  have h_idx7 : 14 * (k + 1) + 7 = 14 * k + 21 := by omega
  have h_idx8 : 14 * (k + 1) + 8 = 14 * k + 22 := by omega
  have h_idx9 : 14 * (k + 1) + 9 = 14 * k + 23 := by omega
  have h_idx10 : 14 * (k + 1) + 10 = 14 * k + 24 := by omega
  have h_idx11 : 14 * (k + 1) + 11 = 14 * k + 25 := by omega
  have h_idx12 : 14 * (k + 1) + 12 = 14 * k + 26 := by omega
  have h_idx13 : 14 * (k + 1) + 13 = 14 * k + 27 := by omega
  have h_idx14 : 14 * (k + 1) + 14 = 14 * k + 28 := by omega
  show H (14 * (k + 1) + 1) % 13 = 2 ∧
    H (14 * (k + 1) + 2) % 13 = 6 ∧
    H (14 * (k + 1) + 3) % 13 = 4 ∧
    H (14 * (k + 1) + 4) % 13 = 7 ∧
    H (14 * (k + 1) + 5) % 13 = 5 ∧
    H (14 * (k + 1) + 6) % 13 = 9 ∧
    H (14 * (k + 1) + 7) % 13 = 10 ∧
    H (14 * (k + 1) + 8) % 13 = 9 ∧
    H (14 * (k + 1) + 9) % 13 = 5 ∧
    H (14 * (k + 1) + 10) % 13 = 7 ∧
    H (14 * (k + 1) + 11) % 13 = 4 ∧
    H (14 * (k + 1) + 12) % 13 = 6 ∧
    H (14 * (k + 1) + 13) % 13 = 2 ∧
    H (14 * (k + 1) + 14) % 13 = 1
  rw [h_idx1, h_idx2, h_idx3, h_idx4, h_idx5, h_idx6, h_idx7, h_idx8, h_idx9, h_idx10, h_idx11, h_idx12, h_idx13, h_idx14]
  exact ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14⟩


theorem H_mod_13_ne_zero (n : ℕ) (hn : 1 ≤ n) : H n % 13 ≠ 0 := by
  have h_prop : H_mod_13_prop ((n - 1) / 14) := by
    induction ((n - 1) / 14) with
    | zero => exact H_mod_13_prop_zero
    | succ k ih => exact H_mod_13_prop_succ k ih
  have h_mod : (n - 1) % 14 < 14 := Nat.mod_lt _ (by decide)
  rcases h_case : (n - 1) % 14 with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
  · have h_eq2 : n = 14 * ((n - 1) / 14) + 1 := by omega
    rw [h_eq2]
    have : H (14 * ((n - 1) / 14) + 1) % 13 = 2 := H_mod_13_proj1 ((n - 1) / 14) h_prop
    omega
  · have h_eq2 : n = 14 * ((n - 1) / 14) + 2 := by omega
    rw [h_eq2]
    have : H (14 * ((n - 1) / 14) + 2) % 13 = 6 := H_mod_13_proj2 ((n - 1) / 14) h_prop
    omega
  · have h_eq2 : n = 14 * ((n - 1) / 14) + 3 := by omega
    rw [h_eq2]
    have : H (14 * ((n - 1) / 14) + 3) % 13 = 4 := H_mod_13_proj3 ((n - 1) / 14) h_prop
    omega
  · have h_eq2 : n = 14 * ((n - 1) / 14) + 4 := by omega
    rw [h_eq2]
    have : H (14 * ((n - 1) / 14) + 4) % 13 = 7 := H_mod_13_proj4 ((n - 1) / 14) h_prop
    omega
  · have h_eq2 : n = 14 * ((n - 1) / 14) + 5 := by omega
    rw [h_eq2]
    have : H (14 * ((n - 1) / 14) + 5) % 13 = 5 := H_mod_13_proj5 ((n - 1) / 14) h_prop
    omega
  · have h_eq2 : n = 14 * ((n - 1) / 14) + 6 := by omega
    rw [h_eq2]
    have : H (14 * ((n - 1) / 14) + 6) % 13 = 9 := H_mod_13_proj6 ((n - 1) / 14) h_prop
    omega
  · have h_eq2 : n = 14 * ((n - 1) / 14) + 7 := by omega
    rw [h_eq2]
    have : H (14 * ((n - 1) / 14) + 7) % 13 = 10 := H_mod_13_proj7 ((n - 1) / 14) h_prop
    omega
  · have h_eq2 : n = 14 * ((n - 1) / 14) + 8 := by omega
    rw [h_eq2]
    have : H (14 * ((n - 1) / 14) + 8) % 13 = 9 := H_mod_13_proj8 ((n - 1) / 14) h_prop
    omega
  · have h_eq2 : n = 14 * ((n - 1) / 14) + 9 := by omega
    rw [h_eq2]
    have : H (14 * ((n - 1) / 14) + 9) % 13 = 5 := H_mod_13_proj9 ((n - 1) / 14) h_prop
    omega
  · have h_eq2 : n = 14 * ((n - 1) / 14) + 10 := by omega
    rw [h_eq2]
    have : H (14 * ((n - 1) / 14) + 10) % 13 = 7 := H_mod_13_proj10 ((n - 1) / 14) h_prop
    omega
  · have h_eq2 : n = 14 * ((n - 1) / 14) + 11 := by omega
    rw [h_eq2]
    have : H (14 * ((n - 1) / 14) + 11) % 13 = 4 := H_mod_13_proj11 ((n - 1) / 14) h_prop
    omega
  · have h_eq2 : n = 14 * ((n - 1) / 14) + 12 := by omega
    rw [h_eq2]
    have : H (14 * ((n - 1) / 14) + 12) % 13 = 6 := H_mod_13_proj12 ((n - 1) / 14) h_prop
    omega
  · have h_eq2 : n = 14 * ((n - 1) / 14) + 13 := by omega
    rw [h_eq2]
    have : H (14 * ((n - 1) / 14) + 13) % 13 = 2 := H_mod_13_proj13 ((n - 1) / 14) h_prop
    omega
  · have h_eq2 : n = 14 * ((n - 1) / 14) + 14 := by omega
    rw [h_eq2]
    have : H (14 * ((n - 1) / 14) + 14) % 13 = 1 := H_mod_13_proj14 ((n - 1) / 14) h_prop
    omega



def H_mod_17_prop (k : ℕ) : Prop :=
  H (18 * k + 1) % 17 = 2 ∧
  H (18 * k + 2) % 17 = 6 ∧
  H (18 * k + 3) % 17 = 0 ∧
  H (18 * k + 4) % 17 = 12 ∧
  H (18 * k + 5) % 17 = 3 ∧
  H (18 * k + 6) % 17 = 15 ∧
  H (18 * k + 7) % 17 = 9 ∧
  H (18 * k + 8) % 17 = 13 ∧
  H (18 * k + 9) % 17 = 14 ∧
  H (18 * k + 10) % 17 = 13 ∧
  H (18 * k + 11) % 17 = 9 ∧
  H (18 * k + 12) % 17 = 15 ∧
  H (18 * k + 13) % 17 = 3 ∧
  H (18 * k + 14) % 17 = 12 ∧
  H (18 * k + 15) % 17 = 0 ∧
  H (18 * k + 16) % 17 = 6 ∧
  H (18 * k + 17) % 17 = 2 ∧
  H (18 * k + 18) % 17 = 1

theorem H_mod_17_prop_zero : H_mod_17_prop 0 := by
  unfold H_mod_17_prop
  decide


theorem H_mod_17_proj1 (k : ℕ) (ih : H_mod_17_prop k) : H (18 * k + 1) % 17 = 2 := by rcases ih with ⟨h, _⟩; exact h
theorem H_mod_17_proj2 (k : ℕ) (ih : H_mod_17_prop k) : H (18 * k + 2) % 17 = 6 := by rcases ih with ⟨_, h, _⟩; exact h
theorem H_mod_17_proj3 (k : ℕ) (ih : H_mod_17_prop k) : H (18 * k + 3) % 17 = 0 := by rcases ih with ⟨_, _, h, _⟩; exact h
theorem H_mod_17_proj4 (k : ℕ) (ih : H_mod_17_prop k) : H (18 * k + 4) % 17 = 12 := by rcases ih with ⟨_, _, _, h, _⟩; exact h
theorem H_mod_17_proj5 (k : ℕ) (ih : H_mod_17_prop k) : H (18 * k + 5) % 17 = 3 := by rcases ih with ⟨_, _, _, _, h, _⟩; exact h
theorem H_mod_17_proj6 (k : ℕ) (ih : H_mod_17_prop k) : H (18 * k + 6) % 17 = 15 := by rcases ih with ⟨_, _, _, _, _, h, _⟩; exact h
theorem H_mod_17_proj7 (k : ℕ) (ih : H_mod_17_prop k) : H (18 * k + 7) % 17 = 9 := by rcases ih with ⟨_, _, _, _, _, _, h, _⟩; exact h
theorem H_mod_17_proj8 (k : ℕ) (ih : H_mod_17_prop k) : H (18 * k + 8) % 17 = 13 := by rcases ih with ⟨_, _, _, _, _, _, _, h, _⟩; exact h
theorem H_mod_17_proj9 (k : ℕ) (ih : H_mod_17_prop k) : H (18 * k + 9) % 17 = 14 := by rcases ih with ⟨_, _, _, _, _, _, _, _, h, _⟩; exact h
theorem H_mod_17_proj10 (k : ℕ) (ih : H_mod_17_prop k) : H (18 * k + 10) % 17 = 13 := by rcases ih with ⟨_, _, _, _, _, _, _, _, _, h, _⟩; exact h
theorem H_mod_17_proj11 (k : ℕ) (ih : H_mod_17_prop k) : H (18 * k + 11) % 17 = 9 := by rcases ih with ⟨_, _, _, _, _, _, _, _, _, _, h, _⟩; exact h
theorem H_mod_17_proj12 (k : ℕ) (ih : H_mod_17_prop k) : H (18 * k + 12) % 17 = 15 := by rcases ih with ⟨_, _, _, _, _, _, _, _, _, _, _, h, _⟩; exact h
theorem H_mod_17_proj13 (k : ℕ) (ih : H_mod_17_prop k) : H (18 * k + 13) % 17 = 3 := by rcases ih with ⟨_, _, _, _, _, _, _, _, _, _, _, _, h, _⟩; exact h
theorem H_mod_17_proj14 (k : ℕ) (ih : H_mod_17_prop k) : H (18 * k + 14) % 17 = 12 := by rcases ih with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h, _⟩; exact h
theorem H_mod_17_proj15 (k : ℕ) (ih : H_mod_17_prop k) : H (18 * k + 15) % 17 = 0 := by rcases ih with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _⟩; exact h
theorem H_mod_17_proj16 (k : ℕ) (ih : H_mod_17_prop k) : H (18 * k + 16) % 17 = 6 := by rcases ih with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _⟩; exact h
theorem H_mod_17_proj17 (k : ℕ) (ih : H_mod_17_prop k) : H (18 * k + 17) % 17 = 2 := by rcases ih with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _⟩; exact h
theorem H_mod_17_proj18 (k : ℕ) (ih : H_mod_17_prop k) : H (18 * k + 18) % 17 = 1 := by rcases ih with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h⟩; exact h

theorem H_mod_17_step_1 (k : ℕ) (ha : H (18 * k + 17) % 17 = 2) (hb : H (18 * k + 18) % 17 = 1) : H (18 * k + 19) % 17 = 2 := by
  have r : H (18 * k + 19) + H (18 * k + 17) = 3 * H (18 * k + 18) + 1 := by
    have := H_recurrence (18 * k + 17) (by omega)
    omega
  have m : H (18 * k + 17) ≤ 3 * H (18 * k + 18) + 1 := by omega
  exact H_mod_17_step (H (18 * k + 17)) (H (18 * k + 18)) (H (18 * k + 19)) 2 1 2 r m ha hb (by decide)

theorem H_mod_17_step_2 (k : ℕ) (ha : H (18 * k + 18) % 17 = 1) (hb : H (18 * k + 19) % 17 = 2) : H (18 * k + 20) % 17 = 6 := by
  have r : H (18 * k + 20) + H (18 * k + 18) = 3 * H (18 * k + 19) + 1 := by
    have := H_recurrence (18 * k + 18) (by omega)
    omega
  have m : H (18 * k + 18) ≤ 3 * H (18 * k + 19) + 1 := by omega
  exact H_mod_17_step (H (18 * k + 18)) (H (18 * k + 19)) (H (18 * k + 20)) 1 2 6 r m ha hb (by decide)

theorem H_mod_17_step_3 (k : ℕ) (ha : H (18 * k + 19) % 17 = 2) (hb : H (18 * k + 20) % 17 = 6) : H (18 * k + 21) % 17 = 0 := by
  have r : H (18 * k + 21) + H (18 * k + 19) = 3 * H (18 * k + 20) + 1 := by
    have := H_recurrence (18 * k + 19) (by omega)
    omega
  have m : H (18 * k + 19) ≤ 3 * H (18 * k + 20) + 1 := by omega
  exact H_mod_17_step (H (18 * k + 19)) (H (18 * k + 20)) (H (18 * k + 21)) 2 6 0 r m ha hb (by decide)

theorem H_mod_17_step_4 (k : ℕ) (ha : H (18 * k + 20) % 17 = 6) (hb : H (18 * k + 21) % 17 = 0) : H (18 * k + 22) % 17 = 12 := by
  have r : H (18 * k + 22) + H (18 * k + 20) = 3 * H (18 * k + 21) + 1 := by
    have := H_recurrence (18 * k + 20) (by omega)
    omega
  have m : H (18 * k + 20) ≤ 3 * H (18 * k + 21) + 1 := by omega
  exact H_mod_17_step (H (18 * k + 20)) (H (18 * k + 21)) (H (18 * k + 22)) 6 0 12 r m ha hb (by decide)

theorem H_mod_17_step_5 (k : ℕ) (ha : H (18 * k + 21) % 17 = 0) (hb : H (18 * k + 22) % 17 = 12) : H (18 * k + 23) % 17 = 3 := by
  have r : H (18 * k + 23) + H (18 * k + 21) = 3 * H (18 * k + 22) + 1 := by
    have := H_recurrence (18 * k + 21) (by omega)
    omega
  have m : H (18 * k + 21) ≤ 3 * H (18 * k + 22) + 1 := by omega
  exact H_mod_17_step (H (18 * k + 21)) (H (18 * k + 22)) (H (18 * k + 23)) 0 12 3 r m ha hb (by decide)

theorem H_mod_17_step_6 (k : ℕ) (ha : H (18 * k + 22) % 17 = 12) (hb : H (18 * k + 23) % 17 = 3) : H (18 * k + 24) % 17 = 15 := by
  have r : H (18 * k + 24) + H (18 * k + 22) = 3 * H (18 * k + 23) + 1 := by
    have := H_recurrence (18 * k + 22) (by omega)
    omega
  have m : H (18 * k + 22) ≤ 3 * H (18 * k + 23) + 1 := by omega
  exact H_mod_17_step (H (18 * k + 22)) (H (18 * k + 23)) (H (18 * k + 24)) 12 3 15 r m ha hb (by decide)

theorem H_mod_17_step_7 (k : ℕ) (ha : H (18 * k + 23) % 17 = 3) (hb : H (18 * k + 24) % 17 = 15) : H (18 * k + 25) % 17 = 9 := by
  have r : H (18 * k + 25) + H (18 * k + 23) = 3 * H (18 * k + 24) + 1 := by
    have := H_recurrence (18 * k + 23) (by omega)
    omega
  have m : H (18 * k + 23) ≤ 3 * H (18 * k + 24) + 1 := by omega
  exact H_mod_17_step (H (18 * k + 23)) (H (18 * k + 24)) (H (18 * k + 25)) 3 15 9 r m ha hb (by decide)

theorem H_mod_17_step_8 (k : ℕ) (ha : H (18 * k + 24) % 17 = 15) (hb : H (18 * k + 25) % 17 = 9) : H (18 * k + 26) % 17 = 13 := by
  have r : H (18 * k + 26) + H (18 * k + 24) = 3 * H (18 * k + 25) + 1 := by
    have := H_recurrence (18 * k + 24) (by omega)
    omega
  have m : H (18 * k + 24) ≤ 3 * H (18 * k + 25) + 1 := by omega
  exact H_mod_17_step (H (18 * k + 24)) (H (18 * k + 25)) (H (18 * k + 26)) 15 9 13 r m ha hb (by decide)

theorem H_mod_17_step_9 (k : ℕ) (ha : H (18 * k + 25) % 17 = 9) (hb : H (18 * k + 26) % 17 = 13) : H (18 * k + 27) % 17 = 14 := by
  have r : H (18 * k + 27) + H (18 * k + 25) = 3 * H (18 * k + 26) + 1 := by
    have := H_recurrence (18 * k + 25) (by omega)
    omega
  have m : H (18 * k + 25) ≤ 3 * H (18 * k + 26) + 1 := by omega
  exact H_mod_17_step (H (18 * k + 25)) (H (18 * k + 26)) (H (18 * k + 27)) 9 13 14 r m ha hb (by decide)

theorem H_mod_17_step_10 (k : ℕ) (ha : H (18 * k + 26) % 17 = 13) (hb : H (18 * k + 27) % 17 = 14) : H (18 * k + 28) % 17 = 13 := by
  have r : H (18 * k + 28) + H (18 * k + 26) = 3 * H (18 * k + 27) + 1 := by
    have := H_recurrence (18 * k + 26) (by omega)
    omega
  have m : H (18 * k + 26) ≤ 3 * H (18 * k + 27) + 1 := by omega
  exact H_mod_17_step (H (18 * k + 26)) (H (18 * k + 27)) (H (18 * k + 28)) 13 14 13 r m ha hb (by decide)

theorem H_mod_17_step_11 (k : ℕ) (ha : H (18 * k + 27) % 17 = 14) (hb : H (18 * k + 28) % 17 = 13) : H (18 * k + 29) % 17 = 9 := by
  have r : H (18 * k + 29) + H (18 * k + 27) = 3 * H (18 * k + 28) + 1 := by
    have := H_recurrence (18 * k + 27) (by omega)
    omega
  have m : H (18 * k + 27) ≤ 3 * H (18 * k + 28) + 1 := by omega
  exact H_mod_17_step (H (18 * k + 27)) (H (18 * k + 28)) (H (18 * k + 29)) 14 13 9 r m ha hb (by decide)

theorem H_mod_17_step_12 (k : ℕ) (ha : H (18 * k + 28) % 17 = 13) (hb : H (18 * k + 29) % 17 = 9) : H (18 * k + 30) % 17 = 15 := by
  have r : H (18 * k + 30) + H (18 * k + 28) = 3 * H (18 * k + 29) + 1 := by
    have := H_recurrence (18 * k + 28) (by omega)
    omega
  have m : H (18 * k + 28) ≤ 3 * H (18 * k + 29) + 1 := by omega
  exact H_mod_17_step (H (18 * k + 28)) (H (18 * k + 29)) (H (18 * k + 30)) 13 9 15 r m ha hb (by decide)

theorem H_mod_17_step_13 (k : ℕ) (ha : H (18 * k + 29) % 17 = 9) (hb : H (18 * k + 30) % 17 = 15) : H (18 * k + 31) % 17 = 3 := by
  have r : H (18 * k + 31) + H (18 * k + 29) = 3 * H (18 * k + 30) + 1 := by
    have := H_recurrence (18 * k + 29) (by omega)
    omega
  have m : H (18 * k + 29) ≤ 3 * H (18 * k + 30) + 1 := by omega
  exact H_mod_17_step (H (18 * k + 29)) (H (18 * k + 30)) (H (18 * k + 31)) 9 15 3 r m ha hb (by decide)

theorem H_mod_17_step_14 (k : ℕ) (ha : H (18 * k + 30) % 17 = 15) (hb : H (18 * k + 31) % 17 = 3) : H (18 * k + 32) % 17 = 12 := by
  have r : H (18 * k + 32) + H (18 * k + 30) = 3 * H (18 * k + 31) + 1 := by
    have := H_recurrence (18 * k + 30) (by omega)
    omega
  have m : H (18 * k + 30) ≤ 3 * H (18 * k + 31) + 1 := by omega
  exact H_mod_17_step (H (18 * k + 30)) (H (18 * k + 31)) (H (18 * k + 32)) 15 3 12 r m ha hb (by decide)

theorem H_mod_17_step_15 (k : ℕ) (ha : H (18 * k + 31) % 17 = 3) (hb : H (18 * k + 32) % 17 = 12) : H (18 * k + 33) % 17 = 0 := by
  have r : H (18 * k + 33) + H (18 * k + 31) = 3 * H (18 * k + 32) + 1 := by
    have := H_recurrence (18 * k + 31) (by omega)
    omega
  have m : H (18 * k + 31) ≤ 3 * H (18 * k + 32) + 1 := by omega
  exact H_mod_17_step (H (18 * k + 31)) (H (18 * k + 32)) (H (18 * k + 33)) 3 12 0 r m ha hb (by decide)

theorem H_mod_17_step_16 (k : ℕ) (ha : H (18 * k + 32) % 17 = 12) (hb : H (18 * k + 33) % 17 = 0) : H (18 * k + 34) % 17 = 6 := by
  have r : H (18 * k + 34) + H (18 * k + 32) = 3 * H (18 * k + 33) + 1 := by
    have := H_recurrence (18 * k + 32) (by omega)
    omega
  have m : H (18 * k + 32) ≤ 3 * H (18 * k + 33) + 1 := by omega
  exact H_mod_17_step (H (18 * k + 32)) (H (18 * k + 33)) (H (18 * k + 34)) 12 0 6 r m ha hb (by decide)

theorem H_mod_17_step_17 (k : ℕ) (ha : H (18 * k + 33) % 17 = 0) (hb : H (18 * k + 34) % 17 = 6) : H (18 * k + 35) % 17 = 2 := by
  have r : H (18 * k + 35) + H (18 * k + 33) = 3 * H (18 * k + 34) + 1 := by
    have := H_recurrence (18 * k + 33) (by omega)
    omega
  have m : H (18 * k + 33) ≤ 3 * H (18 * k + 34) + 1 := by omega
  exact H_mod_17_step (H (18 * k + 33)) (H (18 * k + 34)) (H (18 * k + 35)) 0 6 2 r m ha hb (by decide)

theorem H_mod_17_step_18 (k : ℕ) (ha : H (18 * k + 34) % 17 = 6) (hb : H (18 * k + 35) % 17 = 2) : H (18 * k + 36) % 17 = 1 := by
  have r : H (18 * k + 36) + H (18 * k + 34) = 3 * H (18 * k + 35) + 1 := by
    have := H_recurrence (18 * k + 34) (by omega)
    omega
  have m : H (18 * k + 34) ≤ 3 * H (18 * k + 35) + 1 := by omega
  exact H_mod_17_step (H (18 * k + 34)) (H (18 * k + 35)) (H (18 * k + 36)) 6 2 1 r m ha hb (by decide)

theorem H_mod_17_prop_succ (k : ℕ) (ih : H_mod_17_prop k) : H_mod_17_prop (k + 1) := by
  have ih17 := H_mod_17_proj17 k ih
  have ih18 := H_mod_17_proj18 k ih
  have s1 := H_mod_17_step_1 k ih17 ih18
  have s2 := H_mod_17_step_2 k ih18 s1
  have s3 := H_mod_17_step_3 k s1 s2
  have s4 := H_mod_17_step_4 k s2 s3
  have s5 := H_mod_17_step_5 k s3 s4
  have s6 := H_mod_17_step_6 k s4 s5
  have s7 := H_mod_17_step_7 k s5 s6
  have s8 := H_mod_17_step_8 k s6 s7
  have s9 := H_mod_17_step_9 k s7 s8
  have s10 := H_mod_17_step_10 k s8 s9
  have s11 := H_mod_17_step_11 k s9 s10
  have s12 := H_mod_17_step_12 k s10 s11
  have s13 := H_mod_17_step_13 k s11 s12
  have s14 := H_mod_17_step_14 k s12 s13
  have s15 := H_mod_17_step_15 k s13 s14
  have s16 := H_mod_17_step_16 k s14 s15
  have s17 := H_mod_17_step_17 k s15 s16
  have s18 := H_mod_17_step_18 k s16 s17
  have h_idx1 : 18 * (k + 1) + 1 = 18 * k + 19 := by omega
  have h_idx2 : 18 * (k + 1) + 2 = 18 * k + 20 := by omega
  have h_idx3 : 18 * (k + 1) + 3 = 18 * k + 21 := by omega
  have h_idx4 : 18 * (k + 1) + 4 = 18 * k + 22 := by omega
  have h_idx5 : 18 * (k + 1) + 5 = 18 * k + 23 := by omega
  have h_idx6 : 18 * (k + 1) + 6 = 18 * k + 24 := by omega
  have h_idx7 : 18 * (k + 1) + 7 = 18 * k + 25 := by omega
  have h_idx8 : 18 * (k + 1) + 8 = 18 * k + 26 := by omega
  have h_idx9 : 18 * (k + 1) + 9 = 18 * k + 27 := by omega
  have h_idx10 : 18 * (k + 1) + 10 = 18 * k + 28 := by omega
  have h_idx11 : 18 * (k + 1) + 11 = 18 * k + 29 := by omega
  have h_idx12 : 18 * (k + 1) + 12 = 18 * k + 30 := by omega
  have h_idx13 : 18 * (k + 1) + 13 = 18 * k + 31 := by omega
  have h_idx14 : 18 * (k + 1) + 14 = 18 * k + 32 := by omega
  have h_idx15 : 18 * (k + 1) + 15 = 18 * k + 33 := by omega
  have h_idx16 : 18 * (k + 1) + 16 = 18 * k + 34 := by omega
  have h_idx17 : 18 * (k + 1) + 17 = 18 * k + 35 := by omega
  have h_idx18 : 18 * (k + 1) + 18 = 18 * k + 36 := by omega
  show H (18 * (k + 1) + 1) % 17 = 2 ∧
    H (18 * (k + 1) + 2) % 17 = 6 ∧
    H (18 * (k + 1) + 3) % 17 = 0 ∧
    H (18 * (k + 1) + 4) % 17 = 12 ∧
    H (18 * (k + 1) + 5) % 17 = 3 ∧
    H (18 * (k + 1) + 6) % 17 = 15 ∧
    H (18 * (k + 1) + 7) % 17 = 9 ∧
    H (18 * (k + 1) + 8) % 17 = 13 ∧
    H (18 * (k + 1) + 9) % 17 = 14 ∧
    H (18 * (k + 1) + 10) % 17 = 13 ∧
    H (18 * (k + 1) + 11) % 17 = 9 ∧
    H (18 * (k + 1) + 12) % 17 = 15 ∧
    H (18 * (k + 1) + 13) % 17 = 3 ∧
    H (18 * (k + 1) + 14) % 17 = 12 ∧
    H (18 * (k + 1) + 15) % 17 = 0 ∧
    H (18 * (k + 1) + 16) % 17 = 6 ∧
    H (18 * (k + 1) + 17) % 17 = 2 ∧
    H (18 * (k + 1) + 18) % 17 = 1
  rw [h_idx1, h_idx2, h_idx3, h_idx4, h_idx5, h_idx6, h_idx7, h_idx8, h_idx9, h_idx10, h_idx11, h_idx12, h_idx13, h_idx14, h_idx15, h_idx16, h_idx17, h_idx18]
  exact ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18⟩


theorem H_mod_17_ne_zero_of_not_3_dvd (n : ℕ) (hn : 1 ≤ n) (h3 : ¬ 3 ∣ n) : H n % 17 ≠ 0 := by
  have h_prop : H_mod_17_prop ((n - 1) / 18) := by
    induction ((n - 1) / 18) with
    | zero => exact H_mod_17_prop_zero
    | succ k ih => exact H_mod_17_prop_succ k ih
  have h_mod : (n - 1) % 18 < 18 := Nat.mod_lt _ (by decide)
  rcases h_case : (n - 1) % 18 with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
  · have h_eq2 : n = 18 * ((n - 1) / 18) + 1 := by omega
    rw [h_eq2]
    have : H (18 * ((n - 1) / 18) + 1) % 17 = 2 := H_mod_17_proj1 ((n - 1) / 18) h_prop
    omega
  · have h_eq2 : n = 18 * ((n - 1) / 18) + 2 := by omega
    rw [h_eq2]
    have : H (18 * ((n - 1) / 18) + 2) % 17 = 6 := H_mod_17_proj2 ((n - 1) / 18) h_prop
    omega
  · have h_eq2 : n = 18 * ((n - 1) / 18) + 3 := by omega
    have : 3 ∣ n := by
      rw [h_eq2]
      exact dvd_add (dvd_mul_of_dvd_left (by decide) _) (by decide)
    contradiction
  · have h_eq2 : n = 18 * ((n - 1) / 18) + 4 := by omega
    rw [h_eq2]
    have : H (18 * ((n - 1) / 18) + 4) % 17 = 12 := H_mod_17_proj4 ((n - 1) / 18) h_prop
    omega
  · have h_eq2 : n = 18 * ((n - 1) / 18) + 5 := by omega
    rw [h_eq2]
    have : H (18 * ((n - 1) / 18) + 5) % 17 = 3 := H_mod_17_proj5 ((n - 1) / 18) h_prop
    omega
  · have h_eq2 : n = 18 * ((n - 1) / 18) + 6 := by omega
    rw [h_eq2]
    have : H (18 * ((n - 1) / 18) + 6) % 17 = 15 := H_mod_17_proj6 ((n - 1) / 18) h_prop
    omega
  · have h_eq2 : n = 18 * ((n - 1) / 18) + 7 := by omega
    rw [h_eq2]
    have : H (18 * ((n - 1) / 18) + 7) % 17 = 9 := H_mod_17_proj7 ((n - 1) / 18) h_prop
    omega
  · have h_eq2 : n = 18 * ((n - 1) / 18) + 8 := by omega
    rw [h_eq2]
    have : H (18 * ((n - 1) / 18) + 8) % 17 = 13 := H_mod_17_proj8 ((n - 1) / 18) h_prop
    omega
  · have h_eq2 : n = 18 * ((n - 1) / 18) + 9 := by omega
    rw [h_eq2]
    have : H (18 * ((n - 1) / 18) + 9) % 17 = 14 := H_mod_17_proj9 ((n - 1) / 18) h_prop
    omega
  · have h_eq2 : n = 18 * ((n - 1) / 18) + 10 := by omega
    rw [h_eq2]
    have : H (18 * ((n - 1) / 18) + 10) % 17 = 13 := H_mod_17_proj10 ((n - 1) / 18) h_prop
    omega
  · have h_eq2 : n = 18 * ((n - 1) / 18) + 11 := by omega
    rw [h_eq2]
    have : H (18 * ((n - 1) / 18) + 11) % 17 = 9 := H_mod_17_proj11 ((n - 1) / 18) h_prop
    omega
  · have h_eq2 : n = 18 * ((n - 1) / 18) + 12 := by omega
    rw [h_eq2]
    have : H (18 * ((n - 1) / 18) + 12) % 17 = 15 := H_mod_17_proj12 ((n - 1) / 18) h_prop
    omega
  · have h_eq2 : n = 18 * ((n - 1) / 18) + 13 := by omega
    rw [h_eq2]
    have : H (18 * ((n - 1) / 18) + 13) % 17 = 3 := H_mod_17_proj13 ((n - 1) / 18) h_prop
    omega
  · have h_eq2 : n = 18 * ((n - 1) / 18) + 14 := by omega
    rw [h_eq2]
    have : H (18 * ((n - 1) / 18) + 14) % 17 = 12 := H_mod_17_proj14 ((n - 1) / 18) h_prop
    omega
  · have h_eq2 : n = 18 * ((n - 1) / 18) + 15 := by omega
    have : 3 ∣ n := by
      rw [h_eq2]
      exact dvd_add (dvd_mul_of_dvd_left (by decide) _) (by decide)
    contradiction
  · have h_eq2 : n = 18 * ((n - 1) / 18) + 16 := by omega
    rw [h_eq2]
    have : H (18 * ((n - 1) / 18) + 16) % 17 = 6 := H_mod_17_proj16 ((n - 1) / 18) h_prop
    omega
  · have h_eq2 : n = 18 * ((n - 1) / 18) + 17 := by omega
    rw [h_eq2]
    have : H (18 * ((n - 1) / 18) + 17) % 17 = 2 := H_mod_17_proj17 ((n - 1) / 18) h_prop
    omega
  · have h_eq2 : n = 18 * ((n - 1) / 18) + 18 := by omega
    rw [h_eq2]
    have : H (18 * ((n - 1) / 18) + 18) % 17 = 1 := H_mod_17_proj18 ((n - 1) / 18) h_prop
    omega
theorem fib_dvd_iff (p a m : ℕ) (ha : a > 0) (hp : p ∣ Nat.fib a) (hmin : ∀ k, 0 < k → p ∣ Nat.fib k → a ≤ k) :
    p ∣ Nat.fib m ↔ a ∣ m := by
  constructor
  · intro hm
    have h_gcd_dvd : Nat.gcd a m ∣ a := Nat.gcd_dvd_left a m
    have h_gcd_pos : 0 < Nat.gcd a m := by
      have h_gcd_nz : Nat.gcd a m ≠ 0 := by
        intro hc
        rw [Nat.gcd_eq_zero_iff] at hc
        omega
      omega
    have h_gcd_dvd_fib : p ∣ Nat.fib (Nat.gcd a m) := by
      rw [Nat.fib_gcd]
      exact Nat.dvd_gcd hp hm
    have h_le := hmin (Nat.gcd a m) h_gcd_pos h_gcd_dvd_fib
    have h_gcd_le : Nat.gcd a m ≤ a := Nat.le_of_dvd ha h_gcd_dvd
    have h_eq : Nat.gcd a m = a := by omega
    rw [← h_eq]
    exact Nat.gcd_dvd_right a m
  · intro h
    exact dvd_trans hp (Nat.fib_dvd a m h)

theorem exists_minimal_fib_dvd (p : ℕ) (m : ℕ) (hm : 0 < m) (hp : p ∣ Nat.fib m) :
    ∃ a, 0 < a ∧ p ∣ Nat.fib a ∧ ∀ k, 0 < k → p ∣ Nat.fib k → a ≤ k := by
  have h_ex : ∃ x, 0 < x ∧ p ∣ Nat.fib x := ⟨m, hm, hp⟩
  let P := fun x => 0 < x ∧ p ∣ Nat.fib x
  have h_dec : DecidablePred P := fun x => inferInstance
  use Nat.find h_ex
  have h_prop := Nat.find_spec h_ex
  refine ⟨h_prop.1, h_prop.2, ?_⟩
  intro k hk hpk
  exact Nat.find_min' h_ex ⟨hk, hpk⟩

@[ext]
structure Q5 (p : ℕ) where
  x : ZMod p
  y : ZMod p
  deriving DecidableEq

namespace Q5

variable {p : ℕ} [Fact (Nat.Prime p)]

def add (a b : Q5 p) : Q5 p := ⟨a.x + b.x, a.y + b.y⟩
def neg (a : Q5 p) : Q5 p := ⟨-a.x, -a.y⟩
def sub (a b : Q5 p) : Q5 p := ⟨a.x - b.x, a.y - b.y⟩
def mul (a b : Q5 p) : Q5 p := ⟨a.x * b.x + 5 * a.y * b.y, a.x * b.y + a.y * b.x⟩
def zero : Q5 p := ⟨0, 0⟩
def one : Q5 p := ⟨1, 0⟩

instance : Add (Q5 p) := ⟨add⟩
instance : Neg (Q5 p) := ⟨neg⟩
instance : Sub (Q5 p) := ⟨sub⟩
instance : Mul (Q5 p) := ⟨mul⟩
instance : Zero (Q5 p) := ⟨zero⟩
instance : One (Q5 p) := ⟨one⟩

@[simp] lemma add_x (a b : Q5 p) : (a + b).x = a.x + b.x := rfl
@[simp] lemma add_y (a b : Q5 p) : (a + b).y = a.y + b.y := rfl
@[simp] lemma mul_x (a b : Q5 p) : (a * b).x = a.x * b.x + 5 * a.y * b.y := rfl
@[simp] lemma mul_y (a b : Q5 p) : (a * b).y = a.x * b.y + a.y * b.x := rfl
@[simp] lemma neg_x (a : Q5 p) : (-a).x = -a.x := rfl
@[simp] lemma neg_y (a : Q5 p) : (-a).y = -a.y := rfl
@[simp] lemma sub_x (a b : Q5 p) : (a - b).x = a.x - b.x := rfl
@[simp] lemma sub_y (a b : Q5 p) : (a - b).y = a.y - b.y := rfl
@[simp] lemma zero_x : (0 : Q5 p).x = 0 := rfl
@[simp] lemma zero_y : (0 : Q5 p).y = 0 := rfl
@[simp] lemma one_x : (1 : Q5 p).x = 1 := rfl
@[simp] lemma one_y : (1 : Q5 p).y = 0 := rfl

instance : CommRing (Q5 p) where
  add_assoc a b c := by ext <;> (simp; try ring)
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  add_comm a b := by ext <;> (simp; try ring)
  mul_assoc a b c := by ext <;> (simp; try ring)
  one_mul a := by ext <;> (simp; try ring)
  mul_one a := by ext <;> (simp; try ring)
  left_distrib a b c := by ext <;> (simp; try ring)
  right_distrib a b c := by ext <;> (simp; try ring)
  mul_comm a b := by ext <;> (simp; try ring)
  zero_mul a := by ext <;> simp
  mul_zero a := by ext <;> simp
  neg_add_cancel a := by ext <;> simp
  sub_eq_add_neg a b := by ext <;> (simp; try ring)
  nsmul n a := ⟨(n : ZMod p) * a.x, (n : ZMod p) * a.y⟩
  nsmul_zero a := by ext <;> simp
  nsmul_succ n a := by ext <;> (simp; try ring)
  zsmul n a := ⟨(n : ZMod p) * a.x, (n : ZMod p) * a.y⟩
  zsmul_zero' a := by ext <;> simp
  zsmul_succ' n a := by ext <;> (simp; try ring)
  zsmul_neg' n a := by ext <;> (simp; try ring)

@[simp] lemma natCast_x {p : ℕ} [Fact (Nat.Prime p)] (n : ℕ) : (n : Q5 p).x = (n : ZMod p) := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih]

@[simp] lemma natCast_y {p : ℕ} [Fact (Nat.Prime p)] (n : ℕ) : (n : Q5 p).y = (0 : ZMod p) := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih]

@[simp] lemma intCast_x {p : ℕ} [Fact (Nat.Prime p)] (n : ℤ) : (n : Q5 p).x = (n : ZMod p) := by
  cases n with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, Int.cast_natCast]
    simp [natCast_x (p := p)]
  | negSucc n =>
    have h_cast : (Int.negSucc n : Q5 p) = - (n + 1 : Q5 p) := Int.cast_negSucc n
    rw [h_cast]
    simp [natCast_x (p := p)]

@[simp] lemma intCast_y {p : ℕ} [Fact (Nat.Prime p)] (n : ℤ) : (n : Q5 p).y = (0 : ZMod p) := by
  cases n with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, Int.cast_natCast]
    simp [natCast_y (p := p)]
  | negSucc n =>
    have h_cast : (Int.negSucc n : Q5 p) = - (n + 1 : Q5 p) := Int.cast_negSucc n
    rw [h_cast]
    simp [natCast_y (p := p)]

@[simp] lemma ofNat_x {p : ℕ} [Fact (Nat.Prime p)] (n : ℕ) [h : Nat.AtLeastTwo n] : (no_index (OfNat.ofNat n : Q5 p)).x = OfNat.ofNat n := by
  change (n : Q5 p).x = (n : ZMod p)
  exact natCast_x (p := p) n

@[simp] lemma ofNat_y {p : ℕ} [Fact (Nat.Prime p)] (n : ℕ) [h : Nat.AtLeastTwo n] : (no_index (OfNat.ofNat n : Q5 p)).y = 0 := by
  change (n : Q5 p).y = (0 : ZMod p)
  exact natCast_y (p := p) n

instance (p' : ℕ) [Fact (Nat.Prime p')] : CharP (Q5 p') p' where
  cast_eq_zero_iff n := by
    constructor
    · intro h
      have h_x : (n : Q5 p').x = 0 := by rw [h]; rfl
      rw [natCast_x (p := p')] at h_x
      rwa [CharP.cast_eq_zero_iff (ZMod p') p'] at h_x
    · intro h
      have h_z : (n : ZMod p') = 0 := by rwa [CharP.cast_eq_zero_iff (ZMod p') p']
      ext
      · rw [natCast_x (p := p'), h_z]; rfl
      · rw [natCast_y (p := p')]; rfl

def cast_ZMod (d : ZMod p) : Q5 p := ⟨d, 0⟩
@[simp] lemma cast_ZMod_x (d : ZMod p) : (cast_ZMod d).x = d := rfl
@[simp] lemma cast_ZMod_y (d : ZMod p) : (cast_ZMod d).y = 0 := rfl

-- Let's define the elements
def half (p : ℕ) [Fact (Nat.Prime p)] : ZMod p := (2 : ZMod p)⁻¹

theorem h2_nz (hp_gt : p ≥ 13) : (2 : ZMod p) ≠ 0 := by
  intro hc
  have hp : Nat.Prime p := Fact.out
  have h_cast : ((2 : ℕ) : ZMod p) = 0 := hc
  rw [CharP.cast_eq_zero_iff (ZMod p) p] at h_cast
  have h_le : p ≤ 2 := Nat.le_of_dvd (by decide) h_cast
  omega

def phi (p : ℕ) [Fact (Nat.Prime p)] : Q5 p := ⟨half p, half p⟩
def psi (p : ℕ) [Fact (Nat.Prime p)] : Q5 p := ⟨half p, -half p⟩
def omega (p : ℕ) [Fact (Nat.Prime p)] : Q5 p := ⟨0, 1⟩

-- Basic properties
theorem phi_add_psi (hp_gt : p ≥ 13) : phi p + psi p = 1 := by
  ext
  · simp [phi, psi, half]
    have : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ (h2_nz hp_gt)
    linear_combination this
  · simp [phi, psi, half]

theorem phi_mul_psi (hp_gt : p ≥ 13) : phi p * psi p = -1 := by
  ext
  · simp [phi, psi, half]
    have : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ (h2_nz hp_gt)
    linear_combination -(2 * (2 : ZMod p)⁻¹ + 1) * this
  · simp [phi, psi, half]

theorem phi_sq (hp_gt : p ≥ 13) : phi p * phi p = phi p + 1 := by
  ext
  · simp [phi, half]
    have : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ (h2_nz hp_gt)
    linear_combination (3 * (2 : ZMod p)⁻¹ + 1) * this
  · simp [phi, half]
    have : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ (h2_nz hp_gt)
    linear_combination (2 : ZMod p)⁻¹ * this

theorem psi_sq (hp_gt : p ≥ 13) : psi p * psi p = psi p + 1 := by
  ext
  · simp [psi, half]
    have : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ (h2_nz hp_gt)
    linear_combination (3 * (2 : ZMod p)⁻¹ + 1) * this
  · simp [psi, half]
    have : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ (h2_nz hp_gt)
    linear_combination -(2 : ZMod p)⁻¹ * this

theorem fib_step_identity (A B : Q5 p) (hp_gt : p ≥ 13) :
    (phi p) ^ 2 * A - (psi p) ^ 2 * B = (phi p * A - psi p * B) + (A - B) := by
  have h_phi := phi_sq (p := p) hp_gt
  have h_psi := psi_sq (p := p) hp_gt
  rw [pow_two (phi p), pow_two (psi p)] at *
  rw [h_phi, h_psi]
  ext <;> (simp; try ring)

theorem fib_formula_simult (hp_gt : p ≥ 13) (n : ℕ) :
    (phi p) ^ n - (psi p) ^ n = omega p * cast_ZMod (Nat.fib n : ZMod p) ∧
    (phi p) ^ (n + 1) - (psi p) ^ (n + 1) = omega p * cast_ZMod (Nat.fib (n + 1) : ZMod p) := by
  induction n with
  | zero =>
    constructor
    · ext <;> (simp [phi, psi, half, omega]; try ring)
    · ext
      · simp [phi, psi, half, omega]
      · simp [phi, psi, half, omega]
        have : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ (h2_nz hp_gt)
        linear_combination this
  | succ n ih =>
    rcases ih with ⟨ih1, ih2⟩
    refine ⟨ih2, ?_⟩
    have h_rec := fib_step_identity ((phi p) ^ n) ((psi p) ^ n) hp_gt
    have h_pow1 : (phi p) ^ (n + 2) = (phi p) ^ 2 * (phi p) ^ n := by ring
    have h_pow2 : (psi p) ^ (n + 2) = (psi p) ^ 2 * (psi p) ^ n := by ring
    rw [h_pow1, h_pow2, h_rec]
    have h_pow3 : phi p * (phi p) ^ n = (phi p) ^ (n + 1) := by ring
    have h_pow4 : psi p * (psi p) ^ n = (psi p) ^ (n + 1) := by ring
    rw [h_pow3, h_pow4]
    rw [ih1, ih2]
    ext
    · simp [omega]
    · simp [omega]
      rw [Nat.fib_add_two]
      push_cast
      ring

theorem fib_formula (hp_gt : p ≥ 13) (n : ℕ) :
    (phi p) ^ n - (psi p) ^ n = omega p * cast_ZMod (Nat.fib n : ZMod p) :=
  (fib_formula_simult hp_gt n).1

theorem fib_dvd_iff_pow_eq (hp_gt : p ≥ 13) (a : ℕ) :
    p ∣ Nat.fib a ↔ (phi p) ^ a = (psi p) ^ a := by
  have : p ∣ Nat.fib a ↔ (Nat.fib a : ZMod p) = 0 := by
    rw [CharP.cast_eq_zero_iff (ZMod p) p]
  rw [this]
  constructor
  · intro h
    have h1 := fib_formula hp_gt a
    rw [h] at h1
    have h_sub : (phi p) ^ a - (psi p) ^ a = 0 := by
      have h_zero : omega p * cast_ZMod (0 : ZMod p) = 0 := by
        ext <;> simp [omega]
      rw [h1, h_zero]
    ext
    · have hx : ((phi p) ^ a - (psi p) ^ a).x = 0 := by rw [h_sub]; rfl
      simp at hx
      linear_combination hx
    · have hy : ((phi p) ^ a - (psi p) ^ a).y = 0 := by rw [h_sub]; rfl
      simp at hy
      linear_combination hy
  · intro h
    have h1 := fib_formula hp_gt a
    rw [h] at h1
    have h_zero : (psi p) ^ a - (psi p) ^ a = 0 := by
      ext <;> simp
    rw [h_zero] at h1
    have h_y : (omega p * cast_ZMod (Nat.fib a : ZMod p)).y = 0 := by
      rw [← h1]
      rfl
    simp [omega] at h_y
    exact h_y

theorem sq_eq_one (x : ZMod p) (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : (x - 1) * (x + 1) = 0 := by
    calc (x - 1) * (x + 1) = x ^ 2 - 1 := by ring
    _ = 0 := by linear_combination h
  cases mul_eq_zero.mp this with
  | inl h1 => left; linear_combination h1
  | inr h2 => right; linear_combination h2

theorem h5_pow_eq_one (hp_gt : p ≥ 13) : (5 : ZMod p) ^ (p - 1) = 1 := by
  have h5 : (5 : ZMod p) ≠ 0 := by
    intro hc
    have hp : Nat.Prime p := Fact.out
    have h_cast : ((5 : ℕ) : ZMod p) = 0 := hc
    rw [CharP.cast_eq_zero_iff (ZMod p) p] at h_cast
    have : p ≤ 5 := Nat.le_of_dvd (by decide) h_cast
    omega
  exact ZMod.pow_card_sub_one_eq_one h5

theorem omega_sq : omega p * omega p = 5 := by
  ext <;> (simp [omega]; try ring)

theorem omega_pow_simult (n : ℕ) :
    (omega p) ^ (2 * n) = cast_ZMod ((5 : ZMod p) ^ n) ∧
    (omega p) ^ (2 * n + 1) = cast_ZMod ((5 : ZMod p) ^ n) * omega p := by
  induction n with
  | zero =>
    constructor
    · ext <;> (simp [omega]; try ring)
    · ext <;> (simp [omega]; try ring)
  | succ n ih =>
    rcases ih with ⟨ih1, ih2⟩
    have h_rec1 : (omega p) ^ (2 * (n + 1)) = (omega p) ^ (2 * n + 1) * omega p := by
      have : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
      rw [this, pow_succ]
    have h_rec2 : (omega p) ^ (2 * (n + 1) + 1) = (omega p) ^ (2 * (n + 1)) * omega p := by
      rw [pow_succ]
    constructor
    · rw [h_rec1, ih2]
      rw [mul_assoc, omega_sq]
      ext <;> (simp; try ring)
    · rw [h_rec2]
      have h_first : (omega p) ^ (2 * (n + 1)) = cast_ZMod ((5 : ZMod p) ^ (n + 1)) := by
        rw [h_rec1, ih2, mul_assoc, omega_sq]
        ext <;> (simp; try ring)
      rw [h_first]

theorem omega_pow_p (hp_gt : p ≥ 13) :
    (omega p) ^ p = cast_ZMod ((5 : ZMod p) ^ ((p - 1) / 2)) * omega p := by
  have hp : Nat.Prime p := Fact.out
  have h_div : p = 2 * ((p - 1) / 2) + 1 := by
    have h_odd : p % 2 = 1 := by
      have : p > 2 := by omega
      have h_even : ¬ 2 ∣ p := by
        intro hc
        have : p = 2 := (hp.eq_one_or_self_of_dvd 2 hc).resolve_left (by decide) |>.symm
        omega
      have h_mod : p % 2 < 2 := Nat.mod_lt p (by decide)
      have : p % 2 ≠ 0 := by
        intro hc
        have : 2 ∣ p := Nat.dvd_of_mod_eq_zero hc
        have : p = 2 := (hp.eq_one_or_self_of_dvd 2 this).resolve_left (by decide) |>.symm
        omega
      omega
    omega
  have h_eq : (omega p) ^ p = (omega p) ^ (2 * ((p - 1) / 2) + 1) := by
    congr 1
  rw [h_eq]
  exact (omega_pow_simult ((p - 1) / 2)).2

theorem cast_ZMod_pow (x : ZMod p) (k : ℕ) : (cast_ZMod x) ^ k = cast_ZMod (x ^ k) := by
  induction k with
  | zero => ext <;> (simp; try ring)
  | succ k ih =>
    rw [pow_succ, pow_succ, ih]
    ext <;> (simp; try ring)

theorem natCast_pow_p (n : ℕ) : (n : Q5 p) ^ p = (n : Q5 p) := by
  have h_eq : (n : Q5 p) = cast_ZMod (p := p) (n : ZMod p) := by ext <;> simp
  rw [h_eq]
  rw [cast_ZMod_pow]
  rw [ZMod.pow_card]

theorem cast_ZMod_pow_p (x : ZMod p) : (cast_ZMod x) ^ p = cast_ZMod x := by
  rw [cast_ZMod_pow, ZMod.pow_card]

lemma phi_eq_cast (hp_gt : p ≥ 13) : phi p = cast_ZMod (half p) + cast_ZMod (half p) * omega p := by
  ext <;> (simp [phi, omega]; try ring)

lemma psi_eq_cast (hp_gt : p ≥ 13) : psi p = cast_ZMod (half p) + cast_ZMod (-half p) * omega p := by
  ext <;> (simp [psi, omega]; try ring)

lemma phi_pow_p (hp_gt : p ≥ 13) :
    (phi p) ^ p = cast_ZMod (half p) + cast_ZMod (half p) * (cast_ZMod ((5 : ZMod p) ^ ((p - 1) / 2)) * omega p) := by
  rw [phi_eq_cast hp_gt, add_pow_char, mul_pow, cast_ZMod_pow_p, omega_pow_p hp_gt]

lemma psi_pow_p (hp_gt : p ≥ 13) :
    (psi p) ^ p = cast_ZMod (half p) + cast_ZMod (-half p) * (cast_ZMod ((5 : ZMod p) ^ ((p - 1) / 2)) * omega p) := by
  rw [psi_eq_cast hp_gt, add_pow_char, mul_pow, cast_ZMod_pow_p, cast_ZMod_pow_p, omega_pow_p hp_gt]

lemma phi_pow_p_sub_psi_pow_p (hp_gt : p ≥ 13) :
    (phi p) ^ p - (psi p) ^ p = cast_ZMod ((5 : ZMod p) ^ ((p - 1) / 2)) * omega p := by
  rw [phi_pow_p hp_gt, psi_pow_p hp_gt]
  have h_half : half p * 2 = 1 := by
    rw [mul_comm]
    exact mul_inv_cancel₀ (h2_nz hp_gt)
  ext
  · simp [omega]
  · simp [omega]
    linear_combination (5 : ZMod p) ^ ((p - 1) / 2) * h_half

lemma phi_psi_pow_p_cases (hp_gt : p ≥ 13) :
    ((5 : ZMod p) ^ ((p - 1) / 2) = 1 ∧ (phi p) ^ p = phi p ∧ (psi p) ^ p = psi p) ∨
    ((5 : ZMod p) ^ ((p - 1) / 2) = -1 ∧ (phi p) ^ p = psi p ∧ (psi p) ^ p = phi p) := by
  have hc_sq : ((5 : ZMod p) ^ ((p - 1) / 2)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, ← h5_pow_eq_one (p := p) hp_gt]
    congr 1
    have hp : Nat.Prime p := Fact.out
    have h_odd : p % 2 = 1 := by
      have : p > 2 := by omega
      have h_even : ¬ 2 ∣ p := by
        intro hc
        have : p = 2 := (hp.eq_one_or_self_of_dvd 2 hc).resolve_left (by decide) |>.symm
        omega
      omega
    omega
  have hc_cases := sq_eq_one ((5 : ZMod p) ^ ((p - 1) / 2)) hc_sq
  rcases hc_cases with hc1 | hc2
  · left
    refine ⟨hc1, ?_, ?_⟩
    · rw [phi_pow_p hp_gt, hc1]
      ext <;> (simp [phi, omega]; try ring)
    · rw [psi_pow_p hp_gt, hc1]
      ext <;> (simp [psi, omega]; try ring)
  · right
    refine ⟨hc2, ?_, ?_⟩
    · rw [phi_pow_p hp_gt, hc2]
      ext <;> (simp [phi, psi, omega]; try ring)
    · rw [psi_pow_p hp_gt, hc2]
      ext <;> (simp [phi, psi, omega]; try ring)

lemma prime_entry_point_bound_helper (hp_gt : p ≥ 13) :
    p ∣ Nat.fib (p - 1) ∨ p ∣ Nat.fib (p + 1) := by
  have hc_cases := phi_psi_pow_p_cases hp_gt
  rcases hc_cases with h_one | h_neg_one
  · left
    rw [fib_dvd_iff_pow_eq hp_gt]
    have h_phi : (phi p) ^ (p - 1) * phi p = phi p := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      exact h_one.2.1
    have h_psi : (psi p) ^ (p - 1) * psi p = psi p := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      exact h_one.2.2
    have h_phi_eq : (phi p) ^ (p - 1) = 1 := by
      have h_eq : (phi p) ^ (p - 1) * -1 = -1 := by
        calc (phi p) ^ (p - 1) * -1 = (phi p) ^ (p - 1) * (phi p * psi p) := by rw [← phi_mul_psi hp_gt]
        _ = (phi p) ^ (p - 1) * phi p * psi p := by ring
        _ = phi p * psi p := by rw [h_phi]
        _ = -1 := phi_mul_psi hp_gt
      calc (phi p) ^ (p - 1) = (phi p) ^ (p - 1) * -1 * -1 := by ring
      _ = -1 * -1 := by rw [h_eq]
      _ = 1 := by ring
    have h_psi_eq : (psi p) ^ (p - 1) = 1 := by
      have h_eq : (psi p) ^ (p - 1) * -1 = -1 := by
        calc (psi p) ^ (p - 1) * -1 = (psi p) ^ (p - 1) * (psi p * phi p) := by rw [← phi_mul_psi hp_gt, mul_comm (phi p) (psi p)]
        _ = (psi p) ^ (p - 1) * psi p * phi p := by ring
        _ = psi p * phi p := by rw [h_psi]
        _ = -1 := by rw [mul_comm, phi_mul_psi hp_gt]
      calc (psi p) ^ (p - 1) = (psi p) ^ (p - 1) * -1 * -1 := by ring
      _ = -1 * -1 := by rw [h_eq]
      _ = 1 := by ring
    rw [h_phi_eq, h_psi_eq]
  · right
    rw [fib_dvd_iff_pow_eq hp_gt]
    have h_phi_eq : (phi p) ^ (p + 1) = -1 := by
      calc (phi p) ^ (p + 1) = (phi p) ^ p * phi p := by ring
      _ = psi p * phi p := by rw [h_neg_one.2.1]
      _ = phi p * psi p := by ring
      _ = -1 := phi_mul_psi hp_gt
    have h_psi_eq : (psi p) ^ (p + 1) = -1 := by
      calc (psi p) ^ (p + 1) = (psi p) ^ p * psi p := by ring
      _ = phi p * psi p := by rw [h_neg_one.2.2]
      _ = -1 := phi_mul_psi hp_gt
    rw [h_phi_eq, h_psi_eq]

end Q5

lemma prime_entry_point_bound (p : ℕ) (hp : Nat.Prime p) (hp_gt : p ≥ 13) :
    ∃ a, a > 0 ∧ p ∣ Nat.fib a ∧ a < 3 * p := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  have h_cases := Q5.prime_entry_point_bound_helper (p := p) hp_gt
  rcases h_cases with h_sub | h_add
  · use p - 1
    refine ⟨by omega, h_sub, by omega⟩
  · use p + 1
    refine ⟨by omega, h_add, by omega⟩

lemma descent_step (n : ℕ) (hn : 1 < n) (h_odd : n % 2 = 1) (h3 : ¬ 3 ∣ n) (hdvd : (2 * n) ∣ H n)
    (p : ℕ) (hp : Nat.Prime p) (h_p_div : p ∣ n) (hp_gt : p ≥ 29) :
    ∃ q, Nat.Prime q ∧ q ∣ n ∧ q < p := by
  have h_le : 1 ≤ n := by omega
  have h_p_dvd_2n : p ∣ 2 * n := dvd_mul_of_dvd_right h_p_div 2
  have h_p_dvd_H : p ∣ H n := dvd_trans h_p_dvd_2n hdvd
  have h_p_dvd_fib6 : p ∣ Nat.fib (6 * n) := prime_dvd_fib_six n hn h_odd p hp h_p_dvd_H
  have h_n_pos : 0 < 6 * n := by omega
  obtain ⟨a, ha_pos, ha_dvd, ha_min⟩ := exists_minimal_fib_dvd p (6 * n) h_n_pos h_p_dvd_fib6
  have h_a_dvd_6n : a ∣ 6 * n := by
    rwa [← fib_dvd_iff p a (6 * n) ha_pos ha_dvd ha_min]
  have h_a_ndvd_2n : ¬ a ∣ 2 * n := by
    intro hc
    have h_p_dvd_fib2n : p ∣ Nat.fib (2 * n) := by
      rwa [fib_dvd_iff p a (2 * n) ha_pos ha_dvd ha_min]
    have h_div_eq2 : H n * (H n + 2) = 5 * Nat.fib (2 * n) ^ 2 + 3 := by
      have h_sum_sq : (Nat.fib (2 * n + 1) + Nat.fib (2 * n - 1)) ^ 2 = 5 * Nat.fib (2 * n) ^ 2 + 4 := by
        obtain ⟨k, hk⟩ : ∃ k, n = 2 * k + 1 := by
          use n / 2
          omega
        have h_id := fib_identity_1_k (2 * k)
        have h_idx1 : 2 * (2 * k) + 3 = 2 * n + 1 := by omega
        have h_idx2 : 2 * (2 * k) + 1 = 2 * n - 1 := by omega
        have h_idx3 : 2 * (2 * k) + 2 = 2 * n := by omega
        rw [h_idx1, h_idx2, h_idx3] at h_id
        exact h_id
      have h_H_eq : Nat.fib (2 * n + 1) + Nat.fib (2 * n - 1) = H n + 1 := by
        have h_fib := H_eq_fib n h_le
        have h_pos : Nat.fib (2 * n + 1) ≥ 2 := by
          have : 2 * n + 1 ≥ 3 := by omega
          have h_fib_mono := Nat.fib_mono this
          exact h_fib_mono
        omega
      have h_sq : (H n + 1) ^ 2 = 5 * Nat.fib (2 * n) ^ 2 + 4 := by
        rw [← h_H_eq, h_sum_sq]
      have h_alg_sq : (H n + 1) ^ 2 = H n * (H n + 2) + 1 := by ring
      rw [h_alg_sq] at h_sq
      have h_add : H n * (H n + 2) + 1 = 5 * Nat.fib (2 * n) ^ 2 + 3 + 1 := by
        omega
      exact Nat.add_right_cancel h_add
    have h_p_dvd_lhs : p ∣ H n * (H n + 2) := dvd_mul_of_dvd_left h_p_dvd_H (H n + 2)
    rw [h_div_eq2] at h_p_dvd_lhs
    have h_p_dvd_fib_sq : p ∣ 5 * Nat.fib (2 * n) ^ 2 := dvd_mul_of_dvd_right (dvd_mul_of_dvd_right h_p_dvd_fib2n _) 5
    have h_p_dvd_3 : p ∣ 3 := by
      have : 3 = (5 * Nat.fib (2 * n) ^ 2 + 3) - 5 * Nat.fib (2 * n) ^ 2 := by omega
      rw [this]
      exact Nat.dvd_sub h_p_dvd_lhs h_p_dvd_fib_sq
    have hp_le_3 : p ≤ 3 := Nat.le_of_dvd (by decide) h_p_dvd_3
    omega
  have h_3_dvd_a : 3 ∣ a := by
    by_contra hc
    have h_coprime : Nat.Coprime a 3 := Nat.Coprime.symm (Nat.Prime.coprime_iff_not_dvd Nat.prime_three |>.mpr hc)
    have h_a_dvd_2n : a ∣ 2 * n := by
      have h_6n : 6 * n = 2 * n * 3 := by omega
      rw [h_6n] at h_a_dvd_6n
      exact Nat.Coprime.dvd_of_dvd_mul_right h_coprime h_a_dvd_6n
    contradiction
  obtain ⟨a_p, ha_p_pos, ha_p_dvd, ha_p_bound⟩ := prime_entry_point_bound p hp (by omega)
  have h_a_le_ap : a ≤ a_p := ha_min a_p ha_p_pos ha_p_dvd
  have h_a_lt_3p : a < 3 * p := lt_of_le_of_lt h_a_le_ap ha_p_bound
  have h_a_val : a = 3 * (a / 3) := (Nat.mul_div_cancel' h_3_dvd_a).symm
  have h_a_div_3_dvd_2n : 3 * (a / 3) ∣ 3 * (2 * n) := by
    have : 3 * (2 * n) = 6 * n := by omega
    rw [← h_a_val, this]
    exact h_a_dvd_6n
  have h_a_div_3_dvd_2n_real : a / 3 ∣ 2 * n := Nat.dvd_of_mul_dvd_mul_left (by decide) h_a_div_3_dvd_2n
  have h_a_div_3_pos : a / 3 > 0 := by
    have : a / 3 ≠ 0 := by
      intro hc
      have : a = 0 := by omega
      omega
    omega
  have h_a_div_3_lt_p : a / 3 < p := by
    have : 3 * (a / 3) < 3 * p := by
      rw [← h_a_val]
      exact h_a_lt_3p
    omega
  have h_gcd_eq : Nat.gcd (a / 3) 2 ∣ a / 3 := Nat.gcd_dvd_left (a / 3) 2
  have h_gcd_eq2 : Nat.gcd (a / 3) 2 ∣ 2 := Nat.gcd_dvd_right (a / 3) 2
  have h_gcd_cases : Nat.gcd (a / 3) 2 = 1 ∨ Nat.gcd (a / 3) 2 = 2 := by
    have : Nat.gcd (a / 3) 2 ≤ 2 := Nat.le_of_dvd (by decide) h_gcd_eq2
    have : Nat.gcd (a / 3) 2 ≠ 0 := by
      intro hc
      have : 2 = 0 := Nat.eq_zero_of_gcd_eq_zero_right hc
      omega
    omega
  let d := (a / 3) / Nat.gcd (a / 3) 2
  have h_d_dvd_n : d ∣ n := by
    rcases h_gcd_cases with h_gcd | h_gcd
    · have h_gcd_eq : Nat.gcd (a / 3) 2 = 1 := h_gcd
      have : d = a / 3 := by
        dsimp [d]
        rw [h_gcd_eq]
        exact Nat.div_one (a / 3)
      rw [this]
      have h_cop : Nat.Coprime (a / 3) 2 := by
        rwa [Nat.Coprime]
      have h_a_div_3_dvd_n2 : a / 3 ∣ n * 2 := by
        rw [mul_comm]
        exact h_a_div_3_dvd_2n_real
      exact Nat.Coprime.dvd_of_dvd_mul_right h_cop h_a_div_3_dvd_n2
    · have h_gcd_eq : Nat.gcd (a / 3) 2 = 2 := h_gcd
      have h_div_even : 2 ∣ a / 3 := by
        have : Nat.gcd (a / 3) 2 = 2 := h_gcd
        rw [← this]
        exact Nat.gcd_dvd_left (a / 3) 2
      have : d = (a / 3) / 2 := by
        change (a / 3) / Nat.gcd (a / 3) 2 = (a / 3) / 2
        rw [h_gcd_eq]
      have h_alg : 2 * n = 2 * n := rfl
      have h_dvd_mul : 2 * d ∣ 2 * n := by
        have : 2 * d = a / 3 := by
          dsimp [d]
          rw [h_gcd_eq]
          exact Nat.mul_div_cancel' h_div_even
        rw [this]
        exact h_a_div_3_dvd_2n_real
      exact Nat.dvd_of_mul_dvd_mul_left (by decide) h_dvd_mul
  have h_d_ge_2 : d ≥ 2 := by
    have h_gcd_le : Nat.gcd (a / 3) 2 ≤ a / 3 := Nat.le_of_dvd h_a_div_3_pos (Nat.gcd_dvd_left (a / 3) 2)
    have h_gcd_pos : Nat.gcd (a / 3) 2 > 0 := Nat.gcd_pos_of_pos_right (a / 3) (by decide)
    have h_d_pos : d > 0 := Nat.div_pos h_gcd_le h_gcd_pos
    have h_cases : d = 1 ∨ d ≥ 2 := by omega
    rcases h_cases with hd_eq | h_ge_2
    · rcases h_gcd_cases with h_gcd | h_gcd
      · have : a / 3 = 1 := by
          have : d = a / 3 := by
            dsimp [d]
            rw [h_gcd]
            exact Nat.div_one (a / 3)
          omega
        have : a = 3 := by omega
        have : p ∣ Nat.fib 3 := by
          have : 3 = a := by omega
          rw [this]
          exact ha_dvd
        have : p ∣ 2 := this
        have : p ≤ 2 := Nat.le_of_dvd (by decide) this
        omega
      · have : a / 3 = 2 := by
          have : d = (a / 3) / 2 := by
            change (a / 3) / Nat.gcd (a / 3) 2 = (a / 3) / 2
            rw [h_gcd]
          have : (a / 3) / 2 = 1 := by omega
          have h_div_even : 2 ∣ a / 3 := by
            have : Nat.gcd (a / 3) 2 = 2 := h_gcd
            rw [← this]
            exact Nat.gcd_dvd_left (a / 3) 2
          omega
        have : a = 6 := by omega
        have : p ∣ Nat.fib 6 := by
          have : 6 = a := by omega
          rw [this]
          exact ha_dvd
        have : p ∣ 8 := this
        have : p ≤ 8 := Nat.le_of_dvd (by decide) this
        omega
    · exact h_ge_2
  have h_d_pos : d > 0 := by omega
  have h_ex_prime : ∃ q, Nat.Prime q ∧ q ∣ d := by
    exact Nat.exists_prime_and_dvd (by omega)
  obtain ⟨q, hq, hq_dvd⟩ := h_ex_prime
  refine ⟨q, hq, dvd_trans hq_dvd h_d_dvd_n, ?_⟩
  have hq_le_d : q ≤ d := Nat.le_of_dvd h_d_pos hq_dvd
  have hd_le_a : d ≤ a / 3 := by
    rcases h_gcd_cases with h_gcd | h_gcd
    · dsimp [d]
      rw [h_gcd]
      omega
    · dsimp [d]
      rw [h_gcd]
      omega
  have h_q_lt_p : q < p := by omega
  exact h_q_lt_p

theorem not_dvd_of_not_3_dvd_odd (n : ℕ) (hn : 1 < n) (h3 : ¬ 3 ∣ n) (h_odd : n % 2 = 1) :
    ¬ (2 * n) ∣ H n := by
  intro hdvd
  generalize hp_eq : n.minFac = p
  have hp : Nat.Prime p := by rw [← hp_eq]; exact Nat.minFac_prime (ne_of_gt hn)
  have hp_dvd : p ∣ n := by rw [← hp_eq]; exact Nat.minFac_dvd n
  have hp_odd : p % 2 = 1 := by
    have h_mod : p % 2 = 0 ∨ p % 2 = 1 := by omega
    rcases h_mod with h_even | h_odd
    · have h_div : 2 ∣ p := Nat.dvd_of_mod_eq_zero h_even
      have h_div_n : 2 ∣ n := dvd_trans h_div hp_dvd
      have : n % 2 = 0 := Nat.mod_eq_zero_of_dvd h_div_n
      omega
    · exact h_odd
  have hp_cases : p = 5 ∨ p % 4 = 3 ∨ p = 13 ∨ p = 17 ∨ p ≥ 29 := by
    have : p ≥ 2 := hp.two_le
    have : p ≠ 2 := by
      intro hc
      rw [hc] at hp_odd
      omega
    have : p ≠ 3 := by
      intro hc
      rw [hc] at hp_dvd
      exact h3 hp_dvd
    have : p % 4 = 1 ∨ p % 4 = 3 := by
      have h_mod : p % 4 < 4 := Nat.mod_lt p (by decide)
      have h_odd_mod : p % 2 = 1 := hp_odd
      have : p % 4 ≠ 0 := by
        intro hc
        have : 4 ∣ p := Nat.dvd_of_mod_eq_zero hc
        have : 2 ∣ p := dvd_trans (by decide) this
        have : p % 2 = 0 := Nat.mod_eq_zero_of_dvd this
        omega
      have : p % 4 ≠ 2 := by
        intro hc
        have : p % 2 = 0 := by
          have : p = 4 * (p / 4) + 2 := by
            have : p % 4 = 2 := hc
            omega
          omega
        omega
      omega
    rcases this with h_mod | h_mod
    · -- p % 4 = 1
      have : p ≠ 2 := by omega
      have : p ≠ 3 := by omega
      have : p = 5 ∨ p = 13 ∨ p = 17 ∨ p ≥ 29 := by
        have : p % 4 = 1 := h_mod
        have h_mod_val : p = 4 * (p / 4) + 1 := by omega
        have h_div : p / 4 = 1 ∨ p / 4 = 2 ∨ p / 4 = 3 ∨ p / 4 = 4 ∨ p / 4 = 5 ∨ p / 4 = 6 ∨ p / 4 ≥ 7 := by omega
        rcases h_div with h | h | h | h | h | h | h
        · -- p / 4 = 1 => p = 5
          left
          omega
        · -- p / 4 = 2 => p = 9 (not prime)
          have hp9 : p = 9 := by omega
          have h_not : ¬ Nat.Prime 9 := by decide
          rw [hp9] at hp
          exact False.elim (h_not hp)
        · -- p / 4 = 3 => p = 13
          right; left; omega
        · -- p / 4 = 4 => p = 17
          right; right; left; omega
        · -- p / 4 = 5 => p = 21 (not prime)
          have hp21 : p = 21 := by omega
          have h_not : ¬ Nat.Prime 21 := by decide
          rw [hp21] at hp
          exact False.elim (h_not hp)
        · -- p / 4 = 6 => p = 25 (not prime)
          have hp25 : p = 25 := by omega
          have h_not : ¬ Nat.Prime 25 := by decide
          rw [hp25] at hp
          exact False.elim (h_not hp)
        · -- p / 4 >= 7 => p >= 29
          right; right; right; omega
      omega
    · -- p % 4 = 3
      right; left; exact h_mod
  rcases hp_cases with hp_eq5 | hp_mod | hp_eq13 | hp_eq17 | hp_gt
  · have hp_dvd_5 : 5 ∣ n := hp_eq5 ▸ hp_dvd
    exact not_dvd_of_odd_five n hn h_odd hp_dvd_5 hdvd
  · exact not_dvd_of_prime_three_mod_four n hn h_odd p hp hp_mod hp_dvd hdvd
  · have h_p_dvd_H : 13 ∣ H n := by
      have hp_dvd_13 : 13 ∣ n := hp_eq13 ▸ hp_dvd
      have : 13 ∣ 2 * n := dvd_mul_of_dvd_right hp_dvd_13 2
      exact dvd_trans this hdvd
    have h_mod_zero : H n % 13 = 0 := Nat.mod_eq_zero_of_dvd h_p_dvd_H
    have h_mod_nz : H n % 13 ≠ 0 := H_mod_13_ne_zero n (by omega)
    contradiction
  · have h_p_dvd_H : 17 ∣ H n := by
      have hp_dvd_17 : 17 ∣ n := hp_eq17 ▸ hp_dvd
      have : 17 ∣ 2 * n := dvd_mul_of_dvd_right hp_dvd_17 2
      exact dvd_trans this hdvd
    have h_mod_zero : H n % 17 = 0 := Nat.mod_eq_zero_of_dvd h_p_dvd_H
    have h_mod_nz : H n % 17 ≠ 0 := H_mod_17_ne_zero_of_not_3_dvd n (by omega) h3
    contradiction
  · obtain ⟨q, hq, hq_dvd, hq_lt⟩ := descent_step n hn h_odd h3 hdvd p hp hp_dvd hp_gt
    have hq_gt_1 : q > 1 := by
      have : q ≥ 2 := hq.two_le
      omega
    have hq_ge_p : q ≥ p := by
      rw [← hp_eq]
      exact Nat.minFac_le_of_dvd hq_gt_1 hq_dvd
    omega

/--
A175386 We conjecture that sum((1/i)*C(2n-i-1,i-1),i=1..n) is not an integer for $n>1$.
-/
theorem oeis_175386_conjecture_0 (n : ℕ) (hn : 1 < n) : a n ≠ 1 := by
  intro hc
  rw [a_eq_one_iff n hn] at hc
  have h_cases : 3 ∣ n ∨ (¬ 3 ∣ n ∧ n % 2 = 0) ∨ (¬ 3 ∣ n ∧ n % 2 = 1) := by omega
  rcases h_cases with h3 | h_even | h_odd_not_3
  · exact not_dvd_of_3_dvd n hn h3 hc
  · exact not_dvd_of_not_3_dvd_even n hn h_even.1 h_even.2 hc
  · exact not_dvd_of_not_3_dvd_odd n hn h_odd_not_3.1 h_odd_not_3.2 hc

