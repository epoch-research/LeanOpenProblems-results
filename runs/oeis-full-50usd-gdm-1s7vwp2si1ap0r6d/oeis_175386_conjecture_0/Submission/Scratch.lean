import FormalConjectures.Util.ProblemImports

open scoped BigOperators

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

def a (n : ℕ) : ℕ := (S n).den

theorem a_eq_one_iff (n : ℕ) (hn : 1 < n) : a n = 1 ↔ (2 * n) ∣ H n := by
  have h_nz : (2 * n : ℚ) ≠ 0 := by
    have : 2 * n > 0 := by omega
    positivity
  have h_div : S n = (H n : ℚ) / (2 * n : ℚ) := by
    rw [← H_eq_S n hn]
    rw [mul_div_cancel_left₀ (S n) h_nz]
  unfold a
  rw [h_div]
  have h_nz_nat : 2 * n ≠ 0 := by omega
  have h_cast : (2 * n : ℚ) = ((2 * n : ℕ) : ℚ) := by norm_cast
  rw [h_cast]
  exact Rat.den_div_natCast_eq_one_iff (H n) (2 * n) h_nz_nat


theorem test_fib_sum (n : ℕ) : Nat.fib (n + 1) = ∑ k ∈ Finset.range (n + 1), Nat.choose k (n - k) := by
  rw [Nat.fib_succ_eq_sum_choose]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ]


theorem test_reflect (n : ℕ) : ∑ i ∈ Finset.range (2 * n + 1), Nat.choose (2 * n - i) i = ∑ i ∈ Finset.range (2 * n + 1), Nat.choose i (2 * n - i) := by
  have := Finset.sum_range_reflect (fun i => Nat.choose i (2 * n - i)) (2 * n + 1)
  have h_eq : (fun i => Nat.choose (2 * n + 1 - 1 - i) (2 * n - (2 * n + 1 - 1 - i))) = (fun i => Nat.choose (2 * n - i) i) := by
    funext i
    have : 2 * n + 1 - 1 - i = 2 * n - i := by omega
    rw [this]
    congr 1
    omega
  rw [h_eq] at this
  exact this.symm

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
    have h_insert : Finset.Icc 1 (n + 1) = Finset.insert (n + 1) (Finset.Icc 1 n) := by
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

theorem sum_choose_sub_eq_fib (n : ℕ) (hn : 1 ≤ n) : ∑ i ∈ Finset.Icc 1 n, Nat.choose (2 * n - i - 1) (i - 1) = Nat.fib (2 * n - 1) := by
  have h_eq : (fun i => Nat.choose (2 * n - i - 1) (i - 1)) = (fun i => Nat.choose (2 * n - 2 - (i - 1)) (i - 1)) := by
    funext i
    congr 2
    omega
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
  have h_range : Finset.range (n + 1) = Finset.insert 0 (Finset.Icc 1 n) := by
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
  -- simplify some of the indices in h_fib1 and h_fib2
  have h_idx1 : 2 * n + 1 + 4 = 2 * n + 5 := by omega
  have h_idx2 : 2 * n + 1 + 2 = 2 * n + 3 := by omega
  have h_idx3 : 2 * n - 1 + 4 = 2 * n + 3 := by omega
  have h_idx4 : 2 * n - 1 + 2 = 2 * n + 1 := by omega
  rw [h_idx1, h_idx2] at h_fib1
  rw [h_idx3, h_idx4] at h_fib2
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
  refine ⟨ih2, ?_⟩
  have h_rec := H_recurrence (n + 1) (by omega)
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

def H_mod_5_prop (n : ℕ) : Prop :=
  H (n + 1) % 5 = (if (n + 1) % 2 = 1 then 2 else 1) ∧
  H (n + 2) % 5 = (if (n + 2) % 2 = 1 then 2 else 1)

theorem H_mod_5_prop_zero : H_mod_5_prop 0 := by
  unfold H_mod_5_prop
  decide

theorem H_mod_5_prop_succ (n : ℕ) (ih : H_mod_5_prop n) : H_mod_5_prop (n + 1) := by
  unfold H_mod_5_prop at *
  rcases ih with ⟨ih1, ih2⟩
  refine ⟨ih2, ?_⟩
  have h_rec := H_recurrence (n + 1) (by omega)
  have h_mod : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h_mod with h0 | h1
  · have h_div1 : (n + 1) % 2 = 1 := by omega
    have h_div2 : (n + 2) % 2 = 0 := by omega
    have h_div3 : (n + 3) % 2 = 1 := by omega
    rw [h_div1] at ih1
    rw [if_pos rfl] at ih1
    rw [h_div2] at ih2
    rw [if_neg (by omega)] at ih2
    rw [h_div3]
    rw [if_pos rfl]
    omega
  · have h_div1 : (n + 1) % 2 = 0 := by omega
    have h_div2 : (n + 2) % 2 = 1 := by omega
    have h_div3 : (n + 3) % 2 = 0 := by omega
    rw [h_div1] at ih1
    rw [if_neg (by omega)] at ih1
    rw [h_div2] at ih2
    rw [if_pos rfl] at ih2
    rw [h_div3]
    rw [if_neg (by omega)]
    omega

theorem H_mod_5 (n : ℕ) : H n % 5 = (if n % 2 = 1 then 2 else 1) ∨ n = 0 := by
  cases n with
  | zero => simp
  | succ n =>
    have h_prop : H_mod_5_prop n := by
      induction n with
      | zero => exact H_mod_5_prop_zero
      | succ n ih => exact H_mod_5_prop_succ n ih
    unfold H_mod_5_prop at h_prop
    left
    exact h_prop.1


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

theorem not_dvd_of_not_3_dvd_odd (n : ℕ) (hn : 1 < n) (h3 : ¬ 3 ∣ n) (h_odd : n % 2 = 1) : ¬ (2 * n) ∣ H n := by
  intro hdvd
  have h_5_dvd : 5 ∣ 2 * n := by
    -- wait, we need 5 | n, but what if 5 does not divide n?
    sorry

  omega












