import Mathlib

open ArithmeticFunction Nat Set

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000



lemma divisor_le_div_two (n : ℕ) (d : ℕ) (h_dvd : d ∣ n) (h_lt : d < n) : d ≤ n / 2 := by
  rcases eq_or_ne d 0 with rfl | hd_ne
  · omega
  · have h_div : n / d ≥ 2 := by
      by_contra! h_lt_2
      interval_cases h_div : n / d
      · have h_eq : n = 0 := by
          rw [← Nat.div_mul_cancel h_dvd, h_div, zero_mul]
        omega
      · have h_eq : d = n := by
          rw [← Nat.div_mul_cancel h_dvd, h_div, one_mul]
        omega
    have h_mul_le : 2 * d ≤ n := by
      calc
        2 * d ≤ (n / d) * d := Nat.mul_le_mul_right d h_div
        _ = n := Nat.div_mul_cancel h_dvd
    omega


def S (x : ℕ) : Finset ℕ := (divisors x).erase 1 |>.erase x


lemma divisors_decomp (x : ℕ) (h : x ≥ 5) :
    ∑ d ∈ divisors x, d = 1 + x + ∑ d ∈ S x, d := by
  have h1 : 1 ∈ divisors x := by
    rw [mem_divisors]
    exact ⟨one_dvd x, by omega⟩
  have hx : x ∈ divisors x := by
    rw [mem_divisors]
    exact ⟨dvd_rfl, by omega⟩
  have hne : 1 ≠ x := by omega
  have hx_erase : x ∈ (divisors x).erase 1 := by
    rw [Finset.mem_erase]
    exact ⟨hne.symm, hx⟩
  rw [← Finset.add_sum_erase (divisors x) (fun d => d) h1]
  rw [← Finset.add_sum_erase ((divisors x).erase 1) (fun d => d) hx_erase]
  unfold S
  ring

lemma k_ge_two (x : ℕ) (hx : x ≥ 1200) (h_mod : sigma 1 x % x = 5) (h_ab : sigma 1 x ≥ 2 * x) : sigma 1 x / x ≥ 2 := by
  have h_div : sigma 1 x = x * (sigma 1 x / x) + 5 := by
    have h1 : sigma 1 x = x * (sigma 1 x / x) + (sigma 1 x) % x := (Nat.div_add_mod (sigma 1 x) x).symm
    rw [h_mod] at h1
    exact h1
  by_contra! h_lt
  have hx_ge_5 : x ≥ 5 := by omega
  interval_cases h_k : sigma 1 x / x
  · have h_decomp := divisors_decomp x hx_ge_5
    rw [← sigma_one_apply] at h_decomp
    omega
  · omega


lemma mem_S_two_and_div_two (x : ℕ) (hx : x ≥ 1200) (h_even : 2 ∣ x) : 2 ∈ S x ∧ x / 2 ∈ S x := by
  constructor
  · unfold S
    rw [Finset.mem_erase, Finset.mem_erase, mem_divisors]
    refine ⟨?_, ?_, h_even, ?_⟩
    · omega
    · decide
    · omega
  · unfold S
    rw [Finset.mem_erase, Finset.mem_erase, mem_divisors]
    have h_dvd : x / 2 ∣ x := by
      use 2
      rw [Nat.div_mul_cancel h_even]
    refine ⟨?_, ?_, h_dvd, ?_⟩
    · omega
    · omega
    · omega


lemma odd_divisor_le_div_three (x : ℕ) (h_odd : x % 2 = 1) (d : ℕ) (h_dvd : d ∣ x) (h_lt : d < x) : d ≤ x / 3 := by
  rcases eq_or_ne d 0 with rfl | hd_ne
  · omega
  · have h_div_dvd : x / d ∣ x := div_dvd_of_dvd h_dvd
    have h_div_odd : (x / d) % 2 = 1 := by
      have h_odd_dvd : ∀ y, y ∣ x → y % 2 = 1 := by
        intro y hy
        rcases hy with ⟨c, rfl⟩
        rw [Nat.mul_mod] at h_odd
        by_contra! h_even
        have hy_even : y % 2 = 0 := by omega
        rw [hy_even, zero_mul, zero_mod] at h_odd
        contradiction
      exact h_odd_dvd (x / d) h_div_dvd
    have h_div_ne : x / d ≠ 1 := by
      intro h1
      have h_eq : d = x := by
        rw [← Nat.div_mul_cancel h_dvd, h1, one_mul]
      omega
    have h_div_ne_0 : x / d ≠ 0 := by
      intro h0
      have h_eq : x = 0 := by
        rw [← Nat.div_mul_cancel h_dvd, h0, zero_mul]
      omega
    generalize hu : x / d = u at *
    have h_div : u ≥ 3 := by omega
    have h_mul_le : 3 * d ≤ x := by
      calc
        3 * d ≤ u * d := Nat.mul_le_mul_right d h_div
        _ = x := by rw [← hu]; exact Nat.div_mul_cancel h_dvd
    omega


lemma mem_S_le_div_three_of_odd (x : ℕ) (h_odd : x % 2 = 1) (d : ℕ) (hd : d ∈ S x) : d ≤ x / 3 := by
  unfold S at hd
  rw [Finset.mem_erase, Finset.mem_erase, mem_divisors] at hd
  have h_dvd := hd.2.2.1
  have h_lt : d < x := by
    have h_le := divisor_le (by rw [mem_divisors]; exact ⟨h_dvd, hd.2.2.2⟩)
    omega
  exact odd_divisor_le_div_three x h_odd d h_dvd h_lt


lemma mem_S_le_div_three_of_ne (x : ℕ) (d : ℕ) (hd : d ∈ S x) (hne : d ≠ x / 2) : d ≤ x / 3 := by
  unfold S at hd
  rw [Finset.mem_erase, Finset.mem_erase, mem_divisors] at hd
  have h_dvd := hd.2.2.1
  have h_lt : d < x := by
    have h_le := divisor_le (by rw [mem_divisors]; exact ⟨h_dvd, hd.2.2.2⟩)
    omega
  rcases eq_or_ne d 0 with rfl | hd_ne
  · omega
  · have h_div : x / d ≥ 3 := by
      by_contra! h_lt_3
      interval_cases h_div : x / d
      · have h_eq : x = 0 := by
          rw [← Nat.div_mul_cancel h_dvd, h_div, zero_mul]
        omega
      · have h_eq : d = x := by
          rw [← Nat.div_mul_cancel h_dvd, h_div, one_mul]
        omega
      · have h_eq : d = x / 2 := by
          have h_mul := Nat.div_mul_cancel h_dvd
          rw [h_div] at h_mul
          omega
        omega
    have h_mul_le : 3 * d ≤ x := by
      calc
        3 * d ≤ (x / d) * d := Nat.mul_le_mul_right d h_div
        _ = x := Nat.div_mul_cancel h_dvd
    omega

lemma sum_S_le_of_not_mem (x : ℕ) (h_not_mem : x / 2 ∉ S x) : ∑ d ∈ S x, d ≤ (S x).card * (x / 3) := by
  have h1 : ∑ d ∈ S x, d ≤ ∑ d ∈ S x, x / 3 := by
    apply Finset.sum_le_sum
    intro d hd
    have h_ne : d ≠ x / 2 := by
      intro hc
      exact h_not_mem (hc ▸ hd)
    exact mem_S_le_div_three_of_ne x d hd h_ne
  rw [Finset.sum_const] at h1
  exact h1

lemma sum_S_le_of_mem (x : ℕ) (h_mem : x / 2 ∈ S x) : ∑ d ∈ S x, d ≤ x / 2 + ((S x).card - 1) * (x / 3) := by
  have h_erase : ∑ d ∈ S x, d = x / 2 + ∑ d ∈ (S x).erase (x / 2), d := by
    rw [← Finset.add_sum_erase (S x) (fun d => d) h_mem]
  have h_sum_le : ∑ d ∈ (S x).erase (x / 2), d ≤ ∑ d ∈ (S x).erase (x / 2), x / 3 := by
    apply Finset.sum_le_sum
    intro d hd
    rw [Finset.mem_erase] at hd
    exact mem_S_le_div_three_of_ne x d hd.2 hd.1
  rw [Finset.sum_const] at h_sum_le
  simp only [nsmul_eq_mul, Nat.cast_id] at h_sum_le
  rw [Finset.card_erase_of_mem h_mem] at h_sum_le
  omega

lemma sum_S_eq_four' (x : ℕ) (h : x ≥ 5) (k : ℕ) (h_sig : sigma 1 x = k * x + 5) (hk : k ≥ 1) : ∑ d ∈ S x, d = (k - 1) * x + 4 := by
  have h_decomp := divisors_decomp x h
  rw [sigma_one_apply] at h_sig
  rw [h_decomp] at h_sig
  have h_mul : (k - 1) * x = k * x - x := by
    rw [Nat.sub_mul, one_mul]
  have h_le : x ≤ k * x := by
    calc
      x = 1 * x := by ring
      _ ≤ k * x := Nat.mul_le_mul_right x hk
  rw [h_mul]
  omega

lemma card_S_ge_three (x : ℕ) (hx : x ≥ 1200) (h_mod : sigma 1 x % x = 5) (h_ab : sigma 1 x ≥ 2 * x) : (S x).card ≥ 3 := by
  have hk_ge := k_ge_two x hx h_mod h_ab
  generalize hk : sigma 1 x / x = k at hk_ge ⊢
  have hx_ge : x ≥ 5 := by omega
  have h_sig : sigma 1 x = k * x + 5 := by
    have h1 : sigma 1 x = x * (sigma 1 x / x) + (sigma 1 x) % x := (Nat.div_add_mod (sigma 1 x) x).symm
    rw [h_mod, hk] at h1
    rw [mul_comm] at h1
    exact h1
  have h_sum := sum_S_eq_four' x hx_ge k h_sig (by omega)
  by_cases h_mem : x / 2 ∈ S x
  · have h_le := sum_S_le_of_mem x h_mem
    rw [h_sum] at h_le
    by_contra! h_lt
    have h_le_2 : (S x).card ≤ 2 := by omega
    have h_le_3 : (S x).card - 1 ≤ 1 := by omega
    have h_calc : (k - 1) * x + 4 ≤ x / 2 + 1 * (x / 3) := by
      calc
        (k - 1) * x + 4 ≤ x / 2 + ((S x).card - 1) * (x / 3) := h_le
        _ ≤ x / 2 + 1 * (x / 3) := by gcongr
    have h_k_le : (k - 1) * x + 4 ≥ x + 4 := by
      have : k - 1 ≥ 1 := by omega
      nlinarith
    omega
  · have h_le := sum_S_le_of_not_mem x h_mem
    rw [h_sum] at h_le
    by_contra! h_lt
    have h_le_2 : (S x).card ≤ 2 := by omega
    have h_calc : (k - 1) * x + 4 ≤ 2 * (x / 3) := by
      calc
        (k - 1) * x + 4 ≤ (S x).card * (x / 3) := h_le
        _ ≤ 2 * (x / 3) := by gcongr
    have h_k_le : (k - 1) * x + 4 ≥ x + 4 := by
      have : k - 1 ≥ 1 := by omega
      nlinarith
    omega


lemma sum_div_S_eq_sum_S (x : ℕ) (hx : x ≥ 5) : ∑ d ∈ S x, x / d = ∑ d ∈ S x, d := by
  have hx_ne : x ≠ 0 := by omega
  have h_sum := sum_div_divisors x (fun d => d)
  have h_decomp_lhs : ∑ d ∈ divisors x, x / d = x + 1 + ∑ d ∈ S x, x / d := by
    have h1 : 1 ∈ divisors x := by rw [mem_divisors]; exact ⟨one_dvd x, hx_ne⟩
    have hx_mem : x ∈ divisors x := by rw [mem_divisors]; exact ⟨dvd_rfl, hx_ne⟩
    have h_ne : 1 ≠ x := by omega
    have hx_erase : x ∈ (divisors x).erase 1 := by rw [Finset.mem_erase]; exact ⟨h_ne.symm, hx_mem⟩
    rw [← Finset.add_sum_erase (divisors x) (fun d => x / d) h1]
    rw [← Finset.add_sum_erase ((divisors x).erase 1) (fun d => x / d) hx_erase]
    have h_div_1 : x / 1 = x := Nat.div_one x
    have h_div_x : x / x = 1 := Nat.div_self hx_ne.bot_lt
    rw [h_div_1, h_div_x]
    unfold S
    ring
  have h_decomp_rhs : ∑ d ∈ divisors x, d = x + 1 + ∑ d ∈ S x, d := by
    have h_decomp := divisors_decomp x hx
    omega
  rw [h_decomp_lhs, h_decomp_rhs] at h_sum
  omega

lemma mem_S_two_of_mem_div_two (x : ℕ) (hx : x ≥ 1200) (h_mem : x / 2 ∈ S x) : 2 ∈ S x := by
  have h_mem' := h_mem
  unfold S at h_mem
  rw [Finset.mem_erase, Finset.mem_erase, mem_divisors] at h_mem
  have h_dvd := h_mem.2.2.1
  have hx_ne : x ≠ 0 := h_mem.2.2.2
  have h_even : 2 ∣ x := by
    have h_div_mul : (x / 2) * (x / (x / 2)) = x := Nat.div_mul_cancel h_dvd
    have h_div_div : x / (x / 2) ≥ 2 := by
      by_contra! h_lt_2
      interval_cases h_div : x / (x / 2)
      · rw [h_div, mul_zero] at h_div_mul
        omega
      · rw [h_div, mul_one] at h_div_mul
        have h_S_ne := h_mem'.1
        omega
    have h_even_eq : x = 2 * (x / 2) := by
      have : x / (x / 2) = 2 := by
        have h_mod := Nat.div_add_mod x 2
        omega
      rw [← h_div_mul, this]
      ring
    use x / 2
    rw [mul_comm, h_even_eq]
  unfold S
  rw [Finset.mem_erase, Finset.mem_erase, mem_divisors]
  refine ⟨?_, ?_, h_even, hx_ne⟩
  · omega
  · decide



lemma mem_S_le_div_two (x : ℕ) (d : ℕ) (hd : d ∈ S x) : d ≤ x / 2 := by
  unfold S at hd
  rw [Finset.mem_erase, Finset.mem_erase, mem_divisors] at hd
  have h_dvd := hd.2.2.1
  have h_ne := hd.2.1
  have h_lt : d < x := by
    have h_le := divisor_le (by rw [mem_divisors]; exact ⟨h_dvd, hd.2.2.2⟩)
    omega
  exact divisor_le_div_two x d h_dvd h_lt

lemma helper_ineq (u v : ℕ) (hu : u ≥ 3) (hv : v ≥ 3) : u * v + 4 ≥ 2 * u + 2 * v + 1 := by
  nlinarith

lemma helper_S_ineq (x : ℕ) (d : ℕ) (hd : d ∈ S x) (hd2 : d ≠ 2) (hdx2 : d ≠ x / 2) :
    x + 4 ≥ 2 * d + 2 * (x / d) + 1 := by
  have hu : d ≥ 3 := by
    unfold S at hd
    rw [Finset.mem_erase, Finset.mem_erase, mem_divisors] at hd
    omega
  have hv : x / d ≥ 3 := by
    by_contra! h_lt
    interval_cases h_div : x / d
    · unfold S at hd
      rw [Finset.mem_erase, Finset.mem_erase, mem_divisors] at hd
      have hx_ne := hd.2.2.2
      have h_dvd := hd.2.2.1
      have : x = 0 := by
        rw [← Nat.div_mul_cancel h_dvd, h_div, zero_mul]
      omega
    · unfold S at hd
      rw [Finset.mem_erase, Finset.mem_erase, mem_divisors] at hd
      have h_dvd := hd.2.2.1
      have : d = x := by
        rw [← Nat.div_mul_cancel h_dvd, h_div, one_mul]
      have : d ≠ x := hd.2.1
      contradiction
    · have h_dvd : d ∣ x := by
        unfold S at hd
        rw [Finset.mem_erase, Finset.mem_erase, mem_divisors] at hd
        exact hd.2.2.1
      have : d = x / 2 := by
        have h_mul := Nat.div_mul_cancel h_dvd
        rw [h_div] at h_mul
        omega
      contradiction
  have h_dvd : d ∣ x := by
    unfold S at hd
    rw [Finset.mem_erase, Finset.mem_erase, mem_divisors] at hd
    exact hd.2.2.1
  have h_mul : d * (x / d) = x := Nat.mul_div_cancel' h_dvd
  have h_ineq := helper_ineq d (x / d) hu hv
  rw [h_mul] at h_ineq
  exact h_ineq

lemma S_card_four_contradiction (x : ℕ) (hx : x ≥ 1200) (h_mem : x / 2 ∈ S x) (h_sum : ∑ d ∈ S x, d = x + 4) (h_card : (S x).card = 4) : False := by
  have h_two := mem_S_two_of_mem_div_two x hx h_mem
  have h_ne : 2 ≠ x / 2 := by omega
  let R := ((S x).erase (x / 2)).erase 2
  have h_card_R : R.card = 2 := by
    unfold R
    rw [Finset.card_erase_of_mem, Finset.card_erase_of_mem h_mem]
    · omega
    · rw [Finset.mem_erase]
      exact ⟨h_ne.symm, h_two⟩
  have h_sum_S : ∑ d ∈ S x, d = x / 2 + 2 + ∑ d ∈ R, d := by
    rw [← Finset.add_sum_erase (S x) (fun d => d) h_mem]
    have h_two' : 2 ∈ (S x).erase (x / 2) := by
      rw [Finset.mem_erase]
      exact ⟨h_ne.symm, h_two⟩
    rw [← Finset.add_sum_erase ((S x).erase (x / 2)) (fun d => d) h_two']
    ring
  have h_sum_div_S : ∑ d ∈ S x, x / d = 2 + x / 2 + ∑ d ∈ R, x / d := by
    have h_mem' : x / 2 ∈ S x := h_mem
    rw [← Finset.add_sum_erase (S x) (fun d => x / d) h_mem']
    have h_two' : 2 ∈ (S x).erase (x / 2) := by
      rw [Finset.mem_erase]
      exact ⟨h_ne.symm, h_two⟩
    rw [← Finset.add_sum_erase ((S x).erase (x / 2)) (fun d => x / d) h_two']
    have h_div_half : x / (x / 2) = 2 := by
      have h_even : 2 ∣ x := by
        unfold S at h_mem
        rw [Finset.mem_erase, Finset.mem_erase, mem_divisors] at h_mem
        have h_dvd := h_mem.2.2.1
        have h_div_mul := Nat.div_mul_cancel h_dvd
        have : x / (x / 2) ≥ 2 := by
          by_contra! h_lt_2
          interval_cases h_div : x / (x / 2)
          · rw [h_div, mul_zero] at h_div_mul; omega
          · rw [h_div, mul_one] at h_div_mul; omega
        have : x / (x / 2) = 2 := by
          have h_mod := Nat.div_add_mod x 2
          omega
        exact this
      rw [h_even]
      exact Nat.div_mul_cancel h_even ▸ rfl
    have h_div_two : x / 2 = x / 2 := rfl
    rw [h_div_half, h_div_two]
    ring
  have h_sum_div_eq : ∑ d ∈ S x, x / d = ∑ d ∈ S x, d := sum_div_S_eq_sum_S x (by omega)
  have h_sum_R_eq : ∑ d ∈ R, d + ∑ d ∈ R, x / d = x + 4 := by
    have h_even : 2 ∣ x := by
      unfold S at h_mem
      rw [Finset.mem_erase, Finset.mem_erase, mem_divisors] at h_mem
      have h_dvd := h_mem.2.2.1
      have h_div_mul := Nat.div_mul_cancel h_dvd
      have : x / (x / 2) ≥ 2 := by
        by_contra! h_lt_2
        interval_cases h_div : x / (x / 2)
        · rw [h_div, mul_zero] at h_div_mul; omega
        · rw [h_div, mul_one] at h_div_mul; omega
      have : x / (x / 2) = 2 := by
        have h_mod := Nat.div_add_mod x 2
        omega
      exact this
    have h_x : 2 * (x / 2) = x := Nat.mul_div_cancel' h_even
    rw [h_sum] at h_sum_S h_sum_div_eq
    rw [h_sum_div_S] at h_sum_div_eq
    omega
  have h_sum_ineq : ∑ d ∈ R, (x + 4) ≥ ∑ d ∈ R, (2 * d + 2 * (x / d) + 1) := by
    apply Finset.sum_le_sum
    intro d hd
    rw [Finset.mem_erase, Finset.mem_erase] at hd
    exact helper_S_ineq x d hd.2.2 hd.1 hd.2.1
  rw [Finset.sum_const, Finset.sum_add_distrib, Finset.sum_add_distrib] at h_sum_ineq
  simp only [nsmul_eq_mul, Nat.cast_id, ← Finset.mul_sum] at h_sum_ineq
  rw [h_card_R] at h_sum_ineq
  simp only [Finset.sum_const, card_erase_of_mem, h_mem, nsmul_eq_mul, Nat.cast_id, h_card_R] at h_sum_ineq
  omega

lemma card_S_ge_five (x : ℕ) (hx : x ≥ 1200) (h_mod : sigma 1 x % x = 5) (h_ab : sigma 1 x ≥ 2 * x) : (S x).card ≥ 5 := by
  have h_card_ge_4 := card_S_ge_four x hx h_mod h_ab
  rcases eq_or_ne (S x).card 4 with h4 | h_ne_4
  · have hk_ge := k_ge_two x hx h_mod h_ab
    generalize hk : sigma 1 x / x = k at hk_ge ⊢
    have hx_ge : x ≥ 5 := by omega
    have h_sig : sigma 1 x = k * x + 5 := by
      have h1 : sigma 1 x = x * (sigma 1 x / x) + (sigma 1 x) % x := (Nat.div_add_mod (sigma 1 x) x).symm
      rw [h_mod, hk] at h1
      rw [mul_comm] at h1
      exact h1
    have h_sum := sum_S_eq_four' x hx_ge k h_sig (by omega)
    by_cases h_mem : x / 2 ∈ S x
    · by_cases hk3 : k ≥ 3
      · have h_two := mem_S_two_of_mem_div_two x hx h_mem
        have h_le := sum_S_le_of_mem_two x h_mem h_two hx
        rw [h_sum, h4] at h_le
        have h_le_2 : (S x).card - 2 ≤ 2 := by omega
        have h_calc : (k - 1) * x + 4 ≤ x / 2 + 2 + 2 * (x / 3) := by
          calc
            (k - 1) * x + 4 ≤ x / 2 + 2 + ((S x).card - 2) * (x / 3) := h_le
            _ ≤ x / 2 + 2 + 2 * (x / 3) := by gcongr
        have h_k_le : (k - 1) * x + 4 ≥ 2 * x + 4 := by
          have : k - 1 ≥ 2 := by omega
          nlinarith
        omega
      · have hk2_eq : k = 2 := by omega
        rw [hk2_eq] at h_sum
        simp only [one_mul] at h_sum
        exfalso
        exact S_card_four_contradiction x hx h_mem h_sum h4
    · have h_le := sum_S_le_of_not_mem x h_mem
      rw [h_sum, h4] at h_le
      have h_calc : (k - 1) * x + 4 ≤ 4 * (x / 3) := by
        calc
          (k - 1) * x + 4 ≤ (S x).card * (x / 3) := h_le
          _ ≤ 4 * (x / 3) := by gcongr
      have h_k_le : (k - 1) * x + 4 ≥ x + 4 := by
        have : k - 1 ≥ 1 := by omega
        nlinarith
      omega
  · omega




