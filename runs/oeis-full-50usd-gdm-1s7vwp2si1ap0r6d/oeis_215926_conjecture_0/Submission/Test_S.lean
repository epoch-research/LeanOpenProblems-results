import FormalConjectures.Util.ProblemImports

attribute [local instance] Classical.propDecidable

open Nat Finset

noncomputable def a (n : ℕ) : ℕ :=
  let sigma1 (m : ℕ) : ℕ := m.divisors.sum id
  sInf {k : ℕ | sigma1 k < 2 * k ∧ 2 * (k * n) ≤ sigma1 (k * n)}

def S (n : ℕ) : Set ℕ :=
  {k : ℕ | k.divisors.sum id < 2 * k ∧ 2 * (k * n) ≤ (k * n).divisors.sum id}

theorem a_eq_S (n : ℕ) : a n = sInf (S n) := rfl

theorem sigma1_eq_sigma (m : ℕ) : m.divisors.sum id = ArithmeticFunction.sigma 1 m := by
  rw [ArithmeticFunction.sigma_one_apply]
  rfl

theorem coprime_pow_two_odd (a m : ℕ) (hm : m % 2 = 1) : Nat.Coprime (2 ^ a) m := by
  apply Nat.Coprime.pow_left
  rw [Nat.coprime_iff_gcd_eq_one]
  have h_dvd : Nat.gcd 2 m ∣ 2 := Nat.gcd_dvd_left 2 m
  have : Nat.gcd 2 m = 1 ∨ Nat.gcd 2 m = 2 := by
    have h_pos : Nat.gcd 2 m > 0 := Nat.gcd_pos_of_pos_left m (by decide)
    have h_le : Nat.gcd 2 m ≤ 2 := Nat.le_of_dvd (by decide) h_dvd
    omega
  rcases this with h1 | h2
  · exact h1
  · have hd := Nat.gcd_dvd_right 2 m
    rw [h2] at hd
    have h_mod : m % 2 = 0 := Nat.mod_eq_zero_of_dvd hd
    omega

theorem ord_two_and_odd (k : ℕ) (hk : k ≠ 0) : ∃ a m, k = 2^a * m ∧ m % 2 = 1 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases h_even : 2 ∣ k
    · rcases h_even with ⟨m, rfl⟩
      have hm_pos : m ≠ 0 := by omega
      have hm_lt : m < 2 * m := by omega
      rcases ih m hm_lt hm_pos with ⟨a, m', rfl, h_odd⟩
      use a + 1, m'
      constructor
      · ring
      · exact h_odd
    · use 0, k
      constructor
      · simp
      · rcases Nat.mod_two_eq_zero_or_one k with h_zero | h_one
        · have : 2 ∣ k := dvd_of_mod_eq_zero h_zero
          contradiction
        · exact h_one

theorem test_submult (a b : ℕ) (d : ℕ) (hd : d ∣ a * b) : ∃ d1 d2, d1 ∣ a ∧ d2 ∣ b ∧ d = d1 * d2 := by
  exact exists_dvd_and_dvd_of_dvd_mul hd

theorem divisors_mul_subset (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).divisors ⊆ (a.divisors ×ˢ b.divisors).image (fun p => p.1 * p.2) := by
  intro d hd
  rw [mem_divisors] at hd
  obtain ⟨d1, d2, hd1, hd2, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hd.1
  rw [mem_image]
  use (d1, d2)
  constructor
  · rw [mem_product, mem_divisors, mem_divisors]
    exact ⟨⟨hd1, ha⟩, hd2, hb⟩
  · rfl

theorem sum_image_le {α β : Type*} [DecidableEq α] [DecidableEq β] (s : Finset α) (f : β → ℕ) (g : α → β) :
    (s.image g).sum (fun y => f y) ≤ s.sum (fun x => f (g x)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [sum_insert hx]
    by_cases h_mem : g x ∈ s.image g
    · have h_eq : (insert x s).image g = s.image g := by
        ext y
        constructor
        · intro hy
          rw [mem_image] at hy
          rcases hy with ⟨a, ha, rfl⟩
          rw [mem_insert] at ha
          rcases ha with rfl | ha
          · exact h_mem
          · rw [mem_image]
            exact ⟨a, ha, rfl⟩
        · intro hy
          rw [mem_image] at hy
          rcases hy with ⟨a, ha, rfl⟩
          rw [mem_image]
          use a
          rw [mem_insert]
          exact ⟨Or.inr ha, rfl⟩
      rw [h_eq]
      omega
    · have h_eq : (insert x s).image g = insert (g x) (s.image g) := image_insert g x s
      rw [h_eq, sum_insert h_mem]
      omega

theorem divisors_sum_mul_le (a b : ℕ) :
    (a * b).divisors.sum id ≤ a.divisors.sum id * b.divisors.sum id := by
  by_cases ha : a = 0
  · subst ha
    simp
  · by_cases hb : b = 0
    · subst hb
      simp
    · have h_sub := divisors_mul_subset a b ha hb
      have h_le : (a * b).divisors.sum id ≤ ((a.divisors ×ˢ b.divisors).image (fun p => p.1 * p.2)).sum id := sum_le_sum_of_subset h_sub
      have h_img := sum_image_le (a.divisors ×ˢ b.divisors) id (fun p => p.1 * p.2)
      simp only [id_eq] at h_img ⊢
      have h_trans : (a * b).divisors.sum id ≤ (a.divisors ×ˢ b.divisors).sum (fun p => p.1 * p.2) := le_trans h_le h_img
      rw [sum_product] at h_trans
      have h_eq : (∑ x ∈ a.divisors, ∑ y ∈ b.divisors, x * y) = a.divisors.sum id * b.divisors.sum id := by
        rw [← sum_mul_sum]
        rfl
      rw [h_eq] at h_trans
      exact h_trans

theorem divisors_sum_ge_two_divisors (n a b : ℕ) (ha : a ∈ n.divisors) (hb : b ∈ n.divisors) (hab : a ≠ b) : a + b ≤ n.divisors.sum id := by
  have h_subset : {a, b} ⊆ n.divisors := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  have hne : a ∉ ({b} : Finset ℕ) := by
    simp only [mem_singleton]
    exact hab
  have h_sum : ({a, b} : Finset ℕ).sum id = a + b := by
    rw [sum_insert hne, sum_singleton, id_eq, id_eq]
  rw [← h_sum]
  apply sum_le_sum_of_subset h_subset

theorem divisors_sum_ge_n_plus_one (n : ℕ) (hn2 : 2 ≤ n) : n + 1 ≤ n.divisors.sum id := by
  have h_pos : n > 0 := by omega
  have h1 : 1 ∈ n.divisors := by
    rw [mem_divisors]
    exact ⟨one_dvd n, Nat.ne_of_gt h_pos⟩
  have hn : n ∈ n.divisors := by
    rw [mem_divisors]
    exact ⟨dvd_rfl, Nat.ne_of_gt h_pos⟩
  have hne : 1 ≠ n := by omega
  have h_ge := divisors_sum_ge_two_divisors n 1 n h1 hn hne
  omega

theorem divisors_sum_two_pow (k : ℕ) : (2 ^ k).divisors.sum id = 2 ^ (k + 1) - 1 := by
  have h_prime : Nat.Prime 2 := Nat.prime_two
  rw [sigma1_eq_sigma]
  have h_pow := ArithmeticFunction.sigma_apply_prime_pow (k := 1) (i := k) h_prime
  simp only [mul_one] at h_pow
  rw [h_pow]
  have h_geom := geomSum_eq (m := 2) (by decide) (k + 1)
  rw [h_geom]
  rw [Nat.div_one]

theorem S_le_two_pow (n : ℕ) (hn : 2 ≤ n) (h_non_def : ¬2 * n ≤ n.divisors.sum id) (hn_even : ¬2 ∣ n) (h_two_pow : ∃ x, 2^x ∈ S n) (k : ℕ) (hk : k ∈ S n) :
    2 ^ (Nat.find h_two_pow) ≤ k := by
  let s := Nat.find h_two_pow
  by_cases hk_pow : ∃ j, k = 2 ^ j
  · rcases hk_pow with ⟨j, rfl⟩
    have hs_min : ∀ i < Nat.find h_two_pow, 2^i ∉ S n := Nat.find_min h_two_pow
    by_contra h_lt
    dsimp [s] at *
    have h_lt' : j < Nat.find h_two_pow := by
      have h_pos : 2 > 1 := by decide
      exact (Nat.pow_lt_pow_iff_right h_pos).mp h_lt
    have := hs_min j h_lt'
    contradiction
  · by_contra h_lt
    have hk_pos : k ≠ 0 := by
      intro h_zero
      subst h_zero
      unfold S at hk
      simp at hk
    rcases ord_two_and_odd k hk_pos with ⟨a, m, rfl, hm_odd⟩
    have hm_ne_one : m ≠ 1 := by
      intro h_one
      subst h_one
      simp only [mul_one] at hk_pow
      exact hk_pow ⟨a, rfl⟩
    have hm_ge_three : m ≥ 3 := by
      rcases Nat.mod_two_eq_zero_or_one m with h_zero | h_one
      · omega
      · omega
    have ha_lt : a + 2 ≤ s := by
      have h_pow : 2^(a+1) < 2^s := by
        have h_pow_succ : 2^(a+1) = 2^a * 2 := by rw [pow_succ]
        rw [h_pow_succ]
        have h_trans : 2^a * 2 < 2^a * m := by
          have h_m : 2 < m := by omega
          exact Nat.mul_lt_mul_of_pos_left h_m (pow_pos (by decide) a)
        -- dsimp s here to make h_lt match
        have h_lt_eq : 2^a * m < 2^s := by
          dsimp [s] at h_lt ⊢
          omega
        exact lt_trans h_trans h_lt_eq
      have h_pos : 2 > 1 := by decide
      have h_lt_final := (Nat.pow_lt_pow_iff_right h_pos).mp h_pow
      dsimp [s] at *
      omega
    have h_s_ge_one : s ≥ 1 := by
      dsimp [s] at *
      omega
    have hs_min : ∀ i < Nat.find h_two_pow, 2^i ∉ S n := Nat.find_min h_two_pow
    have h_s_sub_one_not : 2^(s-1) ∉ S n := by
      dsimp [s] at *
      exact hs_min (Nat.find h_two_pow - 1) (by omega)
    have hn_odd : n % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one n with h_zero | h_one
      · have : 2 ∣ n := dvd_of_mod_eq_zero h_zero
        contradiction
      · exact h_one
    have h_cop_s : Nat.Coprime (2 ^ (s - 1)) n := coprime_pow_two_odd (s - 1) n hn_odd
    have h_mult_s : (2^(s-1) * n).divisors.sum id = (2^(s-1)).divisors.sum id * n.divisors.sum id := by
      rw [sigma1_eq_sigma, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h_cop_s, ← sigma1_eq_sigma, ← sigma1_eq_sigma]
    have h_s_not_S : 2 * (2^(s-1) * n) > (2^(s-1) * n).divisors.sum id := by
      by_contra hc
      have hc_le : 2 * (2^(s-1) * n) ≤ (2^(s-1) * n).divisors.sum id := by
        dsimp [s] at hc ⊢
        omega
      have h_S_mem : 2^(s-1) ∈ S n := by
        unfold S
        simp only [Set.mem_setOf_eq]
        constructor
        · rw [divisors_sum_two_pow]
          have h_eq_pow : 2 * 2 ^ (s - 1) = 2 ^ s := by
            dsimp [s] at *
            omega
          rw [h_eq_pow]
          omega
        · exact hc_le
      exact h_s_sub_one_not h_S_mem
    rw [h_mult_s, divisors_sum_two_pow] at h_s_not_S
    have h_eq_pow2 : 2 * (2 ^ (s - 1) * n) = 2^s * n := by
      dsimp [s] at *
      omega
    rw [h_eq_pow2] at h_s_not_S
    have h_calc : 2^s * n > 2^s * n.divisors.sum id - n.divisors.sum id := by
      have h_ring : (2^s - 1) * n.divisors.sum id = 2^s * n.divisors.sum id - n.divisors.sum id := by
        have h_pos : 2^s > 0 := pow_pos (by decide) s
        rw [Nat.sub_mul, one_mul]
      dsimp [s] at *
      omega
    have h_diff : n.divisors.sum id > 2^s * (n.divisors.sum id - n) := by
      dsimp [s] at *
      omega

    unfold S at hk
    simp only [Set.mem_setOf_eq] at hk
    have hk_sum := hk.1
    have hk_sum_n := hk.2
    have h_cop : Nat.Coprime (2 ^ a) m := coprime_pow_two_odd a m hm_odd
    have h_mult : (2 ^ a * m).divisors.sum id = (2 ^ a).divisors.sum id * m.divisors.sum id := by
      rw [sigma1_eq_sigma, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h_cop, ← sigma1_eq_sigma, ← sigma1_eq_sigma]
    rw [h_mult, divisors_sum_two_pow] at hk_sum
    have h_mult2 : (2^a * m * n).divisors.sum id ≤ (2^a * m).divisors.sum id * n.divisors.sum id := divisors_sum_mul_le (2^a * m) n
    have hk_sum_n_le : 2 * (2^a * m * n) ≤ (2^(a+1) - 1) * m.divisors.sum id * n.divisors.sum id := by
      rw [h_mult, divisors_sum_two_pow] at h_mult2
      omega
    have hk_sum_n_le2 : 2^(a+1) * m * n ≤ (2^(a+1) - 1) * m.divisors.sum id * n.divisors.sum id := by
      have h_ring : 2 * (2 ^ a * m) * n = 2 ^ (a + 1) * m * n := by omega
      omega
    have h_D : 2^(a+1) * m - (2^(a+1) - 1) * m.divisors.sum id ≥ 1 := by
      have h_pos : 2^(a+1) > 0 := pow_pos (by decide) (a + 1)
      have h_ge : m + 1 ≤ m.divisors.sum id := divisors_sum_ge_n_plus_one m (by omega)
      have h_calc2 : (2^(a+1) - 1) * m.divisors.sum id ≤ 2^(a+1) * m - 1 := by
        omega
      omega
    let D := 2^(a+1) * m - (2^(a+1) - 1) * m.divisors.sum id
    have h_D_eq : 2^(a+1) * m - (2^(a+1) - 1) * m.divisors.sum id = D := rfl
    have h_D_ge_one : D ≥ 1 := h_D
    have h_D_calc : D * n.divisors.sum id ≤ 2^(a+1) * m * (n.divisors.sum id - n) := by
      have h_eq_D : (2^(a+1) - 1) * m.divisors.sum id = 2^(a+1) * m - D := by omega
      have h_step3 : 2^(a+1) * m * n ≤ (2^(a+1) * m - D) * n.divisors.sum id := by
        rw [← h_eq_D]
        exact hk_sum_n_le2
      have h_step4 : (2^(a+1) * m - D) * n.divisors.sum id = 2^(a+1) * m * n.divisors.sum id - D * n.divisors.sum id := by
        rw [Nat.sub_mul]
      omega
    have h_trans_final : D * (2^s * (n.divisors.sum id - n)) < D * n.divisors.sum id := by
      have h_step5 : 2^s * (n.divisors.sum id - n) < n.divisors.sum id := h_diff
      have h_step6 := Nat.mul_lt_mul_of_pos_left h_step5 h_D_ge_one
      rw [mul_assoc] at h_step6
      dsimp [s] at *
      exact h_step6
    have h_final_bound : D * 2^s < 2^(a+1) * m := by
      have h_sum_ge : 2 ≤ n := hn
      have h_ge2 := divisors_sum_ge_n_plus_one n h_sum_ge
      have h_diff_pos : n.divisors.sum id - n ≥ 1 := by omega
      have h_step7 : D * (2^s * (n.divisors.sum id - n)) < 2^(a+1) * m * (n.divisors.sum id - n) := lt_of_lt_of_le h_trans_final h_D_calc
      dsimp [s] at *
      exact Nat.lt_of_mul_lt_mul_right h_step7
    have h_final_bound2 : D * 2^(s - a - 1) < m := by
      have h_pow_eq_s : 2^s = 2^(a+1) * 2^(s - a - 1) := by
        rw [← pow_add]
        congr 1
        dsimp [s] at *
        omega
      rw [h_pow_eq_s] at h_final_bound
      have h_ring : D * (2^(a+1) * 2^(s - a - 1)) = 2^(a+1) * (D * 2^(s - a - 1)) := by ring
      rw [h_ring] at h_final_bound
      have h_pow_pos : 2^(a+1) > 0 := pow_pos (by decide) (a + 1)
      exact Nat.lt_of_mul_lt_mul_left h_final_bound
    let L := 2^(s - a - 1)
    have h_L : 2^(s - a - 1) = L := rfl
    have h_L_ge : L ≥ 2 := by
      have : s - a - 1 ≥ 1 := by
        dsimp [s] at *
        omega
      have h_pow_le : 2^1 ≤ 2^(s - a - 1) := Nat.pow_le_pow_right (by decide) this
      omega
    have h_DL : D * L < m := h_final_bound2
    have h_L_lt_m : L < m := by
      dsimp [L] at *
      omega
    have h_D_le_val : D ≤ m + 1 - 2^(a+1) := by
      have h_ge : m + 1 ≤ m.divisors.sum id := divisors_sum_ge_n_plus_one m (by omega)
      have h_step8 : (2^(a+1) - 1) * (m + 1) ≤ (2^(a+1) - 1) * m.divisors.sum id := Nat.mul_le_mul_left (2^(a+1) - 1) h_ge
      have h_ring2 : (2^(a+1) - 1) * (m + 1) = 2^(a+1) * m + 2^(a+1) - m - 1 := by
        have h_pos : 2^(a+1) > 0 := pow_pos (by decide) (a + 1)
        rw [Nat.sub_mul, one_mul, mul_add, mul_one]
        omega
      omega

    by_cases h_cases : s - a - 1 ≥ a + 1
    · have h_L_ge2 : L ≥ 2^(a+1) := by
        dsimp [L] at *
        exact Nat.pow_le_pow_right (by decide) h_cases
      have h_L_sub_ge : L - 1 ≥ 2^(a+1) - 1 := by
        dsimp [L] at *
        omega
      by_cases h_D_ge_two : D ≥ 2
      · have h_DL_ge : D * L ≥ 2 * L := Nat.mul_le_mul_right L h_D_ge_two
        have h_m_lt : m < 2 * L := by
          have h_pow_eq_s2 : 2^s = 2^a * (2 * 2^(s - a - 1)) := by
            rw [← mul_assoc, ← pow_succ]
            rw [← pow_add]
            congr 1
            dsimp [s] at *
            omega
          dsimp [L]
          omega
        omega
      · have h_D_one : D = 1 := by omega
        have h_step9 : L * (m + 1 - 2^(a+1)) < m := by
          have h_step10 : D * L ≤ (m + 1 - 2^(a+1)) * L := Nat.mul_le_mul_right L h_D_le_val
          rw [mul_comm] at h_step10
          omega
        have h_step11 : L * (m + 1 - 2^(a+1)) = L * m + L - L * 2^(a+1) := by
          rw [Nat.mul_sub_left_distrib, mul_add, mul_one]
        rw [h_step11] at h_step9
        have h_step12 : (L - 1) * m < L * (2^(a+1) - 1) := by
          have h_ring3 : (L - 1) * m = L * m - m := by
            rw [Nat.sub_mul, one_mul]
          have h_ring4 : L * (2^(a+1) - 1) = L * 2^(a+1) - L := by
            rw [Nat.mul_sub_left_distrib, mul_one]
          omega
        have h_step13 : L * (2^(a+1) - 1) ≤ (L - 1) * L := by
          have h_tmp := Nat.mul_le_mul_left L h_L_sub_ge
          rw [mul_comm L (L - 1)] at h_tmp
          exact h_tmp
        have h_step14 : (L - 1) * m < (L - 1) * L := lt_of_lt_of_le h_step12 h_step13
        have h_L_sub_pos : L - 1 > 0 := by
          dsimp [L] at *
          omega
        have h_step15 : m < L := Nat.lt_of_mul_lt_mul_left h_step14
        omega
    · have h_s_le : s ≤ 2 * a + 1 := by
        dsimp [s] at *
        omega
      have h_m_val : m ≥ 2^(a+1) + 1 := by omega
      have h_k_ge : 2^a * m ≥ 2^(2 * a + 1) + 2^a := by
        have h_step16 : 2^a * m ≥ 2^a * (2^(a+1) + 1) := Nat.mul_le_mul_left (2^a) h_m_val
        have h_ring5 : 2^a * (2^(a+1) + 1) = 2^(2 * a + 1) + 2^a := by
          rw [mul_add, mul_one, ← pow_add]
          congr 1
          omega
        omega
      have h_2s_le : 2^s ≤ 2^(2 * a + 1) := by
        dsimp [s] at *
        exact Nat.pow_le_pow_right (by decide) h_s_le
      omega
