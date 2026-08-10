import FormalConjectures.Util.ProblemImports

open Nat

/--
The $d$-th triangular number, $T(d) = d(d+1)/2$.
-/
def T_triangular (d : ℕ) : ℕ := d * (d + 1) / 2

/--
A275786: $a(n) = \prod_{d|n} T(d)$ where $T(x)$ is the $x$-th triangular number.
-/
def a (n : ℕ) : ℕ :=
  (Nat.divisors n).prod T_triangular

lemma T_triangular_one : T_triangular 1 = 1 := rfl

lemma a_one : a 1 = 1 := by
  dsimp [a]
  rw [Nat.divisors_one]
  rfl

lemma T_triangular_pos (d : ℕ) (hd : d > 0) : T_triangular d > 0 := by
  dsimp [T_triangular]
  have h1 : 2 ≤ d * (d + 1) := by
    have hd1 : 1 ≤ d := hd
    have hd2 : 2 ≤ d + 1 := by omega
    nlinarith
  omega

lemma a_pos (n : ℕ) (_hn : n > 0) : a n > 0 := by
  dsimp [a]
  apply Finset.prod_pos
  intro d hd
  rw [Nat.mem_divisors] at hd
  have hd_ne : d ≠ 0 := by
    rintro rfl
    exact hd.2 (zero_dvd_iff.mp hd.1)
  have hd_pos : d > 0 := Nat.pos_of_ne_zero hd_ne
  exact T_triangular_pos d hd_pos

lemma T_dvd_a (n : ℕ) (hn : n > 0) : T_triangular n ∣ a n := by
  have h_mem : n ∈ Nat.divisors n := by
    rw [Nat.mem_divisors]
    refine ⟨dvd_rfl, Nat.ne_of_gt hn⟩
  exact Finset.dvd_prod_of_mem T_triangular h_mem

lemma T_triangular_mul_two (d : ℕ) : T_triangular d * 2 = d * (d + 1) := by
  dsimp [T_triangular]
  have h2 : 2 ∣ d * (d + 1) := even_iff_two_dvd.mp (Nat.even_mul_succ_self d)
  exact Nat.div_mul_cancel h2

lemma prime_factor_le (n : ℕ) (hn : n > 0) (p : ℕ) (hp : p.Prime) (h : p ∣ a n) : p ≤ n + 1 := by
  have hp' : _root_.Prime p := Nat.prime_iff.mp hp
  dsimp [a] at h
  rw [Prime.dvd_finset_prod_iff hp'] at h
  rcases h with ⟨d, hd, hd_dvd⟩
  rw [Nat.mem_divisors] at hd
  have hd_le : d ≤ n := Nat.le_of_dvd hn hd.1
  have hd_dvd' : p ∣ d * (d + 1) := by
    have h_mul : d * (d + 1) = T_triangular d * 2 := (T_triangular_mul_two d).symm
    rw [h_mul]
    exact dvd_mul_of_dvd_left hd_dvd 2
  have hp_dvd_mul : p ∣ d ∨ p ∣ d + 1 := (Nat.Prime.dvd_mul hp).mp hd_dvd'
  rcases hp_dvd_mul with hp_d | hp_d1
  · have hp_le_d : p ≤ d := Nat.le_of_dvd (by
      have hd_ne : d ≠ 0 := by
        rintro rfl
        exact hd.2 (zero_dvd_iff.mp hd.1)
      exact Nat.pos_of_ne_zero hd_ne) hp_d
    omega
  · have hp_le_d1 : p ≤ d + 1 := Nat.le_of_dvd (by omega) hp_d1
    omega

lemma prime_factors_of_T_le (n m : ℕ) (hn : n > 0) (hm : m > 0) (h_eq : a n = a m) (p : ℕ) (hp : p.Prime) (hp_dvd : p ∣ T_triangular m) : p ≤ n + 1 := by
  have hp_a : p ∣ a n := by
    rw [h_eq]
    have h_dvd : T_triangular m ∣ a m := T_dvd_a m hm
    exact dvd_trans hp_dvd h_dvd
  exact prime_factor_le n hn p hp hp_a

lemma a_gt_one_of_gt_one (m : ℕ) (hm : m > 1) : a m > 1 := by
  have hm_pos : m > 0 := by omega
  have h_dvd := T_dvd_a m hm_pos
  have h_am_pos := a_pos m hm_pos
  have h_le := Nat.le_of_dvd h_am_pos h_dvd
  have h_T_gt : T_triangular m > 1 := by
    dsimp [T_triangular]
    have h_mul : m * (m + 1) ≥ 6 := by
      have h_m : 2 ≤ m := hm
      have h_m1 : 3 ≤ m + 1 := by omega
      nlinarith
    have h_div : m * (m + 1) / 2 ≥ 3 := by omega
    omega
  omega

lemma a_ne_one_of_gt_one (m : ℕ) (hm : m > 1) : a m ≠ 1 := by
  have h_gt := a_gt_one_of_gt_one m hm
  omega

lemma a_eq_one_iff (m : ℕ) (hm : m > 0) : a m = 1 ↔ m = 1 := by
  constructor
  · intro h
    by_cases h_gt : m > 1
    · have h_ne := a_ne_one_of_gt_one m h_gt
      contradiction
    · omega
  · rintro rfl
    exact a_one



lemma prime_factor_le_div_two {x : ℕ} (hx : x ≥ 4) (hc : ¬ x.Prime) (p : ℕ) (hp : p.Prime) (h_dvd : p ∣ x) : p ≤ x / 2 := by
  by_cases h_eq : p = x
  · subst h_eq
    contradiction
  · have h_dvd2 : p ∣ x := h_dvd
    have h_le : p ≤ x := Nat.le_of_dvd (by omega) h_dvd2
    have h_ne : p ≠ x := h_eq
    have h_lt : p < x := lt_of_le_of_ne h_le h_ne
    have h_div_gt1 : x / p > 1 := by
      have h_eq3 : x = p * (x / p) := (Nat.mul_div_cancel' h_dvd).symm
      by_cases h_div : x / p ≤ 1
      · generalize h_div_val : x / p = y at h_div h_eq3
        have h_div_eq : y = 1 ∨ y = 0 := by omega
        rcases h_div_eq with h_1 | h_0
        · rw [h_1, Nat.mul_one] at h_eq3
          omega
        · rw [h_0, Nat.mul_zero] at h_eq3
          omega
      · omega
    have h_div_ge2 : x / p ≥ 2 := by omega
    have h_eq4 : x = p * (x / p) := (Nat.mul_div_cancel' h_dvd).symm
    have h_bound : p * 2 ≤ x := by
      calc
        p * 2 ≤ p * (x / p) := Nat.mul_le_mul_left p h_div_ge2
        _ = x := h_eq4.symm
    omega

lemma a_prime (p : ℕ) (hp : p.Prime) : a p = T_triangular p := by
  dsimp [a]
  rw [hp.prod_divisors]
  rw [T_triangular_one]
  rw [mul_one]

lemma case_m_plus_one_prime (n m : ℕ) (hn : n > 0) (hm : m > 0) (h_lt : n < m) (h_eq : a n = a m) (hp : (m + 1).Prime) : False := by
  have h_dvd_T : m + 1 ∣ T_triangular m := by
    have h_mul : T_triangular m * 2 = m * (m + 1) := T_triangular_mul_two m
    have h_dvd : m + 1 ∣ T_triangular m * 2 := by
      rw [h_mul]
      exact dvd_mul_left (m + 1) m
    rcases (Nat.Prime.dvd_mul hp).mp h_dvd with h1 | h2
    · exact h1
    · -- m + 1 ∣ 2
      have h_le : m + 1 ≤ 2 := Nat.le_of_dvd (by decide) h2
      omega
  have h_le := prime_factors_of_T_le n m hn hm h_eq (m + 1) hp h_dvd_T
  omega

lemma case_m_prime (n m : ℕ) (hn : n > 0) (hm : m > 0) (h_lt : n < m) (h_eq : a n = a m) (hp : m.Prime) : False := by
  have h_dvd_T : m ∣ T_triangular m := by
    have h_mul : T_triangular m * 2 = m * (m + 1) := T_triangular_mul_two m
    have h_dvd : m ∣ T_triangular m * 2 := by
      rw [h_mul]
      exact dvd_mul_right m (m + 1)
    rcases (Nat.Prime.dvd_mul hp).mp h_dvd with h1 | h2
    · exact h1
    · -- m ∣ 2
      have h_le : m ≤ 2 := Nat.le_of_dvd (by decide) h2
      have h_m2 : m = 2 := by
        have hp2 : m ≥ 2 := hp.two_le
        omega
      subst h_m2
      have h_n1 : n = 1 := by omega
      subst h_n1
      have ha1 := a_one
      have ha2 : a 2 = 3 := by decide
      omega
  have h_le := prime_factors_of_T_le n m hn hm h_eq m hp h_dvd_T
  have h_eq_nm : m = n + 1 := by omega
  have h_n_eq : n = m - 1 := by omega
  have h_an_eq : a (m - 1) = a m := by rw [← h_n_eq, h_eq]
  have h_am_eq : a m = T_triangular m := a_prime m hp
  have h_an_eq_T : a (m - 1) = T_triangular m := by rw [h_an_eq, h_am_eq]
  have h_m_gt_one : m - 1 > 0 := by omega
  have h_dvd_an := T_dvd_a (m - 1) h_m_gt_one
  rw [h_an_eq_T] at h_dvd_an
  -- T_triangular (m - 1) ∣ T_triangular m
  have h_dvd_mul : T_triangular (m - 1) * 2 ∣ T_triangular m * 2 := mul_dvd_mul_right h_dvd_an 2
  rw [T_triangular_mul_two (m - 1), T_triangular_mul_two m] at h_dvd_mul
  -- (m - 1) * (m - 1 + 1) ∣ m * (m + 1)
  have h_simpl : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
  rw [h_simpl] at h_dvd_mul
  -- (m - 1) * m ∣ m * (m + 1)
  rw [mul_comm (m - 1) m] at h_dvd_mul
  -- m * (m - 1) ∣ m * (m + 1)
  have h_m_ne : m ≠ 0 := Nat.ne_of_gt hm
  rw [mul_dvd_mul_iff_left h_m_ne] at h_dvd_mul
  -- m - 1 ∣ m + 1
  have h_dvd_sub : m - 1 ∣ (m + 1) - (m - 1) := Nat.dvd_sub h_dvd_mul dvd_rfl
  have h_diff : (m + 1) - (m - 1) = 2 := by omega
  rw [h_diff] at h_dvd_sub
  have h_le_2 : m - 1 ≤ 2 := Nat.le_of_dvd (by decide) h_dvd_sub
  have h_m_le_3 : m ≤ 3 := by omega
  have hp2 : m ≥ 2 := hp.two_le
  rcases eq_or_ne m 2 with rfl | hm2
  · have h_n1 : n = 1 := by omega
    subst h_n1
    have ha1 := a_one
    have ha2 : a 2 = 3 := by decide
    omega
  · rcases eq_or_ne m 3 with rfl | hm3
    · have h_n2 : n = 2 := by omega
      subst h_n2
      have ha2 : a 2 = 3 := by decide
      have ha3 : a 3 = 6 := by decide
      omega
    · omega

lemma a_ne_of_has_prime_factor (n m : ℕ) (hn : n > 0) (hm : m > 0) (h_lt : n < m) 
    (p : ℕ) (hp : p.Prime) (hp_dvd : p ∣ m * (m + 1)) (hp_gt : p > n + 1) : a n ≠ a m := by
  intro h_eq
  have h_dvd_T : p ∣ T_triangular m := by
    have h_mul : T_triangular m * 2 = m * (m + 1) := T_triangular_mul_two m
    have h_dvd : p ∣ T_triangular m * 2 := by
      rw [h_mul]
      exact hp_dvd
    rcases (Nat.Prime.dvd_mul hp).mp h_dvd with h1 | h2
    · exact h1
    · -- p ∣ 2
      have h_le : p ≤ 2 := Nat.le_of_dvd (by decide) h2
      omega
  have h_le := prime_factors_of_T_le n m hn hm h_eq p hp h_dvd_T
  omega

lemma a_lt_of_dvd (n m : ℕ) (hn : n > 0) (hm : m > 0) (h_lt : n < m) (h_dvd : n ∣ m) : a n < a m := by
  have h_subset : Nat.divisors n ⊆ Nat.divisors m := Nat.divisors_subset_of_dvd (Nat.ne_of_gt hm) h_dvd
  have h_prod : (∏ x ∈ Nat.divisors m \ Nat.divisors n, T_triangular x) * ∏ x ∈ Nat.divisors n, T_triangular x = ∏ x ∈ Nat.divisors m, T_triangular x := Finset.prod_sdiff h_subset
  have h_an_pos : a n > 0 := a_pos n hn
  have hm_mem : m ∈ Nat.divisors m := by
    rw [Nat.mem_divisors]
    exact ⟨dvd_rfl, Nat.ne_of_gt hm⟩
  have hm_not_mem : m ∉ Nat.divisors n := by
    rw [Nat.mem_divisors]
    push_neg
    intro h_dvd'
    have h_le := Nat.le_of_dvd hn h_dvd'
    omega
  have hm_mem_diff : m ∈ Nat.divisors m \ Nat.divisors n := by
    rw [Finset.mem_sdiff]
    exact ⟨hm_mem, hm_not_mem⟩
  have h_dvd_prod : T_triangular m ∣ ∏ x ∈ Nat.divisors m \ Nat.divisors n, T_triangular x := by
    exact Finset.dvd_prod_of_mem T_triangular hm_mem_diff
  have h_prod_pos : ∏ x ∈ Nat.divisors m \ Nat.divisors n, T_triangular x > 0 := by
    apply Finset.prod_pos
    intro d hd
    rw [Finset.mem_sdiff, Nat.mem_divisors] at hd
    have hd_ne : d ≠ 0 := by
      rintro rfl
      exact hd.1.2 (zero_dvd_iff.mp hd.1.1)
    exact T_triangular_pos d (Nat.pos_of_ne_zero hd_ne)
  have h_le_prod := Nat.le_of_dvd h_prod_pos h_dvd_prod
  have h_T_gt : T_triangular m > 1 := by
    dsimp [T_triangular]
    have h_mul : m * (m + 1) ≥ 6 := by
      have h_m : 2 ≤ m := by omega
      have h_m1 : 3 ≤ m + 1 := by omega
      nlinarith
    have h_div : m * (m + 1) / 2 ≥ 3 := by omega
    omega
  have h_prod_gt : ∏ x ∈ Nat.divisors m \ Nat.divisors n, T_triangular x > 1 := by omega
  have h_mul_gt : (∏ x ∈ Nat.divisors m \ Nat.divisors n, T_triangular x) * a n > a n := by
    calc
      (∏ x ∈ Nat.divisors m \ Nat.divisors n, T_triangular x) * a n > 1 * a n := Nat.mul_lt_mul_of_pos_right h_prod_gt h_an_pos
      _ = a n := Nat.one_mul (a n)
  dsimp [a]
  rw [← h_prod]
  exact h_mul_gt

lemma p_square_dvd_a_composite (m : ℕ) (hm : m > 0) (hc : ¬ m.Prime) (p : ℕ) (hp : p.Prime) (hp_odd : p ≥ 3) (hp_dvd : p ∣ m) : p^2 ∣ a m := by
  have hp_lt_m : p < m := by
    by_cases h_eq : p = m
    · subst h_eq; contradiction
    · have h_le := Nat.le_of_dvd hm hp_dvd
      omega
  have h_p_mem : p ∈ Nat.divisors m := by
    rw [Nat.mem_divisors]
    exact ⟨hp_dvd, Nat.ne_of_gt hm⟩
  have h_m_mem : m ∈ Nat.divisors m := by
    rw [Nat.mem_divisors]
    exact ⟨dvd_rfl, Nat.ne_of_gt hm⟩
  have h_ne : p ≠ m := Nat.ne_of_lt hp_lt_m
  have h_sub : {p, m} ⊆ Nat.divisors m := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h_p_mem
    · exact h_m_mem
  have h_dvd_prod : ({p, m} : Finset ℕ).prod T_triangular ∣ a m := by
    dsimp [a]
    exact Finset.prod_dvd_prod_of_subset {p, m} (Nat.divisors m) T_triangular h_sub
  have h_prod_eq : ({p, m} : Finset ℕ).prod T_triangular = T_triangular p * T_triangular m := by
    rw [Finset.prod_insert (by simp [h_ne]), Finset.prod_singleton]
  rw [h_prod_eq] at h_dvd_prod
  have h_p_dvd_Tp : p ∣ T_triangular p := by
    have h_mul : T_triangular p * 2 = p * (p + 1) := T_triangular_mul_two p
    have h_dvd : p ∣ T_triangular p * 2 := by
      rw [h_mul]
      exact dvd_mul_right p (p + 1)
    rcases (Nat.Prime.dvd_mul hp).mp h_dvd with h1 | h2
    · exact h1
    · have h_le2 : p ≤ 2 := Nat.le_of_dvd (by decide) h2
      omega
  have h_p_dvd_Tm : p ∣ T_triangular m := by
    have h_mul : T_triangular m * 2 = m * (m + 1) := T_triangular_mul_two m
    have h_dvd : p ∣ T_triangular m * 2 := by
      rw [h_mul]
      exact dvd_trans hp_dvd (dvd_mul_right m (m + 1))
    rcases (Nat.Prime.dvd_mul hp).mp h_dvd with h1 | h2
    · exact h1
    · have h_le2 : p ≤ 2 := Nat.le_of_dvd (by decide) h2
      omega
  have h_p2_dvd : p^2 ∣ T_triangular p * T_triangular m := by
    have h_p2_eq : p^2 = p * p := sq p
    rw [h_p2_eq]
    exact mul_dvd_mul h_p_dvd_Tp h_p_dvd_Tm
  exact dvd_trans h_p2_dvd h_dvd_prod

lemma prime_not_dvd_prod (s : Finset ℕ) (f : ℕ → ℕ) (p : ℕ) (hp : p.Prime) (h : ∀ x ∈ s, ¬ p ∣ f x) : ¬ p ∣ s.prod f := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    intro hp1
    have hp_ge2 : 2 ≤ p := hp.two_le
    have h_le := Nat.le_of_dvd (by decide) hp1
    omega
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    intro h_dvd
    rcases (Nat.Prime.dvd_mul hp).mp h_dvd with h1 | h2
    · have h_not := h a (Finset.mem_insert_self a s)
      contradiction
    · exact ih (fun x hx ↦ h x (Finset.mem_insert_of_mem hx)) h2

lemma prime_sq_dvd_mul_of_not_dvd (A B p : ℕ) (hp : p.Prime) (h_dvd : p^2 ∣ A * B) (h_not : ¬ p ∣ B) : p^2 ∣ A := by
  have hp_dvd : p ∣ A * B := by
    have h_p2 : p ∣ p^2 := dvd_pow_self p (by decide)
    exact dvd_trans h_p2 h_dvd
  have hp_dvd_A : p ∣ A := by
    rcases (Nat.Prime.dvd_mul hp).mp hp_dvd with h1 | h2
    · exact h1
    · contradiction
  rcases hp_dvd_A with ⟨C, rfl⟩
  have h_p2_dvd : p^2 ∣ p * C * B := h_dvd
  have h_p2_eq : p^2 = p * p := sq p
  rw [h_p2_eq] at h_p2_dvd
  have h_p_dvd : p ∣ C * B := by
    rw [mul_assoc] at h_p2_dvd
    exact (mul_dvd_mul_iff_left hp.ne_zero).mp h_p2_dvd
  have hp_dvd_C : p ∣ C := by
    rcases (Nat.Prime.dvd_mul hp).mp h_p_dvd with h1 | h2
    · exact h1
    · contradiction
  rcases hp_dvd_C with ⟨D, rfl⟩
  have h_A_eq : p * (p * D) = p^2 * D := by
    rw [← mul_assoc, ← h_p2_eq]
  rw [h_A_eq]
  exact dvd_mul_right (p^2) D

lemma not_p2_dvd_T_n (n : ℕ) (hn : n ≥ 5) (p : ℕ) (hp : p.Prime) (hp_odd : p ≥ 3) (hp_eq : p = n + 1) : ¬ p^2 ∣ T_triangular n := by
  intro h_dvd
  have h_T_mul : T_triangular n * 2 = n * p := by
    rw [T_triangular_mul_two, hp_eq]
  have h_dvd_mul : p^2 * 2 ∣ T_triangular n * 2 := mul_dvd_mul_right h_dvd 2
  rw [h_T_mul] at h_dvd_mul
  have h_p2_dvd : p^2 ∣ n * p := dvd_trans (dvd_mul_right (p^2) 2) h_dvd_mul
  have h_p2_eq : p^2 = p * p := sq p
  rw [h_p2_eq, mul_comm n p] at h_p2_dvd
  rw [mul_dvd_mul_iff_left hp.ne_zero] at h_p2_dvd
  have h_le := Nat.le_of_dvd (by omega) h_p2_dvd
  omega


lemma not_p_dvd_T_d_of_ne (n : ℕ) (hn : n ≥ 5) (p : ℕ) (hp : p.Prime) (hp_eq : p = n + 1)
    (d : ℕ) (hd : d ∈ Nat.divisors n) (h_ne : d ≠ n) : ¬ p ∣ T_triangular d := by
  intro h_dvd
  have hp_odd : p ≥ 3 := by omega
  have h_mul : T_triangular d * 2 = d * (d + 1) := T_triangular_mul_two d
  have h_p_dvd_mul : p ∣ d * (d + 1) := by
    rw [← h_mul]
    exact dvd_mul_of_dvd_left h_dvd 2
  rcases (Nat.Prime.dvd_mul hp).mp h_p_dvd_mul with h1 | h2
  · -- p | d
    have hd_pos : d > 0 := by
      rw [Nat.mem_divisors] at hd
      have hd_ne : d ≠ 0 := by
        rintro rfl
        exact hd.2 (zero_dvd_iff.mp hd.1)
      exact Nat.pos_of_ne_zero hd_ne
    have h_le := Nat.le_of_dvd hd_pos h1
    have hd_le_n : d ≤ n := by
      rw [Nat.mem_divisors] at hd
      exact Nat.le_of_dvd (by omega) hd.1
    omega
  · -- p | d + 1
    have hd_le_n : d ≤ n := by
      rw [Nat.mem_divisors] at hd
      exact Nat.le_of_dvd (by omega) hd.1
    have h_le := Nat.le_of_dvd (by omega) h2
    have h_eq2 : d = n := by omega
    contradiction

lemma not_p2_dvd_a_n (n : ℕ) (hn : n ≥ 5) (p : ℕ) (hp : p.Prime) (hp_eq : p = n + 1) : ¬ p^2 ∣ a n := by
  have hn_pos : n > 0 := by omega
  have h_mem : n ∈ Nat.divisors n := by
    rw [Nat.mem_divisors]
    exact ⟨dvd_rfl, Nat.ne_of_gt hn_pos⟩
  have h_decomp : Nat.divisors n = insert n (Nat.divisors n \ {n}) := (Finset.insert_sdiff_self_of_mem h_mem).symm
  have h_prod : a n = T_triangular n * (Nat.divisors n \ {n}).prod T_triangular := by
    dsimp [a]
    nth_rw 1 [h_decomp]
    rw [Finset.prod_insert (by simp)]
  rw [h_prod]
  have h_not_dvd_prod : ¬ p ∣ (Nat.divisors n \ {n}).prod T_triangular := by
    apply prime_not_dvd_prod
    · exact hp
    · intro d hd
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hd
      exact not_p_dvd_T_d_of_ne n hn p hp hp_eq d hd.1 hd.2
  have hp_odd : p ≥ 3 := by omega
  have h_not_p2_T := not_p2_dvd_T_n n hn p hp hp_odd hp_eq
  intro h_dvd
  have h_p2_dvd_T := prime_sq_dvd_mul_of_not_dvd (T_triangular n) ((Nat.divisors n \ {n}).prod T_triangular) p hp h_dvd h_not_dvd_prod
  contradiction


lemma divisors_T_dvd_p (n : ℕ) (hn : n > 0) (p : ℕ) (hp : p.Prime) (hp_odd : p ≥ 3) (h_gt : 2 * p > n + 1)
    (d : ℕ) (hd : d ∈ Nat.divisors n) (h_p : p ∣ T_triangular d) : d = p ∨ d = p - 1 := by
  have h_dvd : p ∣ d * (d + 1) := by
    have h_mul : T_triangular d * 2 = d * (d + 1) := T_triangular_mul_two d
    rw [← h_mul]
    exact dvd_mul_of_dvd_left h_p 2
  have hd_dvd : d ∣ n := (Nat.mem_divisors.mp hd).1
  have hd_le_n : d ≤ n := Nat.le_of_dvd hn hd_dvd
  have hd_pos : d > 0 := by
    have hd_ne : d ≠ 0 := by
      rintro rfl
      rw [Nat.mem_divisors] at hd
      exact hd.2 (zero_dvd_iff.mp hd.1)
    exact Nat.pos_of_ne_zero hd_ne
  rcases (Nat.Prime.dvd_mul hp).mp h_dvd with h1 | h2
  · -- p | d
    rcases h1 with ⟨k, rfl⟩
    have hk_gt : k > 0 := by
      by_cases hk : k = 0
      · subst hk; simp at hd_pos
      · omega
    have h_bound : p * k < 2 * p - 1 := by omega
    have hk_eq : k = 1 := by
      by_cases hk2 : k ≥ 2
      · have : p * k ≥ p * 2 := Nat.mul_le_mul_left p hk2
        omega
      · omega
    subst hk_eq
    rw [mul_one]
    left; rfl
  · -- p | d + 1
    rcases h2 with ⟨k, hk⟩
    have hk_gt : k > 0 := by
      by_cases hk0 : k = 0
      · subst hk0; omega
      · omega
    have h_bound : d + 1 < 2 * p := by omega
    rw [hk] at h_bound
    have hk_eq : k = 1 := by
      by_cases hk2 : k ≥ 2
      · have : p * k ≥ p * 2 := Nat.mul_le_mul_left p hk2
        omega
      · omega
    subst hk_eq
    rw [mul_one] at hk
    right; omega

lemma not_p2_dvd_a_n_of_two_p (n : ℕ) (hn : n > 0) (p : ℕ) (hp : p.Prime) (hp_odd : p ≥ 3) (h_gt : 2 * p > n + 1) : ¬ p^2 ∣ a n := by
  have s_eq : Nat.divisors n = Nat.divisors n := rfl
  generalize h_s : Nat.divisors n = s
  by_cases hA : p ∈ s
  · by_cases hB : p - 1 ∈ s
    · -- both in s, impossible
      have h_s2 : Nat.divisors n = s := h_s
      rw [← h_s2] at hA hB
      have hp_dvd_n : p ∣ n := (Nat.mem_divisors.mp hA).1
      have hp1_dvd_n : p - 1 ∣ n := (Nat.mem_divisors.mp hB).1
      have h_coprime : Nat.Coprime p (p - 1) := by
        have h_sub : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
        have h_co : Nat.Coprime (p - 1) (p - 1 + 1) := by simp
        rw [h_sub] at h_co
        exact h_co.symm
      have h_mul_dvd : p * (p - 1) ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd h_coprime hp_dvd_n hp1_dvd_n
      have h_le := Nat.le_of_dvd hn h_mul_dvd
      have h_mul_ge : p * (p - 1) ≥ p * 2 := Nat.mul_le_mul_left p (by omega)
      have h_linear : p * 2 ≤ n := by omega
      omega
    · -- p in s, p-1 not in s
      have h_decomp : s = insert p (s \ {p}) := (Finset.insert_sdiff_self_of_mem hA).symm
      have h_prod : a n = T_triangular p * (s \ {p}).prod T_triangular := by
        dsimp [a]
        rw [h_s]
        nth_rw 1 [h_decomp]
        rw [Finset.prod_insert (by simp)]
      have h_not_dvd_prod : ¬ p ∣ (s \ {p}).prod T_triangular := by
        apply prime_not_dvd_prod
        · exact hp
        · intro d hd
          rw [Finset.mem_sdiff, Finset.mem_singleton] at hd
          intro h_p_dvd
          have h_cases := divisors_T_dvd_p n hn p hp hp_odd h_gt d (by rw [h_s]; exact hd.1) h_p_dvd
          rcases h_cases with rfl | rfl
          · exact hd.2 rfl
          · exact hB hd.1
      have h_not_p2_Tp : ¬ p^2 ∣ T_triangular p := by
        intro h_dvd
        have h_T_mul : T_triangular p * 2 = p * (p + 1) := T_triangular_mul_two p
        have h_dvd_mul : p^2 * 2 ∣ T_triangular p * 2 := mul_dvd_mul_right h_dvd 2
        rw [h_T_mul] at h_dvd_mul
        have h_p2_dvd : p^2 ∣ p * (p + 1) := dvd_trans (dvd_mul_right (p^2) 2) h_dvd_mul
        have h_p2_eq : p^2 = p * p := sq p
        rw [h_p2_eq] at h_p2_dvd
        rw [mul_dvd_mul_iff_left hp.ne_zero] at h_p2_dvd
        have h_p_dvd_1 : p ∣ 1 := (Nat.dvd_add_right (dvd_refl p)).mp h_p2_dvd
        have h_le := Nat.le_of_dvd (by decide) h_p_dvd_1
        omega
      intro h_dvd_a
      rw [h_prod] at h_dvd_a
      have h_p2_dvd_Tp := prime_sq_dvd_mul_of_not_dvd (T_triangular p) ((s \ {p}).prod T_triangular) p hp h_dvd_a h_not_dvd_prod
      contradiction
  · by_cases hB : p - 1 ∈ s
    · -- p-1 in s, p not in s
      have h_decomp : s = insert (p - 1) (s \ {p - 1}) := (Finset.insert_sdiff_self_of_mem hB).symm
      have h_prod : a n = T_triangular (p - 1) * (s \ {p - 1}).prod T_triangular := by
        dsimp [a]
        rw [h_s]
        nth_rw 1 [h_decomp]
        rw [Finset.prod_insert (by simp)]
      have h_not_dvd_prod : ¬ p ∣ (s \ {p - 1}).prod T_triangular := by
        apply prime_not_dvd_prod
        · exact hp
        · intro d hd
          rw [Finset.mem_sdiff, Finset.mem_singleton] at hd
          intro h_p_dvd
          have h_cases := divisors_T_dvd_p n hn p hp hp_odd h_gt d (by rw [h_s]; exact hd.1) h_p_dvd
          rcases h_cases with rfl | rfl
          · exact hA hd.1
          · exact hd.2 rfl
      have h_not_p2_Tp1 : ¬ p^2 ∣ T_triangular (p - 1) := by
        intro h_dvd
        have h_T_mul : T_triangular (p - 1) * 2 = (p - 1) * p := by
          have : T_triangular (p - 1) * 2 = (p - 1) * (p - 1 + 1) := T_triangular_mul_two (p - 1)
          have h_sub : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
          rw [this, h_sub]
        have h_dvd_mul : p^2 * 2 ∣ T_triangular (p - 1) * 2 := mul_dvd_mul_right h_dvd 2
        rw [h_T_mul] at h_dvd_mul
        have h_p2_dvd : p^2 ∣ (p - 1) * p := dvd_trans (dvd_mul_right (p^2) 2) h_dvd_mul
        have h_p2_eq : p^2 = p * p := sq p
        rw [h_p2_eq, mul_comm (p-1) p] at h_p2_dvd
        rw [mul_dvd_mul_iff_left hp.ne_zero] at h_p2_dvd
        have h_le := Nat.le_of_dvd (by omega) h_p2_dvd
        omega
      intro h_dvd_a
      rw [h_prod] at h_dvd_a
      have h_p2_dvd_Tp1 := prime_sq_dvd_mul_of_not_dvd (T_triangular (p - 1)) ((s \ {p - 1}).prod T_triangular) p hp h_dvd_a h_not_dvd_prod
      contradiction
    · -- neither in s
      have h_s2 : Nat.divisors n = s := h_s
      rw [← h_s2] at hA hB
      have h_not_dvd : ¬ p ∣ a n := by
        dsimp [a]
        apply prime_not_dvd_prod
        · exact hp
        · intro d hd h_p_dvd
          have h_cases := divisors_T_dvd_p n hn p hp hp_odd h_gt d hd h_p_dvd
          rcases h_cases with rfl | rfl
          · exact hA hd
          · exact hB hd
      intro h_p2_dvd
      have h_p_dvd : p ∣ a n := by
        have h_p2 : p ∣ p^2 := dvd_pow_self p (by decide)
        exact dvd_trans h_p2 h_p2_dvd
      contradiction


lemma prime_not_dvd_a_n_of_bounds_general (n : ℕ) (hn : n > 0) (p : ℕ) (hp : p.Prime)
    (k : ℕ) (h_gt : k * p > n + 1) (h_ndvd : ¬ p ∣ n)
    (h_ndvd_sub : ∀ c, 1 ≤ c → c < k → ¬ c * p - 1 ∣ n) : ¬ p ∣ a n := by
  intro h_dvd
  dsimp [a] at h_dvd
  have hp' : _root_.Prime p := Nat.prime_iff.mp hp
  rw [Prime.dvd_finset_prod_iff hp'] at h_dvd
  rcases h_dvd with ⟨d, hd, hd_dvd⟩
  rw [Nat.mem_divisors] at hd
  have hd_le : d ≤ n := Nat.le_of_dvd hn hd.1
  have hd_dvd' : p ∣ d * (d + 1) := by
    have h_mul : d * (d + 1) = T_triangular d * 2 := (T_triangular_mul_two d).symm
    rw [h_mul]
    exact dvd_mul_of_dvd_left hd_dvd 2
  have hp_dvd_mul : p ∣ d ∨ p ∣ d + 1 := (Nat.Prime.dvd_mul hp).mp hd_dvd'
  rcases hp_dvd_mul with hp_d | hp_d1
  · have hp_dvd_n : p ∣ n := dvd_trans hp_d hd.1
    exact h_ndvd hp_dvd_n
  · have hd_pos : d + 1 > 0 := by omega
    rcases hp_d1 with ⟨c, hc⟩
    have hc_pos : c > 0 := by
      by_cases hc0 : c = 0
      · subst hc0; omega
      · omega
    have hc_lt : c < k := by
      by_contra hc_ge
      push_neg at hc_ge
      have : d + 1 ≥ k * p := by
        rw [hc]
        calc p * c ≥ p * k := Nat.mul_le_mul_left p hc_ge
        _ = k * p := by ring
      omega
    have hd_eq : d = c * p - 1 := by
      have : d + 1 = c * p := by rw [hc, mul_comm]
      omega
    have h_div_n : c * p - 1 ∣ n := by
      rw [← hd_eq]
      exact hd.1
    exact h_ndvd_sub c hc_pos hc_lt h_div_n


lemma prime_not_dvd_a_n_of_bounds (n : ℕ) (hn : n > 0) (p : ℕ) (hp : p.Prime)
    (h_gt : 2 * p > n + 1) (h_ndvd : ¬ p ∣ n) (h_ndvd_sub : ¬ p - 1 ∣ n) : ¬ p ∣ a n := by
  intro h_dvd
  dsimp [a] at h_dvd
  have hp' : _root_.Prime p := Nat.prime_iff.mp hp
  rw [Prime.dvd_finset_prod_iff hp'] at h_dvd
  rcases h_dvd with ⟨d, hd, hd_dvd⟩
  rw [Nat.mem_divisors] at hd
  have hd_le : d ≤ n := Nat.le_of_dvd hn hd.1
  have hd_dvd' : p ∣ d * (d + 1) := by
    have h_mul : d * (d + 1) = T_triangular d * 2 := (T_triangular_mul_two d).symm
    rw [h_mul]
    exact dvd_mul_of_dvd_left hd_dvd 2
  have hp_dvd_mul : p ∣ d ∨ p ∣ d + 1 := (Nat.Prime.dvd_mul hp).mp hd_dvd'
  rcases hp_dvd_mul with hp_d | hp_d1
  · have hp_dvd_n : p ∣ n := dvd_trans hp_d hd.1
    exact h_ndvd hp_dvd_n
  · have hd_pos : d + 1 > 0 := by omega
    have hd_lt_2p : d + 1 < 2 * p := by omega
    have h_eq : d + 1 = p := by
      rcases hp_d1 with ⟨k, hk⟩
      have hk_pos : k > 0 := by
        by_cases hk0 : k = 0
        · subst hk0; omega
        · omega
      have hk_lt : k < 2 := by
        by_cases hk2 : k ≥ 2
        · have : d + 1 ≥ 2 * p := by
            rw [hk]
            calc p * k ≥ p * 2 := Nat.mul_le_mul_left p hk2
            _ = 2 * p := by ring
          omega
        · omega
      have hk_eq : k = 1 := by omega
      rw [hk, hk_eq, mul_one]
    have hd_eq : d = p - 1 := by omega
    subst hd_eq
    exact h_ndvd_sub hd.1

lemma a_ne_of_T_gt (n m : ℕ) (hn : n > 0) (hm : m > 0) (h_size : T_triangular m > a n) : a n ≠ a m := by
  intro h_eq
  have h_dvd := T_dvd_a m hm
  have h_am_pos := a_pos m hm
  have h_le := Nat.le_of_dvd h_am_pos h_dvd
  rw [← h_eq] at h_le
  omega

lemma T_triangular_ge_of_ge {m : ℕ} (hm : m ≥ 301) : T_triangular m ≥ 45451 := by
  dsimp [T_triangular]
  have h_mul : m * (m + 1) ≥ 90902 := by
    have h1 : m ≥ 301 := hm
    have h2 : m + 1 ≥ 302 := by omega
    nlinarith
  omega


lemma p_square_dvd_a_of_sq_dvd_m_plus_one (m : ℕ) (hm : m > 0) (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) (hp_dvd : p^2 ∣ m + 1) : p^2 ∣ a m := by
  have h_dvd_T : p^2 ∣ T_triangular m := by
    have h_mul : T_triangular m * 2 = m * (m + 1) := T_triangular_mul_two m
    have h_p2_dvd_mul : p^2 ∣ m * (m + 1) := dvd_mul_of_dvd_right hp_dvd m
    rw [← h_mul] at h_p2_dvd_mul
    have hp2_coprime_two : Nat.Coprime (p^2) 2 := by
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra h_gcd
      have h_gcd_dvd : Nat.gcd (p^2) 2 ∣ 2 := Nat.gcd_dvd_right (p^2) 2
      have h_gcd_le : Nat.gcd (p^2) 2 ≤ 2 := Nat.le_of_dvd (by decide) h_gcd_dvd
      have h_gcd_pos : Nat.gcd (p^2) 2 > 0 := Nat.gcd_pos_of_pos_right (p^2) (by decide)
      have h_gcd_cases : Nat.gcd (p^2) 2 = 1 ∨ Nat.gcd (p^2) 2 = 2 := by
        interval_cases Nat.gcd (p^2) 2
        · exact Or.inl rfl
        · exact Or.inr rfl
      rcases h_gcd_cases with h1 | h2
      · contradiction
      · have h_dvd : 2 ∣ p^2 := by
          have h_gcd_dvd_left := Nat.gcd_dvd_left (p^2) 2
          rw [h2] at h_gcd_dvd_left
          exact h_gcd_dvd_left
        have hp_even : 2 ∣ p := by
          have h_p2_eq : p^2 = p * p := sq p
          rw [h_p2_eq] at h_dvd
          rcases ((by decide : Nat.Prime 2).dvd_mul).mp h_dvd with h_p | h_p
          · exact h_p
          · exact h_p
        rcases hp.eq_one_or_self_of_dvd 2 hp_even with h2_1 | h2_p
        · contradiction
        · have hp2 : p = 2 := h2_p.symm
          omega
    exact Nat.Coprime.dvd_of_dvd_mul_right hp2_coprime_two h_p2_dvd_mul
  have h_dvd_a : T_triangular m ∣ a m := T_dvd_a m hm
  exact dvd_trans h_dvd_T h_dvd_a


lemma prime_factor_bounds_of_eq (n m : ℕ) (hn : n > 0) (hm : m > 0) (h_eq : a n = a m)
    (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) (hp_dvd : p ∣ m * (m + 1)) :
    2 * p ≤ n + 1 ∨ p ∣ n ∨ p - 1 ∣ n := by
  by_contra h_neg
  push_neg at h_neg
  rcases h_neg with ⟨h_gt, h_ndvd, h_ndvd_sub⟩
  have h_ndvd_an : ¬ p ∣ a n := prime_not_dvd_a_n_of_bounds n hn p hp h_gt h_ndvd h_ndvd_sub
  have h_dvd_am : p ∣ a m := by
    have h_dvd_T : p ∣ T_triangular m := by
      have h_mul : T_triangular m * 2 = m * (m + 1) := T_triangular_mul_two m
      have h_dvd : p ∣ T_triangular m * 2 := by
        rw [h_mul]
        exact hp_dvd
      rcases (Nat.Prime.dvd_mul hp).mp h_dvd with h1 | h2
      · exact h1
      · -- p ∣ 2
        have h_le : p ≤ 2 := Nat.le_of_dvd (by decide) h2
        omega
    have h_dvd_a : T_triangular m ∣ a m := T_dvd_a m hm
    exact dvd_trans h_dvd_T h_dvd_a
  rw [h_eq] at h_ndvd_an
  contradiction


set_option maxHeartbeats 0
lemma a_ne_of_lt (n m : ℕ) (hn : n > 0) (hm : m > 0) (h_lt : n < m) : a n ≠ a m := by
  intro h_eq
  have h_m_comp : ¬ m.Prime := by
    intro hp
    exact case_m_prime n m hn hm h_lt h_eq hp
  have h_m1_comp : ¬ (m + 1).Prime := by
    intro hp
    exact case_m_plus_one_prime n m hn hm h_lt h_eq hp
  have h_n_not_prime : ¬ n.Prime := by
    intro hn_prime
    have ha_n : a n = T_triangular n := a_prime n hn_prime
    have h_dvd : T_triangular m ∣ a m := T_dvd_a m hm
    rw [← h_eq, ha_n] at h_dvd
    have h_pos : T_triangular n > 0 := T_triangular_pos n hn
    have h_le := Nat.le_of_dvd h_pos h_dvd
    have h_mono : T_triangular n < T_triangular m := by
      dsimp [T_triangular]
      have h1 : n * (n + 1) < m * (m + 1) := by
        nlinarith
      have h2 : 2 ∣ n * (n + 1) := even_iff_two_dvd.mp (Nat.even_mul_succ_self n)
      have h3 : 2 ∣ m * (m + 1) := even_iff_two_dvd.mp (Nat.even_mul_succ_self m)
      omega
    omega
  have h_ndvd : ¬ n ∣ m := by
    intro h_dvd
    have h_lt_a := a_lt_of_dvd n m hn hm h_lt h_dvd
    omega
  by_cases h_m300 : m ≤ 303
  · interval_cases m
    · omega
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
    · interval_cases n <;> (try revert h_eq) <;> decide
  · push_neg at h_m300
    by_cases hn12 : n < 12
    · have h_m301 : m ≥ 301 := by omega
      have h_Tm : T_triangular m ≥ 45451 := T_triangular_ge_of_ge h_m301
      interval_cases n
      · have h_an : a 1 = 1 := by rfl
        have h_size : T_triangular m > a 1 := by omega
        exact a_ne_of_T_gt 1 m hn hm h_size h_eq
      · have h_an : a 2 = 3 := by decide
        have h_size : T_triangular m > a 2 := by omega
        exact a_ne_of_T_gt 2 m hn hm h_size h_eq
      · have h_an : a 3 = 6 := by decide
        have h_size : T_triangular m > a 3 := by omega
        exact a_ne_of_T_gt 3 m hn hm h_size h_eq
      · have h_an : a 4 = 30 := by decide
        have h_size : T_triangular m > a 4 := by omega
        exact a_ne_of_T_gt 4 m hn hm h_size h_eq
      · have h_an : a 5 = 15 := by decide
        have h_size : T_triangular m > a 5 := by omega
        exact a_ne_of_T_gt 5 m hn hm h_size h_eq
      · have h_an : a 6 = 378 := by decide
        have h_size : T_triangular m > a 6 := by omega
        exact a_ne_of_T_gt 6 m hn hm h_size h_eq
      · have h_an : a 7 = 28 := by decide
        have h_size : T_triangular m > a 7 := by omega
        exact a_ne_of_T_gt 7 m hn hm h_size h_eq
      · have h_an : a 8 = 1080 := by decide
        have h_size : T_triangular m > a 8 := by omega
        exact a_ne_of_T_gt 8 m hn hm h_size h_eq
      · have h_an : a 9 = 270 := by decide
        have h_size : T_triangular m > a 9 := by omega
        exact a_ne_of_T_gt 9 m hn hm h_size h_eq
      · have h_an : a 10 = 2475 := by decide
        have h_size : T_triangular m > a 10 := by omega
        exact a_ne_of_T_gt 10 m hn hm h_size h_eq
      · have h_an : a 11 = 66 := by decide
        have h_size : T_triangular m > a 11 := by omega
        exact a_ne_of_T_gt 11 m hn hm h_size h_eq
    · push_neg at hn12
      have h_prime_bound : ∀ p : ℕ, p.Prime → p ∣ m * (m + 1) → p ≤ n + 1 := by
        intro p hp hp_dvd
        rcases eq_or_ne p 2 with rfl | hp2
        · omega
        · have hp3 : p ≥ 3 := by
            have hp_ge2 : p ≥ 2 := hp.two_le
            omega
          have hp_T : p ∣ T_triangular m := by
            have h_mul : T_triangular m * 2 = m * (m + 1) := T_triangular_mul_two m
            have h_dvd : p ∣ T_triangular m * 2 := by
              rw [h_mul]
              exact hp_dvd
            rcases (Nat.Prime.dvd_mul hp).mp h_dvd with h1 | h2
            · exact h1
            · -- p ∣ 2
              have h_le : p ≤ 2 := Nat.le_of_dvd (by decide) h2
              omega
          exact prime_factors_of_T_le n m hn hm h_eq p hp hp_T
      sorry

/-- A275786 Conjecture: the sequence is injective (all terms of this sequence occur only once). -/
theorem oeis_A275786_conjecture :
  ∀ n m : ℕ, n > 0 → m > 0 → (a n = a m → n = m) := by
  intro n m hn hm h_eq
  rcases lt_or_ge n m with h_lt | h_ge
  · have h_ne := a_ne_of_lt n m hn hm h_lt
    contradiction
  · rcases eq_or_lt_of_le h_ge with rfl | h_gt
    · rfl
    · have h_ne := a_ne_of_lt m n hm hn h_gt
      exact (h_ne h_eq.symm).elim

