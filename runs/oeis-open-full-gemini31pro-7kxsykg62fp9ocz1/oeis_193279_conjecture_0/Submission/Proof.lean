import Mathlib

open Nat Finset ArithmeticFunction

lemma factor_even (n : ℕ) (h0 : n ≠ 0) (heven : Even n) :
  ∃ k m : ℕ, k ≥ 1 ∧ Odd m ∧ n = 2^k * m := by
  obtain ⟨k, m, hodd, heq⟩ := exists_eq_two_pow_mul_odd h0
  use k, m
  refine ⟨?_, hodd, heq⟩
  cases k with
  | zero =>
    simp only [pow_zero, one_mul] at heq
    rcases hodd with ⟨a, ha⟩
    rcases heven with ⟨b, hb⟩
    omega
  | succ k => omega

lemma coprime_two_pow_odd (k m : ℕ) (hodd : Odd m) : Coprime (2^k) m := by
  cases k with
  | zero => simp
  | succ k =>
    have hn : 0 < k + 1 := by omega
    rw [coprime_pow_left_iff hn]
    rw [Nat.Prime.coprime_iff_not_dvd prime_two]
    intro h
    have := even_iff_two_dvd.mpr h
    rcases hodd with ⟨a, ha⟩
    rcases this with ⟨b, hb⟩
    omega

lemma sum_2_pow (i : ℕ) : ∑ k ∈ range (i + 1), 2 ^ k = 2 ^ (i + 1) - 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [sum_range_succ, ih]
    have h : 1 ≤ 2 ^ (i + 1) := Nat.one_le_pow' _ 1
    rw [pow_succ 2 (i+1)]
    omega

lemma sigma_two_pow (k : ℕ) : (sigma 1) (2^k) = 2^(k+1) - 1 := by
  rw [sigma_one_apply_prime_pow prime_two]
  exact sum_2_pow k

lemma sigma_mul_of_coprime {k m : ℕ} (hcoprime : Coprime k m) : (sigma 1) (k * m) = (sigma 1) k * (sigma 1) m := by
  exact isMultiplicative_sigma.map_mul_of_coprime hcoprime

lemma sigma_eq_two_mul_of_perfect {n : ℕ} (hn : n > 0) (hperf : n.Perfect) : (sigma 1) n = 2 * n := by
  have := (Nat.perfect_iff_sum_divisors_eq_two_mul hn).mp hperf
  rw [sigma_apply]
  simp [this]

lemma sigma_eq_sum_divs (m : ℕ) : (sigma 1) m = ∑ d ∈ m.divisors, d := by simp [sigma_apply]

lemma q_eq_one (m q : ℕ) (hm : m > 0) (hq_lt : q < m) (hq_dvd : q ∣ m) (hsum : (sigma 1) m = m + q) : q = 1 := by
  rw [sigma_eq_sum_divs] at hsum
  have h_m_in : m ∈ m.divisors := mem_divisors.mpr ⟨dvd_rfl, hm.ne'⟩
  have h_q_in : q ∈ m.divisors := mem_divisors.mpr ⟨hq_dvd, hm.ne'⟩
  have h_1_in : 1 ∈ m.divisors := mem_divisors.mpr ⟨one_dvd m, hm.ne'⟩
  by_contra h_q_ne_1
  have h_m_ne_q : m ≠ q := by omega
  have h_m_ne_1 : m ≠ 1 := by
    by_contra h
    subst h
    have : q = 0 := by omega
    subst this
    simp at h_q_in
  have sub_sum : ∑ x ∈ {m, q, 1}, x ≤ ∑ x ∈ m.divisors, x := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact h_m_in
      · exact h_q_in
      · exact h_1_in
    · intro _ _ _
      omega
  have sum_eq : ∑ x ∈ ({m, q, 1} : Finset ℕ), x = m + q + 1 := by
    rw [sum_insert, sum_insert, sum_singleton]
    · omega
    · simp only [mem_singleton]
      exact h_q_ne_1
    · simp only [mem_insert, mem_singleton, not_or]
      exact ⟨h_m_ne_q, h_m_ne_1⟩
  rw [sum_eq, hsum] at sub_sum
  omega

lemma m_eq_pow_sub_one (k m : ℕ) (hk : k ≥ 1) (hodd : Odd m) (hm0 : m > 0) (hperf : (2^k * m).Perfect) :
  m = 2^(k+1) - 1 := by
  have eq1 : (sigma 1) (2^k * m) = 2^(k+1) * m := by
    have h1 := sigma_eq_two_mul_of_perfect (by positivity) hperf
    rw [h1]
    have : 2 * (2^k * m) = 2^(k+1) * m := by
      rw [← mul_assoc, ← pow_succ']
    exact this
  have eq2 : (sigma 1) (2^k * m) = (2^(k+1) - 1) * (sigma 1) m := by
    rw [sigma_mul_of_coprime (coprime_two_pow_odd k m hodd), sigma_two_pow]
  have eq3 : (2^(k+1) - 1) * (sigma 1) m = (2^(k+1) - 1 + 1) * m := by
    have h_sub : 2^(k+1) - 1 + 1 = 2^(k+1) := by
      have : 1 ≤ 2^(k+1) := Nat.one_le_pow' _ 1
      omega
    rw [h_sub, ← eq1, eq2]
  have eq4 : (2^(k+1) - 1) * (sigma 1) m = (2^(k+1) - 1) * m + m := by
    rw [eq3, add_mul, one_mul]
  have h_le : m ≤ (sigma 1) m := by
    rw [sigma_eq_sum_divs]
    have h_m_in : m ∈ m.divisors := mem_divisors.mpr ⟨dvd_rfl, hm0.ne'⟩
    have sub_sum : ∑ x ∈ {m}, x ≤ ∑ x ∈ m.divisors, x := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro x hx
        simp only [mem_singleton] at hx
        subst hx
        exact h_m_in
      · intro _ _ _
        omega
    have : ∑ x ∈ {m}, x = m := by simp
    rw [this] at sub_sum
    exact sub_sum
  have eq5 : (2^(k+1) - 1) * ((sigma 1) m - m) = m := by
    rw [Nat.mul_sub_left_distrib, eq4]
    omega
  let q := (sigma 1) m - m
  have hP : 2^(k+1) - 1 ≥ 3 := by
    have : 1 + 1 ≤ k + 1 := by omega
    have h2 : 2^2 ≤ 2^(k+1) := Nat.pow_le_pow_right (by decide) this
    omega
  have hq_lt : q < m := by
    have : (2^(k+1) - 1) * q = m := eq5
    nlinarith
  have hq_dvd : q ∣ m := ⟨2^(k+1) - 1, by rw [mul_comm, eq5]⟩
  have hsum : (sigma 1) m = m + q := by omega
  have hq_one := q_eq_one m q hm0 hq_lt hq_dvd hsum
  have : (2^(k+1) - 1) * q = m := eq5
  rw [hq_one, mul_one] at this
  exact this.symm

lemma subset_eq_of_sum_eq_of_pos {A B : Finset ℕ} (hsub : A ⊆ B) (heq : ∑ x ∈ A, x = ∑ x ∈ B, x) (hpos : ∀ x ∈ B, x > 0) : A = B := by
  have H_union : B = A ∪ (B \ A) := by
    ext x
    simp only [mem_union, mem_sdiff]
    tauto
  have hdisj : Disjoint A (B \ A) := disjoint_sdiff
  have h1 : ∑ x ∈ B, x = ∑ x ∈ A, x + ∑ x ∈ (B \ A), x := by
    nth_rw 1 [H_union]
    rw [sum_union hdisj]
  have h2 : ∑ x ∈ (B \ A), x = 0 := by omega
  have h3 : B \ A = ∅ := by
    by_contra h_ne
    obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr h_ne
    have hx_pos : x > 0 := hpos x (sdiff_subset hx)
    have sum_pos : ∑ x ∈ (B \ A), x > 0 := sum_pos' (fun y hy => by omega) ⟨x, hx, hx_pos⟩
    omega
  ext x
  rw [H_union]
  simp [h3]

lemma binary_sum (k y : ℕ) (hy : y < 2^(k+1)) :
  ∃ s : Finset ℕ, s ⊆ Iic k ∧ ∑ x ∈ s, 2^x = y := by
  induction k generalizing y with
  | zero =>
    cases y with
    | zero =>
      use ∅
      simp
    | succ y =>
      cases y with
      | zero =>
        use {0}
        simp
      | succ y =>
        exfalso
        revert hy
        omega
  | succ k ih =>
    by_cases h : y < 2^(k+1)
    · obtain ⟨s, hs1, hs2⟩ := ih y h
      use s
      refine ⟨?_, hs2⟩
      intro x hx
      have H := hs1 hx
      simp only [mem_Iic] at H ⊢
      omega
    · have h_y : y - 2^(k+1) < 2^(k+1) := by
        have : 2^(k+2) = 2^(k+1) + 2^(k+1) := by ring
        omega
      obtain ⟨s', hs1, hs2⟩ := ih (y - 2^(k+1)) h_y
      use insert (k+1) s'
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [mem_insert] at hx
        rcases hx with rfl | hx
        · exact mem_Iic.mpr le_rfl
        · have H := hs1 hx
          simp only [mem_Iic] at H ⊢
          omega
      · rw [sum_insert]
        · rw [hs2]
          omega
        · intro h_in
          have H := hs1 h_in
          simp only [mem_Iic] at H ⊢
          omega

lemma pow_two_ne_pow_two_mul_m (i1 i2 m : ℕ) (hm : m ≥ 3) (hodd : Odd m) : 2^i1 ≠ 2^i2 * m := by
  intro h
  rcases lt_trichotomy i1 i2 with hlt | heq | hgt
  · have h1 : 2^i1 < 2^i2 := Nat.pow_lt_pow_right (by decide) hlt
    have h2 : 2^i2 ≤ 2^i2 * m := Nat.le_mul_of_pos_right _ (by omega)
    omega
  · subst heq
    have h1 : 2^i1 * 1 = 2^i1 * m := by omega
    have hm1 : 1 = m := Nat.eq_of_mul_eq_mul_left (by positivity) h1
    omega
  · have h_add : i1 = i2 + (i1 - i2) := by omega
    have h_sub : i1 - i2 > 0 := by omega
    rw [h_add, pow_add] at h
    have hm_eq : 2^(i1 - i2) = m := Nat.eq_of_mul_eq_mul_left (by positivity) h
    have heven : Even (2^(i1 - i2)) := even_pow.mpr ⟨even_two, h_sub.ne'⟩
    rw [hm_eq] at heven
    rcases hodd with ⟨a, ha⟩
    rcases heven with ⟨b, hb⟩
    omega

lemma image_sum_set (k m b a : ℕ) (hm : m ≥ 3) (hm_odd : Odd m) (s1 s2 : Finset ℕ) (hs1 : s1 ⊆ Iic k) (hs2 : s2 ⊆ Iio k)
  (h_b : ∑ i ∈ s1, 2^i = b) (h_a : ∑ i ∈ s2, 2^i = a) :
  ∃ s : Finset ℕ, (∀ x ∈ s, (∃ i ≤ k, x = 2^i) ∨ (∃ i < k, x = 2^i * m)) ∧ ∑ x ∈ s, x = a * m + b := by
  let sA := s1.image (fun i => 2^i)
  let sB := s2.image (fun i => 2^i * m)
  use sA ∪ sB
  have sumA : ∑ x ∈ sA, x = b := by
    dsimp [sA]
    rw [← h_b, sum_image]
    intro x _ y _ hxy
    exact Nat.pow_right_injective (by decide) hxy
  have sumB : ∑ x ∈ sB, x = a * m := by
    dsimp [sB]
    rw [← h_a, sum_image, sum_mul]
    intro x _ y _ hxy
    have : 2^x = 2^y := Nat.eq_of_mul_eq_mul_right (by omega) hxy
    exact Nat.pow_right_injective (by decide) this
  have hdisj : Disjoint sA sB := by
    rw [disjoint_iff_ne]
    intro x hx y hy
    dsimp [sA, sB] at hx hy
    rw [mem_image] at hx hy
    rcases hx with ⟨i1, _, rfl⟩
    rcases hy with ⟨i2, _, rfl⟩
    exact pow_two_ne_pow_two_mul_m i1 i2 m hm hm_odd
  refine ⟨?_, ?_⟩
  · intro x hx
    dsimp [sA, sB] at hx
    simp only [mem_union, mem_image] at hx
    rcases hx with ⟨i1, hi1, rfl⟩ | ⟨i2, hi2, rfl⟩
    · left
      use i1
      have := hs1 hi1
      simp only [mem_Iic] at this
      exact ⟨this, rfl⟩
    · right
      use i2
      have := hs2 hi2
      simp only [mem_Iio] at this
      exact ⟨this, rfl⟩
  · rw [sum_union hdisj, sumA, sumB]
    omega

lemma sum_subset_D (n : ℕ) (hperf : n.Perfect) (s : Finset ℕ) (hs : s ⊆ n.properDivisors) :
  ∑ x ∈ s, x ≤ n := by
  have : ∑ x ∈ s, x ≤ ∑ x ∈ n.properDivisors, x := sum_le_sum_of_subset_of_nonneg hs (fun _ _ => by omega)
  have eq_n := (Nat.perfect_iff_sum_properDivisors hperf.right).mp hperf
  omega

lemma S_subset_Iic (n : ℕ) (hperf : n.Perfect) :
  (n.properDivisors.powerset.image (fun s : Finset ℕ => s.sum _root_.id)) ⊆ Iic n := by
  intro y hy
  rw [mem_image] at hy
  rcases hy with ⟨s, hs, rfl⟩
  rw [mem_Iic]
  rw [mem_powerset] at hs
  exact sum_subset_D n hperf s hs

lemma in_properDivisors (k m x : ℕ) (hk : k ≥ 1) (hm3 : m ≥ 3)
  (hx : (∃ i ≤ k, x = 2^i) ∨ (∃ i < k, x = 2^i * m)) : x ∈ (2^k * m).properDivisors := by
  rw [mem_properDivisors]
  rcases hx with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
  · refine ⟨?_, ?_⟩
    · exact dvd_mul_of_dvd_left (pow_dvd_pow 2 hi) m
    · have h1 : 2^i ≤ 2^k := Nat.pow_le_pow_right (by decide) hi
      have h2 : 2^k < 2^k * 3 := by
        have : 2^k > 0 := by positivity
        nlinarith
      have h3 : 2^k * 3 ≤ 2^k * m := by
        have : 2^k > 0 := by positivity
        nlinarith
      omega
  · refine ⟨?_, ?_⟩
    · exact mul_dvd_mul (pow_dvd_pow 2 (by omega)) dvd_rfl
    · have h1 : 2^i < 2^k := Nat.pow_lt_pow_right (by decide) hi
      have : 0 < m := by omega
      have : 2^i * m < 2^k * m := Nat.mul_lt_mul_of_pos_right h1 this
      exact this

lemma Iic_subset_S (n : ℕ) (h0 : n > 0) (heven : Even n) (hperf : n.Perfect) :
  Iic n ⊆ (n.properDivisors.powerset.image (fun s : Finset ℕ => s.sum _root_.id)) := by
  intro y hy
  have hy_le : y ≤ n := mem_Iic.mp hy
  obtain ⟨k, m, hk, hodd, hn⟩ := factor_even n h0.ne' heven
  have hm0 : m > 0 := by
    by_contra! h
    have : m = 0 := by omega
    subst this
    have : n = 0 := by omega
    omega
  have hm_eq := m_eq_pow_sub_one k m hk hodd hm0 (by rw [← hn] ; exact hperf)
  have hm3 : m ≥ 3 := by
    rw [hm_eq]
    have : 1 + 1 ≤ k + 1 := by omega
    have h2 : 2^2 ≤ 2^(k+1) := Nat.pow_le_pow_right (by decide) this
    omega
  by_cases hy_n : y = n
  · rw [mem_image]
    use n.properDivisors
    refine ⟨?_, ?_⟩
    · rw [mem_powerset]
    · rw [hy_n]
      exact (Nat.perfect_iff_sum_properDivisors h0).mp hperf
  have hy_lt : y < 2^k * m := by
    rw [← hn]
    exact lt_of_le_of_ne hy_le hy_n
  let b := y % m
  let a := y / m
  have hy_eq : y = a * m + b := by
    have : y = m * a + b := (Nat.div_add_mod y m).symm
    rw [mul_comm m a] at this
    exact this
  have hb_lt : b < m := Nat.mod_lt _ (by omega)
  have hb_lt2 : b < 2^(k+1) := by
    have : m < 2^(k+1) := by rw [hm_eq]; omega
    exact lt_trans hb_lt this
  have ha_lt : a < 2^k := by
    by_contra! h
    have h_le : 2^k * m ≤ a * m := Nat.mul_le_mul_right m h
    have h1 : 2^k * m ≤ y := by
      rw [hy_eq]
      exact le_trans h_le (Nat.le_add_right _ _)
    exact absurd hy_lt (not_lt_of_ge h1)
  obtain ⟨s1, hs1, hb⟩ := binary_sum k b hb_lt2
  have ha_lt2 : a < 2^(k-1+1) := by
    have : k - 1 + 1 = k := by omega
    rw [this]
    exact ha_lt
  obtain ⟨s2, hs2, ha⟩ := binary_sum (k-1) a ha_lt2
  have hs2_lt : s2 ⊆ Iio k := by
    intro x hx
    have : x ≤ k - 1 := mem_Iic.mp (hs2 hx)
    rw [mem_Iio]
    omega
  obtain ⟨s, hs, hsum⟩ := image_sum_set k m b a hm3 hodd s1 s2 hs1 hs2_lt hb ha
  rw [mem_image]
  use s
  refine ⟨?_, ?_⟩
  · rw [mem_powerset]
    intro x hx
    rw [hn]
    exact in_properDivisors k m x hk hm3 (hs x hx)
  · rw [hy_eq, ← hsum]
    rfl
