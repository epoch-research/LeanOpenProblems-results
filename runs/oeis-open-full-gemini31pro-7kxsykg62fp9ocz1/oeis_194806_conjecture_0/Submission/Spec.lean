import FormalConjectures.Util.ProblemImports

open Finset Nat

/-- The set of all products of elements from a Finset S. -/
def set_prod (S : Finset ℕ) : Finset ℕ :=
  (S.product S).image fun p : ℕ × ℕ => p.fst * p.snd

noncomputable def a (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    let T_n := Icc 1 n
    let valid_subsets : Finset (Finset ℕ) :=
      T_n.powerset.filter (fun S : Finset ℕ => T_n ⊆ set_prod S)
    have T_n_is_valid : T_n ∈ valid_subsets := by
      apply mem_filter.mpr
      constructor
      apply mem_powerset.mpr; rfl
      intro k hk
      have one_le_n : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h)
      have h1 : 1 ∈ T_n := mem_Icc.mpr ⟨Nat.le_refl 1, one_le_n⟩
      simp only [set_prod, mem_image, Prod.exists]
      use k, 1
      constructor
      · exact mem_product.mpr ⟨hk, h1⟩
      · exact Nat.mul_one k
    have h_nonempty : valid_subsets.Nonempty := ⟨T_n, T_n_is_valid⟩
    let sizes := valid_subsets.image Finset.card
    have h_sizes_nonempty : sizes.Nonempty := h_nonempty.image Finset.card
    sizes.min' h_sizes_nonempty




lemma a_le_n (n : ℕ) : a n ≤ n := by
  by_cases hn : n = 0
  · subst hn
    simp [a]
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    rw [a]
    simp only [hn, not_false_eq_true, dif_neg]
    let T_n := Icc 1 n
    let valid_subsets : Finset (Finset ℕ) :=
      T_n.powerset.filter (fun S : Finset ℕ => T_n ⊆ set_prod S)
    have T_n_is_valid : T_n ∈ valid_subsets := by
      apply mem_filter.mpr
      constructor
      apply mem_powerset.mpr; rfl
      intro k hk
      have one_le_n : 1 ≤ n := Nat.succ_le_of_lt hn_pos
      have h1 : 1 ∈ T_n := mem_Icc.mpr ⟨Nat.le_refl 1, one_le_n⟩
      simp only [set_prod, mem_image, Prod.exists]
      use k, 1
      constructor
      · exact mem_product.mpr ⟨hk, h1⟩
      · exact Nat.mul_one k
    let sizes := valid_subsets.image Finset.card
    have h_in_sizes : (Icc 1 n).card ∈ sizes := mem_image.mpr ⟨Icc 1 n, T_n_is_valid, rfl⟩
    calc sizes.min' (⟨(Icc 1 n).card, h_in_sizes⟩) ≤ (Icc 1 n).card := Finset.min'_le _ _ h_in_sizes
      _ = n := by rw [Nat.card_Icc, Nat.add_sub_cancel]

lemma a_le_n_real (n : ℕ) : (a n : ℝ) ≤ n := by
  exact_mod_cast a_le_n n

lemma prime_count_eq_Icc (n : ℕ) : (filter Nat.Prime (Icc 1 n)).card = primeCounting n := by
  rw [primeCounting, primeCounting', count_eq_card_filter_range]
  congr 1
  ext x
  simp only [mem_filter, mem_Icc, mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨Nat.lt_succ_of_le h2, h3⟩
  · rintro ⟨h1, h2⟩
    have hx0 : 1 ≤ x := by
      by_cases hx : x = 0
      · exfalso; subst hx; exact Nat.not_prime_zero h2
      · exact Nat.pos_of_ne_zero hx
    exact ⟨⟨hx0, Nat.le_of_lt_succ h1⟩, h2⟩

lemma a_le_K (n K : ℕ) (hK : K ≤ n) (h_cover : ∀ m ∈ Icc 1 n, ∃ x y, x ∈ filter Nat.Prime (Icc 1 n) ∪ Icc 1 K ∧ y ∈ filter Nat.Prime (Icc 1 n) ∪ Icc 1 K ∧ x * y = m) :
  a n ≤ primeCounting n + K := by
  by_cases hn : n = 0
  · subst hn
    simp [a]
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    let S := filter Nat.Prime (Icc 1 n) ∪ Icc 1 K
    have h_S_sub : S ⊆ Icc 1 n := by
      intro x hx
      simp only [S, mem_union, mem_filter, mem_Icc] at hx
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact mem_Icc.mpr h1
      · exact mem_Icc.mpr ⟨h1, le_trans h2 hK⟩
    
    have h_valid : S ∈ filter (fun S : Finset ℕ => Icc 1 n ⊆ set_prod S) (Icc 1 n).powerset := by
      rw [mem_filter, mem_powerset]
      refine ⟨h_S_sub, ?_⟩
      intro m hm
      obtain ⟨x, y, hx, hy, hxy⟩ := h_cover m hm
      simp only [set_prod, mem_image, Prod.exists]
      use x, y
      have hxy_prod : (x, y) ∈ S.product S := mem_product.mpr ⟨hx, hy⟩
      exact ⟨hxy_prod, hxy⟩
    
    have h_min : a n ≤ S.card := by
      rw [a]
      simp only [hn, not_false_eq_true, dif_neg]
      let valid_subsets := filter (fun S : Finset ℕ => Icc 1 n ⊆ set_prod S) (Icc 1 n).powerset
      have h_in_sizes : S.card ∈ valid_subsets.image Finset.card := mem_image.mpr ⟨S, h_valid, rfl⟩
      exact Finset.min'_le _ _ h_in_sizes
      
    calc a n ≤ S.card := h_min
      _ ≤ (filter Nat.Prime (Icc 1 n)).card + (Icc 1 K).card := card_union_le _ _
      _ = (filter Nat.Prime (Icc 1 n)).card + K := by
        by_cases hK0 : K = 0
        · subst hK0; simp
        · rw [Nat.card_Icc, Nat.add_sub_cancel]
      _ = primeCounting n + K := by rw [prime_count_eq_Icc n]

lemma max_div_exists (m K : ℕ) (h : 1 ≤ K) : ∃ d, d ∣ m ∧ d ≤ K ∧ ∀ x, x ∣ m → x ≤ K → x ≤ d := by
  let S := (filter (fun x => x ∣ m) (Icc 1 K))
  have hS : S.Nonempty := by
    use 1
    simp [S, h]
  use S.max' hS
  have h_mem : S.max' hS ∈ S := max'_mem S hS
  simp only [S, mem_filter, mem_Icc] at h_mem
  refine ⟨h_mem.2, h_mem.1.2, ?_⟩
  intro x hx1 hx2
  by_cases hx0 : x = 0
  · subst hx0; exact Nat.zero_le _
  · have hx_mem : x ∈ S := by
      simp only [S, mem_filter, mem_Icc]
      refine ⟨⟨Nat.pos_of_ne_zero hx0, hx2⟩, hx1⟩
    exact le_max' S x hx_mem

lemma mul_le_div_of_le_of_le (a b c d : ℕ) (hd : 0 < d) (h1 : a ≤ c / d) (h2 : b ≤ c / d) : a * b ≤ c * c / (d * d) := by
  have h3 : a * d ≤ c := Nat.mul_le_of_le_div d a c h1
  have h4 : b * d ≤ c := Nat.mul_le_of_le_div d b c h2
  have h5 : (a * d) * (b * d) ≤ c * c := Nat.mul_le_mul h3 h4
  have h6 : a * b * (d * d) ≤ c * c := by nlinarith
  have hdd : 0 < d * d := Nat.mul_pos hd hd
  exact (Nat.le_div_iff_mul_le hdd).mpr h6

lemma gap_lemma (m K : ℕ) (hK1 : 1 ≤ K) (h_m0 : 0 < m) (h_pmax : ∀ p, p.Prime → p ∣ m → p ≤ m / K) (h_m : m ^ 2 ≤ K ^ 3) :
  ∃ d, d ∣ m ∧ d ≤ K ∧ m / d ≤ K := by
  obtain ⟨d, hd1, hd2, hd3⟩ := max_div_exists m K hK1
  use d
  refine ⟨hd1, hd2, ?_⟩
  by_cases hmd : m / d ≤ K
  · exact hmd
  · exfalso
    have hmd_gt : K < m / d := not_le.mp hmd
    have h_md_gt1 : 1 < m / d := by omega
    obtain ⟨q, hq_prime, hq_div⟩ := Nat.exists_prime_and_dvd h_md_gt1.ne'
    have hq_div_m : q ∣ m := Nat.dvd_trans hq_div (Nat.div_dvd_of_dvd hd1)
    have hq_bound : q ≤ m / K := h_pmax q hq_prime hq_div_m
    have hdq_div_m : d * q ∣ m := by
      rw [← Nat.mul_div_cancel' hd1]
      exact Nat.mul_dvd_mul_left d hq_div
    have hd_bound : d ≤ m / K := by
      have hdK : d * K < m := by
        calc d * K < d * (m / d) := (Nat.mul_lt_mul_left (Nat.pos_of_dvd_of_pos hd1 h_m0)).mpr hmd_gt
        _ ≤ m := Nat.mul_div_le m d
      exact (Nat.le_div_iff_mul_le (by omega)).mpr hdK.le
    have hdq_le_m2K2 : d * q ≤ m * m / (K * K) := mul_le_div_of_le_of_le d q m K (by omega) hd_bound hq_bound
    have hm2K2_le_K : m * m / (K * K) ≤ K := by
      have hk2 : 0 < K * K := Nat.mul_pos (by omega) (by omega)
      have h_m2 : m * m ≤ K * K * K := by
        calc m * m = m ^ 2 := by ring
        _ ≤ K ^ 3 := h_m
        _ = K * K * K := by ring
      exact Nat.div_le_of_le_mul h_m2
    have hdq_le_K : d * q ≤ K := le_trans hdq_le_m2K2 hm2K2_le_K
    have h_dq_gt_d : d < d * q := by
      have hq_gt1 : 1 < q := hq_prime.one_lt
      have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd1 h_m0
      nlinarith
    have h_le_d : d * q ≤ d := hd3 (d * q) hdq_div_m hdq_le_K
    omega

lemma a_le_K_bound (n K : ℕ) (hK1 : 1 ≤ K) (hK : K ≤ n) (hn : n ^ 2 ≤ K ^ 3) :
  a n ≤ primeCounting n + K := by
  apply a_le_K n K hK
  intro m hm
  simp only [mem_Icc] at hm
  by_cases h_prime : Nat.Prime m
  · use m, 1
    refine ⟨?_, ?_, by ring⟩
    · simp only [mem_union, mem_filter, mem_Icc]
      left
      exact ⟨⟨hm.1, hm.2⟩, h_prime⟩
    · simp only [mem_union, mem_filter, mem_Icc]
      right
      exact ⟨le_rfl, hK1⟩
  · by_cases h_mK : m ≤ K
    · use m, 1
      refine ⟨?_, ?_, by ring⟩
      · simp only [mem_union, mem_filter, mem_Icc]
        right
        exact ⟨hm.1, h_mK⟩
      · simp only [mem_union, mem_filter, mem_Icc]
        right
        exact ⟨le_rfl, hK1⟩
    · have h_not_mK : K < m := not_le.mp h_mK
      have hm_2_K_3 : m ^ 2 ≤ K ^ 3 := by
        calc m ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hm.2 2
        _ ≤ K ^ 3 := hn
      by_cases h_pmax : ∀ p, p.Prime → p ∣ m → p ≤ m / K
      · obtain ⟨d, hd1, hd2, hd3⟩ := gap_lemma m K hK1 (by omega) h_pmax hm_2_K_3
        use d, m / d
        refine ⟨?_, ?_, Nat.mul_div_cancel' hd1⟩
        · simp only [mem_union, mem_filter, mem_Icc]
          right
          have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd1 (by omega)
          exact ⟨hd_pos, hd2⟩
        · simp only [mem_union, mem_filter, mem_Icc]
          right
          have hd_le : d ≤ m := Nat.le_of_dvd (by omega) hd1
          have h_div_pos : 0 < m / d := Nat.div_pos hd_le (Nat.pos_of_dvd_of_pos hd1 (by omega))
          exact ⟨h_div_pos, hd3⟩
      · push_neg at h_pmax
        obtain ⟨p, hp, hpm, hpgt⟩ := h_pmax
        use p, m / p
        refine ⟨?_, ?_, Nat.mul_div_cancel' hpm⟩
        · simp only [mem_union, mem_filter, mem_Icc]
          left
          exact ⟨⟨hp.pos, le_trans (Nat.le_of_dvd (by omega) hpm) hm.2⟩, hp⟩
        · simp only [mem_union, mem_filter, mem_Icc]
          right
          have h_div_K : m / p ≤ K := by
            have hpK : m / K < p := hpgt
            have hkpos : 0 < K := by omega
            have h_p_K : m / K * K < p * K := (Nat.mul_lt_mul_right hkpos).mpr hpK
            by_cases hK_div : K < m / p
            · have h_K_add : K + 1 ≤ m / p := hK_div
              have h_p_K_add : p * (K + 1) ≤ p * (m / p) := Nat.mul_le_mul_left p h_K_add
              have h_p_m_p : p * (m / p) = m := Nat.mul_div_cancel' hpm
              have h_p_K_add_m : p * K + p ≤ m := by
                calc p * K + p = p * (K + 1) := by ring
                _ ≤ p * (m / p) := h_p_K_add
                _ = m := h_p_m_p
              have h_mod : K * (m / K) + m % K = m := Nat.div_add_mod m K
              have hm_k_mul : K * (m / K) ≤ m := by omega
              have h_m_K : m / K + 1 ≤ p := hpK
              have h_m_K_mul : (m / K + 1) * K ≤ p * K := Nat.mul_le_mul_right K h_m_K
              have h_m_K_mul2 : K * (m / K) + K ≤ p * K := by
                calc K * (m / K) + K = (m / K + 1) * K := by ring
                _ ≤ p * K := h_m_K_mul
              have h_contra2 : K * (m / K) + K + p ≤ m := by omega
              have h_mod3 : K + p ≤ m % K := by omega
              have h_mod_lt : m % K < K := Nat.mod_lt m hkpos
              omega
            · exact not_lt.mp hK_div
          have h_div_pos : 0 < m / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpm) hp.pos
          exact ⟨h_div_pos, h_div_K⟩

lemma prime_count_eq_test (n : ℕ) : (filter Nat.Prime (range (n + 1))).card = primeCounting n := by
  rw [primeCounting, primeCounting', count_eq_card_filter_range]

lemma choose_le_prod (n k : ℕ) (hkn : k ≤ n) (hn : 0 < n) : choose n k ≤ n ^ (primeCounting n) := by
  calc choose n k = ∏ p ∈ range (n + 1), p ^ (choose n k).factorization p := (prod_pow_factorization_choose n k hkn).symm
    _ = ∏ p ∈ filter Nat.Prime (range (n + 1)), p ^ (choose n k).factorization p := by
      symm
      apply prod_filter_of_ne
      intro p _ hp1
      by_contra hc
      have h0 : (choose n k).factorization p = 0 := factorization_eq_zero_of_not_prime _ hc
      rw [h0, pow_zero] at hp1
      exact hp1 rfl
    _ ≤ ∏ p ∈ filter Nat.Prime (range (n + 1)), n := by
      apply prod_le_prod'
      intro p _
      exact pow_factorization_choose_le hn
    _ = n ^ (primeCounting n) := by
      rw [prod_const, prime_count_eq_test]

lemma two_pow_le_mul_choose (n : ℕ) : 2 ^ n ≤ (n + 1) * choose n (n / 2) := by
  calc 2 ^ n = ∑ m ∈ range (n + 1), choose n m := (sum_range_choose n).symm
    _ ≤ ∑ m ∈ range (n + 1), choose n (n / 2) := by
      apply sum_le_sum
      intro m _
      exact choose_le_middle m n
    _ = (n + 1) * choose n (n / 2) := by
      simp

lemma two_pow_le_mul_n_pow_pi (n : ℕ) (hn : 0 < n) : 2 ^ n ≤ (n + 1) * n ^ (primeCounting n) := by
  calc 2 ^ n ≤ (n + 1) * choose n (n / 2) := two_pow_le_mul_choose n
    _ ≤ (n + 1) * n ^ (primeCounting n) := Nat.mul_le_mul_left (n + 1) (choose_le_prod n (n / 2) (Nat.div_le_self n 2) hn)

set_option exponentiation.threshold 10000

lemma m_bound_1 (m : ℕ) (hm : 17 ≤ m) : 3 + 3 * (m + 1) ^ 2 ≤ 4 * m ^ 2 := by
  nlinarith

lemma m_bound_2 (m : ℕ) (hm : 17 ≤ m) : (m + 1) ^ 4 < 2 ^ m := by
  induction' m, hm using Nat.le_induction with k hk ih
  · decide
  · have h1 : (k + 1 + 1) ^ 4 ≤ 2 * (k + 1) ^ 4 := by
      calc (k + 1 + 1) ^ 4 = k^4 + 8*k^3 + 24*k^2 + 32*k + 16 := by ring
        _ ≤ 2*k^4 + 8*k^3 + 12*k^2 + 8*k + 2 := by
          have hk24 : 24 ≤ k * k := by nlinarith
          have hk2 : 24 * k ^ 2 ≤ k ^ 4 := by
            calc 24 * k ^ 2 ≤ (k * k) * k ^ 2 := Nat.mul_le_mul_right (k^2) hk24
              _ = k ^ 4 := by ring
          have hk32 : 32 * k ≤ k ^ 4 := by
            calc 32 * k ≤ (k * k * k) * k := Nat.mul_le_mul_right k (by nlinarith)
              _ = k ^ 4 := by ring
          have hk16 : 16 ≤ k ^ 4 := by nlinarith
          nlinarith
        _ = 2 * (k + 1) ^ 4 := by ring
    calc (k + 1 + 1) ^ 4 ≤ 2 * (k + 1) ^ 4 := h1
      _ < 2 * 2 ^ k := (Nat.mul_lt_mul_left (by omega)).mpr ih
      _ = 2 ^ (k + 1) := by ring

lemma m_bound_main (m : ℕ) (hm : 17 ≤ m) : (m + 1) ^ (3 + 3 * (m + 1) ^ 2) < 2 ^ (m ^ 3) := by
  calc (m + 1) ^ (3 + 3 * (m + 1) ^ 2) ≤ (m + 1) ^ (4 * m ^ 2) := Nat.pow_le_pow_right (by omega) (m_bound_1 m hm)
    _ = ((m + 1) ^ 4) ^ (m ^ 2) := by rw [← Nat.pow_mul]
    _ < (2 ^ m) ^ (m ^ 2) := Nat.pow_lt_pow_left (m_bound_2 m hm) (by nlinarith)
    _ = 2 ^ (m ^ 3) := by rw [← Nat.pow_mul]; congr 1; ring

lemma x_bound_lt (x m : ℕ) (hx : x ^ 3 < (m + 1) ^ 6) : x < (m + 1) ^ 2 := by
  by_contra hc
  have hc2 : (m + 1) ^ 2 ≤ x := not_lt.mp hc
  have hc3 : ((m + 1) ^ 2) ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left hc2 3
  have hc4 : (m + 1) ^ 6 ≤ x ^ 3 := by
    calc (m + 1) ^ 6 = ((m + 1) ^ 2) ^ 3 := by ring
      _ ≤ x ^ 3 := hc3
  omega

lemma main_contradiction_x (n x m : ℕ) (hm : 17 ≤ m) (hn_le : m ^ 3 ≤ n) (hn_lt : n < (m + 1) ^ 3) (hx : x ^ 3 ≤ n ^ 2) : (n + 1) * n ^ x < 2 ^ n := by
  have hx2 : x ^ 3 < (m + 1) ^ 6 := by
    calc x ^ 3 ≤ n ^ 2 := hx
      _ < ((m + 1) ^ 3) ^ 2 := Nat.pow_lt_pow_left hn_lt (by omega)
      _ = (m + 1) ^ 6 := by ring
  have hx5 : x ≤ (m + 1) ^ 2 := by
    have hx4 := x_bound_lt x m hx2
    omega
  have hn_bound1 : n + 1 ≤ (m + 1) ^ 3 := hn_lt
  have hn_bound2 : n ^ x ≤ ((m + 1) ^ 3) ^ ((m + 1) ^ 2) := by
    calc n ^ x ≤ ((m + 1) ^ 3) ^ x := Nat.pow_le_pow_left (by omega) _
      _ ≤ ((m + 1) ^ 3) ^ ((m + 1) ^ 2) := Nat.pow_le_pow_right (by omega) hx5
  have h_prod : (n + 1) * n ^ x ≤ (m + 1) ^ (3 + 3 * (m + 1) ^ 2) := by
    calc (n + 1) * n ^ x ≤ (m + 1) ^ 3 * ((m + 1) ^ 3) ^ ((m + 1) ^ 2) := Nat.mul_le_mul hn_bound1 hn_bound2
      _ = (m + 1) ^ 3 * (m + 1) ^ (3 * (m + 1) ^ 2) := by rw [← Nat.pow_mul]
      _ = (m + 1) ^ (3 + 3 * (m + 1) ^ 2) := by rw [← Nat.pow_add]
  have h_2_m3 : 2 ^ (m ^ 3) ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn_le
  calc (n + 1) * n ^ x ≤ (m + 1) ^ (3 + 3 * (m + 1) ^ 2) := h_prod
    _ < 2 ^ (m ^ 3) := m_bound_main m hm
    _ ≤ 2 ^ n := h_2_m3

lemma exists_cube_root (n : ℕ) : ∃ m : ℕ, m ^ 3 ≤ n ∧ n < (m + 1) ^ 3 := by
  have h : ∃ k, n < k ^ 3 := by
    use n + 1
    have H : n + 1 ≤ (n + 1) ^ 3 := by
      calc n + 1 = (n + 1) ^ 1 := by ring
        _ ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  let m := (Nat.find h) - 1
  have h1 : (m + 1) = Nat.find h := by
    have h_pos : 0 < Nat.find h := by
      by_contra hz
      have h0 : Nat.find h = 0 := by omega
      have hn : n < 0 ^ 3 := by
        have := Nat.find_spec h
        rw [h0] at this
        exact this
      omega
    omega
  use m
  have h_spec : n < (m + 1) ^ 3 := by
    rw [h1]
    exact Nat.find_spec h
  have h_min : ¬ (n < m ^ 3) := by
    have h_lt : m < Nat.find h := by omega
    exact Nat.find_min h h_lt
  have h_le : m ^ 3 ≤ n := by omega
  exact ⟨h_le, h_spec⟩

lemma primeCounting_ge_n_two_thirds_4913 (n : ℕ) (hn : 4913 ≤ n) : n ^ 2 ≤ (primeCounting n) ^ 3 := by
  by_contra hc
  have hc2 : (primeCounting n) ^ 3 ≤ n ^ 2 := by omega
  obtain ⟨m, hm1, hm2⟩ := exists_cube_root n
  have hm_ge : 17 ≤ m := by
    by_contra hm_lt
    have : m ≤ 16 := by omega
    have : (m + 1) ^ 3 ≤ 4913 := by
      calc (m + 1) ^ 3 ≤ 17 ^ 3 := Nat.pow_le_pow_left (by omega) 3
        _ = 4913 := by norm_num
    have : n < 4913 := lt_of_lt_of_le hm2 this
    omega
  have hc3 := main_contradiction_x n (primeCounting n) m hm_ge hm1 hm2 hc2
  have hc4 := two_pow_le_mul_n_pow_pi n (by omega)
  omega

lemma hK_pos_lemma (n : ℕ) (hn : 4913 ≤ n) : 1 ≤ primeCounting n := by
  have h_le : 2 ≤ n := by omega
  have : primeCounting n ≠ 0 := by
    intro hz
    have hz2 : n ≤ 1 := primeCounting_eq_zero_iff.mp hz
    omega
  exact Nat.pos_of_ne_zero this

lemma oeis_194806_conjecture_0_proof :
  ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
    (a n : ℝ) / (Nat.primeCounting n : ℝ) ≤ C := by
  use 4913
  intro n hn
  by_cases h_small : n < 4913
  · have han : (a n : ℝ) ≤ n := a_le_n_real n
    have hn_4913 : (n : ℝ) < 4913 := by exact_mod_cast h_small
    have han_4913 : (a n : ℝ) ≤ 4913 := le_trans han hn_4913.le
    have h1 : 1 ≤ (primeCounting n : ℝ) := by 
      have h2 : 1 ≤ n.primeCounting := by
        have : primeCounting n ≠ 0 := by
          intro hz
          have hz2 : n ≤ 1 := primeCounting_eq_zero_iff.mp hz
          omega
        exact Nat.pos_of_ne_zero this
      exact_mod_cast h2
    have h1_pos : (0 : ℝ) ≤ primeCounting n := by linarith
    calc (a n : ℝ) / primeCounting n ≤ 4913 / primeCounting n := div_le_div_of_nonneg_right han_4913 h1_pos
      _ ≤ 4913 / 1 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) h1
      _ = 4913 := by norm_num
  · have hn_4913 : 4913 ≤ n := not_lt.mp h_small
    have hn_pos : 0 < n := by omega
    have K_val := primeCounting n
    have hK1 : 1 ≤ primeCounting n := hK_pos_lemma n hn_4913
    have hK_le_n : primeCounting n ≤ n := by
      have H2 : (filter Nat.Prime (Icc 1 n)).card ≤ (Icc 1 n).card := card_filter_le _ _
      rw [prime_count_eq_Icc n, Nat.card_Icc, Nat.add_sub_cancel] at H2
      exact H2
    have hn_K : n ^ 2 ≤ (primeCounting n) ^ 3 := primeCounting_ge_n_two_thirds_4913 n hn_4913
    have ha_bound := a_le_K_bound n (primeCounting n) hK1 hK_le_n hn_K
    have ha_bound_real : (a n : ℝ) ≤ 2 * (primeCounting n : ℝ) := by
      calc (a n : ℝ) ≤ (primeCounting n : ℝ) + (primeCounting n : ℝ) := by exact_mod_cast ha_bound
      _ = 2 * (primeCounting n : ℝ) := by ring
    have hK_pos : ((primeCounting n) : ℝ) > 0 := by exact_mod_cast hK1
    have res : ((a n : ℝ) / primeCounting n) ≤ 2 := (div_le_iff₀ hK_pos).mpr ha_bound_real
    exact le_trans res (by norm_num)



theorem oeis_194806_conjecture_0 :
  ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
    (a n : ℝ) / (Nat.primeCounting n : ℝ) ≤ C :=
  oeis_194806_conjecture_0_proof

theorem oeis_194806_conjecture_0.disproof : ¬ (type_of% @oeis_194806_conjecture_0) := sorry
