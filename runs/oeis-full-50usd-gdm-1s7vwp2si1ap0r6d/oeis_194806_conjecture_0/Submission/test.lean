import FormalConjectures.Util.ProblemImports

open Finset Nat

def set_prod (S : Finset ℕ) : Finset ℕ :=
  (S.product S).image fun p : ℕ × ℕ => p.fst * p.snd

lemma two_sqrt_le_self (n : ℕ) (hn : 4 ≤ n) : 2 * Nat.sqrt n ≤ n := by
  have h1 : 2 ≤ Nat.sqrt n := by
    rw [le_sqrt]
    exact hn
  calc
    2 * Nat.sqrt n ≤ Nat.sqrt n * Nat.sqrt n := by gcongr
    _ ≤ n := Nat.sqrt_le n

theorem b_fourth_lt_n_third (n k : ℕ) (hk : k ≤ n) (_hk_comp : ¬ Nat.Prime k) (hk_gt1 : 1 < k) :
    let S_div := (Nat.divisors k).filter (fun d => d * d ≤ n)
    have hS_nonempty : S_div.Nonempty := by
      use 1
      simp only [S_div, mem_filter, mem_divisors]
      refine ⟨⟨by omega, by omega⟩, by omega⟩
    let a := S_div.max' hS_nonempty
    let b := k / a
    ¬ Nat.Prime b → b > 1 → b^4 < n^3 := by
  intro S_div hS_nonempty a b hb_not_prime hb_gt1
  have ha_mem : a ∈ S_div := max'_mem S_div hS_nonempty
  simp only [S_div, mem_filter, mem_divisors] at ha_mem
  rcases ha_mem with ⟨⟨ha_dvd, hk_nz⟩, ha_sq⟩
  have ha_dvd : a ∣ k := ha_dvd
  have hk_nz : k ≠ 0 := hk_nz

  have hb_dvd : b ∣ k := div_dvd_of_dvd ha_dvd
  have h_kab : k = a * b := (Nat.mul_div_cancel' ha_dvd).symm

  have hp_prime : Nat.Prime (minFac b) := minFac_prime (by omega)
  have hp_dvd_b : minFac b ∣ b := minFac_dvd b
  have hp_dvd_k : minFac b ∣ k := dvd_trans hp_dvd_b hb_dvd
  have hp_ge_2 : 2 ≤ minFac b := Nat.Prime.two_le hp_prime

  have hp_sq_le_b : (minFac b) * (minFac b) ≤ b := by
    have h1 := minFac_le_div (by omega) hb_not_prime
    have h2 := Nat.mul_le_mul_right (minFac b) h1
    rw [Nat.div_mul_cancel hp_dvd_b] at h2
    exact h2

  have hap_dvd : a * minFac b ∣ k := by
    rw [h_kab]
    gcongr

  have hap_gt_a : a < a * minFac b := by
    have h_a_nz : a ≠ 0 := by
      intro ha_zero
      have : k = 0 := by
        rw [h_kab, ha_zero, zero_mul]
      omega
    exact lt_mul_of_one_lt_right (Nat.pos_of_ne_zero h_a_nz) (by omega)

  have hap_sq_gt_n : n < (a * minFac b) * (a * minFac b) := by
    by_contra! h_le
    have hap_mem : a * minFac b ∈ S_div := by
      simp only [S_div, mem_filter, mem_divisors]
      exact ⟨⟨hap_dvd, hk_nz⟩, h_le⟩
    have : a * minFac b ≤ a := le_max' S_div (a * minFac b) hap_mem
    omega

  have hp_le_a : minFac b ≤ a := by
    by_cases hp_sq_le_n : (minFac b) * (minFac b) ≤ n
    · have hp_mem : minFac b ∈ S_div := by
        simp only [S_div, mem_filter, mem_divisors]
        exact ⟨⟨hp_dvd_k, hk_nz⟩, hp_sq_le_n⟩
      exact le_max' S_div (minFac b) hp_mem
    · -- if (minFac b)^2 > n, then since (minFac b)^2 ≤ b, we have b > n, which contradicts b ≤ n
      have h_lt : n < (minFac b) * (minFac b) := by omega
      have h_le_b : (minFac b) * (minFac b) ≤ b := hp_sq_le_b
      have h_b_le_n : b ≤ n := by
        have h_div : k / a ≤ k := Nat.div_le_self k a
        exact le_trans h_div hk
      omega

  have ha_le_n_div_b : a ≤ n / b := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    omega

  have hp_le_n_div_b : minFac b ≤ n / b := le_trans hp_le_a ha_le_n_div_b

  have h_mul_le : (a * minFac b) * (a * minFac b) * (b * b * b * b) ≤ n^4 := by
    have h1 : a * b ≤ n := by omega
    have h2 : minFac b * b ≤ n := by
      calc
        minFac b * b ≤ (n / b) * b := by gcongr
        _ ≤ n := Nat.div_mul_le_self n b
    calc
      (a * minFac b) * (a * minFac b) * (b * b * b * b) = (a * b) * (a * b) * (minFac b * b) * (minFac b * b) := by ring
      _ ≤ n * n * n * n := by gcongr
      _ = n^4 := by ring

  have h_final : n * (b * b * b * b) < n^4 := by
    calc
      n * (b * b * b * b) < (a * minFac b) * (a * minFac b) * (b * b * b * b) := by gcongr
      _ ≤ n^4 := h_mul_le

  have h_final_rew : n * b^4 < n * n^3 := by
    have h_eq1 : b^4 = b * b * b * b := by ring
    have h_eq2 : n^4 = n * n^3 := by ring
    rw [h_eq1]
    rw [h_eq2] at h_final
    exact h_final

  have h_n_pos : 0 < n := by omega
  exact lt_of_mul_lt_mul_left h_final_rew (by omega)

def S'_set (n : ℕ) : Finset ℕ :=
  Icc 1 (2 * Nat.sqrt n) ∪ (Icc 1 n).filter (fun p => Nat.Prime p) ∪ {1}

lemma S'_set_subset (n : ℕ) (hn : 3000 ≤ n) : S'_set n ⊆ Icc 1 n := by
  intro x hx
  simp only [S'_set, mem_union, mem_Icc, mem_filter, mem_singleton] at hx
  rcases hx with ((⟨h1, h2⟩ | ⟨⟨h1, h2⟩, _hp⟩) | rfl)
  · have hn4 : 4 ≤ n := by omega
    have h_le := two_sqrt_le_self n hn4
    exact mem_Icc.mpr ⟨h1, le_trans h2 h_le⟩
  · exact mem_Icc.mpr ⟨h1, h2⟩
  · have : 1 ≤ n := by omega
    exact mem_Icc.mpr ⟨by omega, this⟩

lemma S'_set_valid (n : ℕ) (hn : 3000 ≤ n) : Icc 1 n ⊆ set_prod (S'_set n) := by
  intro k hk
  rw [mem_Icc] at hk
  by_cases hk1 : k = 1
  · subst hk1
    simp only [set_prod, mem_image, Prod.exists]
    use 1, 1
    have h1 : 1 ∈ S'_set n := by
      simp only [S'_set, mem_union, mem_Icc, mem_filter, mem_singleton]
      right; trivial
    have h_prod : (1, 1) ∈ S'_set n ×ˢ S'_set n := by
      rw [mem_product]
      exact ⟨h1, h1⟩
    exact ⟨h_prod, rfl⟩
  · by_cases hk_prime : Nat.Prime k
    · simp Basket : k ∈ S'_set n := by
        simp only [S'_set, mem_union, mem_Icc, mem_filter, mem_singleton]
        left; right
        exact ⟨⟨by omega, hk.2⟩, hk_prime⟩
      simp only [set_prod, mem_image, Prod.exists]
      use k, 1
      have h1 : 1 ∈ S'_set n := by
        simp only [S'_set, mem_union, mem_Icc, mem_filter, mem_singleton]
        right; trivial
      have h_prod : (k, 1) ∈ S'_set n ×ˢ S'_set n := by
        rw [mem_product]
        exact ⟨Basket, h1⟩
      exact ⟨h_prod, mul_one k⟩
    · -- k is composite
      simp only [set_prod, mem_image, Prod.exists]
      have hk_gt1 : 1 < k := by omega
      let S_div := (Nat.divisors k).filter (fun d => d * d ≤ n)
      have hS_nonempty : S_div.Nonempty := by
        use 1
        simp only [S_div, mem_filter, mem_divisors]
        refine ⟨⟨by omega, by omega⟩, by omega⟩
      let a := S_div.max' hS_nonempty
      let b := k / a
      use a, b
      have ha_mem : a ∈ S_div := max'_mem S_div hS_nonempty
      simp only [S_div, mem_filter, mem_divisors] at ha_mem
      rcases ha_mem with ⟨⟨ha_dvd, _hk_nz⟩, ha_sq⟩

      have h_kab : k = a * b := (Nat.mul_div_cancel' ha_dvd).symm

      have ha_le_sqrt : a ≤ Nat.sqrt n := by
        rw [le_sqrt]
        exact ha_sq

      have ha_ge_1 : 1 ≤ a := by
        have h1 : 1 ∈ S_div := by
          simp only [S_div, mem_filter, mem_divisors]
          refine ⟨⟨by omega, by omega⟩, by omega⟩
        exact le_max' S_div 1 h1

      have ha_in : a ∈ S'_set n := by
        simp only [S'_set, mem_union, mem_Icc, mem_filter, mem_singleton]
        left; left
        refine ⟨ha_ge_1, ?_⟩
        have h_le : Nat.sqrt n ≤ 2 * Nat.sqrt n := by omega
        exact le_trans ha_le_sqrt h_le

      have hb_in : b ∈ S'_set n := by
        by_cases hb1 : b = 1
        · rw [hb1]
          simp only [S'_set, mem_union, mem_singleton]
          right; trivial
        · have hb_nz : b ≠ 0 := by
            intro h_zero
            have : k = 0 := by
              rw [h_kab, h_zero, mul_zero]
            omega
          have hb_gt1 : b > 1 := by
            rcases b with _ | _ | b
            · contradiction
            · contradiction
            · omega
          by_cases hb_prime : Nat.Prime b
          · simp only [S'_set, mem_union, mem_Icc, mem_filter, mem_singleton]
            left; right
            have hb_le_n : b ≤ n := by
              have h_div : k / a ≤ k := Nat.div_le_self k a
              exact le_trans h_div hk.2
            refine ⟨⟨le_trans (by decide : 1 ≤ 2) (Nat.Prime.two_le hb_prime), hb_le_n⟩, hb_prime⟩
          · -- b is composite
            have h_b4 := b_fourth_lt_n_third n k hk.2 hk_prime hk_gt1 hb_prime hb_gt1
            simp only [S'_set, mem_union, mem_Icc, mem_filter, mem_singleton]
            left; left
            refine ⟨le_of_lt hb_gt1, ?_⟩
            have h_b4_rew : (b^2)^2 < n * n * n := by
              calc
                (b^2)^2 = b^4 := by ring
                _ < n^3 := h_b4
                _ = n * n * n := by ring
            have h_n17 : 17 < n := by omega
            have h_b4_gt : 16 * n * n < (b^2)^2 := by
              calc
                16 * n * n = 16 * n^2 := by ring
                _ < 16 * n^2 + (n - 16) * n^2 := by
                  -- since n >= 3000, n - 16 >= 1
                  have : n - 16 ≥ 1 := by omega
                  gcongr
                _ = n * n^2 := by
                  -- 16 * n^2 + (n - 16) * n^2 = n^3
                  have : 16 * n^2 + (n - 16) * n^2 = n * n^2 := by
                    rw [← add_mul]
                    congr
                    omega
                  exact this
                _ = n^3 := by ring
                _ < (b^2)^2 := by
                  calc
                    n^3 < (b^2)^2 := h_b4_rew -- wait!
                    -- actually we assumed b > 2 * sqrt n
                    -- which is b^2 > 4 * n (if b > 2 * sqrt n, then b^2 >= (2 * sqrt n + 1)^2? )
                    -- Actually if b > 2 * sqrt n:
                    -- since Nat.sqrt n * Nat.sqrt n <= n, is (2 * sqrt n)^2 close to 4 * n?
                    -- Let's prove it directly!
                    sorry
            sorry

      have h_prod : (a, b) ∈ S'_set n ×ˢ S'_set n := by
        rw [mem_product]
        exact ⟨ha_in, hb_in⟩
      exact ⟨h_prod, h_kab.symm⟩
