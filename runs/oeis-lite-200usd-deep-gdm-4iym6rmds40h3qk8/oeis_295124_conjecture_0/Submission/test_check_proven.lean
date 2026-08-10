import Mathlib

open Nat Finset

lemma prime_gt_three {p : ℕ} (hp : p.Prime) (h : p > 3) : p ≥ 5 := by
  by_contra h_lt
  push_neg at h_lt
  have : p = 4 := by omega
  subst this
  have h4 : ¬ Nat.Prime 4 := by decide
  contradiction

lemma prime_gt_five {p : ℕ} (hp : p.Prime) (h : p > 5) : p ≥ 7 := by
  by_contra h_lt
  push_neg at h_lt
  have : p = 6 := by omega
  subst this
  have h6 : ¬ Nat.Prime 6 := by decide
  contradiction

lemma prime_gt_seven {p : ℕ} (hp : p.Prime) (h : p > 7) : p ≥ 11 := by
  by_contra h_lt
  push_neg at h_lt
  have : p = 8 ∨ p = 9 ∨ p = 10 := by omega
  rcases this with rfl | rfl | rfl
  · have h8 : ¬ Nat.Prime 8 := by decide
    contradiction
  · have h9 : ¬ Nat.Prime 9 := by decide
    contradiction
  · have h10 : ¬ Nat.Prime 10 := by decide
    contradiction

lemma prime_gt_eleven {p : ℕ} (hp : p.Prime) (h : p > 11) : p ≥ 13 := by
  by_contra h_lt
  push_neg at h_lt
  have : p = 12 := by omega
  subst this
  have h12 : ¬ Nat.Prime 12 := by decide
  contradiction

lemma prime_gt_thirteen {p : ℕ} (hp : p.Prime) (h : p > 13) : p ≥ 17 := by
  by_contra h_lt
  push_neg at h_lt
  have : p = 14 ∨ p = 15 ∨ p = 16 := by omega
  rcases this with rfl | rfl | rfl
  · have h14 : ¬ Nat.Prime 14 := by decide
    contradiction
  · have h15 : ¬ Nat.Prime 15 := by decide
    contradiction
  · have h16 : ¬ Nat.Prime 16 := by decide
    contradiction

lemma prime_gt_seventeen {p : ℕ} (hp : p.Prime) (h : p > 17) : p ≥ 19 := by
  by_contra h_lt
  push_neg at h_lt
  have : p = 18 := by omega
  subst this
  have h18 : ¬ Nat.Prime 18 := by decide
  contradiction

lemma exists_divisor_helper (k L0 L1 L2 L3 L4 : ℕ)
    (hk : k = L0 * L1 * L2 * L3 * L4)
    (hk_ge : k ≥ 32000)
    (hp0 : L0.Prime) (hp1 : L1.Prime) (hp2 : L2.Prime) (hp3 : L3.Prime) (hp4 : L4.Prime)
    (hlt0 : L0 < L1) (hlt1 : L1 < L2) (hlt2 : L2 < L3) (hlt3 : L3 < L4)
    (h0 : L0 ≥ 3) (h1 : L1 ≥ 5) (h2 : L2 ≥ 7) (h3 : L3 ≥ 11) (h4 : L4 ≥ 13) :
    ∃ d, d ∣ k ∧ d ≥ 126 ∧ k / d ≥ 126 := by
  have h_L3_pos : L3 > 0 := hp3.pos
  have h_L4_pos : L4 > 0 := hp4.pos
  have h_d1_pos : L3 * L4 > 0 := Nat.mul_pos h_L3_pos h_L4_pos

  by_cases hc : L0 * L1 * L2 ≥ 126
  · -- Case A: L0 * L1 * L2 ≥ 126. Choose d = L3 * L4.
    use L3 * L4
    have h_mul : k = (L0 * L1 * L2) * (L3 * L4) := by
      rw [hk]
      ring
    have h_dvd : L3 * L4 ∣ k := by
      use L0 * L1 * L2
      rw [h_mul]
      ring
    have h_div : k / (L3 * L4) = L0 * L1 * L2 := by
      rw [h_mul, Nat.mul_div_cancel _ h_d1_pos]
    refine ⟨h_dvd, ?_, ?_⟩
    · have : L3 * L4 ≥ 11 * 13 := Nat.mul_le_mul h3 h4
      omega
    · rw [h_div]
      exact hc
  · -- Case B: L0 * L1 * L2 < 126.
    -- First, show L0 = 3, L1 = 5, L2 = 7.
    have hL0 : L0 = 3 := by
      by_contra h_ne
      have h_gt : L0 > 3 := by omega
      have h_ge : L0 ≥ 5 := prime_gt_three hp0 h_gt
      have h1_gt : L1 > 5 := by omega
      have h1_ge : L1 ≥ 7 := prime_gt_five hp1 h1_gt
      have h2_gt : L2 > 7 := by omega
      have h2_ge : L2 ≥ 11 := prime_gt_seven hp2 h2_gt
      have h_mul_le : L0 * L1 * L2 ≥ 5 * 7 * 11 := Nat.mul_le_mul (Nat.mul_le_mul h_ge h1_ge) h2_ge
      omega
    have hL1 : L1 = 5 := by
      by_contra h_ne
      have h1_gt : L1 > 5 := by omega
      have h1_ge : L1 ≥ 7 := prime_gt_five hp1 h1_gt
      have h2_gt : L2 > 7 := by omega
      have h2_ge : L2 ≥ 11 := prime_gt_seven hp2 h2_gt
      have h_mul_le : L0 * L1 * L2 ≥ 3 * 7 * 11 := Nat.mul_le_mul (Nat.mul_le_mul (by omega) h1_ge) h2_ge
      omega
    have hL2 : L2 = 7 := by
      by_contra h_ne
      have h2_gt : L2 > 7 := by omega
      have h2_ge : L2 ≥ 11 := prime_gt_seven hp2 h2_gt
      have h_mul_le : L0 * L1 * L2 ≥ 3 * 5 * 11 := Nat.mul_le_mul (Nat.mul_le_mul (by omega) h1) h2_ge
      omega

    -- Now k = 3 * 5 * 7 * L3 * L4 = 105 * L3 * L4.
    have hk_new : k = 105 * (L3 * L4) := by
      rw [hk, hL0, hL1, hL2]
      ring
    have h_prod_ge : L3 * L4 ≥ 305 := by omega
    have h_L4_ge_19 : L4 ≥ 19 := by
      by_contra h_lt
      have h_L4_cases : L4 = 13 ∨ (L4 > 13 ∧ L4 < 19) := by
        clear k hk hk_ge h_prod_ge hk_new h_d1_pos hc
        omega
      rcases h_L4_cases with rfl | ⟨h_gt13, h_lt19⟩
      · -- L4 = 13
        have : L3 < 13 := hlt3
        have : L3 * 13 ≤ 12 * 13 := Nat.mul_le_mul_right _ (by omega)
        omega
      · -- L4 > 13 ∧ L4 < 19
        have h4_ge : L4 ≥ 17 := by
          clear k hk hk_ge h_prod_ge hk_new h_d1_pos hc
          exact prime_gt_thirteen hp4 h_gt13
        have h_ne18 : L4 ≠ 18 := by
          intro h_eq
          rw [h_eq] at hp4
          have : ¬ Nat.Prime 18 := by decide
          contradiction
        have h4_eq : L4 = 17 := by
          clear k hk hk_ge h_prod_ge hk_new h_d1_pos hc
          omega
        have h3_cases : L3 = 11 ∨ (L3 > 11 ∧ L3 < 17) := by
          clear k hk hk_ge h_prod_ge hk_new h_d1_pos hc
          omega
        rcases h3_cases with h3_eq | ⟨h_gt11, h_lt17⟩
        · rw [h3_eq, h4_eq] at h_prod_ge
          revert h_prod_ge
          decide
        · have h3_ge13 : L3 ≥ 13 := by
            clear k hk hk_ge h_prod_ge hk_new h_d1_pos hc
            exact prime_gt_eleven hp3 h_gt11
          have h_ne14 : L3 ≠ 14 := by
            intro h_eq; rw [h_eq] at hp3; contradiction
          have h_ne15 : L3 ≠ 15 := by
            intro h_eq; rw [h_eq] at hp3; contradiction
          have h_ne16 : L3 ≠ 16 := by
            intro h_eq; rw [h_eq] at hp3; contradiction
          have h3_eq : L3 = 13 := by
            clear k hk hk_ge h_prod_ge hk_new h_d1_pos hc
            omega
          rw [h3_eq, h4_eq] at h_prod_ge
          revert h_prod_ge
          decide

    -- Choose d = L2 * L4 = 7 * L4.
    -- Since L2 = 7, d = 7 * L4.
    -- k / d = L0 * L1 * L3 = 15 * L3.
    use 7 * L4
    have h_mul : k = (15 * L3) * (7 * L4) := by
      rw [hk_new]
      ring
    have h_dvd : 7 * L4 ∣ k := by
      use 15 * L3
      rw [h_mul]
      ring
    have h_div : k / (7 * L4) = 15 * L3 := by
      rw [h_mul]
      have h_7_L4 : 7 * L4 > 0 := by omega
      exact Nat.mul_div_cancel _ h_7_L4
    refine ⟨h_dvd, ?_, ?_⟩
    · have : 7 * L4 ≥ 7 * 19 := Nat.mul_le_mul_left _ h_L4_ge_19
      omega
    · rw [h_div]
      have : 15 * L3 ≥ 15 * 11 := Nat.mul_le_mul_left _ h3
      omega

lemma count_divisors_lt_32_of_exists (k : ℕ) (hk_ge : k ≥ 32000) (hk_card : (Nat.divisors k).card = 32)
    (h_exists : ∃ d ∈ Nat.divisors k, d ≥ 126 ∧ k / d ≥ 126) :
    2 * ((Nat.divisors k).filter (fun x => x < 126)).card < 32 := by
  set S1 := (Nat.divisors k).filter (fun x => x < 126)
  set S2 := (Nat.divisors k).filter (fun x => x ≥ 126)

  have h_partition : (Nat.divisors k) = S1 ∪ S2 := by
    dsimp only [S1, S2]
    ext x
    simp only [mem_union, Finset.mem_filter]
    constructor
    · intro h
      rcases lt_or_ge x 126 with h1 | h1
      · left; exact ⟨h, h1⟩
      · right; exact ⟨h, h1⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h

  have h_disjoint : Disjoint S1 S2 := by
    rw [disjoint_iff_ne]
    rintro x hx y hy rfl
    rw [Finset.mem_filter] at hx hy
    omega

  have h_sum : S1.card + S2.card = 32 := by
    rw [← card_union_of_disjoint h_disjoint, ← h_partition, hk_card]

  by_contra h_ge
  push_neg at h_ge
  have hS1_ge16 : S1.card ≥ 16 := by omega
  have hS2_le16 : S2.card ≤ 16 := by omega

  rcases h_exists with ⟨d, hd_mem, hd_ge, h_kd_ge⟩

  have h_inj : (S1 : Set ℕ).InjOn (fun x => k / x) := by
    rintro x hx y hy h_eq
    rw [Finset.mem_coe, Finset.mem_filter] at hx hy
    change k / x = k / y at h_eq
    have hx_dvd : x ∣ k := Nat.dvd_of_mem_divisors hx.1
    have hy_dvd : y ∣ k := Nat.dvd_of_mem_divisors hy.1
    have hk0 : k ≠ 0 := by omega
    have h_eq' : k / (k / x) = k / (k / y) := by rw [h_eq]
    rw [Nat.div_div_self hx_dvd hk0, Nat.div_div_self hy_dvd hk0] at h_eq'
    exact h_eq'

  have h_mem : Set.MapsTo (fun x => k / x) (S1 : Set ℕ) ((S2 \ {d} : Finset ℕ) : Set ℕ) := by
    rintro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx
    rw [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_filter]
    have hk0 : k ≠ 0 := by omega
    dsimp only
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Nat.mem_divisors]
      refine ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hx.1), hk0⟩
    · have hx_le : x ≤ 125 := by omega
      have : 125 * (k / x) ≥ x * (k / x) := Nat.mul_le_mul_right (k / x) hx_le
      have h_prod : x * (k / x) = k := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hx.1)
      rw [h_prod] at this
      have h_ge32000 : 125 * (k / x) ≥ 32000 := by omega
      have h_ge256 : k / x ≥ 256 := by omega
      clear this h_prod h_ge32000
      omega
    · intro h_eq
      have hx_dvd : x ∣ k := Nat.dvd_of_mem_divisors hx.1
      have h_div_div := Nat.div_div_self hx_dvd hk0
      rw [h_eq] at h_div_div
      omega

  have h_le := card_le_card_of_injOn (fun x => k / x) h_mem h_inj
  have h_card_sdiff : (S2 \ {d}).card = S2.card - 1 := by
    have hd_S2 : d ∈ S2 := by
      rw [Finset.mem_filter]
      exact ⟨hd_mem, hd_ge⟩
    have h_sub : {d} ⊆ S2 := singleton_subset_iff.mpr hd_S2
    rw [card_sdiff_of_subset h_sub, card_singleton]

  rw [h_card_sdiff] at h_le
  omega
