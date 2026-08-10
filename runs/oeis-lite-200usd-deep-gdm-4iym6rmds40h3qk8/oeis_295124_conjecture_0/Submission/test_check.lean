import Mathlib

open Nat Finset

lemma exists_divisor_helper (k L0 L1 L2 L3 L4 : ℕ)
    (hk : k = L0 * L1 * L2 * L3 * L4)
    (hk_ge : k ≥ 32000)
    (hp0 : L0.Prime) (hp1 : L1.Prime) (hp2 : L2.Prime) (hp3 : L3.Prime) (hp4 : L4.Prime)
    (hlt0 : L0 < L1) (hlt1 : L1 < L2) (hlt2 : L2 < L3) (hlt3 : L3 < L4)
    (h0 : L0 ≥ 3) (h1 : L1 ≥ 5) (h2 : L2 ≥ 7) (h3 : L3 ≥ 11) (h4 : L4 ≥ 13) :
    ∃ d, d ∣ k ∧ d ≥ 126 ∧ k / d ≥ 126 := by
  sorry

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
      change k / x = d at h_eq
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











