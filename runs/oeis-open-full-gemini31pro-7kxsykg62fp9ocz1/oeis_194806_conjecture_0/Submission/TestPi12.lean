import Mathlib

open Nat Finset

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
