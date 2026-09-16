import Submission.Proof
open Nat Finset

lemma case1_ineq (K r : ℕ) (hr : r < 9 * K + 1) :
    (if r + (7 * K + 0) ≥ 9 * K + 1 then 1 else 0) +
    (if r + (5 * K + 0) ≥ 9 * K + 1 then 1 else 0) +
    (if r + (2 * K + 0) ≥ 9 * K + 1 then 1 else 0) ≥
    2 * (if r + 0 ≥ 9 * K + 1 then 1 else 0) +
    (if r + (6 * K + 0) ≥ 9 * K + 1 then 1 else 0) := by
  split_ifs <;> omega

lemma case1_witness (K : ℕ) :
    9 * (8 * K + 1) = 8 * (9 * K + 1) + 1 ∧
    (8 * K + 1) * 7 + (7 * K + 0) = (9 * K + 1) * 7 ∧
    (8 * K + 1) * 5 + (5 * K + 0) = (9 * K + 1) * 5 ∧
    (8 * K + 1) * 2 + (2 * K + 0) = (9 * K + 1) * 2 ∧
    (8 * K + 1) * 0 + 0 = (9 * K + 1) * 0 ∧
    (8 * K + 1) * 6 + (6 * K + 0) = (9 * K + 1) * 6 ∧
    True := by
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring, trivial⟩

lemma delta_case1 (n K M : ℕ) (hM : M = 9 * K + 1) :
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 7 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 5 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 2 then 1 else 0) ≥
    2 * ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 0 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 6 then 1 else 0) := by
  have hM_pos : M > 0 := by omega
  let inv9 := (8 * K + 1)
  have h_witness := case1_witness K
  rcases h_witness with ⟨h_inv_raw, h_c7_raw, h_c5_raw, h_c2_raw, h_c0_raw, h_c6_raw, _⟩
  have h_inv : 9 * inv9 = 8 * M + 1 := by rw [hM]; exact h_inv_raw
  have h_c7 : inv9 * 7 + (7 * K + 0) = M * 7 := by rw [hM]; exact h_c7_raw
  have hc7_lt : (7 * K + 0) < M := by omega
  have heq7 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 7 then 1 else 0) = n / M + (if n % M + (7 * K + 0) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 7 (7 * K + 0) (fun i hi => count_equiv_add M i 7 inv9 8 (7 * K + 0) 7 (9 * i - 7) h_inv h_c7 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (7 * K + 0) M hM_pos hc7_lt]
    rw [div_eq_div_add_indicator n (7 * K + 0) M hM_pos hc7_lt]
  have h_c5 : inv9 * 5 + (5 * K + 0) = M * 5 := by rw [hM]; exact h_c5_raw
  have hc5_lt : (5 * K + 0) < M := by omega
  have heq5 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 5 then 1 else 0) = n / M + (if n % M + (5 * K + 0) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 5 (5 * K + 0) (fun i hi => count_equiv_add M i 5 inv9 8 (5 * K + 0) 5 (9 * i - 5) h_inv h_c5 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (5 * K + 0) M hM_pos hc5_lt]
    rw [div_eq_div_add_indicator n (5 * K + 0) M hM_pos hc5_lt]
  have h_c2 : inv9 * 2 + (2 * K + 0) = M * 2 := by rw [hM]; exact h_c2_raw
  have hc2_lt : (2 * K + 0) < M := by omega
  have heq2 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 2 then 1 else 0) = n / M + (if n % M + (2 * K + 0) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 2 (2 * K + 0) (fun i hi => count_equiv_add M i 2 inv9 8 (2 * K + 0) 2 (9 * i - 2) h_inv h_c2 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (2 * K + 0) M hM_pos hc2_lt]
    rw [div_eq_div_add_indicator n (2 * K + 0) M hM_pos hc2_lt]
  have h_c0 : inv9 * 0 + 0 = M * 0 := by rw [hM]; exact h_c0_raw
  have hc0_lt : 0 < M := by omega
  have heq0 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 0 then 1 else 0) = n / M + (if n % M + 0 ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 0 0 (fun i hi => count_equiv_add M i 0 inv9 8 0 0 (9 * i - 0) h_inv h_c0 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n 0 M hM_pos hc0_lt]
    rw [div_eq_div_add_indicator n 0 M hM_pos hc0_lt]
  have h_c6 : inv9 * 6 + (6 * K + 0) = M * 6 := by rw [hM]; exact h_c6_raw
  have hc6_lt : (6 * K + 0) < M := by omega
  have heq6 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 6 then 1 else 0) = n / M + (if n % M + (6 * K + 0) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 6 (6 * K + 0) (fun i hi => count_equiv_add M i 6 inv9 8 (6 * K + 0) 6 (9 * i - 6) h_inv h_c6 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (6 * K + 0) M hM_pos hc6_lt]
    rw [div_eq_div_add_indicator n (6 * K + 0) M hM_pos hc6_lt]
  have hr : n % M < 9 * K + 1 := by rw [← hM]; exact mod_lt n hM_pos
  have h_ineq := case1_ineq K (n % M) hr
  rw [heq7, heq5, heq2, heq0, heq6]
  rw [hM] at *
  omega

lemma case2_ineq (K r : ℕ) (hr : r < 9 * K + 2) :
    (if r + (8 * K + 1) ≥ 9 * K + 2 then 1 else 0) +
    (if r + (7 * K + 1) ≥ 9 * K + 2 then 1 else 0) +
    (if r + (1 * K + 0) ≥ 9 * K + 2 then 1 else 0) ≥
    2 * (if r + 0 ≥ 9 * K + 2 then 1 else 0) +
    (if r + (3 * K + 0) ≥ 9 * K + 2 then 1 else 0) := by
  split_ifs <;> omega

lemma case2_witness (K : ℕ) :
    9 * (4 * K + 1) = 4 * (9 * K + 2) + 1 ∧
    (4 * K + 1) * 7 + (8 * K + 1) = (9 * K + 2) * 4 ∧
    (4 * K + 1) * 5 + (7 * K + 1) = (9 * K + 2) * 3 ∧
    (4 * K + 1) * 2 + (1 * K + 0) = (9 * K + 2) * 1 ∧
    (4 * K + 1) * 0 + 0 = (9 * K + 2) * 0 ∧
    (4 * K + 1) * 6 + (3 * K + 0) = (9 * K + 2) * 3 ∧
    True := by
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring, trivial⟩

lemma delta_case2 (n K M : ℕ) (hM : M = 9 * K + 2) :
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 7 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 5 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 2 then 1 else 0) ≥
    2 * ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 0 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 6 then 1 else 0) := by
  have hM_pos : M > 0 := by omega
  let inv9 := (4 * K + 1)
  have h_witness := case2_witness K
  rcases h_witness with ⟨h_inv_raw, h_c7_raw, h_c5_raw, h_c2_raw, h_c0_raw, h_c6_raw, _⟩
  have h_inv : 9 * inv9 = 4 * M + 1 := by rw [hM]; exact h_inv_raw
  have h_c7 : inv9 * 7 + (8 * K + 1) = M * 4 := by rw [hM]; exact h_c7_raw
  have hc7_lt : (8 * K + 1) < M := by omega
  have heq7 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 7 then 1 else 0) = n / M + (if n % M + (8 * K + 1) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 7 (8 * K + 1) (fun i hi => count_equiv_add M i 7 inv9 4 (8 * K + 1) 4 (9 * i - 7) h_inv h_c7 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (8 * K + 1) M hM_pos hc7_lt]
    rw [div_eq_div_add_indicator n (8 * K + 1) M hM_pos hc7_lt]
  have h_c5 : inv9 * 5 + (7 * K + 1) = M * 3 := by rw [hM]; exact h_c5_raw
  have hc5_lt : (7 * K + 1) < M := by omega
  have heq5 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 5 then 1 else 0) = n / M + (if n % M + (7 * K + 1) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 5 (7 * K + 1) (fun i hi => count_equiv_add M i 5 inv9 4 (7 * K + 1) 3 (9 * i - 5) h_inv h_c5 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (7 * K + 1) M hM_pos hc5_lt]
    rw [div_eq_div_add_indicator n (7 * K + 1) M hM_pos hc5_lt]
  have h_c2 : inv9 * 2 + (1 * K + 0) = M * 1 := by rw [hM]; exact h_c2_raw
  have hc2_lt : (1 * K + 0) < M := by omega
  have heq2 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 2 then 1 else 0) = n / M + (if n % M + (1 * K + 0) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 2 (1 * K + 0) (fun i hi => count_equiv_add M i 2 inv9 4 (1 * K + 0) 1 (9 * i - 2) h_inv h_c2 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (1 * K + 0) M hM_pos hc2_lt]
    rw [div_eq_div_add_indicator n (1 * K + 0) M hM_pos hc2_lt]
  have h_c0 : inv9 * 0 + 0 = M * 0 := by rw [hM]; exact h_c0_raw
  have hc0_lt : 0 < M := by omega
  have heq0 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 0 then 1 else 0) = n / M + (if n % M + 0 ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 0 0 (fun i hi => count_equiv_add M i 0 inv9 4 0 0 (9 * i - 0) h_inv h_c0 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n 0 M hM_pos hc0_lt]
    rw [div_eq_div_add_indicator n 0 M hM_pos hc0_lt]
  have h_c6 : inv9 * 6 + (3 * K + 0) = M * 3 := by rw [hM]; exact h_c6_raw
  have hc6_lt : (3 * K + 0) < M := by omega
  have heq6 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 6 then 1 else 0) = n / M + (if n % M + (3 * K + 0) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 6 (3 * K + 0) (fun i hi => count_equiv_add M i 6 inv9 4 (3 * K + 0) 3 (9 * i - 6) h_inv h_c6 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (3 * K + 0) M hM_pos hc6_lt]
    rw [div_eq_div_add_indicator n (3 * K + 0) M hM_pos hc6_lt]
  have hr : n % M < 9 * K + 2 := by rw [← hM]; exact mod_lt n hM_pos
  have h_ineq := case2_ineq K (n % M) hr
  rw [heq7, heq5, heq2, heq0, heq6]
  rw [hM] at *
  omega

lemma case4_ineq (K r : ℕ) (hr : r < 9 * K + 4) :
    (if r + (4 * K + 1) ≥ 9 * K + 4 then 1 else 0) +
    (if r + (8 * K + 3) ≥ 9 * K + 4 then 1 else 0) +
    (if r + (5 * K + 2) ≥ 9 * K + 4 then 1 else 0) ≥
    2 * (if r + 0 ≥ 9 * K + 4 then 1 else 0) +
    (if r + (6 * K + 2) ≥ 9 * K + 4 then 1 else 0) := by
  split_ifs <;> omega

lemma case4_witness (K : ℕ) :
    9 * (2 * K + 1) = 2 * (9 * K + 4) + 1 ∧
    (2 * K + 1) * 7 + (4 * K + 1) = (9 * K + 4) * 2 ∧
    (2 * K + 1) * 5 + (8 * K + 3) = (9 * K + 4) * 2 ∧
    (2 * K + 1) * 2 + (5 * K + 2) = (9 * K + 4) * 1 ∧
    (2 * K + 1) * 0 + 0 = (9 * K + 4) * 0 ∧
    (2 * K + 1) * 6 + (6 * K + 2) = (9 * K + 4) * 2 ∧
    True := by
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring, trivial⟩

lemma delta_case4 (n K M : ℕ) (hM : M = 9 * K + 4) :
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 7 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 5 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 2 then 1 else 0) ≥
    2 * ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 0 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 6 then 1 else 0) := by
  have hM_pos : M > 0 := by omega
  let inv9 := (2 * K + 1)
  have h_witness := case4_witness K
  rcases h_witness with ⟨h_inv_raw, h_c7_raw, h_c5_raw, h_c2_raw, h_c0_raw, h_c6_raw, _⟩
  have h_inv : 9 * inv9 = 2 * M + 1 := by rw [hM]; exact h_inv_raw
  have h_c7 : inv9 * 7 + (4 * K + 1) = M * 2 := by rw [hM]; exact h_c7_raw
  have hc7_lt : (4 * K + 1) < M := by omega
  have heq7 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 7 then 1 else 0) = n / M + (if n % M + (4 * K + 1) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 7 (4 * K + 1) (fun i hi => count_equiv_add M i 7 inv9 2 (4 * K + 1) 2 (9 * i - 7) h_inv h_c7 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (4 * K + 1) M hM_pos hc7_lt]
    rw [div_eq_div_add_indicator n (4 * K + 1) M hM_pos hc7_lt]
  have h_c5 : inv9 * 5 + (8 * K + 3) = M * 2 := by rw [hM]; exact h_c5_raw
  have hc5_lt : (8 * K + 3) < M := by omega
  have heq5 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 5 then 1 else 0) = n / M + (if n % M + (8 * K + 3) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 5 (8 * K + 3) (fun i hi => count_equiv_add M i 5 inv9 2 (8 * K + 3) 2 (9 * i - 5) h_inv h_c5 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (8 * K + 3) M hM_pos hc5_lt]
    rw [div_eq_div_add_indicator n (8 * K + 3) M hM_pos hc5_lt]
  have h_c2 : inv9 * 2 + (5 * K + 2) = M * 1 := by rw [hM]; exact h_c2_raw
  have hc2_lt : (5 * K + 2) < M := by omega
  have heq2 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 2 then 1 else 0) = n / M + (if n % M + (5 * K + 2) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 2 (5 * K + 2) (fun i hi => count_equiv_add M i 2 inv9 2 (5 * K + 2) 1 (9 * i - 2) h_inv h_c2 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (5 * K + 2) M hM_pos hc2_lt]
    rw [div_eq_div_add_indicator n (5 * K + 2) M hM_pos hc2_lt]
  have h_c0 : inv9 * 0 + 0 = M * 0 := by rw [hM]; exact h_c0_raw
  have hc0_lt : 0 < M := by omega
  have heq0 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 0 then 1 else 0) = n / M + (if n % M + 0 ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 0 0 (fun i hi => count_equiv_add M i 0 inv9 2 0 0 (9 * i - 0) h_inv h_c0 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n 0 M hM_pos hc0_lt]
    rw [div_eq_div_add_indicator n 0 M hM_pos hc0_lt]
  have h_c6 : inv9 * 6 + (6 * K + 2) = M * 2 := by rw [hM]; exact h_c6_raw
  have hc6_lt : (6 * K + 2) < M := by omega
  have heq6 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 6 then 1 else 0) = n / M + (if n % M + (6 * K + 2) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 6 (6 * K + 2) (fun i hi => count_equiv_add M i 6 inv9 2 (6 * K + 2) 2 (9 * i - 6) h_inv h_c6 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (6 * K + 2) M hM_pos hc6_lt]
    rw [div_eq_div_add_indicator n (6 * K + 2) M hM_pos hc6_lt]
  have hr : n % M < 9 * K + 4 := by rw [← hM]; exact mod_lt n hM_pos
  have h_ineq := case4_ineq K (n % M) hr
  rw [heq7, heq5, heq2, heq0, heq6]
  rw [hM] at *
  omega

lemma case5_ineq (K r : ℕ) (hr : r < 9 * K + 5) :
    (if r + (5 * K + 2) ≥ 9 * K + 5 then 1 else 0) +
    (if r + (1 * K + 0) ≥ 9 * K + 5 then 1 else 0) +
    (if r + (4 * K + 2) ≥ 9 * K + 5 then 1 else 0) ≥
    2 * (if r + 0 ≥ 9 * K + 5 then 1 else 0) +
    (if r + (3 * K + 1) ≥ 9 * K + 5 then 1 else 0) := by
  split_ifs <;> omega

lemma case5_witness (K : ℕ) :
    9 * (7 * K + 4) = 7 * (9 * K + 5) + 1 ∧
    (7 * K + 4) * 7 + (5 * K + 2) = (9 * K + 5) * 6 ∧
    (7 * K + 4) * 5 + (1 * K + 0) = (9 * K + 5) * 4 ∧
    (7 * K + 4) * 2 + (4 * K + 2) = (9 * K + 5) * 2 ∧
    (7 * K + 4) * 0 + 0 = (9 * K + 5) * 0 ∧
    (7 * K + 4) * 6 + (3 * K + 1) = (9 * K + 5) * 5 ∧
    True := by
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring, trivial⟩

lemma delta_case5 (n K M : ℕ) (hM : M = 9 * K + 5) :
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 7 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 5 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 2 then 1 else 0) ≥
    2 * ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 0 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 6 then 1 else 0) := by
  have hM_pos : M > 0 := by omega
  let inv9 := (7 * K + 4)
  have h_witness := case5_witness K
  rcases h_witness with ⟨h_inv_raw, h_c7_raw, h_c5_raw, h_c2_raw, h_c0_raw, h_c6_raw, _⟩
  have h_inv : 9 * inv9 = 7 * M + 1 := by rw [hM]; exact h_inv_raw
  have h_c7 : inv9 * 7 + (5 * K + 2) = M * 6 := by rw [hM]; exact h_c7_raw
  have hc7_lt : (5 * K + 2) < M := by omega
  have heq7 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 7 then 1 else 0) = n / M + (if n % M + (5 * K + 2) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 7 (5 * K + 2) (fun i hi => count_equiv_add M i 7 inv9 7 (5 * K + 2) 6 (9 * i - 7) h_inv h_c7 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (5 * K + 2) M hM_pos hc7_lt]
    rw [div_eq_div_add_indicator n (5 * K + 2) M hM_pos hc7_lt]
  have h_c5 : inv9 * 5 + (1 * K + 0) = M * 4 := by rw [hM]; exact h_c5_raw
  have hc5_lt : (1 * K + 0) < M := by omega
  have heq5 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 5 then 1 else 0) = n / M + (if n % M + (1 * K + 0) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 5 (1 * K + 0) (fun i hi => count_equiv_add M i 5 inv9 7 (1 * K + 0) 4 (9 * i - 5) h_inv h_c5 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (1 * K + 0) M hM_pos hc5_lt]
    rw [div_eq_div_add_indicator n (1 * K + 0) M hM_pos hc5_lt]
  have h_c2 : inv9 * 2 + (4 * K + 2) = M * 2 := by rw [hM]; exact h_c2_raw
  have hc2_lt : (4 * K + 2) < M := by omega
  have heq2 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 2 then 1 else 0) = n / M + (if n % M + (4 * K + 2) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 2 (4 * K + 2) (fun i hi => count_equiv_add M i 2 inv9 7 (4 * K + 2) 2 (9 * i - 2) h_inv h_c2 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (4 * K + 2) M hM_pos hc2_lt]
    rw [div_eq_div_add_indicator n (4 * K + 2) M hM_pos hc2_lt]
  have h_c0 : inv9 * 0 + 0 = M * 0 := by rw [hM]; exact h_c0_raw
  have hc0_lt : 0 < M := by omega
  have heq0 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 0 then 1 else 0) = n / M + (if n % M + 0 ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 0 0 (fun i hi => count_equiv_add M i 0 inv9 7 0 0 (9 * i - 0) h_inv h_c0 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n 0 M hM_pos hc0_lt]
    rw [div_eq_div_add_indicator n 0 M hM_pos hc0_lt]
  have h_c6 : inv9 * 6 + (3 * K + 1) = M * 5 := by rw [hM]; exact h_c6_raw
  have hc6_lt : (3 * K + 1) < M := by omega
  have heq6 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 6 then 1 else 0) = n / M + (if n % M + (3 * K + 1) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 6 (3 * K + 1) (fun i hi => count_equiv_add M i 6 inv9 7 (3 * K + 1) 5 (9 * i - 6) h_inv h_c6 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (3 * K + 1) M hM_pos hc6_lt]
    rw [div_eq_div_add_indicator n (3 * K + 1) M hM_pos hc6_lt]
  have hr : n % M < 9 * K + 5 := by rw [← hM]; exact mod_lt n hM_pos
  have h_ineq := case5_ineq K (n % M) hr
  rw [heq7, heq5, heq2, heq0, heq6]
  rw [hM] at *
  omega

lemma case7_ineq (K r : ℕ) (hr : r < 9 * K + 7) :
    (if r + (1 * K + 0) ≥ 9 * K + 7 then 1 else 0) +
    (if r + (2 * K + 1) ≥ 9 * K + 7 then 1 else 0) +
    (if r + (8 * K + 6) ≥ 9 * K + 7 then 1 else 0) ≥
    2 * (if r + 0 ≥ 9 * K + 7 then 1 else 0) +
    (if r + (6 * K + 4) ≥ 9 * K + 7 then 1 else 0) := by
  split_ifs <;> omega

lemma case7_witness (K : ℕ) :
    9 * (5 * K + 4) = 5 * (9 * K + 7) + 1 ∧
    (5 * K + 4) * 7 + (1 * K + 0) = (9 * K + 7) * 4 ∧
    (5 * K + 4) * 5 + (2 * K + 1) = (9 * K + 7) * 3 ∧
    (5 * K + 4) * 2 + (8 * K + 6) = (9 * K + 7) * 2 ∧
    (5 * K + 4) * 0 + 0 = (9 * K + 7) * 0 ∧
    (5 * K + 4) * 6 + (6 * K + 4) = (9 * K + 7) * 4 ∧
    True := by
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring, trivial⟩

lemma delta_case7 (n K M : ℕ) (hM : M = 9 * K + 7) :
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 7 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 5 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 2 then 1 else 0) ≥
    2 * ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 0 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 6 then 1 else 0) := by
  have hM_pos : M > 0 := by omega
  let inv9 := (5 * K + 4)
  have h_witness := case7_witness K
  rcases h_witness with ⟨h_inv_raw, h_c7_raw, h_c5_raw, h_c2_raw, h_c0_raw, h_c6_raw, _⟩
  have h_inv : 9 * inv9 = 5 * M + 1 := by rw [hM]; exact h_inv_raw
  have h_c7 : inv9 * 7 + (1 * K + 0) = M * 4 := by rw [hM]; exact h_c7_raw
  have hc7_lt : (1 * K + 0) < M := by omega
  have heq7 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 7 then 1 else 0) = n / M + (if n % M + (1 * K + 0) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 7 (1 * K + 0) (fun i hi => count_equiv_add M i 7 inv9 5 (1 * K + 0) 4 (9 * i - 7) h_inv h_c7 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (1 * K + 0) M hM_pos hc7_lt]
    rw [div_eq_div_add_indicator n (1 * K + 0) M hM_pos hc7_lt]
  have h_c5 : inv9 * 5 + (2 * K + 1) = M * 3 := by rw [hM]; exact h_c5_raw
  have hc5_lt : (2 * K + 1) < M := by omega
  have heq5 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 5 then 1 else 0) = n / M + (if n % M + (2 * K + 1) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 5 (2 * K + 1) (fun i hi => count_equiv_add M i 5 inv9 5 (2 * K + 1) 3 (9 * i - 5) h_inv h_c5 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (2 * K + 1) M hM_pos hc5_lt]
    rw [div_eq_div_add_indicator n (2 * K + 1) M hM_pos hc5_lt]
  have h_c2 : inv9 * 2 + (8 * K + 6) = M * 2 := by rw [hM]; exact h_c2_raw
  have hc2_lt : (8 * K + 6) < M := by omega
  have heq2 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 2 then 1 else 0) = n / M + (if n % M + (8 * K + 6) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 2 (8 * K + 6) (fun i hi => count_equiv_add M i 2 inv9 5 (8 * K + 6) 2 (9 * i - 2) h_inv h_c2 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (8 * K + 6) M hM_pos hc2_lt]
    rw [div_eq_div_add_indicator n (8 * K + 6) M hM_pos hc2_lt]
  have h_c0 : inv9 * 0 + 0 = M * 0 := by rw [hM]; exact h_c0_raw
  have hc0_lt : 0 < M := by omega
  have heq0 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 0 then 1 else 0) = n / M + (if n % M + 0 ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 0 0 (fun i hi => count_equiv_add M i 0 inv9 5 0 0 (9 * i - 0) h_inv h_c0 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n 0 M hM_pos hc0_lt]
    rw [div_eq_div_add_indicator n 0 M hM_pos hc0_lt]
  have h_c6 : inv9 * 6 + (6 * K + 4) = M * 4 := by rw [hM]; exact h_c6_raw
  have hc6_lt : (6 * K + 4) < M := by omega
  have heq6 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 6 then 1 else 0) = n / M + (if n % M + (6 * K + 4) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 6 (6 * K + 4) (fun i hi => count_equiv_add M i 6 inv9 5 (6 * K + 4) 4 (9 * i - 6) h_inv h_c6 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (6 * K + 4) M hM_pos hc6_lt]
    rw [div_eq_div_add_indicator n (6 * K + 4) M hM_pos hc6_lt]
  have hr : n % M < 9 * K + 7 := by rw [← hM]; exact mod_lt n hM_pos
  have h_ineq := case7_ineq K (n % M) hr
  rw [heq7, heq5, heq2, heq0, heq6]
  rw [hM] at *
  omega

lemma case8_ineq (K r : ℕ) (hr : r < 9 * K + 8) :
    (if r + (2 * K + 1) ≥ 9 * K + 8 then 1 else 0) +
    (if r + (4 * K + 3) ≥ 9 * K + 8 then 1 else 0) +
    (if r + (7 * K + 6) ≥ 9 * K + 8 then 1 else 0) ≥
    2 * (if r + 0 ≥ 9 * K + 8 then 1 else 0) +
    (if r + (3 * K + 2) ≥ 9 * K + 8 then 1 else 0) := by
  split_ifs <;> omega

lemma case8_witness (K : ℕ) :
    9 * (1 * K + 1) = 1 * (9 * K + 8) + 1 ∧
    (1 * K + 1) * 7 + (2 * K + 1) = (9 * K + 8) * 1 ∧
    (1 * K + 1) * 5 + (4 * K + 3) = (9 * K + 8) * 1 ∧
    (1 * K + 1) * 2 + (7 * K + 6) = (9 * K + 8) * 1 ∧
    (1 * K + 1) * 0 + 0 = (9 * K + 8) * 0 ∧
    (1 * K + 1) * 6 + (3 * K + 2) = (9 * K + 8) * 1 ∧
    True := by
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring, trivial⟩

lemma delta_case8 (n K M : ℕ) (hM : M = 9 * K + 8) :
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 7 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 5 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 2 then 1 else 0) ≥
    2 * ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 0 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 6 then 1 else 0) := by
  have hM_pos : M > 0 := by omega
  let inv9 := (1 * K + 1)
  have h_witness := case8_witness K
  rcases h_witness with ⟨h_inv_raw, h_c7_raw, h_c5_raw, h_c2_raw, h_c0_raw, h_c6_raw, _⟩
  have h_inv : 9 * inv9 = 1 * M + 1 := by rw [hM]; exact h_inv_raw
  have h_c7 : inv9 * 7 + (2 * K + 1) = M * 1 := by rw [hM]; exact h_c7_raw
  have hc7_lt : (2 * K + 1) < M := by omega
  have heq7 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 7 then 1 else 0) = n / M + (if n % M + (2 * K + 1) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 7 (2 * K + 1) (fun i hi => count_equiv_add M i 7 inv9 1 (2 * K + 1) 1 (9 * i - 7) h_inv h_c7 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (2 * K + 1) M hM_pos hc7_lt]
    rw [div_eq_div_add_indicator n (2 * K + 1) M hM_pos hc7_lt]
  have h_c5 : inv9 * 5 + (4 * K + 3) = M * 1 := by rw [hM]; exact h_c5_raw
  have hc5_lt : (4 * K + 3) < M := by omega
  have heq5 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 5 then 1 else 0) = n / M + (if n % M + (4 * K + 3) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 5 (4 * K + 3) (fun i hi => count_equiv_add M i 5 inv9 1 (4 * K + 3) 1 (9 * i - 5) h_inv h_c5 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (4 * K + 3) M hM_pos hc5_lt]
    rw [div_eq_div_add_indicator n (4 * K + 3) M hM_pos hc5_lt]
  have h_c2 : inv9 * 2 + (7 * K + 6) = M * 1 := by rw [hM]; exact h_c2_raw
  have hc2_lt : (7 * K + 6) < M := by omega
  have heq2 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 2 then 1 else 0) = n / M + (if n % M + (7 * K + 6) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 2 (7 * K + 6) (fun i hi => count_equiv_add M i 2 inv9 1 (7 * K + 6) 1 (9 * i - 2) h_inv h_c2 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (7 * K + 6) M hM_pos hc2_lt]
    rw [div_eq_div_add_indicator n (7 * K + 6) M hM_pos hc2_lt]
  have h_c0 : inv9 * 0 + 0 = M * 0 := by rw [hM]; exact h_c0_raw
  have hc0_lt : 0 < M := by omega
  have heq0 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 0 then 1 else 0) = n / M + (if n % M + 0 ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 0 0 (fun i hi => count_equiv_add M i 0 inv9 1 0 0 (9 * i - 0) h_inv h_c0 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n 0 M hM_pos hc0_lt]
    rw [div_eq_div_add_indicator n 0 M hM_pos hc0_lt]
  have h_c6 : inv9 * 6 + (3 * K + 2) = M * 1 := by rw [hM]; exact h_c6_raw
  have hc6_lt : (3 * K + 2) < M := by omega
  have heq6 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 6 then 1 else 0) = n / M + (if n % M + (3 * K + 2) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 6 (3 * K + 2) (fun i hi => count_equiv_add M i 6 inv9 1 (3 * K + 2) 1 (9 * i - 6) h_inv h_c6 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (3 * K + 2) M hM_pos hc6_lt]
    rw [div_eq_div_add_indicator n (3 * K + 2) M hM_pos hc6_lt]
  have hr : n % M < 9 * K + 8 := by rw [← hM]; exact mod_lt n hM_pos
  have h_ineq := case8_ineq K (n % M) hr
  rw [heq7, heq5, heq2, heq0, heq6]
  rw [hM] at *
  omega

lemma delta_ge_0 (n M : ℕ) (hM_pos : M > 0) (hM_coprime : ¬ 3 ∣ M) :
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 7 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 5 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 2 then 1 else 0) ≥
    2 * ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 0 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 6 then 1 else 0) := by
  have : M % 9 = 1 ∨ M % 9 = 2 ∨ M % 9 = 4 ∨ M % 9 = 5 ∨ M % 9 = 7 ∨ M % 9 = 8 := by
    have : M % 9 < 9 := mod_lt M (by decide)
    have : ¬ 3 ∣ M % 9 := by
      intro h
      apply hM_coprime
      have eq : M = 9 * (M / 9) + M % 9 := (Nat.div_add_mod M 9).symm
      omega
    omega
  rcases this with h1 | h2 | h3 | h4 | h5 | h6
  · have hM_eq : M = 9 * (M / 9) + 1 := by omega
    exact delta_case1 n (M / 9) M hM_eq
  · have hM_eq : M = 9 * (M / 9) + 2 := by omega
    exact delta_case2 n (M / 9) M hM_eq
  · have hM_eq : M = 9 * (M / 9) + 4 := by omega
    exact delta_case4 n (M / 9) M hM_eq
  · have hM_eq : M = 9 * (M / 9) + 5 := by omega
    exact delta_case5 n (M / 9) M hM_eq
  · have hM_eq : M = 9 * (M / 9) + 7 := by omega
    exact delta_case7 n (M / 9) M hM_eq
  · have hM_eq : M = 9 * (M / 9) + 8 := by omega
    exact delta_case8 n (M / 9) M hM_eq
