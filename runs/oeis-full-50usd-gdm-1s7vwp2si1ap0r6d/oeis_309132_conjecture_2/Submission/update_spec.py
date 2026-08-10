import os

new_code = """lemma agoh_giuga_even_ge_4_false (n : ℕ) (h_even : Even n) (hn : 4 ≤ n) :
    ¬ agoh_giuga_condition n := by
  intro h_ag
  unfold agoh_giuga_condition at h_ag
  rcases h_ag with ⟨hn1, h_dvd⟩
  rcases h_even with ⟨m, rfl⟩
  have hm : 2 ≤ m := by omega
  have h_eq_mul : (m + m : ℤ) = (2 * m : ℤ) := by ring
  have h_eq_sum : (∑ k ∈ Finset.range (m + m), (k : ℤ)^(m + m - 1) + 1) = (∑ k ∈ Finset.range (2 * m), (k : ℤ)^(2 * m - 1) + 1) := by
    congr 2
    · ring
    · ext x
      congr 1
      ring
  rw [h_eq_mul, h_eq_sum] at h_dvd
  have h_m_odd : Odd m := by
    apply agoh_giuga_even_implies_m_odd m (by omega)
    exact h_dvd
  rcases h_m_odd with ⟨k, rfl⟩
  have hm3 : 3 ≤ 2 * k + 1 := by omega
  haveI : NeZero (2 * k + 1) := ⟨by omega⟩
  have h_not := agoh_giuga_even_false (2 * k + 1) hm3 (by use k)
  contradiction

lemma agoh_giuga_even_ge_4_false_iff (n : ℕ) (h_even : Even n) (hn : 4 ≤ n) :
    ¬ agoh_giuga_condition n := agoh_giuga_even_ge_4_false n h_even hn

lemma key_equiv_even_ge_4 (n : ℕ) (h_even : Even n) (hn : 4 ≤ n) :
    a n = 1 ↔ agoh_giuga_condition n := by
  constructor
  · intro h_a
    have h_not := a_even_ge_4_false n h_even hn
    contradiction
  · intro h_ag
    have h_not := agoh_giuga_even_ge_4_false n h_even hn
    contradiction

lemma D_sum3_eq_int (n : ℕ) (hn : 1 < n) :
    ((bernoulli (n - 1)).den : ℚ) * (∑ i ∈ Finset.range (n - 1), bernoulli i * ↑(n.choose i) * (n : ℚ) ^ (n - i - 1)) =
    (((bernoulli (n - 1)).den * ((∑ k ∈ Finset.range n, (k : ℤ) ^ (n - 1)) + 1) - (n * (bernoulli (n - 1)).num + (bernoulli (n - 1)).den) : ℤ) : ℚ) := by
  have h_id := bernoulli_sum_identity n hn
  have h_cast_S : ((∑ k ∈ Finset.range n, (k : ℚ) ^ (n - 1)) + 1) = (((∑ k ∈ Finset.range n, (k : ℤ) ^ (n - 1)) + 1 : ℤ) : ℚ) := by
    push_cast
    rfl
  rw [h_cast_S] at h_id
  push_cast at *
  linarith

lemma key_equiv_5 : a 5 = 1 ↔ agoh_giuga_condition 5 := by
  have h_a : a 5 = 1 := by
    unfold a
    split_ifs with h
    · contradiction
    · have h_b4 : bernoulli 4 = -1/30 := by
        rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
        exact bernoulli'_four
      change (((bernoulli 4).num : ℚ) / 5 + ((bernoulli 4).den : ℚ) / (5 * 5)).den = 1
      rw [h_b4]
      norm_num
  have h_ag : agoh_giuga_condition 5 := by
    unfold agoh_giuga_condition
    decide
  simp [h_a, h_ag]

lemma key_equiv_odd_ge_5 (n : ℕ) (h_odd : Odd n) (hn : 5 ≤ n) :
    a n = 1 ↔ agoh_giuga_condition n := by
  have hn0 : n ≠ 0 := by omega
  have hn_gt : 1 < n := by omega
  let D : ℤ := (bernoulli (n - 1)).den
  let N : ℤ := (bernoulli (n - 1)).num
  let S : ℤ := ∑ k ∈ Finset.range n, (k : ℤ) ^ (n - 1)
  let X : ℤ := n * N + D

  rw [a_eq_one_iff n hn0]
  unfold agoh_giuga_condition
  simp only [hn_gt, true_and]
  constructor
  · intro h_div
    rcases h_div with ⟨m, hm⟩
    have h_X_eq : n * N + D = n * n * m := hm
    have h_D_eq : D = n * (n * m - N) := by
      calc D = (n * N + D) - n * N := by ring
      _ = n * n * m - n * N := by rw [h_X_eq]
      _ = n * (n * m - N) := by ring
    let j : ℤ := n * m - N
    have hj_eq : D = n * j := h_D_eq
    
    let Sum4 := ∑ i ∈ Finset.range (n - 2), bernoulli i * ↑(n.choose i) * (n : ℚ) ^ (n - i - 3)
    let Q_Sum4 := ((bernoulli (n - 1)).den : ℚ) * Sum4
    
    have h_id_q : ((D * (S + 1) : ℤ) : ℚ) = ((n * n : ℤ) : ℚ) * (m + Q_Sum4) := by
      rw [show ((D * (S + 1) : ℤ) : ℚ) = ((D * (S + 1) - X : ℤ) : ℚ) + (X : ℚ) by ring]
      rw [show ((X : ℚ)) = (((n * N + D : ℤ) : ℚ)) by rfl]
      rw [h_X_eq]
      rw [← D_sum3_eq_int n hn_gt]
      rw [sum3_eq_n2_sum4 n hn h_odd]
      push_cast
      ring
    
    have h_div_q : ((j * (S + 1) : ℤ) : ℚ) = (n : ℚ) * (m + Q_Sum4) := by
      have h_mul : (n : ℚ) * ((j * (S + 1) : ℤ) : ℚ) = (n : ℚ) * ((n : ℚ) * (m + Q_Sum4)) := by
        calc (n : ℚ) * ((j * (S + 1) : ℤ) : ℚ) = ((n * j * (S + 1) : ℤ) : ℚ) := by push_cast; ring
        _ = ((D * (S + 1) : ℤ) : ℚ) := by rw [← hj_eq]
        _ = ((n * n : ℤ) : ℚ) * (m + Q_Sum4) := h_id_q
        _ = (n : ℚ) * ((n : ℚ) * (m + Q_Sum4)) := by push_cast; ring
      have hn_ne : (n : ℚ) ≠ 0 := by positivity
      exact mul_left_cancel₀ hn_ne h_mul
      
    have h_is_int : ∃ k : ℤ, (n : ℚ) * (m + Q_Sum4) = (k : ℚ) := by
      use j * (S + 1)
      exact h_div_q.symm
      
    rcases h_is_int with ⟨k, hk⟩
    have h_sub_eq : j * (S + 1) = n * k := by
      exact_mod_cast h_div_q.trans hk
      
    have h_n_div_jS1 : (n : ℤ) ∣ j * (S + 1) := ⟨k, h_sub_eq⟩
    
    have h_cop : Nat.Coprime N.natAbs (bernoulli (n - 1)).den := (bernoulli (n - 1)).reduced
    have h_cop_n : Nat.Coprime n j.natAbs := by
      rw [Nat.Prime.not_coprime_iff_dvd]
      push_neg
      intro p hp hp_n hp_j
      have hp_D : p ∣ (bernoulli (n - 1)).den := by
        have h_D_div : (n : ℤ) ∣ D := ⟨j, hj_eq⟩
        have h_D_div_nat : n ∣ (bernoulli (n - 1)).den := Int.natCast_dvd_natCast.mp h_D_div
        exact dvd_trans hp_n h_D_div_nat
      have hp_N : p ∣ N.natAbs := by
        have hj_div : (p : ℤ) ∣ j := Int.natCast_dvd.mpr hp_j
        have hn_div : (p : ℤ) ∣ n := Int.natCast_dvd.mpr hp_n
        have h_N_eq : N = n * m - j := by omega
        have hp_N_z : (p : ℤ) ∣ N := by
          rw [h_N_eq]
          exact dvd_sub (dvd_mul_of_dvd_left hn_div m) hj_div
        exact Int.natCast_dvd_natCast.mp hp_N_z
      have h_cop_p := Nat.Coprime.coprime_of_dvd hp_N hp_D h_cop
      exact hp.ne_one h_cop_p
      
    have h_n_div_S1_nat : n ∣ (S + 1).natAbs := by
      have h_div_nat : n ∣ j.natAbs * (S + 1).natAbs := by
        have h1 : (j * (S + 1)).natAbs = j.natAbs * (S + 1).natAbs := Int.natAbs_mul j (S + 1)
        rw [← h1]
        exact Int.natCast_dvd_natCast.mp ⟨k, h_sub_eq⟩
      exact h_cop_n.symm.dvd_of_dvd_mul_left h_div_nat
      
    exact Int.natCast_dvd.mpr h_n_div_S1_nat

  · intro h_div_ag
    rcases h_div_ag with ⟨j, hj⟩
    have h_n_div_DS : (n : ℤ) ∣ D * S := by
      let Sum4 := ∑ i ∈ Finset.range (n - 2), bernoulli i * ↑(n.choose i) * (n : ℚ) ^ (n - i - 3)
      let Q_Sum4 := ((bernoulli (n - 1)).den : ℚ) * Sum4
      have h_DS_q : ((D * S : ℤ) : ℚ) = (n : ℚ) * (N + n * Q_Sum4) := by
        rw [← D_sum3_eq_int n hn_gt]
        rw [sum3_eq_n2_sum4 n hn h_odd]
        push_cast
        ring
      have h_is_int : ∃ k : ℤ, (n : ℚ) * (N + n * Q_Sum4) = (k : ℚ) := ⟨D * S, h_DS_q.symm⟩
      rcases h_is_int with ⟨k, hk⟩
      have h_eq : D * S = n * k := by exact_mod_cast h_DS_q.trans hk
      exact ⟨k, h_eq⟩
        
    have h_cop_S : Nat.Coprime n S.natAbs := by
      rw [Nat.Prime.not_coprime_iff_dvd]
      push_neg
      intro p hp hp_n hp_S
      have hp_j : (p : ℤ) ∣ n * j := dvd_mul_of_dvd_left (Int.natCast_dvd.mpr hp_n) j
      have hp_S_z : (p : ℤ) ∣ S := Int.natCast_dvd.mpr hp_S
      have h1 : n * j - S = 1 := by omega
      have hp_1 : (p : ℤ) ∣ 1 := by
        rw [← h1]
        exact dvd_sub hp_j hp_S_z
      exact hp.ne_one (Nat.Coprime.of_dvd_left (Int.natCast_dvd_natCast.mp hp_1) (Nat.coprime_one_right p))
      
    have h_n_div_D_nat : n ∣ (bernoulli (n - 1)).den := by
      have h_div_nat : n ∣ D.natAbs * S.natAbs := by
        have h1 : (D * S).natAbs = D.natAbs * S.natAbs := Int.natAbs_mul D S
        rw [← h1]
        rcases h_n_div_DS with ⟨k, hk⟩
        exact Int.natCast_dvd_natCast.mp ⟨k, hk⟩
      exact h_cop_S.symm.dvd_of_dvd_mul_left h_div_nat
      
    have h_n_div_D : (n : ℤ) ∣ D := Int.natCast_dvd.mpr h_n_div_D_nat
    rcases h_n_div_D with ⟨j2, hj2⟩
    
    let Sum4 := ∑ i ∈ Finset.range (n - 2), bernoulli i * ↑(n.choose i) * (n : ℚ) ^ (n - i - 3)
    let Q_Sum4 := ((bernoulli (n - 1)).den : ℚ) * Sum4
    have h_X_q : (((n * N + D : ℤ) : ℚ)) = (n * n : ℚ) * (j2 * j - Q_Sum4) := by
      rw [show (((n * N + D : ℤ) : ℚ)) = ((D * (S + 1) : ℤ) : ℚ) - (((D * (S + 1) - X : ℤ) : ℚ)) by
            simp only [X]
            push_cast
            ring]
      rw [← D_sum3_eq_int n hn_gt]
      rw [sum3_eq_n2_sum4 n hn h_odd]
      rw [hj2, hj]
      push_cast
      ring
      
    have h_is_int : ∃ k : ℤ, (n * n : ℚ) * (j2 * j - Q_Sum4) = (k : ℚ) := ⟨n * N + D, h_X_q.symm⟩
    rcases h_is_int with ⟨k, hk⟩
    have h_eq : n * N + D = n * n * k := by exact_mod_cast h_X_q.trans hk
    exact ⟨k, h_eq⟩

lemma key_equiv (n : ℕ) (hn : 1 < n) : a n = 1 ↔ agoh_giuga_condition n := by
  rcases eq_or_ne n 2 with rfl | hn2
  · exact key_equiv_2
  rcases eq_or_ne n 3 with rfl | hn3
  · exact key_equiv_3
  rcases Nat.even_or_odd n with h_even | h_odd
  · have h4 : 4 ≤ n := by omega
    exact key_equiv_even_ge_4 n h_even h4
  · have h5 : 5 ≤ n := by omega
    exact key_equiv_odd_ge_5 n h_odd h5

theorem oeis_309132_conjecture_2 : A309132_conjecture ↔ agoh_giuga_conjecture := by
  constructor
  · intro h n hn
    have hkey := key_equiv n hn
    have hn_conj := h n hn
    rw [← hn_conj, hkey]
  · intro h n hn
    have hkey := key_equiv n hn
    have hn_conj := h n hn
    rw [hn_conj, ← hkey]
"""

with open('/workspace/leanproject/Submission/Spec.lean', 'r') as f:
    lines = f.readlines()

first_part = lines[:326]

with open('/workspace/leanproject/Submission/Spec.lean', 'w') as f:
    f.writelines(first_part)
    f.write("\n")
    f.write(new_code)

print("Spec.lean updated successfully!")
