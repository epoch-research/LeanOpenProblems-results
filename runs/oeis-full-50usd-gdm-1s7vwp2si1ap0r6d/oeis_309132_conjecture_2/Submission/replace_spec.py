import os

new_code = """lemma D_sum3_eq_int (n : ℕ) (hn : 1 < n) :
    ((bernoulli (n - 1)).den : ℚ) * (∑ i ∈ Finset.range (n - 1), bernoulli i * ↑(n.choose i) * (n : ℚ) ^ (n - i - 1)) =
    (((bernoulli (n - 1)).den * ((∑ k ∈ Finset.range n, (k : ℤ) ^ (n - 1)) + 1) - (n * (bernoulli (n - 1)).num + (bernoulli (n - 1)).den) : ℤ) : ℚ) := by
  have h_id := bernoulli_sum_identity n hn
  have h_cast_S : ((∑ k ∈ Finset.range n, (k : ℚ) ^ (n - 1)) + 1) = (((∑ k ∈ Finset.range n, (k : ℤ) ^ (n - 1)) + 1 : ℤ) : ℚ) := by
    push_cast
    rfl
  rw [h_cast_S] at h_id
  push_cast at *
  linarith

lemma agoh_giuga_even_ge_4_false (n : ℕ) (h_even : Even n) (hn : 4 ≤ n) :
    ¬ agoh_giuga_condition n := by
  intro h_ag
  unfold agoh_giuga_condition at h_ag
  rcases h_ag with ⟨hn1, h_dvd⟩
  rcases h_even with ⟨m, rfl⟩
  have hm : 2 ≤ m := by omega
  have h_eq_mul : m + m = 2 * m := by ring
  rw [h_eq_mul] at h_dvd
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

lemma key_equiv_5 : a 5 = 1 ↔ agoh_giuga_condition 5 := by
  have h_a : a 5 = 1 := by
    unfold a
    simp
    have h_b4 : bernoulli 4 = -1/30 := by
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
      
    have h_cop : Nat.Coprime N.natAbs (bernoulli (n - 1)).den := (bernoulli (n - 1)).reduced
    have h_cop_n : Nat.Coprime n j.natAbs := by
      by_contra h_not_cop
      have hg : Nat.gcd n j.natAbs ≠ 1 := h_not_cop
      rcases Nat.exists_prime_and_dvd hg with ⟨p, hp, hpdvd⟩
      have hp_n : p ∣ n := (Nat.dvd_gcd_iff.mp hpdvd).1
      have hp_j : p ∣ j.natAbs := (Nat.dvd_gcd_iff.mp hpdvd).2
      have hp_j_z : (p : ℤ) ∣ j := Int.natCast_dvd.mpr hp_j
      have hp_D : (p : ℤ) ∣ D := by
        rw [hj_eq]
        exact dvd_mul_of_dvd_right hp_j_z n
      have hp_N : (p : ℤ) ∣ N := by
        have h_N_eq : N = n * m - j := by omega
        rw [h_N_eq]
        exact dvd_sub (dvd_mul_of_dvd_left (Int.natCast_dvd.mpr hp_n) m) hp_j_z
      have hp_D_nat : p ∣ (bernoulli (n - 1)).den := Int.natCast_dvd_natCast.mp hp_D
      have hp_N_nat : p ∣ N.natAbs := Int.natCast_dvd_natCast.mp hp_N
      have h_cop_p := Nat.Coprime.coprime_of_dvd hp_N_nat hp_D_nat h_cop
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
      by_contra h_not_cop
      have hg : Nat.gcd n S.natAbs ≠ 1 := h_not_cop
      rcases Nat.exists_prime_and_dvd hg with ⟨p, hp, hpdvd⟩
      have hp_n : p ∣ n := (Nat.dvd_gcd_iff.mp hpdvd).1
      have hp_S : p ∣ S.natAbs := (Nat.dvd_gcd_iff.mp hpdvd).2
      have hp_S_z : (p : ℤ) ∣ S := Int.natCast_dvd.mpr hp_S
      have hp_S1 : (p : ℤ) ∣ S + 1 := by
        rw [hj]
        exact dvd_mul_of_dvd_left (Int.natCast_dvd.mpr hp_n) j
      have hp_one : (p : ℤ) ∣ 1 := by
        have : (S + 1) - S = 1 := by ring
        rw [← this]
        exact dvd_sub hp_S1 hp_S_z
      have hp_one_nat : p ∣ 1 := Int.natCast_dvd_natCast.mp hp_one
      have : p = 1 := Nat.eq_one_of_dvd_one hp_one_nat
      exact hp.ne_one this
      
    have h_n_div_D_nat : n ∣ (bernoulli (n - 1)).den := by
      have h_div_nat : n ∣ D.natAbs * S.natAbs := by
        have h1 : (D * S).natAbs = D.natAbs * S.natAbs := Int.natAbs_mul D S
        rw [← h1]
        rcases h_n_div_DS with ⟨k, hk⟩
        exact Int.natCast_dvd_natCast.mp ⟨k, hk⟩
      exact h_cop_S.symm.dvd_of_dvd_mul_left h_div_nat
      
    have h_n_div_D : (n : ℤ) ∣ D := Int.natCast_dvd.mpr h_n_div_D_nat
    rcases h_n_div_D with ⟨j2, hj2⟩
    
    have h_div_D_S : (n * n : ℤ) ∣ D * (S + 1) := by
      use j2 * j
      calc D * (S + 1) = (n * j2) * (n * j) := by rw [← hj2, ← hj]
      _ = n * n * (j2 * j) := by ring

    change (n * n : ℤ) ∣ X
    rw [show X = D * (S + 1) - (D * (S + 1) - X) by ring]
    apply dvd_sub
    · exact h_div_D_S
    · let Sum4 := ∑ i ∈ Finset.range (n - 2), bernoulli i * ↑(n.choose i) * (n : ℚ) ^ (n - i - 3)
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
  · rcases h_odd with ⟨k, rfl⟩
    have h5 : 5 ≤ 2 * k + 1 := by omega
    exact key_equiv_odd_ge_5 (2 * k + 1) (by use k) h5

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
    f.write("\\n")
    f.write(new_code)

print("Spec.lean updated successfully!")
