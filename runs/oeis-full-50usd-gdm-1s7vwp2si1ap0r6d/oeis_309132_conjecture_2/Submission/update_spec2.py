import os

new_code = """lemma coprime_den_sum4 (n : ℕ) (hp : n.Prime) (h_odd : Odd n) (hn : 5 ≤ n) :
    Nat.Coprime (∑ i ∈ Finset.range (n - 2), bernoulli i * ↑(n.choose i) * (n : ℚ) ^ (n - i - 3)).den n := by
  apply coprime_den_sum
  intro i hi
  rw [Finset.mem_range] at hi
  have hi3 : i ≤ n - 3 := by omega
  have h_cop : Nat.Coprime (bernoulli i).den n := coprime_den_bernoulli_of_prime n hp i hi3
  have h_eq : bernoulli i * ↑(n.choose i) * (n : ℚ) ^ (n - i - 3) =
      (((n.choose i * n ^ (n - i - 3) : ℕ) : ℤ) : ℚ) * bernoulli i := by
    push_cast
    ring
  rw [h_eq]
  exact coprime_den_mul_int (bernoulli i) ((n.choose i * n ^ (n - i - 3) : ℕ) : ℤ) n h_cop

lemma D_sum4_is_int_of_prime (n : ℕ) (hp : n.Prime) (h_odd : Odd n) (hn : 5 ≤ n) :
    Exists (fun (k : ℤ) => ((bernoulli (n - 1)).den : ℚ) * (∑ i ∈ Finset.range (n - 2), bernoulli i * ↑(n.choose i) * (n : ℚ) ^ (n - i - 3)) = (k : ℚ)) := by
  let Sum4 := ∑ i ∈ Finset.range (n - 2), bernoulli i * ↑(n.choose i) * (n : ℚ) ^ (n - i - 3)
  let D := ((bernoulli (n - 1)).den : ℚ)
  have h_mul : ∃ k : ℤ, (n * n : ℚ) * (D * Sum4) = (k : ℚ) := by
    have hn_gt : 1 < n := by omega
    use ((bernoulli (n - 1)).den * ((∑ k ∈ Finset.range n, (k : ℤ) ^ (n - 1)) + 1) - (n * (bernoulli (n - 1)).num + (bernoulli (n - 1)).den) : ℤ)
    rw [← D_sum3_eq_int n hn_gt]
    rw [sum3_eq_n2_sum4 n hn h_odd]
    ring
  have h_cop : Nat.Coprime Sum4.den n := coprime_den_sum4 n hp h_odd hn
  have h_cop_D : Nat.Coprime (D * Sum4).den n := by
    change Nat.Coprime (((bernoulli (n - 1)).den : ℤ) * Sum4).den n
    exact coprime_den_mul_int Sum4 ((bernoulli (n - 1)).den : ℤ) n h_cop
  exact is_int_of_mul_self_is_int_of_coprime (D * Sum4) n h_mul h_cop_D

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
  by_cases hp : n.Prime
  · have hn0 : n ≠ 0 := by omega
    have hn_gt : 1 < n := by omega
    let D : ℤ := (bernoulli (n - 1)).den
    let N : ℤ := (bernoulli (n - 1)).num
    let S : ℤ := ∑ k ∈ Finset.range n, (k : ℤ) ^ (n - 1)
    let X : ℤ := n * N + D
    rcases D_sum4_is_int_of_prime n hp h_odd hn with ⟨k, hk⟩
    have h_id_q : (((D * (S + 1) - X : ℤ) : ℚ)) = (((n * n * k : ℤ) : ℚ)) := by
      rw [← D_sum3_eq_int n hn_gt]
      rw [sum3_eq_n2_sum4 n hn h_odd]
      rw [mul_assoc]
      rw [hk]
      push_cast
      ring
    have h_id : D * (S + 1) - X = n * n * k := by
      exact_mod_cast h_id_q
    have h_X : X = D * (S + 1) - n * n * k := by omega
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
      have h_DS1 : D * (S + 1) = n * n * (m + k) := by
        calc D * (S + 1) = (D * (S + 1) - X) + X := by ring
        _ = n * n * k + (n * N + D) := by rw [h_id]; rfl
        _ = n * n * k + n * n * m := by rw [h_X_eq]
        _ = n * n * (m + k) := by ring
      have h_sub_eq : j * (S + 1) = n * (m + k) := by
        have h_mul : n * (j * (S + 1)) = n * (n * (m + k)) := by
          calc n * (j * (S + 1)) = (n * j) * (S + 1) := by ring
          _ = D * (S + 1) := by rw [← hj_eq]
          _ = n * n * (m + k) := h_DS1
          _ = n * (n * (m + k)) := by ring
        have hn_ne : (n : ℤ) ≠ 0 := by positivity
        exact mul_left_cancel₀ hn_ne h_mul
      have h_N_S1 : N * (S + 1) = n * (m * (S + 1) - (m + k)) := by
        calc N * (S + 1) = (n * m - j) * (S + 1) := by
              have : N = n * m - j := by omega
              rw [this]
             _ = n * m * (S + 1) - j * (S + 1) := by ring
             _ = n * m * (S + 1) - n * (m + k) := by rw [h_sub_eq]
             _ = n * (m * (S + 1) - (m + k)) := by ring
      have h_n_div_N_S1 : (n : ℤ) ∣ N * (S + 1) := ⟨m * (S + 1) - (m + k), h_N_S1⟩
      have h_n_div_N_S1_nat : n ∣ (N * (S + 1)).natAbs := by
        exact Int.natCast_dvd.1 h_n_div_N_S1
      have h_mul_nat : (N * (S + 1)).natAbs = N.natAbs * (S + 1).natAbs := by
        exact Int.natAbs_mul N (S + 1)
      rw [h_mul_nat] at h_n_div_N_S1_nat
      have h_cop : N.natAbs.Coprime (bernoulli (n - 1)).den := (bernoulli (n - 1)).reduced
      have h_n_div_D_z : (n : ℤ) ∣ ((bernoulli (n - 1)).den : ℤ) := by
        have h_n_div_D : (n : ℤ) ∣ D := by
          have h_DS_eq : D * S = n * N + n * n * k := by
            calc D * S = D * (S + 1) - D := by ring
            _ = (X + n * n * k) - D := by linarith
            _ = (n * N + D + n * n * k) - D := rfl
            _ = n * N + n * n * k := by ring
          have h_div_n : (n : ℤ) ∣ D * (S + 1) := by
            have h_nn : (n : ℤ) ∣ (n * n : ℤ) := by use n
            have h_div_D_S : (n * n : ℤ) ∣ D * (S + 1) := by
              rw [h_X]
              have h_div_add : (n * n : ℤ) ∣ D * (S + 1) - n * n * k + n * n * k := dvd_add hm (by use k)
              ring_nf at h_div_add
              exact h_div_add
            exact dvd_trans h_nn h_div_D_S
          have h_n_div_D_S : (n : ℤ) ∣ D * S := by
            rw [h_DS_eq]
            apply dvd_add
            · exact by use N
            · have : (n : ℤ) ∣ n * n * k := by use n * k; ring
              exact this
          have h_sub : (n : ℤ) ∣ D * (S + 1) - D * S := dvd_sub h_div_n h_n_div_D_S
          have h_simpl : D * (S + 1) - D * S = D := by ring
          rwa [h_simpl] at h_sub
        exact h_n_div_D
      have h_n_div_D_nat : n ∣ (bernoulli (n - 1)).den := Int.natCast_dvd_natCast.1 h_n_div_D_z
      have h_cop_n : Nat.Coprime N.natAbs n := Nat.Coprime.of_dvd_right h_n_div_D_nat h_cop
      have h_div_S1_nat : n ∣ (S + 1).natAbs := h_cop_n.symm.dvd_of_dvd_mul_left h_n_div_N_S1_nat
      rwa [Int.natCast_dvd]
    · intro h_div_ag
      have h_n_div_D_S : (n : ℤ) ∣ D * S := by
        have h_DS_eq : D * S = n * N + n * n * k := by
          calc D * S = D * (S + 1) - D := by ring
          _ = (X + n * n * k) - D := by linarith
          _ = (n * N + D + n * n * k) - D := rfl
          _ = n * N + n * n * k := by ring
        rw [h_DS_eq]
        apply dvd_add
        · exact by use N
        · have : (n : ℤ) ∣ n * n * k := by use n * k; ring
          exact this
      have h_n_div_D : (n : ℤ) ∣ D := by
        rcases h_div_ag with ⟨j, hj⟩
        have h_DS_D_eq : D * S + D = D * (S + 1) := by ring
        have h_div_DS_D : (n : ℤ) ∣ D * S + D := by
          rw [h_DS_D_eq, hj]
          use D * j
          ring
        have h_div_D : (n : ℤ) ∣ (D * S + D) - D * S := dvd_sub h_div_DS_D h_n_div_D_S
        have h_simpl : (D * S + D) - D * S = D := by ring
        rwa [h_simpl] at h_div_D
      rcases h_div_ag with ⟨j1, hj1⟩
      rcases h_n_div_D with ⟨j2, hj2⟩
      have h_D_S1 : D * (S + 1) = n * n * (j1 * j2) := by
        rw [hj1, hj2]
        ring
      change (n * n : ℤ) ∣ X
      rw [h_X]
      rw [h_D_S1]
      use j1 * j2 - k
      ring
  · -- composite case
    sorry

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
    by_cases hp : n.Prime
    · have hkey := key_equiv n hn
      have hn_conj := h n hn
      rw [← hn_conj, hkey]
    · -- composite case
      sorry
  · intro h n hn
    by_cases hp : n.Prime
    · have hkey := key_equiv n hn
      have hn_conj := h n hn
      rw [hn_conj, ← hkey]
    · -- composite case
      sorry
"""

with open('/workspace/leanproject/Submission/Spec.lean', 'r') as f:
    lines = f.readlines()

first_part = lines[:326]

with open('/workspace/leanproject/Submission/Spec.lean', 'w') as f:
    f.writelines(first_part)
    f.write("\\n")
    f.write(new_code)

print("Spec.lean updated successfully!")
