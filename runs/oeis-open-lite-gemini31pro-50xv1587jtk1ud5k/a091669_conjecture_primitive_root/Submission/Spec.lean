import FormalConjectures.Util.ProblemImports
open Nat BigOperators



lemma my_ineq (m p j : ℕ) (hp : 1 < p) (hj : 0 < j) :
  m / (p^j) ≤ m / (p^(j-1) * (p-1)) := by
  have hz : j - 1 + 1 = j := Nat.sub_add_cancel hj
  have h1 : p^(j-1) * (p-1) ≤ p^j := by
    rw [← hz, pow_add, pow_one]
    exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have h2 : 0 < p^(j-1) * (p-1) := Nat.mul_pos (by positivity) (Nat.sub_pos_of_lt hp)
  exact Nat.div_le_div_left h1 h2

lemma strict_ineq (c p : ℕ) (hc : 2 ≤ c) (hp : 1 < p) :
  (c * p - 1) / p + 1 ≤ (c * p - 1) / (p - 1) := by
  have hc_pos : 0 < c := by omega
  have hp_pos : 0 < p := by omega
  have h_cp : 0 < c * p := Nat.mul_pos hc_pos hp_pos
  have h1 : (c * p - 1) = (p - 1) + (c - 1) * p := by
    calc
      (c * p - 1) = (c - 1) * p + p - 1 := by
        have h_cp2 : c * p = (c - 1) * p + p := by
          have h_c : c = c - 1 + 1 := by omega
          nth_rw 1 [h_c]
          rw [Nat.add_mul, Nat.one_mul]
        rw [h_cp2]
      _ = (p - 1) + (c - 1) * p := by omega
  have h2 : (c * p - 1) / p = c - 1 := by
    rw [h1, Nat.add_mul_div_right _ _ hp_pos]
    have hp1 : p - 1 < p := by omega
    have hz : (p - 1) / p = 0 := Nat.div_eq_of_lt hp1
    rw [hz, Nat.zero_add]
  rw [h2]
  have h_c_le : c - 1 + 1 = c := by omega
  rw [h_c_le]
  have h_mul : c * (p - 1) ≤ c * p - 1 := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    omega
  have hp_sub_pos : 0 < p - 1 := by omega
  exact (Nat.le_div_iff_mul_le hp_sub_pos).mpr h_mul

lemma sum_split1 (m p : ℕ) (hm : 1 ≤ m) :
  ∑ i ∈ Finset.Ico 1 (m + 1), m / p ^ i = m / p + ∑ i ∈ Finset.range (m - 1), m / p ^ (2 + i) := by
  have h_tmp := Finset.sum_Ico_eq_sum_range (fun i => m / p ^ i) 1 (m + 1)
  have hz : m + 1 - 1 = m := by omega
  rw [hz] at h_tmp
  rw [h_tmp]
  have hz2 : m = m - 1 + 1 := by omega
  nth_rw 1 [hz2]
  rw [Finset.sum_range_succ']
  have hf0 : m / p ^ (1 + 0) = m / p := by simp
  rw [hf0, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  have h_exp : 1 + (x + 1) = 2 + x := by omega
  rw [h_exp]

lemma sum_split2 (m p : ℕ) (hm : 1 ≤ m) :
  ∑ i ∈ Finset.Ico 1 (m + 2), m / (p ^ (i - 1) * (p - 1)) = m / (p - 1) + ∑ i ∈ Finset.range m, m / (p ^ (2 + i - 1) * (p - 1)) := by
  have h_tmp := Finset.sum_Ico_eq_sum_range (fun i => m / (p ^ (i - 1) * (p - 1))) 1 (m + 2)
  have hz : m + 2 - 1 = m + 1 := by omega
  rw [hz] at h_tmp
  rw [h_tmp]
  rw [Finset.sum_range_succ']
  have hf0 : m / (p ^ (1 + 0 - 1) * (p - 1)) = m / (p - 1) := by simp
  rw [hf0, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  have h_exp : 1 + (x + 1) - 1 = 2 + x - 1 := by omega
  rw [h_exp]

lemma sum_shift (m p : ℕ) (M : ℕ) (hM : M = m / (p - 1)) :
  M + ∑ i ∈ Finset.Ico 1 (m + 1), M / p ^ i = ∑ i ∈ Finset.Ico 1 (m + 2), m / (p ^ (i - 1) * (p - 1)) := by
  have hz : m + 2 - 1 = m + 1 := by omega
  have h1 : ∑ i ∈ Finset.Ico 1 (m + 2), m / (p ^ (i - 1) * (p - 1)) = ∑ i ∈ Finset.range (m + 1), m / (p ^ (1 + i - 1) * (p - 1)) := by
    have h_tmp := Finset.sum_Ico_eq_sum_range (fun i => m / (p ^ (i - 1) * (p - 1))) 1 (m + 2)
    rw [hz] at h_tmp
    exact h_tmp
  rw [h1]
  have hz2 : m + 1 - 1 = m := by omega
  have h2 : ∑ i ∈ Finset.Ico 1 (m + 1), M / p ^ i = ∑ i ∈ Finset.range m, M / p ^ (1 + i) := by
    have h_tmp := Finset.sum_Ico_eq_sum_range (fun i => M / p ^ i) 1 (m + 1)
    rw [hz2] at h_tmp
    exact h_tmp
  rw [h2]
  have h_tmp := Finset.sum_range_succ' (fun i => m / (p ^ (1 + i - 1) * (p - 1))) m
  rw [h_tmp]
  have h_f0 : m / (p ^ (1 + 0 - 1) * (p - 1)) = M := by
    simp [hM]
  rw [h_f0]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  have h_exp : 1 + (x + 1) - 1 = 1 + x := by omega
  rw [h_exp]
  have h_eq2 : M / p ^ (1 + x) = m / (p ^ (1 + x) * (p - 1)) := by
    rw [hM]
    have h_div : (m / (p - 1)) / p ^ (1 + x) = m / ((p - 1) * p ^ (1 + x)) := Nat.div_div_eq_div_mul _ _ _
    rw [h_div, mul_comm (p - 1)]
  rw [h_eq2]

lemma val_fact_le_M_plus_val_M_fact (m p : ℕ) [hp_prime : Fact p.Prime] (hp : Odd p) :
  let M := m / (p - 1)
  padicValNat p (m.factorial) ≤ M + padicValNat p (M.factorial) := by
  intro M
  have hp_gt : 1 < p := hp_prime.out.one_lt
  by_cases hm : m = 0
  · simp [hm]
  have h_log_m : Nat.log p m < m + 1 := Nat.lt_succ_of_le (Nat.log_le_self p m)
  have h_log_M : Nat.log p M < m + 1 := by
    apply Nat.lt_of_le_of_lt (Nat.log_le_self p M)
    apply Nat.lt_succ_of_le
    exact Nat.div_le_self m (p - 1)
  rw [padicValNat_factorial h_log_m, padicValNat_factorial h_log_M]
  have h_eq : M + ∑ i ∈ Finset.Ico 1 (m + 1), M / p ^ i = ∑ i ∈ Finset.Ico 1 (m + 2), m / (p ^ (i - 1) * (p - 1)) := sum_shift m p M rfl
  rw [h_eq]
  have h_sub : Finset.Ico 1 (m + 1) ⊆ Finset.Ico 1 (m + 2) := Finset.Ico_subset_Ico (by rfl) (by omega)
  have h_sum_le : ∑ i ∈ Finset.Ico 1 (m + 1), m / (p ^ (i - 1) * (p - 1)) ≤ ∑ i ∈ Finset.Ico 1 (m + 2), m / (p ^ (i - 1) * (p - 1)) :=
    Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun i _ _ => Nat.zero_le _)
  have h_term_le : ∑ i ∈ Finset.Ico 1 (m + 1), m / p ^ i ≤ ∑ i ∈ Finset.Ico 1 (m + 1), m / (p ^ (i - 1) * (p - 1)) := by
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_Ico] at hi
    exact my_ineq m p i hp_gt hi.1
  exact Nat.le_trans h_term_le h_sum_le

lemma hm_proof (c p m : ℕ) (hc : 2 ≤ c) (hp : 1 < p) (hm_eq : m = c * p - 1) : 1 ≤ m := by
  have h_cp : 4 ≤ c * p := Nat.mul_le_mul hc hp
  omega

lemma val_fact_le_M_plus_val_M_fact_strict (c p m M : ℕ) [hp_prime : Fact p.Prime] (hp : Odd p) (hc : 2 ≤ c)
  (hm_eq : m = c * p - 1) (hM_eq : M = m / (p - 1)) :
  padicValNat p (m.factorial) + 1 ≤ M + padicValNat p (M.factorial) := by
  have hp_gt : 1 < p := hp_prime.out.one_lt
  have h_log_m : Nat.log p m < m + 1 := Nat.lt_succ_of_le (Nat.log_le_self p m)
  have h_log_M : Nat.log p M < m + 1 := by
    apply Nat.lt_of_le_of_lt (Nat.log_le_self p M)
    apply Nat.lt_succ_of_le
    rw [hM_eq]
    exact Nat.div_le_self m (p - 1)
  rw [padicValNat_factorial h_log_m, padicValNat_factorial h_log_M]
  have h_eq : M + ∑ i ∈ Finset.Ico 1 (m + 1), M / p ^ i = ∑ i ∈ Finset.Ico 1 (m + 2), m / (p ^ (i - 1) * (p - 1)) := sum_shift m p M hM_eq
  have hm : 1 ≤ m := hm_proof c p m hc hp_gt hm_eq
  have h_split1 : ∑ i ∈ Finset.Ico 1 (m + 1), m / p ^ i = m / p + ∑ i ∈ Finset.range (m - 1), m / p ^ (2 + i) := sum_split1 m p hm
  have h_split2 : ∑ i ∈ Finset.Ico 1 (m + 2), m / (p ^ (i - 1) * (p - 1)) = m / (p - 1) + ∑ i ∈ Finset.range m, m / (p ^ (2 + i - 1) * (p - 1)) := sum_split2 m p hm
  
  have h_term_1 : m / p + 1 ≤ m / (p - 1) := by
    rw [hm_eq]
    exact strict_ineq c p hc hp_gt
  have h_sum_le : ∑ i ∈ Finset.range (m - 1), m / p ^ (2 + i) ≤ ∑ i ∈ Finset.range m, m / (p ^ (2 + i - 1) * (p - 1)) := by
    have h_sub : Finset.range (m - 1) ⊆ Finset.range m := by
      intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    have h_sum_le_range := Finset.sum_le_sum_of_subset_of_nonneg (f := fun i => m / (p ^ (2 + i - 1) * (p - 1))) h_sub (fun i _ _ => Nat.zero_le _)
    have h_term_le : ∑ i ∈ Finset.range (m - 1), m / p ^ (2 + i) ≤ ∑ i ∈ Finset.range (m - 1), m / (p ^ (2 + i - 1) * (p - 1)) := by
      apply Finset.sum_le_sum
      intro i _
      have hj : 0 < 2 + i := by omega
      exact my_ineq m p (2 + i) hp_gt hj
    exact Nat.le_trans h_term_le h_sum_le_range
  have h_add_le : m / p + 1 + ∑ i ∈ Finset.range (m - 1), m / p ^ (2 + i) ≤ m / (p - 1) + ∑ i ∈ Finset.range m, m / (p ^ (2 + i - 1) * (p - 1)) :=
    Nat.add_le_add h_term_1 h_sum_le
  
  calc
    (∑ i ∈ Finset.Ico 1 (m + 1), m / p ^ i) + 1 = m / p + ∑ i ∈ Finset.range (m - 1), m / p ^ (2 + i) + 1 := by rw [h_split1]
    _ = m / p + 1 + ∑ i ∈ Finset.range (m - 1), m / p ^ (2 + i) := by omega
    _ ≤ m / (p - 1) + ∑ i ∈ Finset.range m, m / (p ^ (2 + i - 1) * (p - 1)) := h_add_le
    _ = ∑ i ∈ Finset.Ico 1 (m + 2), m / (p ^ (i - 1) * (p - 1)) := h_split2.symm
    _ = M + ∑ i ∈ Finset.Ico 1 (m + 1), M / p ^ i := h_eq.symm

lemma sum_multiples_le (m p : ℕ) (hp : 0 < p) (f : ℕ → ℕ) :
  ∑ c ∈ Finset.Ico 1 (m / p + 1), f (c * p) ≤ ∑ k ∈ Finset.Ico 1 (m + 1), f k := by
  let g := fun c => c * p
  have h_inj : Set.InjOn g (Finset.Ico 1 (m / p + 1)) := by
    intro x _ y _ hxy
    dsimp [g] at hxy
    exact Nat.eq_of_mul_eq_mul_right hp hxy
  have h_sub : (Finset.Ico 1 (m / p + 1)).image g ⊆ Finset.Ico 1 (m + 1) := by
    intro k hk
    rw [Finset.mem_image] at hk
    rcases hk with ⟨c, hc, rfl⟩
    rw [Finset.mem_Ico] at hc ⊢
    constructor
    · exact Nat.mul_pos hc.1 hp
    · exact Nat.succ_le_succ ((Nat.le_div_iff_mul_le hp).mp (Nat.le_of_lt_succ hc.2))
  have heq : ∑ c ∈ Finset.Ico 1 (m / p + 1), f (c * p) = ∑ k ∈ (Finset.Ico 1 (m / p + 1)).image g, f k := by
    exact (Finset.sum_image h_inj).symm
  rw [heq]
  exact Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun _ _ _ => Nat.zero_le _)

lemma padicValNat_prod {p : ℕ} [Fact p.Prime] (s : Finset ℕ) (f : ℕ → ℕ) (hf : ∀ x ∈ s, f x ≠ 0) :
  padicValNat p (∏ x ∈ s, f x) = ∑ x ∈ s, padicValNat p (f x) := by
  induction s using Finset.cons_induction with
  | empty => simp [padicValNat.one]
  | cons a s has ih =>
    rw [Finset.prod_cons, Finset.sum_cons]
    have h1 : f a ≠ 0 := hf a (Finset.mem_cons_self a s)
    have h2 : (∏ x ∈ s, f x) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun x hx => hf x (Finset.mem_cons_of_mem hx))
    rw [padicValNat.mul h1 h2]
    congr 1
    exact ih (fun x hx => hf x (Finset.mem_cons_of_mem hx))

lemma lte_lower_bound (p c : ℕ) [hp_prime : Fact p.Prime] (hp : Odd p) (hc : c ≠ 0) :
  padicValNat p c + 1 ≤ padicValNat p ((2^(p-1))^c - 1) := by
  have hp_gt : 1 < p := hp_prime.out.one_lt
  have hp_pos : p - 1 ≠ 0 := (Nat.sub_pos_of_lt hp_gt).ne'
  have hp1 : 1 < 2^(p-1) := Nat.one_lt_pow hp_pos (by decide)

  have h_not_dvd_2 : ¬ p ∣ 2 := by
    intro h
    have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp_prime.out Nat.prime_two).mp h
    have odd2 : Odd 2 := by rw [← this]; exact hp
    contradiction

  have hp_dvd : p ∣ 2^(p-1) - 1 := by
    have h1 : (2 : ZMod p) ≠ 0 := by
      intro h
      have h2 : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
      exact h_not_dvd_2 h2
    have h2 : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h1
    have h3 : ((2^(p-1) : ℕ) : ZMod p) = 1 := by push_cast; exact h2
    have h4 : ((2^(p-1) - 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub (Nat.le_of_lt hp1)]
      rw [h3]
      push_cast
      exact sub_self 1
    exact (CharP.cast_eq_zero_iff (ZMod p) p _).mp h4

  have h_not_dvd : ¬ p ∣ 2^(p-1) := by
    intro h
    exact h_not_dvd_2 (hp_prime.out.dvd_of_dvd_pow h)

  have h_lte := padicValNat.pow_sub_pow hp hp1 hp_dvd h_not_dvd hc
  have h_one : 1 ^ c = 1 := Nat.one_pow c
  have h_eq : padicValNat p ((2^(p-1))^c - 1) = padicValNat p ((2^(p-1))^c - 1^c) := by rw [h_one]
  rw [h_eq, h_lte]
  have h_base : 1 ≤ padicValNat p (2^(p-1) - 1) := by
    have h0 : 2^(p-1) - 1 ≠ 0 := (Nat.sub_pos_of_lt hp1).ne'
    have h_pow_dvd : p^1 ∣ 2^(p-1) - 1 := by rw [pow_one]; exact hp_dvd
    exact (padicValNat_dvd_iff_le h0).mp h_pow_dvd
  omega

lemma factorial_eq_prod_Ico (m : ℕ) : m.factorial = ∏ c ∈ Finset.Ico 1 (m + 1), c := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Nat.factorial_succ, ih]
    have h : 1 ≤ k + 1 := by omega
    rw [Finset.prod_Ico_succ_top h]
    exact mul_comm _ _

lemma padicValNat_factorial_eq_sum (m p : ℕ) [Fact p.Prime] :
  padicValNat p (m.factorial) = ∑ c ∈ Finset.Ico 1 (m + 1), padicValNat p c := by
  rw [factorial_eq_prod_Ico m]
  apply padicValNat_prod
  intro x hx
  rw [Finset.mem_Ico] at hx
  omega

lemma P_val_bound (m p : ℕ) [hp_prime : Fact p.Prime] (hp : Odd p) :
  padicValNat p (m.factorial) ≤ padicValNat p (∏ k ∈ Finset.Ico 1 (m + 1), (2^k - 1)) := by
  let M := m / (p - 1)
  have hp_gt : 1 < p := hp_prime.out.one_lt
  have hp_sub : 0 < p - 1 := Nat.sub_pos_of_lt hp_gt
  have h_fact_le : padicValNat p (m.factorial) ≤ M + padicValNat p (M.factorial) := val_fact_le_M_plus_val_M_fact m p hp
  have h_P_val : padicValNat p (∏ k ∈ Finset.Ico 1 (m + 1), (2^k - 1)) = ∑ k ∈ Finset.Ico 1 (m + 1), padicValNat p (2^k - 1) := by
    apply padicValNat_prod
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk_pos : k ≠ 0 := by omega
    have h1 : 1 < 2^k := Nat.one_lt_pow hk_pos (by decide)
    exact (Nat.sub_pos_of_lt h1).ne'
  rw [h_P_val]
  have h_sum_le : ∑ c ∈ Finset.Ico 1 (M + 1), padicValNat p (2^(c*(p-1)) - 1) ≤ ∑ k ∈ Finset.Ico 1 (m + 1), padicValNat p (2^k - 1) := by
    exact sum_multiples_le m (p - 1) hp_sub (fun k => padicValNat p (2^k - 1))
  have h_M_fact : padicValNat p (M.factorial) = ∑ c ∈ Finset.Ico 1 (M + 1), padicValNat p c := padicValNat_factorial_eq_sum M p
  have h_bound2 : M + padicValNat p (M.factorial) = ∑ c ∈ Finset.Ico 1 (M + 1), (1 + padicValNat p c) := by
    rw [h_M_fact, Finset.sum_add_distrib]
    have h_ones : ∑ c ∈ Finset.Ico 1 (M + 1), 1 = M := by simp
    rw [h_ones]
  rw [h_bound2] at h_fact_le
  have h_term_le : ∑ c ∈ Finset.Ico 1 (M + 1), (1 + padicValNat p c) ≤ ∑ c ∈ Finset.Ico 1 (M + 1), padicValNat p (2^(c*(p-1)) - 1) := by
    apply Finset.sum_le_sum
    intro c hc
    rw [Finset.mem_Ico] at hc
    have h_c_pos : c ≠ 0 := by omega
    have h_lte := lte_lower_bound p c hp h_c_pos
    have h_pow_pow : (2 ^ (p - 1)) ^ c = 2 ^ (c * (p - 1)) := by rw [← pow_mul, mul_comm]
    rw [h_pow_pow] at h_lte
    omega
  exact Nat.le_trans h_fact_le (Nat.le_trans h_term_le h_sum_le)

lemma P_val_bound_strict (c p m : ℕ) [hp_prime : Fact p.Prime] (hp : Odd p) (hc : 2 ≤ c) (hm_eq : m = c * p - 1) :
  padicValNat p (m.factorial) + 1 ≤ padicValNat p (∏ k ∈ Finset.Ico 1 (m + 1), (2^k - 1)) := by
  let M := m / (p - 1)
  have hp_gt : 1 < p := hp_prime.out.one_lt
  have hp_sub : 0 < p - 1 := Nat.sub_pos_of_lt hp_gt
  have h_fact_le : padicValNat p (m.factorial) + 1 ≤ M + padicValNat p (M.factorial) := val_fact_le_M_plus_val_M_fact_strict c p m M hp hc hm_eq rfl
  have h_P_val : padicValNat p (∏ k ∈ Finset.Ico 1 (m + 1), (2^k - 1)) = ∑ k ∈ Finset.Ico 1 (m + 1), padicValNat p (2^k - 1) := by
    apply padicValNat_prod
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk_pos : k ≠ 0 := by omega
    have h1 : 1 < 2^k := Nat.one_lt_pow hk_pos (by decide)
    exact (Nat.sub_pos_of_lt h1).ne'
  rw [h_P_val]
  have h_sum_le : ∑ c ∈ Finset.Ico 1 (M + 1), padicValNat p (2^(c*(p-1)) - 1) ≤ ∑ k ∈ Finset.Ico 1 (m + 1), padicValNat p (2^k - 1) := by
    exact sum_multiples_le m (p - 1) hp_sub (fun k => padicValNat p (2^k - 1))
  have h_M_fact : padicValNat p (M.factorial) = ∑ c ∈ Finset.Ico 1 (M + 1), padicValNat p c := padicValNat_factorial_eq_sum M p
  have h_bound2 : M + padicValNat p (M.factorial) = ∑ c ∈ Finset.Ico 1 (M + 1), (1 + padicValNat p c) := by
    rw [h_M_fact, Finset.sum_add_distrib]
    have h_ones : ∑ c ∈ Finset.Ico 1 (M + 1), 1 = M := by simp
    rw [h_ones]
  rw [h_bound2] at h_fact_le
  have h_term_le : ∑ c ∈ Finset.Ico 1 (M + 1), (1 + padicValNat p c) ≤ ∑ c ∈ Finset.Ico 1 (M + 1), padicValNat p (2^(c*(p-1)) - 1) := by
    apply Finset.sum_le_sum
    intro c hc
    rw [Finset.mem_Ico] at hc
    have h_c_pos : c ≠ 0 := by omega
    have h_lte := lte_lower_bound p c hp h_c_pos
    have h_pow_pow : (2 ^ (p - 1)) ^ c = 2 ^ (c * (p - 1)) := by rw [← pow_mul, mul_comm]
    rw [h_pow_pow] at h_lte
    omega
  exact Nat.le_trans h_fact_le (Nat.le_trans h_term_le h_sum_le)

lemma my_ineq_m_minus_1 (m p j : ℕ) (hp : 1 < p) (hj : 0 < j) :
  m / (p^j) ≤ (m - 1) / (p^(j-1) * (p-1)) := by
  by_cases h : m / (p^j) = 0
  · rw [h]
    exact Nat.zero_le _
  · have hx : 1 ≤ m / (p^j) := Nat.pos_of_ne_zero h
    have hm : (m / p^j) * p^j ≤ m := Nat.div_mul_le_self m (p^j)
    have hpj : 0 < p^(j-1) := by positivity
    have hp1 : 0 < p - 1 := by omega
    have h_denom : p^(j-1) * (p-1) = p^j - p^(j-1) := by
      rw [Nat.mul_sub_left_distrib, mul_one]
      have hz : j - 1 + 1 = j := Nat.sub_add_cancel hj
      have h1 : p^(j-1) * p = p^j := by
        calc
          p^(j-1) * p = p^(j-1) * p^1 := by rw [pow_one]
          _ = p^(j-1+1) := by rw [← pow_add]
          _ = p^j := by rw [hz]
      rw [h1]
    have h_mul_sub : (m / p^j) * (p^j - p^(j-1)) = (m / p^j) * p^j - (m / p^j) * p^(j-1) := Nat.mul_sub_left_distrib _ _ _
    have h_le1 : (m / p^j) * (p^j - p^(j-1)) ≤ m - 1 := by
      rw [h_mul_sub]
      have h_sub_pos : 1 ≤ (m / p^j) * p^(j-1) := Nat.mul_pos hx hpj
      omega
    rw [h_denom]
    have h_pos_denom : 0 < p^j - p^(j-1) := by
      rw [← h_denom]
      exact Nat.mul_pos hpj hp1
    exact (Nat.le_div_iff_mul_le h_pos_denom).mpr h_le1

lemma val_fact_le_M_plus_val_M_fact_minus_1 (m p : ℕ) [hp_prime : Fact p.Prime] (hp : Odd p) (hm : 1 ≤ m) :
  let M := (m - 1) / (p - 1)
  padicValNat p (m.factorial) ≤ M + padicValNat p (M.factorial) := by
  intro M
  have hp_gt : 1 < p := hp_prime.out.one_lt
  have h_log_m : Nat.log p m < m + 1 := Nat.lt_succ_of_le (Nat.log_le_self p m)
  have h_log_M : Nat.log p M < m + 1 := by
    apply Nat.lt_of_le_of_lt (Nat.log_le_self p M)
    apply Nat.lt_succ_of_le
    calc
      M ≤ m - 1 := Nat.div_le_self (m - 1) (p - 1)
      _ ≤ m := by omega
  rw [padicValNat_factorial h_log_m, padicValNat_factorial h_log_M]
  have h_eq : M + ∑ i ∈ Finset.Ico 1 m, M / p ^ i = ∑ i ∈ Finset.Ico 1 (m + 1), (m - 1) / (p ^ (i - 1) * (p - 1)) := by
    have h_shift := sum_shift (m - 1) p M rfl
    have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel hm
    have hm2 : m - 1 + 2 = m + 1 := by omega
    rw [hm1, hm2] at h_shift
    exact h_shift
    
  have h_eq2 : M + ∑ i ∈ Finset.Ico 1 (m + 1), M / p ^ i = M + ∑ i ∈ Finset.Ico 1 m, M / p ^ i + M / p ^ m := by
    have h_split := Finset.sum_Ico_succ_top (by omega : 1 ≤ m) (fun i => M / p ^ i)
    rw [h_split, add_assoc]
    
  have h_M_zero : M / p ^ m = 0 := by
    have h_pow : m ≤ p ^ m := le_of_lt (Nat.lt_pow_self hp_gt)
    have h_M_lt : M < p ^ m := by
      calc
        M ≤ m - 1 := Nat.div_le_self (m - 1) (p - 1)
        _ < m := by omega
        _ ≤ p ^ m := h_pow
    exact Nat.div_eq_of_lt h_M_lt
    
  rw [h_eq2, h_M_zero, add_zero, h_eq]
  
  have h_term_le : ∑ i ∈ Finset.Ico 1 (m + 1), m / p ^ i ≤ ∑ i ∈ Finset.Ico 1 (m + 1), (m - 1) / (p ^ (i - 1) * (p - 1)) := by
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_Ico] at hi
    exact my_ineq_m_minus_1 m p i hp_gt hi.1
  exact h_term_le

lemma P_val_bound_minus_1 (m p : ℕ) [hp_prime : Fact p.Prime] (hp : Odd p) (hm : 1 ≤ m) :
  padicValNat p (m.factorial) ≤ padicValNat p (∏ k ∈ Finset.Ico 1 m, (2^k - 1)) := by
  let M := (m - 1) / (p - 1)
  have hp_gt : 1 < p := hp_prime.out.one_lt
  have hp_sub : 0 < p - 1 := Nat.sub_pos_of_lt hp_gt
  have h_fact_le : padicValNat p (m.factorial) ≤ M + padicValNat p (M.factorial) := val_fact_le_M_plus_val_M_fact_minus_1 m p hp hm
  
  have h_P_val : padicValNat p (∏ k ∈ Finset.Ico 1 m, (2^k - 1)) = ∑ k ∈ Finset.Ico 1 m, padicValNat p (2^k - 1) := by
    apply padicValNat_prod
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk_pos : k ≠ 0 := by omega
    have h1 : 1 < 2^k := Nat.one_lt_pow hk_pos (by decide)
    exact (Nat.sub_pos_of_lt h1).ne'
  rw [h_P_val]
  
  have h_sum_le : ∑ c ∈ Finset.Ico 1 (M + 1), padicValNat p (2^(c*(p-1)) - 1) ≤ ∑ k ∈ Finset.Ico 1 m, padicValNat p (2^k - 1) := by
    exact sum_multiples_le (m - 1) (p - 1) hp_sub (fun k => padicValNat p (2^k - 1))
    
  have h_M_fact : padicValNat p (M.factorial) = ∑ c ∈ Finset.Ico 1 (M + 1), padicValNat p c := padicValNat_factorial_eq_sum M p
  have h_bound2 : M + padicValNat p (M.factorial) = ∑ c ∈ Finset.Ico 1 (M + 1), (1 + padicValNat p c) := by
    rw [h_M_fact, Finset.sum_add_distrib]
    have h_ones : ∑ c ∈ Finset.Ico 1 (M + 1), 1 = M := by simp
    rw [h_ones]
  rw [h_bound2] at h_fact_le
  
  have h_term_le : ∑ c ∈ Finset.Ico 1 (M + 1), (1 + padicValNat p c) ≤ ∑ c ∈ Finset.Ico 1 (M + 1), padicValNat p (2^(c*(p-1)) - 1) := by
    apply Finset.sum_le_sum
    intro c hc
    rw [Finset.mem_Ico] at hc
    have h_c_pos : c ≠ 0 := by omega
    have h_lte := lte_lower_bound p c hp h_c_pos
    have h_pow_pow : (2 ^ (p - 1)) ^ c = 2 ^ (c * (p - 1)) := by rw [← pow_mul, mul_comm]
    rw [h_pow_pow] at h_lte
    omega
    

  exact Nat.le_trans h_fact_le (Nat.le_trans h_term_le h_sum_le)

lemma div_p_eq (c p : ℕ) (hc : 1 ≤ c) (hp : 1 < p) : (c * p - 1) / p = c - 1 := by
  have hc_pos : 0 < c := hc
  have hp_pos : 0 < p := by omega
  have h1 : (c * p - 1) = (p - 1) + (c - 1) * p := by
    calc
      (c * p - 1) = (c - 1) * p + p - 1 := by
        have h_cp2 : c * p = (c - 1) * p + p := by
          have h_c : c = c - 1 + 1 := by omega
          nth_rw 1 [h_c]
          rw [Nat.add_mul, Nat.one_mul]
        rw [h_cp2]
      _ = (p - 1) + (c - 1) * p := by omega
  rw [h1, Nat.add_mul_div_right _ _ hp_pos]
  have hp1 : p - 1 < p := by omega
  have hz : (p - 1) / p = 0 := Nat.div_eq_of_lt hp1
  rw [hz, Nat.zero_add]

lemma div_p_pow_eq (c p j : ℕ) (hc : 1 ≤ c) (hp : 1 < p) :
  (c * p - 1) / p ^ (2 + j) = (c - 1) / p ^ (1 + j) := by
  have h_pow : p ^ (2 + j) = p * p ^ (1 + j) := by
    calc
      p ^ (2 + j) = p ^ (1 + (1 + j)) := by congr 1; omega
      _ = p ^ 1 * p ^ (1 + j) := by rw [pow_add]
      _ = p * p ^ (1 + j) := by rw [pow_one]
  rw [h_pow]
  rw [← Nat.div_div_eq_div_mul]
  rw [div_p_eq c p hc hp]

lemma padicValNat_cp_minus_1_fact (c p : ℕ) [hp_prime : Fact p.Prime] (hc : 1 ≤ c) :
  padicValNat p ((c * p - 1).factorial) = c - 1 + padicValNat p ((c - 1).factorial) := by
  have hp_gt : 1 < p := hp_prime.out.one_lt
  let m := c * p - 1
  have h_log_m : Nat.log p m < m + 1 := Nat.lt_succ_of_le (Nat.log_le_self p m)
  have h_log_c : Nat.log p (c - 1) < m + 1 := by
    apply Nat.lt_of_le_of_lt (Nat.log_le_self p (c - 1))
    apply Nat.lt_succ_of_le
    have h_le : c ≤ c * p := Nat.le_mul_of_pos_right c (by omega)
    exact Nat.sub_le_sub_right h_le 1
  rw [padicValNat_factorial h_log_m, padicValNat_factorial h_log_c]
  have hm_pos : 1 ≤ m := by
    have h_2 : 2 ≤ p := hp_gt
    have h_c : 1 ≤ c := hc
    have h_mul : 2 ≤ c * p := by
      calc
        2 = 1 * 2 := by rfl
        _ ≤ c * p := Nat.mul_le_mul h_c h_2
    omega
  have h_split := sum_split1 m p hm_pos
  rw [h_split]
  have h_div : m / p = c - 1 := div_p_eq c p hc hp_gt
  rw [h_div]
  congr 1
  have h_sum_c : ∑ i ∈ Finset.Ico 1 (m + 1), (c - 1) / p ^ i = ∑ i ∈ Finset.range m, (c - 1) / p ^ (1 + i) := by
    have h_tmp := Finset.sum_Ico_eq_sum_range (fun i => (c - 1) / p ^ i) 1 (m + 1)
    have hz : m + 1 - 1 = m := by omega
    rw [hz] at h_tmp
    exact h_tmp
  rw [h_sum_c]
  
  have h_sum_split2 : ∑ i ∈ Finset.range m, (c - 1) / p ^ (1 + i) = ∑ i ∈ Finset.range (m - 1), (c - 1) / p ^ (1 + i) + (c - 1) / p ^ (1 + (m - 1)) := by
    have hm1 : m = m - 1 + 1 := by omega
    nth_rw 1 [hm1]
    rw [Finset.sum_range_succ]
  rw [h_sum_split2]
  have h_zero : (c - 1) / p ^ (1 + (m - 1)) = 0 := by
    have h_pow : c - 1 < p ^ (1 + (m - 1)) := by
      calc
        c - 1 ≤ m := by
          have h_le : c ≤ c * p := Nat.le_mul_of_pos_right c (by omega)
          exact Nat.sub_le_sub_right h_le 1
        _ < p ^ m := Nat.lt_pow_self hp_gt
        _ = p ^ (1 + (m - 1)) := by
          congr 1
          omega
    exact Nat.div_eq_of_lt h_pow
  rw [h_zero, add_zero]
  
  apply Finset.sum_congr rfl
  intro x _
  exact div_p_pow_eq c p x hc hp_gt

lemma sum_multiples_le_c (m p c : ℕ) (hp : 0 < p) (hc : c * p ≤ m) (f : ℕ → ℕ) :
  ∑ k ∈ Finset.Ico 1 (c + 1), f (k * p) ≤ ∑ k ∈ Finset.Ico 1 (m + 1), f k := by
  let g := fun k => k * p
  have h_inj : Set.InjOn g (Finset.Ico 1 (c + 1)) := by
    intro x _ y _ hxy
    dsimp [g] at hxy
    exact Nat.eq_of_mul_eq_mul_right hp hxy
  have h_sub : (Finset.Ico 1 (c + 1)).image g ⊆ Finset.Ico 1 (m + 1) := by
    intro k hk
    rw [Finset.mem_image] at hk
    rcases hk with ⟨x, hx, rfl⟩
    rw [Finset.mem_Ico] at hx ⊢
    constructor
    · have hx_pos : 1 ≤ x := hx.1
      have hp_pos : 1 ≤ p := hp
      calc
        1 = 1 * 1 := rfl
        _ ≤ x * p := Nat.mul_le_mul hx_pos hp_pos
    · calc
        x * p ≤ c * p := Nat.mul_le_mul_right p (by omega)
        _ ≤ m := hc
        _ < m + 1 := by omega
  have h_eq : ∑ k ∈ Finset.Ico 1 (c + 1), f (k * p) = ∑ k ∈ (Finset.Ico 1 (c + 1)).image g, f k := by
    rw [Finset.sum_image h_inj]
  rw [h_eq]
  exact Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun _ _ _ => Nat.zero_le _)

lemma P_val_bound_minus_1_strict (c p m : ℕ) [hp_prime : Fact p.Prime] (hp : Odd p) (hc : 2 ≤ c) (hm_eq : m = c * p - 1) :
  padicValNat p (m.factorial) + 1 ≤ padicValNat p (∏ k ∈ Finset.Ico 1 m, (2^k - 1)) := by
  have hp_gt : 1 < p := hp_prime.out.one_lt
  have hp_sub : 0 < p - 1 := Nat.sub_pos_of_lt hp_gt
  
  have h_m_pos : 1 ≤ m := by
    have h1 : 4 ≤ c * p := by
      have hp2 : 2 ≤ p := hp_gt
      calc
        4 = 2 * 2 := rfl
        _ ≤ c * p := Nat.mul_le_mul hc hp2
    omega
  
  have h_P_val : padicValNat p (∏ k ∈ Finset.Ico 1 m, (2^k - 1)) = ∑ k ∈ Finset.Ico 1 m, padicValNat p (2^k - 1) := by
    apply padicValNat_prod
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk_pos : k ≠ 0 := by omega
    have h1 : 1 < 2^k := Nat.one_lt_pow hk_pos (by decide)
    exact (Nat.sub_pos_of_lt h1).ne'
  rw [h_P_val]
  
  have h_fact_val : padicValNat p (m.factorial) = c - 1 + padicValNat p ((c - 1).factorial) := by
    rw [hm_eq]
    have hc_pos : 1 ≤ c := by omega
    apply padicValNat_cp_minus_1_fact c p hc_pos
    
  have h_c_fact : padicValNat p ((c - 1).factorial) = ∑ k ∈ Finset.Ico 1 c, padicValNat p k := by
    exact padicValNat_factorial_eq_sum (c - 1) p
    
  have h_fact_val2 : padicValNat p (m.factorial) = ∑ k ∈ Finset.Ico 1 c, (1 + padicValNat p k) := by
    rw [h_fact_val, h_c_fact, Finset.sum_add_distrib]
    have h_ones : ∑ k ∈ Finset.Ico 1 c, 1 = c - 1 := by
      have h1 : ∑ k ∈ Finset.Ico 1 c, 1 = c - 1 := by simp
      exact h1
    rw [h_ones]
  
  have h_c_add : padicValNat p (m.factorial) + (1 + padicValNat p c) = ∑ k ∈ Finset.Ico 1 (c + 1), (1 + padicValNat p k) := by
    have h_split := Finset.sum_Ico_succ_top (by omega : 1 ≤ c) (fun k => 1 + padicValNat p k)
    rw [h_split, ← h_fact_val2]
    
  have h_term_le : ∑ k ∈ Finset.Ico 1 (c + 1), (1 + padicValNat p k) ≤ ∑ k ∈ Finset.Ico 1 (c + 1), padicValNat p (2^(k*(p-1)) - 1) := by
    apply Finset.sum_le_sum
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk_pos : k ≠ 0 := by omega
    have h_lte := lte_lower_bound p k hp hk_pos
    have h_pow_pow : (2 ^ (p - 1)) ^ k = 2 ^ (k * (p - 1)) := by rw [← pow_mul, mul_comm]
    rw [h_pow_pow] at h_lte
    -- h_lte : padicValNat p k + 1 <= padicValNat p (2 ^ (k * (p - 1)) - 1)
    have : 1 + padicValNat p k = padicValNat p k + 1 := add_comm _ _
    rw [this]
    exact h_lte
    
  have h_sum_le : ∑ k ∈ Finset.Ico 1 (c + 1), padicValNat p (2^(k*(p-1)) - 1) ≤ ∑ k ∈ Finset.Ico 1 m, padicValNat p (2^k - 1) := by
    have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel h_m_pos
    have h_c_le : c * (p - 1) ≤ m - 1 := by
      rw [hm_eq]
      have hcp2 : c * p - 2 ≤ c * p - 2 := le_rfl
      calc
        c * (p - 1) = c * p - c := by rw [Nat.mul_sub_left_distrib, mul_one]
        _ ≤ c * p - 2 := by
          have h2c : 2 ≤ c := hc
          exact Nat.sub_le_sub_left h2c (c * p)
        _ = c * p - 1 - 1 := by omega
    have h_le := sum_multiples_le_c (m - 1) (p - 1) c hp_sub h_c_le (fun k => padicValNat p (2^k - 1))
    rw [hm1] at h_le
    exact h_le
    
  have h_base_strict : padicValNat p (m.factorial) + 1 ≤ padicValNat p (m.factorial) + (1 + padicValNat p c) := by
    have : 1 ≤ 1 + padicValNat p c := by omega
    exact Nat.add_le_add_left this _
    
  exact Nat.le_trans h_base_strict (Nat.le_trans (le_of_eq h_c_add) (Nat.le_trans h_term_le h_sum_le))

lemma factorial_dvd_a_num (m : ℕ) (hm : 1 ≤ m) :
  m.factorial ∣ (2 ^ (m - 1)) * ∏ k ∈ Finset.Ico 1 m, (2 ^ k - 1) := by
  have hm0 : m.factorial ≠ 0 := factorial_ne_zero m
  have h_P_ne : ∏ k ∈ Finset.Ico 1 m, (2 ^ k - 1) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk_pos : k ≠ 0 := by omega
    have h1 : 1 < 2 ^ k := Nat.one_lt_pow hk_pos (by decide)
    exact (Nat.sub_pos_of_lt h1).ne'
  have h_pow_pos : 0 < 2 ^ (m - 1) := by positivity
  have h_pow_ne : 2 ^ (m - 1) ≠ 0 := h_pow_pos.ne'
  have h_num_ne : (2 ^ (m - 1)) * ∏ k ∈ Finset.Ico 1 m, (2 ^ k - 1) ≠ 0 := mul_ne_zero h_pow_ne h_P_ne
  
  apply (Nat.factorization_le_iff_dvd hm0 h_num_ne).mp
  intro p
  by_cases hp_prime : p.Prime
  · have hp_prime_fact : Fact p.Prime := ⟨hp_prime⟩
    rw [Nat.factorization_def _ hp_prime, Nat.factorization_def _ hp_prime]
    by_cases hp_even : p = 2
    · rw [hp_even]
      have h_fact_2 : padicValNat 2 m.factorial ≤ m - 1 := by
        have hm0_m : m ≠ 0 := by omega
        have h_lt := padicValNat_factorial_lt_of_ne_zero 2 hm0_m
        omega
      have h_num_2 : m - 1 ≤ padicValNat 2 ((2 ^ (m - 1)) * ∏ k ∈ Finset.Ico 1 m, (2 ^ k - 1)) := by
        rw [padicValNat.mul h_pow_ne h_P_ne, padicValNat.prime_pow]
        omega
      exact Nat.le_trans h_fact_2 h_num_2
    · have hp_odd : Odd p := hp_prime.odd_of_ne_two hp_even
      have h_fact_p := P_val_bound_minus_1 m p hp_odd hm
      have h_num_p : padicValNat p (∏ k ∈ Finset.Ico 1 m, (2 ^ k - 1)) ≤ padicValNat p ((2 ^ (m - 1)) * ∏ k ∈ Finset.Ico 1 m, (2 ^ k - 1)) := by
        rw [padicValNat.mul h_pow_ne h_P_ne]
        omega
      exact Nat.le_trans h_fact_p h_num_p
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp_prime, Nat.factorization_eq_zero_of_not_prime _ hp_prime]

lemma padicValNat_two_pow_minus_one_fact (k : ℕ) :
  padicValNat 2 (2^k - 1).factorial = 2^k - 1 - k := by
  induction k with
  | zero =>
    have : 2^0 - 1 = 0 := rfl
    rw [this, Nat.factorial_zero, padicValNat.one]
  | succ k ih =>
    have h1 : 2^(k+1) - 1 = 2 * (2^k - 1) + 1 := by
      calc
        2^(k+1) - 1 = 2 * 2^k - 1 := by rw [pow_succ']
        _ = 2 * (2^k - 1) + 1 := by
          by_cases hk : k = 0
          · rw [hk]; rfl
          · have h2 : 1 ≤ 2^k := Nat.one_le_two_pow
            omega
    rw [h1]
    have h_lt : 1 < 2 := by decide
    rw [padicValNat_factorial_mul_add (2^k - 1) h_lt]
    rw [padicValNat_factorial_mul (2^k - 1)]
    rw [ih]
    by_cases hk : k = 0
    · rw [hk]; rfl
    · have h2 : k ≤ 2^k - 1 := by
        have : k + 1 ≤ 2^k := Nat.succ_le_of_lt (Nat.lt_pow_self (by decide))
        omega
      have h3 : 2^k - 1 - k + (2^k - 1) = 2 * (2^k - 1) + 1 - (k + 1) := by
        omega
      exact h3

lemma padicValNat_two_prod_pow_minus_one (m : ℕ) :
  padicValNat 2 (∏ k ∈ Finset.Ico 1 m, (2^k - 1)) = 0 := by
  have h_ne : ∏ k ∈ Finset.Ico 1 m, (2^k - 1) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk_pos : k ≠ 0 := by omega
    have h1 : 1 < 2^k := Nat.one_lt_pow hk_pos (by decide)
    exact (Nat.sub_pos_of_lt h1).ne'
  apply padicValNat.eq_zero_of_not_dvd
  intro h_dvd
  have h_prime : _root_.Prime 2 := Nat.prime_iff.mp (by decide)
  have h_mem := (Prime.dvd_finset_prod_iff h_prime (fun k => 2^k - 1)).mp h_dvd
  rcases h_mem with ⟨k, hk, h_dvd2⟩
  rw [Finset.mem_Ico] at hk
  have h_mod : (2^k - 1) % 2 = 0 := Nat.mod_eq_zero_of_dvd h_dvd2
  have h_mod2 : (2^k - 1) % 2 = 1 := by
    have h_pow : 2^k = 2^k - 1 + 1 := by
      have h1 : 1 ≤ 2^k := Nat.one_le_two_pow
      omega
    have h_mod_pow : 2^k % 2 = 0 := by
      have : 2^k = 2 * 2^(k-1) := by
        have : k = 1 + (k - 1) := by omega
        nth_rw 1 [this]
        rw [pow_add, pow_one, mul_comm]
      rw [this, Nat.mul_mod_right]
    omega
  omega

lemma not_dvd_of_padicValNat_lt {A B k : ℕ} (hA : padicValNat 2 A = k - 1) (hB : 2^k ∣ B) (hk : 0 < k) (hA0 : A ≠ 0) :
  ¬ 2^k ∣ A + B := by
  intro h_dvd
  have h_dvdA : 2^k ∣ A := by
    have h_sub : A = A + B - B := by omega
    nth_rw 1 [h_sub]
    exact Nat.dvd_sub h_dvd hB
  have h_le := (padicValNat_dvd_iff_le (p := 2) hA0).mp h_dvdA
  rw [hA] at h_le
  omega

lemma odd_prime_factor (n : ℕ) (hn : n > 2) (h_not_pow : ¬ ∃ k, n = 2^k) :
  ∃ p c, p.Prime ∧ Odd p ∧ n = c * p ∧ 1 ≤ c := by
  have hn0 : n ≠ 0 := by omega
  let k := padicValNat 2 n
  have h_dvd : 2^k ∣ n := pow_padicValNat_dvd
  rcases h_dvd with ⟨q, hq⟩
  have h_not_dvd : ¬ 2 ∣ q := by
    intro h2
    have : 2^(k+1) ∣ n := by
      rcases h2 with ⟨m, hm⟩
      rw [hq, hm, pow_succ]
      have : 2^k * (2 * m) = 2^k * 2 * m := by rw [mul_assoc]
      rw [this]
      exact dvd_mul_right (2^k * 2) m
    have h_le := (padicValNat_dvd_iff_le (p := 2) hn0).mp this
    omega
  have hq_odd : Odd q := by
    have h_mod : q % 2 = 1 := by
      have h1 : q % 2 = 0 ∨ q % 2 = 1 := by omega
      cases h1 with
      | inl h_even =>
        have : 2 ∣ q := Nat.dvd_of_mod_eq_zero h_even
        contradiction
      | inr h_odd => exact h_odd
    exact ⟨q / 2, by omega⟩
  have hq_gt_1 : 1 < q := by
    by_contra h_contra
    push_neg at h_contra
    have : q = 1 := by
      have : q ≠ 0 := by rintro rfl; omega
      omega
    have : n = 2^k := by rw [hq, this, mul_one]
    apply h_not_pow
    exact ⟨k, this⟩
  have h_p := Nat.exists_prime_and_dvd hq_gt_1.ne'
  rcases h_p with ⟨p, hp_prime, hp_dvd⟩
  have hp_odd : Odd p := by
    have : p ∣ q := hp_dvd
    have : ¬ 2 ∣ p := by
      intro h2
      have : 2 ∣ q := dvd_trans h2 hp_dvd
      exact h_not_dvd this
    have h_mod : p % 2 = 1 := by
      have h1 : p % 2 = 0 ∨ p % 2 = 1 := by omega
      cases h1 with
      | inl h_even =>
        have : 2 ∣ p := Nat.dvd_of_mod_eq_zero h_even
        contradiction
      | inr h_odd => exact h_odd
    exact ⟨p / 2, by omega⟩
  have hp_dvd_n : p ∣ n := by
    rw [hq]
    exact dvd_mul_of_dvd_right hp_dvd _
  rcases hp_dvd_n with ⟨c, hc_eq⟩
  have hc_pos : 1 ≤ c := by
    by_contra hc_not
    have : c = 0 := by omega
    have : n = 0 := by
      calc
        n = p * c := hc_eq
        _ = p * 0 := by rw [this]
        _ = 0 := mul_zero p
    exact hn0 this
  have h_n_cp : n = c * p := by
    rw [hc_eq, mul_comm]
  exact ⟨p, c, hp_prime, hp_odd, h_n_cp, hc_pos⟩

lemma Prime_le_of_dvd_factorial {p n : ℕ} (hp : p.Prime) (h_dvd : p ∣ n.factorial) : p ≤ n :=
  hp.dvd_factorial.mp h_dvd


noncomputable def a (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    let n_pred : ℕ := n.pred
    let numerator : ℕ := (2 ^ n_pred) * (Finset.Ico 1 n).prod (fun k => 2 ^ k - 1)
    let denominator : ℕ := n.factorial
    numerator / denominator

theorem a091669_conjecture_primitive_root (n : ℕ) (hn : n > 2) :
  n ∣ (a (n - 1) + 2 ^ (n - 2)) →
  Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n) := by

  intro h_dvd
  have hn_pos : n - 1 ≠ 0 := by omega
  have h_a_def : a (n - 1) = ((2 ^ (n - 2)) * ∏ k ∈ Finset.Ico 1 (n - 1), (2 ^ k - 1)) / (n - 1).factorial := by
    dsimp [a]
    split_ifs with h
    · contradiction
    · have hz : n - 1 - 1 = n - 2 := by omega
      rw [hz]
  
  have h_m_pos : 1 ≤ n - 1 := by omega
  let m := n - 1
  let N := (2 ^ (m - 1)) * ∏ k ∈ Finset.Ico 1 m, (2 ^ k - 1)
  let D := m.factorial
  
  have h_D_dvd_N : D ∣ N := factorial_dvd_a_num m h_m_pos
  
  have hN_pos : N ≠ 0 := by
    dsimp [N]
    have h1 : 2 ^ (m - 1) ≠ 0 := by positivity
    have h2 : ∏ k ∈ Finset.Ico 1 m, (2 ^ k - 1) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hk_pos : k ≠ 0 := by omega
      have h1 : 1 < 2^k := Nat.one_lt_pow hk_pos (by decide)
      exact (Nat.sub_pos_of_lt h1).ne'
    exact mul_ne_zero h1 h2

  have hD_pos : D ≠ 0 := factorial_ne_zero m
  
  have hn_prime : n.Prime := by
    by_contra h_not_prime
    have h_not_pow : ¬ ∃ k, n = 2^k := by
      intro h_pow
      rcases h_pow with ⟨k, hk⟩
      have hk1 : 1 < k := by
        by_contra hk_not
        push_neg at hk_not
        have : k = 0 ∨ k = 1 := by omega
        rcases this with rfl | rfl
        · rw [hk] at hn; omega
        · rw [hk] at hn; omega
      have hk2 : 2 ≤ k := by omega
      have h_v2_N_eq : padicValNat 2 N = 2^k - 2 := by
        dsimp [N]
        have h1 : 2 ^ (m - 1) ≠ 0 := by positivity
        have h2 : ∏ j ∈ Finset.Ico 1 m, (2 ^ j - 1) ≠ 0 := by
          apply Finset.prod_ne_zero_iff.mpr
          intro j hj
          rw [Finset.mem_Ico] at hj
          have h1 : 1 < 2^j := Nat.one_lt_pow (by omega) (by decide)
          exact (Nat.sub_pos_of_lt h1).ne'
        rw [padicValNat.mul h1 h2, padicValNat.prime_pow]
        rw [padicValNat_two_prod_pow_minus_one m]
        have hz : m - 1 = 2^k - 2 := by
          dsimp [m]
          rw [hk]
          rfl
        rw [hz, add_zero]
      have h_v2_D : padicValNat 2 D = 2^k - 1 - k := by
        have hz : D = (2^k - 1).factorial := by
          dsimp [D, m]
          congr 1
          rw [hk]
        rw [hz]
        exact padicValNat_two_pow_minus_one_fact k
      have h_v2_a : padicValNat 2 (N / D) = k - 1 := by
        have : N / D ≠ 0 := by
          intro h0
          have : N = 0 := by
            calc
              N = (N / D) * D := by
                have : D ∣ N := h_D_dvd_N
                exact (Nat.div_mul_cancel this).symm
              _ = 0 * D := by rw [h0]
              _ = 0 := MulZeroClass.zero_mul D
          exact hN_pos this
        rw [padicValNat.div_of_dvd h_D_dvd_N]
        rw [h_v2_N_eq, h_v2_D]
        have h1 : ∀ x, 2 ≤ x → x + 2 ≤ 2^x := by
          intro x hx
          induction x, hx using Nat.le_induction with
          | base => decide
          | succ x' hx' ih =>
            calc
              x' + 1 + 2 = x' + 2 + 1 := by omega
              _ ≤ 2^x' + 1 := by omega
              _ ≤ 2^x' + 2^x' := by
                have : 1 ≤ 2^x' := Nat.one_le_two_pow
                omega
              _ = 2^(x' + 1) := by
                have : 2^x' + 2^x' = 2 * 2^x' := by omega
                rw [this, pow_succ']
        have : k + 2 ≤ 2^k := h1 k hk2
        omega
      have h_not_dvd := not_dvd_of_padicValNat_lt (A := N / D) (B := 2^(n-2)) (k := k) h_v2_a (by
        have : 2^k ∣ 2^(n-2) := by
          apply pow_dvd_pow
          rw [hk]
          have h1 : ∀ x, 2 ≤ x → x + 2 ≤ 2^x := by
            intro x hx
            induction x, hx using Nat.le_induction with
            | base => decide
            | succ x' hx' ih =>
              calc
                x' + 1 + 2 = x' + 2 + 1 := by omega
                _ ≤ 2^x' + 1 := by omega
                _ ≤ 2^x' + 2^x' := by
                  have : 1 ≤ 2^x' := Nat.one_le_two_pow
                  omega
                _ = 2^(x' + 1) := by
                  have : 2^x' + 2^x' = 2 * 2^x' := by omega
                  rw [this, pow_succ']
          have : k + 2 ≤ 2^k := h1 k hk2
          omega
        exact this
      ) (by omega) (by
        intro h0
        have h_val0 : padicValNat 2 0 = 0 := padicValNat.zero
        rw [h0] at h_v2_a
        rw [h_val0] at h_v2_a
        omega
      )
      have : 2^k ∣ N / D + 2 ^ (n - 2) := by
        have : 2^k = n := hk.symm
        rw [this]
        have hz : a (n - 1) = N / D := h_a_def
        have : N / D + 2 ^ (n - 2) = a (n - 1) + 2 ^ (n - 2) := by
          rw [hz]
        rw [this]
        exact h_dvd
      exact h_not_dvd this
    
    -- Now we know n is not a power of 2. So it has an odd prime factor!
    have h_odd_factor := odd_prime_factor n hn h_not_pow
    rcases h_odd_factor with ⟨p, c, hp_prime, hp_odd, hn_eq, hc_pos⟩
    have hp_fact : Fact p.Prime := ⟨hp_prime⟩
    have hp_gt : 1 < p := hp_prime.one_lt
    
    have hc_gt_1 : 2 ≤ c := by
      by_contra hc_not
      have : c = 1 := by omega
      rw [this, one_mul] at hn_eq
      have : n.Prime := by rw [hn_eq]; exact hp_prime
      exact h_not_prime this
      
    have hm_eq : m = c * p - 1 := by
      dsimp [m]
      rw [hn_eq]
    
    have h_val_N_p : padicValNat p N = padicValNat p (∏ k ∈ Finset.Ico 1 m, (2 ^ k - 1)) := by
      dsimp [N]
      have h1 : 2 ^ (m - 1) ≠ 0 := by positivity
      have h2 : ∏ j ∈ Finset.Ico 1 m, (2 ^ j - 1) ≠ 0 := by
        apply Finset.prod_ne_zero_iff.mpr
        intro j hj
        rw [Finset.mem_Ico] at hj
        have h1 : 1 < 2^j := Nat.one_lt_pow (by omega) (by decide)
        exact (Nat.sub_pos_of_lt h1).ne'
      rw [padicValNat.mul h1 h2]
      have : padicValNat p (2 ^ (m - 1)) = 0 := by
        apply padicValNat.eq_zero_of_not_dvd
        intro h_dvd2
        have h_p_dvd_2 : p ∣ 2 := hp_prime.dvd_of_dvd_pow h_dvd2
        have h_p_le_2 : p ≤ 2 := Nat.le_of_dvd (by decide) h_p_dvd_2
        have h_p_odd : p % 2 = 1 := by
          cases hp_odd with
          | intro k hk =>
            have : p = 2 * k + 1 := hk
            omega
        omega
      rw [this, zero_add]
      
    have h_strict := P_val_bound_minus_1_strict c p m hp_odd hc_gt_1 hm_eq
    have h_strict2 : padicValNat p D + 1 ≤ padicValNat p N := by
      have hd : padicValNat p D = padicValNat p m.factorial := rfl
      rw [hd]
      have hv : padicValNat p N = padicValNat p (∏ k ∈ Finset.Ico 1 m, (2 ^ k - 1)) := h_val_N_p
      rw [hv]
      exact h_strict
    
    have h_val_a_p : padicValNat p (N / D) ≥ 1 := by
      have hd_val : padicValNat p (N / D) = padicValNat p N - padicValNat p D := by
        exact padicValNat.div_of_dvd h_D_dvd_N
      rw [hd_val]
      have : padicValNat p D ≤ padicValNat p N := by omega
      omega
      
    have h_p_dvd_a : p ∣ N / D := by
      have : N / D ≠ 0 := by
        intro h0
        have : N = 0 := by
          calc
            N = (N / D) * D := by
              have : D ∣ N := h_D_dvd_N
              exact (Nat.div_mul_cancel this).symm
            _ = 0 * D := by rw [h0]
            _ = 0 := MulZeroClass.zero_mul D
        exact hN_pos this
      have hz : p^1 = p := pow_one p
      have hz2 := (padicValNat_dvd_iff_le (p := p) this).mpr (by
        have : 1 ≤ padicValNat p (N / D) := h_val_a_p
        exact this
      )
      rw [hz] at hz2
      exact hz2
      
    have h_p_dvd_n : p ∣ n := by
      rw [hn_eq]
      exact dvd_mul_left p c
    
    have h_p_dvd_2_pow : p ∣ 2 ^ (n - 2) := by
      have h_sum : p ∣ N / D + 2 ^ (n - 2) := by
        have hz : a (n - 1) = N / D := h_a_def
        have : N / D + 2 ^ (n - 2) = a (n - 1) + 2 ^ (n - 2) := by rw [hz]
        rw [this]
        exact dvd_trans h_p_dvd_n h_dvd
      have h_sub : N / D + 2 ^ (n - 2) = 2 ^ (n - 2) + N / D := add_comm _ _
      rw [h_sub] at h_sum
      have hz3 : 2 ^ (n - 2) = 2 ^ (n - 2) + N / D - N / D := (Nat.add_sub_cancel (2 ^ (n - 2)) (N / D)).symm
      rw [hz3]
      exact Nat.dvd_sub h_sum h_p_dvd_a
      
    have h_p_dvd_2 : p ∣ 2 := hp_prime.dvd_of_dvd_pow h_p_dvd_2_pow
    have h_p_le_2 : p ≤ 2 := Nat.le_of_dvd (by decide) h_p_dvd_2
    have h_p_odd : p % 2 = 1 := by
      cases hp_odd with
      | intro k hk =>
        have : p = 2 * k + 1 := hk
        omega
    omega

  -- Since n is prime!
  constructor
  · exact hn_prime
  · rw [Nat.totient_prime hn_prime]
    rw [IsPrimitiveRoot.iff_orderOf]
    -- The order of 2 mod n is n-1
    apply (orderOf_eq_iff (by omega)).mpr
    constructor
    · have hp_fact : Fact n.Prime := ⟨hn_prime⟩
      have h_n_odd : Odd n := by
        cases hn_prime.eq_two_or_odd with
        | inl h2 => omega
        | inr h_odd => exact ⟨n / 2, by omega⟩
      have h_n_ne_2 : n ≠ 2 := by omega
      -- 2^(n-1) = 1 mod n by Fermat
      have h_zmod_ne_zero : (2 : ZMod n) ≠ 0 := by
        intro h
        have : n ∣ 2 := (CharP.cast_eq_zero_iff (ZMod n) n 2).mp h
        have : n ≤ 2 := Nat.le_of_dvd (by decide) this
        omega
      exact ZMod.pow_card_sub_one_eq_one h_zmod_ne_zero
    · intro q hq hq_pos
      -- If order is not n-1, then 2^q = 1 mod n for some q < n-1.
      -- Then 2^q - 1 is a multiple of n.
      intro h_eq
      have h_dvd_q : n ∣ 2^q - 1 := by
        have : ((2^q - 1 : ℕ) : ZMod n) = 0 := by
          have hz : 1 ≤ 2^q := Nat.one_le_two_pow
          rw [Nat.cast_sub hz]
          push_cast
          rw [h_eq, sub_self]
        exact (CharP.cast_eq_zero_iff (ZMod n) n _).mp this
      
      have h_q_n : q < n - 1 := by omega
      -- N = 2^(n-2) * prod_{k=1}^{n-1} (2^k - 1)
      have h_n_dvd_N : n ∣ N := by
        dsimp [N, m]
        have h_prod : ∏ k ∈ Finset.Ico 1 (n - 1), (2 ^ k - 1) = (2 ^ q - 1) * ∏ k ∈ (Finset.Ico 1 (n - 1)).erase q, (2 ^ k - 1) := by
          have h_mem : q ∈ Finset.Ico 1 (n - 1) := by
            rw [Finset.mem_Ico]
            exact ⟨hq_pos, h_q_n⟩
          exact (Finset.mul_prod_erase (Finset.Ico 1 (n - 1)) _ h_mem).symm
        rw [h_prod]
        have hz : (2 ^ (n - 2)) * ((2 ^ q - 1) * ∏ k ∈ (Finset.Ico 1 (n - 1)).erase q, (2 ^ k - 1)) =
                  ((2 ^ (n - 2)) * (∏ k ∈ (Finset.Ico 1 (n - 1)).erase q, (2 ^ k - 1))) * (2 ^ q - 1) := by
          calc
            (2 ^ (n - 2)) * ((2 ^ q - 1) * ∏ k ∈ (Finset.Ico 1 (n - 1)).erase q, (2 ^ k - 1)) =
            (2 ^ (n - 2)) * ((∏ k ∈ (Finset.Ico 1 (n - 1)).erase q, (2 ^ k - 1)) * (2 ^ q - 1)) := by rw [mul_comm (2^q - 1)]
            _ = ((2 ^ (n - 2)) * ∏ k ∈ (Finset.Ico 1 (n - 1)).erase q, (2 ^ k - 1)) * (2 ^ q - 1) := by rw [← mul_assoc]
        have hz2 : (2 ^ (n - 1 - 1)) * ((2 ^ q - 1) * ∏ k ∈ (Finset.Ico 1 (n - 1)).erase q, (2 ^ k - 1)) =
                   ((2 ^ (n - 2)) * ∏ k ∈ (Finset.Ico 1 (n - 1)).erase q, (2 ^ k - 1)) * (2 ^ q - 1) := by
          have hz3 : n - 1 - 1 = n - 2 := by omega
          rw [hz3, hz]
        rw [hz2]
        exact dvd_mul_of_dvd_right h_dvd_q _
        
      have h_n_dvd_a : n ∣ N / D := by
        -- D = (n-1)!
        -- Since n is prime, (n-1)! and n are coprime.
        -- n | N, D | N, so N = k * D. n | k * D => n | k.
        have hn_coprime : n.Coprime D := by
          dsimp [D, m]
          apply (Nat.Prime.coprime_iff_not_dvd hn_prime).mpr
          intro h_dvd_D
          have : n ≤ n - 1 := Prime_le_of_dvd_factorial hn_prime h_dvd_D
          omega
        -- since n | N and N = (N/D) * D, n | (N/D) * D
        have h1 : n ∣ (N / D) * D := by
          have : (N / D) * D = N := (Nat.div_mul_cancel h_D_dvd_N)
          rw [this]
          exact h_n_dvd_N
        exact hn_coprime.dvd_of_dvd_mul_right h1
      
      have h_n_dvd_pow : n ∣ 2 ^ (n - 2) := by
        have h_sum : n ∣ N / D + 2 ^ (n - 2) := by
          have hz : a (n - 1) = N / D := h_a_def
          have : N / D + 2 ^ (n - 2) = a (n - 1) + 2 ^ (n - 2) := by rw [hz]
          rw [this]
          exact h_dvd
        have h_sub : N / D + 2 ^ (n - 2) = 2 ^ (n - 2) + N / D := add_comm _ _
        rw [h_sub] at h_sum
        have hz3 : 2 ^ (n - 2) = 2 ^ (n - 2) + N / D - N / D := (Nat.add_sub_cancel (2 ^ (n - 2)) (N / D)).symm
        rw [hz3]
        exact Nat.dvd_sub h_sum h_n_dvd_a
        
      have h_n_dvd_2 : n ∣ 2 := hn_prime.dvd_of_dvd_pow h_n_dvd_pow
      have h_n_le_2 : n ≤ 2 := Nat.le_of_dvd (by decide) h_n_dvd_2
      omega


theorem a091669_conjecture_primitive_root.disproof : ¬ (type_of% @a091669_conjecture_primitive_root) := sorry
