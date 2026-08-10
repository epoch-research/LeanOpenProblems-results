import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

lemma gcd_of_prime_lt (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < p) : Nat.gcd k p = 1 := by
  have h_not_dvd : ¬ p ∣ k := Nat.not_dvd_of_pos_of_lt (by omega) hk2
  have h_coprime : Nat.Coprime k p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr h_not_dvd).symm
  exact h_coprime

lemma sum_range_mul (m n : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ range (m * n), f i = ∑ i ∈ range m, ∑ j ∈ range n, f (i * n + j) := by
  induction m with
  | zero =>
    simp
  | succ m ih =>
    rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]

lemma sum_Ico_succ_top_eq_sum_range (n : ℕ) (hn : 0 < n) (f : ℕ → ℕ) (h0 : f 0 = f n) :
    ∑ k ∈ Ico 1 (n + 1), f k = ∑ k ∈ range n, f k := by
  rw [sum_Ico_succ_top hn, ← h0, range_eq_Ico]
  rw [sum_eq_sum_Ico_succ_bot hn]
  ring


lemma test_gcd_mul (x a b : ℕ) (h : Nat.Coprime a b) : Nat.gcd x (a * b) = Nat.gcd x a * Nat.gcd x b := by
  exact Nat.Coprime.gcd_mul x h

lemma test_gcd_mod (x M : ℕ) : Nat.gcd x M = Nat.gcd (x % M) M := by
  rw [Nat.gcd_comm x M, Nat.gcd_rec M x]


lemma test_fin_sum (M : ℕ) (f : ℕ → ℕ) : ∑ i : Fin M, f i = ∑ i ∈ range M, f i := by
  exact Fin.sum_univ_eq_sum_range f



lemma test_zmod_fin (M : ℕ) [NeZero M] : Fin M ≃ ZMod M := by
  exact (ZMod.finEquiv M).toEquiv



lemma sum_zmod_eq_sum_range (M : ℕ) [NeZero M] (f : ℕ → ℕ) :
    ∑ x : ZMod M, f x.val = ∑ i ∈ range M, f i := by
  rw [← Fin.sum_univ_eq_sum_range]
  rw [← Equiv.sum_comp (ZMod.finEquiv M).toEquiv]
  apply Finset.sum_congr rfl
  intro i _
  rfl

def zmodEquiv (p M j : ℕ) (h_cop : Nat.Coprime p M) : ZMod M ≃ ZMod M where
  toFun := fun x => x * (p : ZMod M) + (j : ZMod M)
  invFun := fun y => (y - (j : ZMod M)) * (((ZMod.unitOfCoprime p h_cop)⁻¹ : (ZMod M)ˣ) : ZMod M)
  left_inv := by
    intro x
    dsimp
    rw [add_sub_cancel_right]
    have h_u : ((ZMod.unitOfCoprime p h_cop) : ZMod M) = p := ZMod.coe_unitOfCoprime p h_cop
    rw [← h_u]
    rw [mul_assoc]
    have h_inv : (ZMod.unitOfCoprime p h_cop : ZMod M) * (((ZMod.unitOfCoprime p h_cop)⁻¹ : (ZMod M)ˣ) : ZMod M) = 1 := by
      exact Units.mul_inv (ZMod.unitOfCoprime p h_cop)
    rw [h_inv, mul_one]
  right_inv := by
    intro y
    dsimp
    rw [mul_assoc]
    have h_u : ((ZMod.unitOfCoprime p h_cop) : ZMod M) = p := ZMod.coe_unitOfCoprime p h_cop
    rw [← h_u]
    have h_inv : (((ZMod.unitOfCoprime p h_cop)⁻¹ : (ZMod M)ˣ) : ZMod M) * (ZMod.unitOfCoprime p h_cop : ZMod M) = 1 := by
      exact Units.inv_mul (ZMod.unitOfCoprime p h_cop)
    rw [h_inv, mul_one, sub_add_cancel]

lemma sum_gcd_linear_congruence (p M j : ℕ) [NeZero M] (h_cop : Nat.Coprime p M) :
    ∑ i ∈ range M, Nat.gcd (i * p + j) M = ∑ i ∈ range M, Nat.gcd i M := by
  rw [← sum_zmod_eq_sum_range]
  rw [← sum_zmod_eq_sum_range]
  have h_gcd_eq (x : ZMod M) : Nat.gcd (x.val * p + j) M = Nat.gcd (zmodEquiv p M j h_cop x).val M := by
    dsimp [zmodEquiv]
    rw [test_gcd_mod (x.val * p + j) M]
    rw [test_gcd_mod (x * (p : ZMod M) + (j : ZMod M)).val M]
    have h_val : (x * (p : ZMod M) + (j : ZMod M)).val % M = (x * (p : ZMod M) + (j : ZMod M)).val := Nat.mod_eq_of_lt (ZMod.val_lt _)
    rw [h_val]
    rfl
  have h_sum : (∑ x : ZMod M, Nat.gcd (x.val * p + j) M) = ∑ x : ZMod M, Nat.gcd (zmodEquiv p M j h_cop x).val M := by
    apply Finset.sum_congr rfl
    intro x _
    exact h_gcd_eq x
  rw [h_sum]
  rw [Equiv.sum_comp (zmodEquiv p M j h_cop)]

lemma sum_gcd_coprime_mul (p M : ℕ) (hp : Nat.Prime p) (h_cop : Nat.Coprime p M) :
    (Finset.Ico 1 (p * M + 1)).sum (fun k => Nat.gcd k (p * M)) =
    (2 * p - 1) * (Finset.Ico 1 (M + 1)).sum (fun k => Nat.gcd k M) := by
  have hM_pos : 0 < M := by
    by_contra hM0
    have : M = 0 := by omega
    rw [this] at h_cop
    have : Nat.gcd p 0 = 1 := h_cop
    rw [Nat.gcd_zero_right] at this
    have : p = 1 := this
    rw [this] at hp
    exact Nat.not_prime_one hp
  have hpM_pos : 0 < p * M := Nat.mul_pos hp.pos hM_pos
  have h_gcd_zero1 : Nat.gcd 0 (p * M) = Nat.gcd (p * M) (p * M) := by
    rw [Nat.gcd_zero_left, Nat.gcd_self]
  have h_gcd_zero2 : Nat.gcd 0 M = Nat.gcd M M := by
    rw [Nat.gcd_zero_left, Nat.gcd_self]
  rw [sum_Ico_succ_top_eq_sum_range (p * M) hpM_pos _ h_gcd_zero1]
  rw [sum_Ico_succ_top_eq_sum_range M hM_pos _ h_gcd_zero2]
  have h_comm : p * M = M * p := mul_comm p M
  rw [h_comm]
  rw [sum_range_mul M p]
  have h_term (i j : ℕ) : Nat.gcd (i * p + j) (M * p) = Nat.gcd (i * p + j) M * Nat.gcd j p := by
    rw [h_comm]
    have h_cop_mp : Nat.Coprime M p := h_cop.symm
    rw [Nat.Coprime.gcd_mul (i * p + j) h_cop_mp]
    have h_gcd_p : Nat.gcd (i * p + j) p = Nat.gcd j p := by
      rw [add_comm]
      exact Nat.gcd_add_mul_right_left p j i
    rw [h_gcd_p]
  rw [h_sum_rw]
  rw [sum_comm]
  haveI : NeZero M := ⟨hM_pos⟩
  have h_inner_rw (j : ℕ) : ∑ i ∈ range M, (Nat.gcd (i * p + j) M * Nat.gcd j p) =
                            (∑ i ∈ range M, Nat.gcd (i * p + j) M) * Nat.gcd j p := by
    rw [← sum_mul]
  have h_inner_linear (j : ℕ) : (∑ i ∈ range M, Nat.gcd (i * p + j) M) = ∑ i ∈ range M, Nat.gcd i M := by
    exact sum_gcd_linear_congruence p M j h_cop
  have h_inner_combined (j : ℕ) : ∑ i ∈ range M, (Nat.gcd (i * p + j) M * Nat.gcd j p) =
                                  (∑ i ∈ range M, Nat.gcd i M) * Nat.gcd j p := by
    rw [h_inner_rw j, h_inner_linear j]
  have h_outer_rw : (∑ j ∈ range p, ∑ i ∈ range M, (Nat.gcd (i * p + j) M * Nat.gcd j p)) =
                    ∑ j ∈ range p, ((∑ i ∈ range M, Nat.gcd i M) * Nat.gcd j p) := by
    apply Finset.sum_congr rfl
    intro j _
    exact h_inner_combined j
  rw [h_outer_rw]
  rw [← sum_mul]
  have h_sum_prime_eq : ∑ j ∈ range p, Nat.gcd j p = 2 * p - 1 := by
    have hp_pos : 0 < p := hp.pos
    have h_gcd_zero_p : Nat.gcd 0 p = Nat.gcd p p := by
      rw [Nat.gcd_zero_left, Nat.gcd_self]
    rw [← sum_Ico_succ_top_eq_sum_range p hp_pos _ h_gcd_zero_p]
    exact sum_prime p hp
  rw [h_sum_prime_eq]
  ring


lemma test_sum_M_ge (M : ℕ) (hM : 2 ≤ M) : 2 * M - 1 ≤ (Finset.Ico 1 (M + 1)).sum (fun k => Nat.gcd k M) := by
  by_cases hM_prime : Nat.Prime M
  · rw [sum_prime M hM_prime]
  · have h_sum_split : (Finset.Ico 1 (M + 1)).sum (fun k => Nat.gcd k M) = (Finset.Ico 1 M).sum (fun k => Nat.gcd k M) + M := by
      have h_split : (Finset.Ico 1 (M + 1)).sum (fun k => Nat.gcd k M) = (Finset.Ico 1 M).sum (fun k => Nat.gcd k M) + Nat.gcd M M := Finset.sum_Ico_succ_top (by omega : 1 ≤ M) (fun k => Nat.gcd k M)
      rw [h_split, Nat.gcd_self]
    rw [h_sum_split]
    have hM_ne1 : M ≠ 1 := by omega
    have hM_ne0 : M ≠ 0 := by omega
    have h_sum_ge := sum_composite_ge M hM_ne1 hM_ne0 hM_prime
    omega


lemma sum_composite_le_third (M : ℕ) (hM : 2 ≤ M) (h_comp : ¬ Nat.Prime M) (hM_odd : ¬ 2 ∣ M) :
    ∑ k ∈ Finset.Ico 1 M, Nat.gcd k M ≤ (M - 1) * (M / 3) := by
  have h_const : ∑ k ∈ Finset.Ico 1 M, (M / 3) = (M - 1) * (M / 3) := by
    rw [Finset.sum_const, card_Ico, smul_eq_mul]
  rw [← h_const]
  apply Finset.sum_le_sum
  intro k hk
  rw [Finset.mem_Ico] at hk
  exact gcd_le_third_odd M k hk.1 hM_odd hk.2



lemma case_non_square_free (p M n q D : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (h_n : n = p * M) (hM : M = q * D) (hqd : q ∣ D)
    (hn_dvd_sum : n ∣ 1 + (Finset.Ico 1 (n + 1)).sum (fun k => Nat.gcd k n)) : False := by
  have h_n_rw : n = q * (p * D) := by
    rw [h_n, hM]
    ring
  have h_q2_dvd : q ∣ p * D := by
    exact dvd_mul_of_dvd_right hqd p
  have hq_dvd_sum : q ∣ (Finset.Ico 1 (n + 1)).sum (fun k => Nat.gcd k n) := by
    rw [h_n_rw]
    exact p_dvd_sum_of_square_dvd q (p * D) hq h_q2_dvd
  have hq_dvd_n : q ∣ n := by
    rw [h_n_rw]
    exact dvd_mul_right q (p * D)
  have hq_dvd_one_add : q ∣ 1 + (Finset.Ico 1 (n + 1)).sum (fun k => Nat.gcd k n) := by
    exact Nat.dvd_trans hq_dvd_n hn_dvd_sum
  have hq_dvd_one : q ∣ 1 := by
    exact (Nat.dvd_add_right hq_dvd_sum).mp hq_dvd_one_add
  have hq_ge2 : 2 ≤ q := hq.two_le
  have : q ≤ 1 := Nat.le_of_dvd (by omega) hq_dvd_one
  omega

lemma case_prime_M (p M n : ℕ) (hp : Nat.Prime p) (hM : Nat.Prime M) (h_n : n = p * M) (h_cop : Nat.Coprime p M)
    (hn_dvd_sum : n ∣ 1 + (Finset.Ico 1 (n + 1)).sum (fun k => Nat.gcd k n)) : False := by
  have h_sum := sum_gcd_coprime_mul p M hp h_cop
  rw [← h_n] at h_sum
  have h_sum_M : (Finset.Ico 1 (M + 1)).sum (fun k => Nat.gcd k M) = 2 * M - 1 := sum_prime M hM
  rw [h_sum_M] at h_sum
  have hp_ge2 : 2 ≤ p := hp.two_le
  have hM_ge2 : 2 ≤ M := hM.two_le
  have h_cop' : M ≠ p := by
    rintro rfl
    have : Nat.gcd p p = 1 := h_cop
    rw [Nat.gcd_self] at this
    have : p = 1 := this
    rw [this] at hp
    exact Nat.not_prime_one hp
  have h_M_dvd_n : M ∣ n := by
    rw [h_n]
    exact dvd_mul_left M p
  have hp_le_M : p ≤ M := by
    exact Nat.minFac_le_of_dvd hM_ge2 h_M_dvd_n
  have hM_gt_p' : p < M := by omega
  have hn_dvd : p * M ∣ 1 + (2 * p - 1) * (2 * M - 1) := by
    rw [← h_sum, h_n] at hn_dvd_sum
    exact hn_dvd_sum
  have h_algebra : 1 + (2 * p - 1) * (2 * M - 1) + (2 * p + 2 * M - 2) = 4 * p * M := by omega
  have h_dvd_4pm : p * M ∣ 4 * p * M := dvd_mul_left (p * M) 4
  have h_dvd_sum : p * M ∣ 2 * p + 2 * M - 2 := by
    have h_add_dvd : p * M ∣ 1 + (2 * p - 1) * (2 * M - 1) + (2 * p + 2 * M - 2) := by
      rw [h_algebra]
      exact h_dvd_4pm
    exact (Nat.dvd_add_right hn_dvd).mp h_add_dvd
  have h_M_dvd : M ∣ 2 * p - 2 := by
    have h_M_dvd_term : M ∣ p * M := dvd_mul_left M p
    have h_M_dvd_term2 : M ∣ 2 * p + 2 * M - 2 := by
      exact Nat.dvd_trans h_M_dvd_term h_dvd_sum
    have h_algebra2 : 2 * p + 2 * M - 2 = 2 * M + (2 * p - 2) := by omega
    rw [h_algebra2] at h_M_dvd_term2
    have h_M_dvd_2M : M ∣ 2 * M := dvd_mul_left M 2
    exact (Nat.dvd_add_right h_M_dvd_2M).mp h_M_dvd_term2
  have h_dvd_cases : M ∣ 2 ∨ M ∣ p - 1 := by
    have h_mul : 2 * p - 2 = 2 * (p - 1) := by omega
    rw [h_mul] at h_M_dvd
    exact (Nat.Prime.dvd_mul hM).mp h_M_dvd
  rcases h_dvd_cases with h_dvd_2 | h_dvd_pm1
  · have : M = 2 := by
      rcases Nat.Prime.eq_two_or_odd hM with rfl | h_odd
      · rfl
      · have h_dvd_2_le : M ≤ 2 := Nat.le_of_dvd (by omega) h_dvd_2
        omega
    omega
  · have h_pm1_pos : 0 < p - 1 := by omega
    have : M ≤ p - 1 := Nat.le_of_dvd h_pm1_pos h_dvd_pm1
    omega

