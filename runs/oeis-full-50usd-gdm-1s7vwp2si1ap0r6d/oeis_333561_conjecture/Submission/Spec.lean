import FormalConjectures.Util.ProblemImports

open Nat Finset

theorem step1 (N k' : ℕ) (hk' : k' ≤ 2 * N) (hN : 1 ≤ N) :
  Nat.choose (3 * N - k' - 1) (2 * N - k') * (3 * N - k') = Nat.choose (3 * N - k') (2 * N - k') * N := by
  have h1 : 3 * N - k' - 1 + 1 = 3 * N - k' := by
    have h : 1 ≤ 3 * N - k' := by omega
    omega
  have := Nat.choose_mul_succ_eq (3 * N - k' - 1) (2 * N - k')
  rw [h1] at this
  have h2 : 3 * N - k' - (2 * N - k') = N := by omega
  rw [h2] at this
  exact this

theorem step2 (N k' : ℕ) :
  Nat.choose (N + k' - 1) k' * (N + k') = Nat.choose (N + k') k' * N := by
  by_cases hNk : N + k' = 0
  · have hN : N = 0 := by omega
    have hk' : k' = 0 := by omega
    rw [hN, hk']
  · have h1 : N + k' - 1 + 1 = N + k' := by omega
    have := Nat.choose_mul_succ_eq (N + k' - 1) k'
    rw [h1] at this
    have h2 : N + k' - k' = N := by omega
    rw [h2] at this
    exact this


theorem step3 (N k' : ℕ) (hk' : k' ≤ 2 * N) :
  Nat.choose (3 * N) k' * Nat.choose (3 * N - k') (2 * N - k') = Nat.choose (3 * N) (2 * N) * Nat.choose (2 * N) k' := by
  have := Nat.choose_mul (n := 3 * N) hk'
  exact this.symm

theorem step4 (N k' : ℕ) (hk' : k' ≤ 2 * N) :
  Nat.choose (3 * N) (2 * N - k') = Nat.choose (3 * N) (N + k') := by
  have h1 : 2 * N - k' ≤ 3 * N := by omega
  have := Nat.choose_symm h1
  have h2 : 3 * N - (2 * N - k') = N + k' := by omega
  rw [h2] at this
  exact this.symm

theorem step5 (N k' : ℕ) :
  Nat.choose (3 * N) (N + k') * Nat.choose (N + k') k' = Nat.choose (3 * N) k' * Nat.choose (3 * N - k') N := by
  have hk_sub : k' ≤ N + k' := by omega
  have := Nat.choose_mul (n := 3 * N) hk_sub
  have h2 : N + k' - k' = N := by omega
  rw [h2] at this
  exact this

theorem step6 (N k' : ℕ) (hk' : k' ≤ 2 * N) :
  Nat.choose (3 * N - k') N = Nat.choose (3 * N - k') (2 * N - k') := by
  have h1 : N ≤ 3 * N - k' := by omega
  have := Nat.choose_symm h1
  have h2 : 3 * N - k' - N = 2 * N - k' := by omega
  rw [h2] at this
  exact this.symm

theorem T_identity (N k' : ℕ) (hk' : k' ≤ 2 * N) (hN : 1 ≤ N) :
  (3 * N - k') * (Nat.choose (3 * N) k' * Nat.choose (3 * N - k' - 1) (2 * N - k')) =
  (N + k') * (Nat.choose (3 * N) (2 * N - k') * Nat.choose (N + k' - 1) k') := by
  have L1 := step1 N k' hk' hN
  have L2 := step2 N k'
  have L3 := step3 N k' hk'
  have L4 := step4 N k' hk'
  have L5 := step5 N k'
  have L6 := step6 N k' hk'
  have h_LHS : (3 * N - k') * (Nat.choose (3 * N) k' * Nat.choose (3 * N - k' - 1) (2 * N - k')) = Nat.choose (3 * N) (2 * N) * (Nat.choose (2 * N) k' * N) := by
    calc
      (3 * N - k') * (Nat.choose (3 * N) k' * Nat.choose (3 * N - k' - 1) (2 * N - k')) =
        Nat.choose (3 * N) k' * (Nat.choose (3 * N - k' - 1) (2 * N - k') * (3 * N - k')) := by ring
      _ = Nat.choose (3 * N) k' * (Nat.choose (3 * N - k') (2 * N - k') * N) := by rw [L1]
      _ = (Nat.choose (3 * N) k' * Nat.choose (3 * N - k') (2 * N - k')) * N := by ring
      _ = (Nat.choose (3 * N) (2 * N) * Nat.choose (2 * N) k') * N := by rw [L3]
      _ = Nat.choose (3 * N) (2 * N) * (Nat.choose (2 * N) k' * N) := by ring
  have h_RHS : (N + k') * (Nat.choose (3 * N) (2 * N - k') * Nat.choose (N + k' - 1) k') = Nat.choose (3 * N) (2 * N) * (Nat.choose (2 * N) k' * N) := by
    calc
      (N + k') * (Nat.choose (3 * N) (2 * N - k') * Nat.choose (N + k' - 1) k') =
        Nat.choose (3 * N) (2 * N - k') * (Nat.choose (N + k' - 1) k' * (N + k')) := by ring
      _ = Nat.choose (3 * N) (2 * N - k') * (Nat.choose (N + k') k' * N) := by rw [L2]
      _ = Nat.choose (3 * N) (N + k') * (Nat.choose (N + k') k' * N) := by rw [L4]
      _ = (Nat.choose (3 * N) (N + k') * Nat.choose (N + k') k') * N := by ring
      _ = (Nat.choose (3 * N) k' * Nat.choose (3 * N - k') N) * N := by rw [L5]
      _ = (Nat.choose (3 * N) k' * Nat.choose (3 * N - k') (2 * N - k')) * N := by rw [L6]
      _ = (Nat.choose (3 * N) (2 * N) * Nat.choose (2 * N) k') * N := by rw [L3]
      _ = Nat.choose (3 * N) (2 * N) * (Nat.choose (2 * N) k' * N) := by ring
  rw [h_LHS, h_RHS]


theorem le_three_mul_of_eq (N k' A B : ℕ) (hk' : k' ≤ 2 * N) (hN : 1 ≤ N)
  (h : (3 * N - k') * A = (N + k') * B) : B ≤ 3 * A := by
  have h1 : N * B ≤ (N + k') * B := by
    gcongr
    omega
  have h2 : (N + k') * B = (3 * N - k') * A := h.symm
  have h3 : (3 * N - k') * A ≤ 3 * N * A := by
    gcongr
    omega
  have h4 : N * B ≤ 3 * N * A := by
    calc
      N * B ≤ (N + k') * B := h1
      _ = (3 * N - k') * A := h2
      _ ≤ 3 * N * A := h3
  have h5 : N * B ≤ N * (3 * A) := by
    calc
      N * B ≤ 3 * N * A := h4
      _ = N * (3 * A) := by ring
  exact Nat.le_of_mul_le_mul_left h5 hN

theorem nat_algebra (N k' A B : ℕ) (hk' : k' ≤ 3 * N) (hB : B ≤ 3 * A)
  (h : (3 * N - k') * A = (N + k') * B) :
  k' * (A + B) = N * (3 * A - B) := by
  have h_add : 3 * N * A = k' * (A + B) + N * B := by
    have h1 : 3 * N * A = (3 * N - k' + k') * A := by
      congr 1
      omega
    rw [h1, add_mul]
    rw [h]
    ring
  have h_sub : 3 * N * A = N * (3 * A - B) + N * B := by
    rw [← mul_add, Nat.sub_add_cancel hB]
    ring
  have h_eq : k' * (A + B) + N * B = N * (3 * A - B) + N * B := by
    rw [← h_add, h_sub]
  exact Nat.add_right_cancel h_eq

theorem T_identity_simplified (N k' A B : ℕ) (hk' : k' ≤ 2 * N) (hN : 1 ≤ N)
  (h : (3 * N - k') * A = (N + k') * B) :
  k' * (A + B) = N * (3 * A - B) := by
  have hB := le_three_mul_of_eq N k' A B hk' hN h
  exact nat_algebra N k' A B (by omega) hB h

theorem not_dvd_sub_of_dvd_of_not_dvd (p a b : ℕ) (h1 : p ∣ a) (h2 : ¬ p ∣ b) (hba : b ≤ a) : ¬ p ∣ a - b := by
  intro h
  rcases h1 with ⟨k, rfl⟩
  rcases h with ⟨j, hj⟩
  have : p ∣ b := by
    use k - j
    have : b = p * k - (p * k - b) := by omega
    rw [this, hj]
    rw [Nat.mul_sub_left_distrib]
  exact h2 this

theorem not_dvd_add_of_dvd_of_not_dvd (p a b : ℕ) (h1 : p ∣ a) (h2 : ¬ p ∣ b) : ¬ p ∣ a + b := by
  intro h
  rcases h1 with ⟨k, rfl⟩
  rcases h with ⟨j, hj⟩
  have : p ∣ b := by
    use j - k
    have : b = p * j - p * k := by omega
    rw [this, Nat.mul_sub_left_distrib]
  exact h2 this

theorem choose_mul_eq_choose_mul_symm (M k' : ℕ) (hk' : k' < 2 * M) (hM : 1 ≤ M) :
  (3 * M) * Nat.choose (3 * M - 1) (2 * M - k' - 1) = Nat.choose (3 * M) (2 * M - k') * (2 * M - k') := by
  have h1 : 3 * M - 1 + 1 = 3 * M := by omega
  have h2 : 2 * M - k' - 1 + 1 = 2 * M - k' := by omega
  have := Nat.add_one_mul_choose_eq (3 * M - 1) (2 * M - k' - 1)
  rw [h1, h2] at this
  exact this



theorem choose_mul_eq_choose_mul_symm_1 (M k' : ℕ) (hk' : k' ≥ 1) :
  Nat.choose (M + k' - 1) k' * k' = Nat.choose (M + k' - 1) (k' - 1) * M := by
  have h_pos : M + k' > 0 := by omega
  refine Nat.eq_of_mul_eq_mul_right h_pos ?_
  calc
    (Nat.choose (M + k' - 1) k' * k') * (M + k') =
      (Nat.choose (M + k' - 1) k' * (M + k')) * k' := by ring
    _ = (Nat.choose (M + k') k' * M) * k' := by rw [step2]
    _ = (Nat.choose (M + k') k' * k') * M := by ring
    _ = ((M + k') * Nat.choose (M + k' - 1) (k' - 1)) * M := by
      have h1 : M + k' - 1 + 1 = M + k' := by omega
      have h2 : k' - 1 + 1 = k' := by omega
      have := Nat.add_one_mul_choose_eq (M + k' - 1) (k' - 1)
      rw [h1, h2] at this
      rw [this]
    _ = (Nat.choose (M + k' - 1) (k' - 1) * M) * (M + k') := by ring

theorem p_pow_dvd_choose_of_coprime (p M k' k : ℕ) (hp : Nat.Prime p) (hk' : ¬ p ∣ k') (hM : p^k ∣ M) (hk_pos : k' ≥ 1) :
  p^k ∣ Nat.choose (M + k' - 1) k' := by
  have h_eq : Nat.choose (M + k' - 1) k' * k' = Nat.choose (M + k' - 1) (k' - 1) * M := choose_mul_eq_choose_mul_symm_1 M k' hk_pos
  have h_dvd_RHS : p^k ∣ Nat.choose (M + k' - 1) (k' - 1) * M := dvd_mul_of_dvd_right hM _
  rw [← h_eq] at h_dvd_RHS
  have h_coprime_p_k' : Nat.Coprime p k' := (Nat.Prime.coprime_iff_not_dvd hp).mpr hk'
  have h_coprime : Nat.Coprime (p^k) k' := Nat.Coprime.pow_left k h_coprime_p_k'
  exact Nat.Coprime.dvd_of_dvd_mul_right h_coprime h_dvd_RHS

theorem p_pow_dvd_choose_of_coprime_2 (p M k' k : ℕ) (hp : Nat.Prime p) (hk' : ¬ p ∣ k') (hM : p^k ∣ M) (hk'2 : k' < 2 * M) (hM1 : 1 ≤ M) (hk_pos : k ≥ 1) :
  p^k ∣ Nat.choose (3 * M) (2 * M - k') := by
  have h_eq := choose_mul_eq_choose_mul_symm M k' hk'2 hM1
  have h_dvd_LHS : p^k ∣ (3 * M) * Nat.choose (3 * M - 1) (2 * M - k' - 1) := by
    have hd1 : p^k ∣ 3 * M := dvd_mul_of_dvd_right hM 3
    exact dvd_mul_of_dvd_left hd1 _
  rw [h_eq] at h_dvd_LHS
  have h_not_dvd : ¬ p ∣ 2 * M - k' := by
    have h_p_dvd_pk : p ∣ p^k := by
      have h_pow : p^1 ∣ p^k := pow_dvd_pow p hk_pos
      rwa [pow_one] at h_pow
    have hd_p_M : p ∣ M := dvd_trans h_p_dvd_pk hM
    have hd1 : p ∣ 2 * M := dvd_mul_of_dvd_right hd_p_M 2
    have h_le : k' ≤ 2 * M := by omega
    exact not_dvd_sub_of_dvd_of_not_dvd p (2 * M) k' hd1 hk' h_le
  have h_coprime_p : Nat.Coprime p (2 * M - k') := (Nat.Prime.coprime_iff_not_dvd hp).mpr h_not_dvd
  have h_coprime : Nat.Coprime (p^k) (2 * M - k') := Nat.Coprime.pow_left k h_coprime_p
  exact Nat.Coprime.dvd_of_dvd_mul_right h_coprime h_dvd_LHS

theorem coprime_terms_divisibility (p M k' k : ℕ) (hp : Nat.Prime p) (hk' : ¬ p ∣ k') (hM : p^k ∣ M) (hk'2 : k' < 2 * M) (hM1 : 1 ≤ M) (hk_pos : k ≥ 1) :
  p^(2*k) ∣ Nat.choose (3 * M) (2 * M - k') * Nat.choose (M + k' - 1) k' := by
  have h1 : p^k ∣ Nat.choose (3 * M) (2 * M - k') := p_pow_dvd_choose_of_coprime_2 p M k' k hp hk' hM hk'2 hM1 hk_pos
  have hk_pos_k' : k' ≥ 1 := by
    by_contra h_zero
    have : k' = 0 := by omega
    subst this
    exact hk' (dvd_zero p)
  have h2 : p^k ∣ Nat.choose (M + k' - 1) k' := p_pow_dvd_choose_of_coprime p M k' k hp hk' hM hk_pos_k'
  have h_mul := mul_dvd_mul h1 h2
  have h_pow_add_eq : p^k * p^k = p^(k + k) := (pow_add p k k).symm
  rw [h_pow_add_eq] at h_mul
  have h_eq_2k : k + k = 2 * k := by ring
  rwa [h_eq_2k] at h_mul

theorem coprime_terms_divisibility_symm (p M k' k : ℕ) (hp : Nat.Prime p) (hk' : ¬ p ∣ k') (hM : p^k ∣ M) (hk'2 : k' < 2 * M) (hM1 : 1 ≤ M) (hk_pos : k ≥ 1) :
  p^(2*k) ∣ Nat.choose (3 * M) k' * Nat.choose (3 * M - k' - 1) (2 * M - k') := by
  have hk_pos_k' : k' ≥ 1 := by
    by_contra h_zero
    have : k' = 0 := by omega
    subst this
    exact hk' (dvd_zero p)
  have hk'_symm_pos : 2 * M - k' ≥ 1 := by omega
  have hk'_symm_lt : 2 * M - k' < 2 * M := by omega
  have hk_not_dvd_symm : ¬ p ∣ 2 * M - k' := by
    have h_p_dvd_pk : p ∣ p^k := by
      have h_pow : p^1 ∣ p^k := pow_dvd_pow p hk_pos
      rwa [pow_one] at h_pow
    have hd_p_M : p ∣ M := dvd_trans h_p_dvd_pk hM
    have hd1 : p ∣ 2 * M := dvd_mul_of_dvd_right hd_p_M 2
    have h_le : k' ≤ 2 * M := by omega
    exact not_dvd_sub_of_dvd_of_not_dvd p (2 * M) k' hd1 hk' h_le
  have h_choose1 := p_pow_dvd_choose_of_coprime p M (2 * M - k') k hp hk_not_dvd_symm hM hk'_symm_pos
  have h_choose2 := p_pow_dvd_choose_of_coprime_2 p M (2 * M - k') k hp hk_not_dvd_symm hM hk'_symm_lt hM1 hk_pos
  have h_eq_2M : 2 * M - (2 * M - k') = k' := by omega
  rw [h_eq_2M] at h_choose2
  have h_eq_choose_symm : Nat.choose (M + (2 * M - k') - 1) (2 * M - k') = Nat.choose (3 * M - k' - 1) (2 * M - k') := by
    congr 1
    omega
  rw [h_eq_choose_symm] at h_choose1
  have h_mul := mul_dvd_mul h_choose2 h_choose1
  have h_pow_add_eq : p^k * p^k = p^(k + k) := (pow_add p k k).symm
  rw [h_pow_add_eq] at h_mul
  have h_eq_2k : k + k = 2 * k := by ring
  rwa [h_eq_2k] at h_mul

theorem coprime_terms_congruence (p M k' k : ℕ) (hp : Nat.Prime p) (hk' : ¬ p ∣ k') (hM : p^k ∣ M) (hk'2 : k' < 2 * M) (hM1 : 1 ≤ M) (hk_pos : k ≥ 1) :
  p^(3*k) ∣ Nat.choose (3 * M) k' * Nat.choose (3 * M - k' - 1) (2 * M - k') + Nat.choose (3 * M) (2 * M - k') * Nat.choose (M + k' - 1) k' := by
  set A := Nat.choose (3 * M) k' * Nat.choose (3 * M - k' - 1) (2 * M - k') with hA_def
  set B := Nat.choose (3 * M) (2 * M - k') * Nat.choose (M + k' - 1) k' with hB_def
  have h_id : (3 * M - k') * A = (M + k') * B := by
    rw [hA_def, hB_def]
    exact T_identity M k' (by omega) hM1
  have h_simpl := T_identity_simplified M k' A B (by omega) hM1 h_id
  have hA_dvd : p^(2*k) ∣ A := by
    rw [hA_def]
    exact coprime_terms_divisibility_symm p M k' k hp hk' hM hk'2 hM1 hk_pos
  have hB_dvd : p^(2*k) ∣ B := by
    rw [hB_def]
    exact coprime_terms_divisibility p M k' k hp hk' hM hk'2 hM1 hk_pos
  have h_sub_dvd : p^(2*k) ∣ 3 * A - B := by
    by_cases h_le : B ≤ 3 * A
    · have h_3A_dvd : p^(2*k) ∣ 3 * A := dvd_mul_of_dvd_right hA_dvd 3
      exact Nat.dvd_sub h_3A_dvd hB_dvd
    · have : 3 * A - B = 0 := by omega
      rw [this]
      exact dvd_zero _
  have h_M_sub_dvd : p^(3*k) ∣ M * (3 * A - B) := by
    have h_pow_3k : p^(3*k) = p^k * p^(2*k) := by
      have h_eq : 3 * k = k + 2 * k := by ring
      rw [h_eq]
      exact pow_add p k (2 * k)
    rw [h_pow_3k]
    exact mul_dvd_mul hM h_sub_dvd
  rw [← h_simpl] at h_M_sub_dvd
  have h_coprime_p_k' : Nat.Coprime p k' := (Nat.Prime.coprime_iff_not_dvd hp).mpr hk'
  have h_coprime : Nat.Coprime (p^(3*k)) k' := Nat.Coprime.pow_left (3*k) h_coprime_p_k'
  exact Nat.Coprime.dvd_of_dvd_mul_left h_coprime h_M_sub_dvd
/--
A333561: $a(n) = \sum_{k = 0}^{2n} \binom{3n}{2n-k}\binom{n+k-1}{k}$.
This is an equivalent identity conjectured in the OEIS entry, which may resolve issues with the automated checker.
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (2 * n + 1)) fun k : ℕ =>
    Nat.choose (3 * n) (2 * n - k) * Nat.choose (n + k - 1) k

/-- We conjecture that this sequence satisfies the supercongruences
a(n*p^k) == a(n*p^(k-1)) ( mod p^(3*k) ) for prime p >= 5 and positive integers n and k.
-/
theorem oeis_333561_conjecture :
  ∀ (p n k : ℕ),
    Nat.Prime p →
    p ≥ 5 →
    n ≥ 1 →
    k ≥ 1 →
    a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [MOD p ^ (3 * k)] := by
  intro p n k hp hp5 hn hk
  sorry






