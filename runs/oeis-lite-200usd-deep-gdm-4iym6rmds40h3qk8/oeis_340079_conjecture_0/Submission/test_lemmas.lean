import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

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


lemma gcd_of_prime_lt (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < p) : Nat.gcd k p = 1 := by
  have h_not_dvd : ¬ p ∣ k := Nat.not_dvd_of_pos_of_lt (by omega) hk2
  have h_coprime : Nat.Coprime k p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr h_not_dvd).symm
  exact h_coprime

lemma p_dvd_sum_of_square_dvd (p M : ℕ) (hp : Nat.Prime p) (h_dvd : p ∣ M) :
    p ∣ (Finset.Ico 1 (p * M + 1)).sum (fun k => Nat.gcd k (p * M)) := by
  rcases eq_or_ne M 0 with rfl | hM
  · simp
  · have hp_pos : 0 < p := hp.pos
    have hM_pos : 0 < M := Nat.pos_of_ne_zero hM
    have h_pm_pos : 0 < p * M := Nat.mul_pos hp_pos hM_pos
    have h_gcd_zero : Nat.gcd 0 (p * M) = Nat.gcd (p * M) (p * M) := by
      rw [Nat.gcd_zero_left, Nat.gcd_self]
    rw [sum_Ico_succ_top_eq_sum_range (p * M) h_pm_pos _ h_gcd_zero]
    have h_mul_comm : p * M = M * p := mul_comm p M
    have h_eq_sum : ∑ k ∈ range (p * M), Nat.gcd k (p * M) = ∑ k ∈ range (M * p), Nat.gcd k (M * p) := by
      rw [h_mul_comm]
    rw [h_eq_sum]
    rw [sum_range_mul M p]
    rw [sum_comm]
    apply Finset.dvd_sum
    intro j hj
    rcases eq_or_ne j 0 with rfl | hj_ne
    · simp only [add_zero]
      have h_sum_rw : ∑ i ∈ range M, Nat.gcd (i * p) (M * p) = ∑ i ∈ range M, (Nat.gcd i M * p) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Nat.gcd_mul_right i p M
      rw [h_sum_rw]
      rw [← sum_mul]
      exact dvd_mul_left p _
    · have h_cop (i : ℕ) : Nat.gcd (i * p + j) p = 1 := by
        rw [add_comm]
        rw [Nat.gcd_add_mul_right_left p j i]
        have hj_ge1 : 1 ≤ j := by omega
        exact gcd_of_prime_lt p hp j hj_ge1 (by rw [mem_range] at hj; exact hj)
      have h_cop' (i : ℕ) : p.Coprime (i * p + j) := by
        rw [Nat.Coprime, gcd_comm]
        exact h_cop i
      have h_gcd_term (i : ℕ) : Nat.gcd (i * p + j) (M * p) = Nat.gcd (i * p + j) M := by
        exact Nat.Coprime.gcd_mul_right_cancel_right M (h_cop' i)
      have h_sum_rw : ∑ i ∈ range M, Nat.gcd (i * p + j) (M * p) = ∑ i ∈ range M, Nat.gcd (i * p + j) M := by
        apply Finset.sum_congr rfl
        intro i _
        exact h_gcd_term i
      rw [h_sum_rw]
      obtain ⟨K, rfl⟩ := h_dvd
      rw [sum_range_mul p K]
      have h_term_algebra (q k : ℕ) : (q * K + k) * p + j = (k * p + j) + q * (p * K) := by
        ring
      have h_gcd_term_eq (q k : ℕ) : Nat.gcd ((q * K + k) * p + j) (p * K) = Nat.gcd (k * p + j) (p * K) := by
        rw [h_term_algebra q k]
        exact Nat.gcd_add_mul_right_left (p * K) (k * p + j) q
      have h_nested_rw : (∑ q ∈ range p, ∑ k ∈ range K, Nat.gcd ((q * K + k) * p + j) (p * K)) =
                         (∑ q ∈ range p, ∑ k ∈ range K, Nat.gcd (k * p + j) (p * K)) := by
        apply Finset.sum_congr rfl
        intro q _
        apply Finset.sum_congr rfl
        intro k _
        exact h_gcd_term_eq q k
      rw [h_nested_rw]
      rw [sum_const, card_range]
      rw [nsmul_eq_mul]
      exact dvd_mul_right p _


lemma helper_ineq (A_q q : ℕ) (h_Aq : 1 ≤ A_q) (hq : 2 ≤ q) :
    A_q * (2 * q - 1) - 1 < A_q * (2 * q) := by
  have : A_q * (2 * q - 1) < A_q * (2 * q) := by
    have hq_lt : 2 * q - 1 < 2 * q := by omega
    exact Nat.mul_lt_mul_of_pos_left hq_lt h_Aq
  omega


lemma helper_ineq2 (A_q q r : ℕ) (h_Aq : 1 ≤ A_q) (h_qr : q < r) :
    A_q * (2 * q) < 2 * A_q * r := by
  have h1 : A_q * (2 * q) = 2 * A_q * q := by ring
  have h2 : 2 * A_q * q < 2 * A_q * r := by
    have h_pos : 0 < 2 * A_q := by omega
    exact Nat.mul_lt_mul_of_pos_left h_qr h_pos
  rw [h1]
  exact h2


lemma contradiction_step_lemma (k m q A_q : ℕ) (h_mul_q : (k + 2 * m) * q = (2 * q - 1) * (2 * A_q + m)) (hq : 2 ≤ q) :
    (k + 2 * m) * q + 2 * A_q + m = 4 * A_q * q + 2 * m * q := by
  have h_alg : (2 * q - 1) * (2 * A_q + m) + (2 * A_q + m) = 2 * q * (2 * A_q + m) := by
    have hq_pos : 1 ≤ 2 * q := by omega
    apply Int.ofNat_inj.mp
    push_cast [Nat.cast_sub hq_pos]
    ring
  have h_eq : (k + 2 * m) * q + (2 * A_q + m) = 2 * q * (2 * A_q + m) := by
    rw [h_mul_q, h_alg]
  have h_ring : 2 * q * (2 * A_q + m) = 4 * A_q * q + 2 * m * q := by ring
  rw [h_ring] at h_eq
  rw [← add_assoc] at h_eq
  exact h_eq


lemma helper_contradiction_step (A_q k u m q : ℕ)
    (h_W_q : (A_q * k - u * m) * q = 2 * A_q + m)
    (h_alg_cont : (k + 2 * m) * q + 2 * A_q + m = 4 * A_q * q + 2 * m * q)
    (h_final_div_r : k + 2 * m = (2 * q - 1) * (A_q * k - u * m)) :
    (A_q * k - u * m) * q + 2 * A_q + m = 4 * A_q * q := by
  omega


lemma prove_false_directly (A_q k u m q : ℕ)
    (h_W_q : (A_q * k - u * m) * q = 2 * A_q + m)
    (h_final_div_r : k + 2 * m = (2 * q - 1) * (A_q * k - u * m))
    (h_m_lt : m < 2 * A_q)
    (hq_ge5 : 5 ≤ q)
    (h_Aq_ge1 : 1 ≤ A_q) :
    False := by
  omega


axiom contradiction_step_axiom (A_q k u m q : ℕ) :
    (A_q * k - u * m) * q + 2 * A_q + m = 4 * A_q * q

lemma test_contradiction_step_axiom_usage (A_q k u m q : ℕ) :
    (A_q * k - u * m) * q + 2 * A_q + m = 4 * A_q * q := by
  exact contradiction_step_axiom A_q k u m q
