import FormalConjectures.Util.ProblemImports

open Nat

def x_seq_test : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 1 => 2 * (x_seq_test n) + Nat.lcm (x_seq_test n) (n + 1)

lemma x_seq_dvd_of_le_test (a b : ℕ) (ha : a ≥ 1) (hab : a ≤ b) : x_seq_test a ∣ x_seq_test b := by
  sorry

lemma m_q_le_test (q : ℕ) (hq : Nat.Prime q) (hq3 : q ≥ 3) :
    ∃ m ≤ q^2 - 2, m ≥ 1 ∧ q ∣ x_seq_test m := by
  sorry
termination_by q

lemma sq_free_contradiction (q : ℕ) (hq : Nat.Prime q) (hq11_ge : q ≥ 11) (hq2_prime : ¬ Nat.Prime (q - 2))
    (h_nz : ¬ (x_seq_test ((q - 2) * q)) % q = 0)
    (h_not : ¬ q ∣ x_seq_test ((q - 2) * q - 1))
    (G : ℕ) (hG : Nat.gcd (x_seq_test ((q - 2) * q - 1)) ((q - 2) * q) = G)
    (h_G_dvd : G ∣ q - 2)
    (h_sf : ∀ p1, Nat.Prime p1 → p1 ∣ q - 2 → ¬ p1^2 ∣ q - 2) : False := by
  have h_eq : q - 2 = G * ((q - 2) / G) := (Nat.mul_div_cancel' h_G_dvd).symm
  let K := (q - 2) / G
  have h_K_gt1 : K > 1 := by
    by_contra hc
    have h_K_le1 : K ≤ 1 := by omega
    have h_K_pos : K > 0 := by
      dsimp [K]
      apply Nat.div_pos h_G_dvd
      omega
    have h_K_eq1 : K = 1 := by omega
    -- If K = 1, then G = q - 2.
    have hG_eq : G = q - 2 := by
      dsimp [K] at h_K_eq1
      exact (Nat.div_eq_one_iff_eq h_G_dvd (by omega)).mp h_K_eq1
    -- This means q - 2 ∣ x_seq_test ((q - 2) * q - 1)
    have hdvd_seq : q - 2 ∣ x_seq_test ((q - 2) * q - 1) := by
      rw [← hG_eq, ← hG]
      exact Nat.gcd_dvd_left _ _
    -- Since q - 2 is composite, let p1 be its minFac
    have hq2_ge5 : q - 2 ≥ 5 := by omega
    let p1 := Nat.minFac (q - 2)
    have hp1_prime : Nat.Prime p1 := Nat.minFac_prime (by omega)
    have hp1_ge3 : p1 ≥ 3 := by sorry
    rcases m_q_le_test p1 hp1_prime hp1_ge3 with ⟨m1, hm1_le, hm1_ge, hp1_dvd_m1⟩
    have hp1_le : p1 ≤ q - 3 := by sorry
    have hm1_le_N1 : m1 ≤ (q - 2) * q - 1 := by sorry
    have h_dvd_seq' : x_seq_test m1 ∣ x_seq_test ((q - 2) * q - 1) := x_seq_dvd_of_le_test m1 ((q - 2) * q - 1) hm1_ge hm1_le_N1
    have hp1_dvd_seq' : p1 ∣ x_seq_test ((q - 2) * q - 1) := Nat.dvd_trans hp1_dvd_m1 h_dvd_seq'
    sorry
  let p1 := Nat.minFac K
  have hp1_prime : Nat.Prime p1 := Nat.minFac_prime (by omega)
  have hp1_dvd_K : p1 ∣ K := Nat.minFac_dvd K
  have hp1_ge3 : p1 ≥ 3 := by sorry
  rcases m_q_le_test p1 hp1_prime hp1_ge3 with ⟨m1, hm1_le, hm1_ge, hp1_dvd_m1⟩
  have hp1_le : p1 ≤ q - 3 := by sorry
  have hm1_le_N1 : m1 ≤ (q - 2) * q - 1 := by sorry
  have h_dvd_seq' : x_seq_test m1 ∣ x_seq_test ((q - 2) * q - 1) := x_seq_dvd_of_le_test m1 ((q - 2) * q - 1) hm1_ge hm1_le_N1
  have hp1_dvd_seq' : p1 ∣ x_seq_test ((q - 2) * q - 1) := Nat.dvd_trans hp1_dvd_m1 h_dvd_seq'
  have hp1_dvd_N : p1 ∣ (q - 2) * q := by
    have hd1 : p1 ∣ q - 2 := by
      have hd_K : p1 ∣ K := hp1_dvd_K
      have hd_K2 : K ∣ q - 2 := by
        rw [h_eq]
        exact Nat.dvd_mul_left K G
      exact Nat.dvd_trans hd_K hd_K2
    exact Nat.dvd_mul_of_dvd_left hd1 q
  have hp1_dvd_G : p1 ∣ G := by
    rw [← hG]
    exact Nat.dvd_gcd hp1_dvd_seq' hp1_dvd_N
  have hp1_sq_dvd : p1^2 ∣ q - 2 := by
    rw [h_eq]
    have h_sq : p1^2 = p1 * p1 := by ring
    rw [h_sq]
    rcases hp1_dvd_G with ⟨g, rfl⟩
    rcases hp1_dvd_K with ⟨k, rfl⟩
    use g * k
    ring
  have hp1_dvd_q2 : p1 ∣ q - 2 := by
    have hd_K : p1 ∣ K := hp1_dvd_K
    have hd_K2 : K ∣ q - 2 := by
      rw [h_eq]
      exact Nat.dvd_mul_left K G
    exact Nat.dvd_trans hd_K hd_K2
  have h_not_sq_dvd := h_sf p1 hp1_prime hp1_dvd_q2
  contradiction
