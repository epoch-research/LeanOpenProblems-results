import os

path = "/workspace/leanproject/Submission/Spec.lean"
with open(path, 'r') as f:
    content = f.read()

# Locate the beginning of den_neq_one_of_odd_factor
start_marker = "lemma q_not_dvd_num1_helper"
end_marker = "theorem oeis_265709_conjecture_0.disproof"

start_idx = content.find(start_marker)
end_idx = content.find(end_marker)

if start_idx == -1:
    print("Error: Could not find start marker!")
    exit(1)
if end_idx == -1:
    print("Error: Could not find end marker!")
    exit(1)

print(f"Start index: {start_idx}, End index: {end_idx}")

new_proof = """lemma q_not_dvd_num1_helper (q1 : ℚ) (hq1_pos : q1.num > 0) (q : ℕ) (hq_prime : q.Prime) (hq_dvd : q ∣ q1.den) :
  ¬ q ∣ q1.num.natAbs := by
  intro h_dvd
  have h_num1_cop : q1.num.natAbs.Coprime q1.den := q1.reduced
  have h_gcd : q ∣ Nat.gcd q1.num.natAbs q1.den := Nat.dvd_gcd h_dvd hq_dvd
  rw [h_num1_cop] at h_gcd
  have : q ≤ 1 := Nat.le_of_dvd (by decide) h_gcd
  have : q ≥ 2 := hq_prime.two_le
  omega

lemma q_not_dvd_den2_helper (q1 q2 : ℚ) (h_cop : q1.den.Coprime q2.den) (q : ℕ) (hq_prime : q.Prime) (hq_dvd : q ∣ q1.den) :
  ¬ q ∣ q2.den := by
  intro h_dvd
  have h_gcd : q ∣ Nat.gcd q1.den q2.den := Nat.dvd_gcd hq_dvd h_dvd
  rw [h_cop] at h_gcd
  have : q ≤ 1 := Nat.le_of_dvd (by decide) h_gcd
  have : q ≥ 2 := hq_prime.two_le
  omega

lemma q_adic_contradiction (q1 q2 : ℚ) (hq1_pos : q1.num > 0) (hq2_pos : q2.num > 0)
  (hden12 : (q1 * q2).den = 1) (h_cop : q1.den.Coprime q2.den)
  (q : ℕ) (hq_prime : q.Prime) (hq_dvd : q ∣ q1.den) : False := by
  have h_prime_fact : Fact q.Prime := ⟨hq_prime⟩
  have h_val_n : padicValRat q (q1 * q2) ≥ 0 := by
    exact padicValRat_nonneg_of_den_eq_one q hq_prime _ hden12
  have h_val_mul : padicValRat q (q1 * q2) = padicValRat q q1 + padicValRat q q2 := by
    have hq1_nz : q1 ≠ 0 := by
      intro hc
      rw [hc] at hq1_pos
      norm_num at hq1_pos
    have hq2_nz : q2 ≠ 0 := by
      intro hc
      rw [hc] at hq2_pos
      norm_num at hq2_pos
    exact padicValRat.mul hq1_nz hq2_nz
  have h_val_q1 : padicValRat q q1 = padicValInt q q1.num - padicValNat q q1.den := by
    exact padicValRat_def q q1
  have h_val_q2 : padicValRat q q2 = padicValInt q q2.num - padicValNat q q2.den := by
    exact padicValRat_def q q2
  have h_num1_cop : q1.num.natAbs.Coprime q1.den := q1.reduced
  have h_q_not_dvd_num1 : ¬ q ∣ q1.num.natAbs := q_not_dvd_num1_helper q1 hq1_pos q hq_prime hq_dvd
  have h_val_num1 : padicValInt q q1.num = 0 := by
    have h_eq : padicValInt q q1.num = padicValNat q q1.num.natAbs := rfl
    rw [h_eq]
    exact padicValNat.eq_zero_of_not_dvd h_q_not_dvd_num1
  have h_val_den1 : padicValNat q q1.den ≥ 1 := by
    have h_nz : q1.den ≠ 0 := by
      have : q1.den > 0 := q1.den_pos
      omega
    exact one_le_padicValNat_of_dvd h_nz hq_dvd
  have h_q_not_dvd_den2 : ¬ q ∣ q2.den := q_not_dvd_den2_helper q1 q2 h_cop q hq_prime hq_dvd
  have h_val_den2 : padicValNat q q2.den = 0 := padicValNat.eq_zero_of_not_dvd h_q_not_dvd_den2
  have h_val_q1_neg : padicValRat q q1 ≤ -1 := by
    rw [h_val_q1, h_val_num1]
    omega
  have h_val_q2_nonneg : padicValRat q q2 ≥ 0 := by
    rw [h_val_q2, h_val_den2]
    have h_zero : (↑0 : ℤ) = 0 := rfl
    rw [h_zero]
    have : (↑(padicValInt q q2.num) : ℤ) - 0 = (↑(padicValInt q q2.num) : ℤ) := by ring
    rw [this]
    positivity
  omega

lemma den_neq_one_of_odd_factor (n : ℕ) (p : ℕ) (hp : p ∈ n.primeFactorsList) (hp_odd : p % 2 = 1) :
  ((n.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))).den ≠ 1 := by
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactorsList hp
  have hp_div : p ∣ n := Nat.dvd_of_mem_primeFactorsList hp
  have hn_nz : n ≠ 0 := by
    intro h_zero
    rw [h_zero] at hp
    simp only [Nat.primeFactorsList_zero, List.not_mem_nil] at hp
  let b := padicValNat 2 n
  let m := n / 2^b
  rcases coprime_factorization 2 Nat.prime_two n hn_nz with ⟨h_eq_mul, h_cop, hm_nz⟩
  change n = 2^b * m at h_eq_mul
  change m ≠ 0 at hm_nz
  change Nat.Coprime (2^b) m at h_cop
  have hm_odd : m % 2 = 1 := by
    have : m % 2 ≠ 0 := by
      intro h_mod
      have : 2 ∣ m := Nat.dvd_of_mod_eq_zero h_mod
      have h_div_n : 2^(b+1) ∣ n := by
        rw [h_eq_mul]
        change 2^(b+1) ∣ 2^b * m
        rcases this with ⟨k, hk_eq⟩
        rw [hk_eq]
        use k
        ring
      have h_le : b + 1 ≤ padicValNat 2 n := (padicValNat_dvd_iff_le hn_nz).mp h_div_n
      omega
    omega
  have hp_dvd_m : p ∣ m := by
    have h_prime_p : p.Prime := hp_prime
    have h_dvd_mul : p ∣ 2^b * m := by
      rw [← h_eq_mul]
      exact hp_div
    rcases h_prime_p.dvd_mul.mp h_dvd_mul with h1 | h2
    · have : p ∣ 2 := hp_prime.dvd_of_dvd_pow h1
      have hp_le2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) this
      have hp_ge3 : p ≥ 3 := by
        have : p ≥ 2 := hp_prime.two_le
        omega
      omega
    · exact h2
  have hm_gt1 : 1 < m := by
    have : m ≥ p := Nat.le_of_dvd (Nat.pos_of_ne_zero hm_nz) hp_dvd_m
    have hp_ge3 : p ≥ 3 := by
      have : p ≥ 2 := hp_prime.two_le
      omega
    omega
  have hm_val : padicValRat 2 (m.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) < 0 :=
    padicValRat_two_sum_divisors_odd m hm_odd hm_gt1
  have hn_eq_sum : (n.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) =
    ((2^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) *
    (m.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) := by
    have h2b_nz : 2^b ≠ 0 := _root_.ne_of_gt (Nat.pow_pos (by decide : 0 < 2))
    rw [h_eq_mul]
    exact g_mul_of_coprime h2b_nz hm_nz h_cop
  have h2b_sum_pos : ((2^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) > 0 := by
    apply sum_divisors_pos
    exact Nat.one_le_pow b 2 (by omega)
  have hm_sum_pos : (m.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) > 0 := by
    apply sum_divisors_pos
    omega
  let q1 := (2^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)
  let q2 := m.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)
  have hq1_pos : q1.num > 0 := Rat.num_pos.mpr h2b_sum_pos
  have hq2_pos : q2.num > 0 := Rat.num_pos.mpr hm_sum_pos
  by_cases hb0 : b = 0
  · have hb0_eq : b = 0 := hb0
    have h_q1 : q1 = 1 := by
      dsimp [q1]
      rw [hb0_eq, pow_zero]
      have : (1 : ℕ).divisors = {1} := by decide
      rw [this, sum_singleton]
      rfl
    have h_sum : (n.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = q2 := by
      rw [hn_eq_sum]
      change q1 * q2 = q2
      rw [h_q1, one_mul]
    intro h_den
    rw [h_sum] at h_den
    have h_val_neg : padicValRat 2 q2 < 0 := hm_val
    exact den_neq_one_of_padicValRat_neg 2 q2 h_val_neg h_den
  · have hb_ge1 : b ≥ 1 := by omega
    have h_q1_den_ne_1 : q1.den ≠ 1 := den_neq_one_of_pow_two b hb_ge1
    have h_q1_den_gt_1 : q1.den > 1 := by
      have : q1.den > 0 := q1.den_pos
      omega
    rcases Nat.exists_prime_and_dvd h_q1_den_ne_1 with ⟨q, hq_prime, hq_dvd⟩
    intro h_den
    have h_den_q : (q1 * q2).den = 1 := by
      rw [← hn_eq_sum]
      exact h_den
    have h_cop_den : q1.den.Coprime q2.den := coprime_den q1 q2 hq1_pos h_den_q
    exact q_adic_contradiction q1 q2 hq1_pos hq2_pos h_den_q h_cop_den q hq_prime hq_dvd


"""

# Replace the text between start_idx and end_idx
modified_content = content[:start_idx] + new_proof + content[end_idx:]

with open(path, 'w') as f:
    f.write(modified_content)

print("Replacement complete successfully!")
