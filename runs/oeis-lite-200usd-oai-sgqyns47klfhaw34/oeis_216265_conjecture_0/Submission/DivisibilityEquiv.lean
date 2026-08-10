import FormalConjectures.Util.ProblemImports

open Nat

lemma cube_succ_le_two_mul_cube_of_ten_le {n : ℕ} (hn : 10 ≤ n) :
    (n + 1) ^ 3 ≤ 2 * n ^ 3 := by
  nlinarith [sq_nonneg (n : ℤ), hn]

lemma cube_lt_two_pow_succ_of_ten_le {n : ℕ} (hn : 10 ≤ n) : n ^ 3 < 2 ^ (n + 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      calc
        (n + 1) ^ 3 ≤ 2 * n ^ 3 := cube_succ_le_two_mul_cube_of_ten_le hn
        _ < 2 * 2 ^ (n + 1) := (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).2 ih
        _ = 2 ^ (n + 1 + 1) := by
          conv_rhs => rw [show n + 1 + 1 = (n + 1).succ by omega, Nat.pow_succ']

lemma log_cube_le_self_of_two_le {n p : ℕ} (hn : 10 ≤ n) (hp2 : 2 ≤ p) :
    Nat.log p (n ^ 3) ≤ n := by
  have hlt2 : n ^ 3 < 2 ^ (n + 1) := cube_lt_two_pow_succ_of_ten_le hn
  have hpow : 2 ^ (n + 1) ≤ p ^ (n + 1) := Nat.pow_le_pow_left hp2 (n + 1)
  have hlt : n ^ 3 < p ^ (n + 1) := lt_of_lt_of_le hlt2 hpow
  have hn3ne : n ^ 3 ≠ 0 := by positivity
  exact Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow hn3ne hlt)

lemma log_cube_le_div_cube_sub_self {n p : ℕ} (hn : 14 ≤ n) (hp2 : 2 ≤ p)
    (hle : p ≤ n ^ 3 - n) :
    Nat.log p (n ^ 3) ≤ (n ^ 3 - n) / p := by
  have hn10 : 10 ≤ n := by omega
  have hlogn : Nat.log p (n ^ 3) ≤ n := log_cube_le_self_of_two_le hn10 hp2
  by_cases hsmall : p ≤ n ^ 2 - 1
  · have hnp : n ≤ (n ^ 3 - n) / p := by
      have hmulle : n * p ≤ n ^ 3 - n := by
        calc
          n * p ≤ n * (n ^ 2 - 1) := Nat.mul_le_mul_left n hsmall
          _ = n ^ 3 - n := by
            rw [Nat.mul_sub_left_distrib, mul_one]
            ring_nf
      exact (Nat.le_div_iff_mul_le (by omega : 0 < p)).2 (by simpa [mul_comm] using hmulle)
    exact hlogn.trans hnp
  · have hp2gt : n ^ 3 < p ^ 2 := by
      have hpge : n ^ 2 ≤ p := by omega
      calc
        n ^ 3 < (n ^ 2) ^ 2 := by
          nlinarith [sq_nonneg (n : ℤ), hn]
        _ ≤ p ^ 2 := Nat.pow_le_pow_left hpge 2
    have hloglt : Nat.log p (n ^ 3) < 2 := by
      exact Nat.log_lt_of_lt_pow (by positivity : n ^ 3 ≠ 0) hp2gt
    have hlogle1 : Nat.log p (n ^ 3) ≤ 1 := by omega
    have hdivpos : 1 ≤ (n ^ 3 - n) / p := by
      exact Nat.succ_le_iff.mpr (Nat.div_pos hle (by omega : 0 < p))
    exact hlogle1.trans hdivpos

lemma div_le_factorization_factorial {m p : ℕ} (hp : p.Prime) :
    m / p ≤ (m !).factorization p := by
  by_cases hpm : p ≤ m
  · rw [Nat.factorization_factorial hp (Nat.lt_add_one (Nat.log p m))]
    have hlogpos : 0 < Nat.log p m := Nat.log_pos hp.one_lt hpm
    have hmem : 1 ∈ Finset.Ico 1 (Nat.log p m + 1) := by
      simp only [Finset.mem_Ico]
      exact ⟨le_rfl, Nat.succ_lt_succ hlogpos⟩
    have hterm : (fun i : ℕ => m / p ^ i) 1 = m / p := by simp
    calc
      m / p = (fun i : ℕ => m / p ^ i) 1 := hterm.symm
      _ ≤ ∑ i ∈ Finset.Ico 1 (Nat.log p m + 1), m / p ^ i := by
        exact Finset.single_le_sum (f := fun i : ℕ => m / p ^ i) (s := Finset.Ico 1 (Nat.log p m + 1)) (fun i hi => by omega) hmem
  · have : m / p = 0 := Nat.div_eq_of_lt (Nat.lt_of_not_ge hpm)
    simp [this]

lemma choose_cube_factorization_le_factorial_of_le {n p : ℕ} (hn : 14 ≤ n) (hp : p.Prime)
    (hle : p ≤ n ^ 3 - n) :
    (Nat.choose (n ^ 3) n).factorization p ≤ ((n ^ 3 - n)!).factorization p := by
  exact Nat.factorization_choose_le_log.trans
    ((log_cube_le_div_cube_sub_self hn hp.two_le hle).trans (div_le_factorization_factorial hp))

lemma choose_cube_dvd_factorial_iff_no_interval_prime {n : ℕ} (hn : 14 ≤ n) :
    Nat.choose (n ^ 3) n ∣ (n ^ 3 - n)! ↔
      ¬ ∃ p, p.Prime ∧ n ^ 3 - n < p ∧ p ≤ n ^ 3 := by
  constructor
  · intro hdiv hpr
    rcases hpr with ⟨p,hp,hlo,hhi⟩
    have hpdvd : p ∣ Nat.choose (n ^ 3) n := by
      have hnle : n ≤ n ^ 3 - n := by
        have h2n : 2 * n ≤ n ^ 3 := by nlinarith [sq_nonneg (n : ℤ), hn]
        exact Nat.le_sub_of_add_le (by simpa [two_mul] using h2n)
      have ha : n < p := lt_of_le_of_lt hnle hlo
      exact hp.dvd_choose ha hlo hhi
    have hpdvdfact : p ∣ (n ^ 3 - n)! := hpdvd.trans hdiv
    have hple : p ≤ n ^ 3 - n := (hp.dvd_factorial.mp hpdvdfact)
    omega
  · intro hno
    have hchoose_ne : Nat.choose (n ^ 3) n ≠ 0 := by
      exact (Nat.choose_pos (by
        have hnpos : 0 < n := by omega
        calc n = n * 1 := by rw [mul_one]
          _ ≤ n * (n * n) := Nat.mul_le_mul_left n (by nlinarith [hnpos])
          _ = n ^ 3 := by ring)).ne'
    have hfact_ne : (n ^ 3 - n)! ≠ 0 := Nat.factorial_ne_zero _
    rw [← Nat.factorization_le_iff_dvd hchoose_ne hfact_ne]
    rw [Finsupp.le_iff]
    intro p hpSupp
    by_cases hpprime : p.Prime
    · by_cases hle : p ≤ n ^ 3 - n
      · exact choose_cube_factorization_le_factorial_of_le hn hpprime hle
      · have hpgt : n ^ 3 - n < p := Nat.lt_of_not_ge hle
        have hp_le_cube : p ≤ n ^ 3 := by
          by_contra hnot
          have hgt : n ^ 3 < p := Nat.lt_of_not_ge hnot
          have hz : (Nat.choose (n ^ 3) n).factorization p = 0 := Nat.factorization_choose_eq_zero_of_lt hgt
          exact (Finsupp.mem_support_iff.mp hpSupp) hz
        exact False.elim (hno ⟨p, hpprime, hpgt, hp_le_cube⟩)
    · have hz : (Nat.choose (n ^ 3) n).factorization p = 0 := Nat.factorization_eq_zero_of_not_prime _ hpprime
      exact False.elim ((Finsupp.mem_support_iff.mp hpSupp) hz)
#print axioms choose_cube_dvd_factorial_iff_no_interval_prime
