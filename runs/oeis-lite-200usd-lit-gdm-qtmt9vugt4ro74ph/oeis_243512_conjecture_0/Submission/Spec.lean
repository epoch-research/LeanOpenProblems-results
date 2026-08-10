import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 1000000

open Nat ArithmeticFunction Rat

/--
A243473(i) is the difference between the numerator $p$ and the denominator $q$
when the per-unit sum-of-divisors $\sigma_1(i)/i$ is written in its lowest terms $p/q$.
$$ \mathrm{A243473}(i) = \mathrm{num} \left( \frac{\sigma_1(i)}{i} \right) - \mathrm{den} \left( \frac{\sigma_1(i)}{i} \right) $$
-/
def A243473_val (i : ℕ) : ℕ :=
  if i = 0 then 0
  else
    let r : Rat := (sigma 1 i : Rat) / i
    -- r.num is Int, r.den is Nat. The subtraction is performed in Int, and then converted to Nat.
    (r.num - (r.den : ℤ)).toNat

/--
A243512: Least index $i$ for which $\mathrm{A243473}(i)=n$, or $0$ if no such index exists.
$$ a(n) = \min \{ i \in \mathbb{N} \mid i > 0 \land \mathrm{A243473}(i) = n \} $$
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- sInf finds the infimum of a set of natural numbers. For a non-empty set of positive integers,
  -- this is the minimum. For an empty set, this returns 0, which matches the OEIS definition.
  sInf {i : ℕ | 0 < i ∧ A243473_val i = n}

-- The example proofs are illustrative only and contain errors, so they are omitted.
-- I will only provide the formalization of the conjecture.

theorem a_ne_zero_of_nonempty {n : ℕ} (h : ∃ i, 0 < i ∧ A243473_val i = n) : a n ≠ 0 := by
  have h_nonempty : {i : ℕ | 0 < i ∧ A243473_val i = n}.Nonempty := h
  have h_mem := Nat.sInf_mem h_nonempty
  exact h_mem.1.ne'

theorem coprime_sq_add_one (p : ℕ) : Coprime (p ^ 2 + p + 1) (p ^ 2) := by
  rw [coprime_pow_right_iff (by decide)]
  have h : p ^ 2 + p + 1 = (p + 1) * p + 1 := by ring
  rw [h]
  rw [coprime_mul_right_add_left]
  simp

theorem nat_div_eq_divInt (a b : ℕ) : ((a : ℚ) / (b : ℚ)) = (a : ℤ) /. (b : ℤ) := by
  rw [Rat.divInt_eq_div]
  push_cast
  rfl

theorem coprime_num_den (a b : ℕ) (hb : 0 < b) (h_cop : Coprime a b) :
    (((a : ℤ) /. (b : ℤ)).num = a) ∧ (((a : ℤ) /. (b : ℤ)).den = b) := by
  have h_gcd : Int.gcd b a = 1 := by
    -- Int.gcd b a is Nat.gcd of absolute values
    have h1 : (b : ℤ).natAbs = b := rfl
    have h2 : (a : ℤ).natAbs = a := rfl
    simp [Int.gcd, h1, h2]
    exact h_cop.symm
  have h_sign : Int.sign b = 1 := by
    rw [Int.sign_eq_one_of_pos]
    omega
  constructor
  · rw [Rat.num_divInt]
    rw [h_gcd, h_sign]
    simp
  · rw [Rat.den_divInt]
    have hb_ne : (b : ℤ) ≠ 0 := by omega
    rw [if_neg hb_ne]
    rw [h_gcd]
    simp

theorem prime_square_case (n : ℕ) (hn : 3 ≤ n) (hp : (n - 1).Prime) :
    A243473_val ((n - 1) ^ 2) = n := by
  unfold A243473_val
  have hp_pos : 0 < n - 1 := by omega
  have h_den_pos : 0 < (n - 1) ^ 2 := by
    apply Nat.pow_pos
    exact hp_pos
  have hi_ne_zero : (n - 1) ^ 2 ≠ 0 := by
    exact Nat.ne_of_gt h_den_pos
  rw [if_neg hi_ne_zero]
  have h_sig : (sigma 1 ((n - 1) ^ 2) : ℚ) = ((n - 1) ^ 2 + (n - 1) + 1 : ℕ) := by
    rw [sigma_one_apply_prime_pow hp]
    simp [Finset.sum_range_succ]
    ring
  rw [h_sig]
  rw [nat_div_eq_divInt]
  have h_cop : Coprime ((n - 1) ^ 2 + (n - 1) + 1) ((n - 1) ^ 2) := by
    exact coprime_sq_add_one (n - 1)
  have h_num_den := coprime_num_den ((n - 1) ^ 2 + (n - 1) + 1) ((n - 1) ^ 2) h_den_pos h_cop
  dsimp
  push_cast at h_num_den
  rw [h_num_den.1, h_num_den.2]
  push_cast
  omega

theorem nat_dvd_sub {a b c : ℕ} (h : c ≤ b) (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ b - c := by
  rcases h1 with ⟨x, rfl⟩
  rcases h2 with ⟨y, rfl⟩
  use x - y
  rw [← Nat.mul_sub_left_distrib]

theorem sigma_one_mul_coprime (a b : ℕ) (h : Coprime a b) :
    sigma 1 (a * b) = sigma 1 a * sigma 1 b := by
  exact isMultiplicative_sigma.map_mul_of_coprime h

theorem coprime_three_n_minus_one_two_n_minus_three (n : ℕ) (hn : 3 < n) (hp : (2 * n - 3).Prime) :
    Coprime (3 * (n - 1)) (2 * n - 3) := by
  have h_gcd_dvd_left : Nat.gcd (3 * (n - 1)) (2 * n - 3) ∣ 3 * (n - 1) := Nat.gcd_dvd_left _ _
  have h_gcd_dvd_right : Nat.gcd (3 * (n - 1)) (2 * n - 3) ∣ (2 * n - 3) := Nat.gcd_dvd_right _ _
  have h_dvd_mul_left : Nat.gcd (3 * (n - 1)) (2 * n - 3) ∣ 2 * (3 * (n - 1)) := dvd_mul_of_dvd_right h_gcd_dvd_left _
  have h_dvd_mul_right : Nat.gcd (3 * (n - 1)) (2 * n - 3) ∣ 3 * (2 * n - 3) := dvd_mul_of_dvd_right h_gcd_dvd_right _
  have h_le : 3 * (2 * n - 3) ≤ 2 * (3 * (n - 1)) := by omega
  have h_sub : 2 * (3 * (n - 1)) - 3 * (2 * n - 3) = 3 := by omega
  have h_gcd_dvd_sub : Nat.gcd (3 * (n - 1)) (2 * n - 3) ∣ 2 * (3 * (n - 1)) - 3 * (2 * n - 3) :=
    nat_dvd_sub h_le h_dvd_mul_left h_dvd_mul_right
  have h_gcd_dvd_three : Nat.gcd (3 * (n - 1)) (2 * n - 3) ∣ 3 := by
    rwa [h_sub] at h_gcd_dvd_sub
  have h_prime_three : (3 : ℕ).Prime := by decide
  rcases (Nat.dvd_prime h_prime_three).mp h_gcd_dvd_three with h_one | h_three
  · exact h_one
  · have h_three_dvd : 3 ∣ 2 * n - 3 := by
      rw [h_three] at h_gcd_dvd_right
      exact h_gcd_dvd_right
    have h_prime_two_n_three : (2 * n - 3).Prime := hp
    rcases (Nat.dvd_prime h_prime_two_n_three).mp h_three_dvd with h_three_one | h_three_eq
    · contradiction
    · have : 2 * n - 3 > 3 := by omega
      omega

theorem prime_two_case (n : ℕ) (hn : 3 < n) (hp : (2 * n - 3).Prime) :
    A243473_val (2 * (2 * n - 3)) = n := by
  unfold A243473_val
  have h_two_ne : (2 : ℕ) ≠ 0 := by decide
  have h_prime_two_n_three : (2 * n - 3).Prime := hp
  have h_prime_ne_zero : (2 * n - 3) ≠ 0 := by
    exact Nat.ne_of_gt (Nat.Prime.pos hp)
  have hi_ne_zero : 2 * (2 * n - 3) ≠ 0 := Nat.mul_ne_zero h_two_ne h_prime_ne_zero
  rw [if_neg hi_ne_zero]
  have h_cop_two : Coprime 2 (2 * n - 3) := by
    have h_prime_two_n_three_gt_two : 2 < 2 * n - 3 := by omega
    have h_cop : Coprime (2 * n - 3) 2 := by
      exact Nat.Prime.coprime_iff_not_dvd hp |>.mpr (fun hd => by
        have : 2 * n - 3 ∣ 2 := hd
        have := Nat.le_of_dvd (by decide) this
        omega)
    exact h_cop.symm
  have h_sigma_two : sigma 1 2 = 3 := by rfl
  have h_sigma_prime : sigma 1 (2 * n - 3) = 2 * n - 2 := by
    rw [sigma_apply, Nat.Prime.divisors hp]
    have h_ne : 1 ≠ 2 * n - 3 := by omega
    have h_not_mem : 1 ∉ ({2 * n - 3} : Finset ℕ) := by
      simp; omega
    rw [Finset.sum_insert h_not_mem]
    simp
    omega
  have h_sigma_mul : sigma 1 (2 * (2 * n - 3)) = 6 * (n - 1) := by
    rw [sigma_one_mul_coprime 2 (2 * n - 3) h_cop_two]
    rw [h_sigma_two, h_sigma_prime]
    omega
  have h_le_n : 1 ≤ n := by omega
  have h_le_2n : 3 ≤ 2 * n := by omega
  have h_rat_div : (sigma 1 (2 * (2 * n - 3)) : ℤ) /. (2 * (2 * n - 3) : ℤ) = (3 * (n - 1) : ℤ) /. (2 * n - 3 : ℤ) := by
    have h_num_eq : (sigma 1 (2 * (2 * n - 3)) : ℤ) = (3 * (n - 1) : ℤ) * 2 := by
      rw [h_sigma_mul]
      push_cast [h_le_n]
      ring
    have h_den_eq : (2 * (2 * n - 3) : ℤ) = (2 * n - 3 : ℤ) * 2 := by
      push_cast [h_le_2n]
      ring
    rw [h_num_eq, h_den_eq]
    exact Rat.divInt_mul_right (by decide : (2 : ℤ) ≠ 0)
  have h_div_eq_goal := nat_div_eq_divInt (sigma 1 (2 * (2 * n - 3))) (2 * (2 * n - 3))
  rw [h_div_eq_goal]
  push_cast [h_le_n, h_le_2n]
  rw [h_rat_div]
  have h_cop_three_n : Coprime (3 * (n - 1)) (2 * n - 3) := coprime_three_n_minus_one_two_n_minus_three n hn hp

  have h_den_pos : 0 < 2 * n - 3 := by omega
  have h_num_den := coprime_num_den (3 * (n - 1)) (2 * n - 3) h_den_pos h_cop_three_n
  push_cast [h_le_n, h_le_2n] at h_num_den
  rw [h_num_den.1, h_num_den.2]
  push_cast [h_le_n, h_le_2n]
  omega

theorem coprime_four_n_minus_one_three_n_minus_four (n : ℕ) (hn : 4 < n) (hp : (3 * n - 4).Prime) :
    Coprime (4 * (n - 1)) (3 * n - 4) := by
  have h_gcd_dvd_left : Nat.gcd (4 * (n - 1)) (3 * n - 4) ∣ 4 * (n - 1) := Nat.gcd_dvd_left _ _
  have h_gcd_dvd_right : Nat.gcd (4 * (n - 1)) (3 * n - 4) ∣ (3 * n - 4) := Nat.gcd_dvd_right _ _
  have h_dvd_mul_left : Nat.gcd (4 * (n - 1)) (3 * n - 4) ∣ 3 * (4 * (n - 1)) := dvd_mul_of_dvd_right h_gcd_dvd_left _
  have h_dvd_mul_right : Nat.gcd (4 * (n - 1)) (3 * n - 4) ∣ 4 * (3 * n - 4) := dvd_mul_of_dvd_right h_gcd_dvd_right _
  have h_le_sub : 4 * (3 * n - 4) ≤ 3 * (4 * (n - 1)) := by omega
  have h_sub : 3 * (4 * (n - 1)) - 4 * (3 * n - 4) = 4 := by omega
  have h_gcd_dvd_sub : Nat.gcd (4 * (n - 1)) (3 * n - 4) ∣ 3 * (4 * (n - 1)) - 4 * (3 * n - 4) := by
    apply nat_dvd_sub h_le_sub h_dvd_mul_left h_dvd_mul_right
  have h_gcd_dvd_four : Nat.gcd (4 * (n - 1)) (3 * n - 4) ∣ 4 := by
    rwa [h_sub] at h_gcd_dvd_sub
  have h_prime_three_n_four : (3 * n - 4).Prime := hp
  have h_odd : ¬ 2 ∣ (3 * n - 4) := by
    intro hd
    have h_eq_two : 3 * n - 4 = 2 := by
      rcases (Nat.dvd_prime h_prime_three_n_four).mp hd with h_two_one | h_two_eq
      · contradiction
      · exact h_two_eq.symm
    omega
  have h_cases : Nat.gcd (4 * (n - 1)) (3 * n - 4) = 1 ∨ Nat.gcd (4 * (n - 1)) (3 * n - 4) = 2 ∨ Nat.gcd (4 * (n - 1)) (3 * n - 4) = 4 := by
    have h_le := Nat.le_of_dvd (by decide) h_gcd_dvd_four
    have h_pos : 0 < Nat.gcd (4 * (n - 1)) (3 * n - 4) := Nat.gcd_pos_of_pos_right _ (by omega)
    interval_cases Nat.gcd (4 * (n - 1)) (3 * n - 4)
    · left; rfl
    · right; left; rfl
    · have h3_not : ¬ 3 ∣ 4 := by decide
      exact absurd h_gcd_dvd_four h3_not
    · right; right; rfl
  rcases h_cases with h1 | h2 | h4
  · exact h1
  · have : 2 ∣ 3 * n - 4 := by
      rw [← h2]
      exact h_gcd_dvd_right
    contradiction
  · have : 2 ∣ 3 * n - 4 := by
      have : 2 ∣ Nat.gcd (4 * (n - 1)) (3 * n - 4) := by
        rw [h4]
        decide
      exact dvd_trans this h_gcd_dvd_right
    contradiction

theorem prime_three_case (n : ℕ) (hn : 4 < n) (hp : (3 * n - 4).Prime) :
    A243473_val (3 * (3 * n - 4)) = n := by
  unfold A243473_val
  have h_three_ne : (3 : ℕ) ≠ 0 := by decide
  have h_prime_three_n_four : (3 * n - 4).Prime := hp
  have h_prime_ne_zero : (3 * n - 4) ≠ 0 := by
    exact Nat.ne_of_gt (Nat.Prime.pos hp)
  have hi_ne_zero : 3 * (3 * n - 4) ≠ 0 := Nat.mul_ne_zero h_three_ne h_prime_ne_zero
  rw [if_neg hi_ne_zero]
  have h_cop_three : Coprime 3 (3 * n - 4) := by
    have h_prime_three_n_four_gt_three : 3 < 3 * n - 4 := by omega
    have h_cop : Coprime (3 * n - 4) 3 := by
      exact Nat.Prime.coprime_iff_not_dvd hp |>.mpr (fun hd => by
        have : 3 * n - 4 ∣ 3 := hd
        have := Nat.le_of_dvd (by decide) this
        omega)
    exact h_cop.symm
  have h_sigma_three : sigma 1 3 = 4 := by rfl
  have h_sigma_prime : sigma 1 (3 * n - 4) = 3 * n - 3 := by
    rw [sigma_apply, Nat.Prime.divisors hp]
    have h_ne : 1 ≠ 3 * n - 4 := by omega
    have h_not_mem : 1 ∉ ({3 * n - 4} : Finset ℕ) := by
      simp; omega
    rw [Finset.sum_insert h_not_mem]
    simp
    omega
  have h_sigma_mul : sigma 1 (3 * (3 * n - 4)) = 12 * (n - 1) := by
    rw [sigma_one_mul_coprime 3 (3 * n - 4) h_cop_three]
    rw [h_sigma_three, h_sigma_prime]
    omega
  have h_le_n : 1 ≤ n := by omega
  have h_le_3n : 4 ≤ 3 * n := by omega
  have h_rat_div : (sigma 1 (3 * (3 * n - 4)) : ℤ) /. (3 * (3 * n - 4) : ℤ) = (4 * (n - 1) : ℤ) /. (3 * n - 4 : ℤ) := by
    have h_num_eq : (sigma 1 (3 * (3 * n - 4)) : ℤ) = (4 * (n - 1) : ℤ) * 3 := by
      rw [h_sigma_mul]
      push_cast [h_le_n]
      ring
    have h_den_eq : (3 * (3 * n - 4) : ℤ) = (3 * n - 4 : ℤ) * 3 := by
      push_cast
      ring
    rw [h_num_eq, h_den_eq]
    exact Rat.divInt_mul_right (by decide : (3 : ℤ) ≠ 0)
  have h_div_eq_goal := nat_div_eq_divInt (sigma 1 (3 * (3 * n - 4))) (3 * (3 * n - 4))
  rw [h_div_eq_goal]
  push_cast [h_le_n, h_le_3n]
  rw [h_rat_div]
  have h_cop_four_n : Coprime (4 * (n - 1)) (3 * n - 4) := coprime_four_n_minus_one_three_n_minus_four n hn hp

  have h_den_pos : 0 < 3 * n - 4 := by omega
  have h_num_den := coprime_num_den (4 * (n - 1)) (3 * n - 4) h_den_pos h_cop_four_n
  push_cast [h_le_n, h_le_3n] at h_num_den
  rw [h_num_den.1, h_num_den.2]
  push_cast [h_le_n, h_le_3n]
  omega

theorem coprime_two_n_minus_one_n_minus_two (n : ℕ) (hn : 5 < n) (hp : (n - 2).Prime) :
    Coprime (2 * (n - 1)) (n - 2) := by
  have h_gcd_dvd_left : Nat.gcd (2 * (n - 1)) (n - 2) ∣ 2 * (n - 1) := Nat.gcd_dvd_left _ _
  have h_gcd_dvd_right : Nat.gcd (2 * (n - 1)) (n - 2) ∣ (n - 2) := Nat.gcd_dvd_right _ _
  have h_dvd_mul_left : Nat.gcd (2 * (n - 1)) (n - 2) ∣ 1 * (2 * (n - 1)) := by
    simp [h_gcd_dvd_left]
  have h_dvd_mul_right : Nat.gcd (2 * (n - 1)) (n - 2) ∣ 2 * (n - 2) := dvd_mul_of_dvd_right h_gcd_dvd_right 2
  have h_le_sub : 2 * (n - 2) ≤ 2 * (n - 1) := by omega
  have h_sub : 2 * (n - 1) - 2 * (n - 2) = 2 := by omega
  have h_gcd_dvd_sub : Nat.gcd (2 * (n - 1)) (n - 2) ∣ 2 * (n - 1) - 2 * (n - 2) := by
    apply nat_dvd_sub h_le_sub h_gcd_dvd_left h_dvd_mul_right
  have h_gcd_dvd_two : Nat.gcd (2 * (n - 1)) (n - 2) ∣ 2 := by
    rwa [h_sub] at h_gcd_dvd_sub
  have h_prime_n_two : (n - 2).Prime := hp
  have h_odd : ¬ 2 ∣ (n - 2) := by
    intro hd
    have h_eq_two : n - 2 = 2 := by
      rcases (Nat.dvd_prime h_prime_n_two).mp hd with h_two_one | h_two_eq
      · contradiction
      · exact h_two_eq.symm
    omega
  have h_cases : Nat.gcd (2 * (n - 1)) (n - 2) = 1 ∨ Nat.gcd (2 * (n - 1)) (n - 2) = 2 := by
    have h_le := Nat.le_of_dvd (by decide) h_gcd_dvd_two
    have h_pos : 0 < Nat.gcd (2 * (n - 1)) (n - 2) := Nat.gcd_pos_of_pos_right _ (by omega)
    interval_cases Nat.gcd (2 * (n - 1)) (n - 2)
    · left; rfl
    · right; rfl
  rcases h_cases with h1 | h2
  · exact h1
  · rw [h2] at h_gcd_dvd_right
    contradiction

theorem prime_six_case (n : ℕ) (hn : 5 < n) (hp : (n - 2).Prime) :
    A243473_val (6 * (n - 2)) = n := by
  unfold A243473_val
  have h_six_ne : (6 : ℕ) ≠ 0 := by decide
  have h_prime_n_two : (n - 2).Prime := hp
  have h_prime_ne_zero : (n - 2) ≠ 0 := by
    exact Nat.ne_of_gt (Nat.Prime.pos hp)
  have hi_ne_zero : 6 * (n - 2) ≠ 0 := Nat.mul_ne_zero h_six_ne h_prime_ne_zero
  rw [if_neg hi_ne_zero]
  have h_cop_six : Coprime 6 (n - 2) := by
    have h_prime_n_two_gt_three : 3 < n - 2 := by
      have h_ne : n ≠ 6 := by
        intro hc
        have : ¬ (n - 2).Prime := by
          subst hc
          decide
        contradiction
      have : n < 6 ∨ n > 6 := Nat.lt_or_gt_of_ne h_ne
      omega
    have h_cop : Coprime (n - 2) 6 := by
      exact Nat.Prime.coprime_iff_not_dvd hp |>.mpr (fun hd => by
        have h_dvd_six : n - 2 ∣ 2 * 3 := hd
        rcases (Nat.Prime.dvd_mul hp).mp h_dvd_six with h_dvd_two | h_dvd_three
        · have h_eq_two : n - 2 = 2 := by
            rcases (Nat.dvd_prime Nat.prime_two).mp h_dvd_two with h_two_one | h_two_eq
            · exfalso
              have : n - 2 ≠ 1 := hp.ne_one
              contradiction
            · exact h_two_eq
          omega
        · have h_eq_three : n - 2 = 3 := by
            rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp h_dvd_three with h_three_one | h_three_eq
            · exfalso
              have : n - 2 ≠ 1 := hp.ne_one
              contradiction
            · exact h_three_eq
          omega)
    exact h_cop.symm
  have h_sigma_six : sigma 1 6 = 12 := by rfl
  have h_sigma_prime : sigma 1 (n - 2) = n - 1 := by
    rw [sigma_apply, Nat.Prime.divisors hp]
    have h_ne : 1 ≠ n - 2 := by omega
    have h_not_mem : 1 ∉ ({n - 2} : Finset ℕ) := by
      simp; omega
    rw [Finset.sum_insert h_not_mem]
    simp
    omega
  have h_sigma_mul : sigma 1 (6 * (n - 2)) = 12 * (n - 1) := by
    rw [sigma_one_mul_coprime 6 (n - 2) h_cop_six]
    rw [h_sigma_six, h_sigma_prime]
  have h_le_n : 1 ≤ n := by omega
  have h_le_6n : 12 ≤ 6 * n := by omega
  have h_rat_div : (sigma 1 (6 * (n - 2)) : ℤ) /. (6 * ↑(n - 2) : ℤ) = (2 * (n - 1) : ℤ) /. (n - 2 : ℤ) := by
    have h_num_eq : (sigma 1 (6 * (n - 2)) : ℤ) = (2 * (n - 1) : ℤ) * 6 := by
      rw [h_sigma_mul]
      push_cast [h_le_n]
      ring
    have h_den_eq : (6 * ↑(n - 2) : ℤ) = (n - 2 : ℤ) * 6 := by
      have : 2 ≤ n := by omega
      push_cast [this]
      ring
    rw [h_num_eq, h_den_eq]
    exact Rat.divInt_mul_right (by decide : (6 : ℤ) ≠ 0)
  have h_div_eq_goal := nat_div_eq_divInt (sigma 1 (6 * (n - 2))) (6 * (n - 2))
  rw [h_div_eq_goal]
  push_cast [h_le_n, h_le_6n]
  rw [h_rat_div]
  have h_cop_two_n : Coprime (2 * (n - 1)) (n - 2) := coprime_two_n_minus_one_n_minus_two n hn hp

  have h_den_pos : 0 < n - 2 := by omega
  have h_num_den := coprime_num_den (2 * (n - 1)) (n - 2) h_den_pos h_cop_two_n
  have h_le_one : 1 ≤ n := by omega
  have h_le_two : 2 ≤ n := by omega
  push_cast [h_le_one, h_le_two] at h_num_den
  rw [h_num_den.1, h_num_den.2]
  push_cast [h_le_one, h_le_two]
  omega

theorem coprime_mul_sub_one (k A : ℕ) (h : 0 < k * A) : Coprime A (k * A - 1) := by
  apply Nat.coprime_of_dvd
  intro d hd1 hd2 hd3
  have hd4 : d ∣ k * A := dvd_mul_of_dvd_right hd2 k
  have h_le : k * A - 1 ≤ k * A := by omega
  have hd5 : d ∣ k * A - (k * A - 1) := nat_dvd_sub h_le hd4 hd3
  have h_sub : k * A - (k * A - 1) = 1 := by omega
  rw [h_sub] at hd5
  have hd6 : d ≤ 1 := Nat.le_of_dvd (by decide) hd5
  have : d > 1 := hd1.one_lt
  omega

theorem coprime_helper_left (n k : ℕ) (hk : Coprime (k + 1) n) (h_pos : 0 < k * (n - 1)) :
    Coprime (k + 1) (k * (n - 1) - 1) := by
  apply Nat.coprime_of_dvd
  intro d hd1 hd2 hd3
  have hd4 : d ∣ (k + 1) * (n - 1) := dvd_mul_of_dvd_left hd2 (n - 1)
  have h_eq : (k + 1) * (n - 1) = k * (n - 1) + (n - 1) := by ring
  rw [h_eq] at hd4
  have h_le : k * (n - 1) - 1 ≤ k * (n - 1) + (n - 1) := by omega
  have hd5 : d ∣ (k * (n - 1) + (n - 1)) - (k * (n - 1) - 1) := nat_dvd_sub h_le hd4 hd3
  have hn_gt : n - 1 ≥ 1 := by
    by_contra hc
    have : n - 1 = 0 := by omega
    have h_pos_rewrite := h_pos
    rw [this] at h_pos_rewrite
    simp at h_pos_rewrite
  have hn_eq : n = (n - 1) + 1 := by omega
  have h_sub : (k * (n - 1) + (n - 1)) - (k * (n - 1) - 1) = n := by omega
  rw [h_sub] at hd5
  have hd6 : d ∣ Nat.gcd (k + 1) n := Nat.dvd_gcd hd2 hd5
  have h_gcd_eq : Nat.gcd (k + 1) n = 1 := hk
  rw [h_gcd_eq] at hd6
  have hd7 : d ≤ 1 := Nat.le_of_dvd (by decide) hd6
  have : d > 1 := hd1.one_lt
  omega

theorem coprime_helper (n k : ℕ) (hk : Coprime (k + 1) n) (h_pos : 0 < k * (n - 1)) :
    Coprime ((k + 1) * (n - 1)) (k * (n - 1) - 1) := by
  have hc1 : Coprime (n - 1) (k * (n - 1) - 1) := coprime_mul_sub_one k (n - 1) h_pos
  have hc2 : Coprime (k + 1) (k * (n - 1) - 1) := coprime_helper_left n k hk h_pos
  exact Nat.Coprime.mul_left hc2 hc1

theorem prime_k_case (n : ℕ) (k : ℕ) (hk : k.Prime) (hn : 2 < n) (hk_cop : Coprime (k + 1) n) (hp : (k * (n - 1) - 1).Prime) (h_cop : Coprime k (k * (n - 1) - 1)) :
    A243473_val (k * (k * (n - 1) - 1)) = n := by
  unfold A243473_val
  have hk_pos : 0 < k := hk.pos
  have hk_ge : 2 ≤ k := hk.two_le
  have h_p_pos : 0 < k * (n - 1) - 1 := hp.pos
  have hi_ne_zero : k * (k * (n - 1) - 1) ≠ 0 := Nat.mul_ne_zero hk_pos.ne' h_p_pos.ne'
  rw [if_neg hi_ne_zero]
  have h_sigma_k : sigma 1 k = k + 1 := by
    rw [sigma_apply, Nat.Prime.divisors hk]
    have h_ne : 1 ≠ k := hk.ne_one.symm
    have h_not_mem : 1 ∉ ({k} : Finset ℕ) := by
      simp; exact h_ne
    rw [Finset.sum_insert h_not_mem]
    simp; omega
  have h_sigma_p : sigma 1 (k * (n - 1) - 1) = k * (n - 1) := by
    rw [sigma_apply, Nat.Prime.divisors hp]
    have h_ne : 1 ≠ k * (n - 1) - 1 := by
      have : n - 1 ≥ 2 := by omega
      have : k * (n - 1) ≥ 4 := Nat.mul_le_mul hk_ge (by omega)
      omega
    have h_not_mem : 1 ∉ ({k * (n - 1) - 1} : Finset ℕ) := by
      simp; exact h_ne
    rw [Finset.sum_insert h_not_mem]
    simp; omega
  have h_sigma_mul : sigma 1 (k * (k * (n - 1) - 1)) = (k + 1) * (k * (n - 1)) := by
    rw [sigma_one_mul_coprime k (k * (n - 1) - 1) h_cop]
    rw [h_sigma_k, h_sigma_p]
  have h_le_n : 1 ≤ n := by omega
  have h_le_kn : 1 ≤ k * (n - 1) := by omega
  have h_rat_div : (sigma 1 (k * (k * (n - 1) - 1)) : ℤ) /. (k * (k * (n - 1) - 1) : ℤ) = ((k + 1) * (n - 1) : ℤ) /. (k * (n - 1) - 1 : ℤ) := by
    have h_num_eq : (sigma 1 (k * (k * (n - 1) - 1)) : ℤ) = ((k + 1) * (n - 1) : ℤ) * k := by
      rw [h_sigma_mul]
      push_cast [h_le_n, h_le_kn]
      ring
    have h_den_eq : (k * (k * (n - 1) - 1) : ℤ) = (k * (n - 1) - 1 : ℤ) * (k : ℤ) := by
      push_cast [h_le_n, h_le_kn]
      ring
    rw [h_num_eq, h_den_eq]
    exact Rat.divInt_mul_right (by omega : (k : ℤ) ≠ 0)
  have h_div_eq_goal := nat_div_eq_divInt (sigma 1 (k * (k * (n - 1) - 1))) (k * (k * (n - 1) - 1))
  rw [h_div_eq_goal]
  push_cast [h_le_n, h_le_kn]
  rw [h_rat_div]
  have h_pos : 0 < k * (n - 1) := by
    have : 0 < n - 1 := by omega
    exact Nat.mul_pos hk_pos this
  have h_cop_num_den : Coprime ((k + 1) * (n - 1)) (k * (n - 1) - 1) := coprime_helper n k hk_cop h_pos
  have h_den_pos' : 0 < k * (n - 1) - 1 := h_p_pos
  have h_num_den := coprime_num_den ((k + 1) * (n - 1)) (k * (n - 1) - 1) h_den_pos' h_cop_num_den
  push_cast [h_le_n, h_le_kn] at h_num_den
  rw [h_num_den.1, h_num_den.2]
  push_cast [h_le_n, h_le_kn]
  have h_ring : ((k : ℤ) + 1) * ((n : ℤ) - 1) - ((k : ℤ) * ((n : ℤ) - 1) - 1) = (n : ℤ) := by ring
  rw [h_ring]
  simp


theorem composite_g_case (n : ℕ) (g : ℕ) (hg_pos : 0 < g) (hn : 2 < n) :
    let d := Nat.gcd (sigma 1 g) g
    let val := (sigma 1 g - g) / d
    let b := g / d
    let a := sigma 1 g / d
    let k := (n - 1) / val
    let P := k * b - 1
    (h_val_dvd : val ∣ n - 1) →
    (h_P_prime : P.Prime) →
    (h_P_not_dvd_g : ¬ P ∣ g) →
    (h_cop : Coprime (k * a) P) →
    A243473_val (g * P) = n := by
  intro d val b a k P h_val_dvd h_P_prime h_P_not_dvd_g h_cop
  unfold A243473_val
  have hP_pos : 0 < P := h_P_prime.pos
  have hP_ge_two : 2 ≤ P := h_P_prime.two_le
  have hg_ne_zero : g ≠ 0 := hg_pos.ne'
  have hP_ne_zero : P ≠ 0 := hP_pos.ne'
  have hgP_ne_zero : g * P ≠ 0 := mul_ne_zero hg_ne_zero hP_ne_zero
  rw [if_neg hgP_ne_zero]
  have h_cop_gP : Coprime g P := Nat.Coprime.symm (h_P_prime.coprime_iff_not_dvd.mpr h_P_not_dvd_g)
  have h_sigma_gP : sigma 1 (g * P) = sigma 1 g * (P + 1) := by
    rw [sigma_one_mul_coprime g P h_cop_gP]
    have h_sigma_P : sigma 1 P = P + 1 := by
      rw [sigma_apply, Nat.Prime.divisors h_P_prime]
      have h_ne : 1 ≠ P := h_P_prime.ne_one.symm
      have h_not_mem : 1 ∉ ({P} : Finset ℕ) := by
        simp; exact h_ne
      rw [Finset.sum_insert h_not_mem]
      simp; omega
    rw [h_sigma_P]
  have hd_dvd_g : d ∣ g := Nat.gcd_dvd_right (sigma 1 g) g
  have hd_dvd_sig : d ∣ sigma 1 g := Nat.gcd_dvd_left (sigma 1 g) g
  have hd_pos : 0 < d := Nat.gcd_pos_of_pos_right (sigma 1 g) hg_pos
  have h_g_eq : g = d * b := (Nat.mul_div_cancel' hd_dvd_g).symm
  have h_sig_eq : sigma 1 g = d * a := (Nat.mul_div_cancel' hd_dvd_sig).symm
  have h_kb_pos : 0 < k * b := by
    have : 2 ≤ k * b - 1 := hP_ge_two
    omega
  have h_P_add_one : P + 1 = k * b := by
    have : P = k * b - 1 := rfl
    omega
  have h_sig_gP_val : sigma 1 (g * P) = d * a * (k * b) := by
    rw [h_sigma_gP, h_sig_eq, h_P_add_one]
  have h_gP_val : g * P = d * b * P := by
    rw [h_g_eq, mul_assoc]
  have h_rat_eq : ((sigma 1 (g * P) : Rat) / (g * P : Rat)) = ((k * a : Rat) / (P : Rat)) := by
    have h1 : (sigma 1 (g * P) : Rat) = (a * k * g : Rat) := by
      have : sigma 1 (g * P) = a * k * g := by
        rw [h_sig_gP_val, h_g_eq]
        ring
      rw [this]
      push_cast
      rfl
    have h2 : (g * P : Rat) = (P * g : Rat) := by
      push_cast
      ring
    rw [h1, h2]
    have h_g_ne : (g : Rat) ≠ 0 := cast_ne_zero.mpr hg_ne_zero
    rw [mul_div_mul_right _ _ h_g_ne]
    ring
  have h_gP_cast : ((g * P : ℕ) : Rat) = (g : Rat) * (P : Rat) := by push_cast; rfl
  rw [h_gP_cast]
  rw [h_rat_eq]
  have h_fold : (k * a : Rat) / (P : Rat) = ((k * a : ℕ) : Rat) / ((P : ℕ) : Rat) := by
    push_cast
    rfl
  rw [h_fold]
  rw [nat_div_eq_divInt]
  dsimp only
  have h_num_den := coprime_num_den (k * a) P hP_pos h_cop
  rw [h_num_den.1, h_num_den.2]
  push_cast
  have h_a_sub_b : (a : ℤ) - (b : ℤ) = (val : ℤ) := by
    have h_sig_sub_g : sigma 1 g - g = d * val := by
      have : (sigma 1 g - g) / d = val := rfl
      have hd_dvd_sub : d ∣ sigma 1 g - g := by
        apply Nat.dvd_sub
        · exact hd_dvd_sig
        · exact hd_dvd_g
      exact (Nat.mul_div_cancel' hd_dvd_sub).symm
    have h_ring : (sigma 1 g : ℤ) - (g : ℤ) = ((sigma 1 g - g) : ℕ) := by
      have h_mem : g ∈ divisors g := by
        rw [mem_divisors]
        refine ⟨dvd_rfl, hg_pos.ne'⟩
      have h_le : g ≤ sigma 1 g := by
        rw [sigma_one_apply]
        apply Finset.single_le_sum (fun a _ => zero_le a) h_mem
      omega
    have h_ring2 : (sigma 1 g : ℤ) - (g : ℤ) = (d * a : ℤ) - (d * b : ℤ) := by
      rw [h_sig_eq, h_g_eq]
      push_cast
      rfl
    rw [h_ring2, ← mul_sub_left_distrib] at h_ring
    rw [h_sig_sub_g] at h_ring
    push_cast at h_ring
    have hd_ne_zero : (d : ℤ) ≠ 0 := by
      exact cast_ne_zero.mpr hd_pos.ne'
    exact mul_left_cancel₀ hd_ne_zero h_ring
  have h_final : (k * a : ℤ) - (P : ℤ) = (n : ℤ) := by
    have hP_def : (P : ℤ) = (k * b : ℤ) - 1 := by
      have : P = k * b - 1 := rfl
      omega
    rw [hP_def]
    have h_ring3 : (k * a : ℤ) - ((k * b : ℤ) - 1) = (k : ℤ) * ((a : ℤ) - (b : ℤ)) + 1 := by ring
    rw [h_ring3, h_a_sub_b]
    have h_kv_eq : (k * val : ℕ) = n - 1 := Nat.div_mul_cancel h_val_dvd
    have h_kv_eq_z : (k : ℤ) * (val : ℤ) = (n : ℤ) - 1 := by
      push_cast
      omega
    rw [h_kv_eq_z]
    omega
  rw [h_final]
  rfl


/--
Motivated by the observation that some small numbers (2,12,14,18,...) occur only very late
in the recently added sequence A243473, but all numbers seem to appear sooner or later.
(The definition is completed by "0 if no such index exists" to guarantee well-definedness
in absence of a proof, but I conjecture that no such 0 will ever occur.)
The conjecture is that the sequence $\mathrm{A243473\_val}$ is eventually surjective onto $\mathbb{N} \setminus \{0, 1\}$.
-/
theorem oeis_243512_conjecture_0 (n : ℕ) : a n ≠ 0 := by
  apply a_ne_zero_of_nonempty
  by_cases hn0 : n = 0
  · rw [hn0]
    use 1
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h1 : ¬ 1 = 0 := by decide
    rw [if_neg h1]
    rw [sigma_apply]
    rw [Nat.divisors_one]
    simp
  by_cases hn1 : n = 1
  · rw [hn1]
    use 2
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h1 : ¬ 2 = 0 := by decide
    rw [if_neg h1]
    rw [sigma_apply]
    have h_prime : Nat.Prime 2 := Nat.prime_two
    rw [Nat.Prime.divisors h_prime]
    simp
    norm_num
    rfl
  by_cases hn2 : n = 2
  · rw [hn2]
    use 120
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h1 : ¬ 120 = 0 := by decide
    rw [if_neg h1]
    have h_sig : sigma 1 120 = 360 := by rfl
    rw [h_sig]
    norm_num
    rfl
  by_cases hp : (n - 1).Prime
  · use (n - 1) ^ 2
    have hp_pos : 0 < n - 1 := by omega
    have h_den_pos : 0 < (n - 1) ^ 2 := by
      apply Nat.pow_pos
      exact hp_pos
    refine ⟨h_den_pos, ?_⟩
    exact prime_square_case n (by omega) hp
  by_cases hp2 : (2 * n - 3).Prime
  · use 2 * (2 * n - 3)
    have : 3 < n := by
      by_contra hc
      have : n = 3 := by omega
      subst this
      have : (3 - 1).Prime := by decide
      contradiction
    have h_den_pos : 0 < 2 * (2 * n - 3) := by omega
    refine ⟨h_den_pos, ?_⟩
    exact prime_two_case n (by omega) hp2
  by_cases hp3 : (3 * n - 4).Prime
  · use 3 * (3 * n - 4)
    have : 4 < n := by
      by_contra hc
      have h_cases : n = 3 ∨ n = 4 := by omega
      rcases h_cases with rfl | rfl
      · have : (3 - 1).Prime := by decide
        contradiction
      · have : (4 - 1).Prime := by decide
        contradiction
    have h_den_pos : 0 < 3 * (3 * n - 4) := by omega
    refine ⟨h_den_pos, ?_⟩
    exact prime_three_case n (by omega) hp3
  by_cases hp6 : (n - 2).Prime
  · use 6 * (n - 2)
    have : 5 < n := by
      by_contra hc
      have h_cases : n = 3 ∨ n = 4 ∨ n = 5 := by omega
      rcases h_cases with rfl | rfl | rfl
      · have : (3 - 1).Prime := by decide
        contradiction
      · have : (4 - 1).Prime := by decide
        contradiction
      · have : (2 * 5 - 3).Prime := by decide
        contradiction
    have h_den_pos : 0 < 6 * (n - 2) := by omega
    refine ⟨h_den_pos, ?_⟩
    exact prime_six_case n (by omega) hp6
  by_cases hn26 : n = 26
  · rw [hn26]
    use 760
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h_ne : ¬ 760 = 0 := by decide
    rw [if_neg h_ne]
    have h_sig : sigma 1 760 = 1800 := by
      have h_dec : 760 = 8 * (5 * 19) := by rfl
      have h_cop1 : Coprime 8 (5 * 19) := by decide
      have h_cop2 : Coprime 5 19 := by decide
      rw [h_dec]
      rw [sigma_one_mul_coprime 8 (5 * 19) h_cop1]
      rw [sigma_one_mul_coprime 5 19 h_cop2]
      have h8 : sigma 1 8 = 15 := by rfl
      have h5 : sigma 1 5 = 6 := by rfl
      have h19 : sigma 1 19 = 20 := by rfl
      rw [h8, h5, h19]
    rw [h_sig]
    norm_num
    rfl
  by_cases hn27 : n = 27
  · rw [hn27]
    use 133
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h_ne : ¬ 133 = 0 := by decide
    rw [if_neg h_ne]
    have h_sig : sigma 1 133 = 160 := by
      have h_dec : 133 = 7 * 19 := by rfl
      have h_cop : Coprime 7 19 := by decide
      rw [h_dec]
      rw [sigma_one_mul_coprime 7 19 h_cop]
      have h7 : sigma 1 7 = 8 := by rfl
      have h19 : sigma 1 19 = 20 := by rfl
      rw [h7, h19]
    rw [h_sig]
    norm_num
    rfl
  by_cases hn34 : n = 34
  · rw [hn34]
    use 172
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h_ne : ¬ 172 = 0 := by decide
    rw [if_neg h_ne]
    have h_sig : sigma 1 172 = 308 := by
      have h_dec : 172 = 4 * 43 := by rfl
      have h_cop : Coprime 4 43 := by decide
      rw [h_dec]
      rw [sigma_one_mul_coprime 4 43 h_cop]
      have h4 : sigma 1 4 = 7 := by rfl
      have h43 : sigma 1 43 = 44 := by rfl
      rw [h4, h43]
    rw [h_sig]
    norm_num
    rfl
  by_cases hn36 : n = 36
  · rw [hn36]
    use 522
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h_ne : ¬ 522 = 0 := by decide
    rw [if_neg h_ne]
    have h_sig : sigma 1 522 = 1170 := by
      have h_dec : 522 = 2 * (9 * 29) := by rfl
      have h_cop1 : Coprime 2 (9 * 29) := by decide
      have h_cop2 : Coprime 9 29 := by decide
      rw [h_dec]
      rw [sigma_one_mul_coprime 2 (9 * 29) h_cop1]
      rw [sigma_one_mul_coprime 9 29 h_cop2]
      have h2 : sigma 1 2 = 3 := by rfl
      have h9 : sigma 1 9 = 13 := by rfl
      have h29 : sigma 1 29 = 30 := by rfl
      rw [h2, h9, h29]
    rw [h_sig]
    norm_num
    rfl
  by_cases hn40 : n = 40
  · rw [hn40]
    use 81
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h_ne : ¬ 81 = 0 := by decide
    rw [if_neg h_ne]
    have h_sig : sigma 1 81 = 121 := by rfl
    rw [h_sig]
    norm_num
    rfl
  by_cases hn64 : n = 64
  · rw [hn64]
    use 332
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h_ne : ¬ 332 = 0 := by decide
    rw [if_neg h_ne]
    have h_sig : sigma 1 332 = 588 := by
      have h_dec : 332 = 4 * 83 := by rfl
      have h_cop : Coprime 4 83 := by decide
      rw [h_dec]
      rw [sigma_one_mul_coprime 4 83 h_cop]
      have h4 : sigma 1 4 = 7 := by rfl
      have h83 : sigma 1 83 = 84 := by rfl
      rw [h4, h83]
    rw [h_sig]
    norm_num
    rfl
  by_cases hn66 : n = 66
  · rw [hn66]
    use 108000
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h_ne : ¬ 108000 = 0 := by decide
    rw [if_neg h_ne]
    have h_sig : sigma 1 108000 = 393120 := by
      have h_dec : 108000 = 32 * (27 * 125) := by rfl
      have h_cop1 : Coprime 32 (27 * 125) := by decide
      have h_cop2 : Coprime 27 125 := by decide
      rw [h_dec]
      rw [sigma_one_mul_coprime 32 (27 * 125) h_cop1]
      rw [sigma_one_mul_coprime 27 125 h_cop2]
      have h32 : sigma 1 32 = 63 := by rfl
      have h27 : sigma 1 27 = 40 := by rfl
      have h125 : sigma 1 125 = 156 := by rfl
      rw [h32, h27, h125]
    rw [h_sig]
    norm_num
    rfl
  by_cases hn78 : n = 78
  · rw [hn78]
    use 2047488
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h_ne : ¬ 2047488 = 0 := by decide
    rw [if_neg h_ne]
    have h_sig : sigma 1 2047488 = 5761536 := by
      have h_dec : 2047488 = 512 * (3 * (31 * 43)) := by rfl
      have h_cop1 : Coprime 512 (3 * (31 * 43)) := by decide
      have h_cop2 : Coprime 3 (31 * 43) := by decide
      have h_cop3 : Coprime 31 43 := by decide
      rw [h_dec]
      rw [sigma_one_mul_coprime 512 (3 * (31 * 43)) h_cop1]
      rw [sigma_one_mul_coprime 3 (31 * 43) h_cop2]
      rw [sigma_one_mul_coprime 31 43 h_cop3]
      have h512 : sigma 1 512 = 1023 := by rfl
      have h3 : sigma 1 3 = 4 := by rfl
      have h31 : sigma 1 31 = 32 := by rfl
      have h43 : sigma 1 43 = 44 := by rfl
      rw [h512, h3, h31, h43]
    rw [h_sig]
    norm_num
    rfl
  by_cases hn82 : n = 82
  · rw [hn82]
    use 260
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h_ne : ¬ 260 = 0 := by decide
    rw [if_neg h_ne]
    have h_sig : sigma 1 260 = 588 := by
      have h_dec : 260 = 4 * (5 * 13) := by rfl
      have h_cop1 : Coprime 4 (5 * 13) := by decide
      have h_cop2 : Coprime 5 13 := by decide
      rw [h_dec]
      rw [sigma_one_mul_coprime 4 (5 * 13) h_cop1]
      rw [sigma_one_mul_coprime 5 13 h_cop2]
      have h4 : sigma 1 4 = 7 := by rfl
      have h5 : sigma 1 5 = 6 := by rfl
      have h13 : sigma 1 13 = 14 := by rfl
      rw [h4, h5, h13]
    rw [h_sig]
    norm_num
    rfl
  by_cases hn86 : n = 86
  · rw [hn86]
    use 2680
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h_ne : ¬ 2680 = 0 := by decide
    rw [if_neg h_ne]
    have h_sig : sigma 1 2680 = 6120 := by
      have h_dec : 2680 = 8 * (5 * 67) := by rfl
      have h_cop1 : Coprime 8 (5 * 67) := by decide
      have h_cop2 : Coprime 5 67 := by decide
      rw [h_dec]
      rw [sigma_one_mul_coprime 8 (5 * 67) h_cop1]
      rw [sigma_one_mul_coprime 5 67 h_cop2]
      have h8 : sigma 1 8 = 15 := by rfl
      have h5 : sigma 1 5 = 6 := by rfl
      have h67 : sigma 1 67 = 68 := by rfl
      rw [h8, h5, h67]
    rw [h_sig]
    norm_num
    rfl
  by_cases hn93 : n = 93
  · rw [hn93]
    use 1027
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h_ne : ¬ 1027 = 0 := by decide
    rw [if_neg h_ne]
    have h_sig : sigma 1 1027 = 1120 := by
      have h_dec : 1027 = 13 * 79 := by rfl
      have h_cop : Coprime 13 79 := by decide
      rw [h_dec]
      rw [sigma_one_mul_coprime 13 79 h_cop]
      have h13 : sigma 1 13 = 14 := by rfl
      have h79 : sigma 1 79 = 80 := by rfl
      rw [h13, h79]
    rw [h_sig]
    norm_num
    rfl
  by_cases hn94 : n = 94
  · rw [hn94]
    use 1464
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h_ne : ¬ 1464 = 0 := by decide
    rw [if_neg h_ne]
    have h_sig : sigma 1 1464 = 3720 := by
      have h_dec : 1464 = 8 * (3 * 61) := by rfl
      have h_cop1 : Coprime 8 (3 * 61) := by decide
      have h_cop2 : Coprime 3 61 := by decide
      rw [h_dec]
      rw [sigma_one_mul_coprime 8 (3 * 61) h_cop1]
      rw [sigma_one_mul_coprime 3 61 h_cop2]
      have h8 : sigma 1 8 = 15 := by rfl
      have h3 : sigma 1 3 = 4 := by rfl
      have h61 : sigma 1 61 = 62 := by rfl
      rw [h8, h3, h61]
    rw [h_sig]
    norm_num
    rfl
  by_cases hn96 : n = 96
  · rw [hn96]
    use 2832
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h_ne : ¬ 2832 = 0 := by decide
    rw [if_neg h_ne]
    have h_sig : sigma 1 2832 = 7440 := by
      have h_dec : 2832 = 16 * (3 * 59) := by rfl
      have h_cop1 : Coprime 16 (3 * 59) := by decide
      have h_cop2 : Coprime 3 59 := by decide
      rw [h_dec]
      rw [sigma_one_mul_coprime 16 (3 * 59) h_cop1]
      rw [sigma_one_mul_coprime 3 59 h_cop2]
      have h16 : sigma 1 16 = 31 := by rfl
      have h3 : sigma 1 3 = 4 := by rfl
      have h59 : sigma 1 59 = 60 := by rfl
      rw [h16, h3, h59]
    rw [h_sig]
    norm_num
    rfl
  by_cases hn106 : n = 106
  · rw [hn106]
    use 556
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h_ne : ¬ 556 = 0 := by decide
    rw [if_neg h_ne]
    have h_sig : sigma 1 556 = 980 := by
      have h_dec : 556 = 4 * 139 := by rfl
      have h_cop1 : Coprime 4 (139) := by decide
      rw [h_dec]
      rw [sigma_one_mul_coprime 4 _ h_cop1]
      have h_sig4 : sigma 1 4 = 7 := by rfl
      have h_sig139 : sigma 1 139 = 140 := by rfl
      rw [h_sig4, h_sig139]
    rw [h_sig]
    norm_num
    rfl
  by_cases hn112 : n = 112
  · rw [hn112]
    use 1752
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h_ne : ¬ 1752 = 0 := by decide
    rw [if_neg h_ne]
    have h_sig : sigma 1 1752 = 4440 := by
      have h_dec : 1752 = 3 * (8 * 73) := by rfl
      have h_cop1 : Coprime 3 (8 * 73) := by decide
      have h_cop2 : Coprime 8 (73) := by decide
      rw [h_dec]
      rw [sigma_one_mul_coprime 3 _ h_cop1]
      rw [sigma_one_mul_coprime 8 _ h_cop2]
      have h_sig3 : sigma 1 3 = 4 := by rfl
      have h_sig8 : sigma 1 8 = 15 := by rfl
      have h_sig73 : sigma 1 73 = 74 := by rfl
      rw [h_sig3, h_sig8, h_sig73]
    rw [h_sig]
    norm_num
    rfl
  by_cases hn120 : n = 120
  · rw [hn120]
    use 1818
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h_ne : ¬ 1818 = 0 := by decide
    rw [if_neg h_ne]
    have h_sig : sigma 1 1818 = 3978 := by
      have h_dec : 1818 = 2 * (9 * 101) := by rfl
      have h_cop1 : Coprime 2 (9 * 101) := by decide
      have h_cop2 : Coprime 9 (101) := by decide
      rw [h_dec]
      rw [sigma_one_mul_coprime 2 _ h_cop1]
      rw [sigma_one_mul_coprime 9 _ h_cop2]
      have h2 : sigma 1 2 = 3 := by rfl
      have h9 : sigma 1 9 = 13 := by rfl
      have h101 : sigma 1 101 = 102 := by rfl
      rw [h2, h9, h101]
    rw [h_sig]
    norm_num
    rfl
  by_cases hn123 : n = 123
  · rw [hn123]
    use 1417
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h_ne : ¬ 1417 = 0 := by decide
    rw [if_neg h_ne]
    have h_sig : sigma 1 1417 = 1540 := by
      have h_dec : 1417 = 13 * 109 := by rfl
      have h_cop : Coprime 13 109 := by decide
      rw [h_dec]
      rw [sigma_one_mul_coprime 13 109 h_cop]
      have h13 : sigma 1 13 = 14 := by rfl
      have h109 : sigma 1 109 = 110 := by rfl
      rw [h13, h109]
    rw [h_sig]
    norm_num
    rfl
  by_cases hn124 : n = 124
  · rw [hn124]
    use 652
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h_ne : ¬ 652 = 0 := by decide
    rw [if_neg h_ne]
    have h_sig : sigma 1 652 = 1148 := by
      have h_dec : 652 = 4 * 163 := by rfl
      have h_cop : Coprime 4 163 := by decide
      rw [h_dec]
      rw [sigma_one_mul_coprime 4 163 h_cop]
      have h4 : sigma 1 4 = 7 := by rfl
      have h163 : sigma 1 163 = 164 := by rfl
      rw [h4, h163]
    rw [h_sig]
    norm_num
    rfl
  by_cases hn125 : n = 125
  · rw [hn125]
    use 1243
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h_ne : ¬ 1243 = 0 := by decide
    rw [if_neg h_ne]
    have h_sig : sigma 1 1243 = 1368 := by
      have h_dec : 1243 = 11 * 113 := by rfl
      have h_cop : Coprime 11 113 := by decide
      rw [h_dec]
      rw [sigma_one_mul_coprime 11 113 h_cop]
      have h11 : sigma 1 11 = 12 := by rfl
      have h113 : sigma 1 113 = 114 := by rfl
      rw [h11, h113]
    rw [h_sig]
    norm_num
    rfl
  by_cases hn126 : n = 126
  · rw [hn126]
    use 23154432
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h_ne : ¬ 23154432 = 0 := by decide
    rw [if_neg h_ne]
    have h_sig : sigma 1 23154432 = 72602880 := by
      have h_dec : 23154432 = 256 * (3 * (7 * (59 * 73))) := by rfl
      have h_cop1 : Coprime 256 (3 * (7 * (59 * 73))) := by decide
      have h_cop2 : Coprime 3 (7 * (59 * 73)) := by decide
      have h_cop3 : Coprime 7 (59 * 73) := by decide
      have h_cop4 : Coprime 59 73 := by decide
      rw [h_dec]
      rw [sigma_one_mul_coprime 256 _ h_cop1]
      rw [sigma_one_mul_coprime 3 _ h_cop2]
      rw [sigma_one_mul_coprime 7 _ h_cop3]
      rw [sigma_one_mul_coprime 59 73 h_cop4]
      have h256 : sigma 1 256 = 511 := by rfl
      have h3 : sigma 1 3 = 4 := by rfl
      have h7 : sigma 1 7 = 8 := by rfl
      have h59 : sigma 1 59 = 60 := by rfl
      have h73 : sigma 1 73 = 74 := by rfl
      rw [h256, h3, h7, h59, h73]
    rw [h_sig]
    norm_num
    rfl
  by_cases hn134 : n = 134
  · rw [hn134]
    use 1208
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h_ne : ¬ 1208 = 0 := by decide
    rw [if_neg h_ne]
    have h_sig : sigma 1 1208 = 2280 := by
      have h_dec : 1208 = 8 * 151 := by rfl
      have h_cop : Coprime 8 151 := by decide
      rw [h_dec]
      rw [sigma_one_mul_coprime 8 151 h_cop]
      have h8 : sigma 1 8 = 15 := by rfl
      have h151 : sigma 1 151 = 152 := by rfl
      rw [h8, h151]
    rw [h_sig]
    norm_num
    rfl
  by_cases hn144 : n = 144
  · rw [hn144]
    use 22538880
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h_ne : ¬ 22538880 = 0 := by decide
    rw [if_neg h_ne]
    have h_sig : sigma 1 22538880 = 98017920 := by
      have h_dec : 22538880 = 128 * (5 * (7 * (9 * (13 * 43)))) := by rfl
      have h_cop1 : Coprime 128 (5 * (7 * (9 * (13 * 43)))) := by decide
      have h_cop2 : Coprime 5 (7 * (9 * (13 * 43))) := by decide
      have h_cop3 : Coprime 7 (9 * (13 * 43)) := by decide
      have h_cop4 : Coprime 9 (13 * 43) := by decide
      have h_cop5 : Coprime 13 43 := by decide
      rw [h_dec]
      rw [sigma_one_mul_coprime 128 _ h_cop1]
      rw [sigma_one_mul_coprime 5 _ h_cop2]
      rw [sigma_one_mul_coprime 7 _ h_cop3]
      rw [sigma_one_mul_coprime 9 _ h_cop4]
      rw [sigma_one_mul_coprime 13 43 h_cop5]
      have h128 : sigma 1 128 = 255 := by rfl
      have h5 : sigma 1 5 = 6 := by rfl
      have h7 : sigma 1 7 = 8 := by rfl
      have h9 : sigma 1 9 = 13 := by rfl
      have h13 : sigma 1 13 = 14 := by rfl
      have h43 : sigma 1 43 = 44 := by rfl
      rw [h128, h5, h7, h9, h13, h43]
    rw [h_sig]
    norm_num
    rfl
  by_cases hn146 : n = 146
  · rw [hn146]
    use 27244
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h_ne : ¬ 27244 = 0 := by decide
    rw [if_neg h_ne]
    have h_sig : sigma 1 27244 = 55860 := by
      have h_dec : 27244 = 4 * (49 * 139) := by rfl
      have h_cop1 : Coprime 4 (49 * 139) := by decide
      have h_cop2 : Coprime 49 139 := by decide
      rw [h_dec]
      rw [sigma_one_mul_coprime 4 _ h_cop1]
      rw [sigma_one_mul_coprime 49 139 h_cop2]
      have h4 : sigma 1 4 = 7 := by rfl
      have h49 : sigma 1 49 = 57 := by rfl
      have h139 : sigma 1 139 = 140 := by rfl
      rw [h4, h49, h139]
    rw [h_sig]
    norm_num
    rfl
  by_cases hn147 : n = 147
  · rw [hn147]
    use 1083
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h_ne : ¬ 1083 = 0 := by decide
    rw [if_neg h_ne]
    have h_sig : sigma 1 1083 = 1524 := by
      have h_dec : 1083 = 3 * 361 := by rfl
      have h_cop : Coprime 3 361 := by decide
      rw [h_dec]
      rw [sigma_one_mul_coprime 3 361 h_cop]
      have h3 : sigma 1 3 = 4 := by rfl
      have h361 : sigma 1 361 = 381 := by rfl
      rw [h3, h361]
    rw [h_sig]
    norm_num
    rfl
  by_cases hn154 : n = 154
  · rw [hn154]
    use 2424
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h_ne : ¬ 2424 = 0 := by decide
    rw [if_neg h_ne]
    have h_sig : sigma 1 2424 = 6120 := by
      have h_dec : 2424 = 3 * (8 * 101) := by rfl
      have h_cop1 : Coprime 3 (8 * 101) := by decide
      have h_cop2 : Coprime 8 101 := by decide
      rw [h_dec]
      rw [sigma_one_mul_coprime 3 _ h_cop1]
      rw [sigma_one_mul_coprime 8 101 h_cop2]
      have h3 : sigma 1 3 = 4 := by rfl
      have h8 : sigma 1 8 = 15 := by rfl
      have h101 : sigma 1 101 = 102 := by rfl
      rw [h3, h8, h101]
    rw [h_sig]
    norm_num
    rfl
  by_cases hn156 : n = 156
  · rw [hn156]
    use 625
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h_ne : ¬ 625 = 0 := by decide
    rw [if_neg h_ne]
    have h_sig : sigma 1 625 = 781 := by rfl
    rw [h_sig]
    norm_num
    rfl
  by_cases hn162 : n = 162
  · rw [hn162]
    use 2466
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h_ne : ¬ 2466 = 0 := by decide
    rw [if_neg h_ne]
    have h_sig : sigma 1 2466 = 5382 := by
      have h_dec : 2466 = 2 * (9 * 137) := by rfl
      have h_cop1 : Coprime 2 (9 * 137) := by decide
      have h_cop2 : Coprime 9 137 := by decide
      rw [h_dec]
      rw [sigma_one_mul_coprime 2 _ h_cop1]
      rw [sigma_one_mul_coprime 9 137 h_cop2]
      have h2 : sigma 1 2 = 3 := by rfl
      have h9 : sigma 1 9 = 13 := by rfl
      have h137 : sigma 1 137 = 138 := by rfl
      rw [h2, h9, h137]
    rw [h_sig]
    norm_num
    rfl
  by_cases hn163 : n = 163
  · rw [hn163]
    use 608
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h_ne : ¬ 608 = 0 := by decide
    rw [if_neg h_ne]
    have h_sig : sigma 1 608 = 1260 := by
      have h_dec : 608 = 32 * 19 := by rfl
      have h_cop : Coprime 32 19 := by decide
      rw [h_dec]
      rw [sigma_one_mul_coprime 32 19 h_cop]
      have h32 : sigma 1 32 = 63 := by rfl
      have h19 : sigma 1 19 = 20 := by rfl
      rw [h32, h19]
    rw [h_sig]
    norm_num
    rfl
  by_cases hn166 : n = 166
  · rw [hn166]
    use 2616
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h_ne : ¬ 2616 = 0 := by decide
    rw [if_neg h_ne]
    have h_sig : sigma 1 2616 = 6600 := by
      have h_dec : 2616 = 3 * (8 * 109) := by rfl
      have h_cop1 : Coprime 3 (8 * 109) := by decide
      have h_cop2 : Coprime 8 109 := by decide
      rw [h_dec]
      rw [sigma_one_mul_coprime 3 _ h_cop1]
      rw [sigma_one_mul_coprime 8 109 h_cop2]
      have h3 : sigma 1 3 = 4 := by rfl
      have h8 : sigma 1 8 = 15 := by rfl
      have h109 : sigma 1 109 = 110 := by rfl
      rw [h3, h8, h109]
    rw [h_sig]
    norm_num
    rfl
  by_cases hn172 : n = 172
  · rw [hn172]
    use 908
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h_ne : ¬ 908 = 0 := by decide
    rw [if_neg h_ne]
    have h_sig : sigma 1 908 = 1596 := by
      have h_dec : 908 = 4 * 227 := by rfl
      have h_cop : Coprime 4 227 := by decide
      rw [h_dec]
      rw [sigma_one_mul_coprime 4 227 h_cop]
      have h4 : sigma 1 4 = 7 := by rfl
      have h227 : sigma 1 227 = 228 := by rfl
      rw [h4, h227]
    rw [h_sig]
    norm_num
    rfl
  by_cases hn173 : n = 173
  · rw [hn173]
    use 410
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h_ne : ¬ 410 = 0 := by decide
    rw [if_neg h_ne]
    have h_sig : sigma 1 410 = 756 := by
      have h_dec : 410 = 2 * (5 * 41) := by rfl
      have h_cop1 : Coprime 2 (5 * 41) := by decide
      have h_cop2 : Coprime 5 41 := by decide
      rw [h_dec]
      rw [sigma_one_mul_coprime 2 _ h_cop1]
      rw [sigma_one_mul_coprime 5 41 h_cop2]
      have h2 : sigma 1 2 = 3 := by rfl
      have h5 : sigma 1 5 = 6 := by rfl
      have h41 : sigma 1 41 = 42 := by rfl
      rw [h2, h5, h41]
    rw [h_sig]
    norm_num
    rfl
  by_cases hn177 : n = 177
  · rw [hn177]
    use 1572
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h_ne : ¬ 1572 = 0 := by decide
    rw [if_neg h_ne]
    have h_sig : sigma 1 1572 = 3696 := by
      have h_dec : 1572 = 3 * (4 * 131) := by rfl
      have h_cop1 : Coprime 3 (4 * 131) := by decide
      have h_cop2 : Coprime 4 131 := by decide
      rw [h_dec]
      rw [sigma_one_mul_coprime 3 _ h_cop1]
      rw [sigma_one_mul_coprime 4 131 h_cop2]
      have h3 : sigma 1 3 = 4 := by rfl
      have h4 : sigma 1 4 = 7 := by rfl
      have h131 : sigma 1 131 = 132 := by rfl
      rw [h3, h4, h131]
    rw [h_sig]
    norm_num
    rfl
  by_cases hn179 : n = 179
  · rw [hn179]
    use 506
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h_ne : ¬ 506 = 0 := by decide
    rw [if_neg h_ne]
    have h_sig : sigma 1 506 = 864 := by
      have h_dec : 506 = 2 * (11 * 23) := by rfl
      have h_cop1 : Coprime 2 (11 * 23) := by decide
      have h_cop2 : Coprime 11 23 := by decide
      rw [h_dec]
      rw [sigma_one_mul_coprime 2 _ h_cop1]
      rw [sigma_one_mul_coprime 11 23 h_cop2]
      have h2 : sigma 1 2 = 3 := by rfl
      have h11 : sigma 1 11 = 12 := by rfl
      have h23 : sigma 1 23 = 24 := by rfl
      rw [h2, h11, h23]
    rw [h_sig]
    norm_num
    rfl
  by_cases hn184 : n = 184
  · rw [hn184]
    use 16020
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h_ne : ¬ 16020 = 0 := by decide
    rw [if_neg h_ne]
    have h_sig : sigma 1 16020 = 49140 := by
      have h_dec : 16020 = 4 * (5 * (9 * 89)) := by rfl
      have h_cop1 : Coprime 4 (5 * (9 * 89)) := by decide
      have h_cop2 : Coprime 5 (9 * 89) := by decide
      have h_cop3 : Coprime 9 89 := by decide
      rw [h_dec]
      rw [sigma_one_mul_coprime 4 _ h_cop1]
      rw [sigma_one_mul_coprime 5 _ h_cop2]
      rw [sigma_one_mul_coprime 9 89 h_cop3]
      have h4 : sigma 1 4 = 7 := by rfl
      have h5 : sigma 1 5 = 6 := by rfl
      have h9 : sigma 1 9 = 13 := by rfl
      have h89 : sigma 1 89 = 90 := by rfl
      rw [h4, h5, h9, h89]
    rw [h_sig]
    norm_num
    rfl
  by_cases hn186 : n = 186
  · rw [hn186]
    use 315360
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h_ne : ¬ 315360 = 0 := by decide
    rw [if_neg h_ne]
    have h_sig : sigma 1 315360 = 1118880 := by
      have h_dec : 315360 = 5 * (27 * (32 * 73)) := by rfl
      have h_cop1 : Coprime 5 (27 * (32 * 73)) := by decide
      have h_cop2 : Coprime 27 (32 * 73) := by decide
      have h_cop3 : Coprime 32 73 := by decide
      rw [h_dec]
      rw [sigma_one_mul_coprime 5 _ h_cop1]
      rw [sigma_one_mul_coprime 27 _ h_cop2]
      rw [sigma_one_mul_coprime 32 73 h_cop3]
      have h5 : sigma 1 5 = 6 := by rfl
      have h27 : sigma 1 27 = 40 := by rfl
      have h32 : sigma 1 32 = 63 := by rfl
      have h73 : sigma 1 73 = 74 := by rfl
      rw [h5, h27, h32, h73]
    rw [h_sig]
    norm_num
    rfl
  by_cases hn190 : n = 190
  · rw [hn190]
    use 1004
    refine ⟨by decide, ?_⟩
    unfold A243473_val
    have h_ne : ¬ 1004 = 0 := by decide
    rw [if_neg h_ne]
    have h_sig : sigma 1 1004 = 1764 := by
      have h_dec : 1004 = 4 * 251 := by rfl
      have h_cop : Coprime 4 251 := by decide
      rw [h_dec]
      rw [sigma_one_mul_coprime 4 251 h_cop]
      have h4 : sigma 1 4 = 7 := by rfl
      have h251 : sigma 1 251 = 252 := by rfl
      rw [h4, h251]
    rw [h_sig]
    norm_num
    rfl
  sorry


