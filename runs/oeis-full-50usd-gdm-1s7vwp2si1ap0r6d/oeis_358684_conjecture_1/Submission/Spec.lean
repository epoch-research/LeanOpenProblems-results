import FormalConjectures.Util.ProblemImports

open Nat

/--
A358684: $a(n)$ is the minimum integer $k$ such that the smallest prime factor of the $n$-th Fermat number exceeds $2^{2^n - k}$.
Let $F_n = 2^{2^n} + 1$ be the $n$-th Fermat number, and $P_n$ be its smallest prime factor.
The definition of $a(n)$ is equivalent to the closed form:
$$a(n) = 2^n - \lfloor \log_2(P_n) \rfloor$$
where $P_n = \operatorname{minFac}(\operatorname{fermatNumber} n)$.
The subtraction is defined in $\mathbb{N}$ and is safe since $P_n \le F_n$, implying $\log_2 P_n < 2^n$.
-/
def a (n : ℕ) : ℕ :=
  let pn := minFac (fermatNumber n)
  (2 ^ n) - (log2 pn)

set_option exponentiation.threshold 20000000
set_option maxHeartbeats 10000000

def check_div_conquer_fuel (F : ℕ) (modulus_shift : ℕ) (start : ℕ) (k : ℕ) (fuel : ℕ) : Bool :=
  match fuel with
  | 0 => true
  | fuel' + 1 =>
    if k = 0 then true
    else if k = 1 then
      (F % (start * modulus_shift + 1) != 0)
    else
      let half := k / 2
      check_div_conquer_fuel F modulus_shift start half fuel' &&
      check_div_conquer_fuel F modulus_shift (start + half) (k - half) fuel'

def check_div_conquer (F : ℕ) (modulus_shift : ℕ) (start : ℕ) (k : ℕ) : Bool :=
  check_div_conquer_fuel F modulus_shift start k k

theorem check_div_conquer_fuel_correct (F : ℕ) (modulus_shift : ℕ) (start : ℕ) (k : ℕ) (fuel : ℕ) (q_k : ℕ) (q : ℕ)
    (hq : q = q_k * modulus_shift + 1) (hq_ge : start ≤ q_k) (hq_lt : q_k < start + k) (hq_pos : 0 < q_k)
    (h_fuel : k ≤ fuel) (h_check : check_div_conquer_fuel F modulus_shift start k fuel = true) :
    ¬ (q ∣ F) := by
  induction fuel generalizing start q_k q k with
  | zero =>
    omega
  | succ fuel' ih =>
    unfold check_div_conquer_fuel at h_check
    split_ifs at h_check with hk hk1
    · omega
    · -- k = 1 case
      subst hk1
      have h_qk : q_k = start := by omega
      subst h_qk hq
      intro h_dvd
      rw [Nat.dvd_iff_mod_eq_zero] at h_dvd
      rw [h_dvd] at h_check
      revert h_check
      decide
    · -- k > 1 case
      have h_and : (check_div_conquer_fuel F modulus_shift start (k / 2) fuel' && check_div_conquer_fuel F modulus_shift (start + k / 2) (k - k / 2) fuel') = true := h_check
      rw [Bool.and_eq_true] at h_and
      rcases h_and with ⟨h_left, h_right⟩
      let half := k / 2
      have h_half_lt : half < k := Nat.div_lt_self (by omega) (by decide)
      have h_k_sub_lt : k - half < k := by
        have : 0 < half := Nat.div_pos (by omega) (by decide)
        omega
      have h_cases : q_k < start + half ∨ start + half ≤ q_k := by omega
      rcases h_cases with h_lt | h_ge
      · have h_fuel_left : half ≤ fuel' := by omega
        exact ih start q_k q half hq hq_ge h_lt hq_pos h_fuel_left h_left
      · have h_fuel_right : k - half ≤ fuel' := by
          have : 0 < half := Nat.div_pos (by omega) (by decide)
          omega
        have h_lt_cast : q_k < start + half + (k - half) := by omega
        exact ih (start + half) q_k q (k - half) hq h_ge h_lt_cast hq_pos h_fuel_right h_right

theorem check_div_conquer_correct (F : ℕ) (modulus_shift : ℕ) (start : ℕ) (k : ℕ) (q_k : ℕ) (q : ℕ)
    (hq : q = q_k * modulus_shift + 1) (hq_ge : start ≤ q_k) (hq_lt : q_k < start + k) (hq_pos : 0 < q_k)
    (h_check : check_div_conquer F modulus_shift start k = true) :
    ¬ (q ∣ F) := by
  unfold check_div_conquer at h_check
  exact check_div_conquer_fuel_correct F modulus_shift start k k q_k q hq hq_ge h_lt hq_pos (by omega) h_check

theorem a_eq (n : ℕ) (pn : ℕ) (h : minFac (fermatNumber n) = pn) (val : ℕ) (h_val : (2^n) - log2 pn = val) : a n = val := by
  unfold a
  rw [h]
  exact h_val
\ntheorem check_f15 : check_div_conquer (fermatNumber 15) (2^17) 1 9263 = true := by decide\ntheorem check_f16 : check_div_conquer (fermatNumber 16) (2^18) 1 1574 = true := by decide\ntheorem check_f17 : check_div_conquer (fermatNumber 17) (2^19) 1 59250 = true := by decide\ntheorem check_f19 : check_div_conquer (fermatNumber 19) (2^21) 1 1312 = true := by decide\ntheorem check_f21 : check_div_conquer (fermatNumber 21) (2^23) 1 1018 = true := by decide\n\nattribute [irreducible] check_div_conquer check_div_conquer_fuel\n\n-- F_15
theorem prime_1214251009 : Nat.Prime 1214251009 := by norm_num

theorem minFac_F_15 : minFac (fermatNumber 15) = 1214251009 := by
  have h_dvd : 1214251009 ∣ fermatNumber 15 := by
    rw [← ZMod.natCast_eq_zero_iff]
    unfold fermatNumber; push_cast; reduce_mod_char
  have h1 : minFac (fermatNumber 15) ≤ 1214251009 := by
    apply minFac_le_of_dvd
    · decide
    · exact h_dvd
  have h2 : 1214251009 ≤ minFac (fermatNumber 15) := by
    have h2' : ∀ q, Prime q → q ∣ fermatNumber 15 → 1214251009 ≤ q := by
      intro q hq_prime hq_dvd
      obtain ⟨k, hq_eq⟩ := fermat_primeFactors_one_lt 15 q (by decide) hq_prime hq_dvd
      have hk_pos : 0 < k := by
        by_contra hk_zero
        have hk0 : k = 0 := by omega
        subst hk0
        rw [zero_mul, zero_add] at hq_eq
        subst hq_eq
        exact hq_prime.ne_one rfl
      have h_cases : k ≥ 9264 ∨ k < 9264 := by omega
      rcases h_cases with hk_ge | hk_lt
      · rw [hq_eq]
        have : 1214251009 = 9264 * 2^17 + 1 := by rfl
        rw [this]
        gcongr
      · have h_not_dvd := check_div_conquer_correct (fermatNumber 15) (2^17) 1 9263 k q hq_eq hk_pos hk_lt hk_pos check_f15
        exact h_not_dvd hq_dvd
    have h2_or := le_minFac.mpr h2'
    rcases h2_or with h_one | h_le
    · exfalso
      have : 3 ≤ fermatNumber 15 := three_le_fermatNumber 15
      rw [h_one] at this
      omega
    · exact h_le
  exact le_antisymm h1 h2

theorem a_15_eq : a 15 = 32738 := by
  apply a_eq 15 1214251009 minFac_F_15 32738
  decide
\n-- F_16
theorem prime_825753601 : Nat.Prime 825753601 := by norm_num

theorem minFac_F_16 : minFac (fermatNumber 16) = 825753601 := by
  have h_dvd : 825753601 ∣ fermatNumber 16 := by
    rw [← ZMod.natCast_eq_zero_iff]
    unfold fermatNumber; push_cast; reduce_mod_char
  have h1 : minFac (fermatNumber 16) ≤ 825753601 := by
    apply minFac_le_of_dvd
    · decide
    · exact h_dvd
  have h2 : 825753601 ≤ minFac (fermatNumber 16) := by
    have h2' : ∀ q, Prime q → q ∣ fermatNumber 16 → 825753601 ≤ q := by
      intro q hq_prime hq_dvd
      obtain ⟨k, hq_eq⟩ := fermat_primeFactors_one_lt 16 q (by decide) hq_prime hq_dvd
      have hk_pos : 0 < k := by
        by_contra hk_zero
        have hk0 : k = 0 := by omega
        subst hk0
        rw [zero_mul, zero_add] at hq_eq
        subst hq_eq
        exact hq_prime.ne_one rfl
      have h_cases : k ≥ 1575 ∨ k < 1575 := by omega
      rcases h_cases with hk_ge | hk_lt
      · rw [hq_eq]
        have : 825753601 = 1575 * 2^18 + 1 := by rfl
        rw [this]
        gcongr
      · have h_not_dvd := check_div_conquer_correct (fermatNumber 16) (2^18) 1 1574 k q hq_eq hk_pos hk_lt hk_pos check_f16
        exact h_not_dvd hq_dvd
    have h2_or := le_minFac.mpr h2'
    rcases h2_or with h_one | h_le
    · exfalso
      have : 3 ≤ fermatNumber 16 := three_le_fermatNumber 16
      rw [h_one] at this
      omega
    · exact h_le
  exact le_antisymm h1 h2

theorem a_16_eq : a 16 = 65507 := by
  apply a_eq 16 825753601 minFac_F_16 65507
  decide
\n-- F_17
theorem prime_31065037602817 : Nat.Prime 31065037602817 := by norm_num

theorem minFac_F_17 : minFac (fermatNumber 17) = 31065037602817 := by
  have h_dvd : 31065037602817 ∣ fermatNumber 17 := by
    rw [← ZMod.natCast_eq_zero_iff]
    unfold fermatNumber; push_cast; reduce_mod_char
  have h1 : minFac (fermatNumber 17) ≤ 31065037602817 := by
    apply minFac_le_of_dvd
    · decide
    · exact h_dvd
  have h2 : 31065037602817 ≤ minFac (fermatNumber 17) := by
    have h2' : ∀ q, Prime q → q ∣ fermatNumber 17 → 31065037602817 ≤ q := by
      intro q hq_prime hq_dvd
      obtain ⟨k, hq_eq⟩ := fermat_primeFactors_one_lt 17 q (by decide) hq_prime hq_dvd
      have hk_pos : 0 < k := by
        by_contra hk_zero
        have hk0 : k = 0 := by omega
        subst hk0
        rw [zero_mul, zero_add] at hq_eq
        subst hq_eq
        exact hq_prime.ne_one rfl
      have h_cases : k ≥ 59251 ∨ k < 59251 := by omega
      rcases h_cases with hk_ge | hk_lt
      · rw [hq_eq]
        have : 31065037602817 = 59251 * 2^19 + 1 := by rfl
        rw [this]
        gcongr
      · have h_not_dvd := check_div_conquer_correct (fermatNumber 17) (2^19) 1 59250 k q hq_eq hk_pos hk_lt hk_pos check_f17
        exact h_not_dvd hq_dvd
    have h2_or := le_minFac.mpr h2'
    rcases h2_or with h_one | h_le
    · exfalso
      have : 3 ≤ fermatNumber 17 := three_le_fermatNumber 17
      rw [h_one] at this
      omega
    · exact h_le
  exact le_antisymm h1 h2

theorem a_17_eq : a 17 = 131028 := by
  apply a_eq 17 31065037602817 minFac_F_17 131028
  decide
\n-- F_18
theorem prime_13631489 : Nat.Prime 13631489 := by norm_num

theorem dvd_F_18 : 13631489 ∣ fermatNumber 18 := by
  rw [← ZMod.natCast_eq_zero_iff]
  unfold fermatNumber; push_cast; reduce_mod_char

theorem not_dvd_F_18_7340033 : ¬ 7340033 ∣ fermatNumber 18 := by
  rw [← ZMod.natCast_eq_zero_iff]
  unfold fermatNumber; push_cast; reduce_mod_char; decide

theorem minFac_F_18 : minFac (fermatNumber 18) = 13631489 := by
  have h_dvd : 13631489 ∣ fermatNumber 18 := dvd_F_18
  have h1 : minFac (fermatNumber 18) ≤ 13631489 := by
    apply minFac_le_of_dvd
    · decide
    · exact h_dvd
  have h2 : 13631489 ≤ minFac (fermatNumber 18) := by
    have h2' : ∀ q, Prime q → q ∣ fermatNumber 18 → 13631489 ≤ q := by
      intro q hq_prime hq_dvd
      obtain ⟨k, hq_eq⟩ := fermat_primeFactors_one_lt 18 q (by decide) hq_prime hq_dvd
      have hk_pos : 0 < k := by
        by_contra hk_zero
        have hk0 : k = 0 := by omega
        subst hk0
        rw [zero_mul, zero_add] at hq_eq
        subst hq_eq
        exact hq_prime.ne_one rfl
      have h_cases : k ≥ 13 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 := by omega
      rcases h_cases with hk_ge | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [hq_eq]
        have : 13631489 = 13 * 2^20 + 1 := by rfl
        rw [this]
        gcongr
      · rw [hq_eq] at hq_prime
        exfalso
        have h_comp : ¬ Nat.Prime (1 * 2^20 + 1) := by norm_num
        exact h_comp hq_prime
      · rw [hq_eq] at hq_prime
        exfalso
        have h_comp : ¬ Nat.Prime (2 * 2^20 + 1) := by norm_num
        exact h_comp hq_prime
      · rw [hq_eq] at hq_prime
        exfalso
        have h_comp : ¬ Nat.Prime (3 * 2^20 + 1) := by norm_num
        exact h_comp hq_prime
      · rw [hq_eq] at hq_prime
        exfalso
        have h_comp : ¬ Nat.Prime (4 * 2^20 + 1) := by norm_num
        exact h_comp hq_prime
      · rw [hq_eq] at hq_prime
        exfalso
        have h_comp : ¬ Nat.Prime (5 * 2^20 + 1) := by norm_num
        exact h_comp hq_prime
      · rw [hq_eq] at hq_prime
        exfalso
        have h_comp : ¬ Nat.Prime (6 * 2^20 + 1) := by norm_num
        exact h_comp hq_prime
      · rw [hq_eq] at hq_dvd
        exfalso
        have h_not : ¬ (7 * 2^20 + 1 ∣ fermatNumber 18) := not_dvd_F_18_7340033
        exact h_not hq_dvd
      · rw [hq_eq] at hq_prime
        exfalso
        have h_comp : ¬ Nat.Prime (8 * 2^20 + 1) := by norm_num
        exact h_comp hq_prime
      · rw [hq_eq] at hq_prime
        exfalso
        have h_comp : ¬ Nat.Prime (9 * 2^20 + 1) := by norm_num
        exact h_comp hq_prime
      · rw [hq_eq] at hq_prime
        exfalso
        have h_comp : ¬ Nat.Prime (10 * 2^20 + 1) := by norm_num
        exact h_comp hq_prime
      · rw [hq_eq] at hq_prime
        exfalso
        have h_comp : ¬ Nat.Prime (11 * 2^20 + 1) := by norm_num
        exact h_comp hq_prime
      · rw [hq_eq] at hq_prime
        exfalso
        have h_comp : ¬ Nat.Prime (12 * 2^20 + 1) := by norm_num
        exact h_comp hq_prime
    have h2_or := le_minFac.mpr h2'
    rcases h2_or with h_one | h_le
    · exfalso
      have : 3 ≤ fermatNumber 18 := three_le_fermatNumber 18
      rw [h_one] at this
      omega
    · exact h_le
  exact le_antisymm h1 h2

theorem a_18_eq : a 18 = 262121 := by
  apply a_eq 18 13631489 minFac_F_18 262121
  decide
\n-- F_19
theorem prime_70525124609 : Nat.Prime 70525124609 := by norm_num

theorem minFac_F_19 : minFac (fermatNumber 19) = 70525124609 := by
  have h_dvd : 70525124609 ∣ fermatNumber 19 := by
    rw [← ZMod.natCast_eq_zero_iff]
    unfold fermatNumber; push_cast; reduce_mod_char
  have h1 : minFac (fermatNumber 19) ≤ 70525124609 := by
    apply minFac_le_of_dvd
    · decide
    · exact h_dvd
  have h2 : 70525124609 ≤ minFac (fermatNumber 19) := by
    have h2' : ∀ q, Prime q → q ∣ fermatNumber 19 → 70525124609 ≤ q := by
      intro q hq_prime hq_dvd
      obtain ⟨k, hq_eq⟩ := fermat_primeFactors_one_lt 19 q (by decide) hq_prime hq_dvd
      have hk_pos : 0 < k := by
        by_contra hk_zero
        have hk0 : k = 0 := by omega
        subst hk0
        rw [zero_mul, zero_add] at hq_eq
        subst hq_eq
        exact hq_prime.ne_one rfl
      have h_cases : k ≥ 1313 ∨ k < 1313 := by omega
      rcases h_cases with hk_ge | hk_lt
      · rw [hq_eq]
        have : 70525124609 = 1313 * 2^21 + 1 := by rfl
        rw [this]
        gcongr
      · have h_not_dvd := check_div_conquer_correct (fermatNumber 19) (2^21) 1 1312 k q hq_eq hk_pos hk_lt hk_pos check_f19
        exact h_not_dvd hq_dvd
    have h2_or := le_minFac.mpr h2'
    rcases h2_or with h_one | h_le
    · exfalso
      have : 3 ≤ fermatNumber 19 := three_le_fermatNumber 19
      rw [h_one] at this
      omega
    · exact h_le
  exact le_antisymm h1 h2

theorem a_19_eq : a 19 = 524252 := by
  apply a_eq 19 70525124609 minFac_F_19 524252
  decide
\n-- F_21
theorem prime_4485296422913 : Nat.Prime 4485296422913 := by norm_num

theorem minFac_F_21 : minFac (fermatNumber 21) = 4485296422913 := by
  have h_dvd : 4485296422913 ∣ fermatNumber 21 := by
    rw [← ZMod.natCast_eq_zero_iff]
    unfold fermatNumber; push_cast; reduce_mod_char
  have h1 : minFac (fermatNumber 21) ≤ 4485296422913 := by
    apply minFac_le_of_dvd
    · decide
    · exact h_dvd
  have h2 : 4485296422913 ≤ minFac (fermatNumber 21) := by
    have h2' : ∀ q, Prime q → q ∣ fermatNumber 21 → 4485296422913 ≤ q := by
      intro q hq_prime hq_dvd
      obtain ⟨k, hq_eq⟩ := fermat_primeFactors_one_lt 21 q (by decide) hq_prime hq_dvd
      have hk_pos : 0 < k := by
        by_contra hk_zero
        have hk0 : k = 0 := by omega
        subst hk0
        rw [zero_mul, zero_add] at hq_eq
        subst hq_eq
        exact hq_prime.ne_one rfl
      have h_cases : k ≥ 1019 ∨ k < 1019 := by omega
      rcases h_cases with hk_ge | hk_lt
      · rw [hq_eq]
        have : 4485296422913 = 1019 * 2^23 + 1 := by rfl
        rw [this]
        gcongr
      · have h_not_dvd := check_div_conquer_correct (fermatNumber 21) (2^23) 1 1018 k q hq_eq hk_pos hk_lt hk_pos check_f21
        exact h_not_dvd hq_dvd
    have h2_or := le_minFac.mpr h2'
    rcases h2_or with h_one | h_le
    · exfalso
      have : 3 ≤ fermatNumber 21 := three_le_fermatNumber 21
      rw [h_one] at this
      omega
    · exact h_le
  exact le_antisymm h1 h2

theorem a_21_eq : a 21 = 2097110 := by
  apply a_eq 21 4485296422913 minFac_F_21 2097110
  decide
\n-- F_23
theorem prime_167772161 : Nat.Prime 167772161 := by norm_num

theorem dvd_F_23 : 167772161 ∣ fermatNumber 23 := by
  rw [← ZMod.natCast_eq_zero_iff]
  unfold fermatNumber; push_cast; reduce_mod_char

theorem minFac_F_23 : minFac (fermatNumber 23) = 167772161 := by
  have h_dvd : 167772161 ∣ fermatNumber 23 := dvd_F_23
  have h1 : minFac (fermatNumber 23) ≤ 167772161 := by
    apply minFac_le_of_dvd
    · decide
    · exact h_dvd
  have h2 : 167772161 ≤ minFac (fermatNumber 23) := by
    have h2' : ∀ q, Prime q → q ∣ fermatNumber 23 → 167772161 ≤ q := by
      intro q hq_prime hq_dvd
      obtain ⟨k, hq_eq⟩ := fermat_primeFactors_one_lt 23 q (by decide) hq_prime hq_dvd
      have hk_pos : 0 < k := by
        by_contra hk_zero
        have hk0 : k = 0 := by omega
        subst hk0
        rw [zero_mul, zero_add] at hq_eq
        subst hq_eq
        exact hq_prime.ne_one rfl
      have h_cases : k ≥ 5 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
      rcases h_cases with hk_ge | rfl | rfl | rfl | rfl
      · rw [hq_eq]
        have : 167772161 = 5 * 2^25 + 1 := by rfl
        rw [this]
        gcongr
      · rw [hq_eq] at hq_prime
        exfalso
        have h_comp : ¬ Nat.Prime (1 * 2^25 + 1) := by norm_num
        exact h_comp hq_prime
      · rw [hq_eq] at hq_prime
        exfalso
        have h_comp : ¬ Nat.Prime (2 * 2^25 + 1) := by norm_num
        exact h_comp hq_prime
      · rw [hq_eq] at hq_prime
        exfalso
        have h_comp : ¬ Nat.Prime (3 * 2^25 + 1) := by norm_num
        exact h_comp hq_prime
      · rw [hq_eq] at hq_prime
        exfalso
        have h_comp : ¬ Nat.Prime (4 * 2^25 + 1) := by norm_num
        exact h_comp hq_prime
    have h2_or := le_minFac.mpr h2'
    rcases h2_or with h_one | h_le
    · exfalso
      have : 3 ≤ fermatNumber 23 := three_le_fermatNumber 23
      rw [h_one] at this
      omega
    · exact h_le
  exact le_antisymm h1 h2

theorem a_23_eq : a 23 = 8388581 := by
  apply a_eq 23 167772161 minFac_F_23 8388581
  decide
\n
theorem a_14_eq : a 14 = 16208 := by
  sorry

theorem a_22_eq : a 22 = 4194189 := by
  sorry
\n
theorem oeis_358684_conjecture_1 :
    a 14 = 16208 ∧
    a 15 = 32738 ∧
    a 16 = 65507 ∧
    a 17 = 131028 ∧
    a 18 = 262121 ∧
    a 19 = 524252 ∧
    a 21 = 2097110 ∧
    a 22 = 4194189 ∧
    a 23 = 8388581 := by
  refine ⟨a_14_eq, a_15_eq, a_16_eq, a_17_eq, a_18_eq, a_19_eq, a_21_eq, a_22_eq, a_23_eq⟩
