import FormalConjectures.Util.ProblemImports

/--
Integral factorial ratio sequence:
$$a(n) = \frac{(30n)! n!}{(15n)! (10n)! (6n)!}$$
-/
def a (n : ℕ) : ℕ :=
  (Nat.factorial (30 * n) * Nat.factorial n) /
  (Nat.factorial (15 * n) * Nat.factorial (10 * n) * Nat.factorial (6 * n))

open Finset Nat Int

-- Helper definition for the set of indices coprime to 30.
def coprime_indices (r : ℕ) : Finset ℕ :=
  (Finset.range (r + 1)).filter (fun i => 1 ≤ i ∧ Nat.gcd i 30 = 1)

/--
The product term in the denominator of the general conjecture:
$$\prod_{i = 1..r, i \text{ coprime to } 30} (30n - i)$$
We define this in ℤ to handle the $n=0$ case where $30n-i$ in the product might be negative.
-/
def divisor_product (n r : ℕ) : ℤ :=
  (coprime_indices r).prod (fun i : ℕ => 30 * (n : ℤ) - (i : ℤ))


theorem log_lt_self (p n : ℕ) [hp : Fact p.Prime] : Nat.log p n < n + 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have H1 : p ≥ 2 := Nat.Prime.two_le hp.out
    have H2 : 2 ^ n ≤ p ^ n := Nat.pow_le_pow_left H1 _
    have H3 : 2 ^ n * 2 ≤ p ^ n * p := by apply Nat.mul_le_mul H2 H1
    have H4 : n < 2 ^ n := Nat.lt_pow_self Nat.one_lt_two
    have H5 : n < p ^ (n + 1) := by
      calc
        n < 2 ^ n := H4
        _ ≤ 2 ^ n * 2 := Nat.le_mul_of_pos_right _ (by decide)
        _ ≤ p ^ n * p := H3
        _ = p ^ (n + 1) := by ring
    exact Nat.log_lt_of_lt_pow' (by omega) H5

theorem padicValNat_fact_eq_b (p n b : ℕ) [hp : Fact p.Prime] (hb : n + 1 ≤ b) :
    padicValNat p n.factorial = ∑ i ∈ Ico 1 b, n / p ^ i := by
  have : Nat.log p n < b := lt_of_lt_of_le (log_lt_self p n) hb
  exact padicValNat_factorial this

theorem B_C_padic (p n : ℕ) [hp : Fact p.Prime] (hn : n > 0) :
    padicValNat p ((30 * n).factorial * n.factorial) =
    ∑ i ∈ Ico 1 (30 * n + 1), (30 * n / p ^ i + n / p ^ i) := by
  have H1 : (30 * n).factorial ≠ 0 := Nat.factorial_ne_zero _
  have H2 : n.factorial ≠ 0 := Nat.factorial_ne_zero _
  rw [padicValNat.mul H1 H2]
  rw [padicValNat_fact_eq_b p (30 * n) (30 * n + 1) (by omega)]
  rw [padicValNat_fact_eq_b p n (30 * n + 1) (by omega)]
  rw [← sum_add_distrib]

theorem C_padic (p n : ℕ) [hp : Fact p.Prime] (hn : n > 0) :
    padicValNat p ((15 * n).factorial * (10 * n).factorial * (6 * n).factorial) =
    ∑ i ∈ Ico 1 (30 * n + 1), (15 * n / p ^ i + 10 * n / p ^ i + 6 * n / p ^ i) := by
  have H1 : (15 * n).factorial ≠ 0 := Nat.factorial_ne_zero _
  have H2 : (10 * n).factorial ≠ 0 := Nat.factorial_ne_zero _
  have H3 : (6 * n).factorial ≠ 0 := Nat.factorial_ne_zero _
  rw [padicValNat.mul (Nat.mul_ne_zero H1 H2) H3, padicValNat.mul H1 H2]
  rw [padicValNat_fact_eq_b p (15 * n) (30 * n + 1) (by omega)]
  rw [padicValNat_fact_eq_b p (10 * n) (30 * n + 1) (by omega)]
  rw [padicValNat_fact_eq_b p (6 * n) (30 * n + 1) (by omega)]
  rw [← sum_add_distrib, ← sum_add_distrib]

theorem div_c (c k r q : ℕ) (hq : q > 0) : (c * (k * q + r)) / q = c * k + c * r / q := by
  have h1 : c * (k * q + r) = c * r + c * k * q := by ring
  rw [h1, Nat.add_mul_div_right (c * r) (c * k) hq, Nat.add_comm]

theorem my_div_div (X c q : ℕ) : X / c / q = X / q / c := by
  calc
    X / c / q = X / (c * q) := by rw [Nat.div_div_eq_div_mul]
    _ = X / (q * c) := by rw [Nat.mul_comm c q]
    _ = X / q / c := by rw [← Nat.div_div_eq_div_mul]

theorem m_coprime (m r q : ℕ) (h : 30 * r = m * q + 1) : ¬ 2 ∣ m ∧ ¬ 3 ∣ m ∧ ¬ 5 ∣ m := by
  have h2 : ¬ 2 ∣ m := by
    intro ⟨c, hc⟩
    have : 30 * r = 2 * (c * q) + 1 := by
      calc
        30 * r = m * q + 1 := h
        _ = (2 * c) * q + 1 := by rw [hc]
        _ = 2 * (c * q) + 1 := by ring
    omega
  have h3 : ¬ 3 ∣ m := by
    intro ⟨c, hc⟩
    have : 30 * r = 3 * (c * q) + 1 := by
      calc
        30 * r = m * q + 1 := h
        _ = (3 * c) * q + 1 := by rw [hc]
        _ = 3 * (c * q) + 1 := by ring
    omega
  have h5 : ¬ 5 ∣ m := by
    intro ⟨c, hc⟩
    have : 30 * r = 5 * (c * q) + 1 := by
      calc
        30 * r = m * q + 1 := h
        _ = (5 * c) * q + 1 := by rw [hc]
        _ = 5 * (c * q) + 1 := by ring
    omega
  exact ⟨h2, h3, h5⟩

theorem m_ineq_cases (m : ℕ) (hm : m ≤ 29) (h2 : ¬ 2 ∣ m) (h3 : ¬ 3 ∣ m) (h5 : ¬ 5 ∣ m) :
    m / 2 + m / 3 + m / 5 + 1 ≤ m := by
  interval_cases m <;> (revert h2 h3 h5 hm; decide)

theorem m_ineq_cases2 (m : ℕ) (hm : m ≤ 29) : m / 2 + m / 3 + m / 5 ≤ m := by
  interval_cases m <;> decide

theorem weak_div_ineq (n q : ℕ) (hq : q > 0) :
    15 * n / q + 10 * n / q + 6 * n / q ≤ 30 * n / q + n / q := by
  let k := n / q
  let r := n % q
  have hn : n = k * q + r := by
    calc
      n = q * k + r := (Nat.div_add_mod n q).symm
      _ = k * q + r := by ring
  have hr : r < q := Nat.mod_lt n hq
  have hn_div : n / q = k := rfl
  conv => lhs; rw [hn, div_c 15 k r q hq, div_c 10 k r q hq, div_c 6 k r q hq]
  conv => rhs; rw [hn, div_c 30 k r q hq, ← hn, hn_div]
  have h15 : 15 * r / q = (30 * r / q) / 2 := by
    calc
      15 * r / q = (30 * r) / 2 / q := by congr 1; omega
      _ = (30 * r / q) / 2 := my_div_div (30 * r) 2 q
  have h10 : 10 * r / q = (30 * r / q) / 3 := by
    calc
      10 * r / q = (30 * r) / 3 / q := by congr 1; omega
      _ = (30 * r / q) / 3 := my_div_div (30 * r) 3 q
  have h6 : 6 * r / q = (30 * r / q) / 5 := by
    calc
      6 * r / q = (30 * r) / 5 / q := by congr 1; omega
      _ = (30 * r / q) / 5 := my_div_div (30 * r) 5 q
  rw [h15, h10, h6]
  set m := 30 * r / q
  have hm : m ≤ 29 := by
    have : 30 * r < q * 30 := by omega
    have : 30 * r / q < 30 := Nat.div_lt_of_lt_mul this
    omega
  have H := m_ineq_cases2 m hm
  omega

theorem strict_div_ineq (n q : ℕ) (hq : q > 0) (h : 30 * n % q = 1) :
    15 * n / q + 10 * n / q + 6 * n / q + 1 ≤ 30 * n / q + n / q := by
  let k := n / q
  let r := n % q
  have hn : n = k * q + r := by
    calc
      n = q * k + r := (Nat.div_add_mod n q).symm
      _ = k * q + r := by ring
  have hr : r < q := Nat.mod_lt n hq
  have hn_div : n / q = k := rfl
  conv => lhs; rw [hn, div_c 15 k r q hq, div_c 10 k r q hq, div_c 6 k r q hq]
  conv => rhs; rw [hn, div_c 30 k r q hq, ← hn, hn_div]
  have h15 : 15 * r / q = (30 * r / q) / 2 := by
    calc
      15 * r / q = (30 * r) / 2 / q := by congr 1; omega
      _ = (30 * r / q) / 2 := my_div_div (30 * r) 2 q
  have h10 : 10 * r / q = (30 * r / q) / 3 := by
    calc
      10 * r / q = (30 * r) / 3 / q := by congr 1; omega
      _ = (30 * r / q) / 3 := my_div_div (30 * r) 3 q
  have h6 : 6 * r / q = (30 * r / q) / 5 := by
    calc
      6 * r / q = (30 * r) / 5 / q := by congr 1; omega
      _ = (30 * r / q) / 5 := my_div_div (30 * r) 5 q
  rw [h15, h10, h6]
  set m := 30 * r / q
  have hm1 : 30 * n = 30 * k * q + 30 * r := by
    calc
      30 * n = 30 * (k * q + r) := by rw [hn]
      _ = 30 * k * q + 30 * r := by ring
  have hr_mod : 30 * r % q = 1 := by
    calc
      30 * r % q = (30 * r + 30 * k * q) % q := by rw [Nat.add_mul_mod_self_right]
      _ = (30 * k * q + 30 * r) % q := by rw [Nat.add_comm]
      _ = 30 * n % q := by rw [← hm1]
      _ = 1 := h
  have hr_eq : 30 * r = m * q + 1 := by
    calc
      30 * r = q * m + 30 * r % q := (Nat.div_add_mod (30 * r) q).symm
      _ = q * m + 1 := by rw [hr_mod]
      _ = m * q + 1 := by ring
  have hm_bound : m ≤ 29 := by
    have : 30 * r < q * 30 := by omega
    have : 30 * r / q < 30 := Nat.div_lt_of_lt_mul this
    omega
  have Hcoprime := m_coprime m r q hr_eq
  have H := m_ineq_cases m hm_bound Hcoprime.1 Hcoprime.2.1 Hcoprime.2.2
  omega

theorem sum_ge_k (b k : ℕ) (hk : k < b) (F : ℕ → ℕ)
    (H_strict : ∀ i, i ∈ Ico 1 (k + 1) → F i ≥ 1) :
    ∑ i ∈ Ico 1 b, F i ≥ k := by
  have H_sub : Ico 1 (k + 1) ⊆ Ico 1 b := by
    intro x hx
    rw [mem_Ico] at hx ⊢
    exact ⟨hx.1, lt_of_le_of_lt (Nat.le_of_lt_succ hx.2) hk⟩
  have eq_sum : ∑ i ∈ Ico 1 b, F i = ∑ i ∈ Ico 1 (k + 1), F i + ∑ i ∈ Ico 1 b \ Ico 1 (k + 1), F i := by
    rw [← sum_sdiff H_sub, add_comm]
  calc
    ∑ i ∈ Ico 1 b, F i = ∑ i ∈ Ico 1 (k + 1), F i + ∑ i ∈ Ico 1 b \ Ico 1 (k + 1), F i := eq_sum
    _ ≥ ∑ i ∈ Ico 1 (k + 1), F i := Nat.le_add_right _ _
    _ ≥ ∑ i ∈ Ico 1 (k + 1), 1 := by apply sum_le_sum; intro i hi; exact H_strict i hi
    _ = k := by simp

theorem padic_dvd_of_le (M A B C : ℕ) (hB0 : B ≠ 0) (hC0 : C ≠ 0)
    (hA : B = A * C)
    (H : ∀ p : ℕ, [Fact p.Prime] → ∀ k : ℕ, p ^ k ∣ M → padicValNat p C + k ≤ padicValNat p B) :
    M ∣ A := by
  have hA0 : A ≠ 0 := by
    intro h
    rw [h, zero_mul] at hA
    exact hB0 hA
  apply (Nat.dvd_iff_prime_pow_dvd_dvd A M).mpr
  intro p k hp hpk
  haveI : Fact p.Prime := ⟨hp⟩
  have hle : padicValNat p C + k ≤ padicValNat p B := H p k hpk
  have hpB : padicValNat p B = padicValNat p A + padicValNat p C := by
    rw [hA, padicValNat.mul hA0 hC0]
  have : k ≤ padicValNat p A := by omega
  exact (padicValNat_dvd_iff_le hA0).mpr this

theorem M_mod (n q m : ℕ) (h1 : n > 0) (hq : q > 1) (h : 30 * n - 1 = m * q) :
    30 * n % q = 1 := by
  have eq1 : 30 * n = m * q + 1 := by omega
  calc
    30 * n % q = (m * q + 1) % q := by rw [eq1]
    _ = (1 + m * q) % q := by rw [add_comm]
    _ = 1 % q := Nat.add_mul_mod_self_right 1 m q
    _ = 1 := Nat.mod_eq_of_lt hq

theorem int_dvd_of_nat_dvd (n : ℕ) (a : ℕ) (h : (30 * n - 1) ∣ a) :
    (30 * (n : ℤ) - 1) ∣ (a : ℤ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · norm_num
  · have : (30 * (n : ℤ) - 1) = ((30 * n - 1 : ℕ) : ℤ) := by
      have H : 1 ≤ 30 * n := by omega
      exact (Int.ofNat_sub H).symm
    rw [this]
    exact Int.natCast_dvd_natCast.mpr h

theorem fact_pos (n : ℕ) : n.factorial > 0 := Nat.factorial_pos n

theorem B_padic_eq_C_plus_sum (p n : ℕ) [hp : Fact p.Prime] (hn : n > 0) :
    padicValNat p ((30 * n).factorial * n.factorial) =
    padicValNat p ((15 * n).factorial * (10 * n).factorial * (6 * n).factorial) +
    ∑ i ∈ Ico 1 (30 * n + 1), (30 * n / p ^ i + n / p ^ i - (15 * n / p ^ i + 10 * n / p ^ i + 6 * n / p ^ i)) := by
  rw [B_C_padic p n hn, C_padic p n hn]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  have hq : p ^ i > 0 := Nat.pow_pos hp.out.pos
  exact (Nat.add_sub_cancel' (weak_div_ineq n (p ^ i) hq)).symm

theorem dvd_of_padic_le (B C : ℕ) (hB0 : B ≠ 0) (hC0 : C ≠ 0)
    (hle : ∀ p : ℕ, [Fact p.Prime] → padicValNat p C ≤ padicValNat p B) : C ∣ B := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd B C).mpr
  intro p k hp hpk
  haveI : Fact p.Prime := ⟨hp⟩
  have hk : k ≤ padicValNat p C := (padicValNat_dvd_iff_le hC0).mp hpk
  have hB : k ≤ padicValNat p B := le_trans hk (hle p)
  exact (padicValNat_dvd_iff_le hB0).mpr hB

theorem C_dvd_B (n : ℕ) (hn : n > 0) :
    (15 * n).factorial * (10 * n).factorial * (6 * n).factorial ∣ (30 * n).factorial * n.factorial := by
  apply dvd_of_padic_le
  · exact Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
  · exact Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _)
  · intro p hp
    rw [B_padic_eq_C_plus_sum p n hn]
    exact Nat.le_add_right _ _

theorem a_mul_C (n : ℕ) (hn : n > 0) :
    (30 * n).factorial * n.factorial = a n * ((15 * n).factorial * (10 * n).factorial * (6 * n).factorial) := by
  dsimp [a]
  exact (Nat.div_mul_cancel (C_dvd_B n hn)).symm

theorem M_dvd_a (n : ℕ) (hn : n > 0) : (30 * n - 1) ∣ a n := by
  let B := (30 * n).factorial * n.factorial
  let C := (15 * n).factorial * (10 * n).factorial * (6 * n).factorial
  have hB0 : B ≠ 0 := Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
  have hC0 : C ≠ 0 := Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _)
  apply padic_dvd_of_le (30 * n - 1) (a n) B C hB0 hC0 (a_mul_C n hn)
  intro p hp k hpk
  rw [B_padic_eq_C_plus_sum p n hn]
  have H_strict : ∀ i, i ∈ Ico 1 (k + 1) →
      (30 * n / p ^ i + n / p ^ i - (15 * n / p ^ i + 10 * n / p ^ i + 6 * n / p ^ i)) ≥ 1 := by
    intro i hi
    rw [mem_Ico] at hi
    have hq : p ^ i > 0 := Nat.pow_pos hp.out.pos
    have hq_gt : p ^ i > 1 := by
      have H1 : p ≥ 2 := Nat.Prime.two_le hp.out
      calc
        p ^ i ≥ 2 ^ i := Nat.pow_le_pow_left H1 _
        _ ≥ 2 ^ 1 := Nat.pow_le_pow_right (by decide) hi.1
        _ = 2 := by rfl
        _ > 1 := by decide
    have hdiv : p ^ i ∣ 30 * n - 1 := by
      have : p ^ i ∣ p ^ k := Nat.pow_dvd_pow p (by omega)
      exact dvd_trans this hpk
    obtain ⟨m, hm_eq⟩ := hdiv
    have hm_eq2 : 30 * n - 1 = m * p ^ i := by
      rw [hm_eq, mul_comm]
    have h_mod : 30 * n % p ^ i = 1 := M_mod n (p ^ i) m hn hq_gt hm_eq2
    have h_ineq := strict_div_ineq n (p ^ i) hq h_mod
    omega
  have hk_lt : k < 30 * n + 1 := by
    have h_pk_le : p ^ k ≤ 30 * n - 1 := Nat.le_of_dvd (by omega) hpk
    have : k < p ^ k := by
      have H1 : p ≥ 2 := Nat.Prime.two_le hp.out
      calc
        k < 2 ^ k := Nat.lt_pow_self Nat.one_lt_two
        _ ≤ p ^ k := Nat.pow_le_pow_left H1 _
    omega
  have sum_bound := sum_ge_k (30 * n + 1) k hk_lt _ H_strict
  have : padicValNat p C = padicValNat p ((15 * n).factorial * (10 * n).factorial * (6 * n).factorial) := rfl
  rw [this]
  omega

/--
It appears that a(n)/(30*n - 1) is integral for all n (checked up to n = 1000).
This is the specific case of the general conjecture for r=1 with D(1)=1.
-/
theorem oeis_a211417_conjecture_specific (n : ℕ) :
  (30 * (n : ℤ) - 1) ∣ (a n : ℤ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · dsimp [a]
    norm_num
  · exact int_dvd_of_nat_dvd n (a n) (M_dvd_a n (Nat.pos_of_ne_zero hn))

theorem oeis_a211417_conjecture_specific.disproof : ¬ (type_of% @oeis_a211417_conjecture_specific) := sorry
