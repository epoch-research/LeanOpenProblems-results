import FormalConjectures.Util.ProblemImports

open Nat Finset

noncomputable def a (n : ℕ) : ℕ :=
  let full_sum := (Nat.divisors n).sum (fun d => d * (Nat.divisors d).card)
  let self_term := n * (Nat.divisors n).card
  full_sum - self_term

lemma properDivisors_eq_erase (n : ℕ) (hn : 0 < n) : n.properDivisors = n.divisors.erase n := by
  ext d
  simp [Nat.mem_properDivisors, Nat.mem_divisors, hn.ne']
  constructor
  · rintro ⟨hdvd, hlt⟩
    exact ⟨hlt.ne, hdvd⟩
  · rintro ⟨hne, hdvd⟩
    refine ⟨hdvd, ?_⟩
    have hle := Nat.le_of_dvd hn hdvd
    omega

lemma properDivisors_sum (n : ℕ) (hn : 0 < n) :
    a n = (Nat.properDivisors n).sum (fun d => d * (Nat.divisors d).card) := by
  unfold a
  dsimp
  have h_mem : n ∈ n.divisors := by simp [Nat.mem_divisors, hn.ne']
  have h_eq : n.divisors = insert n n.properDivisors := by
    rw [properDivisors_eq_erase n hn]
    rw [Finset.insert_erase h_mem]
  have h_disj : n ∉ n.properDivisors := by
    rw [properDivisors_eq_erase n hn]
    simp
  rw [h_eq]
  rw [Finset.sum_insert h_disj]
  rw [← h_eq]
  omega

lemma card_divisors_ge_two (k : ℕ) (hk : 2 ≤ k) : 2 ≤ k.divisors.card := by
  have hk0 : k ≠ 0 := by omega
  have h1 : 1 ∈ k.divisors := by simp [Nat.mem_divisors, hk0]
  have hk_mem : k ∈ k.divisors := Nat.mem_divisors_self k hk0
  have h1k : 1 ≠ k := by omega
  have h_sub : ({1, k} : Finset ℕ) ⊆ k.divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h1
    · exact hk_mem
  have h_card := Finset.card_le_card h_sub
  have h_card2 : ({1, k} : Finset ℕ).card = 2 := by simp [h1k]
  omega

lemma a_of_prime (n : ℕ) (hp : n.Prime) : a n = 1 := by
  have hn0 : 0 < n := hp.pos
  rw [properDivisors_sum n hn0]
  rw [hp.properDivisors]
  simp

lemma tau_d_lt_p (n p d : ℕ) (hn : 0 < n) (hp_prime : p.Prime) (hd_eq : n = p * d) (h_a : a n = n) :
    d.divisors.card < p := by
  have hd_pos : 0 < d := by
    by_contra h_zero
    have : d = 0 := by omega
    subst this
    omega
  have h_prop : d ∈ n.properDivisors := by
    simp [Nat.mem_properDivisors]
    refine ⟨by use p; rw [mul_comm]; exact hd_eq, ?_⟩
    rw [hd_eq]
    have : p > 1 := hp_prime.one_lt
    calc
      d = 1 * d := by ring
      _ < p * d := Nat.mul_lt_mul_of_pos_right this hd_pos
  have h_prop1 : 1 ∈ n.properDivisors := by
    simp [Nat.mem_properDivisors]
    rw [hd_eq]
    have : p ≥ 2 := hp_prime.two_le
    have : d ≥ 1 := hd_pos
    nlinarith
  have h1d : 1 ≠ d := by
    intro h_eq
    rw [← h_eq, mul_one] at hd_eq
    have h_a_n : a n = 1 := by
      rw [hd_eq]
      exact a_of_prime p hp_prime
    rw [h_a] at h_a_n
    rw [hd_eq] at h_a_n
    have : p ≥ 2 := hp_prime.two_le
    omega
  have h_sub : ({1, d} : Finset ℕ) ⊆ n.properDivisors := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h_prop1
    · exact h_prop
  have h_sum_le : ∑ x ∈ ({1, d} : Finset ℕ), x * x.divisors.card ≤ ∑ x ∈ n.properDivisors, x * x.divisors.card :=
    Finset.sum_le_sum_of_subset h_sub
  rw [sum_insert (by simp [h1d]), sum_singleton] at h_sum_le
  have h_div1 : (1:ℕ).divisors.card = 1 := by decide
  rw [h_div1, one_mul] at h_sum_le
  have h_proper_sum : a n = ∑ x ∈ n.properDivisors, x * x.divisors.card := properDivisors_sum n hn
  rw [← h_proper_sum] at h_sum_le
  rw [h_a] at h_sum_le
  rw [hd_eq] at h_sum_le
  have : d * d.divisors.card < p * d := by omega
  nlinarith


lemma math_ineq (p m : ℕ) (hp : p ≥ 7) (hm : m ≥ p + 2) :
    3 * p^2 + 2 * p + 1 < m * (p^2 - 4 * p - 2) := by
  obtain ⟨x, rfl⟩ : ∃ x, p = 7 + x := ⟨p - 7, by omega⟩
  have : (7 + x) ^ 2 - 4 * (7 + x) - 2 = 19 + 10 * x + x * x := by
    have h1 : (7 + x) ^ 2 = 49 + 14 * x + x * x := by ring
    rw [h1]
    omega
  rw [this]
  have h_m : m * (19 + 10 * x + x * x) ≥ ((7 + x) + 2) * (19 + 10 * x + x * x) := by
    have : m ≥ (7 + x) + 2 := hm
    nlinarith
  rw [sq]
  nlinarith


lemma m_prime_contradiction (p m : ℕ) (hp : p.Prime) (hm : m.Prime) (hp5 : p ≥ 5) (hm_gt : m > p) (h_eq : 3 * p^2 + 2 * p + 1 = m * (p^2 - 4 * p - 2)) : False := by
  have hp_odd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h2 | h_odd
    · rw [h2] at hp5; contradiction
    · exact h_odd
  have hm_odd : m % 2 = 1 := by
    rcases hm.eq_two_or_odd with h2 | h_odd
    · rw [h2] at hm_gt; omega
    · exact h_odd
  have hm_ge : m ≥ p + 2 := by
    omega
  by_cases hp7 : p ≥ 7
  · have h_lt := math_ineq p m hp7 hm_ge
    omega
  · have hp_eq : p = 5 := by omega
    subst hp_eq
    rw [sq] at h_eq
    have h_calc : 86 = 3 * m := by
      omega
    have h_mod : 86 % 3 = (3 * m) % 3 := by rw [h_calc]
    omega


lemma m_contradiction (p m : ℕ) (hp5 : p ≥ 5) (hm : m ≥ p + 2) (h_eq : 3 * p^2 + 2 * p + 1 = m * (p^2 - 4 * p - 2)) : False := by
  by_cases hp7 : p ≥ 7
  · have h_lt := math_ineq p m hp7 hm
    omega
  · have hp_cases : p = 5 ∨ p = 6 := by omega
    rcases hp_cases with rfl | rfl
    · norm_num at h_eq
      omega
    · norm_num at h_eq
      omega


lemma no_sol_coprime (p y m : ℕ) (hp7 : p ≥ 7) (hy : y ≥ p + 2) (hm : m ≥ y)
    (h_le : 4 * p * y + 3 * (y * m) + 2 * p + 2 * y + 1 ≤ p * y * m) : False := by
  have h1 : p * y * m = (p - 3) * y * m + 3 * y * m := by
    have : p = p - 3 + 3 := by omega
    nth_rw 1 [this]
    ring
  have h2 : (p - 3) * y * m ≥ 4 * y * m := by
    have h_le_pm3 : 4 ≤ p - 3 := by omega
    have := Nat.mul_le_mul_right (y * m) h_le_pm3
    linarith
  have h3 : 4 * y * m ≥ 4 * y * y := Nat.mul_le_mul_left (4 * y) hm
  have h4 : 4 * y * y ≥ 4 * p * y + 2 * p + 2 * y + 1 := by
    obtain ⟨x, rfl⟩ : ∃ x, p = 7 + x := ⟨p - 7, by omega⟩
    obtain ⟨y_var, rfl⟩ : ∃ y_var, y = 9 + x + y_var := ⟨y - (9 + x), by omega⟩
    nlinarith
  omega

lemma no_sol_p_dvd_d (p m : ℕ) (hp5 : p ≥ 5) (hm : m ≥ p + 2) (hn800 : p^2 * m ≥ 800)
    (h_le : 3 * p^2 + 2 * p + 1 + 2 * m + 3 * (p * m) ≤ p^2 * m) : False := by
  by_cases hp6 : p ≥ 6
  · obtain ⟨x, rfl⟩ : ∃ x, p = 6 + x := ⟨p - 6, by omega⟩
    have h_sub : (6 + x) ^ 2 - 3 * (6 + x) - 2 = 16 + 9 * x + x * x := by
      have : (6 + x) ^ 2 = 36 + 12 * x + x * x := by ring
      rw [this]
      omega
    have h_add : (6 + x) ^ 2 * m = m * ((6 + x) ^ 2 - 3 * (6 + x) - 2) + 3 * (6 + x) * m + 2 * m := by
      rw [h_sub]
      ring
    have h_sub_eq : (6 + x) ^ 2 * m - 3 * (6 + x) * m - 2 * m = m * ((6 + x) ^ 2 - 3 * (6 + x) - 2) := by
      omega
    have h_m : m * ((6 + x) ^ 2 - 3 * (6 + x) - 2) ≥ (8 + x) * ((6 + x) ^ 2 - 3 * (6 + x) - 2) := by
      have : m ≥ 8 + x := by omega
      have : (6 + x) ^ 2 - 3 * (6 + x) - 2 ≥ 16 := by omega
      nlinarith
    have : 3 * (6 + x) ^ 2 + 2 * (6 + x) + 1 ≤ (6 + x) ^ 2 * m - 3 * (6 + x) * m - 2 * m := by omega
    rw [h_sub_eq] at this
    have h_final : 3 * (6 + x) ^ 2 + 2 * (6 + x) + 1 ≥ (8 + x) * ((6 + x) ^ 2 - 3 * (6 + x) - 2) := by
      omega
    rw [h_sub] at h_final
    nlinarith
  · have hp_eq : p = 5 := by omega
    subst hp_eq
    have hm32 : m ≥ 32 := by omega
    obtain ⟨m_var, rfl⟩ : ∃ m_var, m = 32 + m_var := ⟨m - 32, by omega⟩
    nlinarith

lemma test_prime_pow4 (p : ℕ) (hp : p.Prime) : (p ^ 4).properDivisors = {1, p, p ^ 2, p ^ 3} := by
  rw [properDivisors_prime_pow hp 4]
  ext x
  simp only [mem_map, mem_range, Function.Embedding.coeFn_mk, mem_insert, mem_singleton]
  constructor
  · rintro ⟨j, hj, rfl⟩
    interval_cases j
    · left; simp
    · right; left; simp
    · right; right; left; simp
    · right; right; right; simp
  · rintro (rfl | rfl | rfl | rfl)
    · use 0; simp
    · use 1; simp
    · use 2; simp
    · use 3; simp

lemma a_prime_four (p : ℕ) (hp : p.Prime) : a (p ^ 4) = 4 * p ^ 3 + 3 * p ^ 2 + 2 * p + 1 := by
  have hp_pos : 0 < p ^ 4 := Nat.pos_of_ne_zero (pow_ne_zero 4 hp.ne_zero)
  rw [properDivisors_sum (p ^ 4) hp_pos]
  rw [test_prime_pow4 p hp]
  have hp1 : 1 ≠ p := hp.one_lt.ne
  have hp2 : p ≠ p ^ 2 := by
    have : p > 1 := hp.one_lt
    nlinarith
  have hp3 : p ^ 2 ≠ p ^ 3 := by
    have : p > 1 := hp.one_lt
    nlinarith
  have hp12 : 1 ≠ p ^ 2 := by
    have : p ≥ 2 := hp.two_le
    have : p ^ 2 ≥ 4 := by
      calc
        p ^ 2 = p * p := sq p
        _ ≥ 2 * 2 := by nlinarith
    omega
  have hp13 : 1 ≠ p ^ 3 := by
    have : p ≥ 2 := hp.two_le
    have : p ^ 3 ≥ 8 := by
      calc
        p ^ 3 = p * p * p := by ring
        _ ≥ 2 * 2 * 2 := by nlinarith
    omega
  have hp23 : p ≠ p ^ 3 := by
    have : p > 1 := hp.one_lt
    nlinarith
  have h_not_mem1 : p ^ 2 ∉ ({p ^ 3} : Finset ℕ) := by simp [hp3]
  have h_not_mem2 : p ∉ ({p ^ 2, p ^ 3} : Finset ℕ) := by simp [hp2, hp23]
  have h_not_mem3 : 1 ∉ ({p, p ^ 2, p ^ 3} : Finset ℕ) := by simp [hp1, hp12, hp13]
  rw [sum_insert h_not_mem3]
  rw [sum_insert h_not_mem2]
  rw [sum_insert h_not_mem1]
  rw [sum_singleton]
  have h1 : (1 : ℕ).divisors.card = 1 := by decide
  have hp_div : p.divisors.card = 2 := by
    rw [hp.divisors]
    simp [hp1]
  have hp2_div : (p ^ 2).divisors.card = 3 := by
    rw [divisors_prime_pow hp 2]
    simp
  have hp3_div : (p ^ 3).divisors.card = 4 := by
    rw [divisors_prime_pow hp 3]
    simp
  rw [h1, hp_div, hp2_div, hp3_div]
  ring


lemma tau_d_eq_p_sub_1 (n p d : ℕ) (hn : 0 < n) (hp_prime : p.Prime) (hd_eq : n = p * d) (h_a : a n = n) (hd_ge : d ≥ p^2) (hp5 : p ≥ 5) :
    d.divisors.card = p - 1 := by
  generalize hC : d.divisors.card = C
  have hd_pos : 0 < d := by
    have : p ^ 2 > 0 := by positivity
    omega
  have h_tau : C < p := by
    have := tau_d_lt_p n p d hn hp_prime hd_eq h_a
    omega
  have h_prop : d ∈ n.properDivisors := by
    simp [Nat.mem_properDivisors]
    refine ⟨by use p; rw [mul_comm]; exact hd_eq, ?_⟩
    rw [hd_eq]
    have : p > 1 := hp_prime.one_lt
    calc
      d = 1 * d := by ring
      _ < p * d := Nat.mul_lt_mul_of_pos_right this hd_pos
  have h_prop_p : p ∈ n.properDivisors := by
    simp [Nat.mem_properDivisors]
    refine ⟨⟨d, hd_eq⟩, ?_⟩
    rw [hd_eq]
    have hd25 : d ≥ 25 := by nlinarith
    calc
      p = p * 1 := by ring
      _ < p * d := Nat.mul_lt_mul_of_pos_left (by omega) hp_prime.pos
  have h_prop1 : 1 ∈ n.properDivisors := by
    simp [Nat.mem_properDivisors]
    rw [hd_eq]
    have : p ≥ 2 := hp_prime.two_le
    nlinarith
  have h1p : 1 ≠ p := hp_prime.one_lt.ne
  have hd25 : d ≥ 25 := by nlinarith
  have h1d : 1 ≠ d := by omega
  have hpd : p ≠ d := by
    intro h_eq
    have hd_eq_p : d = p := h_eq.symm
    rw [hd_eq_p] at hd_ge
    have : p * p ≤ p := by
      rw [sq] at hd_ge
      exact hd_ge
    nlinarith
  have h_sub : ({1, p, d} : Finset ℕ) ⊆ n.properDivisors := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact h_prop1
    · exact h_prop_p
    · exact h_prop
  have h_sum_le : ∑ x ∈ ({1, p, d} : Finset ℕ), x * x.divisors.card ≤ ∑ x ∈ n.properDivisors, x * x.divisors.card :=
    Finset.sum_le_sum_of_subset h_sub
  have h_not_mem1 : (1:ℕ) ∉ ({p, d} : Finset ℕ) := by simp [h1p, h1d]
  have h_not_mem2 : p ∉ ({d} : Finset ℕ) := by simp [hpd]
  rw [sum_insert h_not_mem1, sum_insert h_not_mem2, sum_singleton] at h_sum_le
  have h_div1 : (1:ℕ).divisors.card = 1 := by decide
  have hp_div : p.divisors.card = 2 := by
    rw [hp_prime.divisors]
    simp [h1p]
  rw [h_div1, hp_div, hC] at h_sum_le
  have h_proper_sum : a n = ∑ x ∈ n.properDivisors, x * x.divisors.card := properDivisors_sum n hn
  rw [← h_proper_sum] at h_sum_le
  rw [h_a] at h_sum_le
  rw [hd_eq] at h_sum_le
  have h_le : d * C + 2 * p + 1 ≤ p * d := by omega
  have : p - C = 1 := by
    by_contra h_neq
    have h_pc : p - C ≥ 2 := by omega
    have h_le_diff : 2 * p + 1 ≤ (p - C) * d := by
      rw [Nat.sub_mul]
      rw [mul_comm d C] at h_le
      omega
    have h_contra : (p - C) * d > 2 * p + 1 := by
      have hd_ge_5p : d ≥ 5 * p := by
        have hsq : p * p = p ^ 2 := (sq p).symm
        have hd_ge' : d ≥ p * p := by
          rw [hsq]
          exact hd_ge
        calc
          d ≥ p * p := hd_ge'
          _ ≥ 5 * p := Nat.mul_le_mul_right p hp5
      nlinarith
    omega
  omega

lemma no_sol (q : ℕ) : 2 * q^2 ≠ 22 * q + 11 := by
  intro h
  have h_mod : (2 * q^2) % 2 = (22 * q + 11) % 2 := by rw [h]
  have h_lhs : (2 * q^2) % 2 = 0 := by
    rw [sq]
    omega
  have h_rhs : (22 * q + 11) % 2 = 1 := by
    omega
  rw [h_lhs, h_rhs] at h_mod
  omega

lemma a_ne_n_of_composite_large_p (n p d : ℕ) (hn : 0 < n) (hp_prime : p.Prime) (hd_eq : n = p * d) (h_a : a n = n) (hd_prime : ¬ d.Prime) (hd_ne_p2 : d ≠ p^2) : False := by
  have h_tau := tau_d_lt_p n p d hn hp_prime hd_eq h_a
  sorry


lemma d_ge_p_squared_of_composite (n p d : ℕ) (hn : 0 < n) (hp : p = n.minFac) (hd : d = n / p) (h_comp : ¬ d.Prime) (hd2 : d ≠ 1) :
    d ≥ p ^ 2 := by
  have hp_dvd : p ∣ n := by
    rw [hp]
    exact minFac_dvd n
  have hd_eq : n = p * d := by
    have : n = p * (n / p) := (Nat.mul_div_cancel' hp_dvd).symm
    rw [← hd] at this
    exact this
  have hd_pos : 0 < d := by
    by_contra h_zero
    have : d = 0 := by omega
    subst this
    rw [mul_zero] at hd_eq
    omega
  let q := d.minFac
  have hd_gt_1 : 1 < d := by
    have : d ≠ 0 := by omega
    omega
  have hq_prime : q.Prime := minFac_prime hd_gt_1.ne'
  have hq_dvd : q ∣ d := minFac_dvd d
  have hqd : d / q ≥ q := by
    exact minFac_le_div hd_pos h_comp
  have hq_dvd_n : q ∣ n := by
    have : d ∣ n := by
      rw [hd_eq]
      use p
      rw [mul_comm]
    exact dvd_trans hq_dvd this
  have hp_le_q : p ≤ q := by
    rw [hp]
    exact minFac_le_of_dvd hq_prime.one_lt hq_dvd_n
  have hp_le_dq : p ≤ d / q := le_trans hp_le_q hqd
  have h_eq : d = q * (d / q) := (Nat.mul_div_cancel' hq_dvd).symm
  rw [h_eq]
  have : q * (d / q) ≥ p * p := Nat.mul_le_mul hp_le_q hp_le_dq
  rw [sq]
  exact this


