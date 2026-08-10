import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A245211: $a(n) = \sum_{d \mid n, d < n} (d \cdot \tau(d))$, where $\tau(d)$ is the number of divisors of $d$.
It is computed as $\left(\sum_{d \mid n} d \cdot \tau(d)\right) - n \cdot \tau(n)$.
-/
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

lemma a_gt_of_even (n : ℕ) (heven : 2 ∣ n) (hgt : 21 < n) : a n > n := by
  have hn0 : 0 < n := by omega
  have hk : n / 2 ≥ 11 := by omega
  have h_eq_n : n = 2 * (n / 2) := (Nat.mul_div_cancel' heven).symm
  let k := n / 2
  have hk2 : 2 ≤ k := by omega
  have hk_divs : 2 ≤ k.divisors.card := card_divisors_ge_two k hk2
  have h1 : 1 ∈ n.properDivisors := by
    simp [Nat.mem_properDivisors]
    omega
  have h2 : 2 ∈ n.properDivisors := by
    simp [Nat.mem_properDivisors]
    exact ⟨heven, by omega⟩
  have hk_prop : k ∈ n.properDivisors := by
    simp [Nat.mem_properDivisors]
    have h_dvd : k ∣ n := by
      use 2
      rw [mul_comm]
      exact h_eq_n
    refine ⟨h_dvd, by omega⟩
  have h_sub : ({1, 2, k} : Finset ℕ) ⊆ n.properDivisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact hk_prop
  have h_sum_le : ∑ x ∈ ({1, 2, k} : Finset ℕ), x * x.divisors.card ≤ ∑ x ∈ n.properDivisors, x * x.divisors.card :=
    Finset.sum_le_sum_of_subset h_sub
  have h12 : (1:ℕ) ≠ 2 := by omega
  have h1k : (1:ℕ) ≠ k := by omega
  have h2k : (2:ℕ) ≠ k := by omega
  have h_sum_eq : ∑ x ∈ ({1, 2, k} : Finset ℕ), x * x.divisors.card =
      1 * (1:ℕ).divisors.card + 2 * (2:ℕ).divisors.card + k * k.divisors.card := by
    simp [h12, h1k, h2k]
    omega
  have h_div1 : (1:ℕ).divisors.card = 1 := by decide
  have h_div2 : (2:ℕ).divisors.card = 2 := by decide
  rw [properDivisors_sum n hn0]
  have h_calc : 1 * (1:ℕ).divisors.card + 2 * (2:ℕ).divisors.card + k * k.divisors.card ≥ 5 + n := by
    rw [h_div1, h_div2]
    have h_prod : k * k.divisors.card ≥ 2 * k := by
      nlinarith
    omega
  omega

lemma a_of_prime (n : ℕ) (hp : n.Prime) : a n = 1 := by
  have hn0 : 0 < n := hp.pos
  rw [properDivisors_sum n hn0]
  rw [hp.properDivisors]
  simp

lemma test_prime_pow (p : ℕ) (hp : p.Prime) : (p ^ 2).properDivisors = {1, p} := by
  rw [properDivisors_prime_pow hp 2]
  ext x
  simp only [mem_map, mem_range, Function.Embedding.coeFn_mk, mem_insert, mem_singleton]
  constructor
  · rintro ⟨j, hj, rfl⟩
    interval_cases j
    · left; simp
    · right; simp
  · rintro (rfl | rfl)
    · use 0
      simp
    · use 1
      simp

lemma a_prime_sq (p : ℕ) (hp : p.Prime) : a (p ^ 2) = 2 * p + 1 := by
  have hp_pos : 0 < p ^ 2 := Nat.pos_of_ne_zero (pow_ne_zero 2 hp.ne_zero)
  rw [properDivisors_sum (p ^ 2) hp_pos]
  rw [test_prime_pow p hp]
  have hp1 : 1 ≠ p := hp.one_lt.ne
  have h_not_mem : 1 ∉ ({p} : Finset ℕ) := by simp [hp1]
  rw [sum_insert h_not_mem]
  rw [sum_singleton]
  have h1 : (1 : ℕ).divisors.card = 1 := by decide
  have hp_div : p.divisors.card = 2 := by
    rw [hp.divisors]
    simp [hp1]
  rw [h1, hp_div]
  omega

lemma properDivisors_prime_mul (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    (p * q).properDivisors = {1, p, q} := by
  ext x
  simp only [mem_properDivisors, mem_insert, mem_singleton]
  have hpq_ne : p * q ≠ 0 := by
    apply mul_ne_zero hp.ne_zero hq.ne_zero
  constructor
  · rintro ⟨h_dvd, h_lt⟩
    have h_dvd' : x ∣ p * q := h_dvd
    rcases coprime_or_dvd_of_prime hp x with hpx | hpx
    · have hxp : Nat.Coprime x p := hpx.symm
      have : x ∣ q := hxp.dvd_of_dvd_mul_left h_dvd'
      rcases hq.eq_one_or_self_of_dvd x this with rfl | rfl
      · left; rfl
      · right; right; rfl
    · rcases hpx with ⟨y, rfl⟩
      have : p * y ∣ p * q := h_dvd'
      have hy : y ∣ q := (mul_dvd_mul_iff_left hp.ne_zero).mp this
      rcases hq.eq_one_or_self_of_dvd y hy with rfl | rfl
      · right; left; simp
      · omega
  · rintro (rfl | rfl | rfl)
    · refine ⟨one_dvd _, ?_⟩
      have : 1 < p * q := by
        have : 2 ≤ p := hp.two_le
        have : 2 ≤ q := hq.two_le
        nlinarith
      omega
    · refine ⟨dvd_mul_right _ _, ?_⟩
      have : x * 1 < x * q := Nat.mul_lt_mul_of_pos_left hq.one_lt hp.pos
      simpa using this
    · refine ⟨dvd_mul_left _ _, ?_⟩
      have : 1 * x < p * x := Nat.mul_lt_mul_of_pos_right hp.one_lt hq.pos
      simpa using this

lemma a_prime_mul (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    a (p * q) = 2 * p + 2 * q + 1 := by
  have hpq_pos : 0 < p * q := mul_pos hp.pos hq.pos
  rw [properDivisors_sum (p * q) hpq_pos]
  rw [properDivisors_prime_mul p q hp hq hpq]
  have h1 : 1 ≠ p := hp.one_lt.ne
  have h2 : 1 ≠ q := hq.one_lt.ne
  have h3 : p ≠ q := hpq.ne
  have h_not_mem1 : p ∉ ({q} : Finset ℕ) := by simp [h3]
  have h_not_mem2 : 1 ∉ ({p, q} : Finset ℕ) := by simp [h1, h2]
  rw [sum_insert h_not_mem2]
  rw [sum_insert h_not_mem1]
  rw [sum_singleton]
  have h1_div : (1 : ℕ).divisors.card = 1 := by decide
  have hp_div : p.divisors.card = 2 := by
    rw [hp.divisors]
    simp [h1]
  have hq_div : q.divisors.card = 2 := by
    rw [hq.divisors]
    simp [h2]
  rw [h1_div, hp_div, hq_div]
  omega

lemma test_algebra_false (p q : ℕ) (hp3 : 3 ≤ p) (hq3 : 3 ≤ q) (hpq : p < q)
    (h_eq : p * q = 2 * p + 2 * q + 1) (h_gt : p * q > 21) : False := by
  let A := p - 2
  let B := q - 2
  have hp_eq : p = A + 2 := by omega
  have hq_eq : q = B + 2 := by omega
  have h_ring : p * q = A * B + 2 * A + 2 * B + 4 := by
    rw [hp_eq, hq_eq]
    ring
  have h_ring2 : 2 * p + 2 * q + 1 = 2 * A + 2 * B + 9 := by
    rw [hp_eq, hq_eq]
    ring
  rw [h_eq] at h_ring
  rw [h_ring2] at h_ring
  have h_AB : A * B = 5 := by omega
  have h_lt : A < B := by omega
  have hA : A = 1 := by
    by_contra h_not
    have h_cases : A = 0 ∨ A ≥ 2 := by omega
    rcases h_cases with hA0 | hA2
    · rw [hA0] at h_AB
      simp at h_AB
    · have hB3 : B ≥ 3 := by omega
      have h_prod_ge : A * B ≥ 6 := by nlinarith
      omega
  rw [hA] at h_AB
  simp only [one_mul] at h_AB
  have hp3' : p = 3 := by omega
  have hq7 : q = 7 := by omega
  omega

lemma card_divisors_composite_ge_three (d : ℕ) (hd2 : 2 ≤ d) (hd_comp : ¬ d.Prime) :
    3 ≤ d.divisors.card := by
  have h_exists := exists_dvd_of_not_prime hd2 hd_comp
  rcases h_exists with ⟨k, hk_dvd, hk1, hkd⟩
  have h1 : 1 ∈ d.divisors := by
    simp only [mem_divisors]
    refine ⟨one_dvd d, by omega⟩
  have hk : k ∈ d.divisors := Nat.mem_divisors.mpr ⟨hk_dvd, by omega⟩
  have hd : d ∈ d.divisors := Nat.mem_divisors_self d (by omega)
  have h1k : 1 ≠ k := hk1.symm
  have h1d : 1 ≠ d := by omega
  have hkd' : k ≠ d := hkd
  have h_sub : ({1, k, d} : Finset ℕ) ⊆ d.divisors := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact h1
    · exact hk
    · exact hd
  have h_card := card_le_card h_sub
  have h_card3 : ({1, k, d} : Finset ℕ).card = 3 := by
    simp [h1k, h1d, hkd']
  omega

set_option maxRecDepth 200000
set_option maxHeartbeats 0

lemma a_eq_n_iff_eq_21_1 : ∀ n < 150, 0 < n → (a n = n ↔ n = 21) := by
  decide

lemma a_eq_n_iff_eq_21_2 : ∀ n < 300, 150 ≤ n → a n ≠ n := by
  decide

lemma a_eq_n_iff_eq_21_3 : ∀ n < 450, 300 ≤ n → a n ≠ n := by
  decide

lemma a_eq_n_iff_eq_21_4 : ∀ n < 600, 450 ≤ n → a n ≠ n := by
  decide

lemma a_eq_n_iff_eq_21_5 : ∀ n < 700, 600 ≤ n → a n ≠ n := by
  decide

lemma a_eq_n_iff_eq_21_6 : ∀ n < 800, 700 ≤ n → a n ≠ n := by
  decide

lemma a_eq_n_iff_eq_21 : ∀ n < 800, 0 < n → (a n = n ↔ n = 21) := by
  intro n hn hn0
  by_cases h150 : n < 150
  · exact a_eq_n_iff_eq_21_1 n h150 hn0
  · have hn_ge : 150 ≤ n := by omega
    by_cases h300 : n < 300
    · have h_neq := a_eq_n_iff_eq_21_2 n h300 hn_ge
      constructor <;> intro h_eq
      · contradiction
      · subst h_eq; omega
    · have hn_ge300 : 300 ≤ n := by omega
      by_cases h450 : n < 450
      · have h_neq := a_eq_n_iff_eq_21_3 n h450 hn_ge300
        constructor <;> intro h_eq
        · contradiction
        · subst h_eq; omega
      · have hn_ge450 : 450 ≤ n := by omega
        by_cases h600 : n < 600
        · have h_neq := a_eq_n_iff_eq_21_4 n h600 hn_ge450
          constructor <;> intro h_eq
          · contradiction
          · subst h_eq; omega
        · have hn_ge600 : 600 ≤ n := by omega
          by_cases h700 : n < 700
          · have h_neq := a_eq_n_iff_eq_21_5 n h700 hn_ge600
            constructor <;> intro h_eq
            · contradiction
            · subst h_eq; omega
          · have hn_ge700 : 700 ≤ n := by omega
            have h_neq := a_eq_n_iff_eq_21_6 n hn hn_ge700
            constructor <;> intro h_eq
            · contradiction
            · subst h_eq; omega

lemma test_prime_pow3 (p : ℕ) (hp : p.Prime) : (p ^ 3).properDivisors = {1, p, p ^ 2} := by
  rw [properDivisors_prime_pow hp 3]
  ext x
  simp only [mem_map, mem_range, Function.Embedding.coeFn_mk, mem_insert, mem_singleton]
  constructor
  · rintro ⟨j, hj, rfl⟩
    interval_cases j
    · left; simp
    · right; left; simp
    · right; right; simp
  · rintro (rfl | rfl | rfl)
    · use 0; simp
    · use 1; simp
    · use 2; simp

lemma a_prime_cube (p : ℕ) (hp : p.Prime) : a (p ^ 3) = 3 * p ^ 2 + 2 * p + 1 := by
  have hp_pos : 0 < p ^ 3 := Nat.pos_of_ne_zero (pow_ne_zero 3 hp.ne_zero)
  rw [properDivisors_sum (p ^ 3) hp_pos]
  rw [test_prime_pow3 p hp]
  have hp1 : 1 ≠ p := hp.one_lt.ne
  have hp2 : p ≠ p ^ 2 := by
    have : p > 1 := hp.one_lt
    nlinarith
  have hp12 : 1 ≠ p ^ 2 := by
    have : p > 1 := hp.one_lt
    nlinarith
  have h_not_mem1 : p ∉ ({p ^ 2} : Finset ℕ) := by simp [hp2]
  have h_not_mem2 : 1 ∉ ({p, p ^ 2} : Finset ℕ) := by simp [hp1, hp12]
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
  rw [h1, hp_div, hp2_div]
  ring

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


/-- A245211 Conjecture: 21 is only number such that a(n) = n. -/

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
  have h4 : 4 * y * y > 4 * p * y + 2 * p + 2 * y + 1 := by
    obtain ⟨x, h_eq_p⟩ : ∃ x, p = 7 + x := ⟨p - 7, by omega⟩
    rw [h_eq_p] at *
    obtain ⟨y_var, h_eq_y⟩ : ∃ y_var, y = 9 + x + y_var := ⟨y - (9 + x), by omega⟩
    rw [h_eq_y] at *
    nlinarith
  linarith

lemma no_sol_p_dvd_d (p m : ℕ) (hp6 : p ≥ 6) (hm : m ≥ p + 2) (hn800 : p^2 * m ≥ 800)
    (h_le : 3 * p^2 + 2 * p + 1 + 2 * m + 3 * (p * m) ≤ p^2 * m) : False := by
  obtain ⟨x, rfl⟩ : ∃ x, p = 6 + x := ⟨p - 6, by omega⟩
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
  have : 3 * (6 + x) ^ 2 + 2 * (6 + x) + 1 ≤ (6 + x) ^ 2 * m - 3 * (6 + x) * m - 2 * m := by linarith
  rw [h_sub_eq] at this
  have h_final : 3 * (6 + x) ^ 2 + 2 * (6 + x) + 1 ≥ (8 + x) * ((6 + x) ^ 2 - 3 * (6 + x) - 2) := by nlinarith
  rw [h_sub] at h_final
  nlinarith

lemma no_sol_p5_p_dvd_d (m : ℕ) (hm_prime : m.Prime) (h_eq : 86 + 22 * m = 25 * m) : False := by
  have : 86 = 3 * m := by omega
  have h_mod : 86 % 3 = (3 * m) % 3 := by rw [this]
  omega


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

lemma d_composite_contradiction (n p d : ℕ) (hn : 0 < n) (hp_prime : p.Prime) (hd_eq : n = p * d) (h_a : a n = n) (hd_prime : ¬ d.Prime) (hd_ne_p2 : d ≠ p^2) (hp5 : p ≥ 5) (hn800 : n ≥ 800) (h_odd : ¬ 2 ∣ n) (hp : p = n.minFac) (hd : d = n / p) : False := by
  have hd2 : d ≠ 1 := by
    intro h1
    rw [h1, mul_one] at hd_eq
    have : a p = 1 := a_of_prime p hp_prime
    rw [hd_eq] at h_a
    omega
  have hd_ge_p2 := d_ge_p_squared_of_composite n p d hn hp hd hd_prime hd2
  have h_tau := tau_d_lt_p n p d hn hp_prime hd_eq h_a
  by_cases h_pdvd : p ∣ d
  · obtain ⟨m, hd_eq_pm⟩ : ∃ m, d = p * m := h_pdvd
    have hm_pos : m > 0 := by
      by_contra h_zero
      have : m = 0 := by omega
      subst this
      rw [hd_eq_pm, mul_zero] at hd_eq
      omega
    have hm_ne_1 : m ≠ 1 := by
      intro h1
      subst h1
      rw [hd_eq_pm, mul_one] at hd_prime
      contradiction
    have hm_ne_p : m ≠ p := by
      intro hp_eq
      subst hp_eq
      rw [hd_eq_pm, ← sq] at hd_ne_p2
      contradiction
    have hm_ge_p : m ≥ p := by
      by_contra h_lt
      have h_gt_1 : 1 < m := by omega
      let r := m.minFac
      have hr_prime : r.Prime := minFac_prime h_gt_1.ne'
      have hr_dvd_m : r ∣ m := minFac_dvd m
      have hr_dvd_n : r ∣ n := by
        have : m ∣ n := by
          use p * p
          rw [hd_eq]
          ring
        exact dvd_trans hr_dvd_m this
      have hp_le_r : p ≤ r := by
        have : p = n.minFac := hp
        rw [this]
        exact minFac_le_of_dvd hr_prime.one_lt hr_dvd_n
      have : r ≤ m := Nat.le_of_dvd hm_pos hr_dvd_m
      omega
    have hm_ne_p1 : m ≠ p + 1 := by
      intro hp1
      have h_even_m : 2 ∣ m := by
        rw [hp1]
        have hp_odd : p % 2 = 1 := by
          rcases hp_prime.eq_two_or_odd with h2 | h_odd
          · rw [h2] at hp5; contradiction
          · exact h_odd
        omega
      have h_even_n : 2 ∣ n := by
        rw [hd_eq]
        rcases h_even_m with ⟨k, rfl⟩
        use p * p * k
        ring
      contradiction
    have hm_ge_p2 : m ≥ p + 2 := by omega
    by_cases hm_p2 : m = p^2
    · subst hm_p2
      have h_a_pow4 := a_prime_four p hp_prime
      have hn_pow4 : n = p ^ 4 := by
        rw [hd_eq]
        ring
      rw [hn_pow4] at h_a
      rw [h_a_pow4] at h_a
      obtain ⟨x, rfl⟩ : ∃ x, p = 5 + x := ⟨p - 5, by omega⟩
      nlinarith
    · have h_prop1 : 1 ∈ n.properDivisors := by
        simp [Nat.mem_properDivisors, (by omega : 1 < n)]
      have h_propp : p ∈ n.properDivisors := by
        simp [Nat.mem_properDivisors]
        refine ⟨⟨d, hd_eq⟩, ?_⟩
        rw [hd_eq]
        have : d ≥ 25 := by omega
        calc
          p = p * 1 := by ring
          _ < p * d := Nat.mul_lt_mul_of_pos_left (by omega) hp_prime.pos
      have h_propp2 : p^2 ∈ n.properDivisors := by
        simp [Nat.mem_properDivisors]
        refine ⟨⟨m, ?_⟩, ?_⟩
        · rw [hd_eq]
          ring
        · rw [hd_eq]
          have : m ≥ 27 := by omega
          calc
            p^2 = p^2 * 1 := by ring
            _ < p^2 * m := Nat.mul_lt_mul_of_pos_left (by omega) (by positivity)
      have h_propm : m ∈ n.properDivisors := by
        simp [Nat.mem_properDivisors]
        refine ⟨⟨p^2, ?_⟩, ?_⟩
        · rw [hd_eq]
          ring
        · rw [hd_eq]
          have : m < p^2 * m := by
            have : p^2 > 1 := by positivity
            calc
              m = 1 * m := by ring
              _ < p^2 * m := Nat.mul_lt_mul_of_pos_right this hm_pos
          exact this
      have h_propd : d ∈ n.properDivisors := by
        simp [Nat.mem_properDivisors]
        refine ⟨⟨p, by rw [mul_comm, ← hd_eq]⟩, ?_⟩
        rw [hd_eq]
        have : p > 1 := hp_prime.one_lt
        calc
          d = 1 * d := by ring
          _ < p * d := Nat.mul_lt_mul_of_pos_right this (by omega)
      have h_sub : ({1, p, p^2, m, d} : Finset ℕ) ⊆ n.properDivisors := by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl
        · exact h_prop1
        · exact h_propp
        · exact h_propp2
        · exact h_propm
        · exact h_propd
      have h_sum_le : ∑ x ∈ ({1, p, p^2, m, d} : Finset ℕ), x * x.divisors.card ≤ ∑ x ∈ n.properDivisors, x * x.divisors.card :=
        Finset.sum_le_sum_of_subset h_sub
      have h_lt1 : 1 < p := hp_prime.one_lt
      have h_lt2 : p < p^2 := by
        have : p > 1 := hp_prime.one_lt
        nlinarith
      have h_lt3 : p^2 < m := by omega
      have h_lt4 : m < d := by
        have : p > 1 := hp_prime.one_lt
        calc
          m = 1 * m := by ring
          _ < p * m := Nat.mul_lt_mul_of_pos_right this hm_pos
      have h1p : 1 ≠ p := h_lt1.ne'
      have h1p2 : 1 ≠ p^2 := by omega
      have h1m : 1 ≠ m := by omega
      have h1d : 1 ≠ d := by omega
      have hpp2 : p ≠ p^2 := h_lt2.ne'
      have hpm : p ≠ m := by omega
      have hpd : p ≠ d := by omega
      have hp2m : p^2 ≠ m := h_lt3.ne'
      have hp2d : p^2 ≠ d := by omega
      have hmd : m ≠ d := h_lt4.ne'
      have h_not_mem1 : (1:ℕ) ∉ ({p, p^2, m, d} : Finset ℕ) := by
        simp only [mem_insert, mem_singleton]
        omega
      have h_not_mem2 : p ∉ ({p^2, m, d} : Finset ℕ) := by
        simp only [mem_insert, mem_singleton]
        omega
      have h_not_mem3 : p^2 ∉ ({m, d} : Finset ℕ) := by
        simp only [mem_insert, mem_singleton]
        omega
      have h_not_mem4 : m ∉ ({d} : Finset ℕ) := by
        simp only [mem_insert, mem_singleton]
        omega
      rw [sum_insert h_not_mem1, sum_insert h_not_mem2, sum_insert h_not_mem3, sum_insert h_not_mem4, sum_singleton] at h_sum_le
      have h_div1 : (1:ℕ).divisors.card = 1 := by decide
      have hp_div : p.divisors.card = 2 := by
        rw [hp_prime.divisors]
        simp [h1p]
      have hp2_div : (p^2).divisors.card = 3 := by
        rw [divisors_prime_pow hp_prime 2]
        simp
      have hm_div : m.divisors.card ≥ 2 := card_divisors_ge_two m (by omega)
      have hd_div : d.divisors.card ≥ 3 := card_divisors_composite_ge_three d (by omega) hd_prime
      have h_proper_sum : a n = ∑ x ∈ n.properDivisors, x * x.divisors.card := properDivisors_sum n hn
      rw [← h_proper_sum] at h_sum_le
      rw [h_a] at h_sum_le
      rw [hd_eq] at h_sum_le
      have h_lhs_le : 3 * p^2 + 2 * p + 1 + 2 * m + 3 * (p * m) ≤ 1 * 1 + p * 2 + p^2 * 3 + m * m.divisors.card + d * d.divisors.card := by
        rw [hd_eq_pm]
        nlinarith
      have h_final_le : 3 * p^2 + 2 * p + 1 + 2 * m + 3 * (p * m) ≤ p^2 * m := by
        omega
      by_cases hp6 : p ≥ 6
      · exact no_sol_p_dvd_d p m hp6 hm_ge_p2 hn800 h_final_le
      · have hp5_eq : p = 5 := by omega
        rw [hp5_eq] at *
        have hm32 : m ≥ 32 := by omega
        have hd_div4 : d.divisors.card ≥ 4 := by
          have h_sub_div : ({1, 5, m, 5 * m} : Finset ℕ) ⊆ d.divisors := by
            intro x hx
            simp only [mem_insert, mem_singleton] at hx
            rcases hx with rfl | rfl | rfl | rfl
            · simp [hd_pos]
            · simp [hd_pos]
            · simp [hd_pos]
            · simp [hd_pos]
          have h15 : (1:ℕ) ≠ 5 := by decide
          have h1m : (1:ℕ) ≠ m := by omega
          have h15m : (1:ℕ) ≠ 5 * m := by omega
          have h5m : (5:ℕ) ≠ m := by omega
          have h55m : (5:ℕ) ≠ 5 * m := by omega
          have hm5m : m ≠ 5 * m := by omega
          have h_card4 : ({1, 5, m, 5 * m} : Finset ℕ).card = 4 := by
            have h_not_mem1 : (1:ℕ) ∉ ({5, m, 5 * m} : Finset ℕ) := by
              simp only [mem_insert, mem_singleton]
              omega
            have h_not_mem2 : (5:ℕ) ∉ ({m, 5 * m} : Finset ℕ) := by
              simp only [mem_insert, mem_singleton]
              omega
            have h_not_mem3 : m ∉ ({5 * m} : Finset ℕ) := by
              simp only [mem_insert, mem_singleton]
              omega
            rw [card_insert_of_notMem h_not_mem1]
            rw [card_insert_of_notMem h_not_mem2]
            rw [card_insert_of_notMem h_not_mem3]
            simp
          have h_le_card := card_le_card h_sub_div
          omega
        have h_lhs_le_5 : 86 + 22 * m ≤ 1 * 1 + 5 * 2 + 25 * 3 + m * m.divisors.card + d * d.divisors.card := by
          have : d = 5 * m := by omega
          rw [this]
          nlinarith
        omega
  · have h_tau := tau_d_lt_p n p d hn hp_prime hd_eq h_a
    let y := d.minFac
    have hd_gt_1 : 1 < d := by omega
    have hy_prime : y.Prime := minFac_prime hd_gt_1.ne'
    have hy_dvd : y ∣ d := minFac_dvd d
    have hy_ne_p : y ≠ p := by
      intro h_eq
      subst h_eq
      contradiction
    have hy_gt_p : y > p := by
      have : y ≥ p := by
        have : p = n.minFac := hp
        rw [this]
        have : y ∣ n := by
          have : d ∣ n := by
            use p
            rw [mul_comm, ← hd_eq]
          exact dvd_trans hy_dvd this
        exact minFac_le_of_dvd hy_prime.one_lt this
      omega
    have hy_ge : y ≥ p + 2 := by
      have hp_odd : p % 2 = 1 := by
        rcases hp_prime.eq_two_or_odd with h2 | h_odd
        · rw [h2] at hp5; contradiction
        · exact h_odd
      have hy_odd : y % 2 = 1 := by
        rcases hy_prime.eq_two_or_odd with h2 | h_odd
        · rw [h2] at hy_gt_p; omega
        · exact h_odd
      omega
    let m := d / y
    have hm_pos : m > 0 := Nat.div_pos (Nat.minFac_le_self d) hy_prime.pos
    have hm_ge_y : m ≥ y := by
      exact minFac_le_div (by omega) hd_prime
    have h_prop1 : 1 ∈ n.properDivisors := by simp [Nat.mem_properDivisors, (by omega : 1 < n)]
    have h_propp : p ∈ n.properDivisors := by
      simp [Nat.mem_properDivisors]
      refine ⟨⟨d, hd_eq⟩, ?_⟩
      rw [hd_eq]
      calc
        p = p * 1 := by ring
        _ < p * d := Nat.mul_lt_mul_of_pos_left (by omega) hp_prime.pos
    have h_propy : y ∈ n.properDivisors := by
      simp [Nat.mem_properDivisors]
      refine ⟨⟨p * m, ?_⟩, ?_⟩
      · rw [hd_eq]
        have : d = y * m := (Nat.mul_div_cancel' hy_dvd).symm
        rw [this]
        ring
      · rw [hd_eq]
        have : d = y * m := (Nat.mul_div_cancel' hy_dvd).symm
        rw [this]
        have : p * m ≥ 5 * 7 := by nlinarith
        calc
          y = y * 1 := by ring
          _ < y * (p * m) := Nat.mul_lt_mul_of_pos_left (by omega) hy_prime.pos
    have h_proppy : p * y ∈ n.properDivisors := by
      simp [Nat.mem_properDivisors]
      refine ⟨⟨m, ?_⟩, ?_⟩
      · rw [hd_eq]
        have : d = y * m := (Nat.mul_div_cancel' hy_dvd).symm
        rw [this]
        ring
      · rw [hd_eq]
        have : d = y * m := (Nat.mul_div_cancel' hy_dvd).symm
        rw [this]
        have : p * y * m > p * y * 1 := Nat.mul_lt_mul_of_pos_left hm_pos (by positivity)
        simpa using this
    have h_propd : d ∈ n.properDivisors := by
      simp [Nat.mem_properDivisors]
      refine ⟨⟨p, by rw [mul_comm, ← hd_eq]⟩, ?_⟩
      rw [hd_eq]
      have : p > 1 := hp_prime.one_lt
      calc
        d = 1 * d := by ring
        _ < p * d := Nat.mul_lt_mul_of_pos_right this (by omega)
    have h_sub : ({1, p, y, p * y, d} : Finset ℕ) ⊆ n.properDivisors := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact h_prop1
      · exact h_propp
      · exact h_propy
      · exact h_proppy
      · exact h_propd
    have h_sum_le : ∑ x ∈ ({1, p, y, p * y, d} : Finset ℕ), x * x.divisors.card ≤ ∑ x ∈ n.properDivisors, x * x.divisors.card :=
      Finset.sum_le_sum_of_subset h_sub
    have h_lt1 : 1 < p := hp_prime.one_lt
    have h_lt2 : p < y := hy_gt_p
    have h_lt3 : y < p * y := by
      have : p > 1 := hp_prime.one_lt
      calc
        y = 1 * y := by ring
        _ < p * y := Nat.mul_lt_mul_of_pos_right this hy_prime.pos
    have h_lt4 : p * y < d := by
      have : d = y * m := (Nat.mul_div_cancel' hy_dvd).symm
      rw [this]
      have : p < m := by omega
      calc
        p * y = y * p := by ring
        _ < y * m := Nat.mul_lt_mul_of_pos_left this hy_prime.pos
    have h1p : 1 ≠ p := h_lt1.ne'
    have h1y : 1 ≠ y := by omega
    have h1py : 1 ≠ p * y := by
      have : p * y ≥ 4 := by
        calc
          p * y ≥ 2 * 2 := Nat.mul_le_mul hp_prime.two_le hy_prime.two_le
          _ = 4 := rfl
      omega
    have h1d : 1 ≠ d := by omega
    have hpy : p ≠ y := h_lt2.ne'
    have hppy : p ≠ p * y := by
      have : p < p * y := by
        calc
          p = p * 1 := by ring
          _ < p * y := Nat.mul_lt_mul_of_pos_left hy_prime.one_lt hp_prime.pos
      omega
    have hpd : p ≠ d := by omega
    have hypy : y ≠ p * y := by
      have : y < p * y := by
        calc
          y = 1 * y := by ring
          _ < p * y := Nat.mul_lt_mul_of_pos_right hp_prime.one_lt hy_prime.pos
      omega
    have hyd : y ≠ d := by omega
    have hpyd : p * y ≠ d := h_lt4.ne'
    have h_not_mem1 : (1:ℕ) ∉ ({p, y, p * y, d} : Finset ℕ) := by
      simp only [mem_insert, mem_singleton]
      omega
    have h_not_mem2 : p ∉ ({y, p * y, d} : Finset ℕ) := by
      simp only [mem_insert, mem_singleton]
      omega
    have h_not_mem3 : y ∉ ({p * y, d} : Finset ℕ) := by
      simp only [mem_insert, mem_singleton]
      omega
    have h_not_mem4 : p * y ∉ ({d} : Finset ℕ) := by
      simp only [mem_insert, mem_singleton]
      omega
    rw [sum_insert h_not_mem1, sum_insert h_not_mem2, sum_insert h_not_mem3, sum_insert h_not_mem4, sum_singleton] at h_sum_le
    have h_div1 : (1:ℕ).divisors.card = 1 := by decide
    have hp_div : p.divisors.card = 2 := by
      rw [hp_prime.divisors]
      simp [h1p]
    have hy_div : y.divisors.card = 2 := by
      rw [hy_prime.divisors]
      simp [h1y]
    have hpy_div : (p * y).divisors.card ≥ 4 := by
      have hp1_prime : 1 ≠ p := h1p
      have hy1_prime : 1 ≠ y := h1y
      have hpqy : p ≠ y := hpy
      have h_divs : ({1, p, y, p * y} : Finset ℕ) ⊆ (p * y).divisors := by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · simp
        · simp [hp_prime]
        · simp [hy_prime]
        · simp
      have h_card := card_le_card h_divs
      have h_card4 : ({1, p, y, p * y} : Finset ℕ).card = 4 := by
        have h_not_mem1 : (1:ℕ) ∉ ({p, y, p * y} : Finset ℕ) := by
          simp only [mem_insert, mem_singleton]
          omega
        have h_not_mem2 : p ∉ ({y, p * y} : Finset ℕ) := by
          simp only [mem_insert, mem_singleton]
          omega
        have h_not_mem3 : y ∉ ({p * y} : Finset ℕ) := by
          simp only [mem_insert, mem_singleton]
          omega
        rw [card_insert_of_notMem h_not_mem1]
        rw [card_insert_of_notMem h_not_mem2]
        rw [card_insert_of_notMem h_not_mem3]
        simp
      omega
    have hd_div : d.divisors.card ≥ 3 := card_divisors_composite_ge_three d (by omega) hd_prime
    have h_proper_sum : a n = ∑ x ∈ n.properDivisors, x * x.divisors.card := properDivisors_sum n hn
    rw [← h_proper_sum] at h_sum_le
    rw [h_a] at h_sum_le
    rw [hd_eq] at h_sum_le
    have h_lhs_le : 4 * p * y + 3 * (y * m) + 2 * p + 2 * y + 1 ≤ 1 * 1 + p * 2 + y * 2 + (p * y) * (p * y).divisors.card + d * d.divisors.card := by
      have : d = y * m := (Nat.mul_div_cancel' hy_dvd).symm
      rw [this]
      nlinarith
    have h_final_le : 4 * p * y + 3 * (y * m) + 2 * p + 2 * y + 1 ≤ p * y * m := by
      have : d = y * m := (Nat.mul_div_cancel' hy_dvd).symm
      rw [this] at h_sum_le
      omega
    exact no_sol_coprime p y m hp5 hy_ge hm_ge_y h_final_le

theorem oeis_245211_conjecture_0 : ∀ n : ℕ, 0 < n → (a n = n ↔ n = 21) := by
  intro n hn
  by_cases hn800 : n < 800
  · exact a_eq_n_iff_eq_21 n hn800 hn
  · constructor
    · intro h
      exfalso
      have hgt : 21 < n := by omega
      by_cases h_even : 2 ∣ n
      · have h_gt_even := a_gt_of_even n h_even hgt
        omega
      · by_cases hp : n.Prime
        · have h_prime := a_of_prime n hp
          omega
        · -- here we have n ≥ 800
          -- and h_even : ¬ (2 ∣ n) (odd)
          -- and hp : ¬ n.Prime (composite)
          let p := n.minFac
          have hn1 : n ≠ 1 := by omega
          have hp_prime : p.Prime := minFac_prime hn1
          have hp_dvd : p ∣ n := minFac_dvd n
          let d := n / p
          have hd_eq : n = p * d := (Nat.mul_div_cancel' hp_dvd).symm
          have hp_odd : p ≠ 2 := by
            intro h2
            rw [h2] at hp_dvd
            contradiction
          have hp3 : 3 ≤ p := by
            have : 2 ≤ p := hp_prime.two_le
            omega
          have hd_ge : d ≥ p := minFac_le_div (by omega) hp
          by_cases hdp : d = p
          · have hp_sq : n = p ^ 2 := by
              rw [hdp] at hd_eq
              rw [hd_eq]
              ring
            have hp_gt_11 : p ≥ 11 := by
              by_contra hp_lt
              have : p < 11 := by omega
              have : p ^ 2 < 121 := by nlinarith
              omega
            have h_a_sq := a_prime_sq p hp_prime
            rw [← hp_sq] at h_a_sq
            rw [h_a_sq] at h
            nlinarith
          · have hd_gt : d > p := by omega
            by_cases hd_prime : d.Prime
            · have h_prime_mul := a_prime_mul p d hp_prime hd_prime hd_gt
              rw [← hd_eq] at h_prime_mul
              have h_algebra_false := test_algebra_false p d hp3 (by omega) hd_gt (by rw [← h_prime_mul, h, hd_eq]) (by omega)
              exact h_algebra_false
            · -- d is composite
              by_cases hp3_eq : p = 3
              · rw [hp3_eq] at hd_eq hp_dvd
                have hn0_pos : 0 < n := by omega
                rw [properDivisors_sum n hn0_pos] at h
                have h1 : 1 ∈ n.properDivisors := by simp [Nat.mem_properDivisors, (by omega : 1 < n)]
                have hp_prop : 3 ∈ n.properDivisors := by simp [Nat.mem_properDivisors, hp_dvd, (by omega : 3 < n)]
                have hd_prop : d ∈ n.properDivisors := by
                  simp [Nat.mem_properDivisors]
                  refine ⟨⟨3, by rw [mul_comm, ← hd_eq]⟩, ?_⟩
                  have : d < n := by
                    rw [hd_eq]
                    omega
                  exact this
                have h_sub : ({1, 3, d} : Finset ℕ) ⊆ n.properDivisors := by
                  intro x hx
                  simp only [mem_insert, mem_singleton] at hx
                  rcases hx with rfl | rfl | rfl
                  · exact h1
                  · exact hp_prop
                  · exact hd_prop
                have h_sum_le : ∑ x ∈ ({1, 3, d} : Finset ℕ), x * x.divisors.card ≤ ∑ x ∈ n.properDivisors, x * x.divisors.card :=
                  Finset.sum_le_sum_of_subset h_sub
                have h13 : (1:ℕ) ≠ 3 := by omega
                have h1d : (1:ℕ) ≠ d := by omega
                have h3d : (3:ℕ) ≠ d := by omega
                have h_sum_eq : ∑ x ∈ ({1, 3, d} : Finset ℕ), x * x.divisors.card =
                    1 * (1:ℕ).divisors.card + 3 * (3:ℕ).divisors.card + d * d.divisors.card := by
                  simp [h13, h1d, h3d]
                  omega
                have h_div1 : (1:ℕ).divisors.card = 1 := by decide
                have h_div3 : (3:ℕ).divisors.card = 2 := by decide
                have hd_card : d.divisors.card ≥ 3 := by
                  have : 2 ≤ d := by omega
                  exact card_divisors_composite_ge_three d this hd_prime
                have : ∑ x ∈ n.properDivisors, x * x.divisors.card > n := by
                  rw [h_sum_eq] at h_sum_le
                  rw [h_div1, h_div3] at h_sum_le
                  have : d * d.divisors.card ≥ 3 * d := by nlinarith
                  have : 1 * 1 + 3 * 2 + d * d.divisors.card ≥ 3 * d + 7 := by omega
                  have : 3 * d + 7 > n := by
                    rw [hd_eq]
                    omega
                  omega
                omega
              · -- here we have p ≥ 5 and d is composite
                by_cases hd_eq_p2 : d = p^2
                · -- d = p^2
                  have hp_cube : n = p^3 := by
                    rw [hd_eq, hd_eq_p2]
                    ring
                  have h_a_cube := a_prime_cube p hp_prime
                  rw [← hp_cube] at h_a_cube
                  rw [h_a_cube] at h
                  rw [hp_cube] at h
                  have h_gt : p^3 > 3 * p^2 + 2 * p + 1 := by
                    have hp5 : p ≥ 5 := by omega
                    have h1 : p * p^2 ≥ 5 * p^2 := Nat.mul_le_mul_right (p^2) hp5
                    have h2 : 5 * p^2 = 3 * p^2 + 2 * p^2 := by ring
                    have h3 : 2 * p^2 ≥ 10 * p := by
                      have : p * p ≥ 5 * p := Nat.mul_le_mul_right p hp5
                      nlinarith
                    have h4 : 10 * p > 2 * p + 1 := by omega
                    calc
                      p^3 = p * p^2 := by ring
                      _ ≥ 5 * p^2 := h1
                      _ = 3 * p^2 + 2 * p^2 := h2
                      _ ≥ 3 * p^2 + 10 * p := by omega
                      _ > 3 * p^2 + 2 * p + 1 := by omega
                  omega
                · -- d ≠ p^2
                  have hp5 : p ≥ 5 := by omega
                  have hn0_pos : 0 < n := by omega
                  exact d_composite_contradiction n p d hn0_pos hp_prime hd_eq h hd_prime hd_eq_p2 hp5 (by omega) h_even (by rfl) (by rfl)
    · rintro rfl
      decide



