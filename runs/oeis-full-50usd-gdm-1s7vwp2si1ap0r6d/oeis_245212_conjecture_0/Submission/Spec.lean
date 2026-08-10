import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A245212: $a(n) = n \cdot \tau(n) - \sum_{d|n, d<n} d \cdot \tau(d)$,
where $\tau(n)$ is the number of divisors of $n$.
The formula uses the set of proper divisors for the sum.
The result is an integer ($\mathbb{Z}$) to account for negative values.
-/
def a (n : ℕ) : ℤ :=
  (n : ℤ) * (n.divisors.card : ℤ) - n.properDivisors.sum
    (fun d => (d : ℤ) * (d.divisors.card : ℤ))

-- The sum of divisors function $\sigma_1(n)$, cast to ℤ.
def sigma (n : ℕ) : ℤ :=
  n.divisors.sum (fun d => (d : ℤ))


lemma card_divisors_le_of_proper_divisor (m d : ℕ) (hm : m ≠ 0) (hd : d ∈ m.properDivisors) :
    d.divisors.card + 1 ≤ m.divisors.card := by
  rw [mem_properDivisors] at hd
  have hd_div : d.divisors ⊆ m.divisors := by
    intro x hx
    rw [mem_divisors] at hx ⊢
    obtain ⟨hx1, hx2⟩ := hx
    constructor
    · exact dvd_trans hx1 hd.1
    · exact hm
  have hm_notin : m ∉ d.divisors := by
    rw [mem_divisors]
    rintro ⟨h1, h2⟩
    have h_le := Nat.le_of_dvd (Nat.pos_of_ne_zero h2) h1
    omega
  have hm_in : m ∈ m.divisors := by
    rw [mem_divisors]
    exact ⟨dvd_rfl, hm⟩
  have h_insert : insert m d.divisors ⊆ m.divisors := by
    rw [insert_subset_iff]
    exact ⟨hm_in, hd_div⟩
  have h_card := card_le_card h_insert
  rw [Finset.card_insert_of_notMem hm_notin] at h_card
  exact h_card

lemma sum_properDivisors_eq_sigma_sub_self (m : ℕ) (hm : m ≠ 0) :
    m.properDivisors.sum (fun d => (d : ℤ)) = sigma m - m := by
  have h_insert : m.divisors = insert m m.properDivisors := by
    exact (insert_self_properDivisors hm).symm
  have h_not_mem : m ∉ m.properDivisors := self_notMem_properDivisors
  rw [sigma]
  rw [h_insert, sum_insert h_not_mem]
  push_cast
  ring

lemma card_divisors_two_pow (m : ℕ) : (2 ^ m).divisors.card = m + 1 := by
  rw [divisors_prime_pow prime_two m]
  rw [card_map]
  exact card_range (m + 1)

lemma divisors_two_pow (k : ℕ) : (2 ^ (k + 1)).properDivisors = (2 ^ k).divisors := by
  ext d
  rw [mem_properDivisors, mem_divisors]
  have h_ne : 2 ^ k ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by decide))
  rw [and_iff_left h_ne]
  rw [dvd_prime_pow prime_two, dvd_prime_pow prime_two]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, h_lt⟩
    use i
    have hi_lt : i < k + 1 := by
      exact (Nat.pow_lt_pow_iff_right (by decide)).mp h_lt
    exact ⟨Nat.le_of_lt_add_one hi_lt, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    constructor
    · use i
      exact ⟨Nat.le_succ_of_le hi, rfl⟩
    · exact (Nat.pow_lt_pow_iff_right (by decide)).mpr (Nat.lt_succ_of_le hi)

lemma a_two_pow_recurrence (k : ℕ) : a (2 ^ (k + 1)) = 2 ^ (k + 1) + a (2 ^ k) := by
  rw [a, a]
  rw [card_divisors_two_pow (k + 1), card_divisors_two_pow k]
  rw [divisors_two_pow k]
  have h_insert : (2 ^ k).divisors = insert (2 ^ k) (2 ^ k).properDivisors := by
    have h_ne : 2 ^ k ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by decide))
    exact (insert_self_properDivisors h_ne).symm
  have h_not_mem : 2 ^ k ∉ (2 ^ k).properDivisors := self_notMem_properDivisors
  rw [h_insert]
  rw [sum_insert h_not_mem]
  rw [card_divisors_two_pow k]
  push_cast
  ring

lemma a_two_pow (k : ℕ) : a (2 ^ k) = (2 : ℤ) ^ (k + 1) - 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [a_two_pow_recurrence]
    rw [ih]
    ring

lemma geom_sum_two_pow (k : ℕ) : ∑ i ∈ range (k + 1), (((2 ^ i : ℕ) : ℤ)) = (2 : ℤ) ^ (k + 1) - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

lemma sigma_two_pow (k : ℕ) : sigma (2 ^ k) = (2 : ℤ) ^ (k + 1) - 1 := by
  rw [sigma]
  rw [divisors_prime_pow prime_two k]
  rw [sum_map]
  exact geom_sum_two_pow k

lemma a_eq_sigma_two_pow (k : ℕ) : a (2 ^ k) = sigma (2 ^ k) := by
  rw [a_two_pow, sigma_two_pow]


lemma a_def_alternative (n : ℕ) (hn : n > 0) :
    a n = 2 * (n : ℤ) * (n.divisors.card : ℤ) - n.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) := by
  have h_insert : n.divisors = insert n n.properDivisors := by
    exact (insert_self_properDivisors (Nat.ne_of_gt hn)).symm
  have h_not_mem : n ∉ n.properDivisors := self_notMem_properDivisors
  have h_sum : n.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) =
      (n : ℤ) * (n.divisors.card : ℤ) + n.properDivisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) := by
    conv_lhs => rw [h_insert]
    rw [sum_insert h_not_mem]
  rw [a]
  linarith

lemma a_eq_sigma_iff (n : ℕ) (hn : n > 0) :
    a n = sigma n ↔ 2 * (n : ℤ) * (n.divisors.card : ℤ) = n.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ) + (d : ℤ)) := by
  rw [a_def_alternative n hn, sigma]
  constructor
  · intro h
    have : 2 * (n : ℤ) * (n.divisors.card : ℤ) = n.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) + n.divisors.sum (fun d => (d : ℤ)) := by linarith
    rw [this, ← sum_add_distrib]
  · intro h
    rw [sum_add_distrib] at h
    linarith

lemma exists_odd_part (n : ℕ) :
    n > 0 → Exists (fun k => Exists (fun m => n = 2 ^ k * m ∧ ¬ 2 ∣ m)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases h2 : 2 ∣ n
    · obtain ⟨d, rfl⟩ := h2
      have hd : d > 0 := by
        cases d with
        | zero => simp at hn
        | succ d' => exact Nat.succ_pos d'
      have h_lt : d < 2 * d := by
        omega
      have ih_d := ih d h_lt hd
      obtain ⟨k, m, rfl, hm⟩ := ih_d
      use k + 1, m
      constructor
      · ring
      · exact hm
    · use 0, n
      constructor
      · ring
      · exact h2

lemma isPowerOfTwo_iff_odd_part_eq_one (k m : ℕ) (hm : ¬ 2 ∣ m) :
    (2 ^ k * m).isPowerOfTwo ↔ m = 1 := by
  constructor
  · rintro ⟨j, hj⟩
    have h_dvd : m ∣ 2 ^ j := by
      use 2 ^ k
      rw [mul_comm]
      exact hj.symm
    rw [dvd_prime_pow prime_two] at h_dvd
    obtain ⟨i, hi, rfl⟩ := h_dvd
    cases i with
    | zero => rfl
    | succ i' =>
      have h_div : 2 ∣ 2 ^ (i' + 1) := by
        use 2 ^ i'
        ring
      contradiction
  · rintro rfl
    use k
    ring

lemma sigma_mul_of_coprime (k m : ℕ) (hm : ¬ 2 ∣ m) :
    sigma (2 ^ k * m) = sigma (2 ^ k) * sigma m := by
  have h_coprime : Nat.Coprime (2 ^ k) m := by
    have h2m : Nat.Coprime 2 m := (Nat.Prime.coprime_iff_not_dvd prime_two).mpr hm
    exact Nat.Coprime.pow_left k h2m
  rw [sigma, sigma, sigma]
  have h_nat : (2 ^ k * m).divisors.sum (fun d => d) = (2 ^ k).divisors.sum (fun d => d) * m.divisors.sum (fun d => d) := by
    exact Nat.Coprime.sum_divisors_mul h_coprime
  have h_cast : (((2 ^ k * m).divisors.sum (fun d => d) : ℕ) : ℤ) = (((2 ^ k).divisors.sum (fun d => d) : ℕ) : ℤ) * (((m.divisors.sum (fun d => d) : ℕ) : ℤ)) := by
    exact_mod_cast h_nat
  push_cast at h_cast
  exact h_cast

open scoped ArithmeticFunction

def g_fn : ArithmeticFunction ℤ :=
  ((ArithmeticFunction.id : ArithmeticFunction ℤ).pmul (ArithmeticFunction.sigma 0 : ArithmeticFunction ℤ)) * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)

lemma g_fn_apply (n : ℕ) (hn : n > 0) : g_fn n = n.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) := by
  rw [g_fn]
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  apply sum_congr rfl
  intro d _
  rw [ArithmeticFunction.pmul_apply]
  simp [ArithmeticFunction.sigma_apply]

lemma isMultiplicative_g : g_fn.IsMultiplicative := by
  have h1 : ((ArithmeticFunction.id : ArithmeticFunction ℤ).pmul (ArithmeticFunction.sigma 0 : ArithmeticFunction ℤ)).IsMultiplicative := by
    apply ArithmeticFunction.IsMultiplicative.pmul
    · exact ArithmeticFunction.isMultiplicative_id.natCast (R := ℤ)
    · exact ArithmeticFunction.isMultiplicative_sigma.natCast (R := ℤ)
  exact ArithmeticFunction.IsMultiplicative.mul h1 (ArithmeticFunction.isMultiplicative_zeta.natCast (R := ℤ))

lemma g_mul_of_coprime (k m : ℕ) (hm : ¬ 2 ∣ m) :
    (2 ^ k * m).divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) =
    (2 ^ k).divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) *
    m.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) := by
  have h_coprime : Nat.Coprime (2 ^ k) m := by
    have h2m : Nat.Coprime 2 m := (Nat.Prime.coprime_iff_not_dvd prime_two).mpr hm
    exact Nat.Coprime.pow_left k h2m
  have h_pos2 : 2 ^ k > 0 := Nat.pow_pos (by decide)
  have h_posm : m > 0 := by omega
  have h_pos_mul : 2 ^ k * m > 0 := Nat.mul_pos h_pos2 h_posm
  rw [← g_fn_apply (2 ^ k * m) h_pos_mul]
  rw [← g_fn_apply (2 ^ k) h_pos2]
  rw [← g_fn_apply m h_posm]
  exact isMultiplicative_g.map_mul_of_coprime h_coprime

lemma divisors_two_pow_succ (k : ℕ) :
    (2 ^ (k + 1)).divisors = insert (2 ^ (k + 1)) (2 ^ k).divisors := by
  have h_insert : (2 ^ (k + 1)).divisors = insert (2 ^ (k + 1)) (2 ^ (k + 1)).properDivisors := by
    have h_ne : 2 ^ (k + 1) ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by decide))
    exact (insert_self_properDivisors h_ne).symm
  rw [h_insert, divisors_two_pow k]

lemma g_two_pow (k : ℕ) :
    ((2 ^ k).divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ))) = (k : ℤ) * (2 : ℤ) ^ (k + 1) + 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [divisors_two_pow_succ]
    have h_not_mem : 2 ^ (k + 1) ∉ (2 ^ k).divisors := by
      rw [mem_divisors]
      rintro ⟨h1, h2⟩
      have h3 : 2 ^ (k + 1) ≤ 2 ^ k := Nat.le_of_dvd (Nat.pow_pos (by decide)) h1
      have h4 : 2 ^ (k + 1) > 2 ^ k := Nat.pow_lt_pow_iff_right (by decide) |>.mpr (Nat.lt_succ_self k)
      linarith
    rw [sum_insert h_not_mem]
    rw [ih]
    have h_card : (2 ^ (k + 1)).divisors.card = k + 2 := by
      have h_card' := card_divisors_two_pow (k + 1)
      exact h_card'
    have h_card_cast : ((2 ^ (k + 1)).divisors.card : ℤ) = (k : ℤ) + 2 := by
      exact_mod_cast h_card
    push_cast
    rw [h_card_cast]
    ring

lemma sum_divisors_two_pow_mul_odd (k m : ℕ) (hm : ¬ 2 ∣ m) :
    ((2 ^ k * m).divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ) + (d : ℤ))) =
    (k * 2 ^ (k + 1) + 1) * (m.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ))) +
    (2 ^ (k + 1) - 1) * sigma m := by
  rw [sum_add_distrib]
  have h_fold : (2 ^ k * m).divisors.sum (fun d => (d : ℤ)) = sigma (2 ^ k * m) := rfl
  rw [h_fold]
  rw [g_mul_of_coprime k m hm]
  rw [sigma_mul_of_coprime k m hm]
  rw [g_two_pow k]
  rw [sigma_two_pow k]

lemma left_side_two_pow_mul_odd (k m : ℕ) (hm : ¬ 2 ∣ m) :
    2 * (2 ^ k * m : ℤ) * ((2 ^ k * m).divisors.card : ℤ) = (k + 1) * 2 ^ (k + 1) * m * m.divisors.card := by
  have h_coprime : Nat.Coprime (2 ^ k) m := by
    have h2m : Nat.Coprime 2 m := (Nat.Prime.coprime_iff_not_dvd prime_two).mpr hm
    exact Nat.Coprime.pow_left k h2m
  rw [Nat.Coprime.card_divisors_mul h_coprime, card_divisors_two_pow k]
  push_cast
  ring

lemma a_eq_sigma_two_pow_mul_odd_iff (k m : ℕ) (hm : ¬ 2 ∣ m) :
    a (2 ^ k * m) = sigma (2 ^ k * m) ↔
    (k + 1) * 2 ^ (k + 1) * m * m.divisors.card =
    (k * 2 ^ (k + 1) + 1) * (m.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ))) +
    (2 ^ (k + 1) - 1) * sigma m := by
  have h_pos : 2 ^ k * m > 0 := by
    have h1 : 2 ^ k > 0 := Nat.pow_pos (by decide)
    have h2 : m > 0 := by omega
    exact Nat.mul_pos h1 h2
  rw [a_eq_sigma_iff (2 ^ k * m) h_pos]
  have h_lhs : 2 * (2 ^ k * m : ℤ) * ((2 ^ k * m).divisors.card : ℤ) = 2 * ↑(2 ^ k * m) * ((2 ^ k * m).divisors.card : ℤ) := by rfl
  rw [← h_lhs]
  rw [left_side_two_pow_mul_odd k m hm]
  rw [sum_divisors_two_pow_mul_odd k m hm]

lemma two_pow_dvd_C_sub_S (k m : ℕ) (hm : ¬ 2 ∣ m) (h_eq : a (2 ^ k * m) = sigma (2 ^ k * m)) :
    (2 ^ (k + 1) : ℤ) ∣ (m.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) - sigma m) := by
  rw [a_eq_sigma_two_pow_mul_odd_iff k m hm] at h_eq
  have h_diff : (m.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) - sigma m) =
      (2 ^ (k + 1) : ℤ) * ((k + 1) * m * m.divisors.card - k * (m.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ))) - sigma m) := by
    linarith
  rw [h_diff]
  exact dvd_mul_right (2 ^ (k + 1) : ℤ) _

lemma C_sub_S_pos (m : ℕ) (hm3 : m ≥ 3) :
    (m.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) - sigma m) > 0 := by
  have h_eq : (m.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) - sigma m) =
      m.divisors.sum (fun d => (d : ℤ) * ((d.divisors.card : ℤ) - 1)) := by
    rw [sigma]
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro x _
    ring
  rw [h_eq]
  have hm_mem : m ∈ m.divisors := by
    have h_ne : m ≠ 0 := by linarith
    simp [h_ne]
  rw [sum_eq_add_sum_diff_singleton hm_mem]
  have h_term : (m : ℤ) * ((m.divisors.card : ℤ) - 1) > 0 := by
    have h_m_pos : (m : ℤ) > 0 := by linarith
    have h_card : m.divisors.card ≥ 2 := by
      have hm1 : m ≠ 1 := by linarith
      have hm0 : m ≠ 0 := by linarith
      have h_subset : {1, m} ⊆ m.divisors := by
        rw [insert_subset_iff, singleton_subset_iff]
        have h1 : 1 ∈ m.divisors := by rw [mem_divisors]; exact ⟨one_dvd m, hm0⟩
        have h2 : m ∈ m.divisors := by rw [mem_divisors]; exact ⟨dvd_rfl, hm0⟩
        exact ⟨h1, h2⟩
      have h_two_card : ({1, m} : Finset ℕ).card = 2 := by
        rw [card_insert_of_notMem]
        · rw [card_singleton]
        · simp [hm1.symm]
      have h_le := card_le_card h_subset
      omega
    have h_card_pos : (m.divisors.card : ℤ) - 1 ≥ 1 := by linarith
    exact mul_pos h_m_pos h_card_pos
  have h_rest : (m.divisors \ {m}).sum (fun d => (d : ℤ) * ((d.divisors.card : ℤ) - 1)) ≥ 0 := by
    apply sum_nonneg
    intro x hx
    rw [mem_sdiff, mem_divisors] at hx
    have h_x_pos : (x : ℤ) ≥ 0 := by positivity
    have h_card : x.divisors.card ≥ 1 := by
      have h_div_x : x ∣ m := hx.1.1
      have hx0 : x ≠ 0 := by
        rintro rfl
        have : m = 0 := Nat.eq_zero_of_zero_dvd h_div_x
        omega
      have h1 : 1 ∈ x.divisors := by rw [mem_divisors]; exact ⟨one_dvd x, hx0⟩
      have h_nonempty : x.divisors.Nonempty := ⟨1, h1⟩
      exact card_pos.mpr h_nonempty
    have h_card_pos : (x.divisors.card : ℤ) - 1 ≥ 0 := by linarith
    exact mul_nonneg h_x_pos h_card_pos
  linarith

lemma two_pow_le_C_sub_S (k m : ℕ) (hm : ¬ 2 ∣ m) (hm3 : m ≥ 3) (h_eq : a (2 ^ k * m) = sigma (2 ^ k * m)) :
    (2 ^ (k + 1) : ℤ) ≤ (m.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) - sigma m) := by
  have hdvd := two_pow_dvd_C_sub_S k m hm h_eq
  have hpos := C_sub_S_pos m hm3
  have h_two_pow_pos : (2 ^ (k + 1) : ℤ) > 0 := by positivity
  exact Int.le_of_dvd hpos hdvd



lemma C_prime_D_eq (k m : ℕ) (hm : ¬ 2 ∣ m) (heq : a (2 ^ k * m) = sigma (2 ^ k * m)) :
    (2 ^ (k + 1) - 1 : ℤ) * (m * m.divisors.card - sigma m) =
    (k * 2 ^ (k + 1) + 1 : ℤ) * (m.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) - m * m.divisors.card) := by
  rw [a_eq_sigma_two_pow_mul_odd_iff k m hm] at heq
  linarith


lemma C_prime_pos (m : ℕ) (hm3 : m ≥ 3) :
    (m.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) - (m : ℤ) * (m.divisors.card : ℤ)) > 0 := by
  have h_insert : m.divisors = insert m m.properDivisors := by
    exact (insert_self_properDivisors (by omega)).symm
  have h_not_mem : m ∉ m.properDivisors := self_notMem_properDivisors
  have h_diff : m.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) - (m : ℤ) * (m.divisors.card : ℤ) =
      m.properDivisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) := by
    have h_sum : m.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) =
        (m : ℤ) * (m.divisors.card : ℤ) + m.properDivisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) := by
      conv_lhs => rw [h_insert]
      rw [sum_insert h_not_mem]
    linarith
  rw [h_diff]
  have h_one_mem : 1 ∈ m.properDivisors := (mem_properDivisors).mpr ⟨one_dvd m, by omega⟩
  rw [sum_eq_add_sum_diff_singleton h_one_mem]
  have h_card1 : (1 : ℕ).divisors.card = 1 := by decide
  have h_term : (1 : ℤ) * ((1 : ℕ).divisors.card : ℤ) = 1 := by rw [h_card1]; ring
  push_cast
  rw [h_term]
  have h_rest : (m.properDivisors \ {1}).sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) ≥ 0 := by
    apply sum_nonneg
    intro d hd
    have : (d : ℤ) ≥ 0 := by positivity
    have : (d.divisors.card : ℤ) ≥ 0 := by positivity
    positivity
  linarith




lemma mem_properDivisors_sdiff_one_iff (m d : ℕ) (hm : m ≠ 0) :
    d ∈ m.properDivisors \ {1} ↔ d ∣ m ∧ 1 < d ∧ d < m := by
  rw [mem_sdiff, mem_singleton, mem_properDivisors]
  constructor
  · rintro ⟨⟨hd_div, hd_lt⟩, hd_ne_one⟩
    refine ⟨hd_div, ?_, hd_lt⟩
    have hd_ne_zero : d ≠ 0 := by
      rintro rfl
      have : m = 0 := zero_dvd_iff.mp hd_div
      exact hm this
    omega
  · rintro ⟨hd_div, hd_gt, hd_lt⟩
    exact ⟨⟨hd_div, hd_lt⟩, by omega⟩

lemma C_prime_ge_two_sigma_sub_m (m : ℕ) (hm3 : m ≥ 3) :
    (m.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) - (m : ℤ) * (m.divisors.card : ℤ)) ≥ 2 * (sigma m - m) - 1 := by
  have hm0 : m ≠ 0 := by omega
  have h_insert : m.divisors = insert m m.properDivisors := by
    exact (insert_self_properDivisors hm0).symm
  have h_not_mem : m ∉ m.properDivisors := self_notMem_properDivisors
  have h_diff : (m.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) - (m : ℤ) * (m.divisors.card : ℤ)) =
      m.properDivisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) := by
    have h_sum : m.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) =
        (m : ℤ) * (m.divisors.card : ℤ) + m.properDivisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) := by
      conv_lhs => rw [h_insert]
      rw [sum_insert h_not_mem]
    linarith
  rw [h_diff]
  have h_one_mem : 1 ∈ m.properDivisors := (mem_properDivisors).mpr ⟨one_dvd m, by omega⟩
  rw [sum_eq_add_sum_diff_singleton h_one_mem]
  have h_card1 : (1 : ℕ).divisors.card = 1 := by decide
  have h_term : (1 : ℤ) * ((1 : ℕ).divisors.card : ℤ) = 1 := by rw [h_card1]; ring
  push_cast
  rw [h_term]
  have h_le : (m.properDivisors \ {1}).sum (fun d => 2 * (d : ℤ)) ≤
      (m.properDivisors \ {1}).sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) := by
    apply sum_le_sum
    intro d hd
    have hd_iff : d ∈ m.properDivisors \ {1} ↔ d ∣ m ∧ 1 < d ∧ d < m := mem_properDivisors_sdiff_one_iff m d hm0
    rw [hd_iff] at hd
    have hd_ne_zero : d ≠ 0 := by omega
    have hd_ne_one : d ≠ 1 := by omega
    have hd1 : d > 1 := hd.2.1
    have h_card : d.divisors.card ≥ 2 := by
      have h_subset : {1, d} ⊆ d.divisors := by
        rw [insert_subset_iff, singleton_subset_iff]
        have h1 : 1 ∈ d.divisors := by rw [mem_divisors]; exact ⟨one_dvd d, hd_ne_zero⟩
        have h2 : d ∈ d.divisors := by rw [mem_divisors]; exact ⟨dvd_rfl, hd_ne_zero⟩
        exact ⟨h1, h2⟩
      have h_two_card : ({1, d} : Finset ℕ).card = 2 := by
        rw [card_insert_of_notMem]
        · rw [card_singleton]
        · simp [hd_ne_one.symm]
      have h_le := card_le_card h_subset
      omega
    have hd_pos : (d : ℤ) ≥ 0 := by positivity
    nlinarith
  have h_sum_prop : m.properDivisors.sum (fun d => (d : ℤ)) = sigma m - m := by
    exact sum_properDivisors_eq_sigma_sub_self m hm0
  rw [sum_eq_add_sum_diff_singleton h_one_mem] at h_sum_prop
  have h_sum_diff : (m.properDivisors \ {1}).sum (fun d => (d : ℤ)) = sigma m - m - 1 := by
    simp only [Nat.cast_one] at h_sum_prop
    linarith
  have h_sum_mul : (m.properDivisors \ {1}).sum (fun d => 2 * (d : ℤ)) = 2 * (m.properDivisors \ {1}).sum (fun d => (d : ℤ)) := by
    rw [← mul_sum]
  rw [h_sum_mul, h_sum_diff] at h_le
  linarith

lemma D_pos (m : ℕ) (hm3 : m ≥ 3) :
    ((m : ℤ) * (m.divisors.card : ℤ) - sigma m) > 0 := by
  have h_eq : (m : ℤ) * (m.divisors.card : ℤ) - sigma m =
      m.divisors.sum (fun d => (m : ℤ) - (d : ℤ)) := by
    have h_sum_const : m.divisors.sum (fun d => (m : ℤ)) = (m : ℤ) * (m.divisors.card : ℤ) := by
      rw [sum_const, nsmul_eq_mul, mul_comm]
    rw [sigma, ← h_sum_const, ← sum_sub_distrib]
  rw [h_eq]
  have hm_mem : m ∈ m.divisors := by
    have h_ne : m ≠ 0 := by linarith
    simp [h_ne]
  rw [sum_eq_add_sum_diff_singleton hm_mem]
  have h_term0 : (m : ℤ) - (m : ℤ) = 0 := by ring
  rw [h_term0, zero_add]
  have h_one_mem : 1 ∈ m.divisors \ {m} := by
    rw [mem_sdiff, mem_divisors, mem_singleton]
    refine ⟨⟨one_dvd m, (by omega)⟩, by omega⟩
  rw [sum_eq_add_sum_diff_singleton h_one_mem]
  have h_term1 : (m : ℤ) - (1 : ℤ) > 0 := by omega
  set S_sum := ((m.divisors \ {m}) \ {1}).sum (fun d => (m : ℤ) - (d : ℤ))
  have h_rest : S_sum ≥ 0 := by
    apply sum_nonneg
    intro d hd
    rw [mem_sdiff, mem_sdiff, mem_divisors, mem_singleton, mem_singleton] at hd
    have : (d : ℤ) ≤ (m : ℤ) := by
      have hd_dvd : d ∣ m := hd.1.1.1
      have hm_pos : m > 0 := by omega
      have h_le := Nat.le_of_dvd hm_pos hd_dvd
      exact_mod_cast h_le
    omega
  omega


lemma prime_case (k : ℕ) (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) (heq : a (2 ^ k * p) = sigma (2 ^ k * p)) : False := by
  have hm : ¬ 2 ∣ p := by
    rintro ⟨d, rfl⟩
    have hd_eq : 2 = 1 ∨ 2 = 2 * d := by
      exact hp.eq_one_or_self_of_dvd 2 (by omega)
    rcases hd_eq with h_one | h_self
    · contradiction
    · linarith
  have hdvd := two_pow_dvd_C_sub_S k p hm heq
  have h_C_S : p.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) - sigma p = p := by
    have hp_divs : p.divisors = {1, p} := by
      exact Nat.Prime.divisors hp
    unfold sigma
    rw [hp_divs]
    have h1 : 1 ≠ p := by omega
    rw [sum_pair h1, sum_pair h1]
    have hc1 : (1 : ℕ).divisors.card = 1 := by decide
    have hcp : p.divisors.card = 2 := by
      rw [hp_divs]
      exact card_pair h1
    push_cast
    rw [hc1, hcp]
    ring
  rw [h_C_S] at hdvd
  have h_two_dvd_two_pow : (2 : ℤ) ∣ (2 ^ (k + 1) : ℤ) := by
    use (2 ^ k : ℤ)
    rw [pow_succ]
    push_cast
    ring
  have h_two_dvd_p : (2 : ℤ) ∣ (p : ℤ) := by
    exact dvd_trans h_two_dvd_two_pow hdvd
  have h_two_dvd_p_nat : 2 ∣ p := by
    exact Int.natCast_dvd_natCast.mp h_two_dvd_p
  exact hm h_two_dvd_p_nat


lemma exists_proper_divisor_of_composite (m : ℕ) (hm3 : m ≥ 3) (h_not_prime : ¬ m.Prime) :
    ∃ d, d ∈ m.properDivisors ∧ d > 1 := by
  have hm1 : m ≠ 1 := by omega
  have hm0 : m ≠ 0 := by omega
  obtain ⟨d, hd_dvd, hd1, hdp⟩ := Nat.exists_dvd_of_not_prime (by omega) h_not_prime
  use d
  constructor
  · rw [mem_properDivisors]
    refine ⟨hd_dvd, ?_⟩
    have hd_le := Nat.le_of_dvd (by omega) hd_dvd
    have hd_ne : d ≠ m := hdp
    omega
  · have hd_ne_zero : d ≠ 0 := by
      rintro rfl
      have : m = 0 := zero_dvd_iff.mp hd_dvd
      omega
    omega



lemma proper_divisor_le_div_three (m d : ℕ) (hm_odd : ¬ 2 ∣ m) (hd : d ∈ m.properDivisors) (hd1 : d > 1) :
    3 * d ≤ m := by
  rw [mem_properDivisors] at hd
  obtain ⟨hd_dvd, hd_lt⟩ := hd
  obtain ⟨c, rfl⟩ := hd_dvd
  have hc_odd : ¬ 2 ∣ c := by
    rintro ⟨y, rfl⟩
    have h_even : 2 ∣ d * (2 * y) := by
      use d * y
      ring
    exact hm_odd h_even
  have hc_ne_one : c ≠ 1 := by
    rintro rfl
    simp at hd_lt
  have hc3 : c ≥ 3 := by omega
  nlinarith

lemma sum_properDivisors_le_of_composite (m : ℕ) (hm_odd : ¬ 2 ∣ m) (hm3 : m ≥ 3) (hm_comp : ¬ m.Prime) :
    3 * (sigma m - m - 1) ≤ ((m.divisors.card : ℤ) - 2) * (m : ℤ) := by
  have hm0 : m ≠ 0 := by omega
  have h_one_mem : 1 ∈ m.properDivisors := by
    rw [mem_properDivisors]
    exact ⟨one_dvd m, by omega⟩
  have h_sum_prop_split : m.properDivisors.sum (fun d => (d : ℤ)) =
      1 + (m.properDivisors \ {1}).sum (fun d => (d : ℤ)) := by
    rw [sum_eq_add_sum_diff_singleton h_one_mem]
    ring
  rw [sum_properDivisors_eq_sigma_sub_self m hm0] at h_sum_prop_split
  have h_diff_eq : sigma m - m - 1 = (m.properDivisors \ {1}).sum (fun d => (d : ℤ)) := by
    simp only [Nat.cast_one] at h_sum_prop_split
    linarith
  rw [h_diff_eq]
  rw [mul_sum]
  have h_le : (m.properDivisors \ {1}).sum (fun d => 3 * (d : ℤ)) ≤
      (m.properDivisors \ {1}).sum (fun d => (m : ℤ)) := by
    apply sum_le_sum
    intro d hd
    have hd_ne_zero : d ≠ 0 := by
      rintro rfl
      have hdvd : 0 ∣ m := hd.1.1
      have : m = 0 := zero_dvd_iff.mp hdvd
      omega
    have hd1 : d > 1 := by omega
    have hd_prop : d ∈ m.properDivisors := by
      rw [mem_properDivisors]
      exact hd.1
    have h3d := proper_divisor_le_div_three m d hm_odd hd_prop hd1
    exact_mod_cast h3d
  have h_sum_const : (m.properDivisors \ {1}).sum (fun d => (m : ℤ)) =
      (((m.properDivisors \ {1}).card : ℕ) : ℤ) * (m : ℤ) := by
    rw [sum_const]
    ring
  rw [h_sum_const] at h_le
  have h_card_eq : (m.properDivisors \ {1}).card = m.divisors.card - 2 := by
    have h_prop_card : m.properDivisors.card = m.divisors.card - 1 := by
      have h_insert : m.divisors = insert m m.properDivisors := by
        exact (insert_self_properDivisors hm0).symm
      have h_not_mem : m ∉ m.properDivisors := self_notMem_properDivisors
      rw [h_insert, card_insert_of_notMem h_not_mem]
      omega
    have h_one_mem' : 1 ∈ m.properDivisors := h_one_mem
    have h_subset : {1} ⊆ m.properDivisors := by
      rw [singleton_subset_iff]
      exact h_one_mem'
    rw [card_sdiff h_subset, card_singleton]
    omega
  have h_cast : (((m.properDivisors \ {1}).card : ℕ) : ℤ) = (m.divisors.card : ℤ) - 2 := by
    omega
  rw [h_cast] at h_le
  linarith

lemma C_plus_S_lt_m_plus_tau_S (m : ℕ) (hm_odd : ¬ 2 ∣ m) (hm3 : m ≥ 3) (hm_comp : ¬ m.Prime) :
    m.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ) + (d : ℤ)) <
    (m : ℤ) * (m.divisors.card : ℤ) + (m : ℤ) + (m.divisors.card : ℤ) * (sigma m - m) := by
  have hm0 : m ≠ 0 := by omega
  have h_insert : m.divisors = insert m m.properDivisors := by
    exact (insert_self_properDivisors hm0).symm
  have h_not_mem : m ∉ m.properDivisors := self_notMem_properDivisors
  have h_eq : m.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ) + (d : ℤ)) =
      (m : ℤ) * (m.divisors.card : ℤ) + (m : ℤ) +
      m.properDivisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ) + (d : ℤ)) := by
    nth_rw 1 [h_insert]
    rw [sum_insert h_not_mem]
  rw [h_eq]
  have h_one_mem : 1 ∈ m.properDivisors := ⟨one_dvd m, by omega⟩
  have h_sum_split : m.properDivisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ) + (d : ℤ)) =
      2 + (m.properDivisors \ {1}).sum (fun d => (d : ℤ) * (d.divisors.card : ℤ) + (d : ℤ)) := by
    rw [sum_eq_add_sum_diff_singleton h_one_mem]
    have h_card1 : (1 : ℕ).divisors.card = 1 := by decide
    have h_term : (1 : ℤ) * (((1 : ℕ).divisors.card : ℕ) : ℤ) + (1 : ℤ) = 2 := by rw [h_card1]; ring
    rw [h_term]
  rw [h_sum_split]
  have h_le : (m.properDivisors \ {1}).sum (fun d => (d : ℤ) * (d.divisors.card : ℤ) + (d : ℤ)) ≤
      (m.properDivisors \ {1}).sum (fun d => (d : ℤ) * (m.divisors.card : ℤ)) := by
    apply sum_le_sum
    intro d hd
    have hd_prop : d ∈ m.properDivisors := by
      rw [mem_properDivisors]
      exact hd.1
    have h_card := card_divisors_le_of_proper_divisor m d hm0 hd_prop
    have h_d_pos : (d : ℤ) ≥ 0 := by positivity
    nlinarith
  have h_sum_prop : (m.properDivisors \ {1}).sum (fun d => (d : ℤ) * (m.divisors.card : ℤ)) =
      (m.divisors.card : ℤ) * (m.properDivisors \ {1}).sum (fun d => (d : ℤ)) := by
    rw [← sum_mul]
    ring
  rw [h_sum_prop] at h_le
  have h_sum_prop_split : m.properDivisors.sum (fun d => (d : ℤ)) =
      1 + (m.properDivisors \ {1}).sum (fun d => (d : ℤ)) := by
    rw [sum_eq_add_sum_diff_singleton h_one_mem]
    ring
  rw [sum_properDivisors_eq_sigma_sub_self m hm0] at h_sum_prop_split
  have h_card_gt : (m.divisors.card : ℤ) > 2 := by
    have h_comp_card : m.divisors.card ≥ 3 := by
      have hm1 : m ≠ 1 := by omega
      obtain ⟨d, hd_proper, hd_gt⟩ := exists_proper_divisor_of_composite m hm3 hm_comp
      have h1 : 1 ∈ m.divisors := by simp [hm1]
      have h2 : d ∈ m.divisors := by
        rw [mem_properDivisors] at hd_proper
        exact hd_proper.1
      have h3 : m ∈ m.divisors := by simp [hm1]
      have hd_ne_one : d ≠ 1 := by omega
      have hd_ne_m : d ≠ m := by
        rw [mem_properDivisors] at hd_proper
        omega
      have h1_ne_m : 1 ≠ m := by omega
      have h_subset : {1, d, m} ⊆ m.divisors := by
        rw [insert_subset_iff, insert_subset_iff, singleton_subset_iff]
        refine ⟨h1, h2, h3⟩
      have h_card := card_le_card h_subset
      have h_three : ({1, d, m} : Finset ℕ).card = 3 := by
        rw [card_insert_of_notMem, card_insert_of_notMem]
        · exact card_singleton 1
        · simp [hd_ne_one]
        · simp [h1_ne_m.symm, hd_ne_m.symm]
      omega
    omega
  linarith

lemma C_plus_S_le_m_plus_tau_S (m : ℕ) (hm : m ≠ 0) :
    m.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ) + (d : ℤ)) ≤
    (m : ℤ) + (m.divisors.card : ℤ) * sigma m := by
  have h_insert : m.divisors = insert m m.properDivisors := by
    exact (insert_self_properDivisors hm).symm
  have h_not_mem : m ∉ m.properDivisors := self_notMem_properDivisors
  have h_eq : m.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ) + (d : ℤ)) =
      (m : ℤ) * (m.divisors.card : ℤ) + (m : ℤ) +
      m.properDivisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ) + (d : ℤ)) := by
    nth_rw 1 [h_insert]
    rw [sum_insert h_not_mem]
  rw [h_eq]
  have h_le : m.properDivisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ) + (d : ℤ)) ≤
      m.properDivisors.sum (fun d => (d : ℤ) * (m.divisors.card : ℤ)) := by
    apply sum_le_sum
    intro d hd
    have h_card := card_divisors_le_of_proper_divisor m d hm hd
    have h_d_pos : (d : ℤ) ≥ 0 := by positivity
    nlinarith
  have h_sum_prop : m.properDivisors.sum (fun d => (d : ℤ) * (m.divisors.card : ℤ)) =
      (m.divisors.card : ℤ) * m.properDivisors.sum (fun d => (d : ℤ)) := by
    rw [← sum_mul]
  rw [h_sum_prop] at h_le
  rw [sum_properDivisors_eq_sigma_sub_self m hm] at h_le
  linarith


lemma Y_relation (k m : ℕ) (hm_odd : ¬ 2 ∣ m) (hm3 : m ≥ 3) (heq : a (2 ^ k * m) = sigma (2 ^ k * m)) :
    (2^(k+1) - 1 : ℤ) * ((m * m.divisors.card - sigma m : ℤ) - k * (m.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) - m * m.divisors.card : ℤ)) =
    (k + 1 : ℤ) * (m.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) - m * m.divisors.card : ℤ) := by
  have h_C_prime_D := C_prime_D_eq k m hm_odd heq
  set D := (m * m.divisors.card - sigma m : ℤ)
  set C_prime := (m.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) - m * m.divisors.card : ℤ)
  have h_temp : (2^(k+1) - 1 : ℤ) * D - (k * 2^(k+1) + 1 : ℤ) * C_prime = 0 := by linarith [h_C_prime_D]
  calc (2^(k+1) - 1 : ℤ) * (D - k * C_prime)
    _ = (2^(k+1) - 1 : ℤ) * D - (k * 2^(k+1) + 1 : ℤ) * C_prime + (k + 1) * C_prime := by ring
    _ = 0 + (k + 1) * C_prime := by rw [h_temp]
    _ = (k + 1) * C_prime := by ring

lemma Y_pos (k m : ℕ) (hm_odd : ¬ 2 ∣ m) (hm3 : m ≥ 3) (heq : a (2 ^ k * m) = sigma (2 ^ k * m)) :
    (m * m.divisors.card - sigma m : ℤ) - k * (m.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) - m * m.divisors.card : ℤ) ≥ 1 := by
  have h_C_prime_D := C_prime_D_eq k m hm_odd heq
  have h_C_prime_pos := C_prime_pos m hm3
  have h_D_pos := D_pos m hm3
  set D := (m * m.divisors.card - sigma m : ℤ)
  set C_prime := (m.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) - m * m.divisors.card : ℤ)
  have h_temp_eq : (2^(k+1) : ℤ) * (D - k * C_prime) = D + C_prime := by
    have h_temp : (2^(k+1) - 1 : ℤ) * D - (k * 2^(k+1) + 1 : ℤ) * C_prime = 0 := by linarith [h_C_prime_D]
    calc (2^(k+1) : ℤ) * (D - k * C_prime)
      _ = (2^(k+1) - 1 : ℤ) * D - (k * 2^(k+1) + 1 : ℤ) * C_prime + (D + C_prime) := by ring
      _ = 0 + (D + C_prime) := by rw [h_temp]
      _ = D + C_prime := by ring
  have h_sum_pos : D + C_prime > 0 := by linarith [h_D_pos, h_C_prime_pos]
  have h_two_pow_pos : (2^(k+1) : ℤ) > 0 := by positivity
  have h_Y_pos : D - k * C_prime > 0 := by
    nlinarith [h_temp_eq, h_sum_pos, h_two_pow_pos]
  omega

lemma m_ge_9 (m : ℕ) (hm_odd : ¬ 2 ∣ m) (hm3 : m ≥ 3) (hm_comp : ¬ m.Prime) : m ≥ 9 := by
  by_contra h_lt
  have h_cases : m = 3 ∨ m = 5 ∨ m = 7 := by
    omega
  rcases h_cases with rfl | rfl | rfl
  · exact hm_comp (by decide)
  · exact hm_comp (by decide)
  · exact hm_comp (by decide)


lemma sigma_sub_self_ge_four (m : ℕ) (hm_odd : ¬ 2 ∣ m) (hm3 : m ≥ 3) (hm_comp : ¬ m.Prime) :
    sigma m - m ≥ 4 := by
  have hm0 : m ≠ 0 := by omega
  have h_sum_prop : m.properDivisors.sum (fun d => (d : ℤ)) = sigma m - m := by
    exact sum_properDivisors_eq_sigma_sub_self m hm0
  rw [← h_sum_prop]
  obtain ⟨d, hd, hd1⟩ := exists_proper_divisor_of_composite m hm3 hm_comp
  have hd_odd : ¬ 2 ∣ d := by
    rintro ⟨y, rfl⟩
    have : 2 ∣ m := by
      rw [mem_properDivisors, mem_divisors] at hd
      exact dvd_trans (dvd_mul_right 2 y) hd.1.1
    exact hm_odd this
  have hd3 : d ≥ 3 := by
    have : d ≠ 2 := by
      rintro rfl
      exact hd_odd (dvd_refl 2)
    omega
  have h_one_mem : 1 ∈ m.properDivisors := by
    rw [mem_properDivisors, mem_divisors]
    refine ⟨⟨one_dvd m, hm0⟩, by omega⟩
  have hd_ne_one : d ≠ 1 := by omega
  rw [sum_eq_add_sum_diff_singleton h_one_mem]
  have h_one_mem' : d ∈ m.properDivisors \ {1} := by
    rw [mem_sdiff, mem_singleton]
    exact ⟨hd, hd_ne_one⟩
  rw [sum_eq_add_sum_diff_singleton h_one_mem']
  have h_rest : ((m.properDivisors \ {1}) \ {d}).sum (fun d => (d : ℤ)) ≥ 0 := by
    apply sum_nonneg
    intro x _
    positivity
  linarith

lemma sum_properDivisors_le_three (m : ℕ) (hm_odd : ¬ 2 ∣ m) (hm3 : m ≥ 3) :
    3 * (sigma m - m : ℤ) ≤ ((m.divisors.card : ℤ) - 1) * (m : ℤ) := by
  have hm0 : m ≠ 0 := by omega
  have h_sum_prop : m.properDivisors.sum (fun d => (d : ℤ)) = sigma m - m := by
    exact sum_properDivisors_eq_sigma_sub_self m hm0
  rw [← h_sum_prop]
  rw [mul_sum]
  have h_le : m.properDivisors.sum (fun d => 3 * (d : ℤ)) ≤ m.properDivisors.sum (fun d => (m : ℤ)) := by
    apply sum_le_sum
    intro d hd
    by_cases hd1 : d = 1
    · rw [hd1]
      push_cast
      omega
    · have hd_gt1 : d > 1 := by
        rw [mem_properDivisors] at hd
        have hd_pos : d > 0 := Nat.pos_of_ne_zero (by
          rw [mem_divisors] at hd
          exact hd.1.1.2)
        omega
      have h3d := proper_divisor_le_div_three m d hm_odd hd hd_gt1
      exact_mod_cast h3d
  have h_sum_const : m.properDivisors.sum (fun d => (m : ℤ)) =
      (((m.properDivisors.card : ℕ) : ℤ) * (m : ℤ)) := by
    rw [sum_const]
    ring
  rw [h_sum_const] at h_le
  have h_prop_card : (m.properDivisors.card : ℤ) = (m.divisors.card : ℤ) - 1 := by
    have h_insert : m.divisors = insert m m.properDivisors := by
      exact (insert_self_properDivisors hm0).symm
    have h_not_mem : m ∉ m.properDivisors := self_notMem_properDivisors
    have h_card : (m.divisors.card : ℤ) = (m.properDivisors.card : ℤ) + 1 := by
      rw [h_insert, card_insert_of_notMem h_not_mem]
      push_cast
      rfl
    omega
  rw [h_prop_card] at h_le
  exact_mod_cast h_le


lemma sum_properDivisors_le_fifteen (m : ℕ) (hm_odd : ¬ 2 ∣ m) (hm3 : m ≥ 3) :
    15 * (sigma m - m : ℤ) ≤ (3 * (m.divisors.card : ℤ) - 1) * (m : ℤ) := by
  have hm0 : m ≠ 0 := by omega
  have h_sum_prop : m.properDivisors.sum (fun d => (d : ℤ)) = sigma m - m := by
    exact sum_properDivisors_eq_sigma_sub_self m hm0
  rw [← h_sum_prop]
  rw [mul_sum]
  set T := (m.divisors.card : ℤ)
  set M := (m : ℤ)
  have h_prop_card : (m.properDivisors.card : ℤ) = (m.divisors.card : ℤ) - 1 := by
    have h_insert : m.divisors = insert m m.properDivisors := by
      exact (insert_self_properDivisors hm0).symm
    have h_not_mem : m ∉ m.properDivisors := self_notMem_properDivisors
    have h_card : (m.divisors.card : ℤ) = (m.properDivisors.card : ℤ) + 1 := by
      rw [h_insert, card_insert_of_notMem h_not_mem]
      push_cast
      rfl
    omega
  by_cases h_div3 : 3 ∣ m
  · obtain ⟨d0, hd0⟩ := h_div3
    have hd0_prop : m / 3 ∈ m.properDivisors := by
      rw [mem_properDivisors, mem_divisors]
      refine ⟨⟨?_, hm0⟩, ?_⟩
      · use 3
        omega
      · omega
    have hd0_val : 3 * (m / 3) = m := by omega
    rw [sum_eq_add_sum_diff_singleton hd0_prop]
    have h_term : 15 * ((m / 3 : ℕ) : ℤ) = 5 * M := by
      push_cast
      omega
    rw [h_term]
    have h_le : (m.properDivisors \ {m / 3}).sum (fun d => 15 * (d : ℤ)) ≤
        (m.properDivisors \ {m / 3}).sum (fun d => 3 * M) := by
      apply sum_le_sum
      intro d hd
      rw [mem_sdiff, mem_singleton] at hd
      have hd_gt1 : d > 1 := by
        rw [mem_properDivisors] at hd
        have hd_pos : d > 0 := Nat.pos_of_ne_zero (by
          rw [mem_divisors] at hd
          exact hd.1.1.2)
        omega
      have h3d := proper_divisor_le_div_three m d hm_odd hd.1 hd_gt1
      have hd_ne_div3 : d ≠ m / 3 := hd.2
      have h5d : 5 * d ≤ m := by
        rw [mem_properDivisors] at hd
        obtain ⟨hd_div, hd_lt⟩ := hd.1
        rw [mem_divisors] at hd_div
        obtain ⟨⟨c, rfl⟩, _⟩ := hd_div
        have hc_odd : ¬ 2 ∣ c := by
          rintro ⟨y, rfl⟩
          have : 2 ∣ m := by
            exact dvd_trans (dvd_mul_right 2 y) (dvd_mul_right (2 * y) d)
          exact hm_odd this
        have hc_gt1 : c > 1 := by
          rintro rfl
          simp at hd_lt
        have hc_ne3 : c ≠ 3 := by
          rintro rfl
          apply hd_ne_div3
          omega
        have hc_ge5 : c ≥ 5 := by omega
        nlinarith
      linarith
    have h_sum_const : (m.properDivisors \ {m / 3}).sum (fun d => 3 * M) =
        (((m.properDivisors \ {m / 3}).card : ℕ) : ℤ) * (3 * M) := by
      rw [sum_const]
      ring
    rw [h_sum_const] at h_le
    have h_card_eq : (((m.properDivisors \ {m / 3}).card : ℕ) : ℤ) = T - 2 := by
      rw [card_sdiff, card_singleton]
      · push_cast
        omega
      · rw [singleton_subset_iff]
        exact hd0_prop
    rw [h_card_eq] at h_le
    linarith
  · have h_le : m.properDivisors.sum (fun d => 15 * (d : ℤ)) ≤
        m.properDivisors.sum (fun d => 3 * M) := by
      apply sum_le_sum
      intro d hd
      have hd_gt1 : d > 1 := by
        rw [mem_properDivisors] at hd
        have hd_pos : d > 0 := Nat.pos_of_ne_zero (by
          rw [mem_divisors] at hd
          exact hd.1.1.2)
        omega
      have hd_ne_div3 : d ≠ m / 3 := by
        rintro rfl
        apply h_div3
        use d
        omega
      rw [mem_properDivisors] at hd
      obtain ⟨hd_div, hd_lt⟩ := hd
      rw [mem_divisors] at hd_div
      obtain ⟨⟨c, rfl⟩, _⟩ := hd_div
      have hc_odd : ¬ 2 ∣ c := by
        rintro ⟨y, rfl⟩
        have : 2 ∣ m := by
          exact dvd_trans (dvd_mul_right 2 y) (dvd_mul_right (2 * y) d)
        exact hm_odd this
      have hc_gt1 : c > 1 := by
        rintro rfl
        simp at hd_lt
      have hc_ne3 : c ≠ 3 := by
        rintro rfl
        apply hd_ne_div3
        omega
      have hc_ge5 : c ≥ 5 := by omega
      nlinarith
    have h_sum_const : m.properDivisors.sum (fun d => 3 * M) =
        (((m.properDivisors.card : ℕ) : ℤ) * (3 * M)) := by
      rw [sum_const]
      ring
    rw [h_sum_const] at h_le
    rw [h_prop_card] at h_le
    linarith


lemma sum_properDivisors_le_105 (m : ℕ) (hm_odd : ¬ 2 ∣ m) (hm3 : m ≥ 3) :
    105 * (sigma m - m : ℤ) ≤ (15 * (m.divisors.card : ℤ) - 4) * (m : ℤ) + 105 := by
  have hm0 : m ≠ 0 := by omega
  have h_sum_prop : m.properDivisors.sum (fun d => (d : ℤ)) = sigma m - m := by
    exact sum_properDivisors_eq_sigma_sub_self m hm0
  rw [← h_sum_prop]
  rw [mul_sum]
  set T := (m.divisors.card : ℤ)
  set M := (m : ℤ)
  have h_prop_card : (m.properDivisors.card : ℤ) = (m.divisors.card : ℤ) - 1 := by
    have h_insert : m.divisors = insert m m.properDivisors := by
      exact (insert_self_properDivisors hm0).symm
    have h_not_mem : m ∉ m.properDivisors := self_notMem_properDivisors
    have h_card : (m.divisors.card : ℤ) = (m.properDivisors.card : ℤ) + 1 := by
      rw [h_insert, card_insert_of_notMem h_not_mem]
      push_cast
      rfl
    omega
  by_cases h3 : 3 ∣ m
  · obtain ⟨d3, hd3_eq⟩ := h3
    have hd3_prop : m / 3 ∈ m.properDivisors := by
      rw [mem_properDivisors, mem_divisors]
      refine ⟨⟨?_, hm0⟩, ?_⟩
      · use 3; omega
      · omega
    have hd3_val : 3 * (m / 3) = m := by omega
    by_cases h5 : 5 ∣ m
    · obtain ⟨d5, hd5_eq⟩ := h5
      have hd5_prop : m / 5 ∈ m.properDivisors := by
        rw [mem_properDivisors, mem_divisors]
        refine ⟨⟨?_, hm0⟩, ?_⟩
        · use 5; omega
        · omega
      have hd5_val : 5 * (m / 5) = m := by omega
      have h_ne : m / 3 ≠ m / 5 := by
        intro heq
        have : 3 * (m / 3) = 5 * (m / 5) := by omega
        rw [hd3_val, hd5_val] at this
        have h35 : (3 : ℕ) * (m / 3) = 5 * (m / 3) := by omega
        have h_div_zero : m / 3 = 0 := by omega
        have : m = 0 := by omega
        contradiction
      rw [sum_eq_add_sum_diff_singleton hd3_prop]
      rw [sum_eq_add_sum_diff_singleton (by
        rw [mem_sdiff, mem_singleton]
        exact ⟨hd5_prop, h_ne.symm⟩)]
      have h_term1 : 105 * ((m / 3 : ℕ) : ℤ) = 35 * M := by push_cast; omega
      have h_term2 : 105 * ((m / 5 : ℕ) : ℤ) = 21 * M := by push_cast; omega
      have h_le : ((m.properDivisors \ {m / 3}) \ {m / 5}).sum (fun d => 105 * (d : ℤ)) ≤
          ((m.properDivisors \ {m / 3}) \ {m / 5}).sum (fun d => 15 * M) := by
        apply sum_le_sum
        intro d hd
        rw [mem_sdiff, mem_sdiff, mem_singleton, mem_singleton] at hd
        have hd_gt1 : d > 1 := by
          rw [mem_properDivisors] at hd
          have hd_pos : d > 0 := Nat.pos_of_ne_zero (by
            rw [mem_divisors] at hd
            exact hd.1.1.1.2)
          omega
        have h15 : 15 * d ≤ m := by
          rw [mem_properDivisors] at hd
          obtain ⟨hd_div, hd_lt⟩ := hd.1.1
          rw [mem_divisors] at hd_div
          obtain ⟨⟨c, rfl⟩, _⟩ := hd_div
          have hc_odd : ¬ 2 ∣ c := by
            rintro ⟨y, rfl⟩
            have : 2 ∣ m := by
              exact dvd_trans (dvd_mul_right 2 y) (dvd_mul_right (2 * y) d)
            exact hm_odd this
          have hc_gt1 : c > 1 := by
            rintro rfl
            simp at hd_lt
          have hc_ne3 : c ≠ 3 := by
            rintro rfl
            apply hd.1.2
            omega
          have hc_ne5 : c ≠ 5 := by
            rintro rfl
            apply hd.2
            omega
          have hc_ge7 : c ≥ 7 := by omega
          nlinarith
        linarith
      have h_sum_const : ((m.properDivisors \ {m / 3}) \ {m / 5}).sum (fun d => 15 * M) =
          ((((m.properDivisors \ {m / 3}) \ {m / 5}).card : ℕ) : ℤ) * (15 * M) := by
        rw [sum_const]
        ring
      rw [h_sum_const] at h_le
      have h_card_eq : ((((m.properDivisors \ {m / 3}) \ {m / 5}).card : ℕ) : ℤ) = T - 3 := by
        rw [card_sdiff, card_singleton]
        · rw [card_sdiff, card_singleton]
          · push_cast; omega
          · rw [singleton_subset_iff]; exact hd3_prop
        · rw [singleton_subset_iff, mem_sdiff, mem_singleton]
          exact ⟨hd5_prop, h_ne.symm⟩
      rw [h_card_eq] at h_le
      linarith
    · rw [sum_eq_add_sum_diff_singleton hd3_prop]
      have h_term1 : 105 * ((m / 3 : ℕ) : ℤ) = 35 * M := by push_cast; omega
      have h_le : (m.properDivisors \ {m / 3}).sum (fun d => 105 * (d : ℤ)) ≤
          (m.properDivisors \ {m / 3}).sum (fun d => 15 * M) := by
        apply sum_le_sum
        intro d hd
        rw [mem_sdiff, mem_singleton] at hd
        have hd_gt1 : d > 1 := by
          rw [mem_properDivisors] at hd
          have hd_pos : d > 0 := Nat.pos_of_ne_zero (by
            rw [mem_divisors] at hd
            exact hd.1.1.2)
          omega
        have h15 : 15 * d ≤ m := by
          rw [mem_properDivisors] at hd
          obtain ⟨hd_div, hd_lt⟩ := hd.1
          rw [mem_divisors] at hd_div
          obtain ⟨⟨c, rfl⟩, _⟩ := hd_div
          have hc_odd : ¬ 2 ∣ c := by
            rintro ⟨y, rfl⟩
            have : 2 ∣ m := by
              exact dvd_trans (dvd_mul_right 2 y) (dvd_mul_right (2 * y) d)
            exact hm_odd this
          have hc_gt1 : c > 1 := by
            rintro rfl
            simp at hd_lt
          have hc_ne3 : c ≠ 3 := by
            rintro rfl
            apply hd.2
            omega
          have : ¬ 5 ∣ m := h5
          have hc_ne5 : c ≠ 5 := by
            rintro rfl
            apply h5
            use d
            omega
          have hc_ge7 : c ≥ 7 := by omega
          nlinarith
        linarith
      have h_sum_const : (m.properDivisors \ {m / 3}).sum (fun d => 15 * M) =
          (((m.properDivisors \ {m / 3}).card : ℕ) : ℤ) * (15 * M) := by
        rw [sum_const]
        ring
      rw [h_sum_const] at h_le
      have h_card_eq : (((m.properDivisors \ {m / 3}).card : ℕ) : ℤ) = T - 2 := by
        rw [card_sdiff, card_singleton]
        · push_cast; omega
        · rw [singleton_subset_iff]; exact hd3_prop
      rw [h_card_eq] at h_le
      linarith
  · by_cases h5 : 5 ∣ m
    · obtain ⟨d5, hd5_eq⟩ := h5
      have hd5_prop : m / 5 ∈ m.properDivisors := by
        rw [mem_properDivisors, mem_divisors]
        refine ⟨⟨?_, hm0⟩, ?_⟩
        · use 5; omega
        · omega
      have hd5_val : 5 * (m / 5) = m := by omega
      rw [sum_eq_add_sum_diff_singleton hd5_prop]
      have h_term2 : 105 * ((m / 5 : ℕ) : ℤ) = 21 * M := by push_cast; omega
      have h_le : (m.properDivisors \ {m / 5}).sum (fun d => 105 * (d : ℤ)) ≤
          (m.properDivisors \ {m / 5}).sum (fun d => 15 * M) := by
        apply sum_le_sum
        intro d hd
        rw [mem_sdiff, mem_singleton] at hd
        have hd_gt1 : d > 1 := by
          rw [mem_properDivisors] at hd
          have hd_pos : d > 0 := Nat.pos_of_ne_zero (by
            rw [mem_divisors] at hd
            exact hd.1.1.2)
          omega
        have h15 : 15 * d ≤ m := by
          rw [mem_properDivisors] at hd
          obtain ⟨hd_div, hd_lt⟩ := hd.1
          rw [mem_divisors] at hd_div
          obtain ⟨⟨c, rfl⟩, _⟩ := hd_div
          have hc_odd : ¬ 2 ∣ c := by
            rintro ⟨y, rfl⟩
            have : 2 ∣ m := by
              exact dvd_trans (dvd_mul_right 2 y) (dvd_mul_right (2 * y) d)
            exact hm_odd this
          have hc_gt1 : c > 1 := by
            rintro rfl
            simp at hd_lt
          have : ¬ 3 ∣ m := h3
          have hc_ne3 : c ≠ 3 := by
            rintro rfl
            apply h3
            use d
            omega
          have hc_ne5 : c ≠ 5 := by
            rintro rfl
            apply hd.2
            omega
          have hc_ge7 : c ≥ 7 := by omega
          nlinarith
        linarith
      have h_sum_const : (m.properDivisors \ {m / 5}).sum (fun d => 15 * M) =
          (((m.properDivisors \ {m / 5}).card : ℕ) : ℤ) * (15 * M) := by
        rw [sum_const]
        ring
      rw [h_sum_const] at h_le
      have h_card_eq : (((m.properDivisors \ {m / 5}).card : ℕ) : ℤ) = T - 2 := by
        rw [card_sdiff, card_singleton]
        · push_cast; omega
        · rw [singleton_subset_iff]; exact hd5_prop
      rw [h_card_eq] at h_le
      linarith
    · have h_le : m.properDivisors.sum (fun d => 105 * (d : ℤ)) ≤
          m.properDivisors.sum (fun d => 15 * M) := by
        apply sum_le_sum
        intro d hd
        have hd_gt1 : d > 1 := by
          rw [mem_properDivisors] at hd
          have hd_pos : d > 0 := Nat.pos_of_ne_zero (by
            rw [mem_divisors] at hd
            exact hd.1.1.2)
          omega
        have h15 : 15 * d ≤ m := by
          rw [mem_properDivisors] at hd
          obtain ⟨hd_div, hd_lt⟩ := hd
          rw [mem_divisors] at hd_div
          obtain ⟨⟨c, rfl⟩, _⟩ := hd_div
          have hc_odd : ¬ 2 ∣ c := by
            rintro ⟨y, rfl⟩
            have : 2 ∣ m := by
              exact dvd_trans (dvd_mul_right 2 y) (dvd_mul_right (2 * y) d)
            exact hm_odd this
          have hc_gt1 : c > 1 := by
            rintro rfl
            simp at hd_lt
          have : ¬ 3 ∣ m := h3
          have hc_ne3 : c ≠ 3 := by
            rintro rfl
            apply h3
            use d
            omega
          have : ¬ 5 ∣ m := h5
          have hc_ne5 : c ≠ 5 := by
            rintro rfl
            apply h5
            use d
            omega
          have hc_ge7 : c ≥ 7 := by omega
          nlinarith
        linarith
      have h_sum_const : m.properDivisors.sum (fun d => 15 * M) =
          (((m.properDivisors.card : ℕ) : ℤ) * (15 * M)) := by
        rw [sum_const]
        ring
      rw [h_sum_const] at h_le
      rw [h_prop_card] at h_le
      linarith

lemma k_ineq (k : ℕ) (hk : k ≥ 1) : 3 * ((k : ℤ) * (2^(k+1) : ℤ) + 1) ≥ 5 * ((2^(k+1) : ℤ) - 1) := by
  rcases k with _ | k'
  · contradiction
  · rcases k' with _ | k''
    · decide
    · have h_expr : 3 * (((k'' + 2 : ℕ) : ℤ) * (2^(k'' + 3) : ℤ) + 1) - 5 * ((2^(k'' + 3) : ℤ) - 1) = (3 * (k'' : ℤ) + 1) * (2^(k'' + 3) : ℤ) + 8 := by
        push_cast
        ring
      have h_ge : (3 * (k'' : ℤ) + 1) * (2^(k'' + 3) : ℤ) + 8 ≥ 0 := by
        have : (3 * (k'' : ℤ) + 1) ≥ 0 := by omega
        have h_pow_pos : (2^(k'' + 3) : ℤ) ≥ 0 := by positivity
        positivity
      linarith

lemma three_D_ge_five_C_prime (k m : ℕ) (hm_odd : ¬ 2 ∣ m) (hm3 : m ≥ 3) (heq : a (2 ^ k * m) = sigma (2 ^ k * m)) (hk : k ≥ 1) :
    3 * ((m : ℤ) * m.divisors.card - sigma m) ≥ 5 * (m.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) - (m : ℤ) * m.divisors.card) := by
  have h_C_prime_D := C_prime_D_eq k m hm_odd heq
  have h_C_prime_pos := C_prime_pos m hm3
  set D := ((m : ℤ) * m.divisors.card - sigma m)
  set C_prime := (m.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) - (m : ℤ) * m.divisors.card)
  have h_two_pow_pos : (2^(k+1) : ℤ) - 1 > 0 := by
    have h_pow_ge : (2^(k+1) : ℕ) ≥ 4 := by
      have : k + 1 ≥ 2 := by omega
      exact Nat.pow_le_pow_right (by decide : 0 < 2) this
    have h_pow_ge_cast : (2^(k+1) : ℤ) ≥ 4 := by exact_mod_cast h_pow_ge
    omega
  have h_k_ineq := k_ineq k hk
  have h_mul : 3 * ((2^(k+1) : ℤ) - 1) * D = 3 * ((k : ℤ) * 2^(k+1) + 1) * C_prime := by
    calc 3 * ((2^(k+1) : ℤ) - 1) * D
      _ = 3 * (((2^(k+1) : ℤ) - 1) * D) := by ring
      _ = 3 * (((k : ℤ) * 2^(k+1) + 1) * C_prime) := by rw [h_C_prime_D]
      _ = 3 * ((k : ℤ) * 2^(k+1) + 1) * C_prime := by ring
  have h_le : 5 * ((2^(k+1) : ℤ) - 1) * C_prime ≤ 3 * ((k : ℤ) * 2^(k+1) + 1) * C_prime := by
    nlinarith [h_k_ineq, h_C_prime_pos]
  have h_final : 5 * ((2^(k+1) : ℤ) - 1) * C_prime ≤ 3 * ((2^(k+1) : ℤ) - 1) * D := by
    linarith [h_mul, h_le]
  nlinarith [h_final, h_two_pow_pos]



/--
%C A245212 Conjecture: a(n) = sigma(n) iff n is a power of 2 (A000079).
-/
theorem oeis_245212_conjecture_0 (n : ℕ) (h : n > 0) :
    a n = sigma n ↔ n.isPowerOfTwo := by
  constructor
  · intro heq
    obtain ⟨k, m, rfl, hm⟩ := exists_odd_part n h
    rw [isPowerOfTwo_iff_odd_part_eq_one k m hm]
    by_contra h_ne_one
    have hm3 : m ≥ 3 := by
      have h_m_ne_zero : m ≠ 0 := by
        rintro rfl
        simp at h
      have h_m_ne_one : m ≠ 1 := h_ne_one
      omega
    by_cases hp : m.Prime
    · exact prime_case k m hp hm3 heq
    · have h_lt := C_plus_S_lt_m_plus_tau_S m hm hm3 hp
      have h_rel := Y_relation k m hm hm3 heq
      have h_pos := Y_pos k m hm hm3 heq
      set M := (m : ℤ)
      set T := (m.divisors.card : ℤ)
      set S := sigma m
      set C_prime := m.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) - M * T
      set D := M * T - S
      set Y := D - k * C_prime
      have h_sum_add : m.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ) + (d : ℤ)) =
          C_prime + M * T + S := by
        unfold sigma
        rw [sum_add_distrib]
        linarith
      rw [h_sum_add] at h_lt
      have h_C_lt : C_prime < (T - 1) * (S - M) := by linarith [h_lt]
      have h_S_sub_M : S - M = M * (T - 1) - D := by linarith
      rw [h_S_sub_M] at h_C_lt
      have h_C_lt' : C_prime + (T - 1) * D < M * (T - 1) * (T - 1) := by linarith [h_C_lt]
      by_cases hk : k = 0
      · have h_Y_eq : Y = D := by
          subst hk
          simp [Y]
        have h_rel_k0 : (2 ^ (0 + 1) - 1 : ℤ) * Y = (0 + 1 : ℤ) * C_prime := by
          rw [hk] at h_rel
          exact h_rel
        have h_D_eq_C : D = C_prime := by
          rw [h_Y_eq] at h_rel_k0
          norm_num at h_rel_k0
          exact h_rel_k0
        have h_M_T_lt : M * (T - 1) < T * (S - M) := by
          linarith [h_C_lt', h_D_eq_C, h_S_sub_M]
        have h_T_ge3 : T ≥ 3 := by
          have hm0 : m ≠ 0 := by omega
          have hm1 : m ≠ 1 := by omega
          obtain ⟨d, hd, hd_gt1⟩ := exists_proper_divisor_of_composite m hm3 hp
          have h_sub : {1, d, m} ⊆ m.divisors := by
            rw [insert_subset_iff, insert_subset_iff, singleton_subset_iff]
            have h1 : 1 ∈ m.divisors := by rw [mem_divisors]; exact ⟨one_dvd m, hm0⟩
            have h2 : d ∈ m.divisors := by
              have : d ∣ m := (mem_properDivisors.mp hd).1
              rw [mem_divisors]
              exact ⟨this, hm0⟩
            have h3 : m ∈ m.divisors := by rw [mem_divisors]; exact ⟨dvd_rfl, hm0⟩
            exact ⟨h1, h2, h3⟩
          have h_card := card_le_card h_sub
          have h_three : ({1, d, m} : Finset ℕ).card = 3 := by
            rw [card_insert_of_notMem, card_insert_of_notMem]
            · rw [card_singleton]
            · simp [hd_gt1]
            · have hd_lt : d < m := (mem_properDivisors.mp hd).2
              simp [hd_lt.ne]
          have h_T_nat : m.divisors.card ≥ 3 := by omega
          by omega
        by_cases hT3 : T = 3
        · have h_le := sum_properDivisors_le_three m hm hm3
          linarith [h_M_T_lt, h_le, hT3]
        · have h_T_ge4 : T ≥ 4 := by omega
          have h_comp_le := sum_properDivisors_le_of_composite m hm hm3 hp
          by_cases h_T4 : T = 4
          · have h_ineq : (5 * T - T * T - 3) * M < 3 * T := by
              nlinarith [h_M_T_lt, h_comp_le]
            have h_M_lt12 : M < 12 := by
              rw [h_T4] at h_ineq
              linarith [h_ineq]
            have h_m_lt12 : m < 12 := by by omega
            have h_m9 : m = 9 := by
              have h_m_ge9 := m_ge_9 m hm hm3 hp
              have h_m_ne11 : m ≠ 11 := by
                rintro rfl
                exact hp (by decide)
              have h_m_ne10 : m ≠ 10 := by
                rintro rfl
                exact hm (by decide)
              omega
            have h_card9 : (9 : ℕ).divisors.card = 3 := by decide
            have h_T3_9 : T = 3 := by
              subst h_m9
              by omega
            omega
          · -- T ≥ 5
            by_cases hT5 : T = 5
            · have h_ineq : (-15 * T * T + 109 * T - 105) * M < 105 * T := by
                nlinarith [h_M_T_lt, sum_properDivisors_le_105 m hm hm3]
              have h_M_lt : M < 9 := by
                rw [hT5] at h_ineq
                linarith [h_ineq]
              have h_m_ge9 := m_ge_9 m hm hm3 hp
              omega
            · by_cases hT6 : T = 6
              · have h_ineq : (-15 * T * T + 109 * T - 105) * M < 105 * T := by
                  nlinarith [h_M_T_lt, sum_properDivisors_le_105 m hm hm3]
                have h_M_lt : M < 70 := by
                  rw [hT6] at h_ineq
                  linarith [h_ineq]
                have h_ne11 : m ≠ 11 := by rintro rfl; exact hp (by decide)
                have h_ne13 : m ≠ 13 := by rintro rfl; exact hp (by decide)
                have h_ne17 : m ≠ 17 := by rintro rfl; exact hp (by decide)
                have h_ne19 : m ≠ 19 := by rintro rfl; exact hp (by decide)
                have h_ne23 : m ≠ 23 := by rintro rfl; exact hp (by decide)
                have h_ne29 : m ≠ 29 := by rintro rfl; exact hp (by decide)
                have h_ne31 : m ≠ 31 := by rintro rfl; exact hp (by decide)
                have h_ne37 : m ≠ 37 := by rintro rfl; exact hp (by decide)
                have h_ne41 : m ≠ 41 := by rintro rfl; exact hp (by decide)
                have h_ne43 : m ≠ 43 := by rintro rfl; exact hp (by decide)
                have h_ne47 : m ≠ 47 := by rintro rfl; exact hp (by decide)
                have h_ne53 : m ≠ 53 := by rintro rfl; exact hp (by decide)
                have h_ne59 : m ≠ 59 := by rintro rfl; exact hp (by decide)
                have h_ne61 : m ≠ 61 := by rintro rfl; exact hp (by decide)
                have h_ne67 : m ≠ 67 := by rintro rfl; exact hp (by decide)
                have h_m_ge9 := m_ge_9 m hm hm3 hp
                have h_or : m = 9 ∨ m = 15 ∨ m = 21 ∨ m = 25 ∨ m = 27 ∨ m = 33 ∨ m = 35 ∨ m = 39 ∨ m = 45 ∨ m = 49 ∨ m = 51 ∨ m = 55 ∨ m = 57 ∨ m = 63 ∨ m = 65 ∨ m = 69 := by omega
                rcases h_or with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
                · have h_div : (9 : ℕ).divisors.card = 3 := by decide
                  rw [h_div] at hT6; norm_num at hT6
                · have h_div : (15 : ℕ).divisors.card = 4 := by decide
                  rw [h_div] at hT6; norm_num at hT6
                · have h_div : (21 : ℕ).divisors.card = 4 := by decide
                  rw [h_div] at hT6; norm_num at hT6
                · have h_div : (25 : ℕ).divisors.card = 3 := by decide
                  rw [h_div] at hT6; norm_num at hT6
                · have h_div : (27 : ℕ).divisors.card = 4 := by decide
                  rw [h_div] at hT6; norm_num at hT6
                · have h_div : (33 : ℕ).divisors.card = 4 := by decide
                  rw [h_div] at hT6; norm_num at hT6
                · have h_div : (35 : ℕ).divisors.card = 4 := by decide
                  rw [h_div] at hT6; norm_num at hT6
                · have h_div : (39 : ℕ).divisors.card = 4 := by decide
                  rw [h_div] at hT6; norm_num at hT6
                · revert heq; decide
                · have h_div : (49 : ℕ).divisors.card = 3 := by decide
                  rw [h_div] at hT6; norm_num at hT6
                · have h_div : (51 : ℕ).divisors.card = 4 := by decide
                  rw [h_div] at hT6; norm_num at hT6
                · have h_div : (55 : ℕ).divisors.card = 4 := by decide
                  rw [h_div] at hT6; norm_num at hT6
                · have h_div : (57 : ℕ).divisors.card = 4 := by decide
                  rw [h_div] at hT6; norm_num at hT6
                · revert heq; decide
                · have h_div : (65 : ℕ).divisors.card = 4 := by decide
                  rw [h_div] at hT6; norm_num at hT6
                · have h_div : (69 : ℕ).divisors.card = 4 := by decide
                  rw [h_div] at hT6; norm_num at hT6
              · sorry
      · -- k ≥ 1
        have hk_ge1 : k ≥ 1 := by omega
        have h_three_D := three_D_ge_five_C_prime k m hm hm3 heq hk_ge1
        have h_comp_le := sum_properDivisors_le_of_composite m hm hm3 hp
        have h_C_ge := C_prime_ge_two_sigma_sub_m m hm3
        by_cases hT3 : T = 3
        · have h_four := sigma_sub_self_ge_four m hm hm3 hp
          linarith [h_three_D, h_comp_le, h_C_ge, h_S_sub_M, h_four, hT3]
        · have h_T_ge4 : T ≥ 4 := by omega
          by_cases hT4 : T = 4
          · have h_fifteen := sum_properDivisors_le_fifteen m hm hm3
            have h_four := sigma_sub_self_ge_four m hm hm3 hp
            linarith [h_three_D, h_comp_le, h_C_ge, h_S_sub_M, h_four, hT4, h_fifteen]
          · have h_T_ge5 : T ≥ 5 := by omega
            have h_algebra : 9 * (T - 1) ≤ 12 * (T - 2) := by omega
            have h_four := sigma_sub_self_ge_four m hm hm3 hp
            have h_le : (m.properDivisors \ {1}).sum (fun d => (3 : ℤ)) ≤ (m.properDivisors \ {1}).sum (fun d => (d : ℤ)) := by
              apply sum_le_sum
              intro d hd
              have h_sdiff := mem_sdiff.mp hd
              have hd_prop : d ∈ m.properDivisors := h_sdiff.1
              have hd_ne_one : d ≠ 1 := by
                have : d ∉ {1} := h_sdiff.2
                simp at this; exact this
              have hd_ne_zero : d ≠ 0 := by
                have : d ∣ m := (mem_properDivisors.mp hd_prop).1
                rintro rfl
                have : m = 0 := zero_dvd_iff.mp this
                omega
              have hd_odd : ¬ 2 ∣ d := by
                rintro ⟨y, rfl⟩
                have : 2 ∣ m := dvd_trans (dvd_mul_right 2 y) (mem_properDivisors.mp hd_prop).1
                exact hm this
              omega
            rw [sum_const] at h_le
            have h_card_eq : (m.properDivisors \ {1}).card = m.divisors.card - 2 := by
              have h_prop_card : m.properDivisors.card = m.divisors.card - 1 := by
                have hm0 : m ≠ 0 := by omega
                have h_insert : m.divisors = insert m m.properDivisors := by
                  exact (insert_self_properDivisors hm0).symm
                have h_not_mem : m ∉ m.properDivisors := self_notMem_properDivisors
                rw [h_insert, card_insert_of_notMem h_not_mem]
                omega
              have h_one_mem : 1 ∈ m.properDivisors := mem_properDivisors.mpr ⟨one_dvd m, by omega⟩
              have h_subset : {1} ⊆ m.properDivisors := by
                rw [singleton_subset_iff]
                exact h_one_mem
              rw [card_sdiff_of_subset h_subset, card_singleton]
              omega
            have h_cast : (((m.properDivisors \ {1}).card : ℕ) : ℤ) = T - 2 := by
              rw [h_card_eq]
              omega
            rw [h_cast, nsmul_eq_mul] at h_le
            have h_sum_prop : (m.properDivisors \ {1}).sum (fun d => (d : ℤ)) = sigma m - m - 1 := by
              have h_one_mem : 1 ∈ m.properDivisors := mem_properDivisors.mpr ⟨one_dvd m, by omega⟩
              have h_split : m.properDivisors.sum (fun d => (d : ℤ)) = 1 + (m.properDivisors \ {1}).sum (fun d => (d : ℤ)) := by
                rw [sum_eq_add_sum_diff_singleton h_one_mem]
                ring
              have h_sum : m.properDivisors.sum (fun d => (d : ℤ)) = sigma m - m := by
                have hm0 : m ≠ 0 := by omega
                exact sum_properDivisors_eq_sigma_sub_self m hm0
              rw [h_sum] at h_split
              simp only [Nat.cast_one] at h_split
              linarith
            rw [h_sum_prop] at h_le
            linarith [h_three_D, h_comp_le, h_C_ge, h_S_sub_M, h_four, h_le, h_algebra]
  · rintro ⟨k, rfl⟩
    exact a_eq_sigma_two_pow k

