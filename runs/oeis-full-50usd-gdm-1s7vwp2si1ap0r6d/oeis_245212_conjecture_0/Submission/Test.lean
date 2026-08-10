import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℤ :=
  (n : ℤ) * (n.divisors.card : ℤ) - n.properDivisors.sum
    (fun d => (d : ℤ) * (d.divisors.card : ℤ))

def sigma (n : ℕ) : ℤ :=
  n.divisors.sum (fun d => (d : ℤ))

lemma a_def_alternative (n : ℕ) (hn : n > 0) :
    a n = 2 * (n : ℤ) * (n.divisors.card : ℤ) - n.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) := by
  have h_insert : n.divisors = insert n n.properDivisors := by
    exact (insert_self_properDivisors (ne_of_gt hn)).symm
  have h_not_mem : n ∉ n.properDivisors := self_notMem_properDivisors
  have h_sum : n.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) =
      (n : ℤ) * (n.divisors.card : ℤ) + n.properDivisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) := by
    rw [h_insert, sum_insert h_not_mem]
  rw [a]
  linarith

lemma a_eq_sigma_iff (n : ℕ) (hn : n > 0) :
    a n = sigma n ↔ 2 * (n : ℤ) * (n.divisors.card : ℤ) = n.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ) + (d : ℤ)) := by
  rw [a_def_alternative n hn, sigma]
  rw [← sum_add_distrib]
  constructor
  · intro h
    linarith
  · intro h
    linarith


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
        exact Nat.lt_mul_of_pos_of_one_lt_left hd (by decide)
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
        rw [pow_succ]
        exact dvd_mul_right 2 (2 ^ i')
      contradiction
  · rintro rfl
    use k
    ring

lemma divisors_two_pow_succ_mul_odd (k m : ℕ) (hm : ¬ 2 ∣ m) :
    (2 ^ (k + 1) * m).divisors = (2 ^ k * m).divisors ∪ (m.divisors.map ⟨fun c => 2 ^ (k + 1) * c, fun c1 c2 h => by
      have h2 : 2 ^ (k + 1) ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by decide))
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_iff_ne_zero.mpr h2) h
    ⟩) := by
  sorry


lemma disjoint_divisors (k m : ℕ) (hm : ¬ 2 ∣ m) :
    Disjoint (2 ^ k * m).divisors (m.divisors.map ⟨fun c => 2 ^ (k + 1) * c, fun c1 c2 h => by
      have h2 : 2 ^ (k + 1) ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by decide))
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_iff_ne_zero.mpr h2) h
    ⟩) := by
  rw [disjoint_iff_ne]
  rintro x hx y hy rfl
  rw [mem_divisors] at hx
  rw [mem_map] at hy
  obtain ⟨c, hc, rfl⟩ := hy
  have h_dvd : 2 ^ (k + 1) ∣ 2 ^ k * m := by
    exact dvd_trans (dvd_mul_right (2 ^ (k + 1)) c) hx.1
  have h_dvd_m : 2 ∣ m := by
    have h_pow : 2 ^ (k + 1) = 2 ^ k * 2 := by ring
    rw [h_pow] at h_dvd
    have h_ne : 2 ^ k > 0 := Nat.pow_pos (by decide)
    have h_dvd' := (Nat.mul_dvd_mul_iff_left h_ne).mp h_dvd
    exact h_dvd'
  contradiction



lemma sum_divisors_decomposition (n : ℕ) (hn : n > 1) :
    (n.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ) + (d : ℤ))) =
    2 + (n : ℤ) * (n.divisors.card : ℤ) + (n : ℤ) +
    ((n.divisors \ {1, n}).sum (fun d => (d : ℤ) * (d.divisors.card : ℤ) + (d : ℤ))) := by
  have h1 : 1 ∈ n.divisors := by simp [hn.ne']
  have hn_mem : n ∈ n.divisors := by simp [hn.ne']
  have h1_ne_n : 1 ≠ n := by linarith
  have h_dec : n.divisors = insert 1 (insert n (n.divisors \ {1, n})) := by
    ext d
    simp only [mem_divisors, mem_insert, mem_sdiff, mem_pair, not_or]
    constructor
    · intro hd
      by_cases hd1 : d = 1
      · left; exact hd1
      · right
        by_cases hdn : d = n
        · left; exact hdn
        · right; exact ⟨hd, hd1, hdn⟩
    · rintro (rfl | rfl | ⟨hd, _, _⟩)
      · exact ⟨dvd_one, hn.ne'⟩
      · exact ⟨dvd_rfl, hn.ne'⟩
      · exact hd
  have h_not_mem1 : n ∉ n.divisors \ {1, n} := by simp
  have h_not_mem2 : 1 ∉ insert n (n.divisors \ {1, n}) := by
    simp [h1_ne_n.symm]
  rw [h_dec]
  rw [sum_insert h_not_mem2]
  rw [sum_insert h_not_mem1]
  have h_card1 : (1 : ℕ).divisors.card = 1 := by decide
  push_cast
  rw [h_card1]
  ring


lemma sigma_mul_of_coprime (k m : ℕ) (hm : ¬ 2 ∣ m) :
    sigma (2 ^ k * m) = sigma (2 ^ k) * sigma m := by
  have h_coprime : Nat.Coprime (2 ^ k) m := by
    exact Nat.Coprime.pow_left k (Nat.Coprime.symm (Nat.coprime_two_left_iff_not_dvd.mpr hm))
  rw [sigma, sigma, sigma]
  push_cast
  rw [← Nat.Coprime.sum_divisors_mul h_coprime]


open ArithmeticFunction

def g_fn : ArithmeticFunction ℤ :=
  (id.intCast.pmul (σ 0).intCast) * ζ

lemma g_fn_apply (n : ℕ) (hn : n > 0) : g_fn n = n.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) := by
  rw [g_fn, mul_apply]
  have h_sum : ∑ x ∈ n.divisorsAntidiagonal, (id.intCast.pmul (σ 0).intCast) x.1 * ζ x.2 =
      ∑ x ∈ n.divisors, (id.intCast.pmul (σ 0).intCast) x * ζ (n / x) := by
    exact sum_divisorsAntidiagonal_eq_sum_divisors (fun a b => (id.intCast.pmul (σ 0).intCast) a * ζ b)
  rw [h_sum]
  have h_zeta : ∀ x ∈ n.divisors, ζ (n / x) = 1 := by
    intro x hx
    rw [mem_divisors] at hx
    have h_div_pos : n / x > 0 := Nat.div_pos (by linarith [hx.2]) (Nat.pos_of_ne_zero (by linarith [hn]))
    exact zeta_apply h_div_pos
  have h_sum2 : ∑ x ∈ n.divisors, (id.intCast.pmul (σ 0).intCast) x * ζ (n / x) =
      ∑ x ∈ n.divisors, (id.intCast.pmul (σ 0).intCast) x := by
    apply sum_congr rfl
    intro x hx
    rw [h_zeta x hx]
    ring
  rw [h_sum2]
  apply sum_congr rfl
  intro x hx
  rw [pmul_apply, intCast_apply, intCast_apply, id_apply, sigma_apply]
  simp only [Nat.pow_zero]
  rfl


lemma isMultiplicative_g : g_fn.IsMultiplicative := by
  have h1 : (id.intCast.pmul (σ 0).intCast).IsMultiplicative := by
    apply IsMultiplicative.pmul
    · exact isMultiplicative_id.intCast
    · exact isMultiplicative_sigma.intCast
  exact IsMultiplicative.mul h1 isMultiplicative_zeta


lemma g_mul_of_coprime (k m : ℕ) (hm : ¬ 2 ∣ m) :
    (2 ^ k * m).divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) =
    (2 ^ k).divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) *
    m.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) := by
  have h_coprime : Nat.Coprime (2 ^ k) m := by
    exact Nat.Coprime.pow_left k (Nat.Coprime.symm (Nat.coprime_two_left_iff_not_dvd.mpr hm))
  have h_pos2 : 2 ^ k > 0 := Nat.pow_pos (by decide)
  have h_posm : m > 0 := by
    cases m with
    | zero => contradiction
    | succ m' => exact Nat.succ_pos m'
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
    ((2 ^ k).divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ))) = k * (2 : ℤ) ^ (k + 1) + 1 := by
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
    push_cast
    rw [h_card]
    ring

lemma sum_divisors_two_pow_mul_odd (k m : ℕ) (hm : ¬ 2 ∣ m) :
    ((2 ^ k * m).divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ) + (d : ℤ))) =
    (k * 2 ^ (k + 1) + 1) * (m.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ))) +
    (2 ^ (k + 1) - 1) * sigma m := by
  rw [sum_add_distrib]
  rw [g_mul_of_coprime k m hm]
  rw [sigma_mul_of_coprime k m hm]
  rw [g_two_pow k]
  rw [sigma_two_pow k]

lemma left_side_two_pow_mul_odd (k m : ℕ) (hm : ¬ 2 ∣ m) :
    2 * (2 ^ k * m : ℤ) * ((2 ^ k * m).divisors.card : ℤ) = (k + 1) * 2 ^ (k + 1) * m * m.divisors.card := by
  have h_coprime : Nat.Coprime (2 ^ k) m := by
    exact Nat.Coprime.pow_left k (Nat.Coprime.symm (Nat.coprime_two_left_iff_not_dvd.mpr hm))
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
    have h2 : m > 0 := by
      cases m with
      | zero => contradiction
      | succ m' => exact Nat.succ_pos m'
    exact Nat.mul_pos h1 h2
  rw [a_eq_sigma_iff (2 ^ k * m) h_pos]
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
      exact Nat.two_le_card_divisors hm0 hm1
    have h_card_pos : (m.divisors.card : ℤ) - 1 ≥ 1 := by linarith
    exact mul_pos h_m_pos h_card_pos
  have h_rest : (m.divisors \ {m}).sum (fun d => (d : ℤ) * ((d.divisors.card : ℤ) - 1)) ≥ 0 := by
    apply sum_nonneg
    intro x hx
    rw [mem_sdiff, mem_divisors] at hx
    have h_x_pos : (x : ℤ) ≥ 0 := by positivity
    have h_card : x.divisors.card ≥ 1 := by
      have hx0 : x ≠ 0 := hx.1.2
      exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (by exact divisors_nonempty hx0 |>.card_pos))
    have h_card_pos : (x.divisors.card : ℤ) - 1 ≥ 0 := by linarith
    exact mul_nonneg h_x_pos h_card_pos
  linarith

lemma two_pow_le_C_sub_S (k m : ℕ) (hm : ¬ 2 ∣ m) (hm3 : m ≥ 3) (h_eq : a (2 ^ k * m) = sigma (2 ^ k * m)) :
    (2 ^ (k + 1) : ℤ) ≤ (m.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) - sigma m) := by
  have hdvd := two_pow_dvd_C_sub_S k m hm h_eq
  have hpos := C_sub_S_pos m hm3
  have h_two_pow_pos : (2 ^ (k + 1) : ℤ) > 0 := by positivity
  exact Int.le_of_dvd hpos hdvd

lemma prime_case (k : ℕ) (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) (heq : a (2 ^ k * p) = sigma (2 ^ k * p)) : False := by
  have hm : ¬ 2 ∣ p := by
    rintro ⟨d, rfl⟩
    have hd_eq : 2 = 1 ∨ 2 = p := by
      exact (Nat.Prime.eq_one_or_self_of_dvd hp (dvd_mul_right 2 d))
    rcases hd_eq with h_one | h_self
    · contradiction
    · linarith
  have hdvd := two_pow_dvd_C_sub_S k p hm heq
  have h_C_S : p.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) - sigma p = p := by
    have hp_divs : p.divisors = {1, p} := by
      exact Nat.Prime.divisors hp
    rw [hp_divs, sigma]
    have h1 : 1 ≠ p := by linarith
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



lemma sum_divisors_lt_two_mul (m : ℕ) (hm : ¬ 2 ∣ m) (hm3 : m ≥ 3) :
    (m.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ) + (d : ℤ))) < 2 * (m : ℤ) * (m.divisors.card : ℤ) := by
  have hm_mem : m ∈ m.divisors := by
    have h_ne : m ≠ 0 := by linarith
    simp [h_ne]
  rw [sum_eq_add_sum_diff_singleton hm_mem]
  have h_card : m.divisors.card ≥ 2 := by
    have hm1 : m ≠ 1 := by linarith
    have hm0 : m ≠ 0 := by linarith
    exact Nat.two_le_card_divisors hm0 hm1
  have h_term : (m : ℤ) * (m.divisors.card : ℤ) + (m : ℤ) ≤ 2 * (m : ℤ) * (m.divisors.card : ℤ) - (m : ℤ) := by
    have h_card_pos : (m.divisors.card : ℤ) ≥ 2 := by linarith
    have h_m_pos : (m : ℤ) > 0 := by linarith
    nlinarith
  have h_rest : (m.divisors \ {m}).sum (fun d => (d : ℤ) * (d.divisors.card : ℤ) + (d : ℤ)) ≤
      (m.divisors.card - 1) * ((m : ℤ) * (m.divisors.card : ℤ)) / 3 := by
    -- we can bound each term by m * m.divisors.card / 3
    sorry
  sorry















