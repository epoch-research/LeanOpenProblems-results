import FormalConjectures.Util.ProblemImports

open Nat BigOperators

/--
A091669: $a(n) = \frac{2^{n-1}}{n!} \prod_{k=1}^{n-1} (2^k-1)$.
The sequence $a(n)$ is composed of natural numbers, thus we define it as a function $\mathbb{N} \to \mathbb{N}$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if h : n = 0 then 0 -- Sequence is defined for n >= 1.
  else
    let n_pred : ℕ := n.pred

    -- The numerator of the expression. Both factors are in ℕ.
    let numerator : ℕ := (2 ^ n_pred) * (Finset.Ico 1 n).prod (fun k => 2 ^ k - 1)

    -- The denominator is $n!$.
    let denominator : ℕ := n.factorial

    -- The division is exact, since the result is an integer sequence.
    numerator / denominator


lemma padicValNat_prod {α : Type*} (p : ℕ) [Fact p.Prime] {S : Finset α} {g : α → ℕ} (hg : ∀ x ∈ S, g x ≠ 0) :
  padicValNat p (S.prod g) = S.sum fun x => padicValNat p (g x) := by
  have hp : p.Prime := Fact.out
  have h_prod_ne : S.prod g ≠ 0 := Finset.prod_ne_zero_iff.mpr hg
  rw [← factorization_def _ hp, factorization_prod_apply hg]
  simp_rw [factorization_def _ hp]

lemma dvd_of_orderOf_dvd {p k : ℕ} [Fact p.Prime] (hk : orderOf (2 : ZMod p) ∣ k) : p ∣ 2 ^ k - 1 := by
  have h_pow_one : (2 : ZMod p) ^ k = 1 := orderOf_dvd_iff_pow_eq_one.mp hk
  have h_cast : ((2 ^ k : ℕ) : ZMod p) = (2 : ZMod p) ^ k := by push_cast; rfl
  have h_pow_one' : ((2 ^ k : ℕ) : ZMod p) = 1 := h_cast.trans h_pow_one
  have hk_pos : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
  have h_sub_zero : (((2 ^ k - 1 : ℕ) : ZMod p)) = 0 := by
    have h_eq : (2 ^ k : ℕ) = (2 ^ k - 1) + 1 := (Nat.sub_add_cancel hk_pos).symm
    have h_eq' : ((2 ^ k : ℕ) : ZMod p) = (((2 ^ k - 1 : ℕ) : ZMod p)) + 1 := by
      rw [h_eq]
      push_cast
      rfl
    rw [h_pow_one'] at h_eq'
    have h_eq'' : (((2 ^ k - 1 : ℕ) : ZMod p)) + 1 = 0 + 1 := by
      rw [zero_add]
      exact h_eq'.symm
    exact add_right_cancel h_eq''
  rwa [ZMod.natCast_eq_zero_iff] at h_sub_zero

lemma valuation_prod_ge (p m : ℕ) [Fact p.Prime] :
  ((Finset.Ico 1 m).filter (fun k => orderOf (2 : ZMod p) ∣ k)).card ≤
  padicValNat p ((Finset.Ico 1 m).prod (fun k => 2 ^ k - 1)) := by
  let S := Finset.Ico 1 m
  let g := fun k => 2 ^ k - 1
  have hg : ∀ x ∈ S, g x ≠ 0 := by
    intro x hx
    rw [Finset.mem_Ico] at hx
    have hx1 : 1 ≤ x := hx.1
    have : 2 ^ x ≥ 2 := Nat.pow_le_pow_right (n := 2) (by decide) hx1
    have h_ne : 2 ^ x - 1 ≠ 0 := by omega
    exact h_ne
  rw [padicValNat_prod p hg]
  let d := orderOf (2 : ZMod p)
  let A := S.filter (fun k => d ∣ k)
  have h_subset : A ⊆ S := Finset.filter_subset _ _
  have h_nonneg : ∀ x ∈ S, x ∉ A → 0 ≤ padicValNat p (g x) := by
    intros
    exact Nat.zero_le _
  have h_sum_le := Finset.sum_le_sum_of_subset_of_nonneg h_subset h_nonneg
  have h_one_le : ∀ x ∈ A, 1 ≤ padicValNat p (g x) := by
    intro x hx
    rw [Finset.mem_filter] at hx
    have h_dvd : p ∣ 2 ^ x - 1 := dvd_of_orderOf_dvd hx.2
    have h_ne : 2 ^ x - 1 ≠ 0 := hg x hx.1
    exact one_le_padicValNat_of_dvd h_ne h_dvd
  have h_card_le : A.card ≤ A.sum (fun x => padicValNat p (g x)) := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum h_one_le
  exact h_card_le.trans h_sum_le

lemma card_filter_dvd_le (m d : ℕ) (hd : d > 0) :
  (m - 1) / d ≤ ((Finset.Ico 1 m).filter (fun k => d ∣ k)).card := by
  let f := fun i => i * d
  have h_inj : Function.Injective f := by
    intro x y heq
    exact Nat.eq_of_mul_eq_mul_right hd heq
  have h_image_card : ((Finset.Ico 1 ((m - 1) / d + 1)).image f).card = (m - 1) / d := by
    rw [Finset.card_image_of_injective _ h_inj, card_Ico]
    exact Nat.add_sub_cancel_right _ _
  rw [← h_image_card]
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_image] at hx
  rcases hx with ⟨i, hi, rfl⟩
  rw [Finset.mem_Ico] at hi
  rw [Finset.mem_filter, Finset.mem_Ico]
  have h1 : 1 ≤ i * d := by
    have : 1 ≤ i := hi.1
    have : 1 ≤ d := hd
    exact Nat.mul_le_mul hi.1 (by omega)
  have h2 : i * d < m := by
    have : i ≤ (m - 1) / d := by omega
    have : i * d ≤ ((m - 1) / d) * d := Nat.mul_le_mul_right d this
    have h_div_mul : ((m - 1) / d) * d ≤ m - 1 := Nat.div_mul_le_self (m - 1) d
    omega
  exact ⟨⟨h1, h2⟩, dvd_mul_left d i⟩

lemma orderOf_two_pos (p : ℕ) [Fact p.Prime] (hp3 : p ≥ 3) : orderOf (2 : ZMod p) > 0 := by
  have h_not_dvd : ¬ p ∣ 2 := by
    intro hd
    have : p ≤ 2 := Nat.le_of_dvd (by decide) hd
    omega
  have hp : p.Prime := Fact.out
  have h_cop : Nat.Coprime 2 p := (hp.coprime_iff_not_dvd.mpr h_not_dvd).symm
  let u : (ZMod p)ˣ := ZMod.unitOfCoprime 2 h_cop
  have hd_pos_units : 0 < orderOf u := orderOf_pos u
  have h_coe_u : (u : ZMod p) = 2 := ZMod.coe_unitOfCoprime 2 h_cop
  have h_order_eq : orderOf (2 : ZMod p) = orderOf u := by
    rw [← h_coe_u, orderOf_units]
  rw [h_order_eq]
  exact hd_pos_units

lemma helper_div_lt {a b c : ℕ} (ha : a > 0) (h : a * b < c) : b ≤ (c - 1) / a := by
  have : a * b ≤ c - 1 := by omega
  rwa [Nat.le_div_iff_mul_le ha, mul_comm]

lemma valuation_prod_ge_div (p m : ℕ) [Fact p.Prime] (hp3 : p ≥ 3) :
  (m - 1) / (orderOf (2 : ZMod p)) ≤ padicValNat p ((Finset.Ico 1 m).prod (fun k => 2 ^ k - 1)) := by
  have hd_pos : orderOf (2 : ZMod p) > 0 := orderOf_two_pos p hp3
  exact (card_filter_dvd_le m (orderOf (2 : ZMod p)) hd_pos).trans (valuation_prod_ge p m)

lemma valuation_factorial_le_prod (p m : ℕ) [Fact p.Prime] (hp3 : p ≥ 3) (hm : m ≥ 1) :
  padicValNat p m.factorial ≤ padicValNat p ((Finset.Ico 1 m).prod (fun k => 2 ^ k - 1)) := by
  have hp : p.Prime := Fact.out
  have hp_pos : p - 1 > 0 := by omega
  have h_not_zero : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hz' : ((2 : ℕ) : ZMod p) = 0 := hz
    rw [ZMod.natCast_eq_zero_iff] at hz'
    have : p ≤ 2 := Nat.le_of_dvd (by decide) hz'
    omega
  have h_order_dvd : orderOf (2 : ZMod p) ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one h_not_zero
  have hd_pos : orderOf (2 : ZMod p) > 0 := orderOf_two_pos p hp3
  have hd_le : orderOf (2 : ZMod p) ≤ p - 1 := Nat.le_of_dvd hp_pos h_order_dvd
  have h_div_le : (m - 1) / (p - 1) ≤ (m - 1) / (orderOf (2 : ZMod p)) := by
    exact Nat.div_le_div (by rfl) hd_le (by omega)
  have h_fact_lt : (p - 1) * padicValNat p m.factorial < m := by
    exact sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (by omega)
  have h_fact_le : padicValNat p m.factorial ≤ (m - 1) / (p - 1) := by
    exact helper_div_lt hp_pos h_fact_lt
  exact h_fact_le.trans (h_div_le.trans (valuation_prod_ge_div p m hp3))

lemma valuation_two_le_prod (m : ℕ) (hm : m ≥ 1) :
  padicValNat 2 m.factorial ≤ padicValNat 2 (2 ^ (m - 1) * (Finset.Ico 1 m).prod (fun k => 2 ^ k - 1)) := by
  let P := (Finset.Ico 1 m).prod (fun k => 2 ^ k - 1)
  have hP_ne : P ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro x hx
    rw [Finset.mem_Ico] at hx
    have : 2 ^ x ≥ 2 := Nat.pow_le_pow_right (n := 2) (by decide) hx.1
    omega
  have h2_ne : (2 ^ (m - 1) : ℕ) ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by decide))
  have h_mul : padicValNat 2 (2 ^ (m - 1) * P) = padicValNat 2 (2 ^ (m - 1)) + padicValNat 2 P := by
    exact padicValNat.mul h2_ne hP_ne
  have h_pow : padicValNat 2 (2 ^ (m - 1) : ℕ) = m - 1 := by
    rw [padicValNat.pow (m - 1) (by decide), padicValNat_self]
    omega
  have h_fact_lt : (2 - 1) * padicValNat 2 m.factorial < m := by
    exact sub_one_mul_padicValNat_factorial_lt_of_ne_zero 2 (by omega)
  have h_fact_le : padicValNat 2 m.factorial ≤ m - 1 := by omega
  rw [h_mul, h_pow]
  omega

lemma valuation_le_mul_right (p A B : ℕ) [Fact p.Prime] (hA : A ≠ 0) (hB : B ≠ 0) :
  padicValNat p B ≤ padicValNat p (A * B) := by
  rw [padicValNat.mul hA hB]
  omega

theorem factorial_dvd_numerator (m : ℕ) :
  m.factorial ∣ 2 ^ (m - 1) * (Finset.Ico 1 m).prod (fun k => 2 ^ k - 1) := by
  rcases eq_or_ne m 0 with rfl | hm0
  · simp
  have hm : m ≥ 1 := by omega
  let P := (Finset.Ico 1 m).prod (fun k => 2 ^ k - 1)
  have hP_ne : P ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro x hx
    rw [Finset.mem_Ico] at hx
    have : 2 ^ x ≥ 2 := Nat.pow_le_pow_right (n := 2) (by decide) hx.1
    omega
  have h2_ne : (2 ^ (m - 1) : ℕ) ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by decide))
  have h_num_ne : 2 ^ (m - 1) * P ≠ 0 := Nat.mul_ne_zero h2_ne hP_ne
  have h_fact_ne : m.factorial ≠ 0 := Nat.factorial_ne_zero m
  change m.factorial ∣ 2 ^ (m - 1) * P
  rw [← Nat.factorization_prime_le_iff_dvd h_fact_ne h_num_ne]
  intro p hp
  rw [factorization_def _ hp, factorization_def _ hp]
  haveI : Fact p.Prime := ⟨hp⟩
  rcases eq_or_ne p 2 with rfl | hp2
  · exact valuation_two_le_prod m hm
  · have hp3 : p ≥ 3 := by
      have : p ≥ 2 := hp.two_le
      omega
    have h_le_P : padicValNat p m.factorial ≤ padicValNat p P := valuation_factorial_le_prod p m hp3 hm
    have h_P_le : padicValNat p P ≤ padicValNat p (2 ^ (m - 1) * P) := valuation_le_mul_right p (2 ^ (m - 1)) P h2_ne hP_ne
    exact h_le_P.trans h_P_le

lemma digits_sum_pos (b n : ℕ) (hb : 1 < b) (hn : n ≠ 0) : 1 ≤ (digits b n).sum := by
  induction' n using Nat.strong_induction_on with n ih
  rw [digits_eq_cons_digits_div hb hn]
  simp only [List.sum_cons]
  by_cases h : n / b = 0
  · rw [h, digits_zero, List.sum_nil, add_zero]
    have : n < b := by
      by_contra hlt
      have : n / b ≥ 1 := Nat.div_pos (Nat.le_of_not_lt hlt) (by omega)
      omega
    have : n % b = n := Nat.mod_eq_of_lt this
    omega
  · have h_lt : n / b < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) hb
    have : 1 ≤ (digits b (n / b)).sum := ih (n / b) h_lt h
    omega

lemma pb_sub_one_eq (p b : ℕ) (hp3 : p ≥ 3) (hb : b ≥ 2) : p * b - 1 = (p - 1) + p * (b - 1) := by
  have h_b : b = (b - 1) + 1 := by omega
  nth_rw 1 [h_b]
  rw [Nat.mul_add, mul_one]
  omega

lemma digits_sum_ge (p b : ℕ) [Fact p.Prime] (hp3 : p ≥ 3) (hb : b ≥ 2) :
  p ≤ (p.digits (p * b - 1)).sum := by
  have hp : p.Prime := Fact.out
  have h_pb_ge : p * b ≥ 6 := by
    have : 3 * 2 ≤ p * b := Nat.mul_le_mul hp3 hb
    omega
  have hm0 : p * b - 1 ≠ 0 := by omega
  have h_digits : (p.digits (p * b - 1)).sum = ((p * b - 1) % p) + (p.digits ((p * b - 1) / p)).sum := by
    rw [Nat.digits_def' hp.one_lt (by omega), List.sum_cons]
  rw [h_digits]
  have h_eq : p * b - 1 = (p - 1) + p * (b - 1) := pb_sub_one_eq p b hp3 hb
  have h_mod : (p * b - 1) % p = p - 1 := by
    rw [h_eq, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have h_div : (p * b - 1) / p = b - 1 := by
    rw [h_eq, Nat.add_mul_div_left _ _ hp.pos]
    have : (p - 1) / p = 0 := Nat.div_eq_of_lt (by omega)
    omega
  rw [h_mod, h_div]
  have h_b1_ne : b - 1 ≠ 0 := by omega
  have h_sum : 1 ≤ (p.digits (b - 1)).sum := digits_sum_pos p (b - 1) hp.one_lt h_b1_ne
  omega

lemma digits_two_pow_sub_one_sum (j : ℕ) :
  (Nat.digits 2 (2 ^ j - 1)).sum = j := by
  induction' j with j ih
  · simp
  · have h_2j : 2 ^ j ≥ 1 := Nat.one_le_pow j 2 (by decide)
    have h_eq : 2 ^ (j + 1) - 1 = 2 * (2 ^ j - 1) + 1 := by
      rw [pow_succ, mul_comm]
      omega
    have h_pos : 0 < 2 ^ (j + 1) - 1 := by omega
    rw [h_eq]
    rw [Nat.digits_def' (by decide) (by omega), List.sum_cons]
    have h_mod : (2 * (2 ^ j - 1) + 1) % 2 = 1 := by omega
    have h_div : (2 * (2 ^ j - 1) + 1) / 2 = 2 ^ j - 1 := by omega
    rw [h_mod, h_div, ih]
    omega

lemma eq_pow_two_of_only_prime_factor_two (n : ℕ) :
  (∀ p : ℕ, p.Prime → p ∣ n → p = 2) → ∃ j : ℕ, n = 2 ^ j := by
  induction' n using Nat.strong_induction_on with n ih
  intro h
  rcases eq_or_ne n 0 with rfl | hn0
  · have h3_prime : Nat.Prime 3 := by decide
    have h3_dvd : 3 ∣ 0 := dvd_zero 3
    have : 3 = 2 := h 3 h3_prime h3_dvd
    contradiction
  rcases eq_or_ne n 1 with rfl | hn1
  · use 0
    simp
  have ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hn1
  have hp2 : p = 2 := h p hp hpdvd
  subst hp2
  rcases hpdvd with ⟨k, rfl⟩
  have hk_lt : k < 2 * k := by omega
  have h_prime_k : ∀ q, q.Prime → q ∣ k → q = 2 := by
    intro q hq hqdvd
    have hqdvd_n : q ∣ 2 * k := dvd_mul_of_dvd_right hqdvd 2
    exact h q hq hqdvd_n
  have ⟨j, hk_pow⟩ := ih k hk_lt h_prime_k
  use j + 1
  rw [hk_pow, pow_succ, mul_comm]

lemma valuation_factorial_lt_prod_composite (p b : ℕ) [Fact p.Prime] (hp3 : p ≥ 3) (hb : b ≥ 2) :
  padicValNat p (p * b - 1).factorial < padicValNat p ((Finset.Ico 1 (p * b - 1)).prod (fun k => 2 ^ k - 1)) := by
  have hp : p.Prime := Fact.out
  have hp_pos : p - 1 > 0 := by omega
  have h_pb_ge : p * b ≥ 6 := by
    have : 3 * 2 ≤ p * b := Nat.mul_le_mul hp3 hb
    omega
  have h_pb : 2 * p ≤ p * b := by
    have : 2 ≤ b := hb
    have : 2 * p ≤ b * p := Nat.mul_le_mul_right p this
    rw [mul_comm b p] at this
    exact this
  generalize h_m : p * b - 1 = m at h_pb_ge h_pb ⊢
  have hm : m ≥ 1 := by omega
  have h_sum : p ≤ (p.digits m).sum := by
    rw [← h_m]
    exact digits_sum_ge p b hp3 hb
  have h_sub : (p - 1) * padicValNat p m.factorial = m - (p.digits m).sum := sub_one_mul_padicValNat_factorial m
  have h_le : (p - 1) * padicValNat p m.factorial ≤ m - p := by omega
  have h_div_le : padicValNat p m.factorial ≤ (m - p) / (p - 1) := by
    rwa [Nat.le_div_iff_mul_le hp_pos, mul_comm]
  have h_add : (m - 1) / (p - 1) = (m - p) / (p - 1) + 1 := by
    have : m - 1 = (m - p) + (p - 1) := by omega
    nth_rw 1 [this]
    rw [Nat.add_div_right _ hp_pos]
  have h_div_eq : (m - p) / (p - 1) = (m - 1) / (p - 1) - 1 := by
    rw [h_add]
    exact (Nat.add_sub_cancel _ _).symm
  have h_m1_ge : m - 1 ≥ 2 * (p - 1) := by omega
  have h_ge2 : (m - 1) / (p - 1) ≥ 2 := by
    change 2 ≤ (m - 1) / (p - 1)
    rw [Nat.le_div_iff_mul_le hp_pos]
    exact h_m1_ge
  have h_strict : (m - 1) / (p - 1) - 1 < (m - 1) / (p - 1) := by omega
  have h_fact_lt : padicValNat p m.factorial < (m - 1) / (p - 1) := by omega
  have h_not_zero : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hz' : ((2 : ℕ) : ZMod p) = 0 := hz
    rw [ZMod.natCast_eq_zero_iff] at hz'
    have : p ≤ 2 := Nat.le_of_dvd (by decide) hz'
    omega
  have h_order_dvd : orderOf (2 : ZMod p) ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one h_not_zero
  have hd_pos : orderOf (2 : ZMod p) > 0 := orderOf_two_pos p hp3
  have hd_le : orderOf (2 : ZMod p) ≤ p - 1 := Nat.le_of_dvd hp_pos h_order_dvd
  have h_div_le' : (m - 1) / (p - 1) ≤ (m - 1) / (orderOf (2 : ZMod p)) := by
    exact Nat.div_le_div (by rfl) hd_le (by omega)
  have h_P_ge : (m - 1) / (orderOf (2 : ZMod p)) ≤ padicValNat p ((Finset.Ico 1 m).prod (fun k => 2 ^ k - 1)) := valuation_prod_ge_div p m hp3
  exact lt_of_lt_of_le h_fact_lt (h_div_le'.trans h_P_ge)

lemma j_le_two_pow_sub_two (j : ℕ) (hj : j ≥ 2) : j ≤ 2 ^ j - 2 := by
  induction' j with j ih
  · omega
  · by_cases hj2 : j = 1
    · subst hj2
      decide
    · have : j ≥ 2 := by omega
      have ih' := ih this
      have : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
      have h_pow_ge : 2 ^ j ≥ j + 2 := by omega
      omega


theorem prime_of_dvd (n : ℕ) (hn : n > 2) (hdvd : n ∣ a (n - 1) + 2 ^ (n - 2)) : Nat.Prime n := by
  by_contra hc
  have hn_ne : n ≠ 0 := by omega
  have h_cases : (∃ q, q.Prime ∧ q ≥ 3 ∧ q ∣ n) ∨ (∃ j, j ≥ 2 ∧ n = 2 ^ j) := by
    by_cases h_odd : ∃ p, p.Prime ∧ p ≥ 3 ∧ p ∣ n
    · left; exact h_odd
    · right
      have h_only : ∀ p : ℕ, p.Prime → p ∣ n → p = 2 := by
        intro p hp h_pdvd
        by_contra hp2
        have : p ≥ 3 := by
          have : p ≥ 2 := hp.two_le
          omega
        exact h_odd ⟨p, hp, this, h_pdvd⟩
      have ⟨j, h_eq⟩ := eq_pow_two_of_only_prime_factor_two n h_only
      use j
      refine ⟨?_, h_eq⟩
      by_contra hj
      have : j ≤ 1 := by omega
      interval_cases j
      · rw [h_eq] at hn
        omega
      · rw [h_eq] at hn
        omega
  rcases h_cases with ⟨q, hq, hq3, hqdvd⟩ | ⟨j, hj, rfl⟩
  · -- Case 1: Odd prime factor q of n
    haveI : Fact q.Prime := ⟨hq⟩
    have hq_lt : q < n := by
      by_contra h_ge
      have : q ≤ n := Nat.le_of_dvd (by omega) hqdvd
      have : q = n := by omega
      subst this
      exact hc hq
    have hq_le : q ≤ n - 1 := Nat.le_sub_one_of_lt hq_lt
    have hqdvd_fact : q ∣ (n - 1).factorial := (Nat.Prime.dvd_factorial hq).mpr hq_le
    have hq_ne_zero : q ≠ 0 := hq.ne_zero
    rcases hqdvd with ⟨b, hb_eq⟩
    have hb : b ≥ 2 := by
      by_contra hb_lt
      have : b ≤ 1 := by omega
      interval_cases b
      · rw [hb_eq] at hn
        rw [mul_zero] at hn
        omega
      · rw [mul_one] at hb_eq
        subst hb_eq
        exact hc hq
    have hm : n - 1 = q * b - 1 := by rw [hb_eq]
    let P := (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)
    have h_lt : padicValNat q (n - 1).factorial < padicValNat q P := by
      change padicValNat q (n - 1).factorial < padicValNat q ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1))
      rw [hm]
      exact valuation_factorial_lt_prod_composite q b hq3 hb
    have hP_ne : P ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro x hx
      rw [Finset.mem_Ico] at hx
      have : 2 ^ x ≥ 2 := Nat.pow_le_pow_right (n := 2) (by decide) hx.1
      omega
    have h_pow_ne : (2 ^ (n - 2) : ℕ) ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by decide))
    have h_exact : (n - 1).factorial ∣ 2 ^ (n - 2) * P := factorial_dvd_numerator (n - 1)
    have ha_eq : a (n - 1) = (2 ^ (n - 2) * P) / (n - 1).factorial := by
      unfold a
      split_ifs with h0
      · omega
      · have : (n - 1).pred = n - 2 := by rw [Nat.pred_eq_sub_one]; omega
        rw [this]
    have ha_mul : 2 ^ (n - 2) * P = a (n - 1) * (n - 1).factorial := by
      rw [ha_eq]
      exact (Nat.div_mul_cancel h_exact).symm
    have h_not_dvd : ¬ q ∣ 2 := by
      intro hd
      have : q ≤ 2 := Nat.le_of_dvd (by decide) hd
      omega
    have h_pow_val : padicValNat q (2 ^ (n - 2)) = 0 := by
      rw [padicValNat.pow (n - 2) (by decide), padicValNat.eq_zero_of_not_dvd h_not_dvd]
      simp
    have h_mul_val : padicValNat q (2 ^ (n - 2) * P) = padicValNat q P := by
      rw [padicValNat.mul h_pow_ne hP_ne, h_pow_val, zero_add]
    have ha_ne : a (n - 1) ≠ 0 := by
      rw [ha_eq]
      intro h_zero
      have : 2 ^ (n - 2) * P = 0 := by
        rw [← Nat.div_mul_cancel h_exact, h_zero, zero_mul]
      exact Nat.mul_ne_zero h_pow_ne hP_ne this
    have h_fact_ne : (n - 1).factorial ≠ 0 := Nat.factorial_ne_zero _
    have h_val_eq : padicValNat q (2 ^ (n - 2) * P) = padicValNat q (a (n - 1)) + padicValNat q (n - 1).factorial := by
      rw [ha_mul, padicValNat.mul ha_ne h_fact_ne]
    rw [h_mul_val] at h_val_eq
    have h_one_le : 1 ≤ padicValNat q (a (n - 1)) := by omega
    have hq_dvd_a : q ∣ a (n - 1) := dvd_of_one_le_padicValNat h_one_le
    have hqdvd_new : q ∣ n := ⟨b, hb_eq⟩
    have hqdvd_sum : q ∣ a (n - 1) + 2 ^ (n - 2) := dvd_trans hqdvd_new hdvd
    have hq_dvd_pow : q ∣ 2 ^ (n - 2) := (Nat.dvd_add_right hq_dvd_a).mp hqdvd_sum
    have hq_dvd_2 : q ∣ 2 := hq.dvd_of_dvd_pow hq_dvd_pow
    have : q ≤ 2 := Nat.le_of_dvd (by decide) hq_dvd_2
    omega
  · -- Case 2: n = 2 ^ j
    have hn_sub : 2 ^ j - 1 ≥ 1 := by omega
    let P := (Finset.Ico 1 (2 ^ j - 1)).prod (fun k => 2 ^ k - 1)
    have hP_ne : P ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro x hx
      rw [Finset.mem_Ico] at hx
      have : 2 ^ x ≥ 2 := Nat.pow_le_pow_right (n := 2) (by decide) hx.1
      omega
    have h_pow_ne : (2 ^ (2 ^ j - 2) : ℕ) ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by decide))
    have h_exact : (2 ^ j - 1).factorial ∣ 2 ^ (2 ^ j - 2) * P := factorial_dvd_numerator (2 ^ j - 1)
    have ha_eq : a (2 ^ j - 1) = (2 ^ (2 ^ j - 2) * P) / (2 ^ j - 1).factorial := by
      unfold a
      split_ifs with h0
      · omega
      · have : (2 ^ j - 1).pred = 2 ^ j - 2 := by rw [Nat.pred_eq_sub_one]; omega
        rw [this]
    have ha_mul : 2 ^ (2 ^ j - 2) * P = a (2 ^ j - 1) * (2 ^ j - 1).factorial := by
      rw [ha_eq]
      exact (Nat.div_mul_cancel h_exact).symm
    have h_not_zero_elem : ∀ x ∈ Finset.Ico 1 (2 ^ j - 1), 2 ^ x - 1 ≠ 0 := by
      intro x hx
      rw [Finset.mem_Ico] at hx
      have : 2 ^ x ≥ 2 := Nat.pow_le_pow_right (n := 2) (by decide) hx.1
      omega
    have hP_val : padicValNat 2 P = 0 := by
      rw [padicValNat_prod 2 h_not_zero_elem]
      have h_zero : ∀ x ∈ Finset.Ico 1 (2 ^ j - 1), padicValNat 2 (2 ^ x - 1) = 0 := by
        intro x hx
        rw [Finset.mem_Ico] at hx
        have h_x_ge1 : 1 ≤ x := hx.1
        have : ¬ 2 ∣ 2 ^ x - 1 := by
          intro h_dvd
          have h_div_pow : 2 ∣ 2 ^ x := dvd_pow_self 2 (by omega)
          have h_pow_ge2 : 2 ^ x ≥ 2 := Nat.pow_le_pow_right (n := 2) (by decide) h_x_ge1
          have h_eq : 2 ^ x = (2 ^ x - 1) + 1 := by omega
          have h_div_pow' : 2 ∣ (2 ^ x - 1) + 1 := by rwa [← h_eq]
          have : 2 ∣ 1 := (Nat.dvd_add_right h_dvd).mp h_div_pow'
          omega
        exact padicValNat.eq_zero_of_not_dvd this
      have h_sum_zero : ∑ x ∈ Finset.Ico 1 (2 ^ j - 1), padicValNat 2 (2 ^ x - 1) = 0 := by
        rw [Finset.sum_eq_zero h_zero]
      exact h_sum_zero
    have h_mul_val : padicValNat 2 (2 ^ (2 ^ j - 2) * P) = 2 ^ j - 2 := by
      rw [padicValNat.mul h_pow_ne hP_ne, padicValNat.pow (2 ^ j - 2) (by decide), padicValNat_self]
      omega
    have ha_ne : a (2 ^ j - 1) ≠ 0 := by
      rw [ha_eq]
      intro h_zero
      have : 2 ^ (2 ^ j - 2) * P = 0 := by
        rw [← Nat.div_mul_cancel h_exact, h_zero, zero_mul]
      exact Nat.mul_ne_zero h_pow_ne hP_ne this
    have h_fact_ne : (2 ^ j - 1).factorial ≠ 0 := Nat.factorial_ne_zero _
    have h_val_eq : padicValNat 2 (a (2 ^ j - 1)) + padicValNat 2 (2 ^ j - 1).factorial = 2 ^ j - 2 := by
      rw [← padicValNat.mul ha_ne h_fact_ne, ← ha_mul, h_mul_val]
    have h_fact_val : padicValNat 2 (2 ^ j - 1).factorial = 2 ^ j - 1 - j := by
      have h_sub_digits : (2 - 1) * padicValNat 2 (2 ^ j - 1).factorial = 2 ^ j - 1 - (Nat.digits 2 (2 ^ j - 1)).sum := sub_one_mul_padicValNat_factorial (2 ^ j - 1)
      simp only [Nat.reduceSub] at h_sub_digits
      rw [one_mul] at h_sub_digits
      rw [h_sub_digits, digits_two_pow_sub_one_sum]
    rw [h_fact_val] at h_val_eq
    have h_pow_ge : j ≤ 2 ^ j - 2 := j_le_two_pow_sub_two j hj
    have h_val_a : padicValNat 2 (a (2 ^ j - 1)) = j - 1 := by omega
    have hdvd_pow : 2 ^ j ∣ 2 ^ (2 ^ j - 2) := by
      apply pow_dvd_pow
      exact j_le_two_pow_sub_two j hj
    have h_val_lt : padicValNat 2 (a (2 ^ j - 1)) < j := by omega
    have h_not_dvd : ¬ 2 ^ j ∣ a (2 ^ j - 1) := by
      rw [padicValNat_dvd_iff_le ha_ne]
      omega
    have hdvd_sum : 2 ^ j ∣ a (2 ^ j - 1) + 2 ^ (2 ^ j - 2) := hdvd
    have : 2 ^ j ∣ a (2 ^ j - 1) := (Nat.dvd_add_iff_left hdvd_pow).mpr hdvd_sum
    contradiction



-- The formalization of the conjecture C A091669 from Jan 19 2020.
/--
Conjecture A091669: (for $n > 2$), if $n \mid a(n-1) + 2^{n-2}$, then $n$ is a prime
for which 2 is a primitive root modulo $n$ (A001122).
Note: We use `ZMod n` for the modulo ring and assume `totient` is available through `Mathlib`.
-/
theorem a091669_conjecture_primitive_root (n : ℕ) (hn : n > 2) :
  n ∣ (a (n - 1) + 2 ^ (n - 2)) →
  Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n) := by
  intro hdvd
  have hp : Nat.Prime n := prime_of_dvd n hn hdvd
  constructor
  · exact hp
  · have h_totient : Nat.totient n = n - 1 := Nat.totient_prime hp
    rw [IsPrimitiveRoot.iff_orderOf, h_totient]
    haveI : Fact n.Prime := ⟨hp⟩
    have h2_ne_zero : (2 : ZMod n) ≠ 0 := by
      intro h_zero
      have h_zero' : ((2 : ℕ) : ZMod n) = 0 := h_zero
      rw [ZMod.natCast_eq_zero_iff] at h_zero'
      have : n ≤ 2 := Nat.le_of_dvd (by decide) h_zero'
      omega
    have h_order_dvd : orderOf (2 : ZMod n) ∣ n - 1 := ZMod.orderOf_dvd_card_sub_one h2_ne_zero
    by_contra h_ne
    have h_not_dvd : ¬ n ∣ 2 := by
      intro h_dvd
      have : n ≤ 2 := Nat.le_of_dvd (by decide) h_dvd
      omega
    have h_cop : Nat.Coprime 2 n := (hp.coprime_iff_not_dvd.mpr h_not_dvd).symm
    let u : (ZMod n)ˣ := ZMod.unitOfCoprime 2 h_cop
    have hd_pos_units : 0 < orderOf u := orderOf_pos u
    have h_coe_u : (u : ZMod n) = 2 := ZMod.coe_unitOfCoprime 2 h_cop
    have h_order_eq : orderOf (2 : ZMod n) = orderOf u := by
      rw [← h_coe_u, orderOf_units]
    have hd_pos : 0 < orderOf (2 : ZMod n) := by
      rw [h_order_eq]
      exact hd_pos_units
    have hd_lt : orderOf (2 : ZMod n) < n - 1 := lt_of_le_of_ne (Nat.le_of_dvd (by omega) h_order_dvd) h_ne
    have h_mem : orderOf (2 : ZMod n) ∈ Finset.Ico 1 (n - 1) := by
      rw [Finset.mem_Ico]
      exact ⟨hd_pos, hd_lt⟩
    let d := orderOf (2 : ZMod n)
    have h_pow_one : (2 : ZMod n) ^ d = 1 := pow_orderOf_eq_one (2 : ZMod n)
    have h_cast : ((2 ^ d : ℕ) : ZMod n) = (2 : ZMod n) ^ d := by push_cast; rfl
    have h_pow_one' : ((2 ^ d : ℕ) : ZMod n) = 1 := h_cast.trans h_pow_one
    have hd_ge_one : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by omega)
    have h_sub_zero : (((2 ^ d - 1 : ℕ) : ZMod n)) = 0 := by
      have h_eq : (2 ^ d : ℕ) = (2 ^ d - 1) + 1 := (Nat.sub_add_cancel hd_ge_one).symm
      have h_eq' : ((2 ^ d : ℕ) : ZMod n) = (((2 ^ d - 1 : ℕ) : ZMod n)) + 1 := by
        rw [h_eq]
        push_cast
        rfl
      rw [h_pow_one'] at h_eq'
      have h_eq'' : (((2 ^ d - 1 : ℕ) : ZMod n)) + 1 = 0 + 1 := by
        rw [zero_add]
        exact h_eq'.symm
      exact add_right_cancel h_eq''
    have h_div_sub : n ∣ 2 ^ d - 1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      exact h_sub_zero
    have h_dvd_prod : (2 ^ d - 1) ∣ (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := Finset.dvd_prod_of_mem _ h_mem
    have h_n_dvd_prod : n ∣ (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := dvd_trans h_div_sub h_dvd_prod
    have h_n_dvd_num : n ∣ ((2 ^ (n - 2)) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) := dvd_mul_of_dvd_right h_n_dvd_prod _
    have h_not_dvd_fact : ¬ n ∣ (n - 1).factorial := by
      intro h_dvd
      have h_le : n ≤ n - 1 := (hp.dvd_factorial).mp h_dvd
      omega
    have h_exact : (n - 1).factorial ∣ ((2 ^ (n - 2)) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) := factorial_dvd_numerator (n - 1)
    have ha_eq : a (n - 1) = ((2 ^ (n - 1).pred) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) / (n - 1).factorial := by
      unfold a
      split_ifs with h0
      · omega
      · rfl
    have h_pred : (n - 1).pred = n - 2 := by
      have : n - 1 = (n - 2) + 1 := by omega
      rw [this]
      rfl
    have ha_eq' : a (n - 1) = ((2 ^ (n - 2)) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) / (n - 1).factorial := by
      rw [← h_pred]
      exact ha_eq
    have h_exact_eq : ((2 ^ (n - 2)) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) = a (n - 1) * (n - 1).factorial := by
      rw [ha_eq']
      exact (Nat.div_mul_cancel h_exact).symm
    have h_n_dvd_mul : n ∣ a (n - 1) * (n - 1).factorial := by
      rw [← h_exact_eq]
      exact h_n_dvd_num
    have h_dvd_a : n ∣ a (n - 1) := by
      rcases hp.dvd_mul.mp h_n_dvd_mul with h1 | h2
      · exact h1
      · contradiction
    have h_dvd_pow2 : n ∣ 2 ^ (n - 2) := (@Nat.dvd_add_iff_right n (a (n - 1)) (2 ^ (n - 2)) h_dvd_a).mpr hdvd
    have h_dvd_2 : n ∣ 2 := hp.dvd_of_dvd_pow h_dvd_pow2
    have : n ≤ 2 := Nat.le_of_dvd (by decide) h_dvd_2
    omega


