import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A265710: $a(n) = \mathrm{denominator}\left(\sum_{d|n} \frac{1}{\sigma(d)}\right)$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  Rat.den <| (Nat.divisors n).sum fun d => (1 : Rat) / (ArithmeticFunction.sigma 1 d : Rat)

noncomputable def S (n : ℕ) : ℚ :=
  (Nat.divisors n).sum fun d => (1 : ℚ) / (ArithmeticFunction.sigma 1 d : ℚ)

lemma sum_geom_two (x : ℕ) : (∑ j ∈ range (x + 1), (2 : ℚ) ^ j) = (2 : ℚ) ^ (x + 1) - 1 := by
  induction x with
  | zero => norm_num
  | succ x ih =>
    rw [sum_range_succ, ih]
    ring

lemma sigma_one_two_pow (x : ℕ) : (ArithmeticFunction.sigma 1 (2 ^ x) : ℚ) = (2 : ℚ) ^ (x + 1) - 1 := by
  rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_prime_pow Nat.prime_two]
  push_cast
  exact sum_geom_two x

lemma S_two_pow (k : ℕ) : S (2 ^ k) = ∑ x ∈ range (k + 1), (1 : ℚ) / ((2 : ℚ) ^ (x + 1) - 1) := by
  unfold S
  rw [Nat.sum_divisors_prime_pow Nat.prime_two]
  simp_rw [sigma_one_two_pow]

lemma S_two_pow_le (k : ℕ) : S (2 ^ k) ≤ 2 - (1 / (2 : ℚ) ^ k) := by
  induction k with
  | zero =>
    rw [S_two_pow]
    norm_num
  | succ m ih =>
    rw [S_two_pow] at ih ⊢
    rw [sum_range_succ]
    have h_add : (∑ x ∈ range (m + 1), (1 : ℚ) / ((2 : ℚ) ^ (x + 1) - 1)) + (1 : ℚ) / ((2 : ℚ) ^ (m + 2) - 1) ≤ 2 - 1 / (2 : ℚ) ^ m + 1 / ((2 : ℚ) ^ (m + 2) - 1) := by
      linarith
    apply h_add.trans
    have h_pow : (2 : ℚ) ^ (m + 1) = 2 * (2 : ℚ) ^ m := by ring
    have h_pow2 : (2 : ℚ) ^ (m + 2) = 4 * (2 : ℚ) ^ m := by ring
    have h_pos : 0 < (2 : ℚ) ^ m := by positivity
    have h_ge : 1 ≤ (2 : ℚ) ^ m := one_le_pow₀ (by norm_num)
    have h_sub : (2 : ℚ) ^ (m + 2) - 1 ≥ (2 : ℚ) ^ (m + 1) := by
      rw [h_pow, h_pow2]
      linarith
    have h_div : 1 / ((2 : ℚ) ^ (m + 2) - 1) ≤ 1 / (2 : ℚ) ^ (m + 1) := by
      apply one_div_le_one_div_of_le
      · positivity
      · exact h_sub
    have h_alg : 2 - 1 / (2 : ℚ) ^ m + 1 / (2 : ℚ) ^ (m + 1) = 2 - 1 / (2 : ℚ) ^ (m + 1) := by
      rw [h_pow]
      ring
    linarith

lemma S_two_pow_gt_one (k : ℕ) (hk : k ≥ 1) : 1 < S (2 ^ k) := by
  rw [S_two_pow]
  have h_subset : range 2 ⊆ range (k + 1) := by
    rw [range_subset_range]
    linarith
  have h_nonneg : ∀ x ∈ range (k + 1), 0 ≤ (1 : ℚ) / ((2 : ℚ) ^ (x + 1) - 1) := by
    intro x _
    have h_ge : 1 ≤ (2 : ℚ) ^ x := one_le_pow₀ (by norm_num)
    have h_sub : (2 : ℚ) ^ (x + 1) - 1 > 0 := by
      have : (2 : ℚ) ^ (x + 1) = 2 * (2 : ℚ) ^ x := by ring
      rw [this]
      linarith
    positivity
  have h_sum := sum_le_sum_of_subset_of_nonneg h_subset (fun x hx _ => h_nonneg x hx)
  have h_base : (∑ x ∈ range 2, (1 : ℚ) / ((2 : ℚ) ^ (x + 1) - 1)) = 4 / 3 := by
    rw [sum_range_succ, sum_range_succ, sum_range_zero]
    norm_num
  linarith

lemma not_integer_of_strict_between_one_two (q : ℚ) (h1 : 1 < q) (h2 : q < 2) (z : ℤ) : q ≠ z := by
  rintro rfl
  have h_lt : 1 < z := by exact_mod_cast h1
  have h_gt : z < 2 := by exact_mod_cast h2
  omega

lemma S_two_pow_den_ne_one (k : ℕ) (hk : k ≥ 1) : (S (2 ^ k)).den ≠ 1 := by
  intro h
  have h_eq : S (2 ^ k) = ((S (2 ^ k)).num : ℚ) := by
    exact ((Rat.den_eq_one_iff (S (2 ^ k))).mp h).symm
  have h_lt_2 : S (2 ^ k) < 2 := by
    have h_le := S_two_pow_le k
    have h_pow_pos : 0 < 1 / (2 : ℚ) ^ k := by positivity
    linarith
  have h_gt_1 : 1 < S (2 ^ k) := S_two_pow_gt_one k hk
  exact not_integer_of_strict_between_one_two (S (2 ^ k)) h_gt_1 h_lt_2 (S (2 ^ k)).num h_eq

theorem eq_pow_two_of_no_odd_prime_factor (n : ℕ) : n ≥ 1 → (∀ p : ℕ, p.Prime → p ∣ n → p = 2) → ∃ k : ℕ, n = 2 ^ k := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn h_no_odd
    by_cases hn1 : n = 1
    · use 0
      rw [hn1]
      rfl
    · have hn_gt : n > 1 := by omega
      have ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hn_gt.ne'
      have hp_eq : p = 2 := h_no_odd p hp_prime hp_dvd
      subst hp_eq
      rcases hp_dvd with ⟨m, rfl⟩
      have hm : m < 2 * m := by omega
      have hm1 : m ≥ 1 := by omega
      have ih_m := ih m hm hm1
      have h_no_odd_m : ∀ p : ℕ, p.Prime → p ∣ m → p = 2 := by
        intro p hp hp_dvd_m
        have hp_dvd_n : p ∣ 2 * m := dvd_mul_of_dvd_right hp_dvd_m 2
        exact h_no_odd p hp hp_dvd_n
      have ⟨k, hk_eq⟩ := ih_m h_no_odd_m
      use k + 1
      rw [hk_eq]
      ring

noncomputable def F : ArithmeticFunction ℚ :=
  ⟨fun n => if n = 0 then 0 else (1 : ℚ) / (ArithmeticFunction.sigma 1 n : ℚ), rfl⟩

lemma F_apply {n : ℕ} (hn : n ≠ 0) : F n = (1 : ℚ) / (ArithmeticFunction.sigma 1 n : ℚ) := by
  dsimp [F]
  rw [if_neg hn]

lemma F_one : F 1 = 1 := by
  rw [F_apply (by norm_num)]
  rw [ArithmeticFunction.sigma_one_apply]
  simp

lemma isMultiplicative_F : F.IsMultiplicative := by
  constructor
  · exact F_one
  · intro x y h_cop
    by_cases hx : x = 0
    · subst hx; simp [F]
    · by_cases hy : y = 0
      · subst hy; simp [F]
      · have hxy : x * y ≠ 0 := by
          intro h_zero
          cases Nat.mul_eq_zero.mp h_zero <;> contradiction
        rw [F_apply hx, F_apply hy, F_apply hxy]
        have h_sig : (ArithmeticFunction.sigma 1 (x * y) : ℚ) = ArithmeticFunction.sigma 1 x * ArithmeticFunction.sigma 1 y := by
          have h_sig_nat : ArithmeticFunction.sigma 1 (x * y) = ArithmeticFunction.sigma 1 x * ArithmeticFunction.sigma 1 y := by
            have := ArithmeticFunction.isMultiplicative_sigma (k := 1)
            exact this.2 h_cop
          exact_mod_cast h_sig_nat
        rw [h_sig]
        ring

lemma S_eq_F_mul_zeta {n : ℕ} (hn : n ≠ 0) : S n = (F * ArithmeticFunction.zeta) n := by
  unfold S
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  apply sum_congr rfl
  intro d hd
  have hd_ne : d ≠ 0 := by
    have := Nat.pos_of_mem_divisors hd
    omega
  exact (F_apply hd_ne).symm

lemma S_mul_of_coprime {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) (h_cop : x.Coprime y) :
    S (x * y) = S x * S y := by
  have hxy : x * y ≠ 0 := by
    intro h_zero
    cases Nat.mul_eq_zero.mp h_zero <;> contradiction
  rw [S_eq_F_mul_zeta hx, S_eq_F_mul_zeta hy, S_eq_F_mul_zeta hxy]
  have h_mult : (F * ↑ArithmeticFunction.zeta).IsMultiplicative := by
    apply ArithmeticFunction.IsMultiplicative.mul
    · exact isMultiplicative_F
    · exact ArithmeticFunction.isMultiplicative_zeta.natCast
  exact h_mult.2 h_cop



lemma odd_mul_odd {a b : ℕ} (ha : Odd a) (hb : Odd b) : Odd (a * b) := by
  exact Odd.mul ha hb

lemma odd_of_dvd_odd {a b : ℕ} (ha : Odd a) (hab : b ∣ a) : Odd b := by
  rcases hab with ⟨c, rfl⟩
  by_contra h_even
  have h_even_b : Even (b * c) := Even.mul_right (Nat.not_odd_iff_even.mp h_even) c
  have h_odd_b : Odd (b * c) := ha
  exact (Nat.not_odd_iff_even.mpr h_even_b) h_odd_b

lemma Rat.den_add_odd (q1 q2 : ℚ) (h1 : Odd q1.den) (h2 : Odd q2.den) : Odd (q1 + q2).den := by
  have h_mul : Odd (q1.den * q2.den) := Odd.mul h1 h2
  exact odd_of_dvd_odd h_mul (Rat.add_den_dvd q1 q2)

lemma Rat.den_mul_odd (q1 q2 : ℚ) (h1 : Odd q1.den) (h2 : Odd q2.den) : Odd (q1 * q2).den := by
  have h_mul : Odd (q1.den * q2.den) := Odd.mul h1 h2
  exact odd_of_dvd_odd h_mul (Rat.mul_den_dvd q1 q2)

lemma Rat.den_sum_odd {α : Type _} [DecidableEq α] (s : Finset α) (f : α → ℚ) (h : ∀ x ∈ s, Odd (f x).den) : Odd (s.sum f).den := by
  induction s using Finset.induction with
  | empty =>
    simp
  | insert a s ha ih =>
    rw [sum_insert ha]
    apply Rat.den_add_odd
    · exact h a (mem_insert_self a s)
    · apply ih
      intro x hx
      exact h x (mem_insert_of_mem hx)

lemma den_one_div_natCast (x : ℕ) (hx : x ≠ 0) : ((1 : ℚ) / (x : ℚ)).den = x := by
  have : (1 : ℚ) / (x : ℚ) = (x : ℚ)⁻¹ := by rw [one_div]
  rw [this, Rat.inv_natCast_den, if_neg hx]

lemma cast_sub_one (x : ℕ) : ((2 ^ (x + 1) - 1 : ℕ) : ℚ) = (2 : ℚ) ^ (x + 1) - 1 := by
  have h_le : 1 ≤ 2 ^ (x + 1) := by
    have : 2 ^ (x + 1) ≥ 2 ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have h_sub : ((2 ^ (x + 1) - 1 : ℕ) : ℚ) = ((2 ^ (x + 1) : ℕ) : ℚ) - 1 := Nat.cast_sub h_le
  push_cast at h_sub ⊢
  exact h_sub

lemma sigma_one_two_pow_nat (x : ℕ) : ArithmeticFunction.sigma 1 (2 ^ x) = 2 ^ (x + 1) - 1 := by
  have h_eq : ((ArithmeticFunction.sigma 1 (2 ^ x) : ℚ)) = (((2 ^ (x + 1) - 1 : ℕ) : ℚ)) := by
    rw [cast_sub_one]
    rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_prime_pow Nat.prime_two]
    push_cast
    have h_geom : (∑ j ∈ range (x + 1), (2 : ℚ) ^ j) = (2 : ℚ) ^ (x + 1) - 1 := by
      induction x with
      | zero => norm_num
      | succ x ih =>
        rw [sum_range_succ, ih]
        ring
    exact h_geom
  exact_mod_cast h_eq

lemma odd_two_pow_sub_one (i : ℕ) : Odd (2 ^ (i + 1) - 1) := by
  have h_pow : 2 ^ (i + 1) = 2 * 2 ^ i := by
    rw [pow_succ, mul_comm]
  have h_ge : 1 ≤ 2 ^ i := Nat.one_le_pow i 2 (by decide)
  use 2 ^ i - 1
  omega

lemma sigma_one_two_pow_odd (k : ℕ) (d : ℕ) (hd : d ∈ Nat.divisors (2^k)) : Odd (ArithmeticFunction.sigma 1 d) := by
  rw [Nat.mem_divisors] at hd
  have h_dvd := hd.1
  rw [Nat.dvd_prime_pow Nat.prime_two] at h_dvd
  rcases h_dvd with ⟨i, hi_le, rfl⟩
  rw [sigma_one_two_pow_nat]
  exact odd_two_pow_sub_one i

lemma S_two_pow_den_odd (k : ℕ) : Odd (S (2 ^ k)).den := by
  unfold S
  apply Rat.den_sum_odd
  intro d hd
  have h_odd := sigma_one_two_pow_odd k d hd
  have h_ne : ArithmeticFunction.sigma 1 d ≠ 0 := by
    rcases h_odd with ⟨m, hm⟩
    omega
  rw [den_one_div_natCast _ h_ne]
  exact h_odd

lemma exists_eq_pow_mul_and_not_dvd {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) (hpn : p ∣ n) :
    ∃ (e : ℕ) (K : ℕ), e ≥ 1 ∧ ¬ p ∣ K ∧ n = p ^ e * K := by
  haveI : Fact p.Prime := ⟨hp⟩
  let e := padicValNat p n
  have he_ne_zero : e ≠ 0 := (dvd_iff_padicValNat_ne_zero hn).mp hpn
  have he_ge_1 : e ≥ 1 := Nat.one_le_iff_ne_zero.mpr he_ne_zero
  let K := n / p ^ e
  have h_dvd_pe : p ^ e ∣ n := pow_padicValNat_dvd
  have h_eq : n = p ^ e * K := (Nat.mul_div_cancel' h_dvd_pe).symm
  use e, K
  refine ⟨he_ge_1, ?_, h_eq⟩
  intro hp_dvd_K
  rcases hp_dvd_K with ⟨L, hK⟩
  have h_dvd_pe_succ : p ^ (e + 1) ∣ n := by
    rw [h_eq, hK]
    use L
    rw [pow_succ]
    ring
  have h_not_dvd_pe_succ := pow_succ_padicValNat_not_dvd (p := p) hn
  exact h_not_dvd_pe_succ h_dvd_pe_succ

lemma coprime_of_even_den {q : ℚ} (h : Even q.den) : Odd q.num := by
  have h_cop : Nat.Coprime q.num.natAbs q.den := q.reduced
  by_contra h_even
  have h_even_num : Even q.num := Int.not_odd_iff_even.mp h_even
  have h_even_abs : 2 ∣ q.num.natAbs := by
    rw [even_iff_two_dvd] at h_even_num
    have h_dvd := Int.natAbs_dvd_natAbs.mpr h_even_num
    exact h_dvd
  have h_even_den : 2 ∣ q.den := even_iff_two_dvd.mp h
  have h_gcd : 2 ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd h_even_abs h_even_den
  rw [Nat.Coprime.gcd_eq_one h_cop] at h_gcd
  norm_num at h_gcd

lemma den_mul_even (x y : ℚ) (hx : Even x.den) (hy : Even y.den) : Even (x * y).den := by
  by_contra h_odd
  have h_odd' : Odd (x * y).den := Nat.not_even_iff_odd.mp h_odd
  have hx_num : Odd x.num := coprime_of_even_den hx
  have hy_num : Odd y.num := coprime_of_even_den hy
  let z := x * y
  have h_eq : (z.num : ℚ) / (z.den : ℚ) = ((x.num : ℚ) / (x.den : ℚ)) * ((y.num : ℚ) / (y.den : ℚ)) := by
    rw [Rat.num_div_den x, Rat.num_div_den y, Rat.num_div_den z]
  have h_eq2 : (z.num : ℚ) / (z.den : ℚ) = ((x.num * y.num : ℤ) : ℚ) / ((x.den * y.den : ℕ) : ℚ) := by
    rw [h_eq]
    push_cast
    ring
  have h_den_nz1 : (z.den : ℚ) ≠ 0 := by positivity
  have h_den_nz2 : ((x.den * y.den : ℕ) : ℚ) ≠ 0 := by positivity
  have h_clear : (z.num : ℚ) * ((x.den * y.den : ℕ) : ℚ) = ((x.num * y.num : ℤ) : ℚ) * (z.den : ℚ) := by
    have h_eq_mul : ((z.num : ℚ) / (z.den : ℚ)) * ((z.den : ℚ) * ((x.den * y.den : ℕ) : ℚ)) = (((x.num * y.num : ℤ) : ℚ) / ((x.den * y.den : ℕ) : ℚ)) * ((z.den : ℚ) * ((x.den * y.den : ℕ) : ℚ)) := by
      rw [h_eq2]
    have h_lhs : ((z.num : ℚ) / (z.den : ℚ)) * ((z.den : ℚ) * ((x.den * y.den : ℕ) : ℚ)) = (z.num : ℚ) * ((x.den * y.den : ℕ) : ℚ) := by
      rw [← mul_assoc, div_mul_cancel₀ _ h_den_nz1]
    have h_rhs : (((x.num * y.num : ℤ) : ℚ) / ((x.den * y.den : ℕ) : ℚ)) * ((z.den : ℚ) * ((x.den * y.den : ℕ) : ℚ)) = ((x.num * y.num : ℤ) : ℚ) * (z.den : ℚ) := by
      rw [mul_comm (z.den : ℚ), ← mul_assoc, div_mul_cancel₀ _ h_den_nz2]
    rwa [h_lhs, h_rhs] at h_eq_mul
  have h_clear_int : z.num * (x.den * y.den : ℤ) = x.num * y.num * z.den := by
    exact_mod_cast h_clear
  have h_even_den : Even (x.den * y.den : ℤ) := by
    have hx_int : Even (x.den : ℤ) := by exact_mod_cast hx
    rcases hx_int with ⟨k, hk⟩
    use k * y.den
    rw [hk]
    ring
  have h_even_lhs : Even (z.num * (x.den * y.den : ℤ)) := by
    rcases h_even_den with ⟨m, hm⟩
    use z.num * m
    rw [hm]
    ring
  have h_even_rhs : Even (x.num * y.num * z.den) := by
    rw [← h_clear_int]
    exact h_even_lhs
  have h_odd_z : Odd z.den := h_odd'
  have h_odd_z_int : Odd (z.den : ℤ) := by exact_mod_cast h_odd_z
  have h_odd_rhs : Odd (x.num * y.num * (z.den : ℤ)) := by
    apply Odd.mul (Odd.mul hx_num hy_num) h_odd_z_int
  have h_not_odd : ¬Odd (x.num * y.num * (z.den : ℤ)) := (Int.not_odd_iff_even (n := x.num * y.num * (z.den : ℤ))).mpr h_even_rhs
  exact h_not_odd h_odd_rhs

lemma den_mul_even_right (x y : ℚ) (hx : Odd x.num) (hy : Even y.den) : Even (x * y).den := by
  by_contra h_odd
  have h_odd' : Odd (x * y).den := Nat.not_even_iff_odd.mp h_odd
  have hx_num : Odd x.num := hx
  have hy_num : Odd y.num := coprime_of_even_den hy
  let z := x * y
  have h_eq : (z.num : ℚ) / (z.den : ℚ) = ((x.num : ℚ) / (x.den : ℚ)) * ((y.num : ℚ) / (y.den : ℚ)) := by
    rw [Rat.num_div_den x, Rat.num_div_den y, Rat.num_div_den z]
  have h_eq2 : (z.num : ℚ) / (z.den : ℚ) = ((x.num * y.num : ℤ) : ℚ) / ((x.den * y.den : ℕ) : ℚ) := by
    rw [h_eq]
    push_cast
    ring
  have h_den_nz1 : (z.den : ℚ) ≠ 0 := by positivity
  have h_den_nz2 : ((x.den * y.den : ℕ) : ℚ) ≠ 0 := by positivity
  have h_clear : (z.num : ℚ) * ((x.den * y.den : ℕ) : ℚ) = ((x.num * y.num : ℤ) : ℚ) * (z.den : ℚ) := by
    have h_eq_mul : ((z.num : ℚ) / (z.den : ℚ)) * ((z.den : ℚ) * ((x.den * y.den : ℕ) : ℚ)) = (((x.num * y.num : ℤ) : ℚ) / ((x.den * y.den : ℕ) : ℚ)) * ((z.den : ℚ) * ((x.den * y.den : ℕ) : ℚ)) := by
      rw [h_eq2]
    have h_lhs : ((z.num : ℚ) / (z.den : ℚ)) * ((z.den : ℚ) * ((x.den * y.den : ℕ) : ℚ)) = (z.num : ℚ) * ((x.den * y.den : ℕ) : ℚ) := by
      rw [← mul_assoc, div_mul_cancel₀ _ h_den_nz1]
    have h_rhs : (((x.num * y.num : ℤ) : ℚ) / ((x.den * y.den : ℕ) : ℚ)) * ((z.den : ℚ) * ((x.den * y.den : ℕ) : ℚ)) = ((x.num * y.num : ℤ) : ℚ) * (z.den : ℚ) := by
      rw [mul_comm (z.den : ℚ), ← mul_assoc, div_mul_cancel₀ _ h_den_nz2]
    rwa [h_lhs, h_rhs] at h_eq_mul
  have h_clear_int : z.num * (x.den * y.den : ℤ) = x.num * y.num * z.den := by
    exact_mod_cast h_clear
  have h_even_den : Even (x.den * y.den : ℤ) := by
    have hy_int : Even (y.den : ℤ) := by exact_mod_cast hy
    rcases hy_int with ⟨k, hk⟩
    use x.den * k
    rw [hk]
    ring
  have h_even_lhs : Even (z.num * (x.den * y.den : ℤ)) := by
    rcases h_even_den with ⟨m, hm⟩
    use z.num * m
    rw [hm]
    ring
  have h_even_rhs : Even (x.num * y.num * z.den) := by
    rw [← h_clear_int]
    exact h_even_lhs
  have h_odd_z : Odd z.den := h_odd'
  have h_odd_z_int : Odd (z.den : ℤ) := by exact_mod_cast h_odd_z
  have h_odd_rhs : Odd (x.num * y.num * (z.den : ℤ)) := by
    apply Odd.mul (Odd.mul hx_num hy_num) h_odd_z_int
  have h_not_odd : ¬Odd (x.num * y.num * (z.den : ℤ)) := (Int.not_odd_iff_even (n := x.num * y.num * (z.den : ℤ))).mpr h_even_rhs
  exact h_not_odd h_odd_rhs

lemma sigma_one_prime_pow_succ (p : ℕ) (hp : p.Prime) (j : ℕ) :
    ArithmeticFunction.sigma 1 (p ^ (j + 1)) = ArithmeticFunction.sigma 1 (p ^ j) + p ^ (j + 1) := by
  rw [ArithmeticFunction.sigma_one_apply, ArithmeticFunction.sigma_one_apply]
  rw [sum_divisors_prime_pow hp, sum_divisors_prime_pow hp]
  rw [sum_range_succ]


lemma sigma_one_odd_prime_pow_parity (p : ℕ) (hp : p.Prime) (hp_odd : Odd p) (j : ℕ) :
    Even (ArithmeticFunction.sigma 1 (p ^ j)) ↔ Odd j := by
  induction j with
  | zero =>
    rw [pow_zero]
    rw [ArithmeticFunction.sigma_one_apply, Nat.divisors_one, sum_singleton]
    decide
  | succ j ih =>
    rw [sigma_one_prime_pow_succ p hp j]
    rw [Nat.even_add]
    have h_pow_odd : Odd (p ^ (j + 1)) := Odd.pow hp_odd
    have h_pow_not_even : ¬ Even (p ^ (j + 1)) := Nat.not_even_iff_odd.mpr h_pow_odd
    rw [Nat.odd_add_one]
    rw [iff_false_intro h_pow_not_even]
    rw [iff_false]
    rw [not_iff_not]
    exact ih

lemma sigma_one_prime {p : ℕ} (hp : p.Prime) : ArithmeticFunction.sigma 1 p = p + 1 := by
  have h_pow : p = p ^ 1 := by ring
  nth_rw 1 [h_pow]
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  rw [sum_range_succ, sum_range_succ, sum_range_zero]
  ring

lemma S_p_eq (p : ℕ) (hp : p.Prime) : S p = (p + 2 : ℚ) / (p + 1 : ℚ) := by
  unfold S
  rw [Nat.Prime.divisors hp]
  rw [sum_insert (by intro hc; have : 1 = p := List.mem_singleton.mp hc; exact hp.ne_one this.symm), sum_singleton]
  rw [ArithmeticFunction.sigma_one_apply]
  simp only [Nat.divisors_one, sum_singleton, cast_one]
  rw [sigma_one_prime hp]
  push_cast
  have hp1 : (p + 1 : ℚ) ≠ 0 := by positivity
  have h_eq : (1 : ℚ) / (1 : ℚ) + (1 : ℚ) / (p + 1 : ℚ) = (p + 2 : ℚ) / (p + 1 : ℚ) := by
    field_simp
    ring
  exact h_eq

lemma even_den_of_div_odd_even {a : ℤ} {b : ℕ} (hb : b ≠ 0) (ha_odd : Odd a) (hb_even : Even b) {q : ℚ} (hq : q = (a : ℚ) / (b : ℚ)) : Even q.den := by
  by_contra h_odd
  have h_odd' : Odd q.den := Nat.not_even_iff_odd.mp h_odd
  have h_eq : (q.num : ℚ) / (q.den : ℚ) = (a : ℚ) / (b : ℚ) := by
    rw [Rat.num_div_den q]
    exact hq
  have h_den_nz1 : (q.den : ℚ) ≠ 0 := by positivity
  have h_den_nz2 : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  have h_clear : (q.num : ℚ) * (b : ℚ) = (a : ℚ) * (q.den : ℚ) := by
    have h_eq_mul : ((q.num : ℚ) / (q.den : ℚ)) * ((q.den : ℚ) * (b : ℚ)) = ((a : ℚ) / (b : ℚ)) * ((q.den : ℚ) * (b : ℚ)) := by
      rw [h_eq]
    have h_lhs : ((q.num : ℚ) / (q.den : ℚ)) * ((q.den : ℚ) * (b : ℚ)) = (q.num : ℚ) * (b : ℚ) := by
      rw [← mul_assoc, div_mul_cancel₀ _ h_den_nz1]
    have h_rhs : ((a : ℚ) / (b : ℚ)) * ((q.den : ℚ) * (b : ℚ)) = (a : ℚ) * (q.den : ℚ) := by
      rw [mul_comm (q.den : ℚ), ← mul_assoc, div_mul_cancel₀ _ h_den_nz2]
    rwa [h_lhs, h_rhs] at h_eq_mul
  have h_clear_int : q.num * (b : ℤ) = a * (q.den : ℤ) := by
    exact_mod_cast h_clear
  have h_even_den : Even (b : ℤ) := by exact_mod_cast hb_even
  have h_even_lhs : Even (q.num * (b : ℤ)) := by
    rcases h_even_den with ⟨m, hm⟩
    use q.num * m
    rw [hm]
    ring
  have h_even_rhs : Even (a * (q.den : ℤ)) := by
    rw [← h_clear_int]
    exact h_even_lhs
  have h_odd_den_int : Odd (q.den : ℤ) := by exact_mod_cast h_odd'
  have h_odd_rhs : Odd (a * (q.den : ℤ)) := by
    apply Odd.mul ha_odd h_odd_den_int
  have h_not_odd : ¬Odd (a * (q.den : ℤ)) := (Int.not_odd_iff_even (n := a * (q.den : ℤ))).mpr h_even_rhs
  exact h_not_odd h_odd_rhs

lemma Even_S_p_den {p : ℕ} (hp : p.Prime) (hp_odd : Odd p) : Even (S p).den := by
  have h_S : S p = (p + 2 : ℚ) / (p + 1 : ℚ) := S_p_eq p hp
  have hb_nz : p + 1 ≠ 0 := by omega
  have ha_odd : Odd (p + 2 : ℤ) := by
    rcases hp_odd with ⟨k, hk⟩
    use k + 1
    omega
  have hb_even : Even (p + 1) := by
    rcases hp_odd with ⟨k, hk⟩
    use k + 1
    omega
  have h_S2 : S p = ((p + 2 : ℤ) : ℚ) / ((p + 1 : ℤ) : ℚ) := by
    rw [h_S]
    push_cast
    rfl
  exact even_den_of_div_odd_even hb_nz ha_odd hb_even h_S2


lemma den_add_even_odd (x y : ℚ) (hx : Even x.den) (hy : Odd y.den) : Even (x + y).den := by
  by_contra h_odd
  have h_odd' : Odd (x + y).den := Nat.not_even_iff_odd.mp h_odd
  have hx_num : Odd x.num := coprime_of_even_den hx
  let z := x + y
  have h_eq : (z.num : ℚ) / (z.den : ℚ) = ((x.num : ℚ) / (x.den : ℚ)) + ((y.num : ℚ) / (y.den : ℚ)) := by
    rw [Rat.num_div_den x, Rat.num_div_den y, Rat.num_div_den z]
  have h_den_nz1' : (x.den : ℚ) ≠ 0 := by positivity
  have h_den_nz2' : (y.den : ℚ) ≠ 0 := by positivity
  have h_eq2 : (z.num : ℚ) / (z.den : ℚ) = ((x.num * y.den + y.num * x.den : ℤ) : ℚ) / ((x.den * y.den : ℕ) : ℚ) := by
    rw [h_eq]
    rw [div_add_div (x.num : ℚ) (y.num : ℚ) h_den_nz1' h_den_nz2']
    push_cast
    ring
  have h_den_nz1 : (z.den : ℚ) ≠ 0 := by positivity
  have h_den_nz2 : ((x.den * y.den : ℕ) : ℚ) ≠ 0 := by positivity
  have h_clear : (z.num : ℚ) * ((x.den * y.den : ℕ) : ℚ) = ((x.num * y.den + y.num * x.den : ℤ) : ℚ) * (z.den : ℚ) := by
    have h_eq_mul : ((z.num : ℚ) / (z.den : ℚ)) * ((z.den : ℚ) * ((x.den * y.den : ℕ) : ℚ)) = (((x.num * y.den + y.num * x.den : ℤ) : ℚ) / ((x.den * y.den : ℕ) : ℚ)) * ((z.den : ℚ) * ((x.den * y.den : ℕ) : ℚ)) := by
      rw [h_eq2]
    have h_lhs : ((z.num : ℚ) / (z.den : ℚ)) * ((z.den : ℚ) * ((x.den * y.den : ℕ) : ℚ)) = (z.num : ℚ) * ((x.den * y.den : ℕ) : ℚ) := by
      rw [← mul_assoc, div_mul_cancel₀ _ h_den_nz1]
    have h_rhs : (((x.num * y.den + y.num * x.den : ℤ) : ℚ) / ((x.den * y.den : ℕ) : ℚ)) * ((z.den : ℚ) * ((x.den * y.den : ℕ) : ℚ)) = ((x.num * y.den + y.num * x.den : ℤ) : ℚ) * (z.den : ℚ) := by
      rw [mul_comm (z.den : ℚ), ← mul_assoc, div_mul_cancel₀ _ h_den_nz2]
    rwa [h_lhs, h_rhs] at h_eq_mul
  have h_clear_int : z.num * (x.den * y.den : ℤ) = (x.num * y.den + y.num * x.den) * z.den := by
    exact_mod_cast h_clear
  have h_even_den : Even (x.den * y.den : ℤ) := by
    have hx_int : Even (x.den : ℤ) := by exact_mod_cast hx
    rcases hx_int with ⟨k, hk⟩
    use k * y.den
    rw [hk]
    ring
  have h_even_lhs : Even (z.num * (x.den * y.den : ℤ)) := by
    rcases h_even_den with ⟨m, hm⟩
    use z.num * m
    rw [hm]
    ring
  have h_even_rhs : Even ((x.num * y.den + y.num * x.den) * z.den) := by
    rw [← h_clear_int]
    exact h_even_lhs
  have h_odd_sum : Odd (x.num * y.den + y.num * x.den) := by
    have h_odd_term1 : Odd (x.num * y.den) := Odd.mul hx_num (by exact_mod_cast hy)
    have h_even_term2 : Even (y.num * x.den) := by
      have hx_int : Even (x.den : ℤ) := by exact_mod_cast hx
      rcases hx_int with ⟨k, hk⟩
      use y.num * k
      rw [hk]
      ring
    rcases h_odd_term1 with ⟨a, ha⟩
    rcases h_even_term2 with ⟨b, hb⟩
    use a + b
    omega
  have h_odd_rhs : Odd ((x.num * y.den + y.num * x.den) * z.den) := by
    apply Odd.mul h_odd_sum (by exact_mod_cast h_odd')
  have h_not_odd : ¬Odd ((x.num * y.den + y.num * x.den) * z.den) := (Int.not_odd_iff_even (n := (x.num * y.den + y.num * x.den) * z.den)).mpr h_even_rhs
  exact h_not_odd h_odd_rhs



lemma padicValNat_one_plus_pow_two (p : ℕ) (hp_odd : Odd p) : padicValNat 2 (1 + p ^ 2) = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hp_odd with ⟨k, rfl⟩
  have h_eq : 1 + (2 * k + 1) ^ 2 = 2 * (2 * (k ^ 2 + k) + 1) := by ring
  have h_odd : Odd (2 * (k ^ 2 + k) + 1) := ⟨k ^ 2 + k, rfl⟩
  have h_val_eq : padicValNat 2 (2 * (2 * (k ^ 2 + k) + 1)) = 1 := by
    rw [padicValNat.mul (by decide) (by omega)]
    have h_two : padicValNat 2 2 = 1 := padicValNat_self
    rw [h_two]
    have h_not_dvd : ¬ 2 ∣ 2 * (k ^ 2 + k) + 1 := by
      rw [← even_iff_two_dvd]
      rw [Nat.not_even_iff_odd]
      exact h_odd
    have : padicValNat 2 (2 * (k ^ 2 + k) + 1) = 0 := padicValNat.eq_zero_of_not_dvd h_not_dvd
    rw [this, add_zero]
  rw [h_eq, h_val_eq]

lemma even_one_plus_pow_two (p : ℕ) (hp_odd : Odd p) : Even (1 + p ^ 2) := by
  rcases hp_odd with ⟨k, rfl⟩
  use 2 * k ^ 2 + 2 * k + 1
  ring

lemma sum_pow_two_split (p m : ℕ) :
    (∑ i ∈ range (2 * m), p ^ (2 * i)) = (1 + p ^ 2) * (∑ i ∈ range m, (p ^ 2) ^ (2 * i)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h_split : 2 * (m + 1) = 2 * m + 2 := by ring
    rw [h_split, sum_range_add, sum_range_succ, sum_range_succ, sum_range_zero]
    rw [sum_range_succ]
    rw [ih]
    simp
    ring

lemma padicValNat_sum_pow_two (N : ℕ) (p : ℕ) (hp_odd : Odd p) :
    padicValNat 2 (∑ m ∈ range N, p ^ (2 * m)) = padicValNat 2 N := by
  induction' N using Nat.strong_induction_on generalizing p
  rename_i N ih
  rcases N with _ | N
  · simp
  · by_cases h_even : Even (N + 1)
    · rcases h_even with ⟨m, hm⟩
      have hm_eq : N + 1 = 2 * m := by omega
      have hm_pos : m ≥ 1 := by omega
      rw [hm_eq]
      rw [sum_pow_two_split]
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hp_pos : p > 0 := by
        rcases hp_odd with ⟨k, rfl⟩
        omega
      have h_pe_pos : 0 < 1 + p ^ 2 := by positivity
      have h_sum_pos : 0 < (∑ i ∈ range m, (p ^ 2) ^ (2 * i)) := by
        have h_nonempty : (range m).Nonempty := ⟨0, mem_range.mpr (by omega)⟩
        apply sum_pos (fun i _ => pow_pos (pow_pos hp_pos 2) (2 * i)) h_nonempty
      have h_mul_ne : (1 + p ^ 2) * (∑ i ∈ range m, (p ^ 2) ^ (2 * i)) ≠ 0 := (mul_pos h_pe_pos h_sum_pos).ne'
      rw [padicValNat.mul h_pe_pos.ne' h_sum_pos.ne']
      have h1 : padicValNat 2 (1 + p ^ 2) = 1 := padicValNat_one_plus_pow_two p hp_odd
      have h2 : padicValNat 2 (∑ i ∈ range m, (p ^ 2) ^ (2 * i)) = padicValNat 2 m := by
        have h_odd2 : Odd (p ^ 2) := Odd.pow hp_odd
        have h_lt : m < N + 1 := by omega
        exact ih m h_lt (p ^ 2) h_odd2
      rw [h1, h2]
      have h_eq : padicValNat 2 (2 * m) = 1 + padicValNat 2 m := by
        have hm_ne : m ≠ 0 := by omega
        rw [padicValNat.mul (by decide) hm_ne]
        have : padicValNat 2 2 = 1 := padicValNat_self
        rw [this]
      omega
    · have h_odd : ¬ Even (N + 1) := h_even
      have ⟨m, hm⟩ : ∃ m, N + 1 = 2 * m + 1 := by
        rw [Nat.not_even_iff_odd] at h_odd
        exact h_odd
      rw [hm]
      rw [sum_range_succ]
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have h_even_sum : Even (∑ i ∈ range (2 * m), p ^ (2 * i)) := by
        rw [sum_pow_two_split]
        have h_even : Even (1 + p ^ 2) := even_one_plus_pow_two p hp_odd
        rcases h_even with ⟨k, hk⟩
        use k * (∑ i ∈ range m, (p ^ 2) ^ (2 * i))
        rw [hk]
        ring
      have h_odd_pow : ¬ Even (p ^ (2 * (2 * m))) := by
        rw [Nat.not_even_iff_odd]
        exact Odd.pow hp_odd
      have h_odd_total : ¬ Even (∑ i ∈ range (2 * m), p ^ (2 * i) + p ^ (2 * (2 * m))) := by
        rw [Nat.even_add]
        simp [h_even_sum, h_odd_pow]
      have h_val_zero : padicValNat 2 (∑ i ∈ range (2 * m), p ^ (2 * i) + p ^ (2 * (2 * m))) = 0 := by
        apply padicValNat.eq_zero_of_not_dvd
        rw [← even_iff_two_dvd]
        exact h_odd_total
      rw [h_val_zero]
      have h_val_N_zero : padicValNat 2 (2 * m + 1) = 0 := by
        apply padicValNat.eq_zero_of_not_dvd
        rw [← even_iff_two_dvd]
        exact Nat.not_even_iff_odd.mpr ⟨m, rfl⟩
      omega

lemma unique_max_valuation (Y : ℕ) (y : ℕ) (hy_pos : y > 0) (hy_le : y ≤ Y) (hy_ne : y ≠ 2 ^ (Nat.log 2 Y)) :
    padicValNat 2 y < Nat.log 2 Y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hc
  push_neg at hc
  have h_dvd : 2 ^ (Nat.log 2 Y) ∣ y := by
    rw [padicValNat_dvd_iff]
    right
    exact hc
  rcases h_dvd with ⟨k, rfl⟩
  have hk_pos : k > 0 := by
    by_contra hk0
    have : k = 0 := by omega
    subst this
    simp at hy_pos
  by_cases hk1 : k = 1
  · subst hk1
    simp at hy_ne
  · have hk_ge_2 : k ≥ 2 := by omega
    have h_log_le : 2 ^ (Nat.log 2 Y) * k ≤ Y := hy_le
    have h_le : 2 ^ (Nat.log 2 Y + 1) ≤ 2 ^ (Nat.log 2 Y) * k := by
      rw [pow_add, pow_one]
      nlinarith
    have h_gt : Y < 2 ^ (Nat.log 2 Y + 1) := Nat.lt_pow_succ_log_self (by decide) Y
    omega

lemma sigma_one_prime_pow_eq_sum (p : ℕ) (hp : p.Prime) (j : ℕ) :
    ArithmeticFunction.sigma 1 (p ^ j) = ∑ i ∈ range (j + 1), p ^ i := by
  rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_prime_pow hp]

lemma sigma_split (p : ℕ) (k : ℕ) :
    (∑ i ∈ range (2 * k + 2), p ^ i) = (p + 1) * (∑ i ∈ range (k + 1), p ^ (2 * i)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h_split1 : 2 * (k + 1) + 2 = (2 * k + 2) + 1 + 1 := by ring
    rw [h_split1, sum_range_succ, sum_range_succ]
    nth_rw 2 [sum_range_succ]
    rw [ih]
    ring

lemma padicValNat_sigma_odd (p : ℕ) (hp : p.Prime) (hp_odd : Odd p) (j : ℕ) (hj_odd : Odd j) :
    padicValNat 2 (ArithmeticFunction.sigma 1 (p ^ j)) = padicValNat 2 (p + 1) + padicValNat 2 (j + 1) - 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hj_odd with ⟨k, rfl⟩
  rw [sigma_one_prime_pow_eq_sum p hp (2 * k + 1)]
  rw [sigma_split]
  have hp1_ne : p + 1 ≠ 0 := by omega
  have hp_pos : p > 0 := by
    rcases hp_odd with ⟨m, rm⟩
    omega
  have h_sum_pos : (∑ i ∈ range (k + 1), p ^ (2 * i)) ≠ 0 := by
    have h_nonempty : (range (k + 1)).Nonempty := ⟨0, mem_range.mpr (by omega)⟩
    have h_gt : 0 < ∑ i ∈ range (k + 1), p ^ (2 * i) := by
      apply sum_pos (fun i _ => by positivity) h_nonempty
    exact h_gt.ne'
  rw [padicValNat.mul hp1_ne h_sum_pos]
  rw [padicValNat_sum_pow_two (k + 1) p hp_odd]
  have h_eq : padicValNat 2 (2 * k + 2) = 1 + padicValNat 2 (k + 1) := by
    have h_split : 2 * k + 2 = 2 * (k + 1) := by ring
    rw [h_split]
    have hk1_ne : k + 1 ≠ 0 := by omega
    rw [padicValNat.mul (by decide) hk1_ne]
    have : padicValNat 2 2 = 1 := padicValNat_self
    rw [this]
  rw [h_eq]
  omega

lemma padicValRat_one_div_nat (S : ℕ) (hS : S ≠ 0) : padicValRat 2 (1 / (S : ℚ)) = - (padicValNat 2 S : ℤ) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS_pos : 0 < S := Nat.pos_of_ne_zero hS
  have h_num : ((1 : ℚ) / (S : ℚ)).num = 1 := by
    have : (1 : ℚ) / (S : ℚ) = (S : ℚ)⁻¹ := by rw [one_div]
    rw [this]
    exact Rat.inv_natCast_num_of_pos hS_pos
  have h_den : ((1 : ℚ) / (S : ℚ)).den = S := by
    have : (1 : ℚ) / (S : ℚ) = (S : ℚ)⁻¹ := by rw [one_div]
    rw [this]
    exact Rat.inv_natCast_den_of_pos hS_pos
  unfold padicValRat
  rw [h_num, h_den]
  have h_one : padicValInt 2 1 = 0 := padicValInt.one
  rw [h_one]
  ring

lemma S_prime_pow (p : ℕ) (hp : p.Prime) (e : ℕ) :
    S (p ^ e) = ∑ x ∈ range (e + 1), (1 : ℚ) / (ArithmeticFunction.sigma 1 (p ^ x) : ℚ) := by
  unfold S
  rw [Nat.sum_divisors_prime_pow hp]

lemma S_prime_pow_succ (p : ℕ) (hp : p.Prime) (e : ℕ) :
    S (p ^ (e + 1)) = S (p ^ e) + (1 : ℚ) / (ArithmeticFunction.sigma 1 (p ^ (e + 1)) : ℚ) := by
  rw [S_prime_pow p hp (e + 1), S_prime_pow p hp e]
  rw [sum_range_succ]




lemma even_den_iff_padicValRat_lt_zero (q : ℚ) : Even q.den ↔ padicValRat 2 q < 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_cop : Nat.Coprime q.num.natAbs q.den := q.reduced
  unfold padicValRat
  simp only [sub_lt_zero]
  have h_cases : (2 ∣ q.den) ∨ ¬(2 ∣ q.den) := em _
  rcases h_cases with h_even | h_odd
  · have h_not_dvd : ¬ (2 : ℤ) ∣ q.num := by
      intro h_dvd
      have h_dvd_nat : 2 ∣ q.num.natAbs := Int.natAbs_dvd_natAbs.mpr h_dvd
      have h_gcd : 2 ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd h_dvd_nat h_even
      rw [Nat.Coprime.gcd_eq_one h_cop] at h_gcd
      norm_num at h_gcd
    have h_zero : padicValInt 2 q.num = 0 := padicValInt.eq_zero_of_not_dvd h_not_dvd
    rw [h_zero]
    have h_pos : padicValNat 2 q.den ≥ 1 := by
      apply one_le_padicValNat_of_dvd (Rat.den_nz q) h_even
    simp [even_iff_two_dvd.mpr h_even]
    omega
  · have h_zero : padicValNat 2 q.den = 0 := padicValNat.eq_zero_of_not_dvd h_odd
    rw [h_zero]
    have h_nonneg : padicValInt 2 q.num ≥ 0 := Nat.zero_le _
    have h_nonneg_int : (padicValInt 2 q.num : ℤ) ≥ 0 := by exact_mod_cast h_nonneg
    simp [even_iff_two_dvd, h_odd, h_nonneg_int]

lemma padicValRat_sum_unique_min (s : Finset ℕ) (F : ℕ → ℚ) (j : ℕ) (hj : j ∈ s)
    (h_pos : ∀ i ∈ s, 0 < F i) (h_min : ∀ i ∈ s, i ≠ j → padicValRat 2 (F j) < padicValRat 2 (F i)) :
    padicValRat 2 (s.sum F) = padicValRat 2 (F j) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F' := fun i => if i ∈ s then F i else 1
  have h_pos' : ∀ i, 0 < F' i := by
    intro i
    dsimp [F']
    split_ifs with h
    · exact h_pos i h
    · exact one_pos
  have h_eq_sum : s.sum F = s.sum F' := by
    apply sum_congr rfl
    intro x hx
    dsimp [F']
    rw [if_pos hx]
  have h_eq_sum_erase : (s.erase j).sum F = (s.erase j).sum F' := by
    apply sum_congr rfl
    intro x hx
    have hx_s := mem_of_mem_erase hx
    dsimp [F']
    rw [if_pos hx_s]
  have h_eq_j : F j = F' j := by
    dsimp [F']
    rw [if_pos hj]
  rw [h_eq_sum, h_eq_j]
  by_cases h_single : s = {j}
  · rw [h_single, sum_singleton]
  · have h_nonempty : (s.erase j).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hc
      have h_subset : s ⊆ {j} := by
        intro x hx
        by_cases hx_eq : x = j
        · subst hx_eq; simp
        · have : x ∈ s.erase j := mem_erase.mpr ⟨hx_eq, hx⟩
          rw [hc] at this
          simp at this
      have h_eq : s = {j} := by
        ext x
        simp only [mem_singleton]
        constructor
        · intro h; exact Finset.mem_singleton.mp (h_subset h)
        · rintro rfl; exact hj
      exact h_single h_eq
    have h_split : s.sum F' = F' j + (s.erase j).sum F' := by rw [← add_sum_erase s F' hj]
    rw [h_split]
    have h_lt : padicValRat 2 (F' j) < padicValRat 2 ((s.erase j).sum F') := by
      apply padicValRat.lt_sum_of_lt h_nonempty
      · intro i hi
        have hi_s := mem_of_mem_erase hi
        have hi_neq := ne_of_mem_erase hi
        have h_min_i := h_min i hi_s hi_neq
        have h_eq_i : F i = F' i := by
          dsimp [F']
          rw [if_pos hi_s]
        rwa [h_eq_j, h_eq_i] at h_min_i
      · exact h_pos'
    have h_split_nz : F' j + (s.erase j).sum F' ≠ 0 := by
      have : 0 < F' j + (s.erase j).sum F' := by
        apply add_pos (h_pos' j)
        apply sum_pos
        · intro i hi
          exact h_pos' i
        · exact h_nonempty
      exact this.ne'
    have h_j_nz : F' j ≠ 0 := (h_pos' j).ne'
    have h_erase_nz : (s.erase j).sum F' ≠ 0 := by
      have : 0 < (s.erase j).sum F' := by
        apply sum_pos
        · intro i hi
          exact h_pos' i
        · exact h_nonempty
      exact this.ne'
    exact padicValRat.add_eq_of_lt h_split_nz h_j_nz h_erase_nz h_lt





lemma padicValNat_two_pow (V : ℕ) : padicValNat 2 (2 ^ V) = V := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact padicValNat.prime_pow V

lemma Even_S_prime_pow_den {p : ℕ} (hp : p.Prime) (hp_odd : Odd p) (e : ℕ) (he : e ≥ 1) : Even (S (p ^ e)).den := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp_pos : (p : ℚ) > 0 := by exact_mod_cast hp.pos
  rw [even_den_iff_padicValRat_lt_zero]
  rw [S_prime_pow p hp e]
  let F := fun x => (1 : ℚ) / (ArithmeticFunction.sigma 1 (p ^ x) : ℚ)
  let V := Nat.log 2 (e + 1)
  let j := 2 ^ V - 1
  have h_V_ge_1 : V ≥ 1 := by
    dsimp [V]
    have h_le : 2 ≤ e + 1 := by omega
    exact Nat.le_log_of_pow_le (by decide) h_le
  have h_j_lt : j < e + 1 := by
    dsimp [j]
    have h_pow_le : 2 ^ V ≤ e + 1 := Nat.pow_log_le_self 2 (by omega)
    omega
  have h_j_mem : j ∈ range (e + 1) := mem_range.mpr h_j_lt
  have h_pos : ∀ i ∈ range (e + 1), 0 < F i := by
    intro i _
    dsimp [F]
    have h_sig : (ArithmeticFunction.sigma 1 (p ^ i) : ℚ) > 0 := by
      rw [sigma_one_prime_pow_eq_sum p hp i]
      push_cast
      have h_nonempty : (range (i + 1)).Nonempty := ⟨0, mem_range.mpr (by omega)⟩
      apply sum_pos (fun x _ => by positivity) h_nonempty
    exact one_div_pos.mpr h_sig
  have h_min : ∀ i ∈ range (e + 1), i ≠ j → padicValRat 2 (F j) < padicValRat 2 (F i) := by
    intro i hi_mem hi_ne
    have hi_lt := mem_range.mp hi_mem
    have h_sig_i : (ArithmeticFunction.sigma 1 (p ^ i) : ℚ) > 0 := by
      rw [sigma_one_prime_pow_eq_sum p hp i]
      push_cast
      have h_nonempty : (range (i + 1)).Nonempty := ⟨0, mem_range.mpr (by omega)⟩
      apply sum_pos (fun x _ => by positivity) h_nonempty
    have h_sig_j : (ArithmeticFunction.sigma 1 (p ^ j) : ℚ) > 0 := by
      rw [sigma_one_prime_pow_eq_sum p hp j]
      push_cast
      have h_nonempty : (range (j + 1)).Nonempty := ⟨0, mem_range.mpr (by omega)⟩
      apply sum_pos (fun x _ => by positivity) h_nonempty
    have h_sig_i_nat : ArithmeticFunction.sigma 1 (p ^ i) ≠ 0 := by exact_mod_cast h_sig_i.ne'
    have h_sig_j_nat : ArithmeticFunction.sigma 1 (p ^ j) ≠ 0 := by exact_mod_cast h_sig_j.ne'
    rw [padicValRat_one_div_nat _ h_sig_j_nat, padicValRat_one_div_nat _ h_sig_i_nat]
    have hj_odd : Odd j := by
      dsimp [j]
      use 2 ^ (V - 1) - 1
      have : 2 ^ V = 2 * 2 ^ (V - 1) := by
        have h_v_eq : V = V - 1 + 1 := by omega
        nth_rw 1 [h_v_eq]
        rw [pow_succ, mul_comm]
      have : 1 ≤ 2 ^ (V - 1) := Nat.one_le_pow (V - 1) 2 (by decide)
      omega
    rw [padicValNat_sigma_odd p hp hp_odd j hj_odd]
    have h_p1_even : Even (p + 1) := by
      rcases hp_odd with ⟨k, rfl⟩
      use k + 1
      ring
    have h_p1_val : padicValNat 2 (p + 1) ≥ 1 := one_le_padicValNat_of_dvd (by omega) (by rwa [← even_iff_two_dvd])
    by_cases h_even_i : Even i
    · have h_sig_odd : ¬ Even (ArithmeticFunction.sigma 1 (p ^ i)) := by
        rw [sigma_one_odd_prime_pow_parity p hp hp_odd i]
        rw [Nat.not_odd_iff_even]
        exact h_even_i
      have h_val_zero : padicValNat 2 (ArithmeticFunction.sigma 1 (p ^ i)) = 0 := by
        apply padicValNat.eq_zero_of_not_dvd
        rw [← even_iff_two_dvd]
        exact h_sig_odd
      rw [h_val_zero]
      have h_val_j_pos : padicValNat 2 (p + 1) + padicValNat 2 (j + 1) - 1 > 0 := by
        have h_j1_eq : j + 1 = 2 ^ V := by
          dsimp [j]
          have : 1 ≤ 2 ^ V := Nat.one_le_pow V 2 (by decide)
          omega
        rw [h_j1_eq, padicValNat_two_pow]
        omega
      omega
    · have h_odd_i : ¬ Even i := h_even_i
      have hi_odd : Odd i := Nat.not_even_iff_odd.mp h_odd_i
      rw [padicValNat_sigma_odd p hp hp_odd i hi_odd]
      have h_j1_eq : j + 1 = 2 ^ V := by
        dsimp [j]
        have : 1 ≤ 2 ^ V := Nat.one_le_pow V 2 (by decide)
        omega
      rw [h_j1_eq, padicValNat_two_pow]
      have h_i_ne_j : i + 1 ≠ 2 ^ V := by
        intro hc
        have : i = j := by dsimp [j]; omega
        exact hi_ne this
      have h_unique : padicValNat 2 (i + 1) < V := by
        apply unique_max_valuation (e + 1) (i + 1) (by omega) (by omega) h_i_ne_j
      omega
  have h_sum_val := padicValRat_sum_unique_min (range (e + 1)) F j h_j_mem h_pos h_min
  rw [h_sum_val]
  have h_sig_j : (ArithmeticFunction.sigma 1 (p ^ j) : ℚ) > 0 := by
    rw [sigma_one_prime_pow_eq_sum p hp j]
    push_cast
    have h_nonempty : (range (j + 1)).Nonempty := ⟨0, mem_range.mpr (by omega)⟩
    apply sum_pos (fun x _ => by positivity) h_nonempty
  have h_sig_j_nat : ArithmeticFunction.sigma 1 (p ^ j) ≠ 0 := by exact_mod_cast h_sig_j.ne'
  rw [padicValRat_one_div_nat _ h_sig_j_nat]
  have hj_odd : Odd j := by
    dsimp [j]
    use 2 ^ (V - 1) - 1
    have : 2 ^ V = 2 * 2 ^ (V - 1) := by
      have h_v_eq : V = V - 1 + 1 := by omega
      nth_rw 1 [h_v_eq]
      rw [pow_succ, mul_comm]
    have : 1 ≤ 2 ^ (V - 1) := Nat.one_le_pow (V - 1) 2 (by decide)
    omega
  rw [padicValNat_sigma_odd p hp hp_odd j hj_odd]
  have h_j1_eq : j + 1 = 2 ^ V := by
    dsimp [j]
    have : 1 ≤ 2 ^ V := Nat.one_le_pow V 2 (by decide)
    omega
  rw [h_j1_eq, padicValNat_two_pow]
  have h_p1_even : Even (p + 1) := by
    rcases hp_odd with ⟨k, rfl⟩
    use k + 1
    ring
  have h_p1_val : padicValNat 2 (p + 1) ≥ 1 := one_le_padicValNat_of_dvd (by omega) (by rwa [← even_iff_two_dvd])
  omega

lemma even_num_of_even_den_mul_int (x y : ℚ) (hx : Even x.den) (h_int : (x * y).den = 1) : Even y.num := by
  let z := x * y
  have h_eq : (z.num : ℚ) / (z.den : ℚ) = ((x.num : ℚ) / (x.den : ℚ)) * ((y.num : ℚ) / (y.den : ℚ)) := by
    rw [Rat.num_div_den x, Rat.num_div_den y, Rat.num_div_den z]
  have h_eq2 : (z.num : ℚ) / (z.den : ℚ) = ((x.num * y.num : ℤ) : ℚ) / ((x.den * y.den : ℕ) : ℚ) := by
    rw [h_eq]
    push_cast
    ring
  have h_den_nz1 : (z.den : ℚ) ≠ 0 := by positivity
  have h_den_nz2 : ((x.den * y.den : ℕ) : ℚ) ≠ 0 := by positivity
  have h_clear : (z.num : ℚ) * ((x.den * y.den : ℕ) : ℚ) = ((x.num * y.num : ℤ) : ℚ) * (z.den : ℚ) := by
    have h_eq_mul : ((z.num : ℚ) / (z.den : ℚ)) * ((z.den : ℚ) * ((x.den * y.den : ℕ) : ℚ)) = (((x.num * y.num : ℤ) : ℚ) / ((x.den * y.den : ℕ) : ℚ)) * ((z.den : ℚ) * ((x.den * y.den : ℕ) : ℚ)) := by
      rw [h_eq2]
    have h_lhs : ((z.num : ℚ) / (z.den : ℚ)) * ((z.den : ℚ) * ((x.den * y.den : ℕ) : ℚ)) = (z.num : ℚ) * ((x.den * y.den : ℕ) : ℚ) := by
      rw [← mul_assoc, div_mul_cancel₀ _ h_den_nz1]
    have h_rhs : (((x.num * y.num : ℤ) : ℚ) / ((x.den * y.den : ℕ) : ℚ)) * ((z.den : ℚ) * ((x.den * y.den : ℕ) : ℚ)) = ((x.num * y.num : ℤ) : ℚ) * (z.den : ℚ) := by
      rw [mul_comm (z.den : ℚ), ← mul_assoc, div_mul_cancel₀ _ h_den_nz2]
    rwa [h_lhs, h_rhs] at h_eq_mul
  have h_clear_int : z.num * (x.den * y.den : ℤ) = x.num * y.num * z.den := by
    exact_mod_cast h_clear
  have h_z_den_eq : (z.den : ℤ) = 1 := by
    rw [h_int]
    rfl
  rw [h_z_den_eq, mul_one] at h_clear_int
  have hx_even_int : Even (x.den : ℤ) := by exact_mod_cast hx
  rcases hx_even_int with ⟨k, hk⟩
  have h_even_lhs : Even (z.num * (x.den * y.den : ℤ)) := by
    use z.num * (k * y.den)
    rw [hk]
    ring
  rw [h_clear_int] at h_even_lhs
  have hx_odd : Odd x.num := coprime_of_even_den hx
  have hy_even : Even y.num := by
    by_contra h_odd
    have h_odd' : Odd y.num := Int.not_even_iff_odd.mp h_odd
    have h_mul_odd : Odd (x.num * y.num) := Odd.mul hx_odd h_odd'
    exact (Int.not_even_iff_odd.mpr h_mul_odd) h_even_lhs
  exact hy_even

lemma den_mul_even_left_odd_right (x y : ℚ) (hx : Even x.den) (hy : Odd y.den) (hy_num : Odd y.num) : Even (x * y).den := by
  by_contra h_odd
  have h_odd' : Odd (x * y).den := Nat.not_even_iff_odd.mp h_odd
  have hx_num : Odd x.num := coprime_of_even_den hx
  let z := x * y
  have h_eq : (z.num : ℚ) / (z.den : ℚ) = ((x.num : ℚ) / (x.den : ℚ)) * ((y.num : ℚ) / (y.den : ℚ)) := by
    rw [Rat.num_div_den x, Rat.num_div_den y, Rat.num_div_den z]
  have h_eq2 : (z.num : ℚ) / (z.den : ℚ) = ((x.num * y.num : ℤ) : ℚ) / ((x.den * y.den : ℕ) : ℚ) := by
    rw [h_eq]
    push_cast
    ring
  have h_den_nz1 : (z.den : ℚ) ≠ 0 := by positivity
  have h_den_nz2 : ((x.den * y.den : ℕ) : ℚ) ≠ 0 := by positivity
  have h_clear : (z.num : ℚ) * ((x.den * y.den : ℕ) : ℚ) = ((x.num * y.num : ℤ) : ℚ) * (z.den : ℚ) := by
    have h_eq_mul : ((z.num : ℚ) / (z.den : ℚ)) * ((z.den : ℚ) * ((x.den * y.den : ℕ) : ℚ)) = (((x.num * y.num : ℤ) : ℚ) / ((x.den * y.den : ℕ) : ℚ)) * ((z.den : ℚ) * ((x.den * y.den : ℕ) : ℚ)) := by
      rw [h_eq2]
    have h_lhs : ((z.num : ℚ) / (z.den : ℚ)) * ((z.den : ℚ) * ((x.den * y.den : ℕ) : ℚ)) = (z.num : ℚ) * ((x.den * y.den : ℕ) : ℚ) := by
      rw [← mul_assoc, div_mul_cancel₀ _ h_den_nz1]
    have h_rhs : (((x.num * y.num : ℤ) : ℚ) / ((x.den * y.den : ℕ) : ℚ)) * ((z.den : ℚ) * ((x.den * y.den : ℕ) : ℚ)) = ((x.num * y.num : ℤ) : ℚ) * (z.den : ℚ) := by
      rw [mul_comm (z.den : ℚ), ← mul_assoc, div_mul_cancel₀ _ h_den_nz2]
    rwa [h_lhs, h_rhs] at h_eq_mul
  have h_clear_int : z.num * (x.den * y.den : ℤ) = x.num * y.num * z.den := by
    exact_mod_cast h_clear
  have h_even_den : Even (x.den * y.den : ℤ) := by
    have hx_int : Even (x.den : ℤ) := by exact_mod_cast hx
    rcases hx_int with ⟨k, hk⟩
    use k * y.den
    rw [hk]
    ring
  have h_even_lhs : Even (z.num * (x.den * y.den : ℤ)) := by
    rcases h_even_den with ⟨m, hm⟩
    use z.num * m
    rw [hm]
    ring
  have h_even_rhs : Even (x.num * y.num * z.den) := by
    rw [← h_clear_int]
    exact h_even_lhs
  have h_odd_z : Odd z.den := h_odd'
  have h_odd_z_int : Odd (z.den : ℤ) := by exact_mod_cast h_odd_z
  have h_odd_y_num_int : Odd (y.num : ℤ) := by exact_mod_cast hy_num
  have h_odd_rhs : Odd (x.num * y.num * (z.den : ℤ)) := by
    apply Odd.mul (Odd.mul hx_num h_odd_y_num_int) h_odd_z_int
  have h_not_odd : ¬Odd (x.num * y.num * (z.den : ℤ)) := (Int.not_odd_iff_even (n := x.num * y.num * (z.den : ℤ))).mpr h_even_rhs
  exact h_not_odd h_odd_rhs

lemma Even_S_odd_den (n : ℕ) (hn : n > 1) (h_odd : Odd n) : Even (S n).den := by
  induction' n using Nat.strong_induction_on
  rename_i n ih
  have hn_gt_1 : n > 1 := hn
  have ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hn_gt_1.ne'
  have hp_odd : Odd p := by
    apply odd_of_dvd_odd h_odd hp_dvd
  have hn_ne : n ≠ 0 := by omega
  have ⟨e, K, he, h_not_dvd, h_eq⟩ := exists_eq_pow_mul_and_not_dvd hp_prime hn_ne hp_dvd
  have h_K_nz : K ≠ 0 := by
    intro h_zero
    subst h_zero
    simp at h_eq
    omega
  have hp_nz : p ≠ 0 := hp_prime.ne_zero
  have h_pe_nz : p ^ e ≠ 0 := pow_ne_zero e hp_nz
  have h_cop : (p ^ e).Coprime K := (Nat.Prime.coprime_pow_of_not_dvd hp_prime h_not_dvd).symm
  have h_S_eq : S n = S (p ^ e) * S K := by
    rw [h_eq]
    exact S_mul_of_coprime h_pe_nz h_K_nz h_cop
  by_cases h_K1 : K = 1
  · subst h_K1
    rw [mul_one] at h_eq
    rw [h_eq]
    exact Even_S_prime_pow_den hp_prime hp_odd e he
  · have h_K_gt_1 : K > 1 := by
      have : K ≥ 1 := Nat.pos_of_ne_zero h_K_nz
      omega
    have h_K_lt : K < n := by
      rw [h_eq]
      have h_pe_ge_3 : p ^ e ≥ 3 := by
        have h_pow_ge : p ^ e ≥ p := by
          have : p ^ 1 ≤ p ^ e := Nat.pow_le_pow_right hp_prime.pos he
          rwa [pow_one] at this
        have hp_ge_3 : p ≥ 3 := by
          have : p ≠ 2 := by
            rintro rfl
            norm_num at hp_odd
          have : p ≥ 2 := hp_prime.two_le
          omega
        omega
      have : K ≥ 1 := Nat.pos_of_ne_zero h_K_nz
      nlinarith
    have h_K_odd : Odd K := by
      rw [h_eq] at h_odd
      have : K ∣ p ^ e * K := by
        use p ^ e
        ring
      exact odd_of_dvd_odd h_odd this
    have h_K_even_den := ih K h_K_lt h_K_gt_1 h_K_odd
    rw [h_S_eq]
    exact den_mul_even (S (p ^ e)) (S K) (Even_S_prime_pow_den hp_prime hp_odd e he) h_K_even_den



/--
oeis_265710_conjecture_0: Are there numbers n > 1 such that Sum_{d|n} 1/sigma(d) is an integer?
This statement is equivalent to $\exists n > 1, a(n) = 1$.
-/
theorem oeis_265710_conjecture_0.disproof : ¬ ∃ n : ℕ, 1 < n ∧ a n = 1 := by
  rintro ⟨n, hn, ha⟩
  have h_S : (S n).den = 1 := ha
  have hn_ne : n ≠ 0 := by omega
  rcases eq_two_pow_or_exists_odd_prime_and_dvd n with ⟨k, rfl⟩ | ⟨p, hp_prime, hp_dvd, hp_odd⟩
  · have hk_ge_1 : k ≥ 1 := by
      by_contra hc
      have : k = 0 := by omega
      subst this
      simp at hn
    exact S_two_pow_den_ne_one k hk_ge_1 h_S
  · have ⟨e, K, he, h_not_dvd, h_eq⟩ := exists_eq_pow_mul_and_not_dvd hp_prime hn_ne hp_dvd
    have h_K_nz : K ≠ 0 := by
      intro h_zero
      subst h_zero
      simp at h_eq
      omega
    have hp_nz : p ≠ 0 := hp_prime.ne_zero
    have h_pe_nz : p ^ e ≠ 0 := pow_ne_zero e hp_nz
    have h_cop : (p ^ e).Coprime K := (Nat.Prime.coprime_pow_of_not_dvd hp_prime h_not_dvd).symm
    have h_S_eq : S n = S (p ^ e) * S K := by
      rw [h_eq]
      exact S_mul_of_coprime h_pe_nz h_K_nz h_cop
    have h_SK_even : Even (S K).num := by
      rw [h_S_eq] at h_S
      exact even_num_of_even_den_mul_int (S (p ^ e)) (S K) (Even_S_prime_pow_den hp_prime hp_odd e he) h_S
    by_cases h_K_odd : Odd K
    · have h_K_gt_1 : K > 1 := by
        by_contra hc
        have : K = 1 := by
          have : K ≥ 1 := Nat.pos_of_ne_zero h_K_nz
          omega
        subst this
        have h_S1 : S 1 = 1 := by
          unfold S
          simp
        rw [h_S1] at h_SK_even
        have : (1 : ℚ).num = 1 := rfl
        rw [this] at h_SK_even
        exact Int.not_even_one h_SK_even
      have h_K_even_den := Even_S_odd_den K h_K_gt_1 h_K_odd
      have hx : Even (S (p ^ e)).den := Even_S_prime_pow_den hp_prime hp_odd e he
      have h_even_n : Even (S (p ^ e) * S K).den := den_mul_even (S (p ^ e)) (S K) hx h_K_even_den
      rw [← h_S_eq] at h_even_n
      rw [h_S] at h_even_n
      exact Nat.not_even_one h_even_n
    · sorry

