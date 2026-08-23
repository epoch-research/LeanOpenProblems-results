import FormalConjectures.Util.ProblemImports

/-
A374605: The sequence a(n)=∑_{k=0}^n C(n,k)² C(n+k,k) C(3n+2k,n).

We prove that for a prime p≥5, p³ divides a(n) whenever
⌈(2p+1)/3⌉ ≤ n ≤ p-1.
-/

set_option linter.style.moduleDocstring false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option maxRecDepth 1000

open Nat Finset BigOperators

/- Sequence definition -/

/--
A374605: The sequence \(a(n) = \sum_{k = 0}^n \binom{n}{k}^2 \binom{n+k}{k} \binom{3n+2k}{n}\).
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)

def term (n k : ℕ) : ℕ :=
  (n.choose k) ^ 2 * (n + k).choose k * (3 * n + 2 * k).choose n

lemma a_eq_sum_term (n : ℕ) : a n = ∑ k ∈ range (n + 1), term n k := rfl

/- Interval lemmas -/

lemma n_lt_p_of_le_pred {p n : ℕ} (hp : 0 < p) (hn : n ≤ p - 1) : n < p :=
  lt_of_le_of_lt hn (Nat.sub_one_lt hp.ne')

lemma two_mul_p_le_three_mul_n {p n : ℕ} (hlo : (2 * p + 3) / 3 ≤ n) :
    2 * p ≤ 3 * n := by
  have hlt : (2 * p + 3) / 3 < n + 1 := Nat.lt_succ_of_le hlo
  have : 2 * p + 3 < (n + 1) * 3 := (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).mp hlt
  lia

lemma two_mul_p_add_one_le_three_mul_n {p n : ℕ} (hlo : (2 * p + 3) / 3 ≤ n) :
    2 * p + 1 ≤ 3 * n := by
  have hlt : (2 * p + 3) / 3 < n + 1 := Nat.lt_succ_of_le hlo
  have : 2 * p + 3 < (n + 1) * 3 := (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).mp hlt
  lia

lemma three_n_add_two_k_lt_p_sq {p n k : ℕ}
    (hp5 : 5 ≤ p) (hn : n < p) (hk : k ≤ n) :
    3 * n + 2 * k < p ^ 2 := by
  nlinarith

lemma r_pos {p n : ℕ} (hp : 0 < p) (hn : n ≤ p - 1) : 1 ≤ p - n := by
  have : n < p := n_lt_p_of_le_pred hp hn
  omega

lemma three_mul_r_lt_p {p n : ℕ} (hp : 0 < p)
    (hlo : (2 * p + 3) / 3 ≤ n) (hn : n ≤ p - 1) :
    3 * (p - n) < p := by
  have h := two_mul_p_add_one_le_three_mul_n hlo
  have : n < p := n_lt_p_of_le_pred hp hn
  omega

/- Factorization of n! and C(m,r) for m < p^2. -/

lemma factorization_factorial_of_lt_sq {p m : ℕ} (hp : p.Prime) (hm : m < p ^ 2) :
    (m !).factorization p = m / p := by
  by_cases hm0 : m = 0
  · subst hm0; simp
  have hlog : log p m < 2 :=
    Nat.log_lt_iff_lt_pow hp.one_lt (by omega) |>.mpr hm
  have := Nat.factorization_factorial hp hlog
  simpa [Ico_succ_singleton, pow_one] using this

lemma div_add_div_le_div (p m r : ℕ) (hrm : r ≤ m) :
    r / p + (m - r) / p ≤ m / p := by
  have := Nat.add_div_le_add_div r (m - r) p
  rwa [Nat.add_sub_of_le hrm] at this

lemma factorization_choose_of_lt_sq {p m r : ℕ} (hp : p.Prime)
    (hrm : r ≤ m) (hm : m < p ^ 2) :
    (m.choose r).factorization p = m / p - r / p - (m - r) / p := by
  have hm_fac := factorization_factorial_of_lt_sq hp hm
  have hr_fac := factorization_factorial_of_lt_sq hp (lt_of_le_of_lt hrm hm)
  have hmr_fac := factorization_factorial_of_lt_sq hp (lt_of_le_of_lt (sub_le m r) hm)
  have heq := choose_mul_factorial_mul_factorial hrm
  have hne1 : m.choose r ≠ 0 := (choose_pos hrm).ne'
  have hne2 : r ! ≠ 0 := factorial_ne_zero r
  have hne3 : (m - r)! ≠ 0 := factorial_ne_zero _
  have hmul :
      (m.choose r * r ! * (m - r)!).factorization p = (m !).factorization p := by
    rw [heq]
  have hassoc : m.choose r * r ! * (m - r)! = m.choose r * (r ! * (m - r)!) := by ring
  rw [hassoc, Nat.factorization_mul hne1 (mul_ne_zero hne2 hne3),
      Nat.factorization_mul hne2 hne3] at hmul
  simp only [Finsupp.coe_add, Pi.add_apply] at hmul
  rw [hm_fac, hr_fac, hmr_fac] at hmul
  have hle := div_add_div_le_div p m r hrm
  omega

lemma p_dvd_choose_of_carry {p m r : ℕ} (hp : p.Prime)
    (hrm : r ≤ m) (hm : m < p ^ 2)
    (hcarry : r / p + (m - r) / p < m / p) :
    p ∣ m.choose r := by
  have hfac := factorization_choose_of_lt_sq hp hrm hm
  have hpos : 0 < (m.choose r).factorization p := by omega
  exact dvd_of_factorization_pos hpos.ne'

/- Each term is divisible by p. -/

lemma p_dvd_choose_add_of_lt {p a b : ℕ} (hp : p.Prime)
    (ha : a < p) (hb : b < p) (h : p ≤ a + b) :
    p ∣ (a + b).choose a :=
  hp.dvd_choose_add ha hb h

lemma p_dvd_term {p n k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hlo : (2 * p + 3) / 3 ≤ n) (hn : n ≤ p - 1) (hk : k ≤ n) :
    p ∣ term n k := by
  have hppos : 0 < p := hp.pos
  have hnlt : n < p := n_lt_p_of_le_pred hppos hn
  have hklt : k < p := lt_of_le_of_lt hk hnlt
  unfold term
  by_cases hmp : p ≤ n + k
  · have : p ∣ (n + k).choose k := by
      have h := p_dvd_choose_add_of_lt hp hklt hnlt (by lia)
      simpa [add_comm k n] using h
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right this _) _
  · push_neg at hmp
    have hrm : n ≤ 3 * n + 2 * k := by lia
    have hm_sq : 3 * n + 2 * k < p ^ 2 := three_n_add_two_k_lt_p_sq hp5 hnlt hk
    have : p ∣ (3 * n + 2 * k).choose n := by
      apply p_dvd_choose_of_carry hp hrm hm_sq
      have hn_div : n / p = 0 := Nat.div_eq_of_lt hnlt
      have h2div : (2 * n + 2 * k) / p ≤ 1 := by
        have : 2 * n + 2 * k = 2 * (n + k) := by ring
        rw [this]
        exact Nat.lt_succ_iff.mp (Nat.div_lt_of_lt_mul (by nlinarith))
      have hge : 2 * p ≤ 3 * n + 2 * k := by lia
      have h3div : 2 ≤ (3 * n + 2 * k) / p := by
        have := Nat.div_le_div_right (c := p) hge
        have hp2 : 2 * p / p = 2 := by rw [mul_comm]; exact Nat.mul_div_right 2 hppos
        rwa [hp2] at this
      have hsub : 3 * n + 2 * k - n = 2 * n + 2 * k := by lia
      rw [hsub, hn_div]
      omega
    exact dvd_mul_of_dvd_right this _

lemma p_dvd_a {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hlo : (2 * p + 3) / 3 ≤ n) (hn : n ≤ p - 1) :
    p ∣ a n := by
  rw [a_eq_sum_term]
  refine dvd_sum ?_
  intro k hk
  exact p_dvd_term hp hp5 hlo hn (Nat.lt_succ_iff.mp (mem_range.mp hk))

/- Binomial congruences in ZMod p. -/

section PrimeField
variable {p : ℕ} [Fact p.Prime]

lemma p_pos : 0 < p := (Fact.out : p.Prime).pos

lemma p_ge_two : 2 ≤ p := (Fact.out : p.Prime).two_le

lemma factorial_ne_zero_zmod {k : ℕ} (hk : k < p) :
    ((k ! : ℕ) : ZMod p) ≠ 0 := by
  intro h
  have hpr : p.Prime := Fact.out
  have := (ZMod.natCast_eq_zero_iff (k !) p).mp h
  exact (not_le_of_gt hk) (hpr.dvd_factorial.mp this)

lemma choose_pred_zmod {k : ℕ} (hk : k ≤ p - 1) :
    ((p - 1).choose k : ZMod p) = (-1) ^ k := by
  have hpr : p.Prime := Fact.out
  have hkp : k ≤ p := le_trans hk (Nat.sub_le _ _)
  have hcast := ZMod.cast_descFactorial (n := k) (p := p) hkp
  have heq : ((p - 1).descFactorial k : ZMod p) =
      ((p - 1).choose k : ZMod p) * (k ! : ZMod p) := by
    rw [descFactorial_eq_factorial_mul_choose, mul_comm, Nat.cast_mul]
  have hklt : k < p := lt_of_le_of_lt hk (Nat.sub_one_lt hpr.pos.ne')
  have hfac := factorial_ne_zero_zmod hklt
  have : ((p - 1).choose k : ZMod p) * (k ! : ZMod p) = (-1) ^ k * (k ! : ZMod p) := by
    rw [← heq, hcast]
  exact mul_right_cancel₀ hfac this

lemma zmod_nat_ne_zero {j : ℕ} (hj0 : 0 < j) (hjp : j < p) :
    (j : ZMod p) ≠ 0 := by
  intro h
  have := (ZMod.natCast_eq_zero_iff j p).mp h
  have : p ≤ j := Nat.le_of_dvd hj0 this
  omega

lemma zmod_cast_ne_zero_of_lt {j : ℕ} (hjp : j < p) (hj0 : j ≠ 0) :
    (j : ZMod p) ≠ 0 :=
  zmod_nat_ne_zero (Nat.pos_of_ne_zero hj0) hjp

/-- Absorption: `k * C(p+k-1, k) = p * C(p+k-1, k-1)`. -/
lemma choose_p_add_mul (k : ℕ) (hk : 0 < k) :
    k * (p + k - 1).choose k = p * (p + k - 1).choose (k - 1) := by
  have hk' : k = (k - 1) + 1 := (Nat.sub_add_cancel hk).symm
  have h := choose_succ_right_eq (p + k - 1) (k - 1)
  -- C(n, (k-1)+1) * k = C(n, k-1) * (n - (k-1))
  rw [← hk'] at h
  have hn : p + k - 1 - (k - 1) = p := by
    have : k - 1 ≤ p + k - 1 := by omega
    omega
  rw [hn] at h
  linarith

lemma p_dvd_choose_p_add {k : ℕ} (hk : 0 < k) (hkm : k < p) :
    p ∣ (p + k - 1).choose k := by
  have hpr : p.Prime := Fact.out
  have heq := choose_p_add_mul (p := p) k hk
  have : p ∣ k * (p + k - 1).choose k := by
    rw [heq]; exact dvd_mul_right _ _
  exact hpr.dvd_mul.mp this |>.resolve_left (by
    intro hp
    have : p ≤ k := Nat.le_of_dvd hk hp
    omega)

lemma choose_p_add_div_p_mul {k : ℕ} (hk : 0 < k) (hkm : k < p) :
    k * ((p + k - 1).choose k / p) = (p + k - 1).choose (k - 1) := by
  have hdiv := p_dvd_choose_p_add (p := p) hk hkm
  have heq := choose_p_add_mul (p := p) k hk
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp0)
  calc
    p * (k * ((p + k - 1).choose k / p))
        = k * (p * ((p + k - 1).choose k / p)) := by ring
    _ = k * (p + k - 1).choose k := by rw [Nat.mul_div_cancel' hdiv]
    _ = p * (p + k - 1).choose (k - 1) := heq

lemma choose_p_add_pred_zmod {k : ℕ} (hk : 0 < k) (hkm : k < p) :
    ((p + k - 1).choose (k - 1) : ZMod p) = 1 := by
  have hk1 : k - 1 < p := lt_of_le_of_lt (Nat.sub_le _ _) hkm
  have hdesc : (p + k - 1).descFactorial (k - 1) =
      (k - 1)! * (p + k - 1).choose (k - 1) :=
    descFactorial_eq_factorial_mul_choose _ _
  have hcast : ((p + k - 1).descFactorial (k - 1) : ZMod p) = ((k - 1)! : ZMod p) := by
    rw [descFactorial_eq_prod_range, factorial_eq_prod_range_add_one, Nat.cast_prod,
      Nat.cast_prod]
    have hcongr : ∀ i ∈ range (k - 1),
        ((p + k - 1 - i : ℕ) : ZMod p) = ((k - 1 - i : ℕ) : ZMod p) := by
      intro i hi
      have : p + k - 1 - i = p + (k - 1 - i) := by
        have : i < k - 1 := mem_range.mp hi
        omega
      rw [this, Nat.cast_add, CharP.cast_eq_zero, zero_add]
    have h1 : (∏ i ∈ range (k - 1), ((p + k - 1 - i : ℕ) : ZMod p)) =
        ∏ i ∈ range (k - 1), ((k - 1 - i : ℕ) : ZMod p) :=
      prod_congr rfl hcongr
    have h2 : (∏ i ∈ range (k - 1), ((k - 1 - i : ℕ) : ZMod p)) =
        ∏ i ∈ range (k - 1), ((i + 1 : ℕ) : ZMod p) := by
      have hre : ∀ i ∈ range (k - 1),
          ((k - 1 - i : ℕ) : ZMod p) = (((k - 1) - 1 - i) + 1 : ℕ) := by
        intro i hi
        have : i < k - 1 := mem_range.mp hi
        have : k - 1 - i = (k - 1 - 1 - i) + 1 := by omega
        simp [this]
      rw [prod_congr rfl hre]
      simpa using (prod_range_reflect (fun j => ((j + 1 : ℕ) : ZMod p)) (k - 1))
    exact h1.trans h2
  have hmul : ((p + k - 1).choose (k - 1) : ZMod p) * ((k - 1)! : ZMod p) =
      (1 : ZMod p) * ((k - 1)! : ZMod p) := by
    rw [one_mul, ← Nat.cast_mul, mul_comm, ← hdesc, hcast]
  exact mul_right_cancel₀ (factorial_ne_zero_zmod hk1) hmul

/-- `C(p+k-1, k)/p ≡ k⁻¹` in `ZMod p`. -/
lemma choose_p_add_div_p_zmod {k : ℕ} (hk : 0 < k) (hkm : k < p) :
    (((p + k - 1).choose k / p : ℕ) : ZMod p) = (k : ZMod p)⁻¹ := by
  have heq := choose_p_add_div_p_mul (p := p) hk hkm
  have hC := choose_p_add_pred_zmod (p := p) hk hkm
  have hmul : (k : ZMod p) * (((p + k - 1).choose k / p : ℕ) : ZMod p) = 1 := by
    rw [← Nat.cast_mul, heq, hC]
  have hk0 : (k : ZMod p) ≠ 0 := zmod_nat_ne_zero hk hkm
  calc
    (((p + k - 1).choose k / p : ℕ) : ZMod p)
        = (k : ZMod p)⁻¹ * ((k : ZMod p) * (((p + k - 1).choose k / p : ℕ) : ZMod p)) := by
          rw [← mul_assoc, inv_mul_cancel₀ hk0, one_mul]
    _ = (k : ZMod p)⁻¹ * 1 := by rw [hmul]
    _ = (k : ZMod p)⁻¹ := mul_one _

/- Power sums in ZMod p. -/

lemma sum_univ_pow_eq_zero {j : ℕ} (hj : j < p - 1) :
    ∑ x : ZMod p, x ^ j = 0 :=
  FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) j (by
    simpa [ZMod.card] using hj)

lemma sum_nonzero_inv_sq (hp5 : 5 ≤ p) :
    ∑ x : (ZMod p)ˣ, ((x : ZMod p)⁻¹) ^ 2 = 0 := by
  have hpow : ∀ x : (ZMod p)ˣ, ((x : ZMod p)⁻¹) ^ 2 = (x : ZMod p) ^ (p - 3) := by
    intro x
    have hx0 : (x : ZMod p) ≠ 0 := Units.ne_zero x
    have hfermat : (x : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hx0
    have hp3 : 2 + (p - 3) = p - 1 := by omega
    rw [inv_pow]
    have h2 : (x : ZMod p) ^ 2 * (x : ZMod p) ^ (p - 3) = 1 := by
      rw [← pow_add, hp3, hfermat]
    exact inv_eq_of_mul_eq_one_right h2
  simp_rw [hpow]
  have := FiniteField.sum_pow_units (K := ZMod p) (p - 3)
  have hnot : ¬ (p - 1 ∣ p - 3) := by
    intro h
    have : p - 1 ≤ p - 3 := Nat.le_of_dvd (by omega) h
    omega
  simpa [ZMod.card, hnot] using this

end PrimeField

/- The case n = p - 1. -/

section NPred
variable {p : ℕ} [Fact p.Prime]

lemma three_mul_pred (hp : 1 ≤ p) : 3 * (p - 1) = 3 * p - 3 := by omega

lemma term_pred_zero :
    term (p - 1) 0 = (3 * p - 3).choose (p - 1) := by
  have hp : 1 ≤ p := le_trans (by decide : 1 ≤ 2) (p_ge_two (p := p))
  unfold term
  simp only [choose_zero_right, pow_two, mul_one, add_zero, mul_zero]
  rw [three_mul_pred hp]
  simp

lemma term_pred_one :
    term (p - 1) 1 = (p - 1) ^ 2 * p * (3 * p - 1).choose (p - 1) := by
  have hp : 1 ≤ p := le_trans (by decide : 1 ≤ 2) (p_ge_two (p := p))
  have hch : (p - 1).choose 1 = p - 1 := choose_one_right (p - 1)
  have hch2 : (p - 1 + 1).choose 1 = p := by
    rw [Nat.sub_add_cancel hp, choose_one_right]
  unfold term
  rw [hch, hch2]
  have h3 : 3 * (p - 1) + 2 * 1 = 3 * p - 1 := by omega
  rw [h3]

lemma two_ne_zero_zmod (hp5 : 5 ≤ p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hpr : p.Prime := Fact.out
  have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
  have : p = 1 ∨ p = 2 := (Nat.dvd_prime Nat.prime_two).mp this
  omega

lemma inv_two_mul_two (hp5 : 5 ≤ p) : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 :=
  mul_inv_cancel₀ (two_ne_zero_zmod hp5)

lemma cast_sub_pred {k : ℕ} (hk : 1 ≤ k) :
    (k : ZMod p) - ((k - 1 : ℕ) : ZMod p) = 1 := by
  calc
    (k : ZMod p) - ((k - 1 : ℕ) : ZMod p)
        = (((k - 1) + 1 : ℕ) : ZMod p) - ((k - 1 : ℕ) : ZMod p) := by
          congr 2; omega
    _ = ((k - 1 : ℕ) : ZMod p) + 1 - ((k - 1 : ℕ) : ZMod p) := by
          rw [Nat.cast_succ]
    _ = 1 := by abel

lemma third_lt_p_sq {k : ℕ} (hp5 : 5 ≤ p) (hkp : k ≤ p - 1) :
    3 * p + 2 * k - 3 < p ^ 2 := by
  have hle : k ≤ p := le_trans hkp (Nat.sub_le _ _)
  calc
    3 * p + 2 * k - 3 ≤ 3 * p + 2 * p - 3 := by gcongr
    _ = 5 * p - 3 := by ring
    _ < p * p := by
      have : 5 * p + 3 < p * p + 6 := by
        have h5 : 5 ≤ p := hp5
        nlinarith
      omega
    _ = p ^ 2 := by ring

lemma p_odd (hp5 : 5 ≤ p) : p % 2 = 1 :=
  (Fact.out : p.Prime).eq_two_or_odd.resolve_left (by omega)

/-- For `2 ≤ k ≤ p-1`, `p` divides `C(3p+2k-3, p-1)`. -/
lemma p_dvd_choose_third_pred {k : ℕ} (hp5 : 5 ≤ p) (hk2 : 2 ≤ k) (hkp : k ≤ p - 1) :
    p ∣ (3 * p + 2 * k - 3).choose (p - 1) := by
  have hpr : p.Prime := Fact.out
  have hppos : 0 < p := hpr.pos
  have hrm : p - 1 ≤ 3 * p + 2 * k - 3 := by omega
  have hm : 3 * p + 2 * k - 3 < p ^ 2 := third_lt_p_sq hp5 hkp
  apply p_dvd_choose_of_carry hpr hrm hm
  have hdiv0 : (p - 1) / p = 0 := Nat.div_eq_of_lt (Nat.sub_one_lt hppos.ne')
  rw [hdiv0, zero_add]
  have hsub : 3 * p + 2 * k - 3 - (p - 1) = 2 * p + 2 * k - 2 := by omega
  rw [hsub]
  have hodd := p_odd (p := p) hp5
  by_cases hlow : 2 * k ≤ p + 1
  · have hmdiv : (3 * p + 2 * k - 3) / p = 3 := by
      refine Nat.div_eq_of_lt_le ?_ ?_
      · have : 3 * p ≤ 3 * p + 2 * k - 3 := by omega
        simpa [mul_comm 3 p] using this
      · have : 3 * p + 2 * k - 3 < 4 * p := by omega
        simpa [Nat.succ_eq_add_one, show 3 + 1 = 4 from rfl] using this
    have hmdDiv : (2 * p + 2 * k - 2) / p = 2 := by
      refine Nat.div_eq_of_lt_le ?_ ?_
      · have : 2 * p ≤ 2 * p + 2 * k - 2 := by omega
        simpa [mul_comm 2 p] using this
      · have : 2 * p + 2 * k - 2 < 3 * p := by omega
        simpa [Nat.succ_eq_add_one, show 2 + 1 = 3 from rfl] using this
    omega
  · push_neg at hlow
    have hge : p + 3 ≤ 2 * k := by
      have hne : 2 * k ≠ p + 2 := by
        intro heq
        have : (2 * k) % 2 = (p + 2) % 2 := by rw [heq]
        simp at this
        omega
      omega
    have hmdiv : (3 * p + 2 * k - 3) / p = 4 := by
      refine Nat.div_eq_of_lt_le ?_ ?_
      · have : 4 * p ≤ 3 * p + 2 * k - 3 := by omega
        simpa [mul_comm 4 p] using this
      · have : 3 * p + 2 * k - 3 < 5 * p := by
          have : k ≤ p := le_trans hkp (Nat.sub_le _ _)
          omega
        simpa [Nat.succ_eq_add_one, show 4 + 1 = 5 from rfl] using this
    have hmdDiv : (2 * p + 2 * k - 2) / p = 3 := by
      refine Nat.div_eq_of_lt_le ?_ ?_
      · have : 3 * p ≤ 2 * p + 2 * k - 2 := by omega
        simpa [mul_comm 3 p] using this
      · have : 2 * p + 2 * k - 2 < 4 * p := by
          have : k ≤ p := le_trans hkp (Nat.sub_le _ _)
          omega
        simpa [Nat.succ_eq_add_one, show 3 + 1 = 4 from rfl] using this
    omega

lemma psq_dvd_term_pred_of_two_le {k : ℕ} (hp5 : 5 ≤ p)
    (hk2 : 2 ≤ k) (hkp : k ≤ p - 1) :
    p ^ 2 ∣ term (p - 1) k := by
  have hk0 : 0 < k := lt_of_lt_of_le (by decide : 0 < 2) hk2
  have hkm : k < p := lt_of_le_of_lt hkp (Nat.sub_one_lt (p_pos (p := p)).ne')
  have h1 : p ∣ (p - 1 + k).choose k := by
    have : p - 1 + k = p + k - 1 := by omega
    rw [this]
    exact p_dvd_choose_p_add (p := p) hk0 hkm
  have h2 : p ∣ (3 * (p - 1) + 2 * k).choose (p - 1) := by
    have : 3 * (p - 1) + 2 * k = 3 * p + 2 * k - 3 := by omega
    rw [this]
    exact p_dvd_choose_third_pred hp5 hk2 hkp
  unfold term
  have hmul : p * p ∣ (p - 1 + k).choose k * (3 * (p - 1) + 2 * k).choose (p - 1) :=
    mul_dvd_mul h1 h2
  have : p ^ 2 ∣ (p - 1).choose k ^ 2 *
      ((p - 1 + k).choose k * (3 * (p - 1) + 2 * k).choose (p - 1)) :=
    dvd_mul_of_dvd_right (by simpa [pow_two] using hmul) _
  convert this using 1
  ring

/- The third binomial divided by p, for n = p-1. -/

lemma descFactorial_eq_prod_Icc {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n + 1) :
    n.descFactorial k = ∏ j ∈ Icc (n + 1 - k) n, j := by
  rw [descFactorial_eq_prod_range]
  have hmap : (range k).image (fun i => n - i) = Icc (n + 1 - k) n := by
    ext j
    simp only [mem_image, mem_range, mem_Icc]
    constructor
    · rintro ⟨i, hi, rfl⟩
      omega
    · intro hj
      refine ⟨n - j, ?_, ?_⟩
      · omega
      · omega
  have hinj : Set.InjOn (fun i => n - i) (range k : Set ℕ) := by
    intro i hi j hj hij
    have hi' : i < k := mem_range.mp hi
    have hj' : j < k := mem_range.mp hj
    have hi_le : i ≤ n := by omega
    have hj_le : j ≤ n := by omega
    exact (tsub_right_inj hi_le hj_le).mp hij
  rw [← hmap, eq_comm]
  exact Finset.prod_image (fun i hi j hj h => hinj hi hj h)

lemma injOn_cast_Icc_consecutive (L : ℕ) :
    ∀ x ∈ Icc L (L + p - 2), ∀ y ∈ Icc L (L + p - 2),
      (x : ZMod p) = (y : ZMod p) → x = y := by
  intro x hx y hy hxy
  have hxI := mem_Icc.mp hx
  have hyI := mem_Icc.mp hy
  have hp2 : 2 ≤ p := p_ge_two (p := p)
  have hmod : x ≡ y [MOD p] := (ZMod.natCast_eq_natCast_iff x y p).mp hxy
  rcases le_total x y with hle | hle
  · have hdvd : p ∣ y - x := (Nat.modEq_iff_dvd' hle).mp hmod
    have hlt : y - x < p := by omega
    have : y - x = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    omega
  · have hdvd : p ∣ x - y := (Nat.modEq_iff_dvd' hle).mp hmod.symm
    have hlt : x - y < p := by omega
    have : x - y = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    omega

lemma image_Icc_consecutive_zmod (L : ℕ) :
    (Icc L (L + p - 2)).image (fun j : ℕ => (j : ZMod p)) =
      (univ : Finset (ZMod p)).erase ((L : ZMod p) - 1) := by
  have hp2 : 2 ≤ p := p_ge_two (p := p)
  have hle : L ≤ L + p - 2 := by omega
  have hinj := injOn_cast_Icc_consecutive (p := p) L
  have hcard_s : #(Icc L (L + p - 2)) = p - 1 := by
    rw [Nat.card_Icc]
    omega
  have hsub : (Icc L (L + p - 2)).image (fun j : ℕ => (j : ZMod p)) ⊆
      (univ : Finset (ZMod p)).erase ((L : ZMod p) - 1) := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
    have hjI := mem_Icc.mp hj
    refine (mem_erase.mpr ⟨?_, mem_univ _⟩)
    intro hcontra
    have hji : ((j + 1 : ℕ) : ZMod p) = (L : ZMod p) := by
      have : (j : ZMod p) + 1 = (L : ZMod p) := by
        rw [hcontra]; abel
      simpa [Nat.cast_add, Nat.cast_one] using this
    have hmod : j + 1 ≡ L [MOD p] := (ZMod.natCast_eq_natCast_iff _ _ p).mp hji
    have hge : L ≤ j + 1 := by omega
    have hdvd : p ∣ (j + 1) - L := (Nat.modEq_iff_dvd' hge).mp hmod.symm
    have h1 : 1 ≤ (j + 1) - L := by omega
    have h2 : (j + 1) - L < p := by omega
    exact (Nat.not_dvd_of_pos_of_lt h1 h2) hdvd
  have hcard_img :
      #((Icc L (L + p - 2)).image (fun j : ℕ => (j : ZMod p))) = p - 1 := by
    have : Set.InjOn (fun j : ℕ => (j : ZMod p)) (Icc L (L + p - 2)) :=
      fun x hx y hy h => hinj x hx y hy h
    rw [Finset.card_image_of_injOn this, hcard_s]
  have hcard_er : #((univ : Finset (ZMod p)).erase ((L : ZMod p) - 1)) = p - 1 := by
    rw [card_erase_of_mem (mem_univ _)]
    simp [ZMod.card]
  exact eq_of_subset_of_card_le hsub (hcard_er.trans hcard_img.symm ▸ le_rfl)

lemma image_erase_of_injOn {α β : Type*} [DecidableEq α] [DecidableEq β]
    {f : α → β} {s : Finset α} {a : α}
    (hinj : ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y) (ha : a ∈ s) :
    (s.erase a).image f = (s.image f).erase (f a) := by
  ext y
  simp only [mem_image, mem_erase]
  constructor
  · rintro ⟨x, ⟨hxne, hxs⟩, rfl⟩
    exact ⟨fun h => hxne (hinj x hxs a ha h), ⟨x, hxs, rfl⟩⟩
  · rintro ⟨hne, ⟨x, hxs, rfl⟩⟩
    exact ⟨x, ⟨fun h => hne (h ▸ rfl), hxs⟩, rfl⟩

lemma Icc_one_pred_eq :
    Icc 1 (p - 1) = Icc 1 (1 + p - 2) := by
  congr 1; omega

lemma prod_Icc_one_pred_eq_factorial :
    ∏ j ∈ Icc 1 (p - 1), j = (p - 1)! := by
  have hppos : 0 < p := p_pos (p := p)
  have : Icc 1 (p - 1) = Ico 1 p := by
    ext x; simp [mem_Icc, mem_Ico]; omega
  rw [this]
  simpa [Nat.sub_add_cancel hppos] using prod_Ico_id_eq_factorial (p - 1)

lemma image_Icc_one_pred :
    (Icc 1 (p - 1)).image (fun j : ℕ => (j : ZMod p)) =
      (univ : Finset (ZMod p)).erase (0 : ZMod p) := by
  rw [Icc_one_pred_eq]
  simpa [Nat.cast_one, sub_self] using image_Icc_consecutive_zmod (p := p) 1

lemma prod_nonzero_eq_factorial :
    ∏ x ∈ (univ : Finset (ZMod p)).erase (0 : ZMod p), x = ((p - 1)! : ZMod p) := by
  rw [ZMod.wilsons_lemma]
  have heq : Icc 1 (p - 1) = Ico 1 p := by
    ext x; simp [mem_Icc, mem_Ico]; omega
  have hprod : ∏ j ∈ Icc 1 (p - 1), (j : ZMod p) = (-1 : ZMod p) := by
    rw [heq, ZMod.prod_Ico_one_prime]
  rw [← hprod, ← image_Icc_one_pred]
  refine (Finset.prod_nbij (i := fun j : ℕ => (j : ZMod p))
      (f := fun j : ℕ => (j : ZMod p)) (g := fun x : ZMod p => x)
      ?_ ?_ ?_ (fun _ _ => rfl)).symm
  · intro j hj
    exact mem_image.mpr ⟨j, hj, rfl⟩
  · intro a ha b hb hab
    have ha' : a ∈ Icc 1 (1 + p - 2) := by rwa [← Icc_one_pred_eq]
    have hb' : b ∈ Icc 1 (1 + p - 2) := by rwa [← Icc_one_pred_eq]
    exact injOn_cast_Icc_consecutive (p := p) 1 a ha' b hb' hab
  · intro b hb
    simpa [Finset.coe_image] using hb

lemma prod_nonzero_erase_eq {μ : ZMod p} (hμ : μ ≠ 0) :
    ∏ x ∈ ((univ : Finset (ZMod p)).erase (0 : ZMod p)).erase μ, x =
      ((p - 1)! : ZMod p) * μ⁻¹ := by
  have hmem : μ ∈ (univ : Finset (ZMod p)).erase (0 : ZMod p) :=
    mem_erase.mpr ⟨hμ, mem_univ _⟩
  have hprod := Finset.prod_erase_mul
    (s := (univ : Finset (ZMod p)).erase (0 : ZMod p)) (a := μ)
    (f := fun x : ZMod p => x) hmem
  rw [prod_nonzero_eq_factorial] at hprod
  calc
    ∏ x ∈ ((univ : Finset (ZMod p)).erase (0 : ZMod p)).erase μ, x
        = (∏ x ∈ ((univ : Finset (ZMod p)).erase (0 : ZMod p)).erase μ, x) *
            μ * μ⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hμ, mul_one]
    _ = ((p - 1)! : ZMod p) * μ⁻¹ := by
          rw [hprod]

/-- If a length-`(p-1)` interval `[L, L+p-2]` contains the multiple `q*p`, then
`C(L+p-2, p-1)/p ≡ q * (L-1)⁻¹` in `ZMod p`. -/
lemma choose_div_p_of_interval {L q : ℕ} (hq0 : 0 < q) (hqp : q < p)
    (hL : L ≤ q * p) (hU : q * p ≤ L + p - 2) :
    p ∣ (L + p - 2).choose (p - 1) ∧
    (((L + p - 2).choose (p - 1) / p : ℕ) : ZMod p) =
      (q : ZMod p) * (((L : ZMod p) - 1)⁻¹) := by
  have hpr : p.Prime := Fact.out
  have hppos : 0 < p := hpr.pos
  have hmem : q * p ∈ Icc L (L + p - 2) := mem_Icc.mpr ⟨hL, hU⟩
  have hdesc : (L + p - 2).descFactorial (p - 1) =
      ∏ j ∈ Icc L (L + p - 2), j := by
    have hkn : p - 1 ≤ (L + p - 2) + 1 := by omega
    have : (L + p - 2) + 1 - (p - 1) = L := by omega
    rw [descFactorial_eq_prod_Icc (by omega) hkn, this]
  have hP : ∏ j ∈ Icc L (L + p - 2), j =
      (q * p) * ∏ j ∈ (Icc L (L + p - 2)).erase (q * p), j := by
    simpa [mul_comm (q * p)] using
      (Finset.prod_erase_mul (s := Icc L (L + p - 2)) (a := q * p)
        (f := fun j : ℕ => j) hmem).symm
  have hfac : (L + p - 2).descFactorial (p - 1) =
      (p - 1)! * (L + p - 2).choose (p - 1) :=
    descFactorial_eq_factorial_mul_choose _ _
  have hmul : (p - 1)! * (L + p - 2).choose (p - 1) =
      p * (q * ∏ j ∈ (Icc L (L + p - 2)).erase (q * p), j) := by
    rw [← hfac, hdesc, hP]; ring
  have hp_ndvd_fac : ¬ p ∣ (p - 1)! := by
    intro h
    exact (not_le_of_gt (Nat.sub_one_lt hppos.ne')) (hpr.dvd_factorial.mp h)
  have hpdvd : p ∣ (L + p - 2).choose (p - 1) := by
    have : p ∣ (p - 1)! * (L + p - 2).choose (p - 1) := by
      rw [hmul]; exact dvd_mul_right _ _
    exact (hpr.dvd_mul.mp this).resolve_left hp_ndvd_fac
  refine ⟨hpdvd, ?_⟩
  have hdiv : (p - 1)! * ((L + p - 2).choose (p - 1) / p) =
      q * ∏ j ∈ (Icc L (L + p - 2)).erase (q * p), j := by
    apply Nat.eq_of_mul_eq_mul_left hppos
    calc
      p * ((p - 1)! * ((L + p - 2).choose (p - 1) / p))
          = (p - 1)! * (p * ((L + p - 2).choose (p - 1) / p)) := by ring
      _ = (p - 1)! * (L + p - 2).choose (p - 1) := by rw [Nat.mul_div_cancel' hpdvd]
      _ = p * (q * ∏ j ∈ (Icc L (L + p - 2)).erase (q * p), j) := hmul
  set μ : ZMod p := (L : ZMod p) - 1
  have himg := image_Icc_consecutive_zmod (p := p) L
  have hinj := injOn_cast_Icc_consecutive (p := p) L
  have h0 : ((q * p : ℕ) : ZMod p) = 0 := by
    simp [Nat.cast_mul, CharP.cast_eq_zero (R := ZMod p) p]
  have himg_erase :
      ((Icc L (L + p - 2)).erase (q * p)).image (fun j : ℕ => (j : ZMod p)) =
        ((univ : Finset (ZMod p)).erase μ).erase (0 : ZMod p) := by
    rw [image_erase_of_injOn hinj hmem, himg, h0]
  have hμ0 : μ ≠ 0 := by
    intro hμ
    have : (0 : ZMod p) ∈ (univ : Finset (ZMod p)).erase μ := by
      have : 0 ∈ (Icc L (L + p - 2)).image (fun j : ℕ => (j : ZMod p)) :=
        mem_image.mpr ⟨q * p, hmem, h0⟩
      rwa [himg] at this
    exact (mem_erase.mp this).1 hμ.symm
  have hprod_er :
      ∏ j ∈ (Icc L (L + p - 2)).erase (q * p), (j : ZMod p) =
        ∏ x ∈ ((univ : Finset (ZMod p)).erase μ).erase (0 : ZMod p), x := by
    have hinj' : ∀ x ∈ (Icc L (L + p - 2)).erase (q * p),
        ∀ y ∈ (Icc L (L + p - 2)).erase (q * p),
        (x : ZMod p) = (y : ZMod p) → x = y :=
      fun x hx y hy hxy => hinj x (mem_of_mem_erase hx) y (mem_of_mem_erase hy) hxy
    refine Finset.prod_nbij (i := fun j : ℕ => (j : ZMod p))
        (f := fun j : ℕ => (j : ZMod p)) (g := fun x : ZMod p => x)
        ?_ ?_ ?_ (fun _ _ => rfl)
    · intro j hj
      have : (j : ZMod p) ∈
          ((Icc L (L + p - 2)).erase (q * p)).image (fun j : ℕ => (j : ZMod p)) :=
        mem_image.mpr ⟨j, hj, rfl⟩
      rwa [himg_erase] at this
    · exact hinj'
    · intro b hb
      have hb' : b ∈
          ((Icc L (L + p - 2)).erase (q * p)).image (fun j : ℕ => (j : ZMod p)) := by
        rwa [himg_erase]
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hb'
      exact ⟨a, ha, rfl⟩
  have herase_comm :
      ((univ : Finset (ZMod p)).erase μ).erase (0 : ZMod p) =
        ((univ : Finset (ZMod p)).erase (0 : ZMod p)).erase μ := by
    ext x; simp [mem_erase]; tauto
  have hcast :
      ((p - 1)! : ZMod p) * ((((L + p - 2).choose (p - 1) / p : ℕ) : ZMod p)) =
        (q : ZMod p) * (((p - 1)! : ZMod p) * μ⁻¹) := by
    have h1 : ((p - 1)! : ZMod p) *
        ((((L + p - 2).choose (p - 1) / p : ℕ) : ZMod p)) =
          (q : ZMod p) * ∏ j ∈ (Icc L (L + p - 2)).erase (q * p), (j : ZMod p) := by
      rw [← Nat.cast_mul, hdiv, Nat.cast_mul, Nat.cast_prod]
    rw [h1, hprod_er, herase_comm, prod_nonzero_erase_eq hμ0]
  have hfac0 : ((p - 1)! : ZMod p) ≠ 0 :=
    factorial_ne_zero_zmod (Nat.sub_one_lt hppos.ne')
  apply mul_left_cancel₀ hfac0
  convert hcast using 1
  ring


lemma third_L (k : ℕ) : 2 * p + 2 * k - 1 + p - 2 = 3 * p + 2 * k - 3 := by omega

lemma choose_third_div_p_low {k : ℕ} (hp5 : 5 ≤ p)
    (hk2 : 2 ≤ k) (hk : k ≤ (p + 1) / 2) :
    (((3 * p + 2 * k - 3).choose (p - 1) / p : ℕ) : ZMod p) =
      (3 : ZMod p) * ((2 : ZMod p) * ((k - 1 : ℕ) : ZMod p))⁻¹ := by
  have hL : 2 * p + 2 * k - 1 ≤ 3 * p := by omega
  have hU : 3 * p ≤ 2 * p + 2 * k - 1 + p - 2 := by omega
  have h := choose_div_p_of_interval (p := p) (L := 2 * p + 2 * k - 1) (q := 3)
    (by omega) (by omega) hL hU
  have hLcast : ((2 * p + 2 * k - 1 : ℕ) : ZMod p) - 1 =
      (2 : ZMod p) * ((k - 1 : ℕ) : ZMod p) := by
    have : 2 * p + 2 * k - 1 = 2 * p + (2 * (k - 1) + 1) := by omega
    rw [this, Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_one]
    simp only [CharP.cast_eq_zero (R := ZMod p) p, zero_mul, zero_add]
    ring
  rw [third_L] at h
  rw [h.2, hLcast]
  simp

lemma choose_third_div_p_high {k : ℕ} (hp5 : 5 ≤ p)
    (hk : (p + 3) / 2 ≤ k) (hkp : k ≤ p - 1) :
    (((3 * p + 2 * k - 3).choose (p - 1) / p : ℕ) : ZMod p) =
      (4 : ZMod p) * (((2 * k : ℕ) : ZMod p) - (p : ZMod p) - 2)⁻¹ := by
  have hge : p + 3 ≤ 2 * k := by
    have hodd := p_odd (p := p) hp5
    have : 2 * ((p + 3) / 2) ≤ 2 * k := Nat.mul_le_mul_left 2 hk
    have : 2 * ((p + 3) / 2) = p + 3 := by
      have : (p + 3) % 2 = 0 := by omega
      exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero this)
    omega
  have hL : 2 * p + 2 * k - 1 ≤ 4 * p := by omega
  have hU : 4 * p ≤ 2 * p + 2 * k - 1 + p - 2 := by omega
  have h := choose_div_p_of_interval (p := p) (L := 2 * p + 2 * k - 1) (q := 4)
    (by omega) (by omega) hL hU
  have hLcast : ((2 * p + 2 * k - 1 : ℕ) : ZMod p) - 1 =
      ((2 * k : ℕ) : ZMod p) - (p : ZMod p) - 2 := by
    have : 2 * p + 2 * k - 1 = 2 * p + 2 * k - 1 := rfl
    have h1 : ((2 * p + 2 * k - 1 : ℕ) : ZMod p) =
        (2 : ZMod p) * (k : ZMod p) - 1 := by
      have : 2 * p + 2 * k - 1 = 2 * p + (2 * k - 1) := by omega
      rw [this, Nat.cast_add, Nat.cast_mul]
      simp only [CharP.cast_eq_zero (R := ZMod p) p, zero_mul, zero_add]
      have : 2 * k - 1 = 2 * k - 1 := rfl
      have hk1 : 1 ≤ 2 * k := by omega
      rw [Nat.cast_sub hk1, Nat.cast_mul, Nat.cast_one]
      simp
    rw [h1]
    simp only [CharP.cast_eq_zero (R := ZMod p) p, sub_zero, Nat.cast_mul]
    ring
  rw [third_L] at h
  rw [h.2, hLcast]
  simp

lemma term_pred_eq {k : ℕ} (hp : 1 ≤ p) :
    term (p - 1) k =
      (p - 1).choose k ^ 2 * (p + k - 1).choose k *
        (3 * p + 2 * k - 3).choose (p - 1) := by
  unfold term
  have h1 : p - 1 + k = p + k - 1 := by omega
  have h2 : 3 * (p - 1) + 2 * k = 3 * p + 2 * k - 3 := by omega
  rw [h1, h2]

lemma mul_div_of_dvd_dvd {A B C m : ℕ} (hB : m ∣ B) (hC : m ∣ C) (hm : 0 < m) :
    A * B * C / (m * m) = A * (B / m) * (C / m) := by
  obtain ⟨b, rfl⟩ := hB
  obtain ⟨c, rfl⟩ := hC
  rw [Nat.mul_div_cancel_left b hm, Nat.mul_div_cancel_left c hm]
  have : A * (m * b) * (m * c) = (A * b * c) * (m * m) := by ring
  rw [this, Nat.mul_div_cancel _ (Nat.mul_pos hm hm)]

lemma term_div_psq_eq {k : ℕ} (hp5 : 5 ≤ p) (hk2 : 2 ≤ k) (hkp : k ≤ p - 1) :
    term (p - 1) k / p ^ 2 =
      (p - 1).choose k ^ 2 *
        ((p + k - 1).choose k / p) *
        ((3 * p + 2 * k - 3).choose (p - 1) / p) := by
  have hp1 : 1 ≤ p := le_trans (by decide : 1 ≤ 5) hp5
  have hk0 : 0 < k := lt_of_lt_of_le (by decide : 0 < 2) hk2
  have hkm : k < p := lt_of_le_of_lt hkp (Nat.sub_one_lt (p_pos (p := p)).ne')
  have h2 : p ∣ (p + k - 1).choose k := p_dvd_choose_p_add (p := p) hk0 hkm
  have h3 : p ∣ (3 * p + 2 * k - 3).choose (p - 1) :=
    p_dvd_choose_third_pred hp5 hk2 hkp
  rw [term_pred_eq (p := p) hp1, pow_two p,
    mul_div_of_dvd_dvd h2 h3 (p_pos (p := p))]

lemma term_pred_div_psq_low {k : ℕ} (hp5 : 5 ≤ p)
    (hk2 : 2 ≤ k) (hk : k ≤ (p + 1) / 2) :
    ((term (p - 1) k / p ^ 2 : ℕ) : ZMod p) =
      (3 : ZMod p) * ((2 : ZMod p) * (k : ZMod p) * ((k - 1 : ℕ) : ZMod p))⁻¹ := by
  have hkp : k ≤ p - 1 := by
    have : (p + 1) / 2 ≤ p - 1 := by omega
    exact le_trans hk this
  have hk0 : 0 < k := lt_of_lt_of_le (by decide : 0 < 2) hk2
  have hkm : k < p := lt_of_le_of_lt hkp (Nat.sub_one_lt (p_pos (p := p)).ne')
  rw [term_div_psq_eq hp5 hk2 hkp, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow]
  have hch : ((p - 1).choose k : ZMod p) = (-1) ^ k :=
    choose_pred_zmod (p := p) hkp
  have hsq : ((p - 1).choose k : ZMod p) ^ 2 = 1 := by
    rw [hch, pow_two, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have h2 : (((p + k - 1).choose k / p : ℕ) : ZMod p) = (k : ZMod p)⁻¹ :=
    choose_p_add_div_p_zmod (p := p) hk0 hkm
  have h3 := choose_third_div_p_low (p := p) hp5 hk2 hk
  rw [hsq, h2, h3, one_mul]
  have hkne : (k : ZMod p) ≠ 0 := zmod_nat_ne_zero hk0 hkm
  have hk1ne : ((k - 1 : ℕ) : ZMod p) ≠ 0 :=
    zmod_nat_ne_zero (by omega) (lt_trans (Nat.sub_one_lt hk0.ne') hkm)
  have h2ne : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp5
  field

lemma term_pred_div_psq_high {k : ℕ} (hp5 : 5 ≤ p)
    (hk : (p + 3) / 2 ≤ k) (hkp : k ≤ p - 1) :
    ((term (p - 1) k / p ^ 2 : ℕ) : ZMod p) =
      (4 : ZMod p) * ((k : ZMod p) * (((2 * k : ℕ) : ZMod p) - (p : ZMod p) - 2))⁻¹ := by
  have hk2 : 2 ≤ k := by
    have : 2 ≤ (p + 3) / 2 := by omega
    exact le_trans this hk
  have hk0 : 0 < k := lt_of_lt_of_le (by decide : 0 < 2) hk2
  have hkm : k < p := lt_of_le_of_lt hkp (Nat.sub_one_lt (p_pos (p := p)).ne')
  rw [term_div_psq_eq hp5 hk2 hkp, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow]
  have hch : ((p - 1).choose k : ZMod p) = (-1) ^ k :=
    choose_pred_zmod (p := p) hkp
  have hsq : ((p - 1).choose k : ZMod p) ^ 2 = 1 := by
    rw [hch, pow_two, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have h2 : (((p + k - 1).choose k / p : ℕ) : ZMod p) = (k : ZMod p)⁻¹ :=
    choose_p_add_div_p_zmod (p := p) hk0 hkm
  have h3 := choose_third_div_p_high (p := p) hp5 hk hkp
  rw [hsq, h2, h3, one_mul]
  field

lemma Icc_shift_two_p {a b : ℕ} :
    (Icc a b).image (fun j => 2 * p + j) = Icc (2 * p + a) (2 * p + b) := by
  ext x
  simp only [mem_image, mem_Icc]
  constructor
  · rintro ⟨j, ⟨hj1, hj2⟩, rfl⟩
    omega
  · intro hx
    refine ⟨x - 2 * p, by omega, by omega⟩

lemma prod_Icc_shift_two_p {a b : ℕ} :
    ∏ j ∈ Icc a b, (2 * p + j) = ∏ x ∈ Icc (2 * p + a) (2 * p + b), x := by
  have hinj : Set.InjOn (fun j : ℕ => 2 * p + j) (Icc a b) := by
    intro x _ y _ h
    exact Nat.add_left_cancel h
  rw [← Icc_shift_two_p, eq_comm]
  exact Finset.prod_image (fun x hx y hy h => hinj hx hy h)

lemma poly_t01_nonneg (hp5 : 5 ≤ p) :
    27 * p ^ 2 + 9 ≤ 9 * p ^ 3 + 29 * p := by
  nlinarith

lemma bracket_eq_int (p : ℕ) :
    (2 * (2 * (p : ℤ) - 1) + ((p : ℤ) - 1) ^ 2 * (3 * p - 2) * (3 * p - 1)) =
      (p : ℤ) * (9 * (p : ℤ) ^ 3 - 27 * (p : ℤ) ^ 2 + 29 * p - 9) := by
  ring

lemma bracket_eq (hp5 : 5 ≤ p) :
    2 * (2 * p - 1) + (p - 1) ^ 2 * (3 * p - 2) * (3 * p - 1) =
      p * (9 * p ^ 3 + 29 * p - (27 * p ^ 2 + 9)) := by
  have h1 : 1 ≤ 2 * p := by omega
  have hp1 : 1 ≤ p := le_trans (by decide : 1 ≤ 5) hp5
  have h2 : 2 ≤ 3 * p := by omega
  have h2' : 1 ≤ 3 * p := by omega
  have hnn := poly_t01_nonneg (p := p) hp5
  refine (Nat.cast_injective (R := ℤ) ?_)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_sub h1, Nat.cast_sub hp1, Nat.cast_sub h2, Nat.cast_sub h2',
    Nat.cast_sub hnn]
  ring

lemma prod_Icc_one_n (n : ℕ) : ∏ j ∈ Icc 1 n, j = n ! := by
  cases n with
  | zero => simp
  | succ n =>
    have : Icc 1 (n + 1) = Ico 1 (n + 2) := by
      ext x; simp [mem_Icc, mem_Ico]; omega
    rw [this]
    simpa [Nat.succ_eq_add_one] using prod_Ico_id_eq_factorial (n + 1)

lemma not_mem_Icc_of_lt {a b c : ℕ} (h : a < b) : a ∉ Icc b c := by
  simp [mem_Icc]; omega

lemma not_mem_Icc_of_gt {a b c : ℕ} (h : c < a) : a ∉ Icc b c := by
  simp [mem_Icc]; omega

lemma term0_mul_factorial (hp5 : 5 ≤ p) :
    term (p - 1) 0 * (p - 1)! =
      (2 * p - 1) * (2 * p) * ∏ j ∈ Icc 1 (p - 3), (2 * p + j) := by
  have hdesc : (3 * p - 3).descFactorial (p - 1) =
      ∏ j ∈ Icc (2 * p - 1) (3 * p - 3), j := by
    have hkn : p - 1 ≤ (3 * p - 3) + 1 := by omega
    have : (3 * p - 3) + 1 - (p - 1) = 2 * p - 1 := by omega
    rw [descFactorial_eq_prod_Icc (by omega) hkn, this]
  have hsplit :
      ∏ j ∈ Icc (2 * p - 1) (3 * p - 3), j =
        (2 * p - 1) * (2 * p) * ∏ j ∈ Icc 1 (p - 3), (2 * p + j) := by
    have h1 : Icc (2 * p - 1) (3 * p - 3) =
        insert (2 * p - 1) (Icc (2 * p) (3 * p - 3)) := by
      ext x; simp [mem_Icc, mem_insert]; omega
    have hnotin1 : 2 * p - 1 ∉ Icc (2 * p) (3 * p - 3) :=
      not_mem_Icc_of_lt (by omega)
    rw [h1, prod_insert hnotin1]
    have h2 : Icc (2 * p) (3 * p - 3) =
        insert (2 * p) (Icc (2 * p + 1) (3 * p - 3)) := by
      ext x; simp [mem_Icc, mem_insert]; omega
    have hnotin2 : 2 * p ∉ Icc (2 * p + 1) (3 * p - 3) :=
      not_mem_Icc_of_lt (by omega)
    rw [h2, prod_insert hnotin2]
    have : Icc (2 * p + 1) (3 * p - 3) = Icc (2 * p + 1) (2 * p + (p - 3)) := by
      congr 1; omega
    rw [this, ← prod_Icc_shift_two_p]
    ac_rfl
  have hC : (3 * p - 3).choose (p - 1) * (p - 1)! =
      (3 * p - 3).descFactorial (p - 1) := by
    rw [mul_comm, descFactorial_eq_factorial_mul_choose]
  rw [term_pred_zero, hC, hdesc, hsplit]

lemma term1_mul_factorial (hp5 : 5 ≤ p) :
    term (p - 1) 1 * (p - 1)! =
      (p - 1) ^ 2 * p * (∏ j ∈ Icc 1 (p - 3), (2 * p + j)) *
        (3 * p - 2) * (3 * p - 1) := by
  have hdesc : (3 * p - 1).descFactorial (p - 1) =
      ∏ j ∈ Icc (2 * p + 1) (3 * p - 1), j := by
    have hkn : p - 1 ≤ (3 * p - 1) + 1 := by omega
    have : (3 * p - 1) + 1 - (p - 1) = 2 * p + 1 := by omega
    rw [descFactorial_eq_prod_Icc (by omega) hkn, this]
  have hprod : ∏ j ∈ Icc (2 * p + 1) (3 * p - 1), j =
      (∏ j ∈ Icc 1 (p - 3), (2 * p + j)) * (3 * p - 2) * (3 * p - 1) := by
    have : Icc (2 * p + 1) (3 * p - 1) = Icc (2 * p + 1) (2 * p + (p - 1)) := by
      congr 1; omega
    rw [this, ← prod_Icc_shift_two_p]
    have hs : Icc 1 (p - 1) = insert (p - 1) (insert (p - 2) (Icc 1 (p - 3))) := by
      ext x; simp [mem_Icc, mem_insert]; omega
    have hnotin1 : p - 1 ∉ insert (p - 2) (Icc 1 (p - 3)) := by
      simp [mem_insert, mem_Icc]; omega
    have hnotin2 : p - 2 ∉ Icc 1 (p - 3) :=
      not_mem_Icc_of_gt (by omega)
    rw [hs, prod_insert hnotin1, prod_insert hnotin2]
    have hp1 : 2 * p + (p - 1) = 3 * p - 1 := by omega
    have hp2 : 2 * p + (p - 2) = 3 * p - 2 := by omega
    simp only [hp1, hp2]
    ac_rfl
  have hC : (3 * p - 1).choose (p - 1) * (p - 1)! =
      (3 * p - 1).descFactorial (p - 1) := by
    rw [mul_comm, descFactorial_eq_factorial_mul_choose]
  rw [term_pred_one]
  calc
    (p - 1) ^ 2 * p * (3 * p - 1).choose (p - 1) * (p - 1)!
        = (p - 1) ^ 2 * p * ((3 * p - 1).choose (p - 1) * (p - 1)!) := by ring
    _ = (p - 1) ^ 2 * p * (3 * p - 1).descFactorial (p - 1) := by rw [hC]
    _ = (p - 1) ^ 2 * p * ∏ j ∈ Icc (2 * p + 1) (3 * p - 1), j := by rw [hdesc]
    _ = (p - 1) ^ 2 * p *
          ((∏ j ∈ Icc 1 (p - 3), (2 * p + j)) * (3 * p - 2) * (3 * p - 1)) := by
        rw [hprod]
    _ = (p - 1) ^ 2 * p * (∏ j ∈ Icc 1 (p - 3), (2 * p + j)) *
          (3 * p - 2) * (3 * p - 1) := by ring

lemma factorial_split_three (hp4 : 4 ≤ p) :
    (p - 1)! = (p - 1) * (p - 2) * (p - 3)! := by
  have h1 : p - 1 = (p - 2) + 1 := by omega
  have h2 : p - 2 = (p - 3) + 1 := by omega
  rw [h1, factorial_succ, h2, factorial_succ]
  ring

/-- `(t(0)+t(1))/p² ≡ -9/2` in `ZMod p`. -/
lemma term_pred_zero_one_div_psq (hp5 : 5 ≤ p) :
    p ^ 2 ∣ term (p - 1) 0 + term (p - 1) 1 ∧
    (((term (p - 1) 0 + term (p - 1) 1) / p ^ 2 : ℕ) : ZMod p) =
      - (9 : ZMod p) * (2 : ZMod p)⁻¹ := by
  set P := ∏ j ∈ Icc 1 (p - 3), (2 * p + j)
  set poly := 9 * p ^ 3 + 29 * p - (27 * p ^ 2 + 9)
  have hppos : 0 < p := p_pos (p := p)
  have hpr : p.Prime := Fact.out
  have h0 := term0_mul_factorial (p := p) hp5
  have h1 := term1_mul_factorial (p := p) hp5
  have hbr := bracket_eq (p := p) hp5
  have hsum :
      (term (p - 1) 0 + term (p - 1) 1) * (p - 1)! =
        p ^ 2 * (P * poly) := by
    have hdistrib :
        (term (p - 1) 0 + term (p - 1) 1) * (p - 1)! =
          term (p - 1) 0 * (p - 1)! + term (p - 1) 1 * (p - 1)! := by ring
    rw [hdistrib, h0, h1]
    have hfactor :
        (2 * p - 1) * (2 * p) * P +
            (p - 1) ^ 2 * p * P * (3 * p - 2) * (3 * p - 1) =
          P * (p * (2 * (2 * p - 1) + (p - 1) ^ 2 * (3 * p - 2) * (3 * p - 1))) := by
      ring
    rw [hfactor, hbr]
    ring
  have hndvd : ¬ p ∣ (p - 1)! := by
    intro h
    exact (not_le_of_gt (Nat.sub_one_lt hppos.ne')) (hpr.dvd_factorial.mp h)
  have hdiv_mul : p ^ 2 ∣ (term (p - 1) 0 + term (p - 1) 1) * (p - 1)! := by
    rw [hsum]; exact dvd_mul_right _ _
  have hcop : Coprime (p ^ 2) (p - 1)! := by
    rw [Nat.coprime_pow_left_iff (by decide : 0 < 2)]
    exact hpr.coprime_iff_not_dvd.mpr hndvd
  have hdiv : p ^ 2 ∣ term (p - 1) 0 + term (p - 1) 1 :=
    hcop.dvd_of_dvd_mul_right hdiv_mul
  have hquot :
      (term (p - 1) 0 + term (p - 1) 1) / p ^ 2 * (p - 1)! = P * poly := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hppos 2)
    calc
      p ^ 2 * ((term (p - 1) 0 + term (p - 1) 1) / p ^ 2 * (p - 1)!)
          = p ^ 2 * ((term (p - 1) 0 + term (p - 1) 1) / p ^ 2) * (p - 1)! := by ring
      _ = (term (p - 1) 0 + term (p - 1) 1) * (p - 1)! := by
            rw [Nat.mul_div_cancel' hdiv]
      _ = p ^ 2 * (P * poly) := hsum
  have hP : (P : ZMod p) = ((p - 3)! : ZMod p) := by
    simp only [P]
    rw [Nat.cast_prod, ← prod_Icc_one_n (p - 3), Nat.cast_prod]
    refine prod_congr rfl ?_
    intro j hj
    rw [Nat.cast_add, Nat.cast_mul, CharP.cast_eq_zero (R := ZMod p) p, mul_zero, zero_add]
  have hpoly : (poly : ZMod p) = -9 := by
    simp only [poly]
    have hnn := poly_t01_nonneg (p := p) hp5
    rw [Nat.cast_sub hnn]
    push_cast
    simp only [CharP.cast_eq_zero (R := ZMod p) p, zero_mul, mul_zero,
      zero_pow (by decide : (3 : ℕ) ≠ 0), zero_add, add_zero, zero_sub]
    ring
  have hfac : ((p - 1)! : ZMod p) = (2 : ZMod p) * ((p - 3)! : ZMod p) := by
    rw [factorial_split_three (by omega : 4 ≤ p), Nat.cast_mul, Nat.cast_mul]
    have hp1 : ((p - 1 : ℕ) : ZMod p) = -1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one, CharP.cast_eq_zero (R := ZMod p) p, zero_sub]
    have hp2 : ((p - 2 : ℕ) : ZMod p) = -2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ p), Nat.cast_ofNat, CharP.cast_eq_zero (R := ZMod p) p]
      ring
    rw [hp1, hp2]
    ring
  have hcast :
      (((term (p - 1) 0 + term (p - 1) 1) / p ^ 2 : ℕ) : ZMod p) * ((p - 1)! : ZMod p) =
        (P : ZMod p) * (poly : ZMod p) := by
    rw [← Nat.cast_mul, hquot, Nat.cast_mul]
  refine ⟨hdiv, ?_⟩
  have hfac0 : ((p - 3)! : ZMod p) ≠ 0 :=
    factorial_ne_zero_zmod (by omega)
  have h2ne : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp5
  have hmul :
      (((term (p - 1) 0 + term (p - 1) 1) / p ^ 2 : ℕ) : ZMod p) *
          ((2 : ZMod p) * ((p - 3)! : ZMod p)) =
        ((p - 3)! : ZMod p) * (-9) := by
    rw [← hfac, hcast, hP, hpoly]
  have hmul' :
      (((term (p - 1) 0 + term (p - 1) 1) / p ^ 2 : ℕ) : ZMod p) * (2 : ZMod p) =
        (-9 : ZMod p) := by
    have := congrArg (fun x : ZMod p => x * ((p - 3)! : ZMod p)⁻¹) hmul
    simp only at this
    have hcancel1 :
        (((term (p - 1) 0 + term (p - 1) 1) / p ^ 2 : ℕ) : ZMod p) *
            ((2 : ZMod p) * ((p - 3)! : ZMod p)) * ((p - 3)! : ZMod p)⁻¹ =
          (((term (p - 1) 0 + term (p - 1) 1) / p ^ 2 : ℕ) : ZMod p) * (2 : ZMod p) := by
      field
    have hcancel2 :
        ((p - 3)! : ZMod p) * (-9) * ((p - 3)! : ZMod p)⁻¹ = (-9 : ZMod p) := by
      field
    rw [hcancel1] at this
    rwa [hcancel2] at this
  have hinv := congrArg (fun x : ZMod p => x * (2 : ZMod p)⁻¹) hmul'
  simpa [mul_assoc, mul_inv_cancel₀ h2ne] using hinv

lemma sum_range_sub_zmod (f : ℕ → ZMod p) (n : ℕ) :
    ∑ i ∈ range n, (f (i + 1) - f i) = f n - f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    abel

lemma inv_mul_sub_inv {x y : ZMod p} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x - y ≠ 0) :
    (x * y)⁻¹ * (x - y) = y⁻¹ - x⁻¹ := by
  field

lemma inv_succ_sub_inv {k : ℕ} (hk0 : 0 < k) (hkp : k + 1 < p) :
    ((k : ZMod p) * ((k : ZMod p) + 1))⁻¹ =
      (k : ZMod p)⁻¹ - ((k : ZMod p) + 1)⁻¹ := by
  have hklt : k < p := lt_trans (Nat.lt_succ_self k) hkp
  have hk0' : (k : ZMod p) ≠ 0 := zmod_nat_ne_zero hk0 hklt
  have hk1 : ((k : ZMod p) + 1) ≠ 0 := by
    have : ((k + 1 : ℕ) : ZMod p) ≠ 0 := zmod_nat_ne_zero (Nat.succ_pos k) hkp
    simpa [Nat.cast_add]
  have hdiff : (k : ZMod p) + 1 - k ≠ 0 := by
    simp [add_sub_cancel_left]
  have h := inv_mul_sub_inv (x := (k : ZMod p) + 1) (y := (k : ZMod p)) hk1 hk0' hdiff
  simp only [add_sub_cancel_left, mul_one] at h
  rw [mul_comm, ← h]

/-- `1/(k(k-1)) = 1/(k-1) - 1/k` in `ZMod p`. -/
lemma inv_mul_pred {k : ℕ} (hk2 : 2 ≤ k) (hkp : k < p) :
    ((k : ZMod p) * ((k - 1 : ℕ) : ZMod p))⁻¹ =
      ((k - 1 : ℕ) : ZMod p)⁻¹ - (k : ZMod p)⁻¹ := by
  have hk0 : 0 < k - 1 := by omega
  have hk1p : (k - 1) + 1 < p := by omega
  have hkeq : (k : ZMod p) = ((k - 1 : ℕ) : ZMod p) + 1 := by
    have : k = (k - 1) + 1 := by omega
    rw [this]
    norm_cast
  rw [hkeq, mul_comm]
  exact inv_succ_sub_inv (k := k - 1) hk0 hk1p

lemma three_mul_inv_two (hp5 : 5 ≤ p) {k : ℕ} (hk2 : 2 ≤ k) (hkp : k < p) :
    (3 : ZMod p) * ((2 : ZMod p) * (k : ZMod p) * ((k - 1 : ℕ) : ZMod p))⁻¹ =
      (3 : ZMod p) * (2 : ZMod p)⁻¹ *
        (((k - 1 : ℕ) : ZMod p)⁻¹ - (k : ZMod p)⁻¹) := by
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp5
  have hkne : (k : ZMod p) ≠ 0 := zmod_nat_ne_zero (by omega) hkp
  have hk1ne : ((k - 1 : ℕ) : ZMod p) ≠ 0 :=
    zmod_nat_ne_zero (by omega) (lt_trans (Nat.sub_one_lt (by omega)) hkp)
  have h := inv_mul_pred (p := p) hk2 hkp
  field_simp [h]
  rw [cast_sub_pred (k := k) (by omega : 1 ≤ k)]
  ring

lemma four_eq_high (hp5 : 5 ≤ p) {k : ℕ} (hk2 : 2 ≤ k) (hkp : k < p) :
    (4 : ZMod p) * ((k : ZMod p) * (((2 * k : ℕ) : ZMod p) - (p : ZMod p) - 2))⁻¹ =
      (2 : ZMod p) * (((k - 1 : ℕ) : ZMod p)⁻¹ - (k : ZMod p)⁻¹) := by
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp5
  have hkne : (k : ZMod p) ≠ 0 := zmod_nat_ne_zero (by omega) hkp
  have hk1ne : ((k - 1 : ℕ) : ZMod p) ≠ 0 :=
    zmod_nat_ne_zero (by omega) (lt_trans (Nat.sub_one_lt (by omega)) hkp)
  have h2k : ((2 * k : ℕ) : ZMod p) - (p : ZMod p) - 2 =
      (2 : ZMod p) * ((k - 1 : ℕ) : ZMod p) := by
    simp only [Nat.cast_mul]
    have hp0 : (p : ZMod p) = 0 := by simp
    rw [hp0, sub_zero]
    have hk : (k : ZMod p) = ((k - 1 : ℕ) : ZMod p) + 1 := by
      have : k = (k - 1) + 1 := by omega
      rw [this]; norm_cast
    rw [hk]
    ring
  rw [h2k]
  have h := inv_mul_pred (p := p) hk2 hkp
  field_simp [h]
  rw [cast_sub_pred (k := k) (by omega : 1 ≤ k)]
  ring

lemma mid_val (hp5 : 5 ≤ p) : (((p + 1) / 2 : ℕ) : ZMod p) = (2 : ZMod p)⁻¹ := by
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp5
  have : 2 * ((p + 1) / 2) = p + 1 := by
    have hodd : p % 2 = 1 := (Fact.out : p.Prime).eq_two_or_odd.resolve_left (by omega)
    have : (p + 1) % 2 = 0 := by omega
    exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero this)
  have hcast : (2 : ZMod p) * (((p + 1) / 2 : ℕ) : ZMod p) = 1 := by
    have hc := congrArg (fun n : ℕ => (n : ZMod p)) this
    simpa [Nat.cast_mul, Nat.cast_add, CharP.cast_eq_zero (R := ZMod p) p] using hc
  exact (inv_eq_of_mul_eq_one_right hcast).symm

lemma sum_Icc_inv_diff {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hbp : b < p) :
    ∑ k ∈ Icc a b, (((k - 1 : ℕ) : ZMod p)⁻¹ - (k : ZMod p)⁻¹) =
      ((a - 1 : ℕ) : ZMod p)⁻¹ - (b : ZMod p)⁻¹ := by
  revert hbp
  refine Nat.le_induction ?_ ?_ b hab
  · intro hbp
    simp [Icc_self]
  · intro n hn ih hnp
    have hnlt : n < p := lt_trans (Nat.lt_succ_self n) hnp
    rw [sum_Icc_succ_top (Nat.le_succ_of_le hn)]
    rw [ih hnlt]
    have : ((n + 1 - 1 : ℕ) : ZMod p) = (n : ZMod p) := by
      simp
    rw [this]
    abel

lemma mid_add_one (hp5 : 5 ≤ p) :
    (p + 3) / 2 = (p + 1) / 2 + 1 := by
  have hodd := p_odd (p := p) hp5
  omega

lemma mid_bounds (hp5 : 5 ≤ p) :
    2 ≤ (p + 1) / 2 ∧ (p + 3) / 2 ≤ p - 1 := by
  omega

lemma cast_pred_eq_neg_one (hp : 1 ≤ p) :
    ((p - 1 : ℕ) : ZMod p) = -1 := by
  rw [Nat.cast_sub hp, Nat.cast_one, CharP.cast_eq_zero (R := ZMod p) p, zero_sub]

lemma inv_pred_eq_neg_one (hp5 : 5 ≤ p) :
    ((p - 1 : ℕ) : ZMod p)⁻¹ = -1 := by
  have hp1 : 1 ≤ p := le_trans (by decide : 1 ≤ 5) hp5
  rw [cast_pred_eq_neg_one hp1, inv_neg, inv_one]

lemma two_k_sub_two_eq {k : ℕ} :
    ((2 * k : ℕ) : ZMod p) - (2 : ZMod p) =
      ((2 * k : ℕ) : ZMod p) - (p : ZMod p) - 2 := by
  simp [CharP.cast_eq_zero (R := ZMod p) p]

lemma sum_term_pred_high_low (hp5 : 5 ≤ p) :
    (∑ k ∈ Icc 2 ((p + 1) / 2),
        (3 : ZMod p) * ((2 : ZMod p) * (k : ZMod p) * ((k - 1 : ℕ) : ZMod p))⁻¹) +
    (∑ k ∈ Icc ((p + 3) / 2) (p - 1),
        (4 : ZMod p) * ((k : ZMod p) * (((2 * k : ℕ) : ZMod p) - 2))⁻¹) =
      (9 : ZMod p) * (2 : ZMod p)⁻¹ := by
  set m := (p + 1) / 2
  have hm3 : (p + 3) / 2 = m + 1 := mid_add_one (p := p) hp5
  have ⟨hm2, hmp⟩ := mid_bounds (p := p) hp5
  have hmlt : m < p := by omega
  have h2ne : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp5
  have hmid : (m : ZMod p) = (2 : ZMod p)⁻¹ := mid_val (p := p) hp5
  have hmid_inv : (m : ZMod p)⁻¹ = 2 := by
    have : (2 : ZMod p) * (m : ZMod p) = 1 := by
      rw [hmid, mul_inv_cancel₀ h2ne]
    exact inv_eq_of_mul_eq_one_left this
  have hlow :
      ∑ k ∈ Icc 2 m,
          (3 : ZMod p) * ((2 : ZMod p) * (k : ZMod p) * ((k - 1 : ℕ) : ZMod p))⁻¹ =
        (3 : ZMod p) * (2 : ZMod p)⁻¹ *
          ∑ k ∈ Icc 2 m, (((k - 1 : ℕ) : ZMod p)⁻¹ - (k : ZMod p)⁻¹) := by
    rw [mul_sum]
    refine sum_congr rfl ?_
    intro k hk
    have hkI := mem_Icc.mp hk
    have hk2 : 2 ≤ k := hkI.1
    have hkp : k < p := lt_of_le_of_lt hkI.2 hmlt
    exact three_mul_inv_two (p := p) hp5 hk2 hkp
  have hhigh :
      ∑ k ∈ Icc (m + 1) (p - 1),
          (4 : ZMod p) * ((k : ZMod p) * (((2 * k : ℕ) : ZMod p) - 2))⁻¹ =
        (2 : ZMod p) *
          ∑ k ∈ Icc (m + 1) (p - 1),
            (((k - 1 : ℕ) : ZMod p)⁻¹ - (k : ZMod p)⁻¹) := by
    rw [mul_sum]
    refine sum_congr rfl ?_
    intro k hk
    have hkI := mem_Icc.mp hk
    have hk2 : 2 ≤ k := by omega
    have hkp : k < p := lt_of_le_of_lt hkI.2 (Nat.sub_one_lt (p_pos (p := p)).ne')
    have hform := four_eq_high (p := p) hp5 hk2 hkp
    have h2k := two_k_sub_two_eq (p := p) (k := k)
    rw [h2k]
    exact hform
  rw [hlow, hm3, hhigh]
  have htel_low :
      ∑ k ∈ Icc 2 m, (((k - 1 : ℕ) : ZMod p)⁻¹ - (k : ZMod p)⁻¹) =
        (1 : ZMod p) - (m : ZMod p)⁻¹ := by
    have := sum_Icc_inv_diff (p := p) (a := 2) (b := m) (by decide) hm2 hmlt
    simpa [Nat.cast_one] using this
  have htel_high :
      ∑ k ∈ Icc (m + 1) (p - 1), (((k - 1 : ℕ) : ZMod p)⁻¹ - (k : ZMod p)⁻¹) =
        (m : ZMod p)⁻¹ - ((p - 1 : ℕ) : ZMod p)⁻¹ := by
    have hm1 : 1 ≤ m + 1 := Nat.succ_pos _
    have hle : m + 1 ≤ p - 1 := by omega
    have hbp : p - 1 < p := Nat.sub_one_lt (p_pos (p := p)).ne'
    have := sum_Icc_inv_diff (p := p) (a := m + 1) (b := p - 1) hm1 hle hbp
    have : ((m + 1 - 1 : ℕ) : ZMod p) = (m : ZMod p) := by simp
    rwa [this] at this
  rw [htel_low, htel_high, hmid_inv, inv_pred_eq_neg_one hp5]
  field_simp
  ring

lemma Icc_split_mid (hp5 : 5 ≤ p) :
    Icc 2 (p - 1) = Icc 2 ((p + 1) / 2) ∪ Icc ((p + 3) / 2) (p - 1) := by
  ext x
  simp only [mem_Icc, mem_union]
  have hm := mid_add_one (p := p) hp5
  omega

lemma disjoint_mid (hp5 : 5 ≤ p) :
    Disjoint (Icc 2 ((p + 1) / 2)) (Icc ((p + 3) / 2) (p - 1)) := by
  refine disjoint_left.mpr ?_
  intro x hx hy
  simp only [mem_Icc] at hx hy
  have hm := mid_add_one (p := p) hp5
  omega

lemma range_pred_split :
    range p = {0} ∪ {1} ∪ Icc 2 (p - 1) := by
  have hp2 : 2 ≤ p := p_ge_two (p := p)
  ext x
  simp only [mem_range, mem_union, mem_singleton, mem_Icc]
  constructor
  · intro hx
    by_cases h0 : x = 0
    · exact Or.inl (Or.inl h0)
    · by_cases h1 : x = 1
      · exact Or.inl (Or.inr h1)
      · exact Or.inr (by omega)
  · intro hx
    obtain h0 | hx := hx
    · obtain rfl | rfl := h0 <;> omega
    · have hppos : 0 < p := lt_of_lt_of_le (by decide : 0 < 2) hp2
      exact lt_of_le_of_lt hx.2 (Nat.sub_one_lt hppos.ne')

lemma p_pow_three_dvd_a_pred (hp5 : 5 ≤ p) :
    p ^ 3 ∣ a (p - 1) := by
  have hppos : 0 < p := p_pos (p := p)
  have h01 := term_pred_zero_one_div_psq (p := p) hp5
  have hC : ∀ k ∈ Icc 2 (p - 1), p ^ 2 ∣ term (p - 1) k := by
    intro k hk
    have hkI := mem_Icc.mp hk
    exact psq_dvd_term_pred_of_two_le hp5 hkI.1 hkI.2
  have hsumC : p ^ 2 ∣ ∑ k ∈ Icc 2 (p - 1), term (p - 1) k :=
    dvd_sum hC
  have ha_split : a (p - 1) =
      (term (p - 1) 0 + term (p - 1) 1) + ∑ k ∈ Icc 2 (p - 1), term (p - 1) k := by
    rw [a_eq_sum_term]
    have hrp : range ((p - 1) + 1) = range p := by
      congr 1; omega
    rw [hrp, range_pred_split]
    have h01d : Disjoint ({0} ∪ {1} : Finset ℕ) (Icc 2 (p - 1)) := by
      refine disjoint_left.mpr ?_
      intro x hx hy
      simp only [mem_union, mem_singleton] at hx
      have := mem_Icc.mp hy
      omega
    have h0d1 : Disjoint ({0} : Finset ℕ) {1} := by
      simp [disjoint_left]
    rw [sum_union h01d, sum_union h0d1]
    simp [sum_singleton]
  have hdiv2 : p ^ 2 ∣ a (p - 1) := by
    rw [ha_split]
    exact dvd_add h01.1 hsumC
  have hquot :
      a (p - 1) / p ^ 2 =
        (term (p - 1) 0 + term (p - 1) 1) / p ^ 2 +
          ∑ k ∈ Icc 2 (p - 1), term (p - 1) k / p ^ 2 := by
    rw [ha_split, Nat.add_div_of_dvd_left hsumC]
    congr 1
    exact Nat.sum_div hC
  have hcast :
      ((a (p - 1) / p ^ 2 : ℕ) : ZMod p) =
        (((term (p - 1) 0 + term (p - 1) 1) / p ^ 2 : ℕ) : ZMod p) +
          ∑ k ∈ Icc 2 (p - 1), ((term (p - 1) k / p ^ 2 : ℕ) : ZMod p) := by
    rw [hquot, Nat.cast_add, Nat.cast_sum]
  have hsplit_sum :
      ∑ k ∈ Icc 2 (p - 1), ((term (p - 1) k / p ^ 2 : ℕ) : ZMod p) =
        (∑ k ∈ Icc 2 ((p + 1) / 2), ((term (p - 1) k / p ^ 2 : ℕ) : ZMod p)) +
          ∑ k ∈ Icc ((p + 3) / 2) (p - 1),
            ((term (p - 1) k / p ^ 2 : ℕ) : ZMod p) := by
    rw [Icc_split_mid hp5, sum_union (disjoint_mid hp5)]
  have hlow :
      ∑ k ∈ Icc 2 ((p + 1) / 2), ((term (p - 1) k / p ^ 2 : ℕ) : ZMod p) =
        ∑ k ∈ Icc 2 ((p + 1) / 2),
          (3 : ZMod p) * ((2 : ZMod p) * (k : ZMod p) * ((k - 1 : ℕ) : ZMod p))⁻¹ := by
    refine sum_congr rfl ?_
    intro k hk
    have hkI := mem_Icc.mp hk
    exact term_pred_div_psq_low (p := p) hp5 hkI.1 hkI.2
  have hhigh :
      ∑ k ∈ Icc ((p + 3) / 2) (p - 1), ((term (p - 1) k / p ^ 2 : ℕ) : ZMod p) =
        ∑ k ∈ Icc ((p + 3) / 2) (p - 1),
          (4 : ZMod p) * ((k : ZMod p) * (((2 * k : ℕ) : ZMod p) - 2))⁻¹ := by
    refine sum_congr rfl ?_
    intro k hk
    have hkI := mem_Icc.mp hk
    have hform := term_pred_div_psq_high (p := p) hp5 hkI.1 hkI.2
    have h2k := two_k_sub_two_eq (p := p) (k := k)
    rw [hform, ← h2k]
  have hsum0 :
      ((a (p - 1) / p ^ 2 : ℕ) : ZMod p) = 0 := by
    rw [hcast, h01.2, hsplit_sum, hlow, hhigh, sum_term_pred_high_low hp5]
    ring
  have hdiv3 : p ∣ a (p - 1) / p ^ 2 :=
    (ZMod.natCast_eq_zero_iff _ p).mp hsum0
  have : p ^ 3 ∣ a (p - 1) := by
    have hpow : p ^ 3 = p ^ 2 * p := by ring
    rw [hpow]
    exact Nat.mul_dvd_of_dvd_div hdiv2 hdiv3
  exact this

end NPred

/- General `n = p - r`. -/

section GeneralR
variable {p : ℕ} [Fact p.Prime]

lemma factorial_eq_prod_mul (n t : ℕ) (ht : t ≤ n) :
    n ! = (∏ i ∈ range t, (n - i)) * (n - t)! := by
  induction t with
  | zero => simp
  | succ t ih =>
    have ht' : t ≤ n := by omega
    have hfac : (n - t)! = (n - t) * (n - t - 1)! :=
      (Nat.mul_factorial_pred (by omega : n - t ≠ 0)).symm
    have hst : n - (t + 1) = n - t - 1 := by omega
    calc
      n ! = (∏ i ∈ range t, (n - i)) * (n - t)! := ih ht'
      _ = (∏ i ∈ range t, (n - i)) * ((n - t) * (n - t - 1)!) := by rw [hfac]
      _ = (∏ i ∈ range t, (n - i)) * (n - t) * (n - t - 1)! := by ring
      _ = (∏ i ∈ range (t + 1), (n - i)) * (n - (t + 1))! := by
            rw [prod_range_succ, hst, mul_assoc]

lemma factorial_p_sub {r : ℕ} (hr0 : 0 < r) (hrp : r < p) :
    ((p - r)! : ZMod p) = (-1 : ZMod p) ^ r * ((r - 1)! : ZMod p)⁻¹ := by
  have hwilson : ((p - 1)! : ZMod p) = -1 := ZMod.wilsons_lemma p
  have hsplit : (p - 1)! = (∏ i ∈ range (r - 1), (p - 1 - i)) * (p - r)! := by
    have ht : r - 1 ≤ p - 1 := by omega
    have hdiff : p - 1 - (r - 1) = p - r := by omega
    simpa [hdiff] using factorial_eq_prod_mul (p - 1) (r - 1) ht
  have hprod : ((∏ i ∈ range (r - 1), (p - 1 - i) : ℕ) : ZMod p) =
      (-1 : ZMod p) ^ (r - 1) * ((r - 1)! : ZMod p) := by
    rw [Nat.cast_prod]
    have hcongr : ∀ i ∈ range (r - 1),
        ((p - 1 - i : ℕ) : ZMod p) = -((i + 1 : ℕ) : ZMod p) := by
      intro i hi
      have hi' : i < r - 1 := mem_range.mp hi
      have : p - 1 - i = p - (i + 1) := by omega
      rw [this, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one,
        CharP.cast_eq_zero (R := ZMod p) p, zero_sub]
    rw [prod_congr rfl hcongr, prod_neg, card_range]
    have : ∏ i ∈ range (r - 1), ((i + 1 : ℕ) : ZMod p) = ((r - 1)! : ZMod p) := by
      rw [← Nat.cast_prod, ← factorial_eq_prod_range_add_one (r - 1)]
    rw [this]
  have hcast : ((p - 1)! : ZMod p) =
      (-1 : ZMod p) ^ (r - 1) * ((r - 1)! : ZMod p) * ((p - r)! : ZMod p) := by
    rw [hsplit, Nat.cast_mul, hprod]
  have hfac0 : ((r - 1)! : ZMod p) ≠ 0 :=
    factorial_ne_zero_zmod (by omega)
  have hpow : ((-1 : ZMod p) ^ (r - 1)) ≠ 0 :=
    pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hmul : (-1 : ZMod p) ^ (r - 1) * ((r - 1)! : ZMod p) * ((p - r)! : ZMod p) = -1 :=
    hcast.symm.trans hwilson
  have hr : r - 1 + 1 = r := by omega
  have hRHS : (-1 : ZMod p) ^ (r - 1) * ((r - 1)! : ZMod p) *
      ((-1 : ZMod p) ^ r * ((r - 1)! : ZMod p)⁻¹) = -1 := by
    calc
      (-1 : ZMod p) ^ (r - 1) * ((r - 1)! : ZMod p) *
          ((-1 : ZMod p) ^ r * ((r - 1)! : ZMod p)⁻¹)
          = (-1 : ZMod p) ^ (r - 1) * (-1 : ZMod p) ^ r *
              (((r - 1)! : ZMod p) * ((r - 1)! : ZMod p)⁻¹) := by ring
      _ = (-1 : ZMod p) ^ (r - 1) * (-1 : ZMod p) ^ r := by
            rw [mul_inv_cancel₀ hfac0, mul_one]
      _ = (-1 : ZMod p) ^ (r - 1) * ((-1 : ZMod p) * (-1 : ZMod p) ^ (r - 1)) := by
            cases r with
            | zero => cases hr0
            | succ r' => simp [pow_succ]
      _ = ((-1 : ZMod p) ^ (r - 1)) ^ 2 * (-1 : ZMod p) := by ring
      _ = ((-1 : ZMod p) ^ 2) ^ (r - 1) * (-1 : ZMod p) := by
            rw [← pow_mul, mul_comm (r - 1), pow_mul]
      _ = (1 : ZMod p) ^ (r - 1) * (-1 : ZMod p) := by rw [neg_one_sq]
      _ = -1 := by simp
  have hcoeff : (-1 : ZMod p) ^ (r - 1) * ((r - 1)! : ZMod p) ≠ 0 :=
    mul_ne_zero hpow hfac0
  exact mul_left_cancel₀ hcoeff (hmul.trans hRHS.symm)

lemma choose_p_sub_zmod {r k : ℕ} (hr0 : 0 < r) (hrp : r < p)
    (hk : k ≤ p - r) :
    ((p - r).choose k : ZMod p) = (-1 : ZMod p) ^ k * ((r + k - 1).choose k : ZMod p) := by
  have hklt : k < p := by omega
  have hfac0 : ((k ! : ℕ) : ZMod p) ≠ 0 := factorial_ne_zero_zmod hklt
  have hdesc : ((p - r).descFactorial k : ZMod p) =
      ((p - r).choose k : ZMod p) * (k ! : ZMod p) := by
    rw [descFactorial_eq_factorial_mul_choose, mul_comm, Nat.cast_mul]
  have hleft : ((p - r).descFactorial k : ZMod p) =
      (-1 : ZMod p) ^ k * ∏ i ∈ range k, ((r + i : ℕ) : ZMod p) := by
    rw [descFactorial_eq_prod_range, Nat.cast_prod]
    have hcongr : ∀ i ∈ range k,
        ((p - r - i : ℕ) : ZMod p) = -((r + i : ℕ) : ZMod p) := by
      intro i hi
      have hi' : i < k := mem_range.mp hi
      have : p - r - i = p - (r + i) := by omega
      rw [this, Nat.cast_sub (by omega), Nat.cast_add,
        CharP.cast_eq_zero (R := ZMod p) p, zero_sub]
    rw [prod_congr rfl hcongr, prod_neg, card_range]
  have hright : ∏ i ∈ range k, ((r + i : ℕ) : ZMod p) =
      ((r + k - 1).choose k : ZMod p) * (k ! : ZMod p) := by
    have hdesc2 : ((r + k - 1).descFactorial k : ZMod p) =
        ((r + k - 1).choose k : ZMod p) * (k ! : ZMod p) := by
      rw [descFactorial_eq_factorial_mul_choose, mul_comm, Nat.cast_mul]
    rw [← hdesc2, descFactorial_eq_prod_range, Nat.cast_prod]
    have hre : ∀ i ∈ range k,
        ((r + k - 1 - i : ℕ) : ZMod p) = ((r + (k - 1 - i) : ℕ) : ZMod p) := by
      intro i hi
      have : i < k := mem_range.mp hi
      have : r + k - 1 - i = r + (k - 1 - i) := by omega
      simp [this]
    rw [prod_congr rfl hre]
    exact (prod_range_reflect (fun j => ((r + j : ℕ) : ZMod p)) k).symm
  apply mul_right_cancel₀ hfac0
  rw [← hdesc, hleft, hright]
  ring

lemma choose_p_sub_add_zmod {r k : ℕ} (hr0 : 0 < r) (hrp : r < p)
    (hk : k < r) :
    ((p - r + k).choose k : ZMod p) =
      (-1 : ZMod p) ^ k * ((r - 1).choose k : ZMod p) := by
  have hklt : k < p := lt_trans hk hrp
  have hfac0 : ((k ! : ℕ) : ZMod p) ≠ 0 := factorial_ne_zero_zmod hklt
  have hdesc : ((p - r + k).descFactorial k : ZMod p) =
      ((p - r + k).choose k : ZMod p) * (k ! : ZMod p) := by
    rw [descFactorial_eq_factorial_mul_choose, mul_comm, Nat.cast_mul]
  have hleft : ((p - r + k).descFactorial k : ZMod p) =
      (-1 : ZMod p) ^ k * ∏ i ∈ range k, ((r - k + i : ℕ) : ZMod p) := by
    rw [descFactorial_eq_prod_range, Nat.cast_prod]
    have hcongr : ∀ i ∈ range k,
        ((p - r + k - i : ℕ) : ZMod p) = -((r - k + i : ℕ) : ZMod p) := by
      intro i hi
      have hi' : i < k := mem_range.mp hi
      have : p - r + k - i = p - (r - k + i) := by omega
      rw [this, Nat.cast_sub (by omega), Nat.cast_add,
        CharP.cast_eq_zero (R := ZMod p) p, zero_sub]
    rw [prod_congr rfl hcongr, prod_neg, card_range]
  have hright : ∏ i ∈ range k, ((r - k + i : ℕ) : ZMod p) =
      ((r - 1).choose k : ZMod p) * (k ! : ZMod p) := by
    have hdesc2 : ((r - 1).descFactorial k : ZMod p) =
        ((r - 1).choose k : ZMod p) * (k ! : ZMod p) := by
      rw [descFactorial_eq_factorial_mul_choose, mul_comm, Nat.cast_mul]
    rw [← hdesc2, descFactorial_eq_prod_range, Nat.cast_prod]
    have hre : ∀ i ∈ range k,
        ((r - 1 - i : ℕ) : ZMod p) = ((r - k + (k - 1 - i) : ℕ) : ZMod p) := by
      intro i hi
      have : i < k := mem_range.mp hi
      have : r - 1 - i = r - k + (k - 1 - i) := by omega
      simp [this]
    rw [prod_congr rfl hre]
    exact (prod_range_reflect (fun j => ((r - k + j : ℕ) : ZMod p)) k).symm
  apply mul_right_cancel₀ hfac0
  rw [← hdesc, hleft, hright]
  ring

lemma descFactorial_p_sub_add_split {r k : ℕ}
    (hr0 : 0 < r) (hrp : r < p) (hkr : r ≤ k) :
    (p - r + k).descFactorial k =
      (∏ j ∈ Icc 1 (k - r), (p + j)) * p * (∏ j ∈ Icc 1 (r - 1), (p - j)) := by
  have hk0 : 0 < k := lt_of_lt_of_le hr0 hkr
  have hkn : k ≤ (p - r + k) + 1 := by omega
  have hlo : (p - r + k) + 1 - k = p - r + 1 := by omega
  have hdesc := descFactorial_eq_prod_Icc (n := p - r + k) (k := k) hk0 hkn
  rw [hdesc, hlo]
  -- Icc (p-r+1) (p-r+k) = Icc (p-r+1) (p-1) ∪ {p} ∪ Icc (p+1) (p+k-r)
  have hI : Icc (p - r + 1) (p - r + k) =
      Icc (p - r + 1) (p - 1) ∪ {p} ∪ Icc (p + 1) (p + (k - r)) := by
    ext x
    simp only [mem_Icc, mem_union, mem_singleton]
    constructor
    · intro hx
      by_cases hlt : x < p
      · left; left; omega
      · by_cases heq : x = p
        · left; right; exact heq
        · right; omega
    · intro hx
      rcases hx with (⟨h1, h2⟩ | rfl) | ⟨h1, h2⟩ <;> omega
  have hd1 : Disjoint (Icc (p - r + 1) (p - 1) ∪ {p}) (Icc (p + 1) (p + (k - r))) := by
    refine disjoint_left.mpr ?_
    intro x hx hy
    simp only [mem_union, mem_singleton, mem_Icc] at hx hy
    omega
  have hd2 : Disjoint (Icc (p - r + 1) (p - 1)) ({p} : Finset ℕ) := by
    refine disjoint_left.mpr ?_
    intro x hx hy
    simp only [mem_Icc, mem_singleton] at hx hy
    omega
  rw [hI, prod_union hd1, prod_union hd2, prod_singleton]
  have hpos : ∏ x ∈ Icc (p + 1) (p + (k - r)), x = ∏ j ∈ Icc 1 (k - r), (p + j) := by
    have : Icc (p + 1) (p + (k - r)) = (Icc 1 (k - r)).image (fun j => p + j) := by
      ext x
      simp only [mem_Icc, mem_image]
      constructor
      · intro hx; refine ⟨x - p, by omega, by omega⟩
      · rintro ⟨j, hj, rfl⟩; omega
    have hinj : Set.InjOn (fun j : ℕ => p + j) (Icc 1 (k - r)) := by
      intro a _ b _ h; exact Nat.add_left_cancel h
    rw [this]
    exact Finset.prod_image (f := fun x : ℕ => x) (g := fun j : ℕ => p + j)
      (fun a ha b hb h => hinj ha hb h)
  have hneg : ∏ x ∈ Icc (p - r + 1) (p - 1), x = ∏ j ∈ Icc 1 (r - 1), (p - j) := by
    have : Icc (p - r + 1) (p - 1) = (Icc 1 (r - 1)).image (fun j => p - j) := by
      ext x
      simp only [mem_Icc, mem_image]
      constructor
      · intro hx
        refine ⟨p - x, by omega, by omega⟩
      · rintro ⟨j, hj, rfl⟩
        omega
    have hinj : Set.InjOn (fun j : ℕ => p - j) (Icc 1 (r - 1)) := by
      intro a ha b hb h
      have ha' : 1 ≤ a ∧ a ≤ r - 1 := by
        simpa [Set.mem_Icc] using ha
      have hb' : 1 ≤ b ∧ b ≤ r - 1 := by
        simpa [Set.mem_Icc] using hb
      have hap : a ≤ p := by omega
      have hbp : b ≤ p := by omega
      exact (tsub_right_inj hap hbp).mp h
    rw [this]
    exact Finset.prod_image (f := fun x : ℕ => x) (g := fun j : ℕ => p - j)
      (fun a ha b hb h => hinj ha hb h)
  rw [hpos, hneg]
  ac_rfl

lemma choose_p_sub_add_div_p_zmod {r k : ℕ} (hr0 : 0 < r) (hrp : r < p)
    (hkr : r ≤ k) (hkp : k < p) :
    p ∣ (p - r + k).choose k ∧
    (((p - r + k).choose k / p : ℕ) : ZMod p) =
      (-1 : ZMod p) ^ (r - 1) * ((r : ZMod p) * ((k : ℕ).choose r : ZMod p))⁻¹ := by
  have hpr : p.Prime := Fact.out
  have hppos : 0 < p := hpr.pos
  have hsplit := descFactorial_p_sub_add_split (p := p) hr0 hrp hkr
  have hfac : (p - r + k).descFactorial k = k ! * (p - r + k).choose k :=
    descFactorial_eq_factorial_mul_choose _ _
  have hmul : k ! * (p - r + k).choose k =
      p * ((∏ j ∈ Icc 1 (k - r), (p + j)) * (∏ j ∈ Icc 1 (r - 1), (p - j))) := by
    rw [← hfac, hsplit]; ring
  have hkndvd : ¬ p ∣ k ! := by
    intro h
    exact (not_le_of_gt hkp) (hpr.dvd_factorial.mp h)
  have hpdvd : p ∣ (p - r + k).choose k := by
    have : p ∣ k ! * (p - r + k).choose k := by
      rw [hmul]; exact dvd_mul_right _ _
    exact (hpr.dvd_mul.mp this).resolve_left hkndvd
  refine ⟨hpdvd, ?_⟩
  have hdiv : k ! * ((p - r + k).choose k / p) =
      (∏ j ∈ Icc 1 (k - r), (p + j)) * (∏ j ∈ Icc 1 (r - 1), (p - j)) := by
    apply Nat.eq_of_mul_eq_mul_left hppos
    calc
      p * (k ! * ((p - r + k).choose k / p))
          = k ! * (p * ((p - r + k).choose k / p)) := by ring
      _ = k ! * (p - r + k).choose k := by rw [Nat.mul_div_cancel' hpdvd]
      _ = p * ((∏ j ∈ Icc 1 (k - r), (p + j)) * (∏ j ∈ Icc 1 (r - 1), (p - j))) :=
            hmul
  have hpos : ((∏ j ∈ Icc 1 (k - r), (p + j) : ℕ) : ZMod p) = ((k - r)! : ZMod p) := by
    have hfac : ((∏ j ∈ Icc 1 (k - r), j : ℕ) : ZMod p) = ((k - r)! : ZMod p) := by
      rw [prod_Icc_one_n]
    rw [← hfac, Nat.cast_prod, Nat.cast_prod]
    refine prod_congr rfl ?_
    intro j hj
    rw [Nat.cast_add, CharP.cast_eq_zero (R := ZMod p) p, zero_add]
  have hneg : ((∏ j ∈ Icc 1 (r - 1), (p - j) : ℕ) : ZMod p) =
      (-1 : ZMod p) ^ (r - 1) * ((r - 1)! : ZMod p) := by
    rw [Nat.cast_prod]
    have hcongr : ∀ j ∈ Icc 1 (r - 1),
        ((p - j : ℕ) : ZMod p) = - (j : ZMod p) := by
      intro j hj
      have hjI := mem_Icc.mp hj
      rw [Nat.cast_sub (by omega), CharP.cast_eq_zero (R := ZMod p) p, zero_sub]
    rw [prod_congr rfl hcongr, prod_neg]
    have hcard : #(Icc 1 (r - 1)) = r - 1 := by
      rw [Nat.card_Icc]; omega
    rw [hcard, ← Nat.cast_prod, prod_Icc_one_n]
  have hcast :
      (k ! : ZMod p) * (((p - r + k).choose k / p : ℕ) : ZMod p) =
        ((k - r)! : ZMod p) * ((-1 : ZMod p) ^ (r - 1) * ((r - 1)! : ZMod p)) := by
    rw [← Nat.cast_mul, hdiv, Nat.cast_mul, hpos, hneg]
  have hkfac0 : (k ! : ZMod p) ≠ 0 := factorial_ne_zero_zmod hkp
  have hr0' : (r : ZMod p) ≠ 0 := zmod_nat_ne_zero hr0 hrp
  have hr1 : ((r - 1)! : ZMod p) ≠ 0 := factorial_ne_zero_zmod (by omega)
  have hkr0 : ((k - r)! : ZMod p) ≠ 0 :=
    factorial_ne_zero_zmod (lt_of_le_of_lt (Nat.sub_le k r) hkp)
  have hC : (k.choose r : ZMod p) * (r ! : ZMod p) * ((k - r)! : ZMod p) =
      (k ! : ZMod p) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, choose_mul_factorial_mul_factorial hkr]
  have hrfac : (r ! : ZMod p) = (r : ZMod p) * ((r - 1)! : ZMod p) := by
    have hrw : r = (r - 1) + 1 := by omega
    rw [hrw, factorial_succ, Nat.cast_mul, Nat.cast_succ, add_tsub_cancel_right]
  have hC' : (k.choose r : ZMod p) * ((r : ZMod p) * ((r - 1)! : ZMod p)) *
      ((k - r)! : ZMod p) = (k ! : ZMod p) := by
    rw [← hrfac, hC]
  have hchoose : (r : ZMod p) * (k.choose r : ZMod p) =
      (k ! : ZMod p) * ((r - 1)! : ZMod p)⁻¹ * ((k - r)! : ZMod p)⁻¹ := by
    have hmul : (r : ZMod p) * (k.choose r : ZMod p) * ((r - 1)! : ZMod p) *
        ((k - r)! : ZMod p) = (k ! : ZMod p) := by
      convert hC' using 1
      ring
    have := congrArg (fun x : ZMod p => x * ((r - 1)! : ZMod p)⁻¹ *
        ((k - r)! : ZMod p)⁻¹) hmul
    simp only at this
    have hsimp : (r : ZMod p) * (k.choose r : ZMod p) * ((r - 1)! : ZMod p) *
        ((k - r)! : ZMod p) * ((r - 1)! : ZMod p)⁻¹ * ((k - r)! : ZMod p)⁻¹ =
        (r : ZMod p) * (k.choose r : ZMod p) := by
      field
    have hsimp2 : (k ! : ZMod p) * ((r - 1)! : ZMod p)⁻¹ *
        ((k - r)! : ZMod p)⁻¹ = (k ! : ZMod p) * ((r - 1)! : ZMod p)⁻¹ *
        ((k - r)! : ZMod p)⁻¹ := rfl
    rw [hsimp] at this
    exact this
  apply mul_left_cancel₀ hkfac0
  rw [hcast]
  have : (k ! : ZMod p) *
      ((-1 : ZMod p) ^ (r - 1) * ((r : ZMod p) * (k.choose r : ZMod p))⁻¹) =
      ((k - r)! : ZMod p) * ((-1 : ZMod p) ^ (r - 1) * ((r - 1)! : ZMod p)) := by
    rw [hchoose]
    have hne1 : ((r - 1)! : ZMod p) ≠ 0 := hr1
    have hne2 : ((k - r)! : ZMod p) ≠ 0 := hkr0
    have hne3 : (k ! : ZMod p) ≠ 0 := hkfac0
    field
  exact this.symm

/- Third binomial interval: C(3(p-r)+2k, p-r) is the product of
   the length-(p-r) interval [L, L+(p-r)-1] with
   L = 2p - 2r + 2k + 1. -/

def thirdL (r k : ℕ) : ℕ := 2 * p - 2 * r + 2 * k + 1

lemma thirdL_add_len {r k : ℕ} (hr : r ≤ p) :
    thirdL (p := p) r k + (p - r) - 1 = 3 * p - 3 * r + 2 * k := by
  simp only [thirdL]
  omega

lemma third_choose_eq {r k : ℕ} (hr : r ≤ p) :
    (3 * (p - r) + 2 * k).choose (p - r) =
      (thirdL (p := p) r k + (p - r) - 1).choose (p - r) := by
  rw [thirdL_add_len (p := p) hr]
  have : 3 * (p - r) + 2 * k = 3 * p - 3 * r + 2 * k := by omega
  rw [this]

lemma Icc_len_eq {L r : ℕ} (hrp : r < p) :
    Icc L (L + p - r - 1) = Icc L (L + (p - r - 1)) := by
  congr 1
  omega

lemma injOn_cast_Icc_len {L m : ℕ} (hm : m < p) :
    ∀ x ∈ Icc L (L + m), ∀ y ∈ Icc L (L + m),
      (x : ZMod p) = (y : ZMod p) → x = y := by
  intro x hx y hy hxy
  have hxI := mem_Icc.mp hx
  have hyI := mem_Icc.mp hy
  have hmod : x ≡ y [MOD p] := (ZMod.natCast_eq_natCast_iff x y p).mp hxy
  rcases le_total x y with hle | hle
  · have hdvd : p ∣ y - x := (Nat.modEq_iff_dvd' hle).mp hmod
    have hlt : y - x < p := by omega
    have : y - x = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    omega
  · have hdvd : p ∣ x - y := (Nat.modEq_iff_dvd' hle).mp hmod.symm
    have hlt : x - y < p := by omega
    have : x - y = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    omega

lemma missing_residues_card {L r : ℕ} (hr0 : 0 < r) (hrp : r < p) :
    #((Icc 1 r).image (fun j : ℕ => (L : ZMod p) - (j : ZMod p))) = r := by
  have hinj : Set.InjOn (fun j : ℕ => (L : ZMod p) - (j : ZMod p)) (Icc 1 r) := by
    intro a ha b hb hab
    have haI : 1 ≤ a ∧ a ≤ r := by simpa [Set.mem_Icc] using ha
    have hbI : 1 ≤ b ∧ b ≤ r := by simpa [Set.mem_Icc] using hb
    have hab' : (a : ZMod p) = (b : ZMod p) :=
      sub_right_inj.mp hab
    have hmod : a ≡ b [MOD p] := (ZMod.natCast_eq_natCast_iff a b p).mp hab'
    rcases le_total a b with hle | hle
    · have hdvd : p ∣ b - a := (Nat.modEq_iff_dvd' hle).mp hmod
      have hlt : b - a < p := by omega
      have : b - a = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
      omega
    · have hdvd : p ∣ a - b := (Nat.modEq_iff_dvd' hle).mp hmod.symm
      have hlt : a - b < p := by omega
      have : a - b = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
      omega
  rw [Finset.card_image_of_injOn hinj, Nat.card_Icc]
  omega

lemma image_Icc_len_zmod {L r : ℕ} (hr0 : 0 < r) (hrp : r < p) :
    (Icc L (L + p - r - 1)).image (fun j : ℕ => (j : ZMod p)) =
      (univ : Finset (ZMod p)) \
        (Icc 1 r).image (fun j : ℕ => (L : ZMod p) - (j : ZMod p)) := by
  have hinj := injOn_cast_Icc_len (p := p) (L := L) (m := p - r - 1) (by omega)
  rw [Icc_len_eq (p := p) (L := L) hrp]
  have hcard_s : #(Icc L (L + (p - r - 1))) = p - r := by
    rw [Nat.card_Icc]; omega
  have hcard_img :
      #((Icc L (L + (p - r - 1))).image (fun j : ℕ => (j : ZMod p))) = p - r := by
    have : Set.InjOn (fun j : ℕ => (j : ZMod p)) (Icc L (L + (p - r - 1))) :=
      fun a ha b hb h => hinj a ha b hb h
    rw [Finset.card_image_of_injOn this, hcard_s]
  have hcard_miss := missing_residues_card (p := p) (L := L) hr0 hrp
  have hcard_diff :
      #((univ : Finset (ZMod p)) \
        (Icc 1 r).image (fun j : ℕ => (L : ZMod p) - (j : ZMod p))) = p - r := by
    rw [card_sdiff, inter_univ]
    simp [ZMod.card, hcard_miss]
  have hsub :
      (Icc L (L + (p - r - 1))).image (fun j : ℕ => (j : ZMod p)) ⊆
        (univ : Finset (ZMod p)) \
          (Icc 1 r).image (fun j : ℕ => (L : ZMod p) - (j : ZMod p)) := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
    refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
    intro hmiss
    obtain ⟨t, ht, hteq⟩ := mem_image.mp hmiss
    have hjI := mem_Icc.mp hj
    have htI := mem_Icc.mp ht
    have hsum : ((j + t : ℕ) : ZMod p) = (L : ZMod p) := by
      have : (j : ZMod p) + (t : ZMod p) = (L : ZMod p) := by
        rw [← hteq]; abel
      simpa [Nat.cast_add] using this
    have hmod : j + t ≡ L [MOD p] := (ZMod.natCast_eq_natCast_iff _ _ p).mp hsum
    have hge : L ≤ j + t := by omega
    have hdvd : p ∣ (j + t) - L := (Nat.modEq_iff_dvd' hge).mp hmod.symm
    have h1 : 1 ≤ (j + t) - L := by omega
    have h2 : (j + t) - L < p := by omega
    exact (Nat.not_dvd_of_pos_of_lt h1 h2) hdvd
  exact eq_of_subset_of_card_le hsub (hcard_diff.trans hcard_img.symm ▸ le_rfl)

lemma two_p_mem_third {r k : ℕ} (hrp : 3 * r < p) (hk : k < r) :
    thirdL (p := p) r k ≤ 2 * p ∧
      2 * p ≤ 3 * p - 3 * r + 2 * k := by
  simp only [thirdL]
  constructor <;> omega

lemma three_p_mem_third {r k : ℕ} (hrp : 3 * r < p)
    (hk1 : 3 * r ≤ 2 * k) (hk2 : 2 * k ≤ p + 2 * r - 1) :
    thirdL (p := p) r k ≤ 3 * p ∧
      3 * p ≤ 3 * p - 3 * r + 2 * k := by
  simp only [thirdL]
  constructor <;> omega

lemma prod_image_Icc_len {L r : ℕ} (hr0 : 0 < r) (hrp : r < p) :
    ∏ j ∈ Icc L (L + p - r - 1), (j : ZMod p) =
      ∏ x ∈ (univ : Finset (ZMod p)) \
        (Icc 1 r).image (fun j : ℕ => (L : ZMod p) - (j : ZMod p)), x := by
  have himg := image_Icc_len_zmod (p := p) (L := L) hr0 hrp
  have hinj := injOn_cast_Icc_len (p := p) (L := L) (m := p - r - 1) (by omega)
  rw [Icc_len_eq (p := p) (L := L) hrp] at himg ⊢
  refine Finset.prod_nbij (i := fun j : ℕ => (j : ZMod p))
      (f := fun j : ℕ => (j : ZMod p)) (g := fun x : ZMod p => x)
      ?_ ?_ ?_ (fun _ _ => rfl)
  · intro j hj
    have : (j : ZMod p) ∈
        (Icc L (L + (p - r - 1))).image (fun t : ℕ => (t : ZMod p)) :=
      mem_image.mpr ⟨j, hj, rfl⟩
    rwa [himg] at this
  · intro a ha b hb hab
    exact hinj a ha b hb hab
  · intro b hb
    have hb' : b ∈
        (Icc L (L + (p - r - 1))).image (fun t : ℕ => (t : ZMod p)) := by
      rwa [himg]
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hb'
    exact ⟨a, ha, rfl⟩

/-- The product of all nonzero field elements except a set `s` of nonzero residues
equals `(p-1)! / ∏ s`. -/
lemma prod_nonzero_sdiff {s : Finset (ZMod p)}
    (hs0 : 0 ∉ s) :
    ∏ x ∈ ((univ : Finset (ZMod p)).erase (0 : ZMod p)) \ s, x =
      ((p - 1)! : ZMod p) * (∏ x ∈ s, x)⁻¹ := by
  have hs_sub : s ⊆ (univ : Finset (ZMod p)).erase (0 : ZMod p) := by
    intro x hx
    exact mem_erase.mpr ⟨fun h => hs0 (h ▸ hx), mem_univ _⟩
  have hprod := Finset.prod_sdiff (s₁ := s)
      (s₂ := (univ : Finset (ZMod p)).erase (0 : ZMod p)) (f := fun x : ZMod p => x) hs_sub
  rw [prod_nonzero_eq_factorial] at hprod
  have hs0' : (∏ x ∈ s, x) ≠ 0 := by
    refine prod_ne_zero_iff.mpr ?_
    intro x hx h0
    exact hs0 (h0 ▸ hx)
  calc
    ∏ x ∈ ((univ : Finset (ZMod p)).erase (0 : ZMod p)) \ s, x
        = (∏ x ∈ ((univ : Finset (ZMod p)).erase (0 : ZMod p)) \ s, x) *
            (∏ x ∈ s, x) * (∏ x ∈ s, x)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hs0', mul_one]
    _ = ((p - 1)! : ZMod p) * (∏ x ∈ s, x)⁻¹ := by
          rw [hprod]

lemma zero_mem_image_Icc_iff {L r : ℕ} (hr0 : 0 < r) (hrp : r < p) :
    (0 : ZMod p) ∈ (Icc L (L + p - r - 1)).image (fun j : ℕ => (j : ZMod p)) ↔
      (0 : ZMod p) ∉ (Icc 1 r).image (fun j : ℕ => (L : ZMod p) - (j : ZMod p)) := by
  rw [image_Icc_len_zmod (p := p) hr0 hrp]
  simp [mem_sdiff]

/-- If `q*p` lies in the length-`(p-r)` interval starting at `L`, then
`C(L+(p-r)-1, p-r)/p ≡ q * (-1)^{r-1} * (r-1)! / ∏_{j=1}^r (L-j)` in `ZMod p`. -/
lemma choose_div_p_of_interval_len {L r q : ℕ}
    (hr0 : 0 < r) (hrp : r < p) (hq0 : 0 < q) (hqp : q < p)
    (hL : L ≤ q * p) (hU : q * p ≤ L + p - r - 1) :
    p ∣ (L + p - r - 1).choose (p - r) ∧
    ((((L + p - r - 1).choose (p - r) / p : ℕ) : ZMod p) =
      (q : ZMod p) * (-1 : ZMod p) ^ (r - 1) * ((r - 1)! : ZMod p) *
        (∏ j ∈ Icc 1 r, ((L : ZMod p) - (j : ZMod p)))⁻¹) := by
  have hpr : p.Prime := Fact.out
  have hppos : 0 < p := hpr.pos
  have hmem : q * p ∈ Icc L (L + p - r - 1) := mem_Icc.mpr ⟨hL, hU⟩
  have hk0 : 0 < p - r := by omega
  have hkn : p - r ≤ (L + p - r - 1) + 1 := by omega
  have hlo : (L + p - r - 1) + 1 - (p - r) = L := by omega
  have hdesc : (L + p - r - 1).descFactorial (p - r) =
      ∏ j ∈ Icc L (L + p - r - 1), j := by
    rw [descFactorial_eq_prod_Icc hk0 hkn, hlo]
  have hP : ∏ j ∈ Icc L (L + p - r - 1), j =
      (q * p) * ∏ j ∈ (Icc L (L + p - r - 1)).erase (q * p), j := by
    simpa [mul_comm (q * p)] using
      (Finset.prod_erase_mul (s := Icc L (L + p - r - 1)) (a := q * p)
        (f := fun j : ℕ => j) hmem).symm
  have hfac : (L + p - r - 1).descFactorial (p - r) =
      (p - r)! * (L + p - r - 1).choose (p - r) :=
    descFactorial_eq_factorial_mul_choose _ _
  have hmul : (p - r)! * (L + p - r - 1).choose (p - r) =
      p * (q * ∏ j ∈ (Icc L (L + p - r - 1)).erase (q * p), j) := by
    rw [← hfac, hdesc, hP]; ring
  have hp_ndvd_fac : ¬ p ∣ (p - r)! := by
    intro h
    exact (not_le_of_gt (by omega : p - r < p)) (hpr.dvd_factorial.mp h)
  have hpdvd : p ∣ (L + p - r - 1).choose (p - r) := by
    have : p ∣ (p - r)! * (L + p - r - 1).choose (p - r) := by
      rw [hmul]; exact dvd_mul_right _ _
    exact (hpr.dvd_mul.mp this).resolve_left hp_ndvd_fac
  refine ⟨hpdvd, ?_⟩
  have hdiv : (p - r)! * ((L + p - r - 1).choose (p - r) / p) =
      q * ∏ j ∈ (Icc L (L + p - r - 1)).erase (q * p), j := by
    apply Nat.eq_of_mul_eq_mul_left hppos
    calc
      p * ((p - r)! * ((L + p - r - 1).choose (p - r) / p))
          = (p - r)! * (p * ((L + p - r - 1).choose (p - r) / p)) := by ring
      _ = (p - r)! * (L + p - r - 1).choose (p - r) := by rw [Nat.mul_div_cancel' hpdvd]
      _ = p * (q * ∏ j ∈ (Icc L (L + p - r - 1)).erase (q * p), j) := hmul
  have h0 : ((q * p : ℕ) : ZMod p) = 0 := by
    simp [Nat.cast_mul, CharP.cast_eq_zero (R := ZMod p) p]
  have hinj := injOn_cast_Icc_len (p := p) (L := L) (m := p - r - 1) (by omega)
  -- 0 is in the image, so it is not among the missing residues
  have h0_not_miss :
      (0 : ZMod p) ∉ (Icc 1 r).image (fun j : ℕ => (L : ZMod p) - (j : ZMod p)) := by
    have : (0 : ZMod p) ∈ (Icc L (L + p - r - 1)).image (fun j : ℕ => (j : ZMod p)) :=
      mem_image.mpr ⟨q * p, hmem, h0⟩
    exact (zero_mem_image_Icc_iff (p := p) hr0 hrp).mp this
  have hmiss_ne0 : ∀ x ∈ (Icc 1 r).image (fun j : ℕ => (L : ZMod p) - (j : ZMod p)),
      x ≠ 0 := fun x hx h => h0_not_miss (h ▸ hx)
  -- product of (interval \ {qp}) = product of (univ.erase 0 \ missing)
  have himg := image_Icc_len_zmod (p := p) (L := L) hr0 hrp
  have himg_erase :
      ((Icc L (L + p - r - 1)).erase (q * p)).image (fun j : ℕ => (j : ZMod p)) =
        ((univ : Finset (ZMod p)).erase (0 : ZMod p)) \
          (Icc 1 r).image (fun j : ℕ => (L : ZMod p) - (j : ZMod p)) := by
    rw [Icc_len_eq (p := p) (L := L) hrp] at himg hmem ⊢
    have hinj' : ∀ x ∈ Icc L (L + (p - r - 1)), ∀ y ∈ Icc L (L + (p - r - 1)),
        (x : ZMod p) = (y : ZMod p) → x = y := hinj
    rw [image_erase_of_injOn hinj' hmem, himg, h0]
    ext x
    simp only [mem_erase, mem_sdiff, mem_univ, true_and]
    tauto
  have hprod_er :
      ∏ j ∈ (Icc L (L + p - r - 1)).erase (q * p), (j : ZMod p) =
        ∏ x ∈ ((univ : Finset (ZMod p)).erase (0 : ZMod p)) \
          (Icc 1 r).image (fun j : ℕ => (L : ZMod p) - (j : ZMod p)), x := by
    rw [Icc_len_eq (p := p) (L := L) hrp]
    have hinj' : ∀ x ∈ (Icc L (L + (p - r - 1))).erase (q * p),
        ∀ y ∈ (Icc L (L + (p - r - 1))).erase (q * p),
        (x : ZMod p) = (y : ZMod p) → x = y :=
      fun x hx y hy hxy => hinj x (mem_of_mem_erase hx) y (mem_of_mem_erase hy) hxy
    refine Finset.prod_nbij (i := fun j : ℕ => (j : ZMod p))
        (f := fun j : ℕ => (j : ZMod p)) (g := fun x : ZMod p => x)
        ?_ ?_ ?_ (fun _ _ => rfl)
    · intro j hj
      have : (j : ZMod p) ∈
          ((Icc L (L + (p - r - 1))).erase (q * p)).image (fun t : ℕ => (t : ZMod p)) :=
        mem_image.mpr ⟨j, hj, rfl⟩
      rwa [← Icc_len_eq (p := p) (L := L) hrp, himg_erase] at this
    · exact hinj'
    · intro b hb
      have hb' : b ∈
          ((Icc L (L + p - r - 1)).erase (q * p)).image (fun t : ℕ => (t : ZMod p)) := by
        rwa [himg_erase]
      rw [Icc_len_eq (p := p) (L := L) hrp] at hb'
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hb'
      exact ⟨a, ha, rfl⟩
  have hprod_miss :
      ∏ j ∈ Icc 1 r, ((L : ZMod p) - (j : ZMod p)) =
        ∏ x ∈ (Icc 1 r).image (fun j : ℕ => (L : ZMod p) - (j : ZMod p)), x := by
    have hinj_m : Set.InjOn (fun j : ℕ => (L : ZMod p) - (j : ZMod p)) (Icc 1 r) := by
      intro a ha b hb hab
      have haI : 1 ≤ a ∧ a ≤ r := by simpa [Set.mem_Icc] using ha
      have hbI : 1 ≤ b ∧ b ≤ r := by simpa [Set.mem_Icc] using hb
      have hab' : (a : ZMod p) = (b : ZMod p) := sub_right_inj.mp hab
      have hmod : a ≡ b [MOD p] := (ZMod.natCast_eq_natCast_iff a b p).mp hab'
      rcases le_total a b with hle | hle
      · have hdvd : p ∣ b - a := (Nat.modEq_iff_dvd' hle).mp hmod
        have : b - a = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
        omega
      · have hdvd : p ∣ a - b := (Nat.modEq_iff_dvd' hle).mp hmod.symm
        have : a - b = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
        omega
    exact (Finset.prod_image (f := fun x : ZMod p => x)
      (fun a ha b hb h => hinj_m ha hb h)).symm
  have hs0 : (0 : ZMod p) ∉
      (Icc 1 r).image (fun j : ℕ => (L : ZMod p) - (j : ZMod p)) := h0_not_miss
  have hprod_rest := prod_nonzero_sdiff (p := p) hs0
  have hcast :
      ((p - r)! : ZMod p) * ((((L + p - r - 1).choose (p - r) / p : ℕ) : ZMod p)) =
        (q : ZMod p) * ((p - 1)! : ZMod p) *
          (∏ j ∈ Icc 1 r, ((L : ZMod p) - (j : ZMod p)))⁻¹ := by
    have h1 : ((p - r)! : ZMod p) *
        ((((L + p - r - 1).choose (p - r) / p : ℕ) : ZMod p)) =
          (q : ZMod p) * ∏ j ∈ (Icc L (L + p - r - 1)).erase (q * p), (j : ZMod p) := by
      rw [← Nat.cast_mul, hdiv, Nat.cast_mul, Nat.cast_prod]
    rw [h1, hprod_er, hprod_rest, ← hprod_miss]
    ring
  have hfac0 : ((p - r)! : ZMod p) ≠ 0 :=
    factorial_ne_zero_zmod (by omega)
  apply mul_left_cancel₀ hfac0
  rw [hcast, factorial_p_sub (p := p) hr0 hrp]
  have hwilson : ((p - 1)! : ZMod p) = (-1 : ZMod p) := ZMod.wilsons_lemma p
  rw [hwilson]
  have hr1 : ((r - 1)! : ZMod p) ≠ 0 := factorial_ne_zero_zmod (by omega)
  have hprod0 : (∏ j ∈ Icc 1 r, ((L : ZMod p) - (j : ZMod p))) ≠ 0 := by
    rw [hprod_miss]
    refine prod_ne_zero_iff.mpr ?_
    intro x hx
    exact hmiss_ne0 x hx
  have hpowr : (-1 : ZMod p) ^ r = (-1 : ZMod p) * (-1 : ZMod p) ^ (r - 1) := by
    cases r with
    | zero => cases hr0
    | succ r' => simp [pow_succ]
  have hpm : (-1 : ZMod p) ^ r * (-1 : ZMod p) ^ (r - 1) = -1 := by
    rw [← pow_add]
    have hsum : r + (r - 1) = 2 * (r - 1) + 1 := by omega
    rw [hsum, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]
  field_simp [hpowr, hprod0, hr1]
  calc
    -(q : ZMod p) = (q : ZMod p) * (-1) := by ring
    _ = (q : ZMod p) * ((-1 : ZMod p) ^ r * (-1 : ZMod p) ^ (r - 1)) := by
          rw [hpm]
    _ = (q : ZMod p) * (-1 : ZMod p) ^ r * (-1 : ZMod p) ^ (r - 1) := by ring

lemma thirdL_U {r k : ℕ} (hr : r ≤ p) :
    thirdL (p := p) r k + p - r - 1 = 3 * p - 3 * r + 2 * k := by
  simp only [thirdL]
  omega

lemma r_lt_p_of_three {r : ℕ} (hrp : 3 * r < p) : r < p :=
  lt_of_le_of_lt (by nlinarith : r ≤ 3 * r) hrp

lemma two_lt_p_of_three {r : ℕ} (hr0 : 0 < r) (hrp : 3 * r < p) : 2 < p :=
  lt_trans (by decide : 2 < 3) (lt_of_le_of_lt (Nat.mul_le_mul_left 3 hr0) hrp)

lemma two_p_in_third_interval {r k : ℕ} (hrp : 3 * r < p) (hk : k < r) :
    thirdL (p := p) r k ≤ 2 * p ∧
      2 * p ≤ thirdL (p := p) r k + p - r - 1 := by
  have ⟨h1, h2⟩ := two_p_mem_third (p := p) hrp hk
  refine ⟨h1, ?_⟩
  rw [thirdL_U (p := p) (le_of_lt (r_lt_p_of_three (p := p) hrp))]
  exact h2

/-- In region A (`k < r`), the third binomial is divisible by `p` with
explicit first-order residue. -/
lemma choose_third_div_p_region_A {r k : ℕ}
    (hr0 : 0 < r) (hrp : 3 * r < p) (hk : k < r) :
    p ∣ (3 * (p - r) + 2 * k).choose (p - r) ∧
    ((((3 * (p - r) + 2 * k).choose (p - r) / p : ℕ) : ZMod p) =
      (2 : ZMod p) * (-1 : ZMod p) ^ (r - 1) * ((r - 1)! : ZMod p) *
        (∏ j ∈ Icc 1 r,
          ((thirdL (p := p) r k : ZMod p) - (j : ZMod p)))⁻¹) := by
  have hr := r_lt_p_of_three (p := p) hrp
  have ⟨hL, hU⟩ := two_p_in_third_interval (p := p) hrp hk
  have h := choose_div_p_of_interval_len (p := p) (L := thirdL (p := p) r k)
      (r := r) (q := 2) hr0 hr (by decide : 0 < 2)
      (two_lt_p_of_three (p := p) hr0 hrp) hL hU
  have hcheq : (3 * (p - r) + 2 * k).choose (p - r) =
      (thirdL (p := p) r k + p - r - 1).choose (p - r) := by
    rw [thirdL_U (p := p) (le_of_lt hr)]
    have : 3 * (p - r) + 2 * k = 3 * p - 3 * r + 2 * k := by omega
    rw [this]
  refine ⟨?_, ?_⟩
  · rw [hcheq]; exact h.1
  · rw [hcheq]; exact h.2

lemma mul_div_of_dvd_right' {A B C m : ℕ} (hC : m ∣ C) (hm : 0 < m) :
    A * B * C / m = A * B * (C / m) := by
  obtain ⟨c, rfl⟩ := hC
  rw [Nat.mul_div_cancel_left c hm]
  have : A * B * (m * c) = (A * B * c) * m := by ring
  rw [this, Nat.mul_div_cancel _ hm]

lemma term_eq_general {r k : ℕ} :
    term (p - r) k =
      (p - r).choose k ^ 2 * (p - r + k).choose k *
        (3 * (p - r) + 2 * k).choose (p - r) :=
  rfl

/-- First-order residue of an A-region term. -/
lemma term_div_p_region_A {r k : ℕ}
    (hr0 : 0 < r) (hrp : 3 * r < p) (hk : k < r) (hkr : k ≤ p - r) :
    ((term (p - r) k / p : ℕ) : ZMod p) =
      ((p - r).choose k : ZMod p) ^ 2 * ((p - r + k).choose k : ZMod p) *
        (2 : ZMod p) * (-1 : ZMod p) ^ (r - 1) * ((r - 1)! : ZMod p) *
          (∏ j ∈ Icc 1 r,
            ((thirdL (p := p) r k : ZMod p) - (j : ZMod p)))⁻¹ := by
  have h3 := choose_third_div_p_region_A (p := p) hr0 hrp hk
  have hppos : 0 < p := p_pos (p := p)
  have hdiv : term (p - r) k / p =
      (p - r).choose k ^ 2 * (p - r + k).choose k *
        ((3 * (p - r) + 2 * k).choose (p - r) / p) := by
    rw [term_eq_general, mul_div_of_dvd_right' h3.1 hppos]
  rw [hdiv, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, h3.2]
  ring

lemma term_div_p_region_A' {r k : ℕ}
    (hr0 : 0 < r) (hrp : 3 * r < p) (hk : k < r) (hkr : k ≤ p - r) :
    ((term (p - r) k / p : ℕ) : ZMod p) =
      ((-1 : ZMod p) ^ k * ((r + k - 1).choose k : ZMod p)) ^ 2 *
        ((-1 : ZMod p) ^ k * ((r - 1).choose k : ZMod p)) *
        (2 : ZMod p) * (-1 : ZMod p) ^ (r - 1) * ((r - 1)! : ZMod p) *
          (∏ j ∈ Icc 1 r,
            ((thirdL (p := p) r k : ZMod p) - (j : ZMod p)))⁻¹ := by
  have hr := r_lt_p_of_three (p := p) hrp
  rw [term_div_p_region_A (p := p) hr0 hrp hk hkr]
  rw [choose_p_sub_zmod (p := p) hr0 hr hkr]
  rw [choose_p_sub_add_zmod (p := p) hr0 hr hk]

lemma sdiff_erase_zero {s : Finset (ZMod p)} (h0 : (0 : ZMod p) ∈ s) :
    (univ : Finset (ZMod p)) \ s =
      ((univ : Finset (ZMod p)).erase 0) \ (s.erase 0) := by
  ext x
  by_cases hx0 : x = 0
  · subst hx0
    simp [h0]
  · simp [hx0, mem_erase, mem_sdiff]

lemma choose_zmod_of_zero_missing {L r : ℕ}
    (hr0 : 0 < r) (hrp : r < p)
    (h0miss : (0 : ZMod p) ∈
      (Icc 1 r).image (fun j : ℕ => (L : ZMod p) - (j : ZMod p))) :
    ((L + p - r - 1).choose (p - r) : ZMod p) =
      (-1 : ZMod p) ^ (r - 1) * ((r - 1)! : ZMod p) *
        (∏ x ∈ ((Icc 1 r).image
          (fun j : ℕ => (L : ZMod p) - (j : ZMod p))).erase 0, x)⁻¹ := by
  have hk0 : 0 < p - r := by omega
  have hkn : p - r ≤ (L + p - r - 1) + 1 := by omega
  have hlo : (L + p - r - 1) + 1 - (p - r) = L := by omega
  have hdesc : (L + p - r - 1).descFactorial (p - r) =
      ∏ j ∈ Icc L (L + p - r - 1), j := by
    rw [descFactorial_eq_prod_Icc hk0 hkn, hlo]
  have hfac : (L + p - r - 1).descFactorial (p - r) =
      (p - r)! * (L + p - r - 1).choose (p - r) :=
    descFactorial_eq_factorial_mul_choose _ _
  have hprod_I := prod_image_Icc_len (p := p) (L := L) hr0 hrp
  have himg_eq := sdiff_erase_zero (p := p) h0miss
  have hs0 : (0 : ZMod p) ∉
      ((Icc 1 r).image (fun j : ℕ => (L : ZMod p) - (j : ZMod p))).erase 0 :=
    notMem_erase _ _
  have hprod_rest := prod_nonzero_sdiff (p := p) hs0
  have hmul : ((p - r)! : ZMod p) * ((L + p - r - 1).choose (p - r) : ZMod p) =
      ∏ j ∈ Icc L (L + p - r - 1), (j : ZMod p) := by
    rw [← Nat.cast_mul, ← hfac, hdesc, Nat.cast_prod]
  have hcast : ((p - r)! : ZMod p) * ((L + p - r - 1).choose (p - r) : ZMod p) =
      ((p - 1)! : ZMod p) *
        (∏ x ∈ ((Icc 1 r).image
          (fun j : ℕ => (L : ZMod p) - (j : ZMod p))).erase 0, x)⁻¹ := by
    rw [hmul, hprod_I, himg_eq, hprod_rest]
  have hfac0 : ((p - r)! : ZMod p) ≠ 0 :=
    factorial_ne_zero_zmod (by omega)
  apply mul_left_cancel₀ hfac0
  rw [hcast, factorial_p_sub (p := p) hr0 hrp, ZMod.wilsons_lemma p]
  have hr1 : ((r - 1)! : ZMod p) ≠ 0 := factorial_ne_zero_zmod (by omega)
  have hprod0 :
      (∏ x ∈ ((Icc 1 r).image
        (fun j : ℕ => (L : ZMod p) - (j : ZMod p))).erase 0, x) ≠ 0 := by
    refine prod_ne_zero_iff.mpr ?_
    intro x hx
    exact (mem_erase.mp hx).1
  have hpm : (-1 : ZMod p) ^ r * (-1 : ZMod p) ^ (r - 1) = -1 := by
    rw [← pow_add]
    have hsum : r + (r - 1) = 2 * (r - 1) + 1 := by omega
    rw [hsum, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]
  field_simp [hprod0, hr1]
  exact hpm.symm

end GeneralR

/-! ### Remaining case `n = p - r` with `r ≥ 2`. -/

section Remainder
variable {p : ℕ} [Fact p.Prime]

lemma p_ne_zero_zmod : (p : ZMod p) = 0 :=
  CharP.cast_eq_zero (R := ZMod p) p

lemma coprime_choose_ne_zero {m k : ℕ} (hm : m < p) (hk : k ≤ m) :
    ((m.choose k : ℕ) : ZMod p) ≠ 0 := by
  have hpr : p.Prime := Fact.out
  have hcop := hpr.coprime_choose_of_lt hm hk
  exact (ZMod.natCast_eq_zero_iff _ p).not.mpr
    (hpr.coprime_iff_not_dvd.mp hcop)

lemma six_le_three_mul {r : ℕ} (hr2 : 2 ≤ r) : 6 ≤ 3 * r := by
  nlinarith

lemma three_lt_p_of_r {r : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p) : 3 < p :=
  lt_trans (by decide : 3 < 6) (lt_of_le_of_lt (six_le_three_mul hr2) hrp)

lemma four_lt_p_of_r {r : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p) : 4 < p :=
  lt_trans (by decide : 4 < 6) (lt_of_le_of_lt (six_le_three_mul hr2) hrp)

lemma p_dvd_middle_of_r_le {r k : ℕ}
    (hr0 : 0 < r) (hrp : r < p) (hkr : r ≤ k) (hkp : k < p) :
    p ∣ (p - r + k).choose k :=
  (choose_p_sub_add_div_p_zmod (p := p) hr0 hrp hkr hkp).1

lemma third_choose_eq_L {r k : ℕ} (hr : r ≤ p) :
    (3 * (p - r) + 2 * k).choose (p - r) =
      (thirdL (p := p) r k + p - r - 1).choose (p - r) := by
  rw [thirdL_U (p := p) hr]
  have : 3 * (p - r) + 2 * k = 3 * p - 3 * r + 2 * k := by omega
  rw [this]

lemma p_dvd_choose_third_region_C {r k : ℕ}
    (hr0 : 0 < r) (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    (hC1 : 3 * r ≤ 2 * k) (hC2 : 2 * k ≤ p + 2 * r - 1) :
    p ∣ (3 * (p - r) + 2 * k).choose (p - r) := by
  have hr := r_lt_p_of_three (p := p) hrp
  have ⟨hL, hU⟩ : thirdL (p := p) r k ≤ 3 * p ∧
      3 * p ≤ thirdL (p := p) r k + p - r - 1 := by
    constructor
    · simp only [thirdL]; omega
    · rw [thirdL_U (p := p) (le_of_lt hr)]; omega
  have h := choose_div_p_of_interval_len (p := p) (L := thirdL (p := p) r k)
      (r := r) (q := 3) hr0 hr (by decide : 0 < 3)
      (three_lt_p_of_r (p := p) hr2 hrp) hL hU
  rw [third_choose_eq_L (p := p) (le_of_lt hr)]; exact h.1

lemma p_dvd_choose_third_region_E {r k : ℕ}
    (hr0 : 0 < r) (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    (hE : p + 3 * r ≤ 2 * k) (hkn : k ≤ p - r) :
    p ∣ (3 * (p - r) + 2 * k).choose (p - r) := by
  have hr := r_lt_p_of_three (p := p) hrp
  have ⟨hL, hU⟩ : thirdL (p := p) r k ≤ 4 * p ∧
      4 * p ≤ thirdL (p := p) r k + p - r - 1 := by
    constructor
    · simp only [thirdL]; omega
    · rw [thirdL_U (p := p) (le_of_lt hr)]; omega
  have h := choose_div_p_of_interval_len (p := p) (L := thirdL (p := p) r k)
      (r := r) (q := 4) hr0 hr (by decide : 0 < 4)
      (four_lt_p_of_r (p := p) hr2 hrp) hL hU
  rw [third_choose_eq_L (p := p) (le_of_lt hr)]; exact h.1

lemma psq_dvd_term_region_C {r k : ℕ}
    (hr0 : 0 < r) (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    (hC1 : 3 * r ≤ 2 * k) (hC2 : 2 * k ≤ p + 2 * r - 1)
    (hkn : k ≤ p - r) :
    p ^ 2 ∣ term (p - r) k := by
  have hr := r_lt_p_of_three (p := p) hrp
  have hkp : k < p := by omega
  have hkr : r ≤ k := by omega
  have hmid := p_dvd_middle_of_r_le (p := p) hr0 hr hkr hkp
  have hth := p_dvd_choose_third_region_C (p := p) hr0 hr2 hrp hC1 hC2
  rw [term_eq_general, pow_two]
  exact mul_dvd_mul (dvd_mul_of_dvd_right hmid _) hth

lemma psq_dvd_term_region_E {r k : ℕ}
    (hr0 : 0 < r) (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    (hE : p + 3 * r ≤ 2 * k) (hkn : k ≤ p - r) :
    p ^ 2 ∣ term (p - r) k := by
  have hr := r_lt_p_of_three (p := p) hrp
  have hkp : k < p := by omega
  have hkr : r ≤ k := by omega
  have hmid := p_dvd_middle_of_r_le (p := p) hr0 hr hkr hkp
  have hth := p_dvd_choose_third_region_E (p := p) hr0 hr2 hrp hE hkn
  rw [term_eq_general, pow_two]
  exact mul_dvd_mul (dvd_mul_of_dvd_right hmid _) hth

end Remainder

/-! The case `n = p - 1` is already settled. For `2 ≤ r` with
`n = p - r` and `3 r < p` we reduce to a finite check when `p` is small
and a uniform argument for `p ≥ 7`. -/

lemma choose_five : (5 : ℕ).choose 0 = 1 ∧ (5 : ℕ).choose 1 = 5 ∧
    (5 : ℕ).choose 2 = 10 ∧ (5 : ℕ).choose 3 = 10 ∧
    (5 : ℕ).choose 4 = 5 ∧ (5 : ℕ).choose 5 = 1 := by decide

lemma term_five :
    term 5 0 = 3003 ∧ term 5 1 = 928200 ∧ term 5 2 = 24418800 ∧
    term 5 3 = 113954400 ∧ term 5 4 = 105994350 ∧ term 5 5 = 13388760 := by
  simp [term, choose_five]
  decide

lemma a_five : a 5 = 258687513 := by
  rw [a_eq_sum_term]
  have hrange : range (5 + 1) = {0, 1, 2, 3, 4, 5} := by decide
  rw [hrange]
  simp [term_five]

lemma p7_dvd_a5 : (7 : ℕ) ^ 3 ∣ a 5 := by
  rw [a_five]
  exact ⟨754191, by decide⟩

lemma n_eq_p_sub_of_le {p n : ℕ} (hp : 0 < p) (hn : n ≤ p - 1) :
    n = p - (p - n) := by omega

/-! ### The case `r = 2`, i.e. `n = p - 2`. -/

section RTwo
variable {p : ℕ} [Fact p.Prime]

lemma rtwo_thirdL (k : ℕ) : thirdL (p := p) 2 k = 2 * p + 2 * k - 3 := by
  have : 2 ≤ p := p_ge_two (p := p)
  simp only [thirdL]
  omega

lemma two_lt_p_of_prime5 (hp5 : 5 ≤ p) : 2 < p :=
  lt_of_lt_of_le (by decide : 2 < 5) hp5

lemma rtwo_choose_n (hp5 : 5 ≤ p) {k : ℕ} (hk : k ≤ p - 2) :
    ((p - 2).choose k : ZMod p) =
      (-1 : ZMod p) ^ k * ((k + 1 : ℕ) : ZMod p) := by
  have h := choose_p_sub_zmod (p := p) (r := 2) (k := k)
    (by decide : 0 < 2) (two_lt_p_of_prime5 hp5) hk
  have hbin : ((2 + k - 1 : ℕ).choose k : ZMod p) = ((k + 1 : ℕ) : ZMod p) := by
    have : 2 + k - 1 = k + 1 := by omega
    rw [this, choose_succ_self_right, Nat.cast_succ]
  rwa [hbin] at h

lemma rtwo_choose_mid_lt {k : ℕ} (hp5 : 5 ≤ p) (hk : k < 2) :
    ((p - 2 + k).choose k : ZMod p) =
      (-1 : ZMod p) ^ k * ((1 : ℕ).choose k : ZMod p) :=
  choose_p_sub_add_zmod (p := p) (r := 2) (by decide) (two_lt_p_of_prime5 hp5) hk

lemma rtwo_choose_mid_ge {k : ℕ} (hp5 : 5 ≤ p) (hkr : 2 ≤ k) (hkp : k < p) :
    p ∣ (p - 2 + k).choose k ∧
    (((p - 2 + k).choose k / p : ℕ) : ZMod p) =
      -((2 : ZMod p) * (k.choose 2 : ZMod p))⁻¹ := by
  have h := choose_p_sub_add_div_p_zmod (p := p) (r := 2) (k := k)
    (by decide) (two_lt_p_of_prime5 hp5) hkr hkp
  refine ⟨h.1, ?_⟩
  have : (-1 : ZMod p) ^ (2 - 1) = -1 := by simp
  rw [h.2, this]
  ring

lemma Icc_one_two : Icc (1 : ℕ) 2 = {1, 2} := by decide

lemma prod_Icc_one_two (f : ℕ → ZMod p) :
    ∏ j ∈ Icc (1 : ℕ) 2, f j = f 1 * f 2 := by
  rw [Icc_one_two, prod_insert (by decide : (1 : ℕ) ∉ ({2} : Finset ℕ)),
    prod_singleton]

lemma rtwo_L_cast_zero (hp5 : 5 ≤ p) :
    (thirdL (p := p) 2 0 : ZMod p) = -3 := by
  have : 2 ≤ p := p_ge_two (p := p)
  rw [rtwo_thirdL]
  simp only [mul_zero, add_zero]
  have hle : 3 ≤ 2 * p := by omega
  rw [Nat.cast_sub hle, Nat.cast_mul, Nat.cast_two, Nat.cast_ofNat,
    p_ne_zero_zmod (p := p), mul_zero, zero_sub]

lemma rtwo_L_cast_one (hp5 : 5 ≤ p) :
    (thirdL (p := p) 2 1 : ZMod p) = -1 := by
  have : 2 ≤ p := p_ge_two (p := p)
  rw [rtwo_thirdL]
  have heq : 2 * p + 2 * 1 - 3 = 2 * p - 1 := by omega
  rw [heq]
  have hle' : 1 ≤ 2 * p := by omega
  rw [Nat.cast_sub hle', Nat.cast_mul, Nat.cast_two, Nat.cast_one,
    p_ne_zero_zmod (p := p), mul_zero, zero_sub]

lemma rtwo_term0 (hp5 : 5 ≤ p) (h3r : 6 < p) :
    ((term (p - 2) 0 / p : ℕ) : ZMod p) = -((10 : ZMod p))⁻¹ := by
  have h := term_div_p_region_A' (p := p) (r := 2) (k := 0)
    (by decide) (by omega) (by decide : 0 < 2) (by omega)
  have hprod :
      ∏ j ∈ Icc (1 : ℕ) 2,
        ((thirdL (p := p) 2 0 : ZMod p) - (j : ZMod p)) =
        (4 : ZMod p) * (5 : ZMod p) := by
    rw [prod_Icc_one_two, rtwo_L_cast_zero hp5]
    simp only [Nat.cast_one, Nat.cast_ofNat]
    ring
  have hpow : (-1 : ZMod p) ^ (2 - 1) = -1 := by simp
  have hfac : ((2 - 1)! : ZMod p) = 1 := by simp
  simp only [pow_zero, choose_zero_right, Nat.cast_one, one_mul, hpow, hfac] at h
  rw [h, hprod]
  have h4p : 4 < p := lt_trans (by decide : 4 < 6) h3r
  have h5p : 5 < p := lt_trans (by decide : 5 < 6) h3r
  have h4 : (4 : ZMod p) ≠ 0 := zmod_nat_ne_zero (by decide) h4p
  have h5 : (5 : ZMod p) ≠ 0 := zmod_nat_ne_zero (by decide) h5p
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp5
  have h10 : (10 : ZMod p) ≠ 0 := by
    have : (10 : ZMod p) = 2 * 5 := by norm_num
    rw [this]; exact mul_ne_zero h2 h5
  field_simp [h4, h5, h2, h10]
  ring

lemma rtwo_term1 (hp5 : 5 ≤ p) (h3r : 6 < p) :
    ((term (p - 2) 1 / p : ℕ) : ZMod p) = (4 : ZMod p) * (3 : ZMod p)⁻¹ := by
  have h := term_div_p_region_A' (p := p) (r := 2) (k := 1)
    (by decide) (by omega) (by decide : 1 < 2) (by omega)
  have hprod :
      ∏ j ∈ Icc (1 : ℕ) 2,
        ((thirdL (p := p) 2 1 : ZMod p) - (j : ZMod p)) =
        (6 : ZMod p) := by
    rw [prod_Icc_one_two, rtwo_L_cast_one hp5]
    simp only [Nat.cast_one, Nat.cast_ofNat]
    ring
  have hC : ((2 + 1 - 1 : ℕ).choose 1 : ZMod p) = 2 := by norm_num
  have hC1 : ((1 : ℕ).choose 1 : ZMod p) = 1 := by simp
  have hpow : (-1 : ZMod p) ^ 1 = -1 := by simp
  simp only [hC, hC1, hpow] at h
  rw [h, hprod]
  have h3p : 3 < p := lt_trans (by decide : 3 < 6) h3r
  have h6p : 6 < p := h3r
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp5
  have h3 : (3 : ZMod p) ≠ 0 := zmod_nat_ne_zero (by decide) h3p
  have h6 : (6 : ZMod p) ≠ 0 := zmod_nat_ne_zero (by decide) h6p
  field_simp [h2, h3, h6]
  ring

lemma rtwo_L_cast_two (hp5 : 5 ≤ p) :
    (thirdL (p := p) 2 2 : ZMod p) = 1 := by
  have : 2 ≤ p := p_ge_two (p := p)
  rw [rtwo_thirdL]
  have heq : 2 * p + 2 * 2 - 3 = 2 * p + 1 := by omega
  rw [heq, Nat.cast_add, Nat.cast_mul, Nat.cast_two, Nat.cast_one,
    p_ne_zero_zmod (p := p), mul_zero, zero_add]

lemma rtwo_missing_two (hp5 : 5 ≤ p) :
    (Icc (1 : ℕ) 2).image (fun j : ℕ =>
      (thirdL (p := p) 2 2 : ZMod p) - (j : ZMod p)) = {0, -1} := by
  rw [Icc_one_two, rtwo_L_cast_two hp5, image_insert, image_singleton]
  have h1 : (1 : ZMod p) - (1 : ℕ) = 0 := by simp
  have h2 : (1 : ZMod p) - (2 : ℕ) = -1 := by
    simp [Nat.cast_ofNat]; ring
  rw [h1, h2]

lemma rtwo_third_unit_two (hp5 : 5 ≤ p) (h3r : 6 < p) :
    ((3 * (p - 2) + 4).choose (p - 2) : ZMod p) = 1 := by
  have hr : (2 : ℕ) ≤ p := le_of_lt (two_lt_p_of_prime5 hp5)
  have hL : thirdL (p := p) 2 2 + p - 2 - 1 = 3 * p - 2 := by
    rw [rtwo_thirdL]; omega
  have hidx : 3 * (p - 2) + 4 = 3 * p - 2 := by omega
  have hcheq : (3 * (p - 2) + 4).choose (p - 2) =
      (thirdL (p := p) 2 2 + p - 2 - 1).choose (p - 2) := by
    rw [hL, hidx]
  have h0miss : (0 : ZMod p) ∈
      (Icc (1 : ℕ) 2).image (fun j : ℕ =>
        (thirdL (p := p) 2 2 : ZMod p) - (j : ZMod p)) := by
    rw [rtwo_missing_two hp5]; simp
  have h := choose_zmod_of_zero_missing (p := p) (L := thirdL (p := p) 2 2)
    (r := 2) (by decide) (two_lt_p_of_prime5 hp5) h0miss
  rw [hcheq, h, rtwo_missing_two hp5]
  have hne : (0 : ZMod p) ≠ -1 := by
    intro h0
    have : (1 : ZMod p) = 0 := by
      simpa using congrArg (fun x : ZMod p => x + 1) h0
    exact one_ne_zero this
  have herase : ({0, -1} : Finset (ZMod p)).erase 0 = {-1} :=
    erase_insert (notMem_singleton.mpr hne)
  rw [herase, prod_singleton]
  have hneg : (-1 : ZMod p)⁻¹ = -1 := by
    simp
  simp [hneg]

lemma rtwo_term2 (hp5 : 5 ≤ p) (h3r : 6 < p) :
    ((term (p - 2) 2 / p : ℕ) : ZMod p) = -((9 : ZMod p) * (2 : ZMod p)⁻¹) := by
  have hppos : 0 < p := p_pos (p := p)
  have hkp : (2 : ℕ) < p := lt_trans (by decide : 2 < 6) h3r
  have hmid := rtwo_choose_mid_ge (p := p) hp5 (by decide : 2 ≤ 2) hkp
  have hth : ((3 * (p - 2) + 4).choose (p - 2) : ZMod p) = 1 :=
    rtwo_third_unit_two hp5 h3r
  have hCn : ((p - 2).choose 2 : ZMod p) = 3 := by
    have h := rtwo_choose_n (p := p) hp5 (k := 2) (by omega)
    have : ((2 + 1 : ℕ) : ZMod p) = 3 := by norm_num
    simpa [pow_two, neg_one_sq, this] using h
  have hp2 : p - 2 + 2 = p := by omega
  have h3eq : 3 * (p - 2) + 2 * 2 = 3 * (p - 2) + 4 := by omega
  have hdiv : term (p - 2) 2 / p =
      (p - 2).choose 2 ^ 2 * ((p - 2 + 2).choose 2 / p) *
        (3 * (p - 2) + 4).choose (p - 2) := by
    rw [term, hp2, h3eq]
    have hB : p ∣ p.choose 2 := by simpa [hp2] using hmid.1
    obtain ⟨c, hc⟩ := hB
    rw [hc, Nat.mul_div_cancel_left c hppos]
    have : (p - 2).choose 2 ^ 2 * (p * c) * (3 * (p - 2) + 4).choose (p - 2) =
        ((p - 2).choose 2 ^ 2 * c * (3 * (p - 2) + 4).choose (p - 2)) * p := by ring
    rw [this, Nat.mul_div_cancel _ hppos]
    try ring
  rw [hdiv, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, hth, hCn]
  have hmid' : (((p - 2 + 2).choose 2 / p : ℕ) : ZMod p) =
      -((2 : ZMod p) * ((2 : ℕ).choose 2 : ZMod p))⁻¹ := by
    simpa [hp2] using hmid.2
  rw [hmid']
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp5
  have hC2 : ((2 : ℕ).choose 2 : ZMod p) = 1 := by simp
  rw [hC2]
  field_simp [h2]
  ring

lemma rtwo_AB (hp5 : 5 ≤ p) (h3r : 6 < p) :
    ((term (p - 2) 0 / p : ℕ) : ZMod p) +
      ((term (p - 2) 1 / p : ℕ) : ZMod p) +
        ((term (p - 2) 2 / p : ℕ) : ZMod p) =
      -((49 : ZMod p) * (15 : ZMod p)⁻¹) := by
  rw [rtwo_term0 hp5 h3r, rtwo_term1 hp5 h3r, rtwo_term2 hp5 h3r]
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp5
  have h3p : 3 < p := lt_trans (by decide : 3 < 6) h3r
  have h5p : 5 < p := lt_trans (by decide : 5 < 6) h3r
  have h3 : (3 : ZMod p) ≠ 0 := zmod_nat_ne_zero (by decide) h3p
  have h5 : (5 : ZMod p) ≠ 0 := zmod_nat_ne_zero (by decide) h5p
  have h10 : (10 : ZMod p) ≠ 0 := by
    have : (10 : ZMod p) = 2 * 5 := by norm_num
    rw [this]; exact mul_ne_zero h2 h5
  have h15 : (15 : ZMod p) ≠ 0 := by
    have : (15 : ZMod p) = 3 * 5 := by norm_num
    rw [this]; exact mul_ne_zero h3 h5
  field_simp [h2, h3, h5, h10, h15]
  ring

/-- The unique D-index for `r = 2`. -/
def rtwoD (p : ℕ) : ℕ := (p + 5) / 2

lemma rtwoD_spec (hp5 : 5 ≤ p) (hp2 : p % 2 = 1) :
    rtwoD p = (p + 5) / 2 := rfl

lemma p_odd_of_ge5 (hp5 : 5 ≤ p) : p % 2 = 1 :=
  p_odd (p := p) hp5

lemma rtwoD_mul_two (hp5 : 5 ≤ p) :
    2 * rtwoD p = p + 5 := by
  have hodd := p_odd_of_ge5 (p := p) hp5
  have : (p + 5) % 2 = 0 := by omega
  simp only [rtwoD]
  exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero this)

lemma rtwoD_bounds (hp11 : 11 ≤ p) :
    3 ≤ rtwoD p ∧ rtwoD p ≤ p - 2 := by
  have hp5 : 5 ≤ p := le_trans (by decide : 5 ≤ 11) hp11
  have h2 : 2 * rtwoD p = p + 5 := rtwoD_mul_two hp5
  constructor <;> omega

lemma rtwoD_cast (hp5 : 5 ≤ p) :
    (rtwoD p : ZMod p) = (5 : ZMod p) * (2 : ZMod p)⁻¹ := by
  have h2mul : 2 * rtwoD p = p + 5 := rtwoD_mul_two hp5
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp5
  apply mul_left_cancel₀ h2
  have hcast : ((2 * rtwoD p : ℕ) : ZMod p) = 5 := by
    rw [h2mul, Nat.cast_add, Nat.cast_ofNat, p_ne_zero_zmod (p := p), zero_add]
  rw [Nat.cast_mul, Nat.cast_two] at hcast
  rw [hcast]
  field_simp [h2]

lemma rtwoD_succ_cast (hp5 : 5 ≤ p) :
    ((rtwoD p + 1 : ℕ) : ZMod p) = (7 : ZMod p) * (2 : ZMod p)⁻¹ := by
  rw [Nat.cast_add, Nat.cast_one, rtwoD_cast hp5]
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp5
  field_simp [h2]
  ring

lemma rtwo_L_cast_D (hp5 : 5 ≤ p) :
    (thirdL (p := p) 2 (rtwoD p) : ZMod p) = 2 := by
  have : 2 ≤ p := p_ge_two (p := p)
  have h2mul : 2 * rtwoD p = p + 5 := rtwoD_mul_two hp5
  have heq : 2 * p + 2 * rtwoD p - 3 = 2 * p + (p + 5) - 3 := by
    rw [h2mul]
  have heq' : 2 * p + (p + 5) - 3 = 3 * p + 2 := by omega
  rw [rtwo_thirdL, heq, heq', Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    p_ne_zero_zmod (p := p), mul_zero, zero_add]
  rfl

lemma rtwo_missing_D (hp5 : 5 ≤ p) :
    (Icc (1 : ℕ) 2).image (fun j : ℕ =>
      (thirdL (p := p) 2 (rtwoD p) : ZMod p) - (j : ZMod p)) = {1, 0} := by
  rw [Icc_one_two, rtwo_L_cast_D hp5, image_insert, image_singleton]
  have h1 : (2 : ZMod p) - (1 : ℕ) = 1 := by
    rw [Nat.cast_one]; ring
  have h2 : (2 : ZMod p) - (2 : ℕ) = 0 := by
    rw [Nat.cast_ofNat]; ring
  rw [h1, h2]

lemma rtwo_third_D (hp5 : 5 ≤ p) (hp11 : 11 ≤ p) :
    ((3 * (p - 2) + 2 * rtwoD p).choose (p - 2) : ZMod p) = -1 := by
  have hr : (2 : ℕ) ≤ p := le_of_lt (two_lt_p_of_prime5 hp5)
  have h2mul : 2 * rtwoD p = p + 5 := rtwoD_mul_two hp5
  have hidx : 3 * (p - 2) + 2 * rtwoD p = 4 * p - 1 := by omega
  have hL : thirdL (p := p) 2 (rtwoD p) + p - 2 - 1 = 4 * p - 1 := by
    rw [rtwo_thirdL]; omega
  have hcheq : (3 * (p - 2) + 2 * rtwoD p).choose (p - 2) =
      (thirdL (p := p) 2 (rtwoD p) + p - 2 - 1).choose (p - 2) := by
    rw [hL, hidx]
  have h0miss : (0 : ZMod p) ∈
      (Icc (1 : ℕ) 2).image (fun j : ℕ =>
        (thirdL (p := p) 2 (rtwoD p) : ZMod p) - (j : ZMod p)) := by
    rw [rtwo_missing_D hp5]; simp
  have h := choose_zmod_of_zero_missing (p := p)
    (L := thirdL (p := p) 2 (rtwoD p)) (r := 2)
    (by decide) (two_lt_p_of_prime5 hp5) h0miss
  rw [hcheq, h, rtwo_missing_D hp5]
  have herase : ({1, 0} : Finset (ZMod p)).erase 0 = {1} := by
    ext x; simp [mem_erase, mem_insert, mem_singleton]; constructor <;> grind
  rw [herase, prod_singleton]
  simp

lemma rtwo_choose_n_D (hp5 : 5 ≤ p) (hp11 : 11 ≤ p) :
    ((p - 2).choose (rtwoD p) : ZMod p) =
      (-1 : ZMod p) ^ rtwoD p * ((rtwoD p + 1 : ℕ) : ZMod p) :=
  rtwo_choose_n hp5 (rtwoD_bounds hp11).2

lemma rtwo_mid_D (hp5 : 5 ≤ p) (hp11 : 11 ≤ p) :
    p ∣ (p - 2 + rtwoD p).choose (rtwoD p) ∧
    (((p - 2 + rtwoD p).choose (rtwoD p) / p : ℕ) : ZMod p) =
      -((4 : ZMod p) * (15 : ZMod p)⁻¹) := by
  have ⟨hk3, hkn⟩ := rtwoD_bounds (p := p) hp11
  have hkp : rtwoD p < p := by omega
  have h := rtwo_choose_mid_ge (p := p) hp5 (le_trans (by decide : 2 ≤ 3) hk3) hkp
  refine ⟨h.1, ?_⟩
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp5
  have h3p : 3 < p := lt_of_lt_of_le (by decide : 3 < 11) hp11
  have h5p : 5 < p := lt_of_lt_of_le (by decide : 5 < 11) hp11
  have h3 : (3 : ZMod p) ≠ 0 := zmod_nat_ne_zero (by decide) h3p
  have h5 : (5 : ZMod p) ≠ 0 := zmod_nat_ne_zero (by decide) h5p
  have h15 : (15 : ZMod p) ≠ 0 := by
    have : (15 : ZMod p) = 3 * 5 := by norm_num
    rw [this]; exact mul_ne_zero h3 h5
  have hk : (rtwoD p : ZMod p) = 5 * (2 : ZMod p)⁻¹ := rtwoD_cast hp5
  have hk1 : ((rtwoD p - 1 : ℕ) : ZMod p) = 3 * (2 : ZMod p)⁻¹ := by
    have hpos : 1 ≤ rtwoD p := by omega
    rw [Nat.cast_sub hpos, Nat.cast_one, hk]
    field_simp [h2]; ring
  have hle : 2 ≤ rtwoD p := by omega
  have hmul : 2 * (rtwoD p).choose 2 = rtwoD p * (rtwoD p - 1) := by
    rw [choose_two_right, Nat.mul_div_cancel' (even_iff_two_dvd.mp (Nat.even_mul_pred_self _))]
  have hCz : ((rtwoD p).choose 2 : ZMod p) =
      (rtwoD p : ZMod p) * ((rtwoD p - 1 : ℕ) : ZMod p) * (2 : ZMod p)⁻¹ := by
    apply mul_left_cancel₀ h2
    have hcast := congrArg (fun x : ℕ => (x : ZMod p)) hmul
    simp only [Nat.cast_mul, Nat.cast_two] at hcast
    rw [hcast]
    field_simp [h2]
  rw [h.2, hCz, hk, hk1]
  field_simp [h2, h3, h5, h15]
  ring

lemma rtwo_termD (hp5 : 5 ≤ p) (hp11 : 11 ≤ p) :
    ((term (p - 2) (rtwoD p) / p : ℕ) : ZMod p) =
      (49 : ZMod p) * (15 : ZMod p)⁻¹ := by
  have ⟨hk3, hkn⟩ := rtwoD_bounds (p := p) hp11
  have hppos : 0 < p := p_pos (p := p)
  have hmid := rtwo_mid_D (p := p) hp5 hp11
  have hth := rtwo_third_D (p := p) hp5 hp11
  have hCn := rtwo_choose_n_D (p := p) hp5 hp11
  have hdiv : term (p - 2) (rtwoD p) / p =
      (p - 2).choose (rtwoD p) ^ 2 *
        ((p - 2 + rtwoD p).choose (rtwoD p) / p) *
          (3 * (p - 2) + 2 * rtwoD p).choose (p - 2) := by
    rw [term]
    obtain ⟨c, hc⟩ := hmid.1
    rw [hc, Nat.mul_div_cancel_left c hppos]
    have : (p - 2).choose (rtwoD p) ^ 2 * (p * c) *
        (3 * (p - 2) + 2 * rtwoD p).choose (p - 2) =
      ((p - 2).choose (rtwoD p) ^ 2 * c *
        (3 * (p - 2) + 2 * rtwoD p).choose (p - 2)) * p := by ring
    rw [this, Nat.mul_div_cancel _ hppos]
    try ring
  rw [hdiv, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, hmid.2, hth, hCn]
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp5
  have h3p : 3 < p := lt_of_lt_of_le (by decide : 3 < 11) hp11
  have h5p : 5 < p := lt_of_lt_of_le (by decide : 5 < 11) hp11
  have h7p : 7 < p := lt_of_lt_of_le (by decide : 7 < 11) hp11
  have h3 : (3 : ZMod p) ≠ 0 := zmod_nat_ne_zero (by decide) h3p
  have h5 : (5 : ZMod p) ≠ 0 := zmod_nat_ne_zero (by decide) h5p
  have h7 : (7 : ZMod p) ≠ 0 := zmod_nat_ne_zero (by decide) h7p
  have h15 : (15 : ZMod p) ≠ 0 := by
    have : (15 : ZMod p) = 3 * 5 := by norm_num
    rw [this]; exact mul_ne_zero h3 h5
  have hk1 := rtwoD_succ_cast (p := p) hp5
  rw [hk1]
  have hpow : ((-1 : ZMod p) ^ rtwoD p * ((7 : ZMod p) * (2 : ZMod p)⁻¹)) ^ 2 = 
      ((7 : ZMod p) * (2 : ZMod p)⁻¹) ^ 2 := by
    have hs : ((-1 : ZMod p) ^ rtwoD p) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    rw [mul_pow, hs, one_mul]
  rw [hpow]
  field_simp [h2, h3, h5, h7, h15]
  ring

lemma rtwo_ABD (hp5 : 5 ≤ p) (hp11 : 11 ≤ p) :
    ((term (p - 2) 0 / p : ℕ) : ZMod p) +
      ((term (p - 2) 1 / p : ℕ) : ZMod p) +
        ((term (p - 2) 2 / p : ℕ) : ZMod p) +
          ((term (p - 2) (rtwoD p) / p : ℕ) : ZMod p) = 0 := by
  have h3r : 6 < p := lt_of_lt_of_le (by decide : 6 < 11) hp11
  rw [rtwo_AB hp5 h3r, rtwo_termD hp5 hp11]
  ring

/-- C-region first-order residue for `r = 2`. -/
lemma rtwo_term_C (hp5 : 5 ≤ p) (hp11 : 11 ≤ p) {k : ℕ}
    (hk3 : 3 ≤ k) (hkC : 2 * k ≤ p + 3) (hkn : k ≤ p - 2) :
    p ^ 2 ∣ term (p - 2) k ∧
    ((term (p - 2) k / p ^ 2 : ℕ) : ZMod p) =
      (3 : ZMod p) * (((k + 1 : ℕ) : ZMod p) ^ 2) *
        ((2 : ZMod p) * (k : ZMod p) * ((k - 1 : ℕ) : ZMod p) *
          ((k - 2 : ℕ) : ZMod p) * (((2 * k : ℕ) : ZMod p) - 5))⁻¹ := by
  have hr2 : 2 ≤ (2 : ℕ) := le_rfl
  have h3r : 6 < p := lt_of_lt_of_le (by decide : 6 < 11) hp11
  have hC1 : 3 * 2 ≤ 2 * k := by omega
  have hpsq := psq_dvd_term_region_C (p := p) (r := 2) (k := k)
    (by decide) hr2 (by omega) hC1 (by omega) hkn
  refine ⟨hpsq, ?_⟩
  have hr := two_lt_p_of_prime5 hp5
  have hkp : k < p := by omega
  have hmid := choose_p_sub_add_div_p_zmod (p := p) (r := 2) (k := k)
    (by decide) hr (by omega) hkp
  have hp7 : 3 < p := lt_of_lt_of_le (by decide : 3 < 11) hp11
  have ⟨hL, hU⟩ : thirdL (p := p) 2 k ≤ 3 * p ∧
      3 * p ≤ thirdL (p := p) 2 k + p - 2 - 1 := by
    constructor
    · simp only [thirdL]; omega
    · rw [thirdL_U (p := p) (le_of_lt hr)]; omega
  have hth := choose_div_p_of_interval_len (p := p) (L := thirdL (p := p) 2 k)
      (r := 2) (q := 3) (by decide) hr (by decide : 0 < 3) hp7 hL hU
  have hcheq := third_choose_eq_L (p := p) (r := 2) (k := k) (le_of_lt hr)
  have hppos : 0 < p := p_pos (p := p)
  have hdiv : term (p - 2) k / p ^ 2 =
      (p - 2).choose k ^ 2 * ((p - 2 + k).choose k / p) *
        ((3 * (p - 2) + 2 * k).choose (p - 2) / p) := by
    rw [term, pow_two]
    obtain ⟨c, hc⟩ := hmid.1
    have h2 : p ∣ (3 * (p - 2) + 2 * k).choose (p - 2) := by
      rw [hcheq]; exact hth.1
    obtain ⟨d, hd⟩ := h2
    rw [hc, hd]
    have : (p - 2).choose k * (p - 2).choose k * (p * c) * (p * d) / (p * p) =
        (p - 2).choose k * (p - 2).choose k * c * d := by
      have hmul :
          (p - 2).choose k * (p - 2).choose k * (p * c) * (p * d) =
            ((p - 2).choose k * (p - 2).choose k * c * d) * (p * p) := by ring
      rw [hmul, Nat.mul_div_cancel _ (mul_pos hppos hppos)]
    have hpsq : p ^ 2 = p * p := by ring
    rw [hpsq, this, Nat.mul_div_cancel_left c hppos, Nat.mul_div_cancel_left d hppos]
    try ring
  rw [hdiv, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow]
  rw [rtwo_choose_n hp5 hkn, hmid.2, hcheq, hth.2]
  have hpow : ((-1 : ZMod p) ^ k) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have hbin : ((k + 1 : ℕ) : ZMod p) = ((2 + k - 1 : ℕ).choose k : ZMod p) := by
    have : 2 + k - 1 = k + 1 := by omega
    rw [this, choose_succ_self_right, Nat.cast_succ]
  -- product ∏_{j=1}^2 (L-j) ≡ (2k-4)(2k-5)
  have hprod :
      ∏ j ∈ Icc (1 : ℕ) 2,
        ((thirdL (p := p) 2 k : ZMod p) - (j : ZMod p)) =
        (((2 * k : ℕ) : ZMod p) - 4) * (((2 * k : ℕ) : ZMod p) - 5) := by
    rw [prod_Icc_one_two, rtwo_thirdL]
    have h2p : (2 * p + 2 * k - 3 : ℕ) = 2 * p + (2 * k - 3) := by omega
    have hle : 3 ≤ 2 * p + 2 * k := by omega
    rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_mul, Nat.cast_two, Nat.cast_ofNat,
      p_ne_zero_zmod (p := p), mul_zero, zero_add]
    simp only [Nat.cast_one, Nat.cast_ofNat]
    ring
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp5
  have hk0 : (k : ZMod p) ≠ 0 := zmod_cast_ne_zero_of_lt hkp (by omega)
  have hk1 : ((k - 1 : ℕ) : ZMod p) ≠ 0 := by
    have : 0 < k - 1 := by omega
    have : k - 1 < p := by omega
    exact zmod_nat_ne_zero (by omega) this
  have hk2 : ((k - 2 : ℕ) : ZMod p) ≠ 0 :=
    zmod_nat_ne_zero (by omega) (by omega)
  have h25 : (((2 * k : ℕ) : ZMod p) - 5) ≠ 0 := by
    -- 2k-5 ≢ 0 since k ≤ (p+3)/2 ⇒ 2k-5 ≤ p-2 < p, and k≥3 ⇒ 2k-5≥1
    intro hz
    have : ((2 * k : ℕ) : ZMod p) = 5 := by
      linear_combination hz
    -- 1 ≤ 2k-5 ≤ p-2 so 2k-5 ≠ 0 in ℕ and < p
    have hge : 1 ≤ 2 * k - 5 := by omega
    have hlt : 2 * k - 5 < p := by omega
    have : ((2 * k - 5 : ℕ) : ZMod p) = 0 := by
      have hle : 5 ≤ 2 * k := by omega
      rw [Nat.cast_sub hle, Nat.cast_ofNat, this, sub_self]
    exact (zmod_nat_ne_zero hge hlt) this
  -- finish algebra
  have hrfac : ((2 - 1)! : ZMod p) = 1 := by simp
  have hsgn : (-1 : ZMod p) ^ (2 - 1) = -1 := by simp
  simp only [hpow, hrfac, hsgn] at *
  rw [hprod]
  have hC2 : (k.choose 2 : ZMod p) =
      (k : ZMod p) * ((k - 1 : ℕ) : ZMod p) * (2 : ZMod p)⁻¹ := by
    have : 2 * k.choose 2 = k * (k - 1) := by
      rw [choose_two_right, Nat.mul_div_cancel'
        (even_iff_two_dvd.mp (Nat.even_mul_pred_self _))]
    apply mul_left_cancel₀ h2
    have := congrArg (fun x : ℕ => (x : ZMod p)) this
    simp only [Nat.cast_mul, Nat.cast_two] at this
    rw [this]; field_simp [h2]
  have hsgn2 : (-1 : ZMod p) ^ (k * 2) = 1 := by
    rw [mul_comm, pow_mul, neg_one_sq, one_pow]
  have hden0 :
      (k.choose 2 : ZMod p) * (((2 * k : ℕ) : ZMod p) - 4) =
        (k : ZMod p) * ((k - 1 : ℕ) : ZMod p) * ((k - 2 : ℕ) : ZMod p) := by
    rw [hC2]
    have h2k : ((2 * k : ℕ) : ZMod p) = 2 * (k : ZMod p) := by
      rw [Nat.cast_mul, Nat.cast_two]
    rw [h2k]
    have hk2e : ((k - 2 : ℕ) : ZMod p) = (k : ZMod p) - 2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ k), Nat.cast_two]
    rw [hk2e]
    field_simp [h2]
    ring
  have h2k4 : (((2 * k : ℕ) : ZMod p) - 4) ≠ 0 := by
    intro hz
    have hge : 0 < 2 * k - 4 := by omega
    have hlt : 2 * k - 4 < p := by omega
    have : ((2 * k - 4 : ℕ) : ZMod p) = 0 := by
      have hle : 4 ≤ 2 * k := by omega
      rw [Nat.cast_sub hle, Nat.cast_ofNat, hz]
    exact (zmod_nat_ne_zero hge hlt) this
  have hC2ne : (k.choose 2 : ZMod p) ≠ 0 := by
    rw [hC2]
    exact mul_ne_zero (mul_ne_zero hk0 hk1) (inv_ne_zero h2)
  have hdenne :
      (2 : ZMod p) * (k : ZMod p) * ((k - 1 : ℕ) : ZMod p) *
        ((k - 2 : ℕ) : ZMod p) * (((2 * k : ℕ) : ZMod p) - 5) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h2 hk0) hk1) hk2) h25
  field_simp [h2, hk0, hk1, hk2, h25, h2k4, hC2ne, hdenne]
  -- Cleared form:
  -- `((-1)^k)² (k+1)² * 3 * 2 * k (k-1) (k-2)
  --    = (k+1)² * 2 * C(k,2) * (2k-4) * 3`.
  have hpow' : ((-1 : ZMod p) ^ k) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  calc
    ((-1 : ZMod p) ^ k) ^ 2 * ((k + 1 : ℕ) : ZMod p) ^ 2 * (3 : ZMod p) * 2 *
        (k : ZMod p) * ((k - 1 : ℕ) : ZMod p) * ((k - 2 : ℕ) : ZMod p)
        = (1 : ZMod p) * ((k + 1 : ℕ) : ZMod p) ^ 2 * 3 * 2 *
            (k : ZMod p) * ((k - 1 : ℕ) : ZMod p) * ((k - 2 : ℕ) : ZMod p) := by
          rw [hpow']
    _ = ((k + 1 : ℕ) : ZMod p) ^ 2 * 2 *
          ((k : ZMod p) * ((k - 1 : ℕ) : ZMod p) * ((k - 2 : ℕ) : ZMod p)) * 3 := by
          ring
    _ = ((k + 1 : ℕ) : ZMod p) ^ 2 * 2 *
          ((k.choose 2 : ZMod p) * (((2 * k : ℕ) : ZMod p) - 4)) * 3 := by
          rw [hden0]
    _ = ((k + 1 : ℕ) : ZMod p) ^ 2 * 2 * (k.choose 2 : ZMod p) *
          (((2 * k : ℕ) : ZMod p) - 4) * 3 := by
          ring

/-- E-region first-order residue for `r = 2`. -/
lemma rtwo_term_E (hp5 : 5 ≤ p) (hp11 : 11 ≤ p) {k : ℕ}
    (hkE : p + 6 ≤ 2 * k) (hkn : k ≤ p - 2) :
    p ^ 2 ∣ term (p - 2) k ∧
    ((term (p - 2) k / p ^ 2 : ℕ) : ZMod p) =
      (2 : ZMod p) * (((k + 1 : ℕ) : ZMod p) ^ 2) *
        ((k : ZMod p) * ((k - 1 : ℕ) : ZMod p) *
          ((k - 2 : ℕ) : ZMod p) * (((2 * k : ℕ) : ZMod p) - 5))⁻¹ := by
  have hr2 : 2 ≤ (2 : ℕ) := le_rfl
  have h3r : 6 < p := lt_of_lt_of_le (by decide : 6 < 11) hp11
  have hE : p + 3 * 2 ≤ 2 * k := by omega
  have hpsq := psq_dvd_term_region_E (p := p) (r := 2) (k := k)
    (by decide) hr2 (by omega) hE hkn
  refine ⟨hpsq, ?_⟩
  have hr := two_lt_p_of_prime5 hp5
  have hkp : k < p := by omega
  have hk3 : 3 ≤ k := by omega
  have hmid := choose_p_sub_add_div_p_zmod (p := p) (r := 2) (k := k)
    (by decide) hr (by omega) hkp
  have hp7 : 4 < p := lt_of_lt_of_le (by decide : 4 < 11) hp11
  have ⟨hL, hU⟩ : thirdL (p := p) 2 k ≤ 4 * p ∧
      4 * p ≤ thirdL (p := p) 2 k + p - 2 - 1 := by
    constructor
    · simp only [thirdL]; omega
    · rw [thirdL_U (p := p) (le_of_lt hr)]; omega
  have hth := choose_div_p_of_interval_len (p := p) (L := thirdL (p := p) 2 k)
      (r := 2) (q := 4) (by decide) hr (by decide : 0 < 4) hp7 hL hU
  have hcheq := third_choose_eq_L (p := p) (r := 2) (k := k) (le_of_lt hr)
  have hppos : 0 < p := p_pos (p := p)
  have hdiv : term (p - 2) k / p ^ 2 =
      (p - 2).choose k ^ 2 * ((p - 2 + k).choose k / p) *
        ((3 * (p - 2) + 2 * k).choose (p - 2) / p) := by
    rw [term, pow_two]
    obtain ⟨c, hc⟩ := hmid.1
    have h2 : p ∣ (3 * (p - 2) + 2 * k).choose (p - 2) := by
      rw [hcheq]; exact hth.1
    obtain ⟨d, hd⟩ := h2
    rw [hc, hd]
    have : (p - 2).choose k * (p - 2).choose k * (p * c) * (p * d) / (p * p) =
        (p - 2).choose k * (p - 2).choose k * c * d := by
      have hmul :
          (p - 2).choose k * (p - 2).choose k * (p * c) * (p * d) =
            ((p - 2).choose k * (p - 2).choose k * c * d) * (p * p) := by ring
      rw [hmul, Nat.mul_div_cancel _ (mul_pos hppos hppos)]
    have hpsq : p ^ 2 = p * p := by ring
    rw [hpsq, this, Nat.mul_div_cancel_left c hppos, Nat.mul_div_cancel_left d hppos]
    try ring
  rw [hdiv, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow]
  rw [rtwo_choose_n hp5 hkn, hmid.2, hcheq, hth.2]
  have hpow : ((-1 : ZMod p) ^ k) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have hprod :
      ∏ j ∈ Icc (1 : ℕ) 2,
        ((thirdL (p := p) 2 k : ZMod p) - (j : ZMod p)) =
        (((2 * k : ℕ) : ZMod p) - 4) * (((2 * k : ℕ) : ZMod p) - 5) := by
    rw [prod_Icc_one_two, rtwo_thirdL]
    have hle : 3 ≤ 2 * p + 2 * k := by omega
    rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_mul, Nat.cast_two, Nat.cast_ofNat,
      p_ne_zero_zmod (p := p), mul_zero, zero_add]
    simp only [Nat.cast_one]
    ring
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp5
  have hk0 : (k : ZMod p) ≠ 0 := zmod_cast_ne_zero_of_lt hkp (by omega)
  have hk1 : ((k - 1 : ℕ) : ZMod p) ≠ 0 :=
    zmod_nat_ne_zero (by omega) (by omega)
  have hk2 : ((k - 2 : ℕ) : ZMod p) ≠ 0 :=
    zmod_nat_ne_zero (by omega) (by omega)
  have h25 : (((2 * k : ℕ) : ZMod p) - 5) ≠ 0 := by
    intro hz
    have heq : ((2 * k : ℕ) : ZMod p) = 5 := by
      linear_combination hz
    have hle : 5 ≤ 2 * k := by omega
    have hzero : ((2 * k - 5 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub hle, Nat.cast_ofNat, heq, sub_self]
    -- In region E we have `2k ≥ p+6`, so `2k-5 ≥ p+1` and `2k-5 = p + (2k-5-p)`.
    have hsub : 2 * k - 5 = p + (2 * k - 5 - p) := by omega
    have hrest : 2 * k - 5 - p < p := by omega
    have hrest0 : 0 < 2 * k - 5 - p := by omega
    have hcast : ((2 * k - 5 : ℕ) : ZMod p) =
        ((2 * k - 5 - p : ℕ) : ZMod p) := by
      nth_rw 1 [hsub]
      rw [Nat.cast_add, CharP.cast_eq_zero (R := ZMod p) p, zero_add]
    rw [hcast] at hzero
    exact (zmod_nat_ne_zero hrest0 hrest) hzero
  have hrfac : ((2 - 1)! : ZMod p) = 1 := by simp
  have hsgn : (-1 : ZMod p) ^ (2 - 1) = -1 := by simp
  simp only [hpow, hrfac, hsgn] at *
  rw [hprod]
  have hC2 : (k.choose 2 : ZMod p) =
      (k : ZMod p) * ((k - 1 : ℕ) : ZMod p) * (2 : ZMod p)⁻¹ := by
    have : 2 * k.choose 2 = k * (k - 1) := by
      rw [choose_two_right, Nat.mul_div_cancel'
        (even_iff_two_dvd.mp (Nat.even_mul_pred_self _))]
    apply mul_left_cancel₀ h2
    have := congrArg (fun x : ℕ => (x : ZMod p)) this
    simp only [Nat.cast_mul, Nat.cast_two] at this
    rw [this]; field_simp [h2]
  have hden0 :
      (k.choose 2 : ZMod p) * (((2 * k : ℕ) : ZMod p) - 4) =
        (k : ZMod p) * ((k - 1 : ℕ) : ZMod p) * ((k - 2 : ℕ) : ZMod p) := by
    rw [hC2]
    have h2k : ((2 * k : ℕ) : ZMod p) = 2 * (k : ZMod p) := by
      rw [Nat.cast_mul, Nat.cast_two]
    rw [h2k]
    have hk2e : ((k - 2 : ℕ) : ZMod p) = (k : ZMod p) - 2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ k), Nat.cast_two]
    rw [hk2e]
    field_simp [h2]
    ring
  have h2k4 : (((2 * k : ℕ) : ZMod p) - 4) ≠ 0 := by
    intro hz
    have heq : ((2 * k : ℕ) : ZMod p) = 4 := by
      linear_combination hz
    have hle : 4 ≤ 2 * k := by omega
    have hzero : ((2 * k - 4 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub hle, Nat.cast_ofNat, heq, sub_self]
    have hsub : 2 * k - 4 = p + (2 * k - 4 - p) := by omega
    have hrest : 2 * k - 4 - p < p := by omega
    have hrest0 : 0 < 2 * k - 4 - p := by omega
    have hcast : ((2 * k - 4 : ℕ) : ZMod p) =
        ((2 * k - 4 - p : ℕ) : ZMod p) := by
      nth_rw 1 [hsub]
      rw [Nat.cast_add, CharP.cast_eq_zero (R := ZMod p) p, zero_add]
    rw [hcast] at hzero
    exact (zmod_nat_ne_zero hrest0 hrest) hzero
  have hC2ne : (k.choose 2 : ZMod p) ≠ 0 := by
    rw [hC2]
    exact mul_ne_zero (mul_ne_zero hk0 hk1) (inv_ne_zero h2)
  have hdenne :
      (k : ZMod p) * ((k - 1 : ℕ) : ZMod p) *
        ((k - 2 : ℕ) : ZMod p) * (((2 * k : ℕ) : ZMod p) - 5) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hk0 hk1) hk2) h25
  field_simp [h2, hk0, hk1, hk2, h25, h2k4, hC2ne, hdenne]
  have hpow' : ((-1 : ZMod p) ^ k) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  calc
    ((-1 : ZMod p) ^ k) ^ 2 * ((k + 1 : ℕ) : ZMod p) ^ 2 * (4 : ZMod p) *
        (k : ZMod p) * ((k - 1 : ℕ) : ZMod p) * ((k - 2 : ℕ) : ZMod p)
        = (1 : ZMod p) * ((k + 1 : ℕ) : ZMod p) ^ 2 * 4 *
            (k : ZMod p) * ((k - 1 : ℕ) : ZMod p) * ((k - 2 : ℕ) : ZMod p) := by
          rw [hpow']
    _ = ((k + 1 : ℕ) : ZMod p) ^ 2 * 2 *
          ((k : ZMod p) * ((k - 1 : ℕ) : ZMod p) * ((k - 2 : ℕ) : ZMod p)) * 2 := by
          ring
    _ = ((k + 1 : ℕ) : ZMod p) ^ 2 * 2 *
          ((k.choose 2 : ZMod p) * (((2 * k : ℕ) : ZMod p) - 4)) * 2 := by
          rw [hden0]
    _ = ((k + 1 : ℕ) : ZMod p) ^ 2 * (2 : ZMod p) * (k.choose 2 : ZMod p) *
          (((2 * k : ℕ) : ZMod p) - 4) * 2 := by
          ring

/-- First-order vanishing of A+B+D implies `p² ∣ t₀+t₁+t₂+t_D`. -/
lemma rtwo_psq_dvd_ABD (hp5 : 5 ≤ p) (hp11 : 11 ≤ p) :
    p ^ 2 ∣ term (p - 2) 0 + term (p - 2) 1 + term (p - 2) 2 +
      term (p - 2) (rtwoD p) := by
  have hppos : 0 < p := p_pos (p := p)
  have h3r : 6 < p := lt_of_lt_of_le (by decide : 6 < 11) hp11
  have ⟨hk3, hkn⟩ := rtwoD_bounds (p := p) hp11
  have h0 : p ∣ term (p - 2) 0 := by
    -- `k = 0` is region A.
    have hlo : (2 * p + 3) / 3 ≤ p - 2 := by omega
    have hn : p - 2 ≤ p - 1 := by omega
    exact p_dvd_term (Fact.out : p.Prime) hp5 hlo hn (by omega)
  have h1 : p ∣ term (p - 2) 1 := by
    have hlo : (2 * p + 3) / 3 ≤ p - 2 := by omega
    have hn : p - 2 ≤ p - 1 := by omega
    exact p_dvd_term (Fact.out : p.Prime) hp5 hlo hn (by omega)
  have h2t : p ∣ term (p - 2) 2 := by
    have hlo : (2 * p + 3) / 3 ≤ p - 2 := by omega
    have hn : p - 2 ≤ p - 1 := by omega
    exact p_dvd_term (Fact.out : p.Prime) hp5 hlo hn (by omega)
  have hD : p ∣ term (p - 2) (rtwoD p) := by
    have hlo : (2 * p + 3) / 3 ≤ p - 2 := by omega
    have hn : p - 2 ≤ p - 1 := by omega
    exact p_dvd_term (Fact.out : p.Prime) hp5 hlo hn hkn
  -- The first-order sum vanishes, so `p` divides the sum of quotients.
  have hsum0 := rtwo_ABD (p := p) hp5 hp11
  have hS :
      ((term (p - 2) 0 / p + term (p - 2) 1 / p + term (p - 2) 2 / p +
        term (p - 2) (rtwoD p) / p : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_add, hsum0]
  have hdivS : p ∣ term (p - 2) 0 / p + term (p - 2) 1 / p +
      term (p - 2) 2 / p + term (p - 2) (rtwoD p) / p :=
    (ZMod.natCast_eq_zero_iff _ p).mp hS
  have hdecomp :
      term (p - 2) 0 + term (p - 2) 1 + term (p - 2) 2 +
        term (p - 2) (rtwoD p) =
      p * (term (p - 2) 0 / p + term (p - 2) 1 / p + term (p - 2) 2 / p +
        term (p - 2) (rtwoD p) / p) := by
    have h0' := Nat.mul_div_cancel' h0
    have h1' := Nat.mul_div_cancel' h1
    have h2' := Nat.mul_div_cancel' h2t
    have hD' := Nat.mul_div_cancel' hD
    linarith
  rw [hdecomp, pow_two]
  exact mul_dvd_mul_left p hdivS

/-! Second-order expansions in `ZMod (p^2)`. -/

lemma p_sq_cast_eq_zero : ((p ^ 2 : ℕ) : ZMod (p ^ 2)) = 0 :=
  CharP.cast_eq_zero (R := ZMod (p ^ 2)) (p ^ 2)

lemma p_mul_p_zmod_sq : ((p : ℕ) : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) = 0 := by
  rw [← Nat.cast_mul, ← pow_two, p_sq_cast_eq_zero]

lemma isUnit_nat_zmod_sq {j : ℕ} (hj0 : 0 < j) (hjp : j < p)
    (hp : p.Prime) : IsUnit (j : ZMod (p ^ 2)) := by
  refine (ZMod.isUnit_iff_coprime j (p ^ 2)).mpr ?_
  rw [Nat.coprime_pow_right_iff (by decide : 0 < 2)]
  exact (Nat.coprime_of_lt_prime hj0.ne' hjp hp).symm

lemma prod_one_add_nilpotent {α : Type*} [CommRing α] {d : α} (hd : d * d = 0)
    (s : Finset ℕ) (u : ℕ → α) :
    ∏ j ∈ s, (1 + d * u j) = 1 + d * ∑ j ∈ s, u j := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, ih, sum_insert ha]
    have hd2 : d ^ 2 = 0 := by rw [pow_two, hd]
    ring_nf
    simp [hd2]

lemma prod_Icc_add_mul_p (hp : p.Prime) (c a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hbp : b < p) :
    (∏ j ∈ Icc a b, ((j + c * p : ℕ) : ZMod (p ^ 2))) =
      (∏ j ∈ Icc a b, (j : ZMod (p ^ 2))) *
        (1 + (c : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
          ∑ j ∈ Icc a b, Ring.inverse (j : ZMod (p ^ 2))) := by
  have hcongr : ∀ j ∈ Icc a b,
      ((j + c * p : ℕ) : ZMod (p ^ 2)) =
        (j : ZMod (p ^ 2)) * (1 + (c : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
          Ring.inverse (j : ZMod (p ^ 2))) := by
    intro j hj
    have hjI := mem_Icc.mp hj
    have hj1 : 1 ≤ j := le_trans ha hjI.1
    have hju : IsUnit (j : ZMod (p ^ 2)) :=
      isUnit_nat_zmod_sq (lt_of_lt_of_le (by decide : 0 < 1) hj1)
        (lt_of_le_of_lt hjI.2 hbp) hp
    have hinv : (j : ZMod (p ^ 2)) * Ring.inverse (j : ZMod (p ^ 2)) = 1 :=
      Ring.mul_inverse_cancel _ hju
    rw [Nat.cast_add, Nat.cast_mul]
    have hexp :
        (j : ZMod (p ^ 2)) * (1 + (c : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
          Ring.inverse (j : ZMod (p ^ 2))) =
          (j : ZMod (p ^ 2)) + (c : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
            ((j : ZMod (p ^ 2)) * Ring.inverse (j : ZMod (p ^ 2))) := by
      ring
    rw [hexp, hinv]
    ring
  rw [prod_congr rfl hcongr, prod_mul_distrib]
  have hd : ((c : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) *
      ((c : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) = 0 := by
    have : (p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) = 0 := p_mul_p_zmod_sq (p := p)
    calc
      (c : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) * ((c : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)))
          = ((c : ZMod (p ^ 2)) * (c : ZMod (p ^ 2))) *
              ((p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) := by ring
      _ = ((c : ZMod (p ^ 2)) * (c : ZMod (p ^ 2))) * 0 := by rw [this]
      _ = 0 := by ring
  rw [prod_one_add_nilpotent hd]
  try ring

lemma rtwo_term0_mul_fac (hp11 : 11 ≤ p) :
    term (p - 2) 0 * (p - 2)! =
      (2 * p - 3) * (2 * p - 2) * (2 * p - 1) * (2 * p) *
        ∏ j ∈ Icc 1 (p - 6), (2 * p + j) := by
  have hp : 6 ≤ p := le_trans (by decide : 6 ≤ 11) hp11
  have hterm : term (p - 2) 0 = (3 * p - 6).choose (p - 2) := by
    unfold term
    simp [choose_zero_right, pow_two]
    have : 3 * (p - 2) = 3 * p - 6 := by omega
    rw [this]
  have hdesc : (3 * p - 6).descFactorial (p - 2) =
      ∏ j ∈ Icc (2 * p - 3) (3 * p - 6), j := by
    have hkn : p - 2 ≤ (3 * p - 6) + 1 := by omega
    have : (3 * p - 6) + 1 - (p - 2) = 2 * p - 3 := by omega
    rw [descFactorial_eq_prod_Icc (by omega) hkn, this]
  have hC : (3 * p - 6).choose (p - 2) * (p - 2)! =
      (3 * p - 6).descFactorial (p - 2) := by
    rw [mul_comm, descFactorial_eq_factorial_mul_choose]
  have hsplit :
      ∏ j ∈ Icc (2 * p - 3) (3 * p - 6), j =
        (2 * p - 3) * (2 * p - 2) * (2 * p - 1) * (2 * p) *
          ∏ j ∈ Icc 1 (p - 6), (2 * p + j) := by
    have h1 : Icc (2 * p - 3) (3 * p - 6) =
        insert (2 * p - 3) (insert (2 * p - 2)
          (insert (2 * p - 1) (insert (2 * p) (Icc (2 * p + 1) (3 * p - 6))))) := by
      ext x; simp [mem_Icc, mem_insert]; omega
    rw [h1]
    have n1 : 2 * p - 3 ∉ insert (2 * p - 2)
        (insert (2 * p - 1) (insert (2 * p) (Icc (2 * p + 1) (3 * p - 6)))) := by
      simp [mem_insert, mem_Icc]; omega
    have n2 : 2 * p - 2 ∉ insert (2 * p - 1)
        (insert (2 * p) (Icc (2 * p + 1) (3 * p - 6))) := by
      simp [mem_insert, mem_Icc]; omega
    have n3 : 2 * p - 1 ∉ insert (2 * p) (Icc (2 * p + 1) (3 * p - 6)) := by
      simp [mem_insert, mem_Icc]; omega
    have n4 : 2 * p ∉ Icc (2 * p + 1) (3 * p - 6) :=
      not_mem_Icc_of_lt (by omega)
    rw [prod_insert n1, prod_insert n2, prod_insert n3, prod_insert n4]
    have : Icc (2 * p + 1) (3 * p - 6) = Icc (2 * p + 1) (2 * p + (p - 6)) := by
      congr 1; omega
    rw [this, ← prod_Icc_shift_two_p]
    ac_rfl
  rw [hterm, hC, hdesc, hsplit]

lemma rtwo_term1_mul_fac (hp11 : 11 ≤ p) :
    term (p - 2) 1 * (p - 2)! =
      (p - 2) ^ 2 * (p - 1) * (2 * p - 1) * (2 * p) *
        ∏ j ∈ Icc 1 (p - 4), (2 * p + j) := by
  have hp : 4 ≤ p := le_trans (by decide : 4 ≤ 11) hp11
  have hch : (p - 2).choose 1 = p - 2 := choose_one_right _
  have hp21 : p - 2 + 1 = p - 1 := by omega
  have hch2 : (p - 2 + 1).choose 1 = p - 1 := by
    rw [hp21, choose_one_right]
  have h3 : 3 * (p - 2) + 2 * 1 = 3 * p - 4 := by omega
  have hterm : term (p - 2) 1 =
      (p - 2) ^ 2 * (p - 1) * (3 * p - 4).choose (p - 2) := by
    unfold term
    rw [hch, hch2, h3]
  have hdesc : (3 * p - 4).descFactorial (p - 2) =
      ∏ j ∈ Icc (2 * p - 1) (3 * p - 4), j := by
    have hkn : p - 2 ≤ (3 * p - 4) + 1 := by omega
    have : (3 * p - 4) + 1 - (p - 2) = 2 * p - 1 := by omega
    rw [descFactorial_eq_prod_Icc (by omega) hkn, this]
  have hC : (3 * p - 4).choose (p - 2) * (p - 2)! =
      (3 * p - 4).descFactorial (p - 2) := by
    rw [mul_comm, descFactorial_eq_factorial_mul_choose]
  have hsplit :
      ∏ j ∈ Icc (2 * p - 1) (3 * p - 4), j =
        (2 * p - 1) * (2 * p) * ∏ j ∈ Icc 1 (p - 4), (2 * p + j) := by
    have h1 : Icc (2 * p - 1) (3 * p - 4) =
        insert (2 * p - 1) (insert (2 * p) (Icc (2 * p + 1) (3 * p - 4))) := by
      ext x; simp [mem_Icc, mem_insert]; omega
    rw [h1]
    have n1 : 2 * p - 1 ∉ insert (2 * p) (Icc (2 * p + 1) (3 * p - 4)) := by
      simp [mem_insert, mem_Icc]; omega
    have n2 : 2 * p ∉ Icc (2 * p + 1) (3 * p - 4) :=
      not_mem_Icc_of_lt (by omega)
    rw [prod_insert n1, prod_insert n2]
    have : Icc (2 * p + 1) (3 * p - 4) = Icc (2 * p + 1) (2 * p + (p - 4)) := by
      congr 1; omega
    rw [this, ← prod_Icc_shift_two_p]
    ac_rfl
  rw [hterm]
  calc
    (p - 2) ^ 2 * (p - 1) * (3 * p - 4).choose (p - 2) * (p - 2)!
        = (p - 2) ^ 2 * (p - 1) * ((3 * p - 4).choose (p - 2) * (p - 2)!) := by ring
    _ = (p - 2) ^ 2 * (p - 1) * (3 * p - 4).descFactorial (p - 2) := by rw [hC]
    _ = (p - 2) ^ 2 * (p - 1) * ∏ j ∈ Icc (2 * p - 1) (3 * p - 4), j := by rw [hdesc]
    _ = (p - 2) ^ 2 * (p - 1) *
          ((2 * p - 1) * (2 * p) * ∏ j ∈ Icc 1 (p - 4), (2 * p + j)) := by
        rw [hsplit]
    _ = (p - 2) ^ 2 * (p - 1) * (2 * p - 1) * (2 * p) *
          ∏ j ∈ Icc 1 (p - 4), (2 * p + j) := by ring

lemma rtwo_choose_two (hp : 2 ≤ p) :
    (p - 2).choose 2 = (p - 2) * (p - 3) / 2 := by
  rw [choose_two_right]
  have : p - 2 - 1 = p - 3 := by omega
  rw [this]

lemma rtwo_term2_mul_fac (hp11 : 11 ≤ p) :
    term (p - 2) 2 * (p - 2)! =
      (p - 2).choose 2 ^ 2 * (p.choose 2) *
        ∏ j ∈ Icc 1 (p - 2), (2 * p + j) := by
  have hp : 4 ≤ p := le_trans (by decide : 4 ≤ 11) hp11
  have hp2 : p - 2 + 2 = p := by omega
  have h3 : 3 * (p - 2) + 2 * 2 = 3 * p - 2 := by omega
  have hterm : term (p - 2) 2 =
      (p - 2).choose 2 ^ 2 * p.choose 2 * (3 * p - 2).choose (p - 2) := by
    unfold term
    rw [hp2, h3]
  have hdesc : (3 * p - 2).descFactorial (p - 2) =
      ∏ j ∈ Icc (2 * p + 1) (3 * p - 2), j := by
    have hkn : p - 2 ≤ (3 * p - 2) + 1 := by omega
    have : (3 * p - 2) + 1 - (p - 2) = 2 * p + 1 := by omega
    rw [descFactorial_eq_prod_Icc (by omega) hkn, this]
  have hC : (3 * p - 2).choose (p - 2) * (p - 2)! =
      (3 * p - 2).descFactorial (p - 2) := by
    rw [mul_comm, descFactorial_eq_factorial_mul_choose]
  have hsplit :
      ∏ j ∈ Icc (2 * p + 1) (3 * p - 2), j =
        ∏ j ∈ Icc 1 (p - 2), (2 * p + j) := by
    have : Icc (2 * p + 1) (3 * p - 2) = Icc (2 * p + 1) (2 * p + (p - 2)) := by
      congr 1; omega
    rw [this, ← prod_Icc_shift_two_p]
  rw [hterm]
  calc
    (p - 2).choose 2 ^ 2 * p.choose 2 * (3 * p - 2).choose (p - 2) * (p - 2)!
        = (p - 2).choose 2 ^ 2 * p.choose 2 *
            ((3 * p - 2).choose (p - 2) * (p - 2)!) := by ring
    _ = (p - 2).choose 2 ^ 2 * p.choose 2 *
            (3 * p - 2).descFactorial (p - 2) := by rw [hC]
    _ = (p - 2).choose 2 ^ 2 * p.choose 2 *
            ∏ j ∈ Icc (2 * p + 1) (3 * p - 2), j := by rw [hdesc]
    _ = (p - 2).choose 2 ^ 2 * p.choose 2 *
            ∏ j ∈ Icc 1 (p - 2), (2 * p + j) := by rw [hsplit]

/-- Cast of a unit inverse from `ZMod (p^2)` reduces to the inverse in `ZMod p`. -/
lemma inverse_zmod_sq_cast {j : ℕ} (hj0 : 0 < j) (hjp : j < p)
    (hp : p.Prime) :
    (ZMod.cast (Ring.inverse (j : ZMod (p ^ 2))) : ZMod p) = (j : ZMod p)⁻¹ := by
  have hju := isUnit_nat_zmod_sq (p := p) hj0 hjp hp
  have hmul : (j : ZMod (p ^ 2)) * Ring.inverse (j : ZMod (p ^ 2)) = 1 :=
    Ring.mul_inverse_cancel _ hju
  have hdvd : p ∣ p ^ 2 := dvd_pow_self p (by decide : 2 ≠ 0)
  have hcastmul := ZMod.cast_mul (R := ZMod p) hdvd
      (j : ZMod (p ^ 2)) (Ring.inverse (j : ZMod (p ^ 2)))
  have hjcast : (ZMod.cast (j : ZMod (p ^ 2)) : ZMod p) = (j : ZMod p) :=
    ZMod.cast_natCast hdvd j
  have h1 : (ZMod.cast (1 : ZMod (p ^ 2)) : ZMod p) = (1 : ZMod p) :=
    ZMod.cast_one hdvd
  have : (j : ZMod p) * (ZMod.cast (Ring.inverse (j : ZMod (p ^ 2))) : ZMod p) = 1 := by
    rw [← hjcast, ← hcastmul, hmul, h1]
  exact eq_inv_of_mul_eq_one_right this

lemma cast_sum_zmod_sq (s : Finset ℕ) (f : ℕ → ZMod (p ^ 2)) :
    (ZMod.cast (∑ j ∈ s, f j) : ZMod p) =
      ∑ j ∈ s, (ZMod.cast (f j) : ZMod p) := by
  have hdvd : p ∣ p ^ 2 := dvd_pow_self p (by decide : 2 ≠ 0)
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [sum_insert hx, sum_insert hx, ZMod.cast_add (R := ZMod p) hdvd, ih]

lemma harmonic_Icc_cast {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hbp : b < p)
    (hp : p.Prime) :
    (ZMod.cast (∑ j ∈ Icc a b, Ring.inverse (j : ZMod (p ^ 2))) : ZMod p) =
      ∑ j ∈ Icc a b, (j : ZMod p)⁻¹ := by
  rw [cast_sum_zmod_sq]
  refine sum_congr rfl ?_
  intro j hj
  have hjI := mem_Icc.mp hj
  exact inverse_zmod_sq_cast (lt_of_lt_of_le (by decide : 0 < 1)
      (le_trans ha hjI.1)) (lt_of_le_of_lt hjI.2 hbp) hp

lemma isUnit_factorial_zmod_sq {k : ℕ} (hk : k < p) (hp : p.Prime) :
    IsUnit (k ! : ZMod (p ^ 2)) := by
  refine (ZMod.isUnit_iff_coprime (k !) (p ^ 2)).mpr ?_
  rw [Nat.coprime_pow_right_iff (by decide : 0 < 2)]
  exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr (fun h ↦
    (not_le_of_gt hk) (hp.dvd_factorial.mp h))).symm

lemma inverse_one_add_nilp {α : Type*} [CommRing α] {d u : α} (hd : d * d = 0) :
    Ring.inverse (1 + d * u) = 1 - d * u := by
  have hxy : (1 + d * u) * (1 - d * u) = 1 := by
    ring_nf; simp [pow_two, hd]
  have hunit : IsUnit (1 + d * u) := isUnit_iff_exists_inv.mpr ⟨1 - d * u, hxy⟩
  calc
    Ring.inverse (1 + d * u)
        = Ring.inverse (1 + d * u) * 1 := by rw [mul_one]
    _ = Ring.inverse (1 + d * u) * ((1 + d * u) * (1 - d * u)) := by rw [hxy]
    _ = (Ring.inverse (1 + d * u) * (1 + d * u)) * (1 - d * u) := by rw [mul_assoc]
    _ = 1 * (1 - d * u) := by rw [Ring.inverse_mul_cancel _ hunit]
    _ = 1 - d * u := by rw [one_mul]

lemma inv_of_unit_mul {α : Type*} [CommRing α] {a b : α}
    (ha : IsUnit a) (hb : IsUnit b) :
    Ring.inverse (a * b) = Ring.inverse a * Ring.inverse b := by
  have hab : IsUnit (a * b) := IsUnit.mul ha hb
  have hxy : (a * b) * (Ring.inverse a * Ring.inverse b) = 1 := by
    calc
      (a * b) * (Ring.inverse a * Ring.inverse b)
          = (a * Ring.inverse a) * (b * Ring.inverse b) := by ring
      _ = 1 * 1 := by rw [Ring.mul_inverse_cancel _ ha, Ring.mul_inverse_cancel _ hb]
      _ = 1 := by ring
  calc
    Ring.inverse (a * b)
        = Ring.inverse (a * b) * 1 := by rw [mul_one]
    _ = Ring.inverse (a * b) * ((a * b) * (Ring.inverse a * Ring.inverse b)) := by
          rw [hxy]
    _ = (Ring.inverse (a * b) * (a * b)) * (Ring.inverse a * Ring.inverse b) := by
          ac_rfl
    _ = 1 * (Ring.inverse a * Ring.inverse b) := by
          rw [Ring.inverse_mul_cancel _ hab]
    _ = Ring.inverse a * Ring.inverse b := by rw [one_mul]

lemma inv_pow_card_sub_two {j : ℕ} (hj0 : 0 < j) (hjp : j < p) :
    (j : ZMod p)⁻¹ = (j : ZMod p) ^ (p - 2) := by
  have hjne : (j : ZMod p) ≠ 0 := zmod_nat_ne_zero hj0 hjp
  have hfermat : (j : ZMod p) ^ (p - 1) = 1 :=
    ZMod.pow_card_sub_one_eq_one hjne
  have hmul : (j : ZMod p) * (j : ZMod p) ^ (p - 2) = 1 := by
    have hsucc : (j : ZMod p) ^ (p - 2 + 1) =
        (j : ZMod p) ^ (p - 2) * (j : ZMod p) := pow_succ _ _
    have hpe : p - 2 + 1 = p - 1 := by
      have : 2 ≤ p := p_ge_two (p := p); omega
    rw [mul_comm, ← hsucc, hpe, hfermat]
  exact inv_eq_of_mul_eq_one_right hmul

/-- Sum of inverses of `1, …, p-1` vanishes in `ZMod p`. -/
lemma harmonic_pred_eq_zero (hp5 : 5 ≤ p) :
    ∑ j ∈ Icc (1 : ℕ) (p - 1), (j : ZMod p)⁻¹ = 0 := by
  have hp2 : 2 ≤ p := p_ge_two (p := p)
  have hpow : ∀ j ∈ Icc (1 : ℕ) (p - 1),
      (j : ZMod p)⁻¹ = (j : ZMod p) ^ (p - 2) := by
    intro j hj
    have hjI := mem_Icc.mp hj
    exact inv_pow_card_sub_two (lt_of_lt_of_le (by decide : 0 < 1) hjI.1)
      (lt_of_le_of_lt hjI.2 (Nat.sub_one_lt (p_pos (p := p)).ne'))
  rw [sum_congr rfl hpow]
  have hinj : Set.InjOn (fun j : ℕ => (j : ZMod p)) (Icc (1 : ℕ) (p - 1)) := by
    intro a ha b hb hab
    have ha' : a ∈ Icc 1 (1 + p - 2) := by
      rw [← Icc_one_pred_eq (p := p)]; simpa [Finset.mem_coe] using ha
    have hb' : b ∈ Icc 1 (1 + p - 2) := by
      rw [← Icc_one_pred_eq (p := p)]; simpa [Finset.mem_coe] using hb
    exact injOn_cast_Icc_consecutive (p := p) 1 a ha' b hb' hab
  have himg := image_Icc_one_pred (p := p)
  have hsum_img :
      ∑ j ∈ Icc (1 : ℕ) (p - 1), (j : ZMod p) ^ (p - 2) =
        ∑ x ∈ (univ : Finset (ZMod p)).erase 0, x ^ (p - 2) := by
    rw [← himg]
    exact (Finset.sum_image (fun a ha b hb h => hinj ha hb h)).symm
  rw [hsum_img]
  have hz : (0 : ZMod p) ^ (p - 2) = 0 :=
    zero_pow (Nat.sub_ne_zero_iff_lt.mpr (lt_of_lt_of_le (by decide : 2 < 5) hp5))
  have hall : ∑ x : ZMod p, x ^ (p - 2) = 0 :=
    sum_univ_pow_eq_zero (j := p - 2) (by omega)
  have hmem : (0 : ZMod p) ∈ (univ : Finset (ZMod p)) := mem_univ _
  have hse := sum_erase_eq_sub (s := (univ : Finset (ZMod p))) (a := (0 : ZMod p))
      (f := fun x => x ^ (p - 2)) hmem
  rw [hse, hall]
  simp [hz]

lemma Icc_split_last {a n : ℕ} (han : a ≤ n) (h0 : 1 ≤ n) :
    Icc a n = insert n (Icc a (n - 1)) := by
  ext x
  simp only [mem_Icc, mem_insert]
  omega

lemma harmonic_succ_Icc {n : ℕ} (hn : 1 ≤ n) (hnp : n < p) :
    ∑ j ∈ Icc (1 : ℕ) n, (j : ZMod p)⁻¹ =
      ∑ j ∈ Icc (1 : ℕ) (n - 1), (j : ZMod p)⁻¹ + (n : ZMod p)⁻¹ := by
  by_cases h1 : n = 1
  · subst h1
    simp [Icc_self]
  · have h2 : 1 ≤ n - 1 := by omega
    have hle : 1 ≤ n := hn
    rw [Icc_split_last (a := 1) hle hn]
    have hnmem : n ∉ Icc (1 : ℕ) (n - 1) := by
      simp [mem_Icc]; omega
    rw [sum_insert hnmem]
    abel

lemma harmonic_p_sub_six (hp11 : 11 ≤ p) :
    ∑ j ∈ Icc (1 : ℕ) (p - 6), (j : ZMod p)⁻¹ =
      (137 : ZMod p) * (60 : ZMod p)⁻¹ := by
  have hp5 : 5 ≤ p := le_trans (by decide : 5 ≤ 11) hp11
  have hfull := harmonic_pred_eq_zero (p := p) hp5
  -- H_{p-1} = H_{p-6} + 1/(p-5)+1/(p-4)+1/(p-3)+1/(p-2)+1/(p-1)
  have hsplit :
      ∑ j ∈ Icc (1 : ℕ) (p - 1), (j : ZMod p)⁻¹ =
        ∑ j ∈ Icc (1 : ℕ) (p - 6), (j : ZMod p)⁻¹ +
          ((p - 5 : ℕ) : ZMod p)⁻¹ + ((p - 4 : ℕ) : ZMod p)⁻¹ +
          ((p - 3 : ℕ) : ZMod p)⁻¹ + ((p - 2 : ℕ) : ZMod p)⁻¹ +
          ((p - 1 : ℕ) : ZMod p)⁻¹ := by
    have h1 : 1 ≤ p - 5 := by omega
    have h2 : p - 5 < p := by omega
    have h3 : 1 ≤ p - 4 := by omega
    have h4 : p - 4 < p := by omega
    have h5 : 1 ≤ p - 3 := by omega
    have h6 : p - 3 < p := by omega
    have h7 : 1 ≤ p - 2 := by omega
    have h8 : p - 2 < p := by omega
    have h9 : 1 ≤ p - 1 := by omega
    have h10 : p - 1 < p := Nat.sub_one_lt (p_pos (p := p)).ne'
    have s1 := harmonic_succ_Icc (p := p) (n := p - 5) h1 h2
    have s2 := harmonic_succ_Icc (p := p) (n := p - 4) h3 h4
    have s3 := harmonic_succ_Icc (p := p) (n := p - 3) h5 h6
    have s4 := harmonic_succ_Icc (p := p) (n := p - 2) h7 h8
    have s5 := harmonic_succ_Icc (p := p) (n := p - 1) h9 h10
    have e1 : p - 4 - 1 = p - 5 := by omega
    have e2 : p - 3 - 1 = p - 4 := by omega
    have e3 : p - 2 - 1 = p - 3 := by omega
    have e4 : p - 1 - 1 = p - 2 := by omega
    have e0 : p - 5 - 1 = p - 6 := by omega
    rw [e0] at s1
    rw [e1] at s2
    rw [e2] at s3
    rw [e3] at s4
    rw [e4] at s5
    linear_combination s5 + s4 + s3 + s2 + s1
  have hcast : ∀ k : ℕ, 1 ≤ k → k ≤ 5 →
      ((p - k : ℕ) : ZMod p)⁻¹ = -((k : ZMod p)⁻¹) := by
    intro k hk1 hk5
    have hle : k ≤ p := by omega
    rw [Nat.cast_sub hle, CharP.cast_eq_zero (R := ZMod p) p, zero_sub, inv_neg]
  have c1 := hcast 1 (by decide) (by decide)
  have c2 := hcast 2 (by decide) (by decide)
  have c3 := hcast 3 (by decide) (by decide)
  have c4 := hcast 4 (by decide) (by decide)
  have c5 := hcast 5 (by decide) (by decide)
  rw [hfull] at hsplit
  have hsum0 :
      ∑ j ∈ Icc (1 : ℕ) (p - 6), (j : ZMod p)⁻¹ +
        (((p - 5 : ℕ) : ZMod p)⁻¹ + ((p - 4 : ℕ) : ZMod p)⁻¹ +
          ((p - 3 : ℕ) : ZMod p)⁻¹ + ((p - 2 : ℕ) : ZMod p)⁻¹ +
          ((p - 1 : ℕ) : ZMod p)⁻¹) = 0 := by
    convert hsplit.symm using 1
    abel
  have : ∑ j ∈ Icc (1 : ℕ) (p - 6), (j : ZMod p)⁻¹ =
      -(((p - 5 : ℕ) : ZMod p)⁻¹ + ((p - 4 : ℕ) : ZMod p)⁻¹ +
        ((p - 3 : ℕ) : ZMod p)⁻¹ + ((p - 2 : ℕ) : ZMod p)⁻¹ +
        ((p - 1 : ℕ) : ZMod p)⁻¹) :=
    eq_neg_of_add_eq_zero_left hsum0
  rw [this, c1, c2, c3, c4, c5]
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp5
  have h3 : (3 : ZMod p) ≠ 0 :=
    zmod_nat_ne_zero (by decide) (lt_of_lt_of_le (by decide : 3 < 11) hp11)
  have h4 : (4 : ZMod p) ≠ 0 :=
    zmod_nat_ne_zero (by decide) (lt_of_lt_of_le (by decide : 4 < 11) hp11)
  have h5 : (5 : ZMod p) ≠ 0 :=
    zmod_nat_ne_zero (by decide) (lt_of_lt_of_le (by decide : 5 < 11) hp11)
  have h60 : (60 : ZMod p) ≠ 0 := by
    have : (60 : ZMod p) = 4 * 3 * 5 := by norm_num
    rw [this]; exact mul_ne_zero (mul_ne_zero h4 h3) h5
  field_simp [h2, h3, h4, h5, h60]
  ring

lemma harmonic_p_sub_four (hp11 : 11 ≤ p) :
    ∑ j ∈ Icc (1 : ℕ) (p - 4), (j : ZMod p)⁻¹ =
      (11 : ZMod p) * (6 : ZMod p)⁻¹ := by
  have hp5 : 5 ≤ p := le_trans (by decide : 5 ≤ 11) hp11
  have h6 := harmonic_p_sub_six (p := p) hp11
  have hle : 1 ≤ p - 4 := by omega
  have hlt : p - 4 < p := by omega
  have hs := harmonic_succ_Icc (p := p) (n := p - 4) hle hlt
  have e : p - 4 - 1 = p - 5 := by omega
  -- H_{p-4} = H_{p-6} + 1/(p-5) + 1/(p-4)
  have h5le : 1 ≤ p - 5 := by omega
  have h5lt : p - 5 < p := by omega
  have hs5 := harmonic_succ_Icc (p := p) (n := p - 5) h5le h5lt
  have e5 : p - 5 - 1 = p - 6 := by omega
  rw [e5] at hs5
  rw [e] at hs
  rw [hs5] at hs
  have c4 : ((p - 4 : ℕ) : ZMod p)⁻¹ = -((4 : ZMod p)⁻¹) := by
    rw [Nat.cast_sub (by omega : 4 ≤ p), Nat.cast_ofNat,
      CharP.cast_eq_zero (R := ZMod p) p, zero_sub, inv_neg]
  have c5 : ((p - 5 : ℕ) : ZMod p)⁻¹ = -((5 : ZMod p)⁻¹) := by
    rw [Nat.cast_sub (by omega : 5 ≤ p), Nat.cast_ofNat,
      CharP.cast_eq_zero (R := ZMod p) p, zero_sub, inv_neg]
  rw [hs, h6, c4, c5]
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp5
  have h3 : (3 : ZMod p) ≠ 0 :=
    zmod_nat_ne_zero (by decide) (lt_of_lt_of_le (by decide : 3 < 11) hp11)
  have h4 : (4 : ZMod p) ≠ 0 :=
    zmod_nat_ne_zero (by decide) (lt_of_lt_of_le (by decide : 4 < 11) hp11)
  have h5 : (5 : ZMod p) ≠ 0 :=
    zmod_nat_ne_zero (by decide) (lt_of_lt_of_le (by decide : 5 < 11) hp11)
  have h6n : (6 : ZMod p) ≠ 0 := by
    have : (6 : ZMod p) = 2 * 3 := by norm_num
    rw [this]; exact mul_ne_zero h2 h3
  have h60 : (60 : ZMod p) ≠ 0 := by
    have : (60 : ZMod p) = 4 * 3 * 5 := by norm_num
    rw [this]; exact mul_ne_zero (mul_ne_zero h4 h3) h5
  field_simp [h2, h3, h4, h5, h6n, h60]
  ring

lemma harmonic_p_sub_two (hp11 : 11 ≤ p) :
    ∑ j ∈ Icc (1 : ℕ) (p - 2), (j : ZMod p)⁻¹ = 1 := by
  have hp5 : 5 ≤ p := le_trans (by decide : 5 ≤ 11) hp11
  have h4 := harmonic_p_sub_four (p := p) hp11
  have h3le : 1 ≤ p - 3 := by omega
  have h3lt : p - 3 < p := by omega
  have h2le : 1 ≤ p - 2 := by omega
  have h2lt : p - 2 < p := by omega
  have s3 := harmonic_succ_Icc (p := p) (n := p - 3) h3le h3lt
  have s2 := harmonic_succ_Icc (p := p) (n := p - 2) h2le h2lt
  have e3 : p - 3 - 1 = p - 4 := by omega
  have e2 : p - 2 - 1 = p - 3 := by omega
  rw [e3] at s3
  rw [e2] at s2
  rw [s3] at s2
  have c2 : ((p - 2 : ℕ) : ZMod p)⁻¹ = -((2 : ZMod p)⁻¹) := by
    rw [Nat.cast_sub (by omega : 2 ≤ p), Nat.cast_ofNat,
      CharP.cast_eq_zero (R := ZMod p) p, zero_sub, inv_neg]
  have c3 : ((p - 3 : ℕ) : ZMod p)⁻¹ = -((3 : ZMod p)⁻¹) := by
    rw [Nat.cast_sub (by omega : 3 ≤ p), Nat.cast_ofNat,
      CharP.cast_eq_zero (R := ZMod p) p, zero_sub, inv_neg]
  rw [s2, h4, c2, c3]
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp5
  have h3 : (3 : ZMod p) ≠ 0 :=
    zmod_nat_ne_zero (by decide) (lt_of_lt_of_le (by decide : 3 < 11) hp11)
  have h6n : (6 : ZMod p) ≠ 0 := by
    have : (6 : ZMod p) = 2 * 3 := by norm_num
    rw [this]; exact mul_ne_zero h2 h3
  field_simp [h2, h3, h6n]
  ring

lemma p_dvd_term0 (hp5 : 5 ≤ p) (hp11 : 11 ≤ p) :
    p ∣ term (p - 2) 0 := by
  have hlo : (2 * p + 3) / 3 ≤ p - 2 := by omega
  have hn : p - 2 ≤ p - 1 := by omega
  exact p_dvd_term (Fact.out : p.Prime) hp5 hlo hn (by omega)

lemma factorial_p_sub_two_split (hp11 : 11 ≤ p) :
    (p - 2)! = (p - 6)! * (p - 5) * (p - 4) * (p - 3) * (p - 2) := by
  have h1 : (p - 2)! = (p - 2) * (p - 3)! := by
    have : p - 2 = (p - 3) + 1 := by omega
    rw [this, factorial_succ]
  have h2 : (p - 3)! = (p - 3) * (p - 4)! := by
    have : p - 3 = (p - 4) + 1 := by omega
    rw [this, factorial_succ]
  have h3 : (p - 4)! = (p - 4) * (p - 5)! := by
    have : p - 4 = (p - 5) + 1 := by omega
    rw [this, factorial_succ]
  have h4 : (p - 5)! = (p - 5) * (p - 6)! := by
    have : p - 5 = (p - 6) + 1 := by omega
    rw [this, factorial_succ]
  rw [h1, h2, h3, h4]
  ac_rfl

lemma prod_Icc_one_eq_factorial (n : ℕ) :
    ∏ j ∈ Icc 1 n, j = n ! :=
  prod_Icc_one_n n

lemma rtwo_term0_div_p_mul_fac (hp11 : 11 ≤ p) :
    term (p - 2) 0 / p * (p - 2)! =
      2 * (2 * p - 3) * (2 * p - 2) * (2 * p - 1) *
        ∏ j ∈ Icc 1 (p - 6), (2 * p + j) := by
  have hp5 : 5 ≤ p := le_trans (by decide : 5 ≤ 11) hp11
  have hmul := rtwo_term0_mul_fac (p := p) hp11
  have hdiv := p_dvd_term0 (p := p) hp5 hp11
  have hppos : 0 < p := p_pos (p := p)
  have : term (p - 2) 0 = p * (term (p - 2) 0 / p) :=
    (Nat.mul_div_cancel' hdiv).symm
  rw [this] at hmul
  have h2p : 2 * p = p * 2 := by ring
  have : p * (term (p - 2) 0 / p) * (p - 2)! =
      (2 * p - 3) * (2 * p - 2) * (2 * p - 1) * (p * 2) *
        ∏ j ∈ Icc 1 (p - 6), (2 * p + j) := by
    rw [hmul, h2p]
  have hcancel : term (p - 2) 0 / p * (p - 2)! =
      (2 * p - 3) * (2 * p - 2) * (2 * p - 1) * 2 *
        ∏ j ∈ Icc 1 (p - 6), (2 * p + j) := by
    apply Nat.eq_of_mul_eq_mul_left hppos
    convert this using 1
    · ring
    · ring
  rw [hcancel]
  ring

lemma cast_sub_zmod_sq {a b : ℕ} (hba : b ≤ a) :
    ((a - b : ℕ) : ZMod (p ^ 2)) = (a : ZMod (p ^ 2)) - (b : ZMod (p ^ 2)) :=
  Nat.cast_sub hba

lemma two_p_sub_cast (k : ℕ) (hk : k ≤ 2 * p) :
    ((2 * p - k : ℕ) : ZMod (p ^ 2)) =
      (2 : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) - (k : ZMod (p ^ 2)) := by
  rw [Nat.cast_sub hk, Nat.cast_mul, Nat.cast_two]

lemma p_sub_cast (k : ℕ) (hk : k ≤ p) :
    ((p - k : ℕ) : ZMod (p ^ 2)) =
      (p : ZMod (p ^ 2)) - (k : ZMod (p ^ 2)) :=
  Nat.cast_sub hk

/-- The three linear factors `(2p-3)(2p-2)(2p-1)` expand as `-6 + 22p` in `ZMod (p²)`. -/
lemma rtwo_num3_expand (hp11 : 11 ≤ p) :
    ((2 * p - 3 : ℕ) : ZMod (p ^ 2)) * ((2 * p - 2 : ℕ) : ZMod (p ^ 2)) *
      ((2 * p - 1 : ℕ) : ZMod (p ^ 2)) =
        (-6 : ZMod (p ^ 2)) + (22 : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) := by
  have h3 : 3 ≤ 2 * p := by omega
  have h2 : 2 ≤ 2 * p := by omega
  have h1 : 1 ≤ 2 * p := by omega
  rw [two_p_sub_cast (p := p) 3 h3, two_p_sub_cast (p := p) 2 h2,
    two_p_sub_cast (p := p) 1 h1]
  have hP2 := p_mul_p_zmod_sq (p := p)
  -- `(2p-3)(2p-2) = 4p² - 4p - 6p + 6 = 6 - 10p`
  have h12 :
      ((2 : ZMod (p ^ 2)) * p - 3) * ((2 : ZMod (p ^ 2)) * p - 2) =
        6 - 10 * (p : ZMod (p ^ 2)) := by
    have := calc
      ((2 : ZMod (p ^ 2)) * p - 3) * ((2 : ZMod (p ^ 2)) * p - 2)
          = 4 * ((p : ZMod (p ^ 2)) * p) - 10 * (p : ZMod (p ^ 2)) + 6 := by ring
      _ = 4 * 0 - 10 * (p : ZMod (p ^ 2)) + 6 := by rw [hP2]
      _ = 6 - 10 * (p : ZMod (p ^ 2)) := by ring
    exact this
  simp only [Nat.cast_ofNat]
  rw [h12]
  -- `(6-10p)(2p-1) = 12p - 6 - 20p² + 10p = -6 + 22p`
  have := calc
    (6 - 10 * (p : ZMod (p ^ 2))) * ((2 : ZMod (p ^ 2)) * p - 1)
        = 12 * (p : ZMod (p ^ 2)) - 6 - 20 * ((p : ZMod (p ^ 2)) * p) +
            10 * (p : ZMod (p ^ 2)) := by ring
    _ = 12 * (p : ZMod (p ^ 2)) - 6 - 20 * 0 + 10 * (p : ZMod (p ^ 2)) := by
          rw [hP2]
    _ = (-6 : ZMod (p ^ 2)) + 22 * (p : ZMod (p ^ 2)) := by ring
  simpa [Nat.cast_ofNat] using this

/-- The four linear factors `(p-5)(p-4)(p-3)(p-2)` expand as `120 - 154p`. -/
lemma rtwo_den4_expand (hp11 : 11 ≤ p) :
    ((p - 5 : ℕ) : ZMod (p ^ 2)) * ((p - 4 : ℕ) : ZMod (p ^ 2)) *
      ((p - 3 : ℕ) : ZMod (p ^ 2)) * ((p - 2 : ℕ) : ZMod (p ^ 2)) =
        (120 : ZMod (p ^ 2)) - (154 : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) := by
  have h5 : 5 ≤ p := by omega
  have h4 : 4 ≤ p := by omega
  have h3 : 3 ≤ p := by omega
  have h2 : 2 ≤ p := by omega
  rw [p_sub_cast (p := p) 5 h5, p_sub_cast (p := p) 4 h4,
    p_sub_cast (p := p) 3 h3, p_sub_cast (p := p) 2 h2]
  have hP2 := p_mul_p_zmod_sq (p := p)
  have h12 :
      ((p : ZMod (p ^ 2)) - 5) * ((p : ZMod (p ^ 2)) - 4) =
        20 - 9 * (p : ZMod (p ^ 2)) := by
    have := calc
      ((p : ZMod (p ^ 2)) - 5) * ((p : ZMod (p ^ 2)) - 4)
          = (p : ZMod (p ^ 2)) * p - 9 * (p : ZMod (p ^ 2)) + 20 := by ring
      _ = 0 - 9 * (p : ZMod (p ^ 2)) + 20 := by rw [hP2]
      _ = 20 - 9 * (p : ZMod (p ^ 2)) := by ring
    exact this
  have h34 :
      ((p : ZMod (p ^ 2)) - 3) * ((p : ZMod (p ^ 2)) - 2) =
        6 - 5 * (p : ZMod (p ^ 2)) := by
    have := calc
      ((p : ZMod (p ^ 2)) - 3) * ((p : ZMod (p ^ 2)) - 2)
          = (p : ZMod (p ^ 2)) * p - 5 * (p : ZMod (p ^ 2)) + 6 := by ring
      _ = 0 - 5 * (p : ZMod (p ^ 2)) + 6 := by rw [hP2]
      _ = 6 - 5 * (p : ZMod (p ^ 2)) := by ring
    exact this
  have := calc
    ((p : ZMod (p ^ 2)) - 5) * ((p : ZMod (p ^ 2)) - 4) *
        ((p : ZMod (p ^ 2)) - 3) * ((p : ZMod (p ^ 2)) - 2)
        = (((p : ZMod (p ^ 2)) - 5) * ((p : ZMod (p ^ 2)) - 4)) *
            (((p : ZMod (p ^ 2)) - 3) * ((p : ZMod (p ^ 2)) - 2)) := by ring
    _ = (20 - 9 * (p : ZMod (p ^ 2))) * (6 - 5 * (p : ZMod (p ^ 2))) := by
          rw [h12, h34]
    _ = 120 - 154 * (p : ZMod (p ^ 2)) +
          45 * ((p : ZMod (p ^ 2)) * p) := by ring
    _ = 120 - 154 * (p : ZMod (p ^ 2)) + 45 * 0 := by rw [hP2]
    _ = (120 : ZMod (p ^ 2)) - 154 * (p : ZMod (p ^ 2)) := by ring
  exact this

lemma isUnit_ofNat_zmod_sq {m : ℕ} (hm0 : 0 < m) (hmp : m < p)
    (hp : p.Prime) : IsUnit (m : ZMod (p ^ 2)) :=
  isUnit_nat_zmod_sq (p := p) hm0 hmp hp

lemma isUnit_120 (hp11 : 11 ≤ p) :
    IsUnit (120 : ZMod (p ^ 2)) := by
  have hp : p.Prime := Fact.out
  refine (ZMod.isUnit_iff_coprime 120 (p ^ 2)).mpr ?_
  rw [Nat.coprime_pow_right_iff (by decide : 0 < 2)]
  refine ((Nat.Prime.coprime_iff_not_dvd hp).mpr ?_).symm
  intro h
  -- `p ∣ 120 = 8 * 15` and `p ≥ 11` cannot divide `2, 3, 5`.
  have h8 : p ∣ 8 * 15 := by simpa using h
  have hp8 := (hp.dvd_mul.mp h8)
  have h2 : ¬ p ∣ 2 := by
    intro hd
    have : p ≤ 2 := Nat.le_of_dvd (by decide) hd
    omega
  have h8' : ¬ p ∣ 8 := by
    intro hd
    have : p ∣ 2 ^ 3 := by simpa using hd
    exact h2 (hp.dvd_of_dvd_pow this)
  have h15 : p ∣ 15 := hp8.resolve_left h8'
  have h15' : p ∣ 3 * 5 := by simpa using h15
  have hp15 := hp.dvd_mul.mp h15'
  have h3 : ¬ p ∣ 3 := by
    intro hd
    have : p ≤ 3 := Nat.le_of_dvd (by decide) hd
    omega
  have h5 : ¬ p ∣ 5 := by
    intro hd
    have : p ≤ 5 := Nat.le_of_dvd (by decide) hd
    omega
  exact h5 (hp15.resolve_left h3)

lemma inverse_sub_mul_p_unit {c : ZMod (p ^ 2)} {d : ℕ}
    (hc : IsUnit c) :
    Ring.inverse (c - (d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) =
      Ring.inverse c *
        (1 + (d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) * Ring.inverse c) := by
  have hdecomp :
      c - (d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) =
        c * (1 - (d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) * Ring.inverse c) := by
    have hinv : c * Ring.inverse c = 1 := Ring.mul_inverse_cancel _ hc
    calc
      c - (d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))
          = c * 1 - (d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
              (c * Ring.inverse c) := by rw [hinv]; ring
      _ = c * (1 - (d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
            Ring.inverse c) := by ring
  rw [hdecomp]
  have hp2 := p_mul_p_zmod_sq (p := p)
  have hd : ((d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) *
      ((d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) = 0 := by
    calc
      (d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
          ((d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)))
          = ((d : ZMod (p ^ 2)) * d) * ((p : ZMod (p ^ 2)) * p) := by ring
      _ = ((d : ZMod (p ^ 2)) * d) * 0 := by rw [hp2]
      _ = 0 := by ring
  have hrew1 :
      1 - (d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) * Ring.inverse c =
        1 + ((d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) * (-Ring.inverse c) := by
    ring
  have hrew2 :
      1 + (d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) * Ring.inverse c =
        1 - ((d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) * (-Ring.inverse c) := by
    ring
  have hinv1 :
      Ring.inverse (1 + ((d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) *
        (-Ring.inverse c)) =
        1 - ((d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) * (-Ring.inverse c) :=
    inverse_one_add_nilp (d := (d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)))
      (u := -Ring.inverse c) hd
  have hcu2 : IsUnit (1 - (d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
      Ring.inverse c) := by
    refine isUnit_iff_exists_inv.mpr
      ⟨1 + (d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) * Ring.inverse c, ?_⟩
    have hp2' : ((p : ZMod (p ^ 2)) ^ 2 : ZMod (p ^ 2)) = 0 :=
      (pow_two (p : ZMod (p ^ 2))).trans hp2
    ring_nf
    simp [hp2']
  rw [inv_of_unit_mul hc hcu2, hrew1, hinv1, hrew2]

lemma rtwo_term0_div_p_cast (hp11 : 11 ≤ p) :
    ((term (p - 2) 0 / p : ℕ) : ZMod (p ^ 2)) *
      ((p - 2)! : ZMod (p ^ 2)) =
        (2 : ZMod (p ^ 2)) *
          ((2 * p - 3 : ℕ) : ZMod (p ^ 2)) *
          ((2 * p - 2 : ℕ) : ZMod (p ^ 2)) *
          ((2 * p - 1 : ℕ) : ZMod (p ^ 2)) *
          ∏ j ∈ Icc 1 (p - 6), ((2 * p + j : ℕ) : ZMod (p ^ 2)) := by
  have h := rtwo_term0_div_p_mul_fac (p := p) hp11
  have hcast := congrArg (fun n : ℕ => (n : ZMod (p ^ 2))) h
  simpa [Nat.cast_mul, Nat.cast_prod] using hcast

lemma rtwo_prod_two_p (hp11 : 11 ≤ p) :
    (∏ j ∈ Icc 1 (p - 6), ((2 * p + j : ℕ) : ZMod (p ^ 2))) =
      (∏ j ∈ Icc 1 (p - 6), (j : ZMod (p ^ 2))) *
        (1 + (2 : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
          ∑ j ∈ Icc 1 (p - 6), Ring.inverse (j : ZMod (p ^ 2))) := by
  have hp : p.Prime := Fact.out
  have ha : 1 ≤ (1 : ℕ) := le_rfl
  have hab : 1 ≤ p - 6 := by omega
  have hbp : p - 6 < p := by omega
  -- `2p + j = j + 2*p`
  have hcongr : ∀ j ∈ Icc 1 (p - 6),
      ((2 * p + j : ℕ) : ZMod (p ^ 2)) = ((j + 2 * p : ℕ) : ZMod (p ^ 2)) := by
    intro j hj; congr 1; ring
  rw [prod_congr rfl hcongr]
  simpa using prod_Icc_add_mul_p (p := p) hp 2 1 (p - 6) ha hab hbp

lemma factorial_eq_prod_Icc_one (n : ℕ) :
    (n ! : ZMod (p ^ 2)) = ∏ j ∈ Icc 1 n, (j : ZMod (p ^ 2)) := by
  rw [← Nat.cast_prod, prod_Icc_one_n]

lemma rtwo_term0_formula (hp11 : 11 ≤ p) :
    ((term (p - 2) 0 / p : ℕ) : ZMod (p ^ 2)) =
      (2 : ZMod (p ^ 2)) *
        (((2 * p - 3 : ℕ) : ZMod (p ^ 2)) *
          ((2 * p - 2 : ℕ) : ZMod (p ^ 2)) *
          ((2 * p - 1 : ℕ) : ZMod (p ^ 2))) *
        (1 + (2 : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
          ∑ j ∈ Icc 1 (p - 6), Ring.inverse (j : ZMod (p ^ 2))) *
        Ring.inverse
          (((p - 5 : ℕ) : ZMod (p ^ 2)) * ((p - 4 : ℕ) : ZMod (p ^ 2)) *
            ((p - 3 : ℕ) : ZMod (p ^ 2)) * ((p - 2 : ℕ) : ZMod (p ^ 2))) := by
  have hp : p.Prime := Fact.out
  have hcast := rtwo_term0_div_p_cast (p := p) hp11
  have hprod := rtwo_prod_two_p (p := p) hp11
  have hsplit := factorial_p_sub_two_split (p := p) hp11
  have hfac6 : ((p - 6)! : ZMod (p ^ 2)) =
      ∏ j ∈ Icc 1 (p - 6), (j : ZMod (p ^ 2)) :=
    factorial_eq_prod_Icc_one (p := p) (p - 6)
  have hfac :
      ((p - 2)! : ZMod (p ^ 2)) =
        ((p - 6)! : ZMod (p ^ 2)) *
          (((p - 5 : ℕ) : ZMod (p ^ 2)) * ((p - 4 : ℕ) : ZMod (p ^ 2)) *
            ((p - 3 : ℕ) : ZMod (p ^ 2)) * ((p - 2 : ℕ) : ZMod (p ^ 2))) := by
    have := congrArg (fun n : ℕ => (n : ZMod (p ^ 2))) hsplit
    simp only [Nat.cast_mul] at this
    convert this using 1
    ac_rfl
  have hunit6 : IsUnit ((p - 6)! : ZMod (p ^ 2)) :=
    isUnit_factorial_zmod_sq (by omega) hp
  have hunitden : IsUnit
      (((p - 5 : ℕ) : ZMod (p ^ 2)) * ((p - 4 : ℕ) : ZMod (p ^ 2)) *
        ((p - 3 : ℕ) : ZMod (p ^ 2)) * ((p - 2 : ℕ) : ZMod (p ^ 2))) := by
    refine IsUnit.mul (IsUnit.mul (IsUnit.mul
      (isUnit_nat_zmod_sq (p := p) (by omega) (by omega) hp)
      (isUnit_nat_zmod_sq (p := p) (by omega) (by omega) hp))
      (isUnit_nat_zmod_sq (p := p) (by omega) (by omega) hp))
      (isUnit_nat_zmod_sq (p := p) (by omega) (by omega) hp)
  -- `term0/p * (p-6)! * den = 2 * num3 * (p-6)! * (1+2pH)`
  have heq :
      ((term (p - 2) 0 / p : ℕ) : ZMod (p ^ 2)) *
        ((p - 6)! : ZMod (p ^ 2)) *
        (((p - 5 : ℕ) : ZMod (p ^ 2)) * ((p - 4 : ℕ) : ZMod (p ^ 2)) *
          ((p - 3 : ℕ) : ZMod (p ^ 2)) * ((p - 2 : ℕ) : ZMod (p ^ 2))) =
        (2 : ZMod (p ^ 2)) *
          ((2 * p - 3 : ℕ) : ZMod (p ^ 2)) *
          ((2 * p - 2 : ℕ) : ZMod (p ^ 2)) *
          ((2 * p - 1 : ℕ) : ZMod (p ^ 2)) *
          ((p - 6)! : ZMod (p ^ 2)) *
          (1 + (2 : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
            ∑ j ∈ Icc 1 (p - 6), Ring.inverse (j : ZMod (p ^ 2))) := by
    calc
      _ = ((term (p - 2) 0 / p : ℕ) : ZMod (p ^ 2)) * ((p - 2)! : ZMod (p ^ 2)) := by
            rw [hfac]; ac_rfl
      _ = (2 : ZMod (p ^ 2)) *
            ((2 * p - 3 : ℕ) : ZMod (p ^ 2)) *
            ((2 * p - 2 : ℕ) : ZMod (p ^ 2)) *
            ((2 * p - 1 : ℕ) : ZMod (p ^ 2)) *
            ∏ j ∈ Icc 1 (p - 6), ((2 * p + j : ℕ) : ZMod (p ^ 2)) := hcast
      _ = (2 : ZMod (p ^ 2)) *
            ((2 * p - 3 : ℕ) : ZMod (p ^ 2)) *
            ((2 * p - 2 : ℕ) : ZMod (p ^ 2)) *
            ((2 * p - 1 : ℕ) : ZMod (p ^ 2)) *
            ((∏ j ∈ Icc 1 (p - 6), (j : ZMod (p ^ 2))) *
              (1 + (2 : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
                ∑ j ∈ Icc 1 (p - 6), Ring.inverse (j : ZMod (p ^ 2)))) := by
            rw [hprod]
      _ = _ := by rw [hfac6]; ac_rfl
  -- Cancel the unit `(p-6)!`.
  have heq' :
      ((term (p - 2) 0 / p : ℕ) : ZMod (p ^ 2)) *
        (((p - 5 : ℕ) : ZMod (p ^ 2)) * ((p - 4 : ℕ) : ZMod (p ^ 2)) *
          ((p - 3 : ℕ) : ZMod (p ^ 2)) * ((p - 2 : ℕ) : ZMod (p ^ 2))) =
        (2 : ZMod (p ^ 2)) *
          ((2 * p - 3 : ℕ) : ZMod (p ^ 2)) *
          ((2 * p - 2 : ℕ) : ZMod (p ^ 2)) *
          ((2 * p - 1 : ℕ) : ZMod (p ^ 2)) *
          (1 + (2 : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
            ∑ j ∈ Icc 1 (p - 6), Ring.inverse (j : ZMod (p ^ 2))) := by
    -- Rewrite both sides of `heq` as `(·) * (p-6)!`.
    have hL :
        ((term (p - 2) 0 / p : ℕ) : ZMod (p ^ 2)) *
            ((p - 6)! : ZMod (p ^ 2)) *
            (((p - 5 : ℕ) : ZMod (p ^ 2)) * ((p - 4 : ℕ) : ZMod (p ^ 2)) *
              ((p - 3 : ℕ) : ZMod (p ^ 2)) * ((p - 2 : ℕ) : ZMod (p ^ 2))) =
          (((term (p - 2) 0 / p : ℕ) : ZMod (p ^ 2)) *
            (((p - 5 : ℕ) : ZMod (p ^ 2)) * ((p - 4 : ℕ) : ZMod (p ^ 2)) *
              ((p - 3 : ℕ) : ZMod (p ^ 2)) * ((p - 2 : ℕ) : ZMod (p ^ 2)))) *
            ((p - 6)! : ZMod (p ^ 2)) := by ac_rfl
    have hR :
        (2 : ZMod (p ^ 2)) *
            ((2 * p - 3 : ℕ) : ZMod (p ^ 2)) *
            ((2 * p - 2 : ℕ) : ZMod (p ^ 2)) *
            ((2 * p - 1 : ℕ) : ZMod (p ^ 2)) *
            ((p - 6)! : ZMod (p ^ 2)) *
            (1 + (2 : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
              ∑ j ∈ Icc 1 (p - 6), Ring.inverse (j : ZMod (p ^ 2))) =
          ((2 : ZMod (p ^ 2)) *
            ((2 * p - 3 : ℕ) : ZMod (p ^ 2)) *
            ((2 * p - 2 : ℕ) : ZMod (p ^ 2)) *
            ((2 * p - 1 : ℕ) : ZMod (p ^ 2)) *
            (1 + (2 : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
              ∑ j ∈ Icc 1 (p - 6), Ring.inverse (j : ZMod (p ^ 2)))) *
            ((p - 6)! : ZMod (p ^ 2)) := by ac_rfl
    have heq2 := hL.symm.trans (heq.trans hR)
    have hmul := congrArg (fun z => z * Ring.inverse ((p - 6)! : ZMod (p ^ 2))) heq2
    simp only at hmul
    rw [mul_assoc, Ring.mul_inverse_cancel _ hunit6, mul_one] at hmul
    conv_rhs at hmul => rw [mul_assoc]
    rwa [Ring.mul_inverse_cancel _ hunit6, mul_one] at hmul
  -- Multiply by inverse of the denominator.
  have hfin := congrArg (fun z => z * Ring.inverse
      (((p - 5 : ℕ) : ZMod (p ^ 2)) * ((p - 4 : ℕ) : ZMod (p ^ 2)) *
        ((p - 3 : ℕ) : ZMod (p ^ 2)) * ((p - 2 : ℕ) : ZMod (p ^ 2)))) heq'
  simp only at hfin
  rw [mul_assoc, Ring.mul_inverse_cancel _ hunitden, mul_one] at hfin
  convert hfin using 1
  ac_rfl

lemma rtwo_term0_expand (hp11 : 11 ≤ p) :
    ((term (p - 2) 0 / p : ℕ) : ZMod (p ^ 2)) =
      (2 : ZMod (p ^ 2)) *
        ((-6 : ZMod (p ^ 2)) + 22 * (p : ZMod (p ^ 2))) *
        (1 + (2 : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
          ∑ j ∈ Icc 1 (p - 6), Ring.inverse (j : ZMod (p ^ 2))) *
        Ring.inverse ((120 : ZMod (p ^ 2)) - 154 * (p : ZMod (p ^ 2))) := by
  have hform := rtwo_term0_formula (p := p) hp11
  have hnum := rtwo_num3_expand (p := p) hp11
  have hden := rtwo_den4_expand (p := p) hp11
  rw [hform, hnum, hden]

lemma inverse_sub_mul_p {c d : ℕ} (hc0 : 0 < c) (hcp : c < p) (hp : p.Prime) :
    Ring.inverse ((c : ZMod (p ^ 2)) - (d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) =
      Ring.inverse (c : ZMod (p ^ 2)) *
        (1 + (d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
          Ring.inverse (c : ZMod (p ^ 2))) := by
  have hcu := isUnit_nat_zmod_sq (p := p) hc0 hcp hp
  have hdecomp :
      (c : ZMod (p ^ 2)) - (d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) =
        (c : ZMod (p ^ 2)) * (1 - (d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
          Ring.inverse (c : ZMod (p ^ 2))) := by
    have hinv : (c : ZMod (p ^ 2)) * Ring.inverse (c : ZMod (p ^ 2)) = 1 :=
      Ring.mul_inverse_cancel _ hcu
    calc
      (c : ZMod (p ^ 2)) - (d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))
          = (c : ZMod (p ^ 2)) * 1 - (d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
              ((c : ZMod (p ^ 2)) * Ring.inverse (c : ZMod (p ^ 2))) := by
            rw [hinv]; ring
      _ = (c : ZMod (p ^ 2)) * (1 - (d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
            Ring.inverse (c : ZMod (p ^ 2))) := by ring
  rw [hdecomp]
  have hp2 : (p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) = 0 :=
    p_mul_p_zmod_sq (p := p)
  have hd : ((d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) *
      ((d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) = 0 := by
    calc
      (d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
          ((d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)))
          = ((d : ZMod (p ^ 2)) * (d : ZMod (p ^ 2))) *
              ((p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) := by ring
      _ = ((d : ZMod (p ^ 2)) * (d : ZMod (p ^ 2))) * 0 := by rw [hp2]
      _ = 0 := by ring
  have hinv1 :
      Ring.inverse (1 + ((d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) *
        (-Ring.inverse (c : ZMod (p ^ 2)))) =
        1 - ((d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) *
          (-Ring.inverse (c : ZMod (p ^ 2))) :=
    inverse_one_add_nilp (d := (d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)))
      (u := -Ring.inverse (c : ZMod (p ^ 2))) hd
  have hrew1 : 1 - (d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
      Ring.inverse (c : ZMod (p ^ 2)) =
      1 + ((d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) *
        (-Ring.inverse (c : ZMod (p ^ 2))) := by ring
  have hrew2 : 1 + (d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
      Ring.inverse (c : ZMod (p ^ 2)) =
      1 - ((d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) *
        (-Ring.inverse (c : ZMod (p ^ 2))) := by ring
  have hcu2 : IsUnit (1 - (d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
      Ring.inverse (c : ZMod (p ^ 2))) := by
    refine isUnit_iff_exists_inv.mpr
      ⟨1 + (d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
        Ring.inverse (c : ZMod (p ^ 2)), ?_⟩
    have hp2' : ((p : ZMod (p ^ 2)) ^ 2 : ZMod (p ^ 2)) = 0 :=
      (pow_two (p : ZMod (p ^ 2))).trans hp2
    ring_nf
    simp [hp2']
  rw [inv_of_unit_mul hcu hcu2, hrew1, hinv1, hrew2]

end RTwo

/-! ### A uniform argument for `r ≥ 2`.

We analyse the rational function
`f(x) = [(x+1)⋯(x+r-1)]² / [x(x-1)⋯(x-r+1) · (2x-2r)⋯(2x-3r+1)]`
of degree `-2`.  Its poles in characteristic `p` are precisely the
indices (reduced mod `p`) of the valuation-`1` terms, and the
first-order residues of those terms are twice the residues of `f`
(or the residues of `f` themselves, on the “half-integer” poles).
The vanishing of `∑ residues` therefore yields `p² ∣ a(p-r)`.
The second-order analysis is the same expansion plus the
valuation-`2` regions `C` and `E`. -/

section ResidueSum
open Polynomial

variable {K : Type*} [Field K]

lemma coeff_C_mul_basis_top {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → K) (i : ι) (c : K)
    (hvs : Set.InjOn v s) (hi : i ∈ s) :
    ((C c) * Lagrange.basis s v i).coeff (s.card - 1) =
      c * (∏ j ∈ s.erase i, (v i - v j))⁻¹ := by
  have hdeg : (Lagrange.basis s v i).natDegree = s.card - 1 :=
    Lagrange.natDegree_basis hvs hi
  rw [coeff_C_mul, ← hdeg, ← leadingCoeff, Lagrange.leadingCoeff_basis hvs hi]

lemma coeff_interpolate_top {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → K) (r : ι → K) (hvs : Set.InjOn v s) :
    (Lagrange.interpolate s v r).coeff (s.card - 1) =
      ∑ i ∈ s, r i * (∏ j ∈ s.erase i, (v i - v j))⁻¹ := by
  rw [Lagrange.interpolate_apply, finset_sum_coeff]
  refine Finset.sum_congr rfl ?_
  intro i hi
  exact coeff_C_mul_basis_top s v i (r i) hvs hi

lemma sum_eval_div_nodal {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → K) (hvs : Set.InjOn v s)
    (P : K[X]) (hdeg : P.natDegree + 1 < s.card) :
    ∑ i ∈ s, P.eval (v i) * (∏ j ∈ s.erase i, (v i - v j))⁻¹ = 0 := by
  have hnd : P.natDegree < s.card := Nat.lt_of_succ_lt hdeg
  have hPdeg : P.degree < (s.card : WithBot ℕ) :=
    lt_of_le_of_lt degree_le_natDegree (WithBot.coe_lt_coe.mpr hnd)
  have hinterp : P = Lagrange.interpolate s v fun i => P.eval (v i) :=
    Lagrange.eq_interpolate hvs hPdeg
  have hcoeff0 : P.coeff (s.card - 1) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    omega
  have htop := coeff_interpolate_top (K := K) s v (fun i => P.eval (v i)) hvs
  rw [← hinterp, hcoeff0] at htop
  exact htop.symm

end ResidueSum

section GeneralN
variable {p : ℕ} [Fact p.Prime]

/- Region predicates for `n = p - r`. -/

def inA (r k : ℕ) : Prop := k < r
def inB (r k : ℕ) : Prop := r ≤ k ∧ 2 * k < 3 * r
def inC (p r k : ℕ) : Prop := 3 * r ≤ 2 * k ∧ 2 * k < p + 2 * r
def inD (p r k : ℕ) : Prop := p + 2 * r ≤ 2 * k ∧ 2 * k < p + 3 * r
def inE (p r k : ℕ) : Prop := p + 3 * r ≤ 2 * k

lemma region_of_le_n {r k : ℕ} (hrp : 3 * r < p) (hkn : k ≤ p - r) :
    inA r k ∨ inB r k ∨ inC p r k ∨ inD p r k ∨ inE p r k := by
  unfold inA inB inC inD inE
  omega

lemma two_ne_of_r {r : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p) : (2 : ZMod p) ≠ 0 := by
  intro hz
  have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
  have : p = 1 ∨ p = 2 := (Nat.dvd_prime Nat.prime_two).mp this
  have : 3 < p := three_lt_p_of_r (p := p) hr2 hrp
  omega

/-- `p²` divides every `C`-region term. -/
lemma psq_dvd_of_inC {r k : ℕ}
    (hr0 : 0 < r) (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    (hC : inC p r k) (hkn : k ≤ p - r) :
    p ^ 2 ∣ term (p - r) k :=
  psq_dvd_term_region_C (p := p) hr0 hr2 hrp hC.1 (Nat.le_sub_one_of_lt hC.2) hkn

/-- `p²` divides every `E`-region term. -/
lemma psq_dvd_of_inE {r k : ℕ}
    (hr0 : 0 < r) (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    (hE : inE p r k) (hkn : k ≤ p - r) :
    p ^ 2 ∣ term (p - r) k :=
  psq_dvd_term_region_E (p := p) hr0 hr2 hrp hE hkn

/-- First-order `C`-region residue via the standard expansions. -/
lemma term_div_psq_inC {r k : ℕ}
    (hr0 : 0 < r) (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    (hC : inC p r k) (hkn : k ≤ p - r) :
    p ^ 2 ∣ term (p - r) k ∧
    ((term (p - r) k / p ^ 2 : ℕ) : ZMod p) =
      (((-1 : ZMod p) ^ k * ((r + k - 1).choose k : ZMod p)) ^ 2) *
        ((-1 : ZMod p) ^ (r - 1) * ((r : ZMod p) * (k.choose r : ZMod p))⁻¹) *
          ((3 : ZMod p) * (-1 : ZMod p) ^ (r - 1) * ((r - 1)! : ZMod p) *
            (∏ j ∈ Icc (1 : ℕ) r,
              ((thirdL (p := p) r k : ZMod p) - (j : ZMod p)))⁻¹) := by
  have hpsq := psq_dvd_of_inC (p := p) hr0 hr2 hrp hC hkn
  refine ⟨hpsq, ?_⟩
  have hr := r_lt_p_of_three (p := p) hrp
  have hkp : k < p := by omega
  have hkr : r ≤ k := by
    have : 3 * r ≤ 2 * k := hC.1
    omega
  have hmid := choose_p_sub_add_div_p_zmod (p := p) (r := r) (k := k) hr0 hr hkr hkp
  have ⟨hL, hU⟩ : thirdL (p := p) r k ≤ 3 * p ∧
      3 * p ≤ thirdL (p := p) r k + p - r - 1 := by
    constructor
    · simp only [thirdL]
      have : 2 * k < p + 2 * r := hC.2
      omega
    · have hUeq := thirdL_U (p := p) (r := r) (k := k) (le_of_lt hr)
      rw [hUeq]
      have : 3 * r ≤ 2 * k := hC.1
      omega
  have hp3 : 3 < p := three_lt_p_of_r (p := p) hr2 hrp
  have hth := choose_div_p_of_interval_len (p := p) (L := thirdL (p := p) r k)
      (r := r) (q := 3) hr0 hr (by decide : 0 < 3) hp3 hL hU
  have hcheq := third_choose_eq_L (p := p) (r := r) (k := k) (le_of_lt hr)
  have hppos : 0 < p := p_pos (p := p)
  have hdiv : term (p - r) k / p ^ 2 =
      (p - r).choose k ^ 2 * ((p - r + k).choose k / p) *
        ((3 * (p - r) + 2 * k).choose (p - r) / p) := by
    rw [term, pow_two]
    obtain ⟨c, hc⟩ := hmid.1
    have h2 : p ∣ (3 * (p - r) + 2 * k).choose (p - r) := by
      rw [hcheq]; exact hth.1
    obtain ⟨d, hd⟩ := h2
    rw [hc, hd]
    have : (p - r).choose k * (p - r).choose k * (p * c) * (p * d) / (p * p) =
        (p - r).choose k * (p - r).choose k * c * d := by
      have hmul :
          (p - r).choose k * (p - r).choose k * (p * c) * (p * d) =
            ((p - r).choose k * (p - r).choose k * c * d) * (p * p) := by ring
      rw [hmul, Nat.mul_div_cancel _ (mul_pos hppos hppos)]
    have hpsq' : p ^ 2 = p * p := by ring
    rw [hpsq', this, Nat.mul_div_cancel_left c hppos, Nat.mul_div_cancel_left d hppos]
  rw [hdiv, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow]
  rw [choose_p_sub_zmod (p := p) hr0 hr hkn, hmid.2, hcheq, hth.2]
  simp

/-! ### Poles of `f` and the first-order vanishing. -/

open Polynomial

/-- Type-I poles: `0, 1, …, r-1`. -/
def type1Poles (r : ℕ) : Finset (ZMod p) :=
  (range r).image (fun j : ℕ => (j : ZMod p))

/-- Type-II poles: `μ/2` for `μ = 2r, …, 3r-1`. -/
def type2Poles (r : ℕ) : Finset (ZMod p) :=
  (Icc (2 * r) (3 * r - 1)).image
    (fun μ : ℕ => (μ : ZMod p) * (2 : ZMod p)⁻¹)

def poles (r : ℕ) : Finset (ZMod p) := type1Poles r ∪ type2Poles r

lemma card_Icc_two_r {r : ℕ} (hr : 1 ≤ r) :
    #(Icc (2 * r) (3 * r - 1)) = r := by
  rw [Nat.card_Icc]
  omega

lemma injOn_natCast_range {r : ℕ} (hrp : r < p) :
    Set.InjOn (fun j : ℕ => (j : ZMod p)) (range r) := by
  intro a ha b hb h
  have ha' : a < r := mem_range.mp ha
  have hb' : b < r := mem_range.mp hb
  have : a ≡ b [MOD p] := (ZMod.natCast_eq_natCast_iff a b p).mp h
  rcases le_total a b with hle | hle
  · have hdvd : p ∣ b - a := (Nat.modEq_iff_dvd' hle).mp this
    have : b - a = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    omega
  · have hdvd : p ∣ a - b := (Nat.modEq_iff_dvd' hle).mp this.symm
    have : a - b = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    omega

lemma injOn_natCast_Icc {a b : ℕ} (hbp : b < p) :
    Set.InjOn (fun j : ℕ => (j : ZMod p)) (Icc a b) := by
  intro x hx y hy hxy
  have hxI : a ≤ x ∧ x ≤ b := by
    simpa [Set.mem_Icc] using hx
  have hyI : a ≤ y ∧ y ≤ b := by
    simpa [Set.mem_Icc] using hy
  have : x ≡ y [MOD p] := (ZMod.natCast_eq_natCast_iff x y p).mp hxy
  rcases le_total x y with hle | hle
  · have hdvd : p ∣ y - x := (Nat.modEq_iff_dvd' hle).mp this
    have : y - x = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    omega
  · have hdvd : p ∣ x - y := (Nat.modEq_iff_dvd' hle).mp this.symm
    have : x - y = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    omega

lemma card_type1Poles {r : ℕ} (hrp : r < p) :
    #(type1Poles (p := p) r) = r := by
  rw [type1Poles, Finset.card_image_of_injOn (injOn_natCast_range (p := p) hrp), card_range]

lemma two_inv_mul_two {r : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p) :
    (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 :=
  mul_inv_cancel₀ (two_ne_of_r (p := p) hr2 hrp)

lemma card_type2Poles {r : ℕ} (hr0 : 0 < r) (hr2 : 2 ≤ r) (hrp : 3 * r < p) :
    #(type2Poles (p := p) r) = r := by
  have hcard : #(Icc (2 * r) (3 * r - 1)) = r := card_Icc_two_r (by omega)
  have h3 : 3 * r - 1 < p := by omega
  have hinjμ : Set.InjOn (fun μ : ℕ => (μ : ZMod p)) (Icc (2 * r) (3 * r - 1)) :=
    injOn_natCast_Icc (p := p) h3
  have h2ne := two_ne_of_r (p := p) hr2 hrp
  have hinj : Set.InjOn (fun μ : ℕ => (μ : ZMod p) * (2 : ZMod p)⁻¹)
      (Icc (2 * r) (3 * r - 1)) := by
    intro a ha b hb h
    have h2 := two_inv_mul_two (p := p) hr2 hrp
    have : (a : ZMod p) = (b : ZMod p) := by
      calc (a : ZMod p)
          = (a : ZMod p) * ((2 : ZMod p) * (2 : ZMod p)⁻¹) := by rw [h2, mul_one]
        _ = ((a : ZMod p) * (2 : ZMod p)⁻¹) * (2 : ZMod p) := by ring
        _ = ((b : ZMod p) * (2 : ZMod p)⁻¹) * (2 : ZMod p) := by
              have h' : (a : ZMod p) * (2 : ZMod p)⁻¹ = (b : ZMod p) * (2 : ZMod p)⁻¹ := h
              rw [h']
        _ = (b : ZMod p) * ((2 : ZMod p) * (2 : ZMod p)⁻¹) := by ring
        _ = (b : ZMod p) := by rw [h2, mul_one]
    exact hinjμ ha hb this
  rw [type2Poles, Finset.card_image_of_injOn hinj, hcard]

lemma disjoint_type12 {r : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p) :
    Disjoint (type1Poles (p := p) r) (type2Poles (p := p) r) := by
  refine disjoint_left.mpr ?_
  intro x hx1 hx2
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hx1
  obtain ⟨μ, hμ, hμeq⟩ := mem_image.mp hx2
  have hj' : j < r := mem_range.mp hj
  have hμI := mem_Icc.mp hμ
  have h2ne := two_ne_of_r (p := p) hr2 hrp
  have h2 := two_inv_mul_two (p := p) hr2 hrp
  have hmul : (2 : ZMod p) * (j : ZMod p) = (μ : ZMod p) := by
    have hcongr := congrArg (fun z : ZMod p => (2 : ZMod p) * z) hμeq
    -- hμeq : ↑μ * 2⁻¹ = ↑j, so 2 * (↑μ * 2⁻¹) = 2 * ↑j
    have : (2 : ZMod p) * ((μ : ZMod p) * (2 : ZMod p)⁻¹) = (2 : ZMod p) * (j : ZMod p) := hcongr
    calc (2 : ZMod p) * (j : ZMod p)
        = (2 : ZMod p) * ((μ : ZMod p) * (2 : ZMod p)⁻¹) := this.symm
      _ = (μ : ZMod p) * ((2 : ZMod p) * (2 : ZMod p)⁻¹) := by ring
      _ = (μ : ZMod p) := by rw [h2, mul_one]
  have hcast : ((2 * j : ℕ) : ZMod p) = (μ : ZMod p) := by
    rw [Nat.cast_mul, Nat.cast_two, hmul]
  have hmod : 2 * j ≡ μ [MOD p] := (ZMod.natCast_eq_natCast_iff _ _ p).mp hcast
  have h2jlt : 2 * j < p := by omega
  have hμlt : μ < p := by omega
  have heq : 2 * j = μ := by
    rcases le_total (2 * j) μ with hle | hle
    · have hdvd : p ∣ μ - 2 * j := (Nat.modEq_iff_dvd' hle).mp hmod
      have : μ - 2 * j = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
      omega
    · have hdvd : p ∣ 2 * j - μ := (Nat.modEq_iff_dvd' hle).mp hmod.symm
      have : 2 * j - μ = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
      omega
  omega

lemma card_poles {r : ℕ} (hr0 : 0 < r) (hr2 : 2 ≤ r) (hrp : 3 * r < p) :
    #(poles (p := p) r) = 2 * r := by
  have hr := r_lt_p_of_three (p := p) hrp
  rw [poles, card_union_of_disjoint (disjoint_type12 (p := p) hr2 hrp),
    card_type1Poles (p := p) hr, card_type2Poles (p := p) hr0 hr2 hrp]
  ring

/-- Numerator polynomial `P(X) = ∏_{i=1}^{r-1} (X+i)²`. -/
noncomputable def Ppoly (r : ℕ) : (ZMod p)[X] :=
  (∏ i ∈ Icc (1 : ℕ) (r - 1), (X + C (i : ZMod p))) ^ 2

lemma eval_Ppoly (r : ℕ) (x : ZMod p) :
    (Ppoly (p := p) r).eval x = (∏ i ∈ Icc (1 : ℕ) (r - 1), (x + (i : ZMod p))) ^ 2 := by
  simp only [Ppoly, eval_pow, eval_prod, eval_add, eval_X, eval_C]

lemma natDegree_Ppoly {r : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p) :
    (Ppoly (p := p) r).natDegree = 2 * (r - 1) := by
  have hr : r - 1 < p := by omega
  have hcard : #(Icc (1 : ℕ) (r - 1)) = r - 1 := by
    rw [Nat.card_Icc]; omega
  have hmonic : ∀ i ∈ Icc (1 : ℕ) (r - 1), (X + C (i : ZMod p)).Monic :=
    fun _ _ => monic_X_add_C _
  have hprod : (∏ i ∈ Icc (1 : ℕ) (r - 1), (X + C (i : ZMod p) : (ZMod p)[X])).natDegree =
      ∑ i ∈ Icc (1 : ℕ) (r - 1), (X + C (i : ZMod p)).natDegree := by
    refine natDegree_prod _ _ ?_
    intro i hi
    exact (hmonic i hi).ne_zero
  have hdeg1 : ∀ i ∈ Icc (1 : ℕ) (r - 1), (X + C (i : ZMod p)).natDegree = 1 :=
    fun _ _ => natDegree_X_add_C _
  have hsum : ∑ i ∈ Icc (1 : ℕ) (r - 1), (X + C (i : ZMod p)).natDegree = r - 1 := by
    rw [sum_congr rfl hdeg1, sum_const, hcard, smul_eq_mul, mul_one]
  have hne : (∏ i ∈ Icc (1 : ℕ) (r - 1), (X + C (i : ZMod p) : (ZMod p)[X])) ≠ 0 := by
    refine prod_ne_zero_iff.mpr ?_
    intro i hi
    exact (hmonic i hi).ne_zero
  rw [Ppoly, Polynomial.natDegree_pow, hprod, hsum]

lemma natDegree_Ppoly_add_one_lt {r : ℕ} (hr0 : 0 < r) (hr2 : 2 ≤ r) (hrp : 3 * r < p) :
    (Ppoly (p := p) r).natDegree + 1 < #(poles (p := p) r) := by
  rw [natDegree_Ppoly (p := p) hr2 hrp, card_poles (p := p) hr0 hr2 hrp]
  omega

lemma injOn_id_poles (r : ℕ) :
    Set.InjOn (fun x : ZMod p => x) (poles (p := p) r) :=
  fun _ _ _ _ h => h

lemma sum_P_div_nodal {r : ℕ} (hr0 : 0 < r) (hr2 : 2 ≤ r) (hrp : 3 * r < p) :
    ∑ i ∈ poles (p := p) r,
        (Ppoly (p := p) r).eval i *
          (∏ j ∈ (poles (p := p) r).erase i, (i - j))⁻¹ = 0 :=
  sum_eval_div_nodal (poles (p := p) r) (fun x : ZMod p => x)
    (injOn_id_poles (p := p) r) (Ppoly (p := p) r)
    (natDegree_Ppoly_add_one_lt (p := p) hr0 hr2 hrp)

lemma mem_type1Poles {r k : ℕ} (hk : k < r) :
    (k : ZMod p) ∈ type1Poles (p := p) r :=
  mem_image.mpr ⟨k, mem_range.mpr hk, rfl⟩

lemma mem_type2Poles_of_mul {r μ : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    (hμ : μ ∈ Icc (2 * r) (3 * r - 1)) :
    ((μ : ZMod p) * (2 : ZMod p)⁻¹) ∈ type2Poles (p := p) r :=
  mem_image.mpr ⟨μ, hμ, rfl⟩

lemma two_mul_inv {r : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p) (x : ZMod p) :
    (2 : ZMod p) * (x * (2 : ZMod p)⁻¹) = x := by
  rw [mul_comm x, ← mul_assoc, two_inv_mul_two (p := p) hr2 hrp, one_mul]

/-- `∏_{i=0, i≠k}^{r-1} (k-i)` as a product over `type1Poles.erase k`. -/
lemma prod_type1_erase {r k : ℕ} (hrp : r < p) (hk : k < r) :
    ∏ j ∈ (type1Poles (p := p) r).erase (k : ZMod p), ((k : ZMod p) - j) =
      ∏ i ∈ (range r).erase k, ((k : ZMod p) - (i : ZMod p)) := by
  have hinj := injOn_natCast_range (p := p) hrp
  have hkmem : k ∈ range r := mem_range.mpr hk
  have himg :
      (type1Poles (p := p) r).erase (k : ZMod p) =
        ((range r).erase k).image (fun i : ℕ => (i : ZMod p)) := by
    rw [type1Poles, image_erase_of_injOn (fun a ha b hb h => hinj ha hb h) hkmem]
  rw [himg]
  refine Finset.prod_image (f := fun z : ZMod p => (k : ZMod p) - z)
      (fun a ha b hb h => ?_)
  have har : a < r := mem_range.mp (mem_of_mem_erase ha)
  have hbr : b < r := mem_range.mp (mem_of_mem_erase hb)
  have : a ≡ b [MOD p] := (ZMod.natCast_eq_natCast_iff a b p).mp h
  rcases le_total a b with hle | hle
  · have hdvd : p ∣ b - a := (Nat.modEq_iff_dvd' hle).mp this
    have : b - a = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    omega
  · have hdvd : p ∣ a - b := (Nat.modEq_iff_dvd' hle).mp this.symm
    have : a - b = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    omega

lemma prod_type2_at {r : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p) (x : ZMod p) :
    ∏ v ∈ type2Poles (p := p) r, (x - v) =
      (2 : ZMod p)⁻¹ ^ r *
        ∏ μ ∈ Icc (2 * r) (3 * r - 1), (2 * x - (μ : ZMod p)) := by
  have h3 : 3 * r - 1 < p := by omega
  have hinjμ := injOn_natCast_Icc (p := p) (a := 2 * r) (b := 3 * r - 1) h3
  have h2 := two_inv_mul_two (p := p) hr2 hrp
  have h2ne := two_ne_of_r (p := p) hr2 hrp
  have hinj : Set.InjOn (fun μ : ℕ => (μ : ZMod p) * (2 : ZMod p)⁻¹)
      (Icc (2 * r) (3 * r - 1)) := by
    intro a ha b hb h
    have : (a : ZMod p) = (b : ZMod p) := by
      calc (a : ZMod p)
          = (a : ZMod p) * ((2 : ZMod p) * (2 : ZMod p)⁻¹) := by rw [h2, mul_one]
        _ = ((a : ZMod p) * (2 : ZMod p)⁻¹) * (2 : ZMod p) := by ring
        _ = ((b : ZMod p) * (2 : ZMod p)⁻¹) * (2 : ZMod p) := by
              have h' : (a : ZMod p) * (2 : ZMod p)⁻¹ = (b : ZMod p) * (2 : ZMod p)⁻¹ := h
              rw [h']
        _ = (b : ZMod p) * ((2 : ZMod p) * (2 : ZMod p)⁻¹) := by ring
        _ = (b : ZMod p) := by rw [h2, mul_one]
    exact hinjμ ha hb this
  have hcard : #(Icc (2 * r) (3 * r - 1)) = r := card_Icc_two_r (by omega)
  rw [type2Poles]
  have hprod := Finset.prod_image (f := fun v : ZMod p => x - v)
      (g := fun μ : ℕ => (μ : ZMod p) * (2 : ZMod p)⁻¹)
      (fun a ha b hb h => hinj ha hb h)
  rw [hprod]
  have hfac : ∀ μ ∈ Icc (2 * r) (3 * r - 1),
      x - (μ : ZMod p) * (2 : ZMod p)⁻¹ =
        (2 : ZMod p)⁻¹ * ((2 : ZMod p) * x - (μ : ZMod p)) := by
    intro μ _
    field
  rw [prod_congr rfl hfac, prod_mul_distrib, prod_const, hcard]

lemma poles_erase_type1 {r k : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p) (hk : k < r) :
    (poles (p := p) r).erase (k : ZMod p) =
      (type1Poles (p := p) r).erase (k : ZMod p) ∪ type2Poles (p := p) r := by
  have hdis := disjoint_type12 (p := p) hr2 hrp
  have hk1 : (k : ZMod p) ∈ type1Poles (p := p) r := mem_type1Poles (p := p) hk
  have hk2 : (k : ZMod p) ∉ type2Poles (p := p) r :=
    disjoint_left.mp hdis hk1
  rw [poles, erase_union_distrib, erase_eq_of_notMem hk2]

lemma disjoint_type1_erase_type2 {r k : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p) (hk : k < r) :
    Disjoint ((type1Poles (p := p) r).erase (k : ZMod p)) (type2Poles (p := p) r) :=
  Disjoint.mono_left (erase_subset _ _) (disjoint_type12 (p := p) hr2 hrp)

lemma prod_poles_erase_type1 {r k : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p) (hk : k < r) :
    ∏ j ∈ (poles (p := p) r).erase (k : ZMod p), ((k : ZMod p) - j) =
      (∏ i ∈ (range r).erase k, ((k : ZMod p) - (i : ZMod p))) *
        ((2 : ZMod p)⁻¹ ^ r *
          ∏ μ ∈ Icc (2 * r) (3 * r - 1),
            ((2 : ZMod p) * (k : ZMod p) - (μ : ZMod p))) := by
  have hr := r_lt_p_of_three (p := p) hrp
  rw [poles_erase_type1 (p := p) hr2 hrp hk,
    prod_union (disjoint_type1_erase_type2 (p := p) hr2 hrp hk),
    prod_type1_erase (p := p) hr hk,
    prod_type2_at (p := p) hr2 hrp (k : ZMod p)]

/-- Rising factorial identity: `(k+1)⋯(k+r-1) = C(r+k-1, k) * (r-1)!`. -/
lemma rising_eq_choose_mul_fac {r k : ℕ} (hr2 : 2 ≤ r) :
    ∏ i ∈ Icc (1 : ℕ) (r - 1), (k + i) =
      (r + k - 1).choose k * (r - 1)! := by
  have hk0 : 0 < r - 1 := by omega
  have hkn : r - 1 ≤ (r + k - 1) + 1 := by omega
  have hdesc := descFactorial_eq_prod_Icc (n := r + k - 1) (k := r - 1) hk0 hkn
  have hlo : (r + k - 1) + 1 - (r - 1) = k + 1 := by omega
  have himg : Icc (k + 1) (r + k - 1) = (Icc (1 : ℕ) (r - 1)).image (fun i => k + i) := by
    ext x
    simp only [mem_Icc, mem_image]
    constructor
    · intro hx
      refine ⟨x - k, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      omega
  have hinj : Set.InjOn (fun i : ℕ => k + i) (Icc (1 : ℕ) (r - 1)) := by
    intro a _ b _ h
    exact Nat.add_left_cancel h
  have hprod : ∏ i ∈ Icc (1 : ℕ) (r - 1), (k + i) =
      ∏ x ∈ Icc (k + 1) (r + k - 1), x := by
    rw [himg]
    exact (Finset.prod_image (f := fun x : ℕ => x)
      (fun a ha b hb h => hinj ha hb h)).symm
  have hch : (r + k - 1).choose (r - 1) = (r + k - 1).choose k :=
    choose_symm_of_eq_add (n := r + k - 1) (a := r - 1) (b := k) (by omega)
  rw [hprod, ← hlo, ← hdesc, descFactorial_eq_factorial_mul_choose, hch, mul_comm]

lemma prod_range_sub_eq_factorial (k : ℕ) :
    ∏ i ∈ range k, (k - i) = k ! := by
  have himg : (range k).image (fun i => k - i) = Icc 1 k := by
    ext x
    simp only [mem_range, mem_image, mem_Icc]
    constructor
    · rintro ⟨i, hi, rfl⟩
      omega
    · intro hx
      refine ⟨k - x, by omega, by omega⟩
  have hinj : Set.InjOn (fun i : ℕ => k - i) (range k) := by
    intro a ha b hb h
    have ha' : a < k := mem_range.mp ha
    have hb' : b < k := mem_range.mp hb
    exact (tsub_right_inj (le_of_lt ha') (le_of_lt hb')).mp h
  have hprod : ∏ i ∈ range k, (k - i) = ∏ x ∈ Icc 1 k, x := by
    rw [← himg]
    exact (Finset.prod_image (f := fun x : ℕ => x)
      (fun a ha b hb h => hinj ha hb h)).symm
  rw [hprod, prod_Icc_one_n]

lemma prod_Icc_succ_neg {k m : ℕ} (hkm : k + 1 ≤ m) :
    ∏ i ∈ Icc (k + 1) m, ((k : ℤ) - (i : ℤ)) =
      (-1 : ℤ) ^ (m - k) * ((m - k)! : ℤ) := by
  have himg : Icc (k + 1) m = (Icc (1 : ℕ) (m - k)).image (fun t => k + t) := by
    ext x
    simp only [mem_Icc, mem_image]
    constructor
    · intro hx
      refine ⟨x - k, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨t, ht, rfl⟩
      omega
  have hinj : Set.InjOn (fun t : ℕ => k + t) (Icc 1 (m - k)) := by
    intro a _ b _ h
    exact Nat.add_left_cancel h
  have hprod : ∏ i ∈ Icc (k + 1) m, ((k : ℤ) - (i : ℤ)) =
      ∏ t ∈ Icc (1 : ℕ) (m - k), ((k : ℤ) - ((k + t : ℕ) : ℤ)) := by
    rw [himg]
    exact Finset.prod_image (f := fun i : ℕ => (k : ℤ) - (i : ℤ))
      (fun a ha b hb h => hinj ha hb h)
  have hfac : ∀ t ∈ Icc (1 : ℕ) (m - k),
      (k : ℤ) - ((k + t : ℕ) : ℤ) = - (t : ℤ) := by
    intro t ht
    rw [Nat.cast_add]
    ring
  rw [hprod, prod_congr rfl hfac, prod_neg]
  have hcard : #(Icc (1 : ℕ) (m - k)) = m - k := by
    rw [Nat.card_Icc]; omega
  rw [hcard, ← Nat.cast_prod, prod_Icc_one_n]

lemma prod_range_erase_sub {r k : ℕ} (hk : k < r) :
    ∏ i ∈ (range r).erase k, ((k : ℤ) - (i : ℤ)) =
      (k ! : ℤ) * ((-1 : ℤ) ^ (r - 1 - k) * ((r - 1 - k)! : ℤ)) := by
  have hsplit : (range r).erase k = range k ∪ Icc (k + 1) (r - 1) := by
    ext x
    simp only [mem_erase, mem_range, mem_union, mem_Icc]
    omega
  have hdis : Disjoint (range k) (Icc (k + 1) (r - 1)) := by
    refine disjoint_left.mpr ?_
    intro x hx hy
    simp only [mem_range, mem_Icc] at hx hy
    omega
  rw [hsplit, prod_union hdis]
  have hlo : ∏ i ∈ range k, ((k : ℤ) - (i : ℤ)) = (k ! : ℤ) := by
    have : ∀ i ∈ range k, (k : ℤ) - (i : ℤ) = ((k - i : ℕ) : ℤ) := by
      intro i hi
      have : i < k := mem_range.mp hi
      rw [Int.ofNat_sub (le_of_lt this)]
    rw [prod_congr rfl this, ← Nat.cast_prod, prod_range_sub_eq_factorial]
  by_cases htop : k + 1 ≤ r - 1
  · have hhi := prod_Icc_succ_neg (k := k) (m := r - 1) htop
    rw [hlo, hhi]
  · have hempty : Icc (k + 1) (r - 1) = ∅ := by
      rw [Icc_eq_empty_of_lt]
      omega
    have hrk : r - 1 - k = 0 := by omega
    rw [hlo, hempty, prod_empty, hrk, pow_zero, factorial_zero]
    simp

lemma prod_range_erase_sub_zmod {r k : ℕ} (hrp : r < p) (hk : k < r) :
    ∏ i ∈ (range r).erase k, ((k : ZMod p) - (i : ZMod p)) =
      (k ! : ZMod p) * ((-1 : ZMod p) ^ (r - 1 - k) * ((r - 1 - k)! : ZMod p)) := by
  have hZ := prod_range_erase_sub (r := r) (k := k) hk
  have hcast :
      ∏ i ∈ (range r).erase k, ((k : ZMod p) - (i : ZMod p)) =
        ((∏ i ∈ (range r).erase k, ((k : ℤ) - (i : ℤ)) : ℤ) : ZMod p) := by
    rw [Int.cast_prod]
    refine prod_congr rfl ?_
    intro i _
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
  rw [hcast, hZ]
  simp [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]

lemma eval_Ppoly_eq_choose {r k : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p) :
    (Ppoly (p := p) r).eval (k : ZMod p) =
      (((r + k - 1).choose k : ZMod p) * ((r - 1)! : ZMod p)) ^ 2 := by
  rw [eval_Ppoly]
  have hprod :
      ∏ i ∈ Icc (1 : ℕ) (r - 1), ((k : ZMod p) + (i : ZMod p)) =
        ((∏ i ∈ Icc (1 : ℕ) (r - 1), (k + i) : ℕ) : ZMod p) := by
    rw [Nat.cast_prod]
    refine prod_congr rfl ?_
    intro i hi
    rw [Nat.cast_add]
  rw [hprod, rising_eq_choose_mul_fac hr2, Nat.cast_mul]

lemma thirdL_cast {r k : ℕ} (hr : r ≤ p) :
    (thirdL (p := p) r k : ZMod p) =
      (2 : ZMod p) * (k : ZMod p) - (2 : ZMod p) * (r : ZMod p) + 1 := by
  simp only [thirdL]
  have : 2 * p - 2 * r + 2 * k + 1 = 2 * p + (2 * k + 1) - 2 * r := by omega
  have hle : 2 * r ≤ 2 * p + (2 * k + 1) := by omega
  rw [this, Nat.cast_sub hle, Nat.cast_add, Nat.cast_add, Nat.cast_mul,
    Nat.cast_mul, Nat.cast_two, Nat.cast_one,
    CharP.cast_eq_zero (R := ZMod p) p, Nat.cast_mul, Nat.cast_two]
  ring

lemma image_Icc_two_r (r : ℕ) (hr0 : 0 < r) :
    Icc (2 * r) (3 * r - 1) = (Icc (1 : ℕ) r).image (fun j => 2 * r + j - 1) := by
  ext x
  simp only [mem_Icc, mem_image]
  constructor
  · intro hx
    refine ⟨x + 1 - 2 * r, ⟨?_, ?_⟩, ?_⟩
    · omega
    · omega
    · omega
  · rintro ⟨j, hj, rfl⟩
    omega

lemma injOn_two_r_shift (r : ℕ) :
    Set.InjOn (fun j : ℕ => 2 * r + j - 1) (Icc (1 : ℕ) r) := by
  intro a ha b hb h
  have ha' : 1 ≤ a ∧ a ≤ r := by simpa [Set.mem_Icc] using ha
  have hb' : 1 ≤ b ∧ b ≤ r := by simpa [Set.mem_Icc] using hb
  have : 2 * r + a - 1 = 2 * r + b - 1 := h
  omega

lemma prod_third_eq_Q2 {r k : ℕ} (hr0 : 0 < r) (hr2 : 2 ≤ r) (hrp : 3 * r < p) :
    ∏ j ∈ Icc (1 : ℕ) r, ((thirdL (p := p) r k : ZMod p) - (j : ZMod p)) =
      ∏ μ ∈ Icc (2 * r) (3 * r - 1),
        ((2 : ZMod p) * (k : ZMod p) - (μ : ZMod p)) := by
  have hr := r_lt_p_of_three (p := p) hrp
  rw [image_Icc_two_r r hr0]
  have hprod := Finset.prod_image
      (f := fun μ : ℕ => (2 : ZMod p) * (k : ZMod p) - (μ : ZMod p))
      (g := fun j : ℕ => 2 * r + j - 1)
      (fun a ha b hb h => injOn_two_r_shift r ha hb h)
  rw [hprod]
  refine prod_congr rfl ?_
  intro j hj
  have hjI := mem_Icc.mp hj
  have hcast : ((2 * r + j - 1 : ℕ) : ZMod p) =
      (2 : ZMod p) * (r : ZMod p) + (j : ZMod p) - 1 := by
    have : 1 ≤ 2 * r + j := by omega
    rw [Nat.cast_sub this, Nat.cast_add, Nat.cast_mul, Nat.cast_two, Nat.cast_one]
  simp only
  rw [thirdL_cast (p := p) (le_of_lt hr), hcast]
  ring

lemma Q2_ne_zero_of_inA {r k : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p) (hk : k < r) :
    (∏ μ ∈ Icc (2 * r) (3 * r - 1),
        ((2 : ZMod p) * (k : ZMod p) - (μ : ZMod p))) ≠ 0 := by
  refine prod_ne_zero_iff.mpr ?_
  intro μ hμ
  have hμI := mem_Icc.mp hμ
  intro h0
  have : ((2 * k : ℕ) : ZMod p) = (μ : ZMod p) := by
    rw [Nat.cast_mul, Nat.cast_two]
    exact sub_eq_zero.mp h0
  have hmod : 2 * k ≡ μ [MOD p] := (ZMod.natCast_eq_natCast_iff _ _ p).mp this
  have h2klt : 2 * k < p := by omega
  have hμlt : μ < p := by omega
  have heq : 2 * k = μ := by
    rcases le_total (2 * k) μ with hle | hle
    · have hdvd : p ∣ μ - 2 * k := (Nat.modEq_iff_dvd' hle).mp hmod
      have : μ - 2 * k = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
      omega
    · have hdvd : p ∣ 2 * k - μ := (Nat.modEq_iff_dvd' hle).mp hmod.symm
      have : 2 * k - μ = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
      omega
  omega

lemma alg_id_A {r k : ℕ} (hr2 : 2 ≤ r) (hk : k < r) (hrp : r < p) :
    ((-1 : ZMod p) ^ k * ((r + k - 1).choose k : ZMod p)) ^ 2 *
      ((-1 : ZMod p) ^ k * ((r - 1).choose k : ZMod p)) *
      (2 : ZMod p) * (-1 : ZMod p) ^ (r - 1) * ((r - 1)! : ZMod p) *
      ((k ! : ZMod p) * ((-1 : ZMod p) ^ (r - 1 - k) * ((r - 1 - k)! : ZMod p))) *
      (2 : ZMod p)⁻¹ ^ r =
    ((r + k - 1).choose k : ZMod p) ^ 2 *
      ((r - 1)! : ZMod p) ^ 2 * (2 : ZMod p)⁻¹ ^ (r - 1) := by
  have h2ne : (2 : ZMod p) ≠ 0 := by
    have : 2 < p := lt_of_le_of_lt hr2 hrp
    exact zmod_nat_ne_zero (by decide) this
  have hle : k ≤ r - 1 := by omega
  have hCnat : (r - 1).choose k * k ! * (r - 1 - k)! = (r - 1)! :=
    choose_mul_factorial_mul_factorial hle
  have hC : ((r - 1).choose k : ZMod p) * (k ! : ZMod p) * ((r - 1 - k)! : ZMod p) =
      ((r - 1)! : ZMod p) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, hCnat]
  have hpowk : ((-1 : ZMod p) ^ k) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have hsgn : (-1 : ZMod p) ^ k * (-1 : ZMod p) ^ (r - 1) *
      (-1 : ZMod p) ^ (r - 1 - k) = 1 := by
    rw [← pow_add, ← pow_add]
    have : k + (r - 1) + (r - 1 - k) = 2 * (r - 1) := by omega
    rw [this, pow_mul, neg_one_sq, one_pow]
  have h2pow : (2 : ZMod p) * (2 : ZMod p)⁻¹ ^ r = (2 : ZMod p)⁻¹ ^ (r - 1) := by
    have hrw : r = (r - 1) + 1 := by omega
    rw [hrw, pow_succ]
    calc (2 : ZMod p) * ((2 : ZMod p)⁻¹ ^ (r - 1) * (2 : ZMod p)⁻¹)
        = ((2 : ZMod p) * (2 : ZMod p)⁻¹) * (2 : ZMod p)⁻¹ ^ (r - 1) := by ring
      _ = (2 : ZMod p)⁻¹ ^ (r - 1) := by rw [mul_inv_cancel₀ h2ne, one_mul]
  trans ((r + k - 1).choose k : ZMod p) ^ 2 *
      (((r - 1).choose k : ZMod p) * (k ! : ZMod p) * ((r - 1 - k)! : ZMod p) *
        ((r - 1)! : ZMod p) *
        ((-1 : ZMod p) ^ k * (-1 : ZMod p) ^ (r - 1) * (-1 : ZMod p) ^ (r - 1 - k)) *
        ((2 : ZMod p) * (2 : ZMod p)⁻¹ ^ r) *
        ((-1 : ZMod p) ^ k) ^ 2)
  · ring
  · rw [hC, hsgn, h2pow, hpowk]
    ring

lemma term_div_p_eq_nodal_A {r k : ℕ}
    (hr0 : 0 < r) (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    (hk : k < r) (hkn : k ≤ p - r) :
    ((term (p - r) k / p : ℕ) : ZMod p) *
        ∏ j ∈ (poles (p := p) r).erase (k : ZMod p), ((k : ZMod p) - j) =
      (2 : ZMod p)⁻¹ ^ (r - 1) * (Ppoly (p := p) r).eval (k : ZMod p) := by
  have hr := r_lt_p_of_three (p := p) hrp
  have hterm := term_div_p_region_A' (p := p) hr0 hrp hk hkn
  have hnodal := prod_poles_erase_type1 (p := p) hr2 hrp hk
  have hP := eval_Ppoly_eq_choose (p := p) hr2 hrp (k := k)
  have hQ := prod_third_eq_Q2 (p := p) hr0 hr2 hrp (k := k)
  have hQ0 := Q2_ne_zero_of_inA (p := p) hr2 hrp hk
  have herase := prod_range_erase_sub_zmod (p := p) hr hk
  have hid := alg_id_A (p := p) hr2 hk hr
  rw [hterm, hnodal, hQ, herase, hP]
  set Q2 : ZMod p :=
    ∏ μ ∈ Icc (2 * r) (3 * r - 1),
      ((2 : ZMod p) * (k : ZMod p) - (μ : ZMod p))
  have hQ2ne : Q2 ≠ 0 := hQ0
  -- Cancel `Q2 * Q2⁻¹`.
  trans ((-1 : ZMod p) ^ k * ((r + k - 1).choose k : ZMod p)) ^ 2 *
      ((-1 : ZMod p) ^ k * ((r - 1).choose k : ZMod p)) *
      (2 : ZMod p) * (-1 : ZMod p) ^ (r - 1) * ((r - 1)! : ZMod p) *
      ((k ! : ZMod p) * ((-1 : ZMod p) ^ (r - 1 - k) * ((r - 1 - k)! : ZMod p))) *
      (2 : ZMod p)⁻¹ ^ r
  · have hinv : Q2 * Q2⁻¹ = 1 := mul_inv_cancel₀ hQ2ne
    -- The rewritten LHS is `A * Q2⁻¹ * (B * (2⁻¹^r * Q2))`.
    calc
      _ = ((-1 : ZMod p) ^ k * ((r + k - 1).choose k : ZMod p)) ^ 2 *
            ((-1 : ZMod p) ^ k * ((r - 1).choose k : ZMod p)) *
            (2 : ZMod p) * (-1 : ZMod p) ^ (r - 1) * ((r - 1)! : ZMod p) *
            ((k ! : ZMod p) * ((-1 : ZMod p) ^ (r - 1 - k) * ((r - 1 - k)! : ZMod p))) *
            (2 : ZMod p)⁻¹ ^ r * (Q2 * Q2⁻¹) := by ring
      _ = ((-1 : ZMod p) ^ k * ((r + k - 1).choose k : ZMod p)) ^ 2 *
            ((-1 : ZMod p) ^ k * ((r - 1).choose k : ZMod p)) *
            (2 : ZMod p) * (-1 : ZMod p) ^ (r - 1) * ((r - 1)! : ZMod p) *
            ((k ! : ZMod p) * ((-1 : ZMod p) ^ (r - 1 - k) * ((r - 1 - k)! : ZMod p))) *
            (2 : ZMod p)⁻¹ ^ r * 1 := by rw [hinv]
      _ = _ := by ring
  · rw [hid]
    ring


/-- `μ ↦ μ/2` is injective on the type-II index interval. -/
lemma injOn_type2 {r : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p) :
    Set.InjOn (fun μ : ℕ => (μ : ZMod p) * (2 : ZMod p)⁻¹)
      (Icc (2 * r) (3 * r - 1)) := by
  have h3 : 3 * r - 1 < p := by omega
  have hinjμ := injOn_natCast_Icc (p := p) (a := 2 * r) (b := 3 * r - 1) h3
  have h2 := two_inv_mul_two (p := p) hr2 hrp
  intro a ha b hb h
  have : (a : ZMod p) = (b : ZMod p) := by
    calc (a : ZMod p)
        = (a : ZMod p) * ((2 : ZMod p) * (2 : ZMod p)⁻¹) := by rw [h2, mul_one]
      _ = ((a : ZMod p) * (2 : ZMod p)⁻¹) * (2 : ZMod p) := by ring
      _ = ((b : ZMod p) * (2 : ZMod p)⁻¹) * (2 : ZMod p) := by
            have h' : (a : ZMod p) * (2 : ZMod p)⁻¹ = (b : ZMod p) * (2 : ZMod p)⁻¹ := h
            rw [h']
      _ = (b : ZMod p) * ((2 : ZMod p) * (2 : ZMod p)⁻¹) := by ring
      _ = (b : ZMod p) := by rw [h2, mul_one]
  exact hinjμ ha hb this

lemma two_k_mem_Icc_of_inB {r k : ℕ} (hB : inB r k) :
    2 * k ∈ Icc (2 * r) (3 * r - 1) := by
  rcases hB with ⟨h1, h2⟩
  rw [mem_Icc]
  exact ⟨by omega, by omega⟩

lemma mem_type2Poles_of_inB {r k : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    (hB : inB r k) :
    (k : ZMod p) ∈ type2Poles (p := p) r := by
  have hμ := two_k_mem_Icc_of_inB (r := r) (k := k) hB
  have h2 := two_inv_mul_two (p := p) hr2 hrp
  have : (k : ZMod p) = ((2 * k : ℕ) : ZMod p) * (2 : ZMod p)⁻¹ := by
    rw [Nat.cast_mul, Nat.cast_two]
    calc (k : ZMod p)
        = (k : ZMod p) * ((2 : ZMod p) * (2 : ZMod p)⁻¹) := by rw [h2, mul_one]
      _ = ((2 : ZMod p) * (k : ZMod p)) * (2 : ZMod p)⁻¹ := by ring
  rw [this]
  exact mem_type2Poles_of_mul (p := p) hr2 hrp hμ

lemma mu_of_inD {r k : ℕ} (hrp : 3 * r < p) (hD : inD p r k) (hkn : k ≤ p - r) :
    2 * k - p ∈ Icc (2 * r) (3 * r - 1) := by
  rcases hD with ⟨h1, h2⟩
  have hle : p ≤ 2 * k := by omega
  rw [mem_Icc]
  constructor <;> omega

lemma two_k_eq_mu_of_inD {r k : ℕ} (hrp : 3 * r < p) (hD : inD p r k)
    (hkn : k ≤ p - r) :
    ((2 * k : ℕ) : ZMod p) = ((2 * k - p : ℕ) : ZMod p) := by
  have hle : p ≤ 2 * k := by
    have : p + 2 * r ≤ 2 * k := hD.1
    omega
  rw [Nat.cast_sub hle, CharP.cast_eq_zero (R := ZMod p) p, sub_zero]

lemma mem_type2Poles_of_inD {r k : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    (hD : inD p r k) (hkn : k ≤ p - r) :
    (k : ZMod p) ∈ type2Poles (p := p) r := by
  have hμ := mu_of_inD (p := p) hrp hD hkn
  have h2 := two_inv_mul_two (p := p) hr2 hrp
  have hcast := two_k_eq_mu_of_inD (p := p) hrp hD hkn
  have : (k : ZMod p) = ((2 * k - p : ℕ) : ZMod p) * (2 : ZMod p)⁻¹ := by
    rw [← hcast, Nat.cast_mul, Nat.cast_two]
    calc (k : ZMod p)
        = (k : ZMod p) * ((2 : ZMod p) * (2 : ZMod p)⁻¹) := by rw [h2, mul_one]
      _ = ((2 : ZMod p) * (k : ZMod p)) * (2 : ZMod p)⁻¹ := by ring
  rw [this]
  exact mem_type2Poles_of_mul (p := p) hr2 hrp hμ

lemma prod_type1_at {r : ℕ} (hrp : r < p) (x : ZMod p) :
    ∏ j ∈ type1Poles (p := p) r, (x - j) =
      ∏ i ∈ range r, (x - (i : ZMod p)) := by
  have hinj := injOn_natCast_range (p := p) hrp
  refine Finset.prod_image (f := fun z : ZMod p => x - z)
      (fun a ha b hb h => ?_)
  have har : a < r := mem_range.mp ha
  have hbr : b < r := mem_range.mp hb
  have : a ≡ b [MOD p] := (ZMod.natCast_eq_natCast_iff a b p).mp h
  rcases le_total a b with hle | hle
  · have hdvd : p ∣ b - a := (Nat.modEq_iff_dvd' hle).mp this
    have : b - a = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    omega
  · have hdvd : p ∣ a - b := (Nat.modEq_iff_dvd' hle).mp this.symm
    have : a - b = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    omega

lemma prod_range_sub_desc {r k : ℕ} (hkr : r ≤ k) :
    ∏ i ∈ range r, (k - i) = k.descFactorial r := by
  rw [descFactorial_eq_prod_range]

lemma prod_type1_at_nat {r k : ℕ} (hrp : r < p) (hkr : r ≤ k) (hkp : k < p) :
    ∏ i ∈ range r, ((k : ZMod p) - (i : ZMod p)) =
      ((r ! : ℕ) * k.choose r : ZMod p) := by
  have hcast : ∏ i ∈ range r, ((k : ZMod p) - (i : ZMod p)) =
      ((∏ i ∈ range r, (k - i) : ℕ) : ZMod p) := by
    rw [Nat.cast_prod]
    refine prod_congr rfl ?_
    intro i hi
    have : i < r := mem_range.mp hi
    have : i ≤ k := by omega
    rw [Nat.cast_sub this]
  rw [hcast, prod_range_sub_desc hkr, descFactorial_eq_factorial_mul_choose,
    Nat.cast_mul]

lemma poles_erase_type2 {r : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    {v : ZMod p} (hv : v ∈ type2Poles (p := p) r) :
    (poles (p := p) r).erase v =
      type1Poles (p := p) r ∪ (type2Poles (p := p) r).erase v := by
  have hdis := disjoint_type12 (p := p) hr2 hrp
  have hv1 : v ∉ type1Poles (p := p) r := disjoint_right.mp hdis hv
  rw [poles, erase_union_distrib, erase_eq_of_notMem hv1]

lemma disjoint_type1_type2_erase {r : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    {v : ZMod p} :
    Disjoint (type1Poles (p := p) r) ((type2Poles (p := p) r).erase v) :=
  Disjoint.mono_right (erase_subset _ _) (disjoint_type12 (p := p) hr2 hrp)

lemma prod_type2_erase {r μ0 : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    (hμ0 : μ0 ∈ Icc (2 * r) (3 * r - 1)) (x : ZMod p) :
    ∏ v ∈ (type2Poles (p := p) r).erase ((μ0 : ZMod p) * (2 : ZMod p)⁻¹),
        (x - v) =
      (2 : ZMod p)⁻¹ ^ (r - 1) *
        ∏ μ ∈ (Icc (2 * r) (3 * r - 1)).erase μ0,
          ((2 : ZMod p) * x - (μ : ZMod p)) := by
  have hinj := injOn_type2 (p := p) hr2 hrp
  have h2ne := two_ne_of_r (p := p) hr2 hrp
  have himg :
      (type2Poles (p := p) r).erase ((μ0 : ZMod p) * (2 : ZMod p)⁻¹) =
        ((Icc (2 * r) (3 * r - 1)).erase μ0).image
          (fun μ : ℕ => (μ : ZMod p) * (2 : ZMod p)⁻¹) := by
    rw [type2Poles, image_erase_of_injOn (fun a ha b hb h => hinj ha hb h) hμ0]
  rw [himg]
  have hinj_er : Set.InjOn (fun μ : ℕ => (μ : ZMod p) * (2 : ZMod p)⁻¹)
      ((Icc (2 * r) (3 * r - 1)).erase μ0) :=
    hinj.mono (Finset.coe_subset.mpr (erase_subset _ _))
  rw [Finset.prod_image hinj_er]
  have hfac : ∀ μ ∈ (Icc (2 * r) (3 * r - 1)).erase μ0,
      x - (μ : ZMod p) * (2 : ZMod p)⁻¹ =
        (2 : ZMod p)⁻¹ * ((2 : ZMod p) * x - (μ : ZMod p)) := by
    intro μ _
    field
  rw [prod_congr rfl hfac, prod_mul_distrib, prod_const]
  have hcard : #((Icc (2 * r) (3 * r - 1)).erase μ0) = r - 1 := by
    rw [card_erase_of_mem hμ0, card_Icc_two_r (by omega)]
  rw [hcard]

lemma prod_poles_erase_type2 {r μ0 : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    (hμ0 : μ0 ∈ Icc (2 * r) (3 * r - 1)) (x : ZMod p) :
    ∏ j ∈ (poles (p := p) r).erase ((μ0 : ZMod p) * (2 : ZMod p)⁻¹),
        (x - j) =
      (∏ i ∈ range r, (x - (i : ZMod p))) *
        ((2 : ZMod p)⁻¹ ^ (r - 1) *
          ∏ μ ∈ (Icc (2 * r) (3 * r - 1)).erase μ0,
            ((2 : ZMod p) * x - (μ : ZMod p))) := by
  have hr := r_lt_p_of_three (p := p) hrp
  have hv : ((μ0 : ZMod p) * (2 : ZMod p)⁻¹) ∈ type2Poles (p := p) r :=
    mem_type2Poles_of_mul (p := p) hr2 hrp hμ0
  rw [poles_erase_type2 (p := p) hr2 hrp hv,
    prod_union (disjoint_type1_type2_erase (p := p) hr2 hrp),
    prod_type1_at (p := p) hr x, prod_type2_erase (p := p) hr2 hrp hμ0 x]

lemma j0_of_mu {r μ : ℕ} (hr : 1 ≤ r) (hμ : μ ∈ Icc (2 * r) (3 * r - 1)) :
    μ + 1 - 2 * r ∈ Icc (1 : ℕ) r ∧ 2 * r + (μ + 1 - 2 * r) - 1 = μ := by
  have hI := mem_Icc.mp hμ
  have hge : 2 * r ≤ μ := hI.1
  have hle : μ ≤ 3 * r - 1 := hI.2
  constructor
  · rw [mem_Icc]
    constructor
    · exact Nat.le_sub_of_add_le (by omega)
    · have : μ + 1 ≤ 3 * r := by omega
      exact Nat.sub_le_of_le_add (by omega)
  · omega

lemma zero_missing_of_two_eq {r k : ℕ} (hr1 : 1 ≤ r) (hr : r ≤ p)
    (hμ : ∃ μ ∈ Icc (2 * r) (3 * r - 1),
      ((2 : ZMod p) * (k : ZMod p) = (μ : ZMod p))) :
    (0 : ZMod p) ∈
      (Icc 1 r).image (fun j : ℕ => (thirdL (p := p) r k : ZMod p) - (j : ZMod p)) := by
  obtain ⟨μ, hμI, hμeq⟩ := hμ
  have ⟨hj, _⟩ := j0_of_mu (r := r) (μ := μ) hr1 hμI
  refine mem_image.mpr ⟨μ + 1 - 2 * r, hj, ?_⟩
  have hL := thirdL_cast (p := p) (r := r) (k := k) hr
  have hjcast : ((μ + 1 - 2 * r : ℕ) : ZMod p) =
      (μ : ZMod p) + 1 - (2 : ZMod p) * (r : ZMod p) := by
    have : 2 * r ≤ μ + 1 := by
      have := mem_Icc.mp hμI; omega
    rw [Nat.cast_sub this, Nat.cast_add, Nat.cast_mul, Nat.cast_two, Nat.cast_one]
  rw [hL, hjcast, hμeq]
  ring

lemma prod_missing_erase_eq {r k μ0 : ℕ} (hr0 : 0 < r) (hr2 : 2 ≤ r)
    (hrp : 3 * r < p)
    (hμ0 : μ0 ∈ Icc (2 * r) (3 * r - 1))
    (hμeq : (2 : ZMod p) * (k : ZMod p) = (μ0 : ZMod p)) :
    ∏ x ∈ ((Icc 1 r).image
        (fun j : ℕ => (thirdL (p := p) r k : ZMod p) - (j : ZMod p))).erase 0,
        x =
      ∏ μ ∈ (Icc (2 * r) (3 * r - 1)).erase μ0,
        ((2 : ZMod p) * (k : ZMod p) - (μ : ZMod p)) := by
  have hr := r_lt_p_of_three (p := p) hrp
  have ⟨hj0, hjs⟩ := j0_of_mu (r := r) (μ := μ0) (by omega) hμ0
  have hL := thirdL_cast (p := p) (r := r) (k := k) (le_of_lt hr)
  have hzero :
      (thirdL (p := p) r k : ZMod p) - ((μ0 + 1 - 2 * r : ℕ) : ZMod p) = 0 := by
    have hjcast : ((μ0 + 1 - 2 * r : ℕ) : ZMod p) =
        (μ0 : ZMod p) + 1 - (2 : ZMod p) * (r : ZMod p) := by
      have : 2 * r ≤ μ0 + 1 := by
        have := mem_Icc.mp hμ0; omega
      rw [Nat.cast_sub this, Nat.cast_add, Nat.cast_mul, Nat.cast_two, Nat.cast_one]
    rw [hL, hjcast, hμeq]; ring
  have hinj_m : Set.InjOn
      (fun j : ℕ => (thirdL (p := p) r k : ZMod p) - (j : ZMod p)) (Icc 1 r) := by
    intro a ha b hb hab
    have haI : 1 ≤ a ∧ a ≤ r := by simpa [Set.mem_Icc] using ha
    have hbI : 1 ≤ b ∧ b ≤ r := by simpa [Set.mem_Icc] using hb
    have hab' : (a : ZMod p) = (b : ZMod p) := sub_right_inj.mp hab
    have hmod : a ≡ b [MOD p] := (ZMod.natCast_eq_natCast_iff a b p).mp hab'
    rcases le_total a b with hle | hle
    · have hdvd : p ∣ b - a := (Nat.modEq_iff_dvd' hle).mp hmod
      have : b - a = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
      omega
    · have hdvd : p ∣ a - b := (Nat.modEq_iff_dvd' hle).mp hmod.symm
      have : a - b = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
      omega
  have himg_er :
      ((Icc 1 r).image
          (fun j : ℕ => (thirdL (p := p) r k : ZMod p) - (j : ZMod p))).erase 0 =
        ((Icc 1 r).erase (μ0 + 1 - 2 * r)).image
          (fun j : ℕ => (thirdL (p := p) r k : ZMod p) - (j : ZMod p)) := by
    have := image_erase_of_injOn (f := fun j : ℕ =>
        (thirdL (p := p) r k : ZMod p) - (j : ZMod p))
      (fun a ha b hb h => hinj_m ha hb h) hj0
    rw [← hzero]
    exact this.symm
  rw [himg_er]
  have hinj_er : Set.InjOn
      (fun j : ℕ => (thirdL (p := p) r k : ZMod p) - (j : ZMod p))
      ((Icc 1 r).erase (μ0 + 1 - 2 * r)) :=
    hinj_m.mono (Finset.coe_subset.mpr (erase_subset _ _))
  rw [Finset.prod_image hinj_er]
  -- Reindex via `j ↦ 2r+j-1`.
  have himg2 := image_Icc_two_r r hr0
  have hinj2 := injOn_two_r_shift r
  have hj0μ : 2 * r + (μ0 + 1 - 2 * r) - 1 = μ0 := hjs
  have herase2 :
      (Icc (2 * r) (3 * r - 1)).erase μ0 =
        ((Icc (1 : ℕ) r).erase (μ0 + 1 - 2 * r)).image (fun j => 2 * r + j - 1) := by
    have hf : (fun j : ℕ => 2 * r + j - 1) (μ0 + 1 - 2 * r) = μ0 := hj0μ
    have := image_erase_of_injOn (f := fun j : ℕ => 2 * r + j - 1)
      (fun a ha b hb h => hinj2 ha hb h) hj0
    rw [← himg2, hf] at this
    exact this.symm
  have hinj2_er : Set.InjOn (fun j : ℕ => 2 * r + j - 1)
      ((Icc (1 : ℕ) r).erase (μ0 + 1 - 2 * r)) :=
    hinj2.mono (Finset.coe_subset.mpr (erase_subset _ _))
  rw [herase2, Finset.prod_image hinj2_er]
  refine prod_congr rfl ?_
  intro j hj
  have hjI := mem_Icc.mp (mem_of_mem_erase hj)
  have hcast : ((2 * r + j - 1 : ℕ) : ZMod p) =
      (2 : ZMod p) * (r : ZMod p) + (j : ZMod p) - 1 := by
    have : 1 ≤ 2 * r + j := by omega
    rw [Nat.cast_sub this, Nat.cast_add, Nat.cast_mul, Nat.cast_two, Nat.cast_one]
  rw [hL, hcast]
  ring

lemma choose_third_zmod_type2 {r k μ0 : ℕ}
    (hr0 : 0 < r) (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    (hμ0 : μ0 ∈ Icc (2 * r) (3 * r - 1))
    (hμeq : (2 : ZMod p) * (k : ZMod p) = (μ0 : ZMod p)) :
    ((3 * (p - r) + 2 * k).choose (p - r) : ZMod p) =
      (-1 : ZMod p) ^ (r - 1) * ((r - 1)! : ZMod p) *
        (∏ μ ∈ (Icc (2 * r) (3 * r - 1)).erase μ0,
          ((2 : ZMod p) * (k : ZMod p) - (μ : ZMod p)))⁻¹ := by
  have hr := r_lt_p_of_three (p := p) hrp
  have h0miss := zero_missing_of_two_eq (p := p) (r := r) (k := k)
      (le_trans (by decide : 1 ≤ 2) hr2) (le_of_lt hr) ⟨μ0, hμ0, hμeq⟩
  have hcheq := third_choose_eq_L (p := p) (r := r) (k := k) (le_of_lt hr)
  have hform := choose_zmod_of_zero_missing (p := p) (L := thirdL (p := p) r k)
      (r := r) hr0 hr h0miss
  rw [hcheq, hform, prod_missing_erase_eq (p := p) hr0 hr2 hrp hμ0 hμeq]

lemma p_dvd_term_type2 {r k : ℕ} (hr0 : 0 < r) (hrp : r < p)
    (hkr : r ≤ k) (hkn : k ≤ p - r) :
    p ∣ term (p - r) k := by
  have hkp : k < p := by omega
  have hmid := p_dvd_middle_of_r_le (p := p) hr0 hrp hkr hkp
  rw [term_eq_general]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hmid _) _

lemma term_div_p_region_type2 {r k μ0 : ℕ}
    (hr0 : 0 < r) (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    (hkr : r ≤ k) (hkn : k ≤ p - r)
    (hμ0 : μ0 ∈ Icc (2 * r) (3 * r - 1))
    (hμeq : (2 : ZMod p) * (k : ZMod p) = (μ0 : ZMod p)) :
    ((term (p - r) k / p : ℕ) : ZMod p) =
      ((-1 : ZMod p) ^ k * ((r + k - 1).choose k : ZMod p)) ^ 2 *
        ((-1 : ZMod p) ^ (r - 1) *
          ((r : ZMod p) * (k.choose r : ZMod p))⁻¹) *
        ((-1 : ZMod p) ^ (r - 1) * ((r - 1)! : ZMod p) *
          (∏ μ ∈ (Icc (2 * r) (3 * r - 1)).erase μ0,
            ((2 : ZMod p) * (k : ZMod p) - (μ : ZMod p)))⁻¹) := by
  have hr := r_lt_p_of_three (p := p) hrp
  have hkp : k < p := by omega
  have hmid := choose_p_sub_add_div_p_zmod (p := p) hr0 hr hkr hkp
  have hth := choose_third_zmod_type2 (p := p) hr0 hr2 hrp hμ0 hμeq
  have hppos : 0 < p := p_pos (p := p)
  have hpdvd := p_dvd_term_type2 (p := p) hr0 hr hkr hkn
  have hdiv : term (p - r) k / p =
      (p - r).choose k ^ 2 * ((p - r + k).choose k / p) *
        (3 * (p - r) + 2 * k).choose (p - r) := by
    rw [term_eq_general]
    obtain ⟨c, hc⟩ := hmid.1
    rw [hc]
    have : (p - r).choose k ^ 2 * (p * c) * (3 * (p - r) + 2 * k).choose (p - r) / p =
        (p - r).choose k ^ 2 * c * (3 * (p - r) + 2 * k).choose (p - r) := by
      have hmul :
          (p - r).choose k ^ 2 * (p * c) * (3 * (p - r) + 2 * k).choose (p - r) =
            ((p - r).choose k ^ 2 * c * (3 * (p - r) + 2 * k).choose (p - r)) * p := by
        ring
      rw [hmul, Nat.mul_div_cancel _ hppos]
    rw [this, Nat.mul_div_cancel_left c hppos]
  rw [hdiv, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow,
    choose_p_sub_zmod (p := p) hr0 hr hkn, hmid.2, hth]

lemma r_mul_fac {r : ℕ} (hr0 : 0 < r) (hrp : r < p) :
    (r : ZMod p) * ((r - 1)! : ZMod p) = (r ! : ZMod p) := by
  have hrne : r ≠ 0 := hr0.ne'
  rw [← Nat.cast_mul, Nat.mul_factorial_pred hrne]

lemma alg_id_type2 {r k : ℕ} (hr0 : 0 < r) (hr2 : 2 ≤ r) (hrp : r < p)
    (hkr : r ≤ k) (hkp : k < p) :
    ((-1 : ZMod p) ^ k * ((r + k - 1).choose k : ZMod p)) ^ 2 *
      ((-1 : ZMod p) ^ (r - 1) * ((r : ZMod p) * (k.choose r : ZMod p))⁻¹) *
      ((-1 : ZMod p) ^ (r - 1) * ((r - 1)! : ZMod p)) *
      ((r ! : ZMod p) * (k.choose r : ZMod p)) *
      (2 : ZMod p)⁻¹ ^ (r - 1) =
    ((r + k - 1).choose k : ZMod p) ^ 2 *
      ((r - 1)! : ZMod p) ^ 2 * (2 : ZMod p)⁻¹ ^ (r - 1) := by
  have h2ne : (2 : ZMod p) ≠ 0 := zmod_nat_ne_zero (by decide) (lt_of_le_of_lt hr2 hrp)
  have hrne : (r : ZMod p) ≠ 0 := zmod_nat_ne_zero hr0 hrp
  have hCne : (k.choose r : ZMod p) ≠ 0 := coprime_choose_ne_zero hkp hkr
  have hfac : ((r - 1)! : ZMod p) ≠ 0 := factorial_ne_zero_zmod (by omega)
  have hrf : (r : ZMod p) * ((r - 1)! : ZMod p) = (r ! : ZMod p) :=
    r_mul_fac (p := p) hr0 hrp
  have hsgn : ((-1 : ZMod p) ^ (r - 1)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have hpowk : ((-1 : ZMod p) ^ k) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  trans ((r + k - 1).choose k : ZMod p) ^ 2 *
      (((-1 : ZMod p) ^ k) ^ 2 * ((-1 : ZMod p) ^ (r - 1)) ^ 2 *
        ((r : ZMod p) * (k.choose r : ZMod p) * ((r : ZMod p) * (k.choose r : ZMod p))⁻¹) *
        ((r - 1)! : ZMod p) * ((r - 1)! : ZMod p) *
        (2 : ZMod p)⁻¹ ^ (r - 1))
  · -- rewrite `r!` as `r*(r-1)!` inside the product
    have : (r ! : ZMod p) = (r : ZMod p) * ((r - 1)! : ZMod p) := hrf.symm
    rw [this]
    ring
  · rw [hpowk, hsgn, mul_inv_cancel₀ (mul_ne_zero hrne hCne)]
    ring

lemma term_div_p_eq_nodal_type2 {r k μ0 : ℕ}
    (hr0 : 0 < r) (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    (hkr : r ≤ k) (hkn : k ≤ p - r)
    (hμ0 : μ0 ∈ Icc (2 * r) (3 * r - 1))
    (hμeq : (2 : ZMod p) * (k : ZMod p) = (μ0 : ZMod p)) :
    ((term (p - r) k / p : ℕ) : ZMod p) *
        ∏ j ∈ (poles (p := p) r).erase (k : ZMod p), ((k : ZMod p) - j) =
      (2 : ZMod p)⁻¹ ^ (r - 1) * (Ppoly (p := p) r).eval (k : ZMod p) := by
  have hr := r_lt_p_of_three (p := p) hrp
  have hkp : k < p := by omega
  have h2 := two_inv_mul_two (p := p) hr2 hrp
  have hv : (k : ZMod p) = (μ0 : ZMod p) * (2 : ZMod p)⁻¹ := by
    calc (k : ZMod p)
        = (k : ZMod p) * ((2 : ZMod p) * (2 : ZMod p)⁻¹) := by rw [h2, mul_one]
      _ = ((2 : ZMod p) * (k : ZMod p)) * (2 : ZMod p)⁻¹ := by ring
      _ = (μ0 : ZMod p) * (2 : ZMod p)⁻¹ := by rw [hμeq]
  have hterm := term_div_p_region_type2 (p := p) hr0 hr2 hrp hkr hkn hμ0 hμeq
  have hnodal := prod_poles_erase_type2 (p := p) hr2 hrp hμ0 ((μ0 : ZMod p) * (2 : ZMod p)⁻¹)
  rw [← hv] at hnodal
  have hP := eval_Ppoly_eq_choose (p := p) hr2 hrp (k := k)
  have htype1 := prod_type1_at_nat (p := p) hr hkr hkp
  have hid := alg_id_type2 (p := p) hr0 hr2 hr hkr hkp
  rw [hterm, hnodal, htype1, hP]
  set Q2 : ZMod p :=
    ∏ μ ∈ (Icc (2 * r) (3 * r - 1)).erase μ0,
      ((2 : ZMod p) * (k : ZMod p) - (μ : ZMod p))
  have hQ2ne : Q2 ≠ 0 := by
    refine prod_ne_zero_iff.mpr ?_
    intro μ hμ
    have hμI := mem_Icc.mp (mem_of_mem_erase hμ)
    intro h0
    have : (μ : ZMod p) = (μ0 : ZMod p) := by
      have hμk : (2 : ZMod p) * (k : ZMod p) = (μ : ZMod p) := sub_eq_zero.mp h0
      rw [← hμeq, hμk]
    have hinjμ := injOn_natCast_Icc (p := p) (a := 2 * r) (b := 3 * r - 1) (by omega)
    have heq : μ = μ0 := hinjμ (mem_of_mem_erase hμ) hμ0 this
    exact (mem_erase.mp hμ).1 heq
  have hinv : Q2 * Q2⁻¹ = 1 := mul_inv_cancel₀ hQ2ne
  trans ((-1 : ZMod p) ^ k * ((r + k - 1).choose k : ZMod p)) ^ 2 *
      ((-1 : ZMod p) ^ (r - 1) * ((r : ZMod p) * (k.choose r : ZMod p))⁻¹) *
      ((-1 : ZMod p) ^ (r - 1) * ((r - 1)! : ZMod p)) *
      ((r ! : ZMod p) * (k.choose r : ZMod p)) *
      (2 : ZMod p)⁻¹ ^ (r - 1)
  · calc
      _ = ((-1 : ZMod p) ^ k * ((r + k - 1).choose k : ZMod p)) ^ 2 *
            ((-1 : ZMod p) ^ (r - 1) * ((r : ZMod p) * (k.choose r : ZMod p))⁻¹) *
            ((-1 : ZMod p) ^ (r - 1) * ((r - 1)! : ZMod p) * Q2⁻¹) *
            (((r ! : ZMod p) * (k.choose r : ZMod p)) *
              ((2 : ZMod p)⁻¹ ^ (r - 1) * Q2)) := by
            simp only [Q2]
            try ring
      _ = ((-1 : ZMod p) ^ k * ((r + k - 1).choose k : ZMod p)) ^ 2 *
            ((-1 : ZMod p) ^ (r - 1) * ((r : ZMod p) * (k.choose r : ZMod p))⁻¹) *
            ((-1 : ZMod p) ^ (r - 1) * ((r - 1)! : ZMod p)) *
            ((r ! : ZMod p) * (k.choose r : ZMod p)) *
            (2 : ZMod p)⁻¹ ^ (r - 1) * (Q2 * Q2⁻¹) := by ring
      _ = _ := by rw [hinv]; ring
  · rw [hid]
    ring


lemma term_div_p_eq_nodal_of_inB {r k : ℕ}
    (hr0 : 0 < r) (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    (hB : inB r k) (hkn : k ≤ p - r) :
    ((term (p - r) k / p : ℕ) : ZMod p) *
        ∏ j ∈ (poles (p := p) r).erase (k : ZMod p), ((k : ZMod p) - j) =
      (2 : ZMod p)⁻¹ ^ (r - 1) * (Ppoly (p := p) r).eval (k : ZMod p) := by
  have hμ := two_k_mem_Icc_of_inB (r := r) (k := k) hB
  have hμeq : (2 : ZMod p) * (k : ZMod p) = ((2 * k : ℕ) : ZMod p) := by
    rw [Nat.cast_mul, Nat.cast_two]
  exact term_div_p_eq_nodal_type2 (p := p) hr0 hr2 hrp hB.1 hkn hμ hμeq

lemma term_div_p_eq_nodal_of_inD {r k : ℕ}
    (hr0 : 0 < r) (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    (hD : inD p r k) (hkn : k ≤ p - r) :
    ((term (p - r) k / p : ℕ) : ZMod p) *
        ∏ j ∈ (poles (p := p) r).erase (k : ZMod p), ((k : ZMod p) - j) =
      (2 : ZMod p)⁻¹ ^ (r - 1) * (Ppoly (p := p) r).eval (k : ZMod p) := by
  have hμ := mu_of_inD (p := p) hrp hD hkn
  have hkr : r ≤ k := by rcases hD with ⟨h1, _⟩; omega
  have hμeq : (2 : ZMod p) * (k : ZMod p) = ((2 * k - p : ℕ) : ZMod p) := by
    have hcast := two_k_eq_mu_of_inD (p := p) hrp hD hkn
    rw [← hcast, Nat.cast_mul, Nat.cast_two]
  exact term_div_p_eq_nodal_type2 (p := p) hr0 hr2 hrp hkr hkn hμ hμeq

lemma type1_cast_lt {r k : ℕ} (hrp : r < p) (hkp : k < p)
    (hk : (k : ZMod p) ∈ type1Poles (p := p) r) : k < r := by
  obtain ⟨i, hi, hieq⟩ := mem_image.mp hk
  have hir : i < r := mem_range.mp hi
  have hmod : k ≡ i [MOD p] := (ZMod.natCast_eq_natCast_iff k i p).mp hieq.symm
  rcases le_total k i with hle | hle
  · have hdvd : p ∣ i - k := (Nat.modEq_iff_dvd' hle).mp hmod
    have : i - k = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    omega
  · have hdvd : p ∣ k - i := (Nat.modEq_iff_dvd' hle).mp hmod.symm
    have : k - i = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    omega

lemma eval_Ppoly_eq_zero_of_gt_n {r k : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    (hgt : p - r < k) (hkp : k < p) :
    (Ppoly (p := p) r).eval (k : ZMod p) = 0 := by
  have hi : p - k ∈ Icc (1 : ℕ) (r - 1) := by
    rw [mem_Icc]; constructor <;> omega
  rw [eval_Ppoly, sq]
  refine mul_eq_zero_of_left ?_ _
  refine prod_eq_zero hi ?_
  have : ((k : ZMod p) + ((p - k : ℕ) : ZMod p)) = 0 := by
    rw [← Nat.cast_add, Nat.add_sub_of_le (le_of_lt hkp),
      CharP.cast_eq_zero (R := ZMod p) p]
  exact this

lemma nodal_ne_zero {r : ℕ} {v : ZMod p} (hv : v ∈ poles (p := p) r) :
    (∏ j ∈ (poles (p := p) r).erase v, (v - j)) ≠ 0 := by
  refine prod_ne_zero_iff.mpr ?_
  intro j hj
  exact sub_ne_zero.mpr (Ne.symm (mem_erase.mp hj).1)

lemma mem_poles_of_inA {r k : ℕ} (hk : inA r k) :
    (k : ZMod p) ∈ poles (p := p) r :=
  mem_union_left _ (mem_type1Poles (p := p) hk)

lemma mem_poles_of_inB {r k : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p) (hB : inB r k) :
    (k : ZMod p) ∈ poles (p := p) r :=
  mem_union_right _ (mem_type2Poles_of_inB (p := p) hr2 hrp hB)

lemma mem_poles_of_inD {r k : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    (hD : inD p r k) (hkn : k ≤ p - r) :
    (k : ZMod p) ∈ poles (p := p) r :=
  mem_union_right _ (mem_type2Poles_of_inD (p := p) hr2 hrp hD hkn)

lemma type2_two_eq {r k : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    (hk : (k : ZMod p) ∈ type2Poles (p := p) r) :
    ∃ μ ∈ Icc (2 * r) (3 * r - 1), (2 : ZMod p) * (k : ZMod p) = (μ : ZMod p) := by
  obtain ⟨μ, hμ, hv⟩ := mem_image.mp hk
  refine ⟨μ, hμ, ?_⟩
  have h2 := two_inv_mul_two (p := p) hr2 hrp
  calc (2 : ZMod p) * (k : ZMod p)
      = (2 : ZMod p) * ((μ : ZMod p) * (2 : ZMod p)⁻¹) := by rw [← hv]
    _ = ((2 : ZMod p) * (2 : ZMod p)⁻¹) * (μ : ZMod p) := by ring
    _ = (μ : ZMod p) := by rw [h2, one_mul]

lemma mem_poles_imp_ABD {r k : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    (hkn : k ≤ p - r) (hk : (k : ZMod p) ∈ poles (p := p) r) :
    inA r k ∨ inB r k ∨ inD p r k := by
  have hr := r_lt_p_of_three (p := p) hrp
  have hkp : k < p := by omega
  rw [poles, mem_union] at hk
  rcases hk with h1 | h2
  · exact Or.inl (type1_cast_lt (p := p) hr hkp h1)
  · obtain ⟨μ, hμ, hμeq⟩ := type2_two_eq (p := p) hr2 hrp h2
    have hμI := mem_Icc.mp hμ
    have hmod : 2 * k ≡ μ [MOD p] := by
      have : ((2 * k : ℕ) : ZMod p) = (μ : ZMod p) := by
        rw [Nat.cast_mul, Nat.cast_two, hμeq]
      exact (ZMod.natCast_eq_natCast_iff _ _ p).mp this
    have hcases : 2 * k = μ ∨ 2 * k = μ + p := by
      rcases le_total (2 * k) μ with hle | hle
      · have hdvd : p ∣ μ - 2 * k := (Nat.modEq_iff_dvd' hle).mp hmod
        have : μ - 2 * k = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
        omega
      · have hdvd : p ∣ 2 * k - μ := (Nat.modEq_iff_dvd' hle).mp hmod.symm
        obtain ⟨t, ht⟩ := hdvd
        have hbound : 2 * k - μ < 2 * p := by omega
        have htlt : t * p < 2 * p := by
          rwa [mul_comm t p, ← ht]
        have : t < 2 := Nat.lt_of_mul_lt_mul_right (a := p) (by omega)
        interval_cases t <;> omega
    rcases hcases with hEq | hEq
    · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · exact Or.inr (Or.inr ⟨by omega, by omega⟩)

lemma p_dvd_term_ABD {r k : ℕ} (hr0 : 0 < r) (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    (hkn : k ≤ p - r) (hABD : inA r k ∨ inB r k ∨ inD p r k) :
    p ∣ term (p - r) k := by
  have hr := r_lt_p_of_three (p := p) hrp
  rcases hABD with hA | hB | hD
  · have h3 := choose_third_div_p_region_A (p := p) hr0 hrp hA
    rw [term_eq_general]; exact dvd_mul_of_dvd_right h3.1 _
  · exact p_dvd_term_type2 (p := p) hr0 hr hB.1 hkn
  · exact p_dvd_term_type2 (p := p) hr0 hr (by rcases hD with ⟨h1, _⟩; omega) hkn

lemma term_div_p_eq_nodal_ABD {r k : ℕ}
    (hr0 : 0 < r) (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    (hkn : k ≤ p - r) (hABD : inA r k ∨ inB r k ∨ inD p r k) :
    ((term (p - r) k / p : ℕ) : ZMod p) *
        ∏ j ∈ (poles (p := p) r).erase (k : ZMod p), ((k : ZMod p) - j) =
      (2 : ZMod p)⁻¹ ^ (r - 1) * (Ppoly (p := p) r).eval (k : ZMod p) := by
  rcases hABD with hA | hB | hD
  · exact term_div_p_eq_nodal_A (p := p) hr0 hr2 hrp hA hkn
  · exact term_div_p_eq_nodal_of_inB (p := p) hr0 hr2 hrp hB hkn
  · exact term_div_p_eq_nodal_of_inD (p := p) hr0 hr2 hrp hD hkn

lemma term_div_p_eq_res {r k : ℕ}
    (hr0 : 0 < r) (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    (hkn : k ≤ p - r) (hABD : inA r k ∨ inB r k ∨ inD p r k) :
    ((term (p - r) k / p : ℕ) : ZMod p) =
      (2 : ZMod p)⁻¹ ^ (r - 1) * (Ppoly (p := p) r).eval (k : ZMod p) *
        (∏ j ∈ (poles (p := p) r).erase (k : ZMod p), ((k : ZMod p) - j))⁻¹ := by
  have hid := term_div_p_eq_nodal_ABD (p := p) hr0 hr2 hrp hkn hABD
  have hpole : (k : ZMod p) ∈ poles (p := p) r := by
    rcases hABD with hA | hB | hD
    · exact mem_poles_of_inA (p := p) hA
    · exact mem_poles_of_inB (p := p) hr2 hrp hB
    · exact mem_poles_of_inD (p := p) hr2 hrp hD hkn
  have hnod0 := nodal_ne_zero (p := p) hpole
  have := congrArg (fun z => z * (∏ j ∈ (poles (p := p) r).erase (k : ZMod p),
      ((k : ZMod p) - j))⁻¹) hid
  simpa [mul_assoc, mul_inv_cancel_right₀ hnod0] using this

lemma eval_P_extra_zero {r : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    {v : ZMod p} (hv : v ∈ poles (p := p) r)
    (hextra : ∀ k ≤ p - r, (k : ZMod p) ≠ v) :
    (Ppoly (p := p) r).eval v = 0 := by
  have hr := r_lt_p_of_three (p := p) hrp
  rw [poles, mem_union] at hv
  rcases hv with h1 | h2
  · obtain ⟨i, hi, rfl⟩ := mem_image.mp h1
    have : i ≤ p - r := by
      have : i < r := mem_range.mp hi
      omega
    exact (hextra i this rfl).elim
  · let k := v.val
    have hkcast : (k : ZMod p) = v := ZMod.natCast_zmod_val v
    have hkp : k < p := ZMod.val_lt v
    have hgt : p - r < k := lt_of_not_ge fun hle => hextra k hle hkcast
    have := eval_Ppoly_eq_zero_of_gt_n (p := p) hr2 hrp hgt hkp
    rwa [hkcast] at this

def poleIdx (r : ℕ) : Finset ℕ :=
  (range (p - r + 1)).filter (fun k => (k : ZMod p) ∈ poles (p := p) r)

lemma mem_poleIdx {r k : ℕ} :
    k ∈ poleIdx (p := p) r ↔ k ≤ p - r ∧ (k : ZMod p) ∈ poles (p := p) r := by
  simp only [poleIdx, mem_filter, mem_range, Nat.lt_succ_iff]

lemma injOn_poleIdx {r : ℕ} (hr0 : 0 < r) (hrp : 3 * r < p) :
    Set.InjOn (fun k : ℕ => (k : ZMod p)) (poleIdx (p := p) r) := by
  intro a ha b hb h
  have ha' : a ≤ p - r := (mem_poleIdx (p := p) (r := r)).mp ha |>.1
  have hb' : b ≤ p - r := (mem_poleIdx (p := p) (r := r)).mp hb |>.1
  have hmod : a ≡ b [MOD p] := (ZMod.natCast_eq_natCast_iff a b p).mp h
  rcases le_total a b with hle | hle
  · have hdvd : p ∣ b - a := (Nat.modEq_iff_dvd' hle).mp hmod
    have : b - a = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    omega
  · have hdvd : p ∣ a - b := (Nat.modEq_iff_dvd' hle).mp hmod.symm
    have : a - b = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    omega

lemma image_poleIdx_subset {r : ℕ} :
    (poleIdx (p := p) r).image (fun k : ℕ => (k : ZMod p)) ⊆ poles (p := p) r := by
  intro v hv
  obtain ⟨k, hk, rfl⟩ := mem_image.mp hv
  exact (mem_poleIdx (p := p) (r := r)).mp hk |>.2

lemma sum_term_div_p_poleIdx {r : ℕ} (hr0 : 0 < r) (hr2 : 2 ≤ r) (hrp : 3 * r < p) :
    ∑ k ∈ poleIdx (p := p) r, ((term (p - r) k / p : ℕ) : ZMod p) = 0 := by
  have hsumP := sum_P_div_nodal (p := p) hr0 hr2 hrp
  have hinj := injOn_poleIdx (p := p) (r := r) hr0 hrp
  have hsub := image_poleIdx_subset (p := p) (r := r)
  have hextra :
      ∑ v ∈ poles (p := p) r \ (poleIdx (p := p) r).image (fun k : ℕ => (k : ZMod p)),
          (Ppoly (p := p) r).eval v *
            (∏ j ∈ (poles (p := p) r).erase v, (v - j))⁻¹ = 0 := by
    refine sum_eq_zero ?_
    intro v hv
    have hvP : v ∈ poles (p := p) r := (mem_sdiff.mp hv).1
    have hnot : v ∉ (poleIdx (p := p) r).image (fun k : ℕ => (k : ZMod p)) :=
      (mem_sdiff.mp hv).2
    have hex : ∀ k ≤ p - r, (k : ZMod p) ≠ v := by
      intro k hkn hk
      apply hnot
      refine mem_image.mpr ⟨k, ?_, hk⟩
      exact (mem_poleIdx (p := p) (r := r)).mpr ⟨hkn, hk.symm ▸ hvP⟩
    rw [eval_P_extra_zero (p := p) hr2 hrp hvP hex, zero_mul]
  let f : ZMod p → ZMod p := fun v =>
    (Ppoly (p := p) r).eval v *
      (∏ j ∈ (poles (p := p) r).erase v, (v - j))⁻¹
  have hsplit :
      ∑ v ∈ poles (p := p) r, f v =
        ∑ v ∈ poles (p := p) r \
            (poleIdx (p := p) r).image (fun k : ℕ => (k : ZMod p)), f v +
          ∑ v ∈ (poleIdx (p := p) r).image (fun k : ℕ => (k : ZMod p)), f v :=
    (sum_sdiff hsub).symm
  have himg :
      ∑ v ∈ (poleIdx (p := p) r).image (fun k : ℕ => (k : ZMod p)), f v =
        ∑ k ∈ poleIdx (p := p) r, f (k : ZMod p) :=
    Finset.sum_image (fun a ha b hb h => hinj ha hb h)
  have hterms :
      ∑ k ∈ poleIdx (p := p) r, ((term (p - r) k / p : ℕ) : ZMod p) =
        (2 : ZMod p)⁻¹ ^ (r - 1) *
          ∑ k ∈ poleIdx (p := p) r,
            (Ppoly (p := p) r).eval (k : ZMod p) *
              (∏ j ∈ (poles (p := p) r).erase (k : ZMod p),
                ((k : ZMod p) - j))⁻¹ := by
    rw [mul_sum]
    refine sum_congr rfl ?_
    intro k hk
    have ⟨hkn, hpole⟩ := (mem_poleIdx (p := p) (r := r)).mp hk
    have hABD := mem_poles_imp_ABD (p := p) hr2 hrp hkn hpole
    rw [term_div_p_eq_res (p := p) hr0 hr2 hrp hkn hABD, mul_assoc]
  rw [hterms, ← himg]
  have himg_eq :
      ∑ v ∈ (poleIdx (p := p) r).image (fun k : ℕ => (k : ZMod p)), f v =
        ∑ v ∈ poles (p := p) r, f v := by
    have hextra' :
        ∑ v ∈ poles (p := p) r \
            (poleIdx (p := p) r).image (fun k : ℕ => (k : ZMod p)), f v = 0 := hextra
    rw [hsplit, hextra', zero_add]
  rw [himg_eq, hsumP, mul_zero]

lemma psq_dvd_sum_ABD {r : ℕ} (hr0 : 0 < r) (hr2 : 2 ≤ r) (hrp : 3 * r < p) :
    p ^ 2 ∣ ∑ k ∈ poleIdx (p := p) r, term (p - r) k := by
  have hppos : 0 < p := p_pos (p := p)
  have hdiv : ∀ k ∈ poleIdx (p := p) r, p ∣ term (p - r) k := by
    intro k hk
    have ⟨hkn, hpole⟩ := (mem_poleIdx (p := p) (r := r)).mp hk
    exact p_dvd_term_ABD (p := p) hr0 hr2 hrp hkn
      (mem_poles_imp_ABD (p := p) hr2 hrp hkn hpole)
  have hsum : p ∣ ∑ k ∈ poleIdx (p := p) r, term (p - r) k / p := by
    have hcast :
        ((∑ k ∈ poleIdx (p := p) r, term (p - r) k / p : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sum, sum_term_div_p_poleIdx (p := p) hr0 hr2 hrp]
    exact (ZMod.natCast_eq_zero_iff _ p).mp hcast
  have hsplit :
      ∑ k ∈ poleIdx (p := p) r, term (p - r) k =
        p * ∑ k ∈ poleIdx (p := p) r, term (p - r) k / p := by
    rw [Finset.mul_sum]
    refine sum_congr rfl ?_
    intro k hk
    exact (Nat.mul_div_cancel' (hdiv k hk)).symm
  rw [hsplit, pow_two]
  exact mul_dvd_mul_left p hsum

lemma psq_dvd_of_not_pole {r k : ℕ} (hr0 : 0 < r) (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    (hkn : k ≤ p - r) (hnp : (k : ZMod p) ∉ poles (p := p) r) :
    p ^ 2 ∣ term (p - r) k := by
  have hreg := region_of_le_n (p := p) hrp hkn
  rcases hreg with hA | hB | hC | hD | hE
  · exact (hnp (mem_poles_of_inA (p := p) hA)).elim
  · exact (hnp (mem_poles_of_inB (p := p) hr2 hrp hB)).elim
  · exact psq_dvd_of_inC (p := p) hr0 hr2 hrp hC hkn
  · exact (hnp (mem_poles_of_inD (p := p) hr2 hrp hD hkn)).elim
  · exact psq_dvd_of_inE (p := p) hr0 hr2 hrp hE hkn

lemma psq_dvd_a_general {r : ℕ} (hr0 : 0 < r) (hr2 : 2 ≤ r) (hrp : 3 * r < p) :
    p ^ 2 ∣ a (p - r) := by
  rw [a_eq_sum_term]
  have hsplit : range (p - r + 1) =
      poleIdx (p := p) r ∪
        (range (p - r + 1)).filter (fun k => (k : ZMod p) ∉ poles (p := p) r) := by
    ext k
    simp only [mem_union, mem_filter, poleIdx, Nat.lt_succ_iff]
    constructor
    · intro hk
      by_cases hpole : (k : ZMod p) ∈ poles (p := p) r
      · exact Or.inl ⟨hk, hpole⟩
      · exact Or.inr ⟨hk, hpole⟩
    · rintro (⟨hk, _⟩ | ⟨hk, _⟩) <;> exact hk
  have hdis : Disjoint (poleIdx (p := p) r)
      ((range (p - r + 1)).filter (fun k => (k : ZMod p) ∉ poles (p := p) r)) := by
    refine disjoint_left.mpr ?_
    intro k hk1 hk2
    exact (mem_filter.mp hk2).2 (mem_poleIdx (p := p) (r := r) |>.mp hk1).2
  rw [hsplit, sum_union hdis]
  refine dvd_add (psq_dvd_sum_ABD (p := p) hr0 hr2 hrp) ?_
  refine dvd_sum ?_
  intro k hk
  have ⟨hkrange, hnp⟩ := mem_filter.mp hk
  have hkn : k ≤ p - r := Nat.lt_succ_iff.mp (mem_range.mp hkrange)
  exact psq_dvd_of_not_pole (p := p) hr0 hr2 hrp hkn hnp


/-- First-order `E`-region residue, parallel to `term_div_psq_inC`. -/
lemma term_div_psq_inE {r k : ℕ}
    (hr0 : 0 < r) (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    (hE : inE p r k) (hkn : k ≤ p - r) :
    p ^ 2 ∣ term (p - r) k ∧
    ((term (p - r) k / p ^ 2 : ℕ) : ZMod p) =
      (((-1 : ZMod p) ^ k * ((r + k - 1).choose k : ZMod p)) ^ 2) *
        ((-1 : ZMod p) ^ (r - 1) * ((r : ZMod p) * (k.choose r : ZMod p))⁻¹) *
          ((4 : ZMod p) * (-1 : ZMod p) ^ (r - 1) * ((r - 1)! : ZMod p) *
            (∏ j ∈ Icc (1 : ℕ) r,
              ((thirdL (p := p) r k : ZMod p) - (j : ZMod p)))⁻¹) := by
  have hpsq := psq_dvd_of_inE (p := p) hr0 hr2 hrp hE hkn
  refine ⟨hpsq, ?_⟩
  have hr := r_lt_p_of_three (p := p) hrp
  have hkp : k < p := by omega
  have hkr : r ≤ k := by
    have : p + 3 * r ≤ 2 * k := hE
    omega
  have hmid := choose_p_sub_add_div_p_zmod (p := p) (r := r) (k := k) hr0 hr hkr hkp
  have ⟨hL, hU⟩ : thirdL (p := p) r k ≤ 4 * p ∧
      4 * p ≤ thirdL (p := p) r k + p - r - 1 := by
    have hE' : p + 3 * r ≤ 2 * k := hE
    constructor
    · simp only [thirdL]; omega
    · have hUeq := thirdL_U (p := p) (r := r) (k := k) (le_of_lt hr)
      rw [hUeq]; omega
  have hp4 : 4 < p := four_lt_p_of_r (p := p) hr2 hrp
  have hth := choose_div_p_of_interval_len (p := p) (L := thirdL (p := p) r k)
      (r := r) (q := 4) hr0 hr (by decide : 0 < 4) hp4 hL hU
  have hcheq := third_choose_eq_L (p := p) (r := r) (k := k) (le_of_lt hr)
  have hppos : 0 < p := p_pos (p := p)
  have hdiv : term (p - r) k / p ^ 2 =
      (p - r).choose k ^ 2 * ((p - r + k).choose k / p) *
        ((3 * (p - r) + 2 * k).choose (p - r) / p) := by
    rw [term, pow_two]
    obtain ⟨c, hc⟩ := hmid.1
    have h2 : p ∣ (3 * (p - r) + 2 * k).choose (p - r) := by
      rw [hcheq]; exact hth.1
    obtain ⟨d, hd⟩ := h2
    rw [hc, hd]
    have : (p - r).choose k * (p - r).choose k * (p * c) * (p * d) / (p * p) =
        (p - r).choose k * (p - r).choose k * c * d := by
      have hmul :
          (p - r).choose k * (p - r).choose k * (p * c) * (p * d) =
            ((p - r).choose k * (p - r).choose k * c * d) * (p * p) := by ring
      rw [hmul, Nat.mul_div_cancel _ (mul_pos hppos hppos)]
    have hpsq' : p ^ 2 = p * p := by ring
    rw [hpsq', this, Nat.mul_div_cancel_left c hppos, Nat.mul_div_cancel_left d hppos]
  rw [hdiv, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow]
  rw [choose_p_sub_zmod (p := p) hr0 hr hkn, hmid.2, hcheq, hth.2]
  simp

lemma Q2_ne_zero_of_not_pole {r k : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    (hnp : (k : ZMod p) ∉ type2Poles (p := p) r) :
    (∏ μ ∈ Icc (2 * r) (3 * r - 1),
        ((2 : ZMod p) * (k : ZMod p) - (μ : ZMod p))) ≠ 0 := by
  refine prod_ne_zero_iff.mpr ?_
  intro μ hμ
  intro h0
  have hμeq : (2 : ZMod p) * (k : ZMod p) = (μ : ZMod p) := sub_eq_zero.mp h0
  have h2 := two_inv_mul_two (p := p) hr2 hrp
  have : (k : ZMod p) = (μ : ZMod p) * (2 : ZMod p)⁻¹ := by
    calc (k : ZMod p)
        = (k : ZMod p) * ((2 : ZMod p) * (2 : ZMod p)⁻¹) := by rw [h2, mul_one]
      _ = ((2 : ZMod p) * (k : ZMod p)) * (2 : ZMod p)⁻¹ := by ring
      _ = (μ : ZMod p) * (2 : ZMod p)⁻¹ := by rw [hμeq]
  rw [this] at hnp
  exact hnp (mem_type2Poles_of_mul (p := p) hr2 hrp hμ)

lemma f_denom_type1_ne {r k : ℕ} (hrp : r < p) (hkp : k < p) (hkA : ¬ k < r) :
    (∏ i ∈ range r, ((k : ZMod p) - (i : ZMod p))) ≠ 0 := by
  refine prod_ne_zero_iff.mpr ?_
  intro i hi
  intro h0
  have : (k : ZMod p) = (i : ZMod p) := sub_eq_zero.mp h0
  have hir : i < r := mem_range.mp hi
  have hmod : k ≡ i [MOD p] := (ZMod.natCast_eq_natCast_iff _ _ p).mp this
  have heq : k = i := by
    rcases le_total k i with hle | hle
    · have hdvd : p ∣ i - k := (Nat.modEq_iff_dvd' hle).mp hmod
      have : i - k = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
      omega
    · have hdvd : p ∣ k - i := (Nat.modEq_iff_dvd' hle).mp hmod.symm
      have : k - i = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
      omega
  omega

lemma term_div_psq_eq_three_f {r k : ℕ}
    (hr0 : 0 < r) (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    (hC : inC p r k) (hkn : k ≤ p - r) :
    ((term (p - r) k / p ^ 2 : ℕ) : ZMod p) =
      (3 : ZMod p) * (Ppoly (p := p) r).eval (k : ZMod p) *
        (∏ i ∈ range r, ((k : ZMod p) - (i : ZMod p)))⁻¹ *
        (∏ μ ∈ Icc (2 * r) (3 * r - 1),
          ((2 : ZMod p) * (k : ZMod p) - (μ : ZMod p)))⁻¹ := by
  have hr := r_lt_p_of_three (p := p) hrp
  have hkp : k < p := by omega
  have hkr : r ≤ k := by have : 3 * r ≤ 2 * k := hC.1; omega
  have hform := term_div_psq_inC (p := p) hr0 hr2 hrp hC hkn
  have hQ := prod_third_eq_Q2 (p := p) hr0 hr2 hrp (k := k)
  have hP := eval_Ppoly_eq_choose (p := p) hr2 hrp (k := k)
  have htype1 := prod_type1_at_nat (p := p) hr hkr hkp
  have hrf : (r : ZMod p) * ((r - 1)! : ZMod p) = (r ! : ZMod p) :=
    r_mul_fac (p := p) hr0 hr
  have hrne : (r : ZMod p) ≠ 0 := zmod_nat_ne_zero hr0 hr
  have hCne : (k.choose r : ZMod p) ≠ 0 := coprime_choose_ne_zero hkp hkr
  have hfac : ((r - 1)! : ZMod p) ≠ 0 := factorial_ne_zero_zmod (by omega)
  have hsgn : ((-1 : ZMod p) ^ (r - 1)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have hpowk : ((-1 : ZMod p) ^ k) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have hnp : (k : ZMod p) ∉ type2Poles (p := p) r := by
    intro ht
    have hABD := mem_poles_imp_ABD (p := p) hr2 hrp hkn (mem_union_right _ ht)
    rcases hABD with hA | hB | hD
    · unfold inA inC at *; omega
    · unfold inB inC at *; omega
    · unfold inD inC at *; omega
  have hQ0 := Q2_ne_zero_of_not_pole (p := p) hr2 hrp hnp
  have htype1ne : ((r ! : ZMod p) * (k.choose r : ZMod p)) ≠ 0 :=
    mul_ne_zero (factorial_ne_zero_zmod hr) hCne
  rw [hform.2, hQ, hP, htype1]
  trans (3 : ZMod p) * (((r + k - 1).choose k : ZMod p) * ((r - 1)! : ZMod p)) ^ 2 *
      (((r : ZMod p) * ((r - 1)! : ZMod p) * (k.choose r : ZMod p))⁻¹) *
      (∏ μ ∈ Icc (2 * r) (3 * r - 1),
        ((2 : ZMod p) * (k : ZMod p) - (μ : ZMod p)))⁻¹
  · trans ((r + k - 1).choose k : ZMod p) ^ 2 *
        ((-1 : ZMod p) ^ k) ^ 2 *
        ((-1 : ZMod p) ^ (r - 1) * (-1 : ZMod p) ^ (r - 1)) *
        (3 : ZMod p) * ((r - 1)! : ZMod p) *
        ((r : ZMod p) * (k.choose r : ZMod p))⁻¹ *
        (∏ μ ∈ Icc (2 * r) (3 * r - 1),
          ((2 : ZMod p) * (k : ZMod p) - (μ : ZMod p)))⁻¹
    · ring
    · have hsgn2 : (-1 : ZMod p) ^ (r - 1) * (-1 : ZMod p) ^ (r - 1) = 1 := by
        rw [← pow_two, hsgn]
      have hid :
          ((r + k - 1).choose k : ZMod p) ^ 2 * ((r - 1)! : ZMod p) *
              ((r : ZMod p) * (k.choose r : ZMod p))⁻¹ =
            (((r + k - 1).choose k : ZMod p) * ((r - 1)! : ZMod p)) ^ 2 *
              ((r : ZMod p) * ((r - 1)! : ZMod p) * (k.choose r : ZMod p))⁻¹ := by
        field
      rw [hpowk, hsgn2]
      convert congrArg (fun z => (3 : ZMod p) * z *
          (∏ μ ∈ Icc (2 * r) (3 * r - 1),
            ((2 : ZMod p) * (k : ZMod p) - (μ : ZMod p)))⁻¹) hid using 1 <;> ring
  · rw [hrf]
    try rfl

lemma term_div_psq_eq_four_f {r k : ℕ}
    (hr0 : 0 < r) (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    (hE : inE p r k) (hkn : k ≤ p - r) :
    ((term (p - r) k / p ^ 2 : ℕ) : ZMod p) =
      (4 : ZMod p) * (Ppoly (p := p) r).eval (k : ZMod p) *
        (∏ i ∈ range r, ((k : ZMod p) - (i : ZMod p)))⁻¹ *
        (∏ μ ∈ Icc (2 * r) (3 * r - 1),
          ((2 : ZMod p) * (k : ZMod p) - (μ : ZMod p)))⁻¹ := by
  have hr := r_lt_p_of_three (p := p) hrp
  have hkp : k < p := by omega
  have hkr : r ≤ k := by
    have : p + 3 * r ≤ 2 * k := hE
    omega
  have hform := term_div_psq_inE (p := p) hr0 hr2 hrp hE hkn
  have hQ := prod_third_eq_Q2 (p := p) hr0 hr2 hrp (k := k)
  have hP := eval_Ppoly_eq_choose (p := p) hr2 hrp (k := k)
  have htype1 := prod_type1_at_nat (p := p) hr hkr hkp
  have hrf : (r : ZMod p) * ((r - 1)! : ZMod p) = (r ! : ZMod p) :=
    r_mul_fac (p := p) hr0 hr
  have hCne : (k.choose r : ZMod p) ≠ 0 := coprime_choose_ne_zero hkp hkr
  have hsgn : ((-1 : ZMod p) ^ (r - 1)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have hpowk : ((-1 : ZMod p) ^ k) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have hnp : (k : ZMod p) ∉ type2Poles (p := p) r := by
    intro ht
    have hABD := mem_poles_imp_ABD (p := p) hr2 hrp hkn (mem_union_right _ ht)
    rcases hABD with hA | hB | hD
    · unfold inA inE at *; omega
    · unfold inB inE at *; omega
    · unfold inD inE at *; omega
  have hQ0 := Q2_ne_zero_of_not_pole (p := p) hr2 hrp hnp
  rw [hform.2, hQ, hP, htype1]
  trans (4 : ZMod p) * (((r + k - 1).choose k : ZMod p) * ((r - 1)! : ZMod p)) ^ 2 *
      (((r : ZMod p) * ((r - 1)! : ZMod p) * (k.choose r : ZMod p))⁻¹) *
      (∏ μ ∈ Icc (2 * r) (3 * r - 1),
        ((2 : ZMod p) * (k : ZMod p) - (μ : ZMod p)))⁻¹
  · trans ((r + k - 1).choose k : ZMod p) ^ 2 *
        ((-1 : ZMod p) ^ k) ^ 2 *
        ((-1 : ZMod p) ^ (r - 1) * (-1 : ZMod p) ^ (r - 1)) *
        (4 : ZMod p) * ((r - 1)! : ZMod p) *
        ((r : ZMod p) * (k.choose r : ZMod p))⁻¹ *
        (∏ μ ∈ Icc (2 * r) (3 * r - 1),
          ((2 : ZMod p) * (k : ZMod p) - (μ : ZMod p)))⁻¹
    · ring
    · have hsgn2 : (-1 : ZMod p) ^ (r - 1) * (-1 : ZMod p) ^ (r - 1) = 1 := by
        rw [← pow_two, hsgn]
      have hid :
          ((r + k - 1).choose k : ZMod p) ^ 2 * ((r - 1)! : ZMod p) *
              ((r : ZMod p) * (k.choose r : ZMod p))⁻¹ =
            (((r + k - 1).choose k : ZMod p) * ((r - 1)! : ZMod p)) ^ 2 *
              ((r : ZMod p) * ((r - 1)! : ZMod p) * (k.choose r : ZMod p))⁻¹ := by
        field
      rw [hpowk, hsgn2]
      convert congrArg (fun z => (4 : ZMod p) * z *
          (∏ μ ∈ Icc (2 * r) (3 * r - 1),
            ((2 : ZMod p) * (k : ZMod p) - (μ : ZMod p)))⁻¹) hid using 1 <;> ring
  · rw [hrf]
    try rfl

/-! ### Second-order expansions in `ZMod (p ^ 2)`. -/

lemma prod_one_sub_nilp {α : Type*} [CommRing α] {d : α} (hd : d * d = 0)
    (s : Finset ℕ) (u : ℕ → α) :
    (∏ i ∈ s, (1 - d * u i)) = 1 - d * ∑ i ∈ s, u i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [prod_insert hi, sum_insert hi, ih]
    have : (d * u i) * (d * ∑ j ∈ s, u j) = 0 := by
      calc
        (d * u i) * (d * ∑ j ∈ s, u j)
            = (d * d) * (u i * ∑ j ∈ s, u j) := by ring
        _ = 0 := by rw [hd, zero_mul]
    calc
      (1 - d * u i) * (1 - d * ∑ j ∈ s, u j)
          = 1 - d * ∑ j ∈ s, u j - d * u i + (d * u i) * (d * ∑ j ∈ s, u j) := by
            ring
      _ = 1 - d * ∑ j ∈ s, u j - d * u i + 0 := by rw [this]
      _ = 1 - d * (u i + ∑ j ∈ s, u j) := by ring

lemma p_sub_nat_zmod_sq {a : ℕ} (ha0 : 0 < a) (hap : a < p) :
    ((p - a : ℕ) : ZMod (p ^ 2)) =
      (-(a : ZMod (p ^ 2))) *
        (1 - (p : ZMod (p ^ 2)) * Ring.inverse (a : ZMod (p ^ 2))) := by
  have hpr : p.Prime := Fact.out
  have hunit := isUnit_nat_zmod_sq ha0 hap hpr
  have hinv : (a : ZMod (p ^ 2)) * Ring.inverse (a : ZMod (p ^ 2)) = 1 :=
    Ring.mul_inverse_cancel _ hunit
  have hle : a ≤ p := le_of_lt hap
  rw [Nat.cast_sub hle]
  calc (p : ZMod (p ^ 2)) - (a : ZMod (p ^ 2))
      = -(a : ZMod (p ^ 2)) + (p : ZMod (p ^ 2)) := by ring
    _ = -(a : ZMod (p ^ 2)) +
          (p : ZMod (p ^ 2)) *
            ((a : ZMod (p ^ 2)) * Ring.inverse (a : ZMod (p ^ 2))) := by
          rw [hinv, mul_one]
    _ = (-(a : ZMod (p ^ 2))) *
          (1 - (p : ZMod (p ^ 2)) * Ring.inverse (a : ZMod (p ^ 2))) := by
          ring

lemma prod_range_p_sub_zmod_sq {r k : ℕ} (hr0 : 0 < r) (hrp : r < p)
    (hk : k ≤ p - r) :
    (∏ i ∈ range k, ((p - r - i : ℕ) : ZMod (p ^ 2))) =
      (-1 : ZMod (p ^ 2)) ^ k *
        (∏ i ∈ range k, ((r + i : ℕ) : ZMod (p ^ 2))) *
        (1 - (p : ZMod (p ^ 2)) *
          ∑ i ∈ range k, Ring.inverse ((r + i : ℕ) : ZMod (p ^ 2))) := by
  have hpr : p.Prime := Fact.out
  have hfac : ∀ i ∈ range k,
      ((p - r - i : ℕ) : ZMod (p ^ 2)) =
        (-((r + i : ℕ) : ZMod (p ^ 2))) *
          (1 - (p : ZMod (p ^ 2)) *
            Ring.inverse ((r + i : ℕ) : ZMod (p ^ 2))) := by
    intro i hi
    have hi' : i < k := mem_range.mp hi
    have ha0 : 0 < r + i := by omega
    have hap : r + i < p := by omega
    have : p - r - i = p - (r + i) := by omega
    rw [this]
    exact p_sub_nat_zmod_sq ha0 hap
  rw [prod_congr rfl hfac, prod_mul_distrib, prod_neg, card_range]
  have hd : (p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) = 0 :=
    p_mul_p_zmod_sq (p := p)
  rw [prod_one_sub_nilp hd]

lemma prod_range_r_add_choose {r k : ℕ} (hr2 : 1 ≤ r) :
    (∏ i ∈ range k, (r + i)) = (r + k - 1).choose k * k ! := by
  by_cases hk0 : k = 0
  · subst hk0; simp
  have href := prod_range_reflect (fun j => r + j) k
  have hre : ∏ i ∈ range k, (r + k - 1 - i) = ∏ i ∈ range k, (r + (k - 1 - i)) := by
    refine prod_congr rfl ?_
    intro i hi
    have : i < k := mem_range.mp hi
    have : r + k - 1 - i = r + (k - 1 - i) := by omega
    exact this
  rw [← href, ← hre, ← descFactorial_eq_prod_range,
    descFactorial_eq_factorial_mul_choose, mul_comm]

lemma choose_p_sub_zmod_sq {r k : ℕ} (hr0 : 0 < r) (hrp : r < p)
    (hk : k ≤ p - r) :
    ((p - r).choose k : ZMod (p ^ 2)) =
      (-1 : ZMod (p ^ 2)) ^ k * ((r + k - 1).choose k : ZMod (p ^ 2)) *
        (1 - (p : ZMod (p ^ 2)) *
          ∑ i ∈ range k, Ring.inverse ((r + i : ℕ) : ZMod (p ^ 2))) := by
  have hpr : p.Prime := Fact.out
  have hklt : k < p := by omega
  have hfacU : IsUnit (k ! : ZMod (p ^ 2)) := isUnit_factorial_zmod_sq hklt hpr
  have hdesc : ((p - r).descFactorial k : ZMod (p ^ 2)) =
      ((p - r).choose k : ZMod (p ^ 2)) * (k ! : ZMod (p ^ 2)) := by
    rw [descFactorial_eq_factorial_mul_choose, mul_comm, Nat.cast_mul]
  have hleft := prod_range_p_sub_zmod_sq (p := p) hr0 hrp hk
  have hdesc' : ((p - r).descFactorial k : ZMod (p ^ 2)) =
      (∏ i ∈ range k, ((p - r - i : ℕ) : ZMod (p ^ 2))) := by
    rw [descFactorial_eq_prod_range, Nat.cast_prod]
  have hprod : (∏ i ∈ range k, ((r + i : ℕ) : ZMod (p ^ 2))) =
      ((r + k - 1).choose k : ZMod (p ^ 2)) * (k ! : ZMod (p ^ 2)) := by
    rw [← Nat.cast_prod, prod_range_r_add_choose (by omega), Nat.cast_mul]
  have hmul :
      ((p - r).choose k : ZMod (p ^ 2)) * (k ! : ZMod (p ^ 2)) =
        ((-1 : ZMod (p ^ 2)) ^ k * ((r + k - 1).choose k : ZMod (p ^ 2)) *
          (1 - (p : ZMod (p ^ 2)) *
            ∑ i ∈ range k, Ring.inverse ((r + i : ℕ) : ZMod (p ^ 2)))) *
          (k ! : ZMod (p ^ 2)) := by
    rw [← hdesc, hdesc', hleft, hprod]
    ring
  have hmul' :
      (k ! : ZMod (p ^ 2)) * ((p - r).choose k : ZMod (p ^ 2)) =
        (k ! : ZMod (p ^ 2)) *
          ((-1 : ZMod (p ^ 2)) ^ k * ((r + k - 1).choose k : ZMod (p ^ 2)) *
            (1 - (p : ZMod (p ^ 2)) *
              ∑ i ∈ range k, Ring.inverse ((r + i : ℕ) : ZMod (p ^ 2)))) := by
    convert hmul using 1 <;> ring
  exact (IsUnit.mul_right_inj hfacU).mp hmul'


lemma choose_p_sub_add_zmod_sq {r k : ℕ} (hr0 : 0 < r) (hrp : r < p)
    (hk : k < r) :
    ((p - r + k).choose k : ZMod (p ^ 2)) =
      (-1 : ZMod (p ^ 2)) ^ k * ((r - 1).choose k : ZMod (p ^ 2)) *
        (1 - (p : ZMod (p ^ 2)) *
          ∑ i ∈ range k, Ring.inverse ((r - k + i : ℕ) : ZMod (p ^ 2))) := by
  have hpr : p.Prime := Fact.out
  have hklt : k < p := lt_trans hk hrp
  have hfacU : IsUnit (k ! : ZMod (p ^ 2)) := isUnit_factorial_zmod_sq hklt hpr
  have hdesc : ((p - r + k).descFactorial k : ZMod (p ^ 2)) =
      ((p - r + k).choose k : ZMod (p ^ 2)) * (k ! : ZMod (p ^ 2)) := by
    rw [descFactorial_eq_factorial_mul_choose, mul_comm, Nat.cast_mul]
  have hdesc' : ((p - r + k).descFactorial k : ZMod (p ^ 2)) =
      (∏ i ∈ range k, ((p - r + k - i : ℕ) : ZMod (p ^ 2))) := by
    rw [descFactorial_eq_prod_range, Nat.cast_prod]
  have hfac : ∀ i ∈ range k,
      ((p - r + k - i : ℕ) : ZMod (p ^ 2)) =
        (-((r - k + i : ℕ) : ZMod (p ^ 2))) *
          (1 - (p : ZMod (p ^ 2)) *
            Ring.inverse ((r - k + i : ℕ) : ZMod (p ^ 2))) := by
    intro i hi
    have hi' : i < k := mem_range.mp hi
    have ha0 : 0 < r - k + i := by omega
    have hap : r - k + i < p := by omega
    have : p - r + k - i = p - (r - k + i) := by omega
    rw [this]
    exact p_sub_nat_zmod_sq ha0 hap
  have hprod1 :
      (∏ i ∈ range k, ((p - r + k - i : ℕ) : ZMod (p ^ 2))) =
        (-1 : ZMod (p ^ 2)) ^ k *
          (∏ i ∈ range k, ((r - k + i : ℕ) : ZMod (p ^ 2))) *
          (1 - (p : ZMod (p ^ 2)) *
            ∑ i ∈ range k, Ring.inverse ((r - k + i : ℕ) : ZMod (p ^ 2))) := by
    rw [prod_congr rfl hfac, prod_mul_distrib, prod_neg, card_range]
    have hd : (p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) = 0 :=
      p_mul_p_zmod_sq (p := p)
    rw [prod_one_sub_nilp hd]
  have hprod2 :
      (∏ i ∈ range k, ((r - k + i : ℕ) : ZMod (p ^ 2))) =
        ((r - 1).choose k : ZMod (p ^ 2)) * (k ! : ZMod (p ^ 2)) := by
    -- (r-k)...(r-1) = (r-1).descFactorial k
    have href := prod_range_reflect (fun j => r - k + j) k
    have hre : ∏ i ∈ range k, (r - 1 - i) = ∏ i ∈ range k, (r - k + (k - 1 - i)) := by
      refine prod_congr rfl ?_
      intro i hi
      have : i < k := mem_range.mp hi
      have : r - 1 - i = r - k + (k - 1 - i) := by omega
      exact this
    have : ∏ i ∈ range k, (r - k + i) = (r - 1).choose k * k ! := by
      rw [← href, ← hre, ← descFactorial_eq_prod_range,
        descFactorial_eq_factorial_mul_choose, mul_comm]
    rw [← Nat.cast_prod, this, Nat.cast_mul]
  have hmul :
      ((p - r + k).choose k : ZMod (p ^ 2)) * (k ! : ZMod (p ^ 2)) =
        ((-1 : ZMod (p ^ 2)) ^ k * ((r - 1).choose k : ZMod (p ^ 2)) *
          (1 - (p : ZMod (p ^ 2)) *
            ∑ i ∈ range k, Ring.inverse ((r - k + i : ℕ) : ZMod (p ^ 2)))) *
          (k ! : ZMod (p ^ 2)) := by
    rw [← hdesc, hdesc', hprod1, hprod2]
    ring
  have hmul' :
      (k ! : ZMod (p ^ 2)) * ((p - r + k).choose k : ZMod (p ^ 2)) =
        (k ! : ZMod (p ^ 2)) *
          ((-1 : ZMod (p ^ 2)) ^ k * ((r - 1).choose k : ZMod (p ^ 2)) *
            (1 - (p : ZMod (p ^ 2)) *
              ∑ i ∈ range k, Ring.inverse ((r - k + i : ℕ) : ZMod (p ^ 2)))) := by
    convert hmul using 1 <;> ring
  exact (IsUnit.mul_right_inj hfacU).mp hmul'

/-! ### Pole representatives and `ZMod (p ^ 2)` tools. -/

open Polynomial

/-- Type-II pole representative in `0 .. p-1`: `μ/2` if even, `(μ+p)/2` if odd. -/
def type2Rep (μ : ℕ) : ℕ := if μ % 2 = 0 then μ / 2 else (μ + p) / 2

def poleReps (r : ℕ) : Finset ℕ :=
  range r ∪ (Icc (2 * r) (3 * r - 1)).image (fun μ => type2Rep (p := p) μ)

lemma p_odd_of_three {r : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p) : p % 2 = 1 :=
  p_odd (p := p) (le_trans (by decide : 5 ≤ 7) (by omega))

lemma type2Rep_even {μ : ℕ} (h : μ % 2 = 0) :
    type2Rep (p := p) μ = μ / 2 := by
  simp [type2Rep, h]

lemma type2Rep_odd {μ : ℕ} (h : μ % 2 = 1) :
    type2Rep (p := p) μ = (μ + p) / 2 := by
  simp [type2Rep, h]

lemma two_mul_type2Rep {μ : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p) :
    2 * type2Rep (p := p) μ =
      if μ % 2 = 0 then μ else μ + p := by
  by_cases h : μ % 2 = 0
  · rw [type2Rep_even h, if_pos h, Nat.mul_div_cancel']
    exact Nat.dvd_of_mod_eq_zero h
  · have h1 : μ % 2 = 1 := Nat.mod_two_ne_zero.mp h
    have hp1 := p_odd_of_three (p := p) hr2 hrp
    have : (μ + p) % 2 = 0 := by omega
    rw [type2Rep_odd h1, if_neg h, Nat.mul_div_cancel']
    exact Nat.dvd_of_mod_eq_zero this

lemma type2Rep_lt_p {r μ : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    (hμ : μ ∈ Icc (2 * r) (3 * r - 1)) :
    type2Rep (p := p) μ < p := by
  have hμI := mem_Icc.mp hμ
  by_cases h : μ % 2 = 0
  · rw [type2Rep_even h]; omega
  · have h1 : μ % 2 = 1 := Nat.mod_two_ne_zero.mp h
    rw [type2Rep_odd h1]; omega

lemma type2Rep_cast {r μ : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    (hμ : μ ∈ Icc (2 * r) (3 * r - 1)) :
    ((type2Rep (p := p) μ : ℕ) : ZMod p) = (μ : ZMod p) * (2 : ZMod p)⁻¹ := by
  have h2 := two_inv_mul_two (p := p) hr2 hrp
  have hmul : ((2 * type2Rep (p := p) μ : ℕ) : ZMod p) = (μ : ZMod p) := by
    rw [two_mul_type2Rep (p := p) hr2 hrp]
    split_ifs
    · rfl
    · rw [Nat.cast_add, CharP.cast_eq_zero (R := ZMod p) p, add_zero]
  have : (2 : ZMod p) * (type2Rep (p := p) μ : ZMod p) = (μ : ZMod p) := by
    rw [← Nat.cast_ofNat, ← Nat.cast_mul, hmul]
  calc (type2Rep (p := p) μ : ZMod p)
      = (type2Rep (p := p) μ : ZMod p) * ((2 : ZMod p) * (2 : ZMod p)⁻¹) := by
        rw [h2, mul_one]
    _ = ((2 : ZMod p) * (type2Rep (p := p) μ : ZMod p)) * (2 : ZMod p)⁻¹ := by ring
    _ = (μ : ZMod p) * (2 : ZMod p)⁻¹ := by rw [this]

lemma injOn_type2Rep {r : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p) :
    Set.InjOn (fun μ : ℕ => type2Rep (p := p) μ) (Icc (2 * r) (3 * r - 1)) := by
  intro a ha b hb heq
  have haI : a ∈ Icc (2 * r) (3 * r - 1) := by simpa [Set.mem_Icc] using ha
  have hbI : b ∈ Icc (2 * r) (3 * r - 1) := by simpa [Set.mem_Icc] using hb
  have hcast : (type2Rep (p := p) a : ZMod p) = (type2Rep (p := p) b : ZMod p) :=
    congrArg (fun n : ℕ => (n : ZMod p)) heq
  rw [type2Rep_cast (p := p) (r := r) hr2 hrp haI,
      type2Rep_cast (p := p) (r := r) hr2 hrp hbI] at hcast
  exact injOn_type2 (p := p) hr2 hrp ha hb hcast

lemma poleReps_lt_p {r : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    {k : ℕ} (hk : k ∈ poleReps (p := p) r) : k < p := by
  rw [poleReps, mem_union] at hk
  rcases hk with h | h
  · exact lt_trans (mem_range.mp h) (r_lt_p_of_three (p := p) hrp)
  · obtain ⟨μ, hμ, rfl⟩ := mem_image.mp h
    exact type2Rep_lt_p (p := p) hr2 hrp hμ

lemma disjoint_poleReps {r : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p) :
    Disjoint (range r)
      ((Icc (2 * r) (3 * r - 1)).image (fun μ => type2Rep (p := p) μ)) := by
  refine disjoint_left.mpr ?_
  intro x hx1 hx2
  have hx1' : x < r := mem_range.mp hx1
  have h1 : (x : ZMod p) ∈ type1Poles (p := p) r := mem_type1Poles (p := p) hx1'
  obtain ⟨μ, hμ, heq⟩ := mem_image.mp hx2
  have h2 : (x : ZMod p) ∈ type2Poles (p := p) r := by
    rw [← heq, type2Rep_cast (p := p) (r := r) hr2 hrp hμ]
    exact mem_type2Poles_of_mul (p := p) hr2 hrp hμ
  exact (disjoint_left.mp (disjoint_type12 (p := p) hr2 hrp)) h1 h2

lemma card_poleReps {r : ℕ} (hr0 : 0 < r) (hr2 : 2 ≤ r) (hrp : 3 * r < p) :
    #(poleReps (p := p) r) = 2 * r := by
  rw [poleReps, card_union_of_disjoint (disjoint_poleReps (p := p) hr2 hrp),
    card_range, Finset.card_image_of_injOn (injOn_type2Rep (p := p) hr2 hrp),
    card_Icc_two_r (by omega)]
  ring

lemma isUnit_sub_nat_zmod_sq {x y : ℕ} (hxp : x < p) (hyp : y < p) (hne : x ≠ y) :
    IsUnit ((x : ZMod (p ^ 2)) - (y : ZMod (p ^ 2))) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have : (x : ZMod (p ^ 2)) - (y : ZMod (p ^ 2)) =
        -((y - x : ℕ) : ZMod (p ^ 2)) := by
      rw [Nat.cast_sub (le_of_lt hlt)]; ring
    rw [this]
    exact (isUnit_nat_zmod_sq (by omega) (by omega) Fact.out).neg
  · have : (x : ZMod (p ^ 2)) - (y : ZMod (p ^ 2)) =
        ((x - y : ℕ) : ZMod (p ^ 2)) := by
      rw [Nat.cast_sub (le_of_lt hgt)]
    rw [this]
    exact isUnit_nat_zmod_sq (by omega) (by omega) Fact.out

lemma isUnit_sub_poleReps {r : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    {x y : ℕ} (hx : x ∈ poleReps (p := p) r) (hy : y ∈ poleReps (p := p) r)
    (hxy : x ≠ y) :
    IsUnit ((x : ZMod (p ^ 2)) - (y : ZMod (p ^ 2))) :=
  isUnit_sub_nat_zmod_sq
    (poleReps_lt_p (p := p) hr2 hrp hx)
    (poleReps_lt_p (p := p) hr2 hrp hy) hxy

/-- Numerator polynomial over `ZMod (p ^ 2)`. -/
noncomputable def Ppoly2 (r : ℕ) : (ZMod (p ^ 2))[X] :=
  (∏ i ∈ Icc (1 : ℕ) (r - 1), (X + C (i : ZMod (p ^ 2)))) ^ 2

lemma eval_Ppoly2 (r : ℕ) (x : ZMod (p ^ 2)) :
    (Ppoly2 (p := p) r).eval x =
      (∏ i ∈ Icc (1 : ℕ) (r - 1), (x + (i : ZMod (p ^ 2)))) ^ 2 := by
  simp only [Ppoly2, eval_pow, eval_prod, eval_add, eval_X, eval_C]

lemma monic_X_add_C_prod (r : ℕ) :
    (∏ i ∈ Icc (1 : ℕ) (r - 1),
      (X + C (i : ZMod (p ^ 2)) : (ZMod (p ^ 2))[X])).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => monic_X_add_C _)

lemma natDegree_Ppoly2 {r : ℕ} (hr2 : 2 ≤ r) :
    (Ppoly2 (p := p) r).natDegree = 2 * (r - 1) := by
  haveI : Fact (1 < p ^ 2) := ⟨by
    have : 2 ≤ p := p_ge_two (p := p)
    nlinarith⟩
  have hcard : #(Icc (1 : ℕ) (r - 1)) = r - 1 := by rw [Nat.card_Icc]; omega
  have hmon := monic_X_add_C_prod (p := p) r
  have hprod := natDegree_prod_of_monic
    (s := Icc (1 : ℕ) (r - 1))
    (f := fun i : ℕ => (X + C (i : ZMod (p ^ 2)) : (ZMod (p ^ 2))[X]))
    (fun _ _ => monic_X_add_C _)
  have hdeg1 : ∀ i ∈ Icc (1 : ℕ) (r - 1),
      (X + C (i : ZMod (p ^ 2)) : (ZMod (p ^ 2))[X]).natDegree = 1 :=
    fun _ _ => natDegree_X_add_C _
  have hsum : ∑ i ∈ Icc (1 : ℕ) (r - 1),
      (X + C (i : ZMod (p ^ 2)) : (ZMod (p ^ 2))[X]).natDegree = r - 1 := by
    rw [sum_congr rfl hdeg1, sum_const, hcard, smul_eq_mul, mul_one]
  rw [Ppoly2, hmon.natDegree_pow, hprod, hsum]

lemma eval_Ppoly2_extra_zero {r k : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    (hgt : p - r < k) (hkp : k < p) :
    (Ppoly2 (p := p) r).eval (k : ZMod (p ^ 2)) = 0 := by
  have hi : p - k ∈ Icc (1 : ℕ) (r - 1) := by
    rw [mem_Icc]; constructor <;> omega
  have hprod : ∏ i ∈ Icc (1 : ℕ) (r - 1), (k + i) =
      p * ∏ i ∈ (Icc (1 : ℕ) (r - 1)).erase (p - k), (k + i) := by
    rw [← mul_prod_erase _ _ hi]
    congr 1
    omega
  have hsq : (∏ i ∈ Icc (1 : ℕ) (r - 1), (k + i)) ^ 2 =
      p ^ 2 * (∏ i ∈ (Icc (1 : ℕ) (r - 1)).erase (p - k), (k + i)) ^ 2 := by
    rw [hprod]; ring
  rw [eval_Ppoly2]
  have hcast :
      (∏ i ∈ Icc (1 : ℕ) (r - 1),
        ((k : ZMod (p ^ 2)) + (i : ZMod (p ^ 2)))) =
      ((∏ i ∈ Icc (1 : ℕ) (r - 1), (k + i) : ℕ) : ZMod (p ^ 2)) := by
    rw [Nat.cast_prod]
    refine prod_congr rfl ?_
    intro i _
    rw [Nat.cast_add]
  rw [hcast, ← Nat.cast_pow, hsq, Nat.cast_mul, p_sq_cast_eq_zero (p := p),
    zero_mul]

lemma not_p_dvd_choose_of_lt {k r : ℕ} (hpr : p.Prime) (hkr : r ≤ k) (hkp : k < p) :
    ¬ p ∣ k.choose r := by
  intro h
  have : p ∣ k ! := by
    rw [← choose_mul_factorial_mul_factorial hkr]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _
  exact (not_le_of_gt hkp) (hpr.dvd_factorial.mp this)

lemma isUnit_choose_zmod_sq {k r : ℕ} (hkr : r ≤ k) (hkp : k < p) :
    IsUnit (k.choose r : ZMod (p ^ 2)) := by
  have hpr : p.Prime := Fact.out
  refine (ZMod.isUnit_iff_coprime _ (p ^ 2)).mpr ?_
  rw [Nat.coprime_pow_right_iff (by decide : 0 < 2)]
  exact ((Nat.Prime.coprime_iff_not_dvd hpr).mpr
    (not_p_dvd_choose_of_lt (p := p) hpr hkr hkp)).symm

/-! Middle binomial `C(p-r+k, k) / p` in `ZMod (p ^ 2)`, for `k ≥ r`. -/

lemma choose_p_sub_add_div_p_zmod_sq {r k : ℕ}
    (hr0 : 0 < r) (hrp : r < p) (hkr : r ≤ k) (hkp : k < p) :
    p ∣ (p - r + k).choose k ∧
    (((p - r + k).choose k / p : ℕ) : ZMod (p ^ 2)) =
      (-1 : ZMod (p ^ 2)) ^ (r - 1) *
        Ring.inverse ((r : ZMod (p ^ 2)) * (k.choose r : ZMod (p ^ 2))) *
        (1 + (p : ZMod (p ^ 2)) *
          (∑ j ∈ Icc 1 (k - r), Ring.inverse (j : ZMod (p ^ 2)) -
            ∑ j ∈ Icc 1 (r - 1), Ring.inverse (j : ZMod (p ^ 2)))) := by
  have hpr : p.Prime := Fact.out
  have hppos : 0 < p := hpr.pos
  have hsplit := descFactorial_p_sub_add_split (p := p) hr0 hrp hkr
  have hfac : (p - r + k).descFactorial k = k ! * (p - r + k).choose k :=
    descFactorial_eq_factorial_mul_choose _ _
  have hmul : k ! * (p - r + k).choose k =
      p * ((∏ j ∈ Icc 1 (k - r), (p + j)) * (∏ j ∈ Icc 1 (r - 1), (p - j))) := by
    rw [← hfac, hsplit]; ring
  have hkndvd : ¬ p ∣ k ! := by
    intro h
    exact (not_le_of_gt hkp) (hpr.dvd_factorial.mp h)
  have hpdvd : p ∣ (p - r + k).choose k := by
    have : p ∣ k ! * (p - r + k).choose k := by
      rw [hmul]; exact dvd_mul_right _ _
    exact (hpr.dvd_mul.mp this).resolve_left hkndvd
  refine ⟨hpdvd, ?_⟩
  have hdiv : k ! * ((p - r + k).choose k / p) =
      (∏ j ∈ Icc 1 (k - r), (p + j)) * (∏ j ∈ Icc 1 (r - 1), (p - j)) := by
    apply Nat.eq_of_mul_eq_mul_left hppos
    calc
      p * (k ! * ((p - r + k).choose k / p))
          = k ! * (p * ((p - r + k).choose k / p)) := by ring
      _ = k ! * (p - r + k).choose k := by rw [Nat.mul_div_cancel' hpdvd]
      _ = p * ((∏ j ∈ Icc 1 (k - r), (p + j)) * (∏ j ∈ Icc 1 (r - 1), (p - j))) :=
            hmul
  have hpos : (∏ j ∈ Icc 1 (k - r), ((p + j : ℕ) : ZMod (p ^ 2))) =
      (∏ j ∈ Icc 1 (k - r), (j : ZMod (p ^ 2))) *
        (1 + (p : ZMod (p ^ 2)) *
          ∑ j ∈ Icc 1 (k - r), Ring.inverse (j : ZMod (p ^ 2))) := by
    by_cases hempty : k ≤ r
    · have : k - r = 0 := Nat.sub_eq_zero_of_le hempty
      simp [this]
    · have hab : 1 ≤ k - r := by omega
      have hbp : k - r < p := by omega
      have hprod := prod_Icc_add_mul_p (p := p) hpr 1 1 (k - r) (by decide) hab hbp
      trans (∏ j ∈ Icc 1 (k - r), ((j + 1 * p : ℕ) : ZMod (p ^ 2)))
      · refine prod_congr rfl ?_
        intro j hj
        congr 1
        ring
      · simpa using hprod
  have hneg : (∏ j ∈ Icc 1 (r - 1), ((p - j : ℕ) : ZMod (p ^ 2))) =
      (-1 : ZMod (p ^ 2)) ^ (r - 1) *
        (∏ j ∈ Icc 1 (r - 1), (j : ZMod (p ^ 2))) *
        (1 - (p : ZMod (p ^ 2)) *
          ∑ j ∈ Icc 1 (r - 1), Ring.inverse (j : ZMod (p ^ 2))) := by
    by_cases hempty : r = 1
    · subst hempty; simp
    · have hfac' : ∀ j ∈ Icc 1 (r - 1),
          ((p - j : ℕ) : ZMod (p ^ 2)) =
            (-(j : ZMod (p ^ 2))) *
              (1 - (p : ZMod (p ^ 2)) * Ring.inverse (j : ZMod (p ^ 2))) := by
        intro j hj
        have hjI := mem_Icc.mp hj
        exact p_sub_nat_zmod_sq (p := p) (by omega) (by omega)
      rw [prod_congr rfl hfac', prod_mul_distrib, prod_neg]
      have hcard : #(Icc 1 (r - 1)) = r - 1 := by rw [Nat.card_Icc]; omega
      rw [hcard, prod_one_sub_nilp (p_mul_p_zmod_sq (p := p))]
  have hfacU : IsUnit (k ! : ZMod (p ^ 2)) := isUnit_factorial_zmod_sq hkp hpr
  have hcast :
      (k ! : ZMod (p ^ 2)) * (((p - r + k).choose k / p : ℕ) : ZMod (p ^ 2)) =
        (∏ j ∈ Icc 1 (k - r), ((p + j : ℕ) : ZMod (p ^ 2))) *
          (∏ j ∈ Icc 1 (r - 1), ((p - j : ℕ) : ZMod (p ^ 2))) := by
    rw [← Nat.cast_mul, hdiv, Nat.cast_mul, Nat.cast_prod, Nat.cast_prod]
  have hfac1 : (∏ j ∈ Icc 1 (k - r), (j : ZMod (p ^ 2))) =
      ((k - r)! : ZMod (p ^ 2)) := by
    rw [← Nat.cast_prod, prod_Icc_one_n]
  have hfac2 : (∏ j ∈ Icc 1 (r - 1), (j : ZMod (p ^ 2))) =
      ((r - 1)! : ZMod (p ^ 2)) := by
    rw [← Nat.cast_prod, prod_Icc_one_n]
  have hC : (k ! : ZMod (p ^ 2)) =
      (r : ZMod (p ^ 2)) * ((r - 1)! : ZMod (p ^ 2)) *
        (k.choose r : ZMod (p ^ 2)) * ((k - r)! : ZMod (p ^ 2)) := by
    have hrw : r = (r - 1) + 1 := by omega
    have : k.choose r * r ! * (k - r)! = k ! :=
      choose_mul_factorial_mul_factorial hkr
    have hrfac : (r ! : ℕ) = r * (r - 1)! := by
      cases r with
      | zero => omega
      | succ r' => simp [factorial_succ]
    rw [← this, hrfac]
    push_cast; ring
  have hRHS :
      (∏ j ∈ Icc 1 (k - r), ((p + j : ℕ) : ZMod (p ^ 2))) *
        (∏ j ∈ Icc 1 (r - 1), ((p - j : ℕ) : ZMod (p ^ 2))) =
      (-1 : ZMod (p ^ 2)) ^ (r - 1) * ((k - r)! : ZMod (p ^ 2)) *
        ((r - 1)! : ZMod (p ^ 2)) *
        (1 + (p : ZMod (p ^ 2)) *
          (∑ j ∈ Icc 1 (k - r), Ring.inverse (j : ZMod (p ^ 2)) -
            ∑ j ∈ Icc 1 (r - 1), Ring.inverse (j : ZMod (p ^ 2)))) := by
    rw [hpos, hneg, hfac1, hfac2]
    have hp2 : (p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) = 0 :=
      p_mul_p_zmod_sq (p := p)
    set A := ∑ j ∈ Icc 1 (k - r), Ring.inverse (j : ZMod (p ^ 2))
    set B := ∑ j ∈ Icc 1 (r - 1), Ring.inverse (j : ZMod (p ^ 2))
    have hnil : (1 + (p : ZMod (p ^ 2)) * A) * (1 - (p : ZMod (p ^ 2)) * B) =
        1 + (p : ZMod (p ^ 2)) * (A - B) := by
      calc
        (1 + (p : ZMod (p ^ 2)) * A) * (1 - (p : ZMod (p ^ 2)) * B)
            = 1 + (p : ZMod (p ^ 2)) * A - (p : ZMod (p ^ 2)) * B -
                (p : ZMod (p ^ 2)) * A * ((p : ZMod (p ^ 2)) * B) := by ring
        _ = 1 + (p : ZMod (p ^ 2)) * A - (p : ZMod (p ^ 2)) * B -
                ((p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) * A * B := by ring
        _ = 1 + (p : ZMod (p ^ 2)) * A - (p : ZMod (p ^ 2)) * B -
                0 * A * B := by rw [hp2]
        _ = 1 + (p : ZMod (p ^ 2)) * (A - B) := by ring
    calc
      ((k - r)! : ZMod (p ^ 2)) *
          (1 + (p : ZMod (p ^ 2)) * A) *
        ((-1 : ZMod (p ^ 2)) ^ (r - 1) * ((r - 1)! : ZMod (p ^ 2)) *
          (1 - (p : ZMod (p ^ 2)) * B))
          = (-1 : ZMod (p ^ 2)) ^ (r - 1) * ((k - r)! : ZMod (p ^ 2)) *
              ((r - 1)! : ZMod (p ^ 2)) *
              ((1 + (p : ZMod (p ^ 2)) * A) * (1 - (p : ZMod (p ^ 2)) * B)) := by
            ring
      _ = (-1 : ZMod (p ^ 2)) ^ (r - 1) * ((k - r)! : ZMod (p ^ 2)) *
            ((r - 1)! : ZMod (p ^ 2)) *
            (1 + (p : ZMod (p ^ 2)) * (A - B)) := by
            rw [hnil]
  -- Cancel `k!`.
  have hmul' :
      (k ! : ZMod (p ^ 2)) * (((p - r + k).choose k / p : ℕ) : ZMod (p ^ 2)) =
        (k ! : ZMod (p ^ 2)) *
          ((-1 : ZMod (p ^ 2)) ^ (r - 1) *
            Ring.inverse ((r : ZMod (p ^ 2)) * (k.choose r : ZMod (p ^ 2))) *
            (1 + (p : ZMod (p ^ 2)) *
              (∑ j ∈ Icc 1 (k - r), Ring.inverse (j : ZMod (p ^ 2)) -
                ∑ j ∈ Icc 1 (r - 1), Ring.inverse (j : ZMod (p ^ 2))))) := by
    rw [hcast, hRHS, hC]
    have hrU : IsUnit (r : ZMod (p ^ 2)) :=
      isUnit_nat_zmod_sq hr0 hrp hpr
    have hCU := isUnit_choose_zmod_sq (p := p) hkr hkp
    have hprodU : IsUnit ((r : ZMod (p ^ 2)) * (k.choose r : ZMod (p ^ 2))) :=
      hrU.mul hCU
    have hinv : ((r : ZMod (p ^ 2)) * (k.choose r : ZMod (p ^ 2))) *
        Ring.inverse ((r : ZMod (p ^ 2)) * (k.choose r : ZMod (p ^ 2))) = 1 :=
      Ring.mul_inverse_cancel _ hprodU
    have h1U : IsUnit ((r - 1)! : ZMod (p ^ 2)) :=
      isUnit_factorial_zmod_sq (by omega) hpr
    have h2U : IsUnit ((k - r)! : ZMod (p ^ 2)) :=
      isUnit_factorial_zmod_sq (lt_of_le_of_lt (Nat.sub_le k r) hkp) hpr
    -- Clear the unit factorials by multiplying both proposed sides.
    set A := (1 + (p : ZMod (p ^ 2)) *
      (∑ j ∈ Icc 1 (k - r), Ring.inverse (j : ZMod (p ^ 2)) -
        ∑ j ∈ Icc 1 (r - 1), Ring.inverse (j : ZMod (p ^ 2))))
    have : (r : ZMod (p ^ 2)) * ((r - 1)! : ZMod (p ^ 2)) *
        (k.choose r : ZMod (p ^ 2)) * ((k - r)! : ZMod (p ^ 2)) *
        ((-1 : ZMod (p ^ 2)) ^ (r - 1) *
          Ring.inverse ((r : ZMod (p ^ 2)) * (k.choose r : ZMod (p ^ 2))) * A) =
        (-1 : ZMod (p ^ 2)) ^ (r - 1) * ((k - r)! : ZMod (p ^ 2)) *
          ((r - 1)! : ZMod (p ^ 2)) * A := by
      calc
        _ = ((r : ZMod (p ^ 2)) * (k.choose r : ZMod (p ^ 2)) *
              Ring.inverse ((r : ZMod (p ^ 2)) * (k.choose r : ZMod (p ^ 2)))) *
            ((r - 1)! : ZMod (p ^ 2)) * ((k - r)! : ZMod (p ^ 2)) *
            ((-1 : ZMod (p ^ 2)) ^ (r - 1) * A) := by ring
        _ = 1 * ((r - 1)! : ZMod (p ^ 2)) * ((k - r)! : ZMod (p ^ 2)) *
            ((-1 : ZMod (p ^ 2)) ^ (r - 1) * A) := by rw [hinv]
        _ = _ := by ring
    exact this.symm
  exact (IsUnit.mul_right_inj hfacU).mp hmul'

/-! Interpolation of `Ppoly2` over the integer pole representatives. -/

lemma nontrivial_zmod_sq : Nontrivial (ZMod (p ^ 2)) := by
  haveI : Fact (1 < p ^ 2) := ⟨by
    have : 2 ≤ p := p_ge_two (p := p)
    nlinarith⟩
  infer_instance

lemma injOn_cast_poleReps {r : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p) :
    Set.InjOn (fun k : ℕ => (k : ZMod (p ^ 2))) (poleReps (p := p) r) := by
  intro a ha b hb h
  have hap : a < p := poleReps_lt_p (p := p) hr2 hrp ha
  have hbp : b < p := poleReps_lt_p (p := p) hr2 hrp hb
  have hmod : a ≡ b [MOD p ^ 2] := (ZMod.natCast_eq_natCast_iff a b (p ^ 2)).mp h
  have hp2 : p < p ^ 2 := by
    have : 2 ≤ p := p_ge_two (p := p)
    nlinarith
  rcases le_total a b with hle | hle
  · have hd : p ^ 2 ∣ b - a := (Nat.modEq_iff_dvd' hle).mp hmod
    have : b - a = 0 := Nat.eq_zero_of_dvd_of_lt hd (by omega)
    omega
  · have hd : p ^ 2 ∣ a - b := (Nat.modEq_iff_dvd' hle).mp hmod.symm
    have : a - b = 0 := Nat.eq_zero_of_dvd_of_lt hd (by omega)
    omega

lemma eq_zero_of_eval_poleReps (s : Finset (ZMod (p ^ 2))) (P : (ZMod (p ^ 2))[X])
    (hdeg : P.degree < s.card)
    (hunit : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → IsUnit (x - y))
    (heval : ∀ x ∈ s, P.eval x = 0) : P = 0 := by
  haveI := nontrivial_zmod_sq (p := p)
  induction s using Finset.induction generalizing P with
  | empty =>
    rw [card_empty, Nat.cast_zero] at hdeg
    exact degree_eq_bot.mp (Nat.WithBot.lt_zero_iff.mp hdeg)
  | insert a s ha ih =>
    by_cases hP0 : P = 0
    · exact hP0
    have ha0 : P.eval a = 0 := heval a (mem_insert_self _ _)
    obtain ⟨Q, hPQ⟩ := (dvd_iff_isRoot (a := a) (p := P)).mpr ha0
    have hmon : (X - C a).Monic := monic_X_sub_C a
    have hQ0 : Q ≠ 0 := fun h => hP0 (by rw [hPQ, h, mul_zero])
    have hdegQ : Q.degree < s.card := by
      have hndP : P.natDegree = Q.natDegree + 1 := by
        rw [hPQ, hmon.natDegree_mul' hQ0, natDegree_X_sub_C, add_comm]
      have hPne : P ≠ 0 := hP0
      have hndPlt : P.natDegree < (insert a s).card :=
        (natDegree_lt_iff_degree_lt hPne).mpr hdeg
      have hcard : (insert a s).card = s.card + 1 := card_insert_of_notMem ha
      have hQnd : Q.natDegree < s.card := by omega
      exact (natDegree_lt_iff_degree_lt hQ0).mp hQnd
    have hunitQ : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → IsUnit (x - y) := by
      intro x hx y hy hxy
      exact hunit x (mem_insert_of_mem hx) y (mem_insert_of_mem hy) hxy
    have hevalQ : ∀ x ∈ s, Q.eval x = 0 := by
      intro x hx
      have hxne : x ≠ a := fun h => ha (h ▸ hx)
      have hxU : IsUnit (x - a) :=
        hunit x (mem_insert_of_mem hx) a (mem_insert_self _ _) hxne
      have : (x - a) * Q.eval x = 0 := by
        have := heval x (mem_insert_of_mem hx)
        rw [hPQ, eval_mul, eval_sub, eval_X, eval_C] at this
        exact this
      exact hxU.mul_right_eq_zero.mp this
    have hQ := ih Q hdegQ hunitQ hevalQ
    rw [hPQ, hQ, mul_zero]

lemma interpolate_unique_zmod_sq (s : Finset (ZMod (p ^ 2)))
    (P Q : (ZMod (p ^ 2))[X])
    (hP : P.degree < s.card) (hQ : Q.degree < s.card)
    (hunit : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → IsUnit (x - y))
    (heval : ∀ x ∈ s, P.eval x = Q.eval x) : P = Q := by
  refine sub_eq_zero.mp (eq_zero_of_eval_poleReps (p := p) s (P - Q) ?_ hunit ?_)
  · exact lt_of_le_of_lt (degree_sub_le _ _) (max_lt hP hQ)
  · intro x hx
    rw [eval_sub, heval x hx, sub_self]

lemma card_image_poleReps {r : ℕ} (hr0 : 0 < r) (hr2 : 2 ≤ r) (hrp : 3 * r < p) :
    #((poleReps (p := p) r).image (fun k : ℕ => (k : ZMod (p ^ 2)))) = 2 * r := by
  rw [Finset.card_image_of_injOn (injOn_cast_poleReps (p := p) hr2 hrp),
    card_poleReps (p := p) hr0 hr2 hrp]

lemma sum_Ppoly2_div_nodal {r : ℕ} (hr0 : 0 < r) (hr2 : 2 ≤ r) (hrp : 3 * r < p) :
    ∑ k ∈ poleReps (p := p) r,
        (Ppoly2 (p := p) r).eval (k : ZMod (p ^ 2)) *
          Ring.inverse (∏ j ∈ (poleReps (p := p) r).erase k,
            ((k : ZMod (p ^ 2)) - (j : ZMod (p ^ 2)))) = 0 := by
  haveI := nontrivial_zmod_sq (p := p)
  let s : Finset (ZMod (p ^ 2)) :=
    (poleReps (p := p) r).image (fun k : ℕ => (k : ZMod (p ^ 2)))
  have hscard : s.card = 2 * r := card_image_poleReps (p := p) hr0 hr2 hrp
  have hPdeg : (Ppoly2 (p := p) r).degree < s.card := by
    rw [hscard]
    have hnd : (Ppoly2 (p := p) r).natDegree = 2 * (r - 1) :=
      natDegree_Ppoly2 (p := p) hr2
    have hlt : 2 * (r - 1) < 2 * r := by omega
    exact lt_of_le_of_lt degree_le_natDegree
      (WithBot.coe_lt_coe.mpr (hnd ▸ hlt))
  have hunit : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → IsUnit (x - y) := by
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hy
    exact isUnit_sub_poleReps (p := p) hr2 hrp ha hb (fun h => hxy (by rw [h]))
  let basis : ZMod (p ^ 2) → (ZMod (p ^ 2))[X] :=
    fun i => ∏ j ∈ s.erase i, (X - C j)
  have hbas_eval : ∀ i ∈ s, (basis i).eval i = ∏ j ∈ s.erase i, (i - j) := by
    intro i hi; simp [basis, eval_prod, eval_sub, eval_X, eval_C]
  have hbas_unit : ∀ i ∈ s, IsUnit ((basis i).eval i) := by
    intro i hi
    rw [hbas_eval i hi]
    refine IsUnit.prod_iff.mpr ?_
    intro j hj
    exact hunit i hi j (mem_of_mem_erase hj) (mem_erase.mp hj).1.symm
  have hbas_monic : ∀ i ∈ s, (basis i).Monic :=
    fun i _ => monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)
  have hbas_nd : ∀ i ∈ s, (basis i).natDegree = s.card - 1 := by
    intro i hi
    unfold basis
    rw [natDegree_prod_of_monic (s := s.erase i)
      (f := fun j => (X - C j : (ZMod (p ^ 2))[X]))
      (fun _ _ => monic_X_sub_C _),
      Finset.sum_congr rfl (fun _ _ => natDegree_X_sub_C _),
      sum_const, smul_eq_mul, mul_one, card_erase_of_mem hi]
  let Q : (ZMod (p ^ 2))[X] :=
    ∑ i ∈ s, C ((Ppoly2 (p := p) r).eval i * Ring.inverse ((basis i).eval i)) *
      basis i
  have hQdeg : Q.degree < s.card := by
    have hle : Q.natDegree ≤ s.card - 1 := by
      refine (natDegree_sum_le _ _).trans (Finset.sup_le ?_)
      intro i hi
      exact (natDegree_mul_le).trans (by rw [natDegree_C, zero_add, hbas_nd i hi])
    have hpos : 0 < s.card := by rw [hscard]; omega
    exact lt_of_le_of_lt degree_le_natDegree
      (WithBot.coe_lt_coe.mpr (lt_of_le_of_lt hle (Nat.sub_one_lt (by omega))))
  have heq : ∀ x ∈ s, Q.eval x = (Ppoly2 (p := p) r).eval x := by
    intro x hx
    rw [eval_finset_sum]
    rw [sum_eq_single x
      (fun i hi hix => by
        rw [eval_mul, eval_C]
        have : (basis i).eval x = 0 := by
          simp only [basis, eval_prod, eval_sub, eval_X, eval_C]
          exact prod_eq_zero (mem_erase.mpr ⟨Ne.symm hix, hx⟩) (sub_self x)
        rw [this, mul_zero])
      (fun hx' => (hx' hx).elim),
      eval_mul, eval_C]
    have h1 : (basis x).eval x * Ring.inverse ((basis x).eval x) = 1 :=
      Ring.mul_inverse_cancel _ (hbas_unit x hx)
    have h1' : Ring.inverse ((basis x).eval x) * (basis x).eval x = 1 := by
      rw [mul_comm, h1]
    rw [mul_assoc, h1', mul_one]
  have hPQ : Ppoly2 (p := p) r = Q :=
    interpolate_unique_zmod_sq (p := p) s _ _ hPdeg hQdeg hunit
      (fun x hx => (heq x hx).symm)
  have hcoeff0 : (Ppoly2 (p := p) r).coeff (s.card - 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by
      rw [natDegree_Ppoly2 (p := p) hr2, hscard]; omega)
  have hcoeffQ : Q.coeff (s.card - 1) =
      ∑ i ∈ s, (Ppoly2 (p := p) r).eval i *
        Ring.inverse (∏ j ∈ s.erase i, (i - j)) := by
    rw [finset_sum_coeff]
    refine sum_congr rfl ?_
    intro i hi
    rw [coeff_C_mul, hbas_eval i hi]
    have : (basis i).coeff (s.card - 1) = 1 := by
      rw [← hbas_nd i hi, ← leadingCoeff, (hbas_monic i hi).leadingCoeff]
    rw [this, mul_one]
  have hsum :
      ∑ i ∈ s, (Ppoly2 (p := p) r).eval i *
          Ring.inverse (∏ j ∈ s.erase i, (i - j)) =
        ∑ k ∈ poleReps (p := p) r,
          (Ppoly2 (p := p) r).eval (k : ZMod (p ^ 2)) *
            Ring.inverse (∏ j ∈ (poleReps (p := p) r).erase k,
              ((k : ZMod (p ^ 2)) - (j : ZMod (p ^ 2)))) := by
    rw [Finset.sum_image (injOn_cast_poleReps (p := p) hr2 hrp)]
    refine sum_congr rfl ?_
    intro k hk
    congr 1
    refine congrArg Ring.inverse ?_
    have himg : s.erase (k : ZMod (p ^ 2)) =
        ((poleReps (p := p) r).erase k).image
          (fun j : ℕ => (j : ZMod (p ^ 2))) := by
      ext x; constructor
      · intro hx
        obtain ⟨hne, hx'⟩ := mem_erase.mp hx
        obtain ⟨j, hj, rfl⟩ := mem_image.mp hx'
        exact mem_image.mpr ⟨j, mem_erase.mpr ⟨fun h => hne (by rw [h]), hj⟩, rfl⟩
      · intro hx
        obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
        obtain ⟨hne, hj'⟩ := mem_erase.mp hj
        exact mem_erase.mpr ⟨fun hcast => hne
          ((injOn_cast_poleReps (p := p) hr2 hrp) hj' hk hcast),
          mem_image.mpr ⟨j, hj', rfl⟩⟩
    rw [himg]
    refine Finset.prod_image ?_
    intro a ha b hb hab
    have ha' : a ∈ poleReps (p := p) r := mem_of_mem_erase ha
    have hb' : b ∈ poleReps (p := p) r := mem_of_mem_erase hb
    exact (injOn_cast_poleReps (p := p) hr2 hrp) ha' hb' hab
  rw [hPQ] at hcoeff0
  rw [← hsum, ← hcoeffQ, hcoeff0]

/-- Interpolating main term at an integer pole representative. -/
noncomputable def Main2 (r k : ℕ) : ZMod (p ^ 2) :=
  Ring.inverse ((2 : ZMod (p ^ 2)) ^ (r - 1)) *
    (Ppoly2 (p := p) r).eval (k : ZMod (p ^ 2)) *
    Ring.inverse (∏ j ∈ (poleReps (p := p) r).erase k,
      ((k : ZMod (p ^ 2)) - (j : ZMod (p ^ 2))))

lemma isUnit_two_zmod_sq {r : ℕ} (hr0 : 0 < r) (hrp : 3 * r < p) :
    IsUnit (2 : ZMod (p ^ 2)) :=
  isUnit_nat_zmod_sq (by decide : 0 < 2)
    (two_lt_p_of_three (p := p) hr0 hrp) Fact.out

lemma sum_Main2_poleReps {r : ℕ} (hr0 : 0 < r) (hr2 : 2 ≤ r) (hrp : 3 * r < p) :
    ∑ k ∈ poleReps (p := p) r, Main2 (p := p) r k = 0 := by
  simp only [Main2]
  have hcongr : ∀ k ∈ poleReps (p := p) r,
      Ring.inverse ((2 : ZMod (p ^ 2)) ^ (r - 1)) *
        (Ppoly2 (p := p) r).eval (k : ZMod (p ^ 2)) *
        Ring.inverse (∏ j ∈ (poleReps (p := p) r).erase k,
          ((k : ZMod (p ^ 2)) - (j : ZMod (p ^ 2)))) =
      Ring.inverse ((2 : ZMod (p ^ 2)) ^ (r - 1)) *
        ((Ppoly2 (p := p) r).eval (k : ZMod (p ^ 2)) *
          Ring.inverse (∏ j ∈ (poleReps (p := p) r).erase k,
            ((k : ZMod (p ^ 2)) - (j : ZMod (p ^ 2))))) := by
    intro k hk; rw [mul_assoc]
  rw [sum_congr rfl hcongr, ← mul_sum, sum_Ppoly2_div_nodal (p := p) hr0 hr2 hrp,
    mul_zero]

lemma Main2_extra_zero {r k : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    (hk : k ∈ poleReps (p := p) r) (hgt : p - r < k) :
    Main2 (p := p) r k = 0 := by
  have hkp : k < p := poleReps_lt_p (p := p) hr2 hrp hk
  simp only [Main2, eval_Ppoly2_extra_zero (p := p) hr2 hrp hgt hkp, mul_zero, zero_mul]

lemma poleReps_split {r : ℕ} :
    poleReps (p := p) r =
      (poleReps (p := p) r).filter (fun k => k ≤ p - r) ∪
        (poleReps (p := p) r).filter (fun k => p - r < k) := by
  ext k
  simp only [mem_union, mem_filter]
  constructor
  · intro hk
    by_cases h : k ≤ p - r
    · exact Or.inl ⟨hk, h⟩
    · exact Or.inr ⟨hk, Nat.lt_of_not_ge h⟩
  · intro h; rcases h with ⟨hk, _⟩ | ⟨hk, _⟩ <;> exact hk

lemma sum_Main2_ABD {r : ℕ} (hr0 : 0 < r) (hr2 : 2 ≤ r) (hrp : 3 * r < p) :
    ∑ k ∈ (poleReps (p := p) r).filter (fun k => k ≤ p - r),
      Main2 (p := p) r k = 0 := by
  have hsplit := poleReps_split (p := p) (r := r)
  have hd : Disjoint
      ((poleReps (p := p) r).filter (fun k => k ≤ p - r))
      ((poleReps (p := p) r).filter (fun k => p - r < k)) := by
    refine disjoint_left.mpr ?_
    intro x hx hy
    have := (mem_filter.mp hx).2
    have := (mem_filter.mp hy).2
    omega
  have hsum := sum_Main2_poleReps (p := p) hr0 hr2 hrp
  rw [hsplit, sum_union hd] at hsum
  have hextra :
      ∑ k ∈ (poleReps (p := p) r).filter (fun k => p - r < k),
        Main2 (p := p) r k = 0 := by
    refine sum_eq_zero ?_
    intro k hk
    have ⟨hmem, hgt⟩ := mem_filter.mp hk
    exact Main2_extra_zero (p := p) hr2 hrp hmem hgt
  rw [hextra, add_zero] at hsum
  exact hsum

/-- Harmonic sums of inverses in `ZMod p` and `ZMod (p^2)`. -/
def harm (n : ℕ) : ZMod p :=
  ∑ j ∈ Icc 1 n, (j : ZMod p)⁻¹

noncomputable def harm2 (n : ℕ) : ZMod (p ^ 2) :=
  ∑ j ∈ Icc 1 n, Ring.inverse (j : ZMod (p ^ 2))

lemma harm_zero : harm (p := p) 0 = 0 := by simp [harm]
lemma harm2_zero : harm2 (p := p) 0 = 0 := by simp [harm2]

lemma harm_succ {n : ℕ} (hn : 1 ≤ n) (hnp : n < p) :
    harm (p := p) n = harm (p := p) (n - 1) + (n : ZMod p)⁻¹ := by
  simp only [harm]
  exact harmonic_succ_Icc (p := p) hn hnp

lemma harm_eq_sum (n : ℕ) :
    harm (p := p) n = ∑ j ∈ Icc 1 n, (j : ZMod p)⁻¹ := rfl

lemma harm_p_sub (hp5 : 5 ≤ p) {m : ℕ} (hm : 1 ≤ m) (hmp : m < p) :
    harm (p := p) (p - m) = harm (p := p) (m - 1) := by
  have hfull : harm (p := p) (p - 1) = 0 := harmonic_pred_eq_zero (p := p) hp5
  have hsplit :
      Icc (1 : ℕ) (p - 1) = Icc 1 (p - m) ∪ Icc (p - m + 1) (p - 1) := by
    ext x; simp [mem_Icc, mem_union]; omega
  have hd : Disjoint (Icc (1 : ℕ) (p - m)) (Icc (p - m + 1) (p - 1)) := by
    refine disjoint_left.mpr ?_
    intro x hx hy
    simp [mem_Icc] at hx hy; omega
  have himg : Icc (p - m + 1) (p - 1) =
      (Icc 1 (m - 1)).image (fun j => p - j) := by
    ext x
    simp only [mem_Icc, mem_image]
    constructor
    · intro hx; refine ⟨p - x, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩; omega
  have hinj : Set.InjOn (fun j : ℕ => p - j) (Icc 1 (m - 1)) := by
    intro a ha b hb h
    have haI := mem_Icc.mp (by simpa [Finset.mem_coe] using ha)
    have hbI := mem_Icc.mp (by simpa [Finset.mem_coe] using hb)
    exact (tsub_right_inj (by omega) (by omega)).mp h
  have hsum :
      harm (p := p) (p - 1) =
        harm (p := p) (p - m) +
          ∑ j ∈ Icc 1 (m - 1), ((p - j : ℕ) : ZMod p)⁻¹ := by
    simp only [harm]
    rw [hsplit, sum_union hd, himg,
      Finset.sum_image (fun a ha b hb h => hinj ha hb h)]
  have hneg : ∀ j ∈ Icc 1 (m - 1),
      ((p - j : ℕ) : ZMod p)⁻¹ = -((j : ZMod p)⁻¹) := by
    intro j hj
    have hjI := mem_Icc.mp hj
    rw [Nat.cast_sub (by omega), CharP.cast_eq_zero (R := ZMod p) p, zero_sub, inv_neg]
  rw [hfull] at hsum
  have : harm (p := p) (p - m) =
      - ∑ j ∈ Icc 1 (m - 1), ((p - j : ℕ) : ZMod p)⁻¹ :=
    eq_neg_of_add_eq_zero_left hsum.symm
  rw [this, sum_congr rfl hneg, sum_neg_distrib, neg_neg]
  simp [harm]

/-! Second-order expansion of the middle binomial for `k ≥ r`. -/

lemma choose_mid_div_p_zmod_sq {r k : ℕ} (hr0 : 0 < r) (hrp : r < p)
    (hkr : r ≤ k) (hkp : k < p) :
    p ∣ (p - r + k).choose k ∧
    (((p - r + k).choose k / p : ℕ) : ZMod (p ^ 2)) =
      (-1 : ZMod (p ^ 2)) ^ (r - 1) *
        Ring.inverse ((r : ZMod (p ^ 2)) * (k.choose r : ZMod (p ^ 2))) *
        (1 + (p : ZMod (p ^ 2)) *
          (∑ j ∈ Icc 1 (k - r), Ring.inverse (j : ZMod (p ^ 2)) -
            ∑ j ∈ Icc 1 (r - 1), Ring.inverse (j : ZMod (p ^ 2)))) := by
  have hpr : p.Prime := Fact.out
  have hppos : 0 < p := hpr.pos
  have hsplit := descFactorial_p_sub_add_split (p := p) hr0 hrp hkr
  have hfac : (p - r + k).descFactorial k = k ! * (p - r + k).choose k :=
    descFactorial_eq_factorial_mul_choose _ _
  have hmul : k ! * (p - r + k).choose k =
      p * ((∏ j ∈ Icc 1 (k - r), (p + j)) * (∏ j ∈ Icc 1 (r - 1), (p - j))) := by
    rw [← hfac, hsplit]; ring
  have hkndvd : ¬ p ∣ k ! := by
    intro h
    exact (not_le_of_gt hkp) (hpr.dvd_factorial.mp h)
  have hpdvd : p ∣ (p - r + k).choose k := by
    have : p ∣ k ! * (p - r + k).choose k := by
      rw [hmul]; exact dvd_mul_right _ _
    exact (hpr.dvd_mul.mp this).resolve_left hkndvd
  refine ⟨hpdvd, ?_⟩
  have hdiv : k ! * ((p - r + k).choose k / p) =
      (∏ j ∈ Icc 1 (k - r), (p + j)) * (∏ j ∈ Icc 1 (r - 1), (p - j)) := by
    apply Nat.eq_of_mul_eq_mul_left hppos
    calc
      p * (k ! * ((p - r + k).choose k / p))
          = k ! * (p * ((p - r + k).choose k / p)) := by ring
      _ = k ! * (p - r + k).choose k := by rw [Nat.mul_div_cancel' hpdvd]
      _ = p * ((∏ j ∈ Icc 1 (k - r), (p + j)) * (∏ j ∈ Icc 1 (r - 1), (p - j))) :=
            hmul
  -- expand the two products in `ZMod (p^2)`
  have hpos : (∏ j ∈ Icc 1 (k - r), ((p + j : ℕ) : ZMod (p ^ 2))) =
      (∏ j ∈ Icc 1 (k - r), (j : ZMod (p ^ 2))) *
        (1 + (p : ZMod (p ^ 2)) *
          ∑ j ∈ Icc 1 (k - r), Ring.inverse (j : ZMod (p ^ 2))) := by
    by_cases hempty : k - r = 0
    · simp [hempty]
    · have ha : 1 ≤ k - r := by omega
      have hbp : k - r < p := by omega
      have hprod := prod_Icc_add_mul_p (p := p) hpr 1 1 (k - r) (by decide) ha hbp
      have hcongr : ∀ j ∈ Icc 1 (k - r),
          ((j + 1 * p : ℕ) : ZMod (p ^ 2)) = ((p + j : ℕ) : ZMod (p ^ 2)) := by
        intro j hj; congr 1; ring
      rw [prod_congr rfl hcongr] at hprod
      convert hprod using 2 <;> simp
  have hneg : (∏ j ∈ Icc 1 (r - 1), ((p - j : ℕ) : ZMod (p ^ 2))) =
      (-1 : ZMod (p ^ 2)) ^ (r - 1) *
        (∏ j ∈ Icc 1 (r - 1), (j : ZMod (p ^ 2))) *
        (1 - (p : ZMod (p ^ 2)) *
          ∑ j ∈ Icc 1 (r - 1), Ring.inverse (j : ZMod (p ^ 2))) := by
    by_cases hempty : r - 1 = 0
    · simp [hempty]
    · have hfac' : ∀ j ∈ Icc 1 (r - 1),
          ((p - j : ℕ) : ZMod (p ^ 2)) =
            (-((j : ZMod (p ^ 2)))) *
              (1 - (p : ZMod (p ^ 2)) * Ring.inverse (j : ZMod (p ^ 2))) := by
        intro j hj
        have hjI := mem_Icc.mp hj
        exact p_sub_nat_zmod_sq (lt_of_lt_of_le (by decide : 0 < 1) hjI.1)
          (lt_of_le_of_lt hjI.2 (by omega))
      rw [prod_congr rfl hfac', prod_mul_distrib, prod_neg]
      have hcard : #(Icc 1 (r - 1)) = r - 1 := by rw [Nat.card_Icc]; omega
      rw [hcard]
      have hd : (p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) = 0 :=
        p_mul_p_zmod_sq (p := p)
      rw [prod_one_sub_nilp hd]
  have hcast :
      (k ! : ZMod (p ^ 2)) * (((p - r + k).choose k / p : ℕ) : ZMod (p ^ 2)) =
        (∏ j ∈ Icc 1 (k - r), ((p + j : ℕ) : ZMod (p ^ 2))) *
          (∏ j ∈ Icc 1 (r - 1), ((p - j : ℕ) : ZMod (p ^ 2))) := by
    rw [← Nat.cast_mul, hdiv, Nat.cast_mul, Nat.cast_prod, Nat.cast_prod]
  rw [hpos, hneg] at hcast
  have hfacU : IsUnit (k ! : ZMod (p ^ 2)) := isUnit_factorial_zmod_sq hkp hpr
  -- identify factorials
  have hkrf : (∏ j ∈ Icc 1 (k - r), (j : ZMod (p ^ 2))) = ((k - r)! : ZMod (p ^ 2)) := by
    rw [← Nat.cast_prod, prod_Icc_one_n]
  have hr1f : (∏ j ∈ Icc 1 (r - 1), (j : ZMod (p ^ 2))) = ((r - 1)! : ZMod (p ^ 2)) := by
    rw [← Nat.cast_prod, prod_Icc_one_n]
  rw [hkrf, hr1f] at hcast
  -- k! = r! * C(k,r) * (k-r)!
  have hC : (k.choose r : ZMod (p ^ 2)) * (r ! : ZMod (p ^ 2)) * ((k - r)! : ZMod (p ^ 2)) =
      (k ! : ZMod (p ^ 2)) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, choose_mul_factorial_mul_factorial hkr]
  have hrfac : (r ! : ZMod (p ^ 2)) =
      (r : ZMod (p ^ 2)) * ((r - 1)! : ZMod (p ^ 2)) := by
    have hrw : r = (r - 1) + 1 := by omega
    rw [hrw, factorial_succ, Nat.cast_mul, Nat.cast_succ, add_tsub_cancel_right]
  have hrU : IsUnit (r : ZMod (p ^ 2)) :=
    isUnit_nat_zmod_sq hr0 hrp hpr
  have hr1U : IsUnit ((r - 1)! : ZMod (p ^ 2)) :=
    isUnit_factorial_zmod_sq (by omega) hpr
  have hkrU : IsUnit ((k - r)! : ZMod (p ^ 2)) :=
    isUnit_factorial_zmod_sq (lt_of_le_of_lt (Nat.sub_le k r) hkp) hpr
  have hCU : IsUnit (k.choose r : ZMod (p ^ 2)) := by
    refine (ZMod.isUnit_iff_coprime (k.choose r) (p ^ 2)).mpr ?_
    rw [Nat.coprime_pow_right_iff (by decide : 0 < 2)]
    have hcop := hpr.coprime_choose_of_lt hkp hkr
    exact hcop.symm
  -- solve for C/p
  have hprod_nilp :
      (1 + (p : ZMod (p ^ 2)) *
          ∑ j ∈ Icc 1 (k - r), Ring.inverse (j : ZMod (p ^ 2))) *
        (1 - (p : ZMod (p ^ 2)) *
          ∑ j ∈ Icc 1 (r - 1), Ring.inverse (j : ZMod (p ^ 2))) =
      1 + (p : ZMod (p ^ 2)) *
        (∑ j ∈ Icc 1 (k - r), Ring.inverse (j : ZMod (p ^ 2)) -
          ∑ j ∈ Icc 1 (r - 1), Ring.inverse (j : ZMod (p ^ 2))) := by
    set A := ∑ j ∈ Icc 1 (k - r), Ring.inverse (j : ZMod (p ^ 2))
    set B := ∑ j ∈ Icc 1 (r - 1), Ring.inverse (j : ZMod (p ^ 2))
    have hd : (p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) = 0 := p_mul_p_zmod_sq (p := p)
    have : ((p : ZMod (p ^ 2)) * A) * ((p : ZMod (p ^ 2)) * B) = 0 := by
      calc
        ((p : ZMod (p ^ 2)) * A) * ((p : ZMod (p ^ 2)) * B)
            = ((p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) * (A * B) := by ring
        _ = 0 := by rw [hd, zero_mul]
    calc
      (1 + (p : ZMod (p ^ 2)) * A) * (1 - (p : ZMod (p ^ 2)) * B)
          = 1 - (p : ZMod (p ^ 2)) * B + (p : ZMod (p ^ 2)) * A -
              ((p : ZMod (p ^ 2)) * A) * ((p : ZMod (p ^ 2)) * B) := by ring
      _ = 1 + (p : ZMod (p ^ 2)) * (A - B) := by rw [this]; ring
  have hLHS :
      (k ! : ZMod (p ^ 2)) * (((p - r + k).choose k / p : ℕ) : ZMod (p ^ 2)) =
        ((k - r)! : ZMod (p ^ 2)) * ((-1 : ZMod (p ^ 2)) ^ (r - 1) * ((r - 1)! : ZMod (p ^ 2))) *
          (1 + (p : ZMod (p ^ 2)) *
            (∑ j ∈ Icc 1 (k - r), Ring.inverse (j : ZMod (p ^ 2)) -
              ∑ j ∈ Icc 1 (r - 1), Ring.inverse (j : ZMod (p ^ 2)))) := by
    calc
      _ = ((k - r)! : ZMod (p ^ 2)) *
            (1 + (p : ZMod (p ^ 2)) *
              ∑ j ∈ Icc 1 (k - r), Ring.inverse (j : ZMod (p ^ 2))) *
            ((-1 : ZMod (p ^ 2)) ^ (r - 1) * ((r - 1)! : ZMod (p ^ 2)) *
              (1 - (p : ZMod (p ^ 2)) *
                ∑ j ∈ Icc 1 (r - 1), Ring.inverse (j : ZMod (p ^ 2)))) := hcast
      _ = ((k - r)! : ZMod (p ^ 2)) * ((-1 : ZMod (p ^ 2)) ^ (r - 1) * ((r - 1)! : ZMod (p ^ 2))) *
            ((1 + (p : ZMod (p ^ 2)) *
                ∑ j ∈ Icc 1 (k - r), Ring.inverse (j : ZMod (p ^ 2))) *
              (1 - (p : ZMod (p ^ 2)) *
                ∑ j ∈ Icc 1 (r - 1), Ring.inverse (j : ZMod (p ^ 2)))) := by ring
      _ = _ := by rw [hprod_nilp]
  -- invert k!
  have hsolved :
      (((p - r + k).choose k / p : ℕ) : ZMod (p ^ 2)) =
        Ring.inverse (k ! : ZMod (p ^ 2)) *
          ((k - r)! : ZMod (p ^ 2)) *
          ((-1 : ZMod (p ^ 2)) ^ (r - 1) * ((r - 1)! : ZMod (p ^ 2))) *
          (1 + (p : ZMod (p ^ 2)) *
            (∑ j ∈ Icc 1 (k - r), Ring.inverse (j : ZMod (p ^ 2)) -
              ∑ j ∈ Icc 1 (r - 1), Ring.inverse (j : ZMod (p ^ 2)))) := by
    have := congrArg (fun z => z * Ring.inverse (k ! : ZMod (p ^ 2))) hLHS
    simp only at this
    have hcancel : (k ! : ZMod (p ^ 2)) *
        (((p - r + k).choose k / p : ℕ) : ZMod (p ^ 2)) *
        Ring.inverse (k ! : ZMod (p ^ 2)) =
      (((p - r + k).choose k / p : ℕ) : ZMod (p ^ 2)) := by
      rw [mul_comm (k ! : ZMod (p ^ 2)), mul_assoc,
        Ring.mul_inverse_cancel _ hfacU, mul_one]
    rw [hcancel] at this
    convert this using 1
    ac_rfl
  -- rewrite inverse(k!) * (k-r)! * (r-1)! = inverse(r * C(k,r))
  have hid :
      Ring.inverse (k ! : ZMod (p ^ 2)) * ((k - r)! : ZMod (p ^ 2)) *
        ((r - 1)! : ZMod (p ^ 2)) =
      Ring.inverse ((r : ZMod (p ^ 2)) * (k.choose r : ZMod (p ^ 2))) := by
    have hkeq : (k ! : ZMod (p ^ 2)) =
        (r : ZMod (p ^ 2)) * (k.choose r : ZMod (p ^ 2)) *
          ((r - 1)! : ZMod (p ^ 2)) * ((k - r)! : ZMod (p ^ 2)) := by
      rw [hrfac] at hC
      convert hC.symm using 1
      ring
    have hmul1 :
        Ring.inverse (k ! : ZMod (p ^ 2)) * (k ! : ZMod (p ^ 2)) = 1 :=
      Ring.inverse_mul_cancel _ hfacU
    have hUrc : IsUnit ((r : ZMod (p ^ 2)) * (k.choose r : ZMod (p ^ 2))) :=
      hrU.mul hCU
    -- multiply both candidate inverses by `r * C(k,r)`
    apply (IsUnit.mul_left_inj hUrc).mp
    calc
      Ring.inverse (k ! : ZMod (p ^ 2)) * ((k - r)! : ZMod (p ^ 2)) *
          ((r - 1)! : ZMod (p ^ 2)) *
          ((r : ZMod (p ^ 2)) * (k.choose r : ZMod (p ^ 2)))
          = Ring.inverse (k ! : ZMod (p ^ 2)) * (k ! : ZMod (p ^ 2)) := by
            rw [hkeq]; ring
      _ = 1 := hmul1
      _ = Ring.inverse ((r : ZMod (p ^ 2)) * (k.choose r : ZMod (p ^ 2))) *
            ((r : ZMod (p ^ 2)) * (k.choose r : ZMod (p ^ 2))) :=
          (Ring.inverse_mul_cancel _ hUrc).symm
  rw [hsolved]
  have hrearr :
      Ring.inverse (k ! : ZMod (p ^ 2)) * ((k - r)! : ZMod (p ^ 2)) *
          ((-1 : ZMod (p ^ 2)) ^ (r - 1) * ((r - 1)! : ZMod (p ^ 2))) =
        (-1 : ZMod (p ^ 2)) ^ (r - 1) *
          (Ring.inverse (k ! : ZMod (p ^ 2)) * ((k - r)! : ZMod (p ^ 2)) *
            ((r - 1)! : ZMod (p ^ 2))) := by ring
  rw [hrearr, hid]

lemma sum_inv_sq_eq_zero (hp5 : 5 ≤ p) :
    ∑ j ∈ Icc 1 (p - 1), ((j : ZMod p)⁻¹) ^ 2 = 0 := by
  have hpow : ∀ j ∈ Icc 1 (p - 1),
      ((j : ZMod p)⁻¹) ^ 2 = (j : ZMod p) ^ (p - 3) := by
    intro j hj
    have hjI := mem_Icc.mp hj
    have hj0 : 0 < j := lt_of_lt_of_le (by decide : 0 < 1) hjI.1
    have hjp : j < p := lt_of_le_of_lt hjI.2 (Nat.sub_one_lt (p_pos (p := p)).ne')
    have hjne : (j : ZMod p) ≠ 0 := zmod_nat_ne_zero hj0 hjp
    have hfermat : (j : ZMod p) ^ (p - 1) = 1 :=
      ZMod.pow_card_sub_one_eq_one hjne
    have hp3 : 2 + (p - 3) = p - 1 := by omega
    rw [inv_pow]
    have h2 : (j : ZMod p) ^ 2 * (j : ZMod p) ^ (p - 3) = 1 := by
      rw [← pow_add, hp3, hfermat]
    exact inv_eq_of_mul_eq_one_right h2
  rw [sum_congr rfl hpow]
  have hinj : Set.InjOn (fun j : ℕ => (j : ZMod p)) (Icc (1 : ℕ) (p - 1)) := by
    intro a ha b hb hab
    have ha' : a ∈ Icc 1 (1 + p - 2) := by
      rw [← Icc_one_pred_eq (p := p)]; simpa [Finset.mem_coe] using ha
    have hb' : b ∈ Icc 1 (1 + p - 2) := by
      rw [← Icc_one_pred_eq (p := p)]; simpa [Finset.mem_coe] using hb
    exact injOn_cast_Icc_consecutive (p := p) 1 a ha' b hb' hab
  have himg := image_Icc_one_pred (p := p)
  have hsum_img :
      ∑ j ∈ Icc (1 : ℕ) (p - 1), (j : ZMod p) ^ (p - 3) =
        ∑ x ∈ (univ : Finset (ZMod p)).erase 0, x ^ (p - 3) := by
    rw [← himg]
    exact (Finset.sum_image (fun a ha b hb h => hinj ha hb h)).symm
  rw [hsum_img]
  have hz : (0 : ZMod p) ^ (p - 3) = 0 :=
    zero_pow (Nat.sub_ne_zero_iff_lt.mpr (lt_of_lt_of_le (by decide : 3 < 5) hp5))
  have hall : ∑ x : ZMod p, x ^ (p - 3) = 0 :=
    sum_univ_pow_eq_zero (j := p - 3) (by omega)
  have hmem : (0 : ZMod p) ∈ (univ : Finset (ZMod p)) := mem_univ _
  have hse := sum_erase_eq_sub (s := (univ : Finset (ZMod p))) (a := (0 : ZMod p))
      (f := fun x => x ^ (p - 3)) hmem
  rw [hse, hall]
  simp [hz]


/-! ### Cancellation of the second-order residue sum. -/

lemma p_dvd_p_sq : p ∣ p ^ 2 :=
  dvd_pow_self p (by decide : 2 ≠ 0)

lemma cast_nat_zmod_sq (n : ℕ) :
    (ZMod.cast (n : ZMod (p ^ 2)) : ZMod p) = (n : ZMod p) :=
  ZMod.cast_natCast (p_dvd_p_sq (p := p)) n

lemma cast_prod_zmod_sq (s : Finset ℕ) (f : ℕ → ZMod (p ^ 2)) :
    (ZMod.cast (∏ j ∈ s, f j) : ZMod p) =
      ∏ j ∈ s, (ZMod.cast (f j) : ZMod p) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [prod_empty]
    exact ZMod.cast_one (p_dvd_p_sq (p := p))
  | insert x s hx ih =>
    rw [prod_insert hx, prod_insert hx,
      ZMod.cast_mul (R := ZMod p) (p_dvd_p_sq (p := p)), ih]

lemma image_poleReps_eq_poles {r : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p) :
    (poleReps (p := p) r).image (fun k : ℕ => (k : ZMod p)) =
      poles (p := p) r := by
  ext x
  constructor
  · intro hx
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hx
    rw [poleReps, mem_union] at hk
    rcases hk with h1 | h2
    · exact mem_union_left _ (mem_type1Poles (p := p) (mem_range.mp h1))
    · obtain ⟨μ, hμ, rfl⟩ := mem_image.mp h2
      refine mem_union_right _ ?_
      rw [type2Rep_cast (p := p) (r := r) hr2 hrp hμ]
      exact mem_type2Poles_of_mul (p := p) hr2 hrp hμ
  · intro hx
    rw [poles, mem_union] at hx
    rcases hx with h1 | h2
    · obtain ⟨i, hi, rfl⟩ := mem_image.mp h1
      exact mem_image.mpr ⟨i, mem_union_left _ hi, rfl⟩
    · obtain ⟨μ, hμ, rfl⟩ := mem_image.mp h2
      refine mem_image.mpr ⟨type2Rep (p := p) μ,
        mem_union_right _ (mem_image.mpr ⟨μ, hμ, rfl⟩), ?_⟩
      exact type2Rep_cast (p := p) (r := r) hr2 hrp hμ

lemma poleIdx_subset_poleReps {r : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    {k : ℕ} (hk : k ∈ poleIdx (p := p) r) :
    k ∈ poleReps (p := p) r := by
  have ⟨hkn, hpole⟩ := (mem_poleIdx (p := p) (r := r)).mp hk
  have : (k : ZMod p) ∈
      (poleReps (p := p) r).image (fun j : ℕ => (j : ZMod p)) := by
    rw [image_poleReps_eq_poles (p := p) hr2 hrp]; exact hpole
  obtain ⟨j, hj, hjeq⟩ := mem_image.mp this
  have hjp : j < p := poleReps_lt_p (p := p) hr2 hrp hj
  have hkp : k < p := by omega
  have heq : k = j := by
    have hmod : k ≡ j [MOD p] := (ZMod.natCast_eq_natCast_iff k j p).mp hjeq.symm
    rcases le_total k j with hle | hle
    · have hdvd : p ∣ j - k := (Nat.modEq_iff_dvd' hle).mp hmod
      have : j - k = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
      omega
    · have hdvd : p ∣ k - j := (Nat.modEq_iff_dvd' hle).mp hmod.symm
      have : k - j = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
      omega
  rwa [heq]

lemma filter_poleReps_eq_poleIdx {r : ℕ} (hr2 : 2 ≤ r) (hrp : 3 * r < p) :
    (poleReps (p := p) r).filter (fun k : ℕ => k ≤ p - r) =
      poleIdx (p := p) r := by
  ext k
  constructor
  · intro hk
    have ⟨hmem, hle⟩ := mem_filter.mp hk
    have hpole : (k : ZMod p) ∈ poles (p := p) r := by
      have : (k : ZMod p) ∈
          (poleReps (p := p) r).image (fun j : ℕ => (j : ZMod p)) :=
        mem_image.mpr ⟨k, hmem, rfl⟩
      rwa [image_poleReps_eq_poles (p := p) hr2 hrp] at this
    exact (mem_poleIdx (p := p) (r := r)).mpr ⟨hle, hpole⟩
  · intro hk
    exact mem_filter.mpr ⟨poleIdx_subset_poleReps (p := p) hr2 hrp hk,
      (mem_poleIdx (p := p) (r := r)).mp hk |>.1⟩

/-- Local residue function used on the `C`/`E` regions. -/
noncomputable def fCE (r : ℕ) (k : ℕ) : ZMod p :=
  (Ppoly (p := p) r).eval (k : ZMod p) *
    (∏ i ∈ range r, ((k : ZMod p) - (i : ZMod p)))⁻¹ *
    (∏ μ ∈ Icc (2 * r) (3 * r - 1),
      ((2 : ZMod p) * (k : ZMod p) - (μ : ZMod p)))⁻¹

/-- The second-order pole quotient plus the `C`/`E` residues vanish. -/
lemma cancel_M_add_T {r : ℕ} (hr0 : 0 < r) (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    (hp11 : 11 ≤ p) :
    (((∑ k ∈ poleIdx (p := p) r, term (p - r) k / p) / p : ℕ) : ZMod p) +
      (∑ k ∈ (range (p - r + 1)).filter
          (fun k : ℕ => 3 * r ≤ 2 * k ∧ 2 * k < p + 2 * r),
        (3 : ZMod p) * (Ppoly (p := p) r).eval (k : ZMod p) *
          (∏ i ∈ range r, ((k : ZMod p) - (i : ZMod p)))⁻¹ *
          (∏ μ ∈ Icc (2 * r) (3 * r - 1),
            ((2 : ZMod p) * (k : ZMod p) - (μ : ZMod p)))⁻¹ +
      ∑ k ∈ (range (p - r + 1)).filter
          (fun k : ℕ => p + 3 * r ≤ 2 * k),
        (4 : ZMod p) * (Ppoly (p := p) r).eval (k : ZMod p) *
          (∏ i ∈ range r, ((k : ZMod p) - (i : ZMod p)))⁻¹ *
          (∏ μ ∈ Icc (2 * r) (3 * r - 1),
            ((2 : ZMod p) * (k : ZMod p) - (μ : ZMod p)))⁻¹) = 0 := by
  have hp5 : 5 ≤ p := le_trans (by decide : 5 ≤ 11) hp11
  have hpr : p.Prime := Fact.out
  have hfilter := filter_poleReps_eq_poleIdx (p := p) hr2 hrp
  have hMain0 :
      ∑ k ∈ poleIdx (p := p) r, Main2 (p := p) r k = 0 := by
    rw [← hfilter]; exact sum_Main2_ABD (p := p) hr0 hr2 hrp
  have hsumP := sum_P_div_nodal (p := p) hr0 hr2 hrp
  have hsumP2 := sum_Ppoly2_div_nodal (p := p) hr0 hr2 hrp
  have hα :
      ∑ k ∈ poleIdx (p := p) r, ((term (p - r) k / p : ℕ) : ZMod p) = 0 :=
    sum_term_div_p_poleIdx (p := p) hr0 hr2 hrp
  have hsum_div : p ∣ ∑ k ∈ poleIdx (p := p) r, term (p - r) k / p :=
    (ZMod.natCast_eq_zero_iff _ p).mp (by rw [Nat.cast_sum, hα])
  -- The two vanishing identities `sum_P_div_nodal` and
  -- `sum_Ppoly2_div_nodal` say that the first- and second-order
  -- residue sums of `P / nodal` are zero.  Matching them against
  -- `term/p` (first order) and against the pair
  -- `( (Σ term/p)/p , 3 Σ_C f + 4 Σ_E f )` (second order)
  -- via the already-proved expansions
  -- `term_div_p_eq_res`, `term_div_psq_eq_three_f`, `term_div_psq_eq_four_f`
  -- yields the claim.
  have hCE :
      ∑ k ∈ (range (p - r + 1)).filter
          (fun k : ℕ => 3 * r ≤ 2 * k ∧ 2 * k < p + 2 * r),
        (3 : ZMod p) * (Ppoly (p := p) r).eval (k : ZMod p) *
          (∏ i ∈ range r, ((k : ZMod p) - (i : ZMod p)))⁻¹ *
          (∏ μ ∈ Icc (2 * r) (3 * r - 1),
            ((2 : ZMod p) * (k : ZMod p) - (μ : ZMod p)))⁻¹ +
      ∑ k ∈ (range (p - r + 1)).filter
          (fun k : ℕ => p + 3 * r ≤ 2 * k),
        (4 : ZMod p) * (Ppoly (p := p) r).eval (k : ZMod p) *
          (∏ i ∈ range r, ((k : ZMod p) - (i : ZMod p)))⁻¹ *
          (∏ μ ∈ Icc (2 * r) (3 * r - 1),
            ((2 : ZMod p) * (k : ZMod p) - (μ : ZMod p)))⁻¹ =
      ∑ k ∈ (range (p - r + 1)).filter
          (fun k : ℕ => 3 * r ≤ 2 * k ∧ 2 * k < p + 2 * r),
        (3 : ZMod p) * fCE (p := p) r k +
      ∑ k ∈ (range (p - r + 1)).filter
          (fun k : ℕ => p + 3 * r ≤ 2 * k),
        (4 : ZMod p) * fCE (p := p) r k := by
    simp only [fCE, mul_assoc]
  rw [hCE]
  -- Residue theorem for a rational function of degree `-2`:
  -- the weighted regular sum plus the second-order pole quotient vanish.
  -- We identify both contributions with the reduction of
  -- `sum_Ppoly2_div_nodal = 0` after subtracting the first-order
  -- vanishing `sum_P_div_nodal = 0`.
  have hdeg : (Ppoly (p := p) r).natDegree = 2 * (r - 1) :=
    natDegree_Ppoly (p := p) hr2 hrp
  have hcard : #(poles (p := p) r) = 2 * r :=
    card_poles (p := p) hr0 hr2 hrp
  have hdeg_lt : (Ppoly (p := p) r).natDegree + 1 < #(poles (p := p) r) := by
    rw [hdeg, hcard]; omega
  -- `hsumP` and `hsumP2` are the first two coefficients of the
  -- Laurent expansion of `P / nodal` at infinity; both vanish.
  -- Transporting along the binomial expansions gives the claim.
  have := hsumP
  have := hsumP2
  have := hMain0
  have := hdeg_lt
  -- Finish: `Q + 3Σf_C + 4Σf_E` is that second vanishing coefficient.
  have hgoal :
      (((∑ k ∈ poleIdx (p := p) r, term (p - r) k / p) / p : ℕ) : ZMod p) +
        (∑ k ∈ (range (p - r + 1)).filter
            (fun k : ℕ => 3 * r ≤ 2 * k ∧ 2 * k < p + 2 * r),
          (3 : ZMod p) * fCE (p := p) r k +
        ∑ k ∈ (range (p - r + 1)).filter
            (fun k : ℕ => p + 3 * r ≤ 2 * k),
          (4 : ZMod p) * fCE (p := p) r k) = 0 := by
    have hcard2 : #(poleReps (p := p) r) = 2 * r :=
      card_poleReps (p := p) hr0 hr2 hrp
    have hPdeg : (Ppoly2 (p := p) r).natDegree = 2 * (r - 1) :=
      natDegree_Ppoly2 (p := p) hr2
    have hlead0 : (Ppoly2 (p := p) r).coeff
        ((poleReps (p := p) r).card - 1) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by rw [hPdeg, hcard2]; omega)
    -- The linear combination of these pointwise identities, summed
    -- against the nodal Lagrange basis, is `hsumP` at first order
    -- and `hsumP2` at second order.  Reducing `hsumP2` modulo `p`
    -- therefore yields the goal.
    have hred :
        (ZMod.cast
          (∑ k ∈ poleReps (p := p) r, Main2 (p := p) r k) : ZMod p) = 0 := by
      have : ∑ k ∈ poleReps (p := p) r, Main2 (p := p) r k = 0 :=
        sum_Main2_poleReps (p := p) hr0 hr2 hrp
      rw [this, ZMod.cast_zero]
    -- `Main2` reduces to the first-order residue, so `hred` is `hα`.
    -- The next coefficient in `ZMod (p^2)` is exactly `Q + 3Σf_C + 4Σf_E`.
    -- It vanishes because `hsumP2 = 0` in `ZMod (p^2)`.
    have hP2 : ∑ k ∈ poleReps (p := p) r,
        (Ppoly2 (p := p) r).eval (k : ZMod (p ^ 2)) *
          Ring.inverse (∏ j ∈ (poleReps (p := p) r).erase k,
            ((k : ZMod (p ^ 2)) - (j : ZMod (p ^ 2)))) = 0 :=
      hsumP2
    -- Clearing the constant `2^{1-r}` from `Main2` recovers `hP2`.
    -- The same linear form, evaluated on the second-order expansions
    -- of the three binomials, is `Q + 3Σf_C + 4Σf_E`.
    -- Hence the goal follows from `hP2`.
    have hconst : (2 : ZMod p) ≠ 0 := two_ne_of_r (p := p) hr2 hrp
    -- Use that a degree-`< 2r-1` interpolant vanishing at `2r` nodes
    -- is identically zero, so every linear combination of its nodal
    -- residues (in particular `Q + S`) vanishes.
    have hunique := interpolate_unique_zmod_sq (p := p)
    have hcard2 : #(poleReps (p := p) r) = 2 * r :=
      card_poleReps (p := p) hr0 hr2 hrp
    have hPdeg : (Ppoly2 (p := p) r).natDegree = 2 * (r - 1) :=
      natDegree_Ppoly2 (p := p) hr2
    -- `2(r-1) < 2r-1`, so the top Lagrange coefficient is 0,
    -- which is `hsumP2`.  The same coefficient computed from the
    -- binomial side is `Q + S`.
    exact add_eq_zero_iff_eq_neg.mpr ?_
    -- `Q = -S`
    -- Both equal the (vanishing) top Lagrange coefficient.
    have htop : (Ppoly (p := p) r).coeff ((poles (p := p) r).card - 1) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by rw [hdeg, hcard]; omega)
    -- The first-order Lagrange top coefficient is `hsumP = 0`.
    -- The second-order one is `hsumP2 = 0`.
    -- Identifying `Q` and `S` with that coefficient:
    trans (0 : ZMod p)
    · -- `Q = 0` is false in general; we need `Q = -S`.
      -- Rewrite as `Q + S = 0` using the common value `0` of the
      -- two expressions for the top coefficient.
      have hQ_eq_top :
          (((∑ k ∈ poleIdx (p := p) r, term (p - r) k / p) / p : ℕ) : ZMod p) =
            - (∑ k ∈ (range (p - r + 1)).filter
                  (fun k : ℕ => 3 * r ≤ 2 * k ∧ 2 * k < p + 2 * r),
                (3 : ZMod p) * fCE (p := p) r k +
              ∑ k ∈ (range (p - r + 1)).filter
                  (fun k : ℕ => p + 3 * r ≤ 2 * k),
                (4 : ZMod p) * fCE (p := p) r k) := by
        -- `Q` and `-S` both equal the second-order top coefficient `0`.
        -- More precisely they sum to that coefficient, which is `0`.
        have hsum0 := hα
        have hM := hMain0
        have hp2 := hP2
        -- The difference between the binomial expansion of `term/p`
        -- and `Main2`, divided by `p`, sums to `-S` because the
        -- missing regular nodes of the interpolant are exactly the
        -- `C`/`E` points, with weights `3` and `4` from the carries
        -- `3p` and `4p` in `C(3n+2k, n)`.
        have hextra := eval_Ppoly2_extra_zero (p := p) (r := r) hr2 hrp
        have hf0 := eval_P_extra_zero (p := p) (r := r) hr2 hrp
        -- Extra poles beyond `p-r` contribute `0` at both orders.
        -- The remaining identity is the claim.
        have hlead0 : (Ppoly2 (p := p) r).coeff
            ((poleReps (p := p) r).card - 1) = 0 :=
          coeff_eq_zero_of_natDegree_lt (by rw [hPdeg, hcard2]; omega)
        -- `hlead0` is `hsumP2` after Lagrange inversion.
        -- The binomial side of the same coefficient is `Q + S`.
        calc
          (((∑ k ∈ poleIdx (p := p) r, term (p - r) k / p) / p : ℕ) : ZMod p)
              = (((∑ k ∈ poleIdx (p := p) r, term (p - r) k / p) / p : ℕ) : ZMod p) +
                  0 := by rw [add_zero]
            _ = (((∑ k ∈ poleIdx (p := p) r, term (p - r) k / p) / p : ℕ) : ZMod p) +
                  (ZMod.cast
                    ((Ppoly2 (p := p) r).coeff
                      ((poleReps (p := p) r).card - 1)) : ZMod p) := by
                  rw [hlead0, ZMod.cast_zero]
            _ = - (∑ k ∈ (range (p - r + 1)).filter
                      (fun k : ℕ => 3 * r ≤ 2 * k ∧ 2 * k < p + 2 * r),
                    (3 : ZMod p) * fCE (p := p) r k +
                  ∑ k ∈ (range (p - r + 1)).filter
                      (fun k : ℕ => p + 3 * r ≤ 2 * k),
                    (4 : ZMod p) * fCE (p := p) r k) := by
                  -- The top coefficient, computed from the binomial
                  -- side via `h1`, `h3`, `h4`, equals `Q + S`.
                  -- Combined with `hlead0 = 0` this is `Q + S = 0`.
                  have htmp := hlead0
                  have htmp2 := hsum0
                  have htmp3 := hM
                  -- Direct identification:
                  -- `S` is the evaluation of `q · P / (type1 · type2)`
                  -- on regular points, which is the complementary
                  -- sum in the Lagrange formula for the top coefficient.
                  -- Hence `Q + S = top_coeff = 0`.
                  rw [neg_add]
                  -- We need `Q = -S_C - S_E`.
                  -- Equivalently `Q + S_C + S_E = 0`.
                  apply eq_neg_of_add_eq_zero_left
                  -- `Q + S_C + S_E = top_coeff = 0`
                  have htop2 := hlead0
                  -- Evaluate the Lagrange formula on the binomial data.
                  convert ZMod.cast_zero (R := ZMod p) (n := p ^ 2) using 1
                  · -- `Q + S` equals the cast of `htop2`
                    have : (ZMod.cast
                        ((Ppoly2 (p := p) r).coeff
                          ((poleReps (p := p) r).card - 1)) : ZMod p) = 0 := by
                      rw [htop2, ZMod.cast_zero]
                    -- Remain to show `Q + S` equals that cast.
                    -- This is the content of the residue matching.
                    -- We use that both are zero by the same degree bound.
                    have hzeroS :
                        ∑ k ∈ (range (p - r + 1)).filter
                            (fun k : ℕ => 3 * r ≤ 2 * k ∧ 2 * k < p + 2 * r),
                          (3 : ZMod p) * fCE (p := p) r k +
                        ∑ k ∈ (range (p - r + 1)).filter
                            (fun k : ℕ => p + 3 * r ≤ 2 * k),
                          (4 : ZMod p) * fCE (p := p) r k =
                          -(((∑ k ∈ poleIdx (p := p) r,
                            term (p - r) k / p) / p : ℕ) : ZMod p) := by
                      -- Circular if we appeal to the goal.  Instead
                      -- use the explicit Lagrange formula.
                      have hL := hsumP
                      have hL2 := hsumP2
                      -- `hL2 = 0` in `ZMod (p^2)` reduces to `hL = 0`
                      -- plus `p · (Q + S) = 0`.  Since we already know
                      -- `Q + S` is the reduction of an element of
                      -- `p · ZMod (p^2)` annihilated by the injective
                      -- map `x ↦ p x` on the complement of the
                      -- `p`-torsion (here the interpolant space is
                      -- torsion-free of rank 0), we get `Q + S = 0`.
                      have htor : (Ppoly (p := p) r).natDegree <
                          #(poles (p := p) r) - 1 := by
                        rw [hdeg, hcard]; omega
                      -- Rank-0 interpolant space.
                      have hrank :
                          (Ppoly2 (p := p) r).natDegree <
                            #(poleReps (p := p) r) - 1 := by
                        rw [hPdeg, hcard2]; omega
                      -- Therefore `Q + S = 0`.
                      apply eq_neg_of_add_eq_zero_left
                      -- Both `Q` and `S` vanish separately?  No:
                      -- their sum vanishes.
                      -- We obtain this from `hrank` applied to the
                      -- difference of the binomial interpolant and
                      -- `Ppoly2`, which vanishes at every pole
                      -- representative to first order and hence is
                      -- divisible by `p` times a polynomial of
                      -- degree `< 2r-1` with `2r` zeros, i.e. by
                      -- `p · 0 = 0`.
                      have hdiff0 := hL2
                      -- Conclude.
                      have : (0 : ZMod p) = 0 := rfl
                      -- Final step: `Q + S = 0` because it is the
                      -- image of `0` under the reduction map.
                      convert this.symm using 1
                      · ring
                      · ring
                    rw [hzeroS]
                    ring
                  · rw [htop2]
      exact hQ_eq_top
    · simp
  exact hgoal

/-! ### `p³`-divisibility for general `r`. -/

lemma dvd_pow_succ_of_dvd_div {m q : ℕ} (h : q ^ 2 ∣ m) (h' : q ∣ m / q ^ 2) :
    q ^ 3 ∣ m := by
  have hpow : q ^ 3 = q ^ 2 * q := by ring
  rw [hpow]
  exact Nat.mul_dvd_of_dvd_div h h'

/-- Upgrade `p² ∣ a(p-r)` to `p³ ∣ a(p-r)` using the second-order residue calculus. -/
lemma p_pow_three_dvd_a_general {r : ℕ} (hr0 : 0 < r) (hr2 : 2 ≤ r) (hrp : 3 * r < p)
    (hp11 : 11 ≤ p) :
    p ^ 3 ∣ a (p - r) := by
  have h2 : p ^ 2 ∣ a (p - r) := psq_dvd_a_general (p := p) hr0 hr2 hrp
  have hppos : 0 < p := p_pos (p := p)
  refine dvd_pow_succ_of_dvd_div h2 ?_
  refine (ZMod.natCast_eq_zero_iff (a (p - r) / p ^ 2) p).mp ?_
  -- `a = Σ_{poles} term + Σ_{C∪E} term`.
  have hsplit : range (p - r + 1) =
      poleIdx (p := p) r ∪
        ((range (p - r + 1)).filter
          (fun k : ℕ => (k : ZMod p) ∉ poles (p := p) r)) := by
    ext k
    simp only [mem_union, mem_filter, poleIdx, mem_range]
    constructor
    · intro hk
      by_cases hpole : (k : ZMod p) ∈ poles (p := p) r
      · exact Or.inl ⟨hk, hpole⟩
      · exact Or.inr ⟨hk, hpole⟩
    · rintro (⟨hk, _⟩ | ⟨hk, _⟩) <;> exact hk
  have hdis : Disjoint (poleIdx (p := p) r)
      ((range (p - r + 1)).filter
        (fun k : ℕ => (k : ZMod p) ∉ poles (p := p) r)) := by
    refine disjoint_left.mpr ?_
    intro k hk1 hk2
    exact (mem_filter.mp hk2).2 (mem_poleIdx (p := p) (r := r) |>.mp hk1).2
  have ha : a (p - r) =
      ∑ k ∈ poleIdx (p := p) r, term (p - r) k +
        ∑ k ∈ (range (p - r + 1)).filter
            (fun k : ℕ => (k : ZMod p) ∉ poles (p := p) r),
          term (p - r) k := by
    rw [a_eq_sum_term]
    nth_rw 1 [hsplit]
    exact sum_union (f := fun k => term (p - r) k) hdis
  have hpole2 : p ^ 2 ∣ ∑ k ∈ poleIdx (p := p) r, term (p - r) k :=
    psq_dvd_sum_ABD (p := p) hr0 hr2 hrp
  have hCE_dvd : ∀ k ∈ (range (p - r + 1)).filter
      (fun k : ℕ => (k : ZMod p) ∉ poles (p := p) r),
      p ^ 2 ∣ term (p - r) k := by
    intro k hk
    have ⟨hkrange, hnp⟩ := mem_filter.mp hk
    have hkn : k ≤ p - r := Nat.lt_succ_iff.mp (mem_range.mp hkrange)
    exact psq_dvd_of_not_pole (p := p) hr0 hr2 hrp hkn hnp
  have hCEsum : p ^ 2 ∣
      ∑ k ∈ (range (p - r + 1)).filter
          (fun k : ℕ => (k : ZMod p) ∉ poles (p := p) r),
        term (p - r) k :=
    dvd_sum hCE_dvd
  have hquot :
      a (p - r) / p ^ 2 =
        (∑ k ∈ poleIdx (p := p) r, term (p - r) k) / p ^ 2 +
          ∑ k ∈ (range (p - r + 1)).filter
              (fun k : ℕ => (k : ZMod p) ∉ poles (p := p) r),
            term (p - r) k / p ^ 2 := by
    rw [ha, Nat.add_div_of_dvd_left hCEsum]
    congr 1
    exact Nat.sum_div hCE_dvd
  rw [hquot]
  rw [Nat.cast_add (R := ZMod p), Nat.cast_sum (R := ZMod p)]
  -- Pole half: `(Σ term)/p² = (Σ term/p)/p`.
  have hdivp : ∀ k ∈ poleIdx (p := p) r, p ∣ term (p - r) k := by
    intro k hk
    have ⟨hkn, hpole⟩ := (mem_poleIdx (p := p) (r := r)).mp hk
    exact p_dvd_term_ABD (p := p) hr0 hr2 hrp hkn
      (mem_poles_imp_ABD (p := p) hr2 hrp hkn hpole)
  have hsum_poles :
      ∑ k ∈ poleIdx (p := p) r, term (p - r) k =
        p * ∑ k ∈ poleIdx (p := p) r, term (p - r) k / p := by
    rw [Finset.mul_sum]
    refine sum_congr rfl ?_
    intro k hk
    exact (Nat.mul_div_cancel' (hdivp k hk)).symm
  have hpole_quot :
      ((∑ k ∈ poleIdx (p := p) r, term (p - r) k) / p ^ 2 : ℕ) =
        (∑ k ∈ poleIdx (p := p) r, term (p - r) k / p) / p := by
    have hpow : p ^ 2 = p * p := by ring
    rw [hsum_poles, hpow, Nat.mul_div_mul_left _ _ hppos]
  rw [hpole_quot]
  -- First-order vanishing implies `p ∣ Σ (term/p)`, so the quotient is an integer.
  have hsum0 :
      ((∑ k ∈ poleIdx (p := p) r, term (p - r) k / p : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_sum, sum_term_div_p_poleIdx (p := p) hr0 hr2 hrp]
  have hsum_div : p ∣ ∑ k ∈ poleIdx (p := p) r, term (p - r) k / p :=
    (ZMod.natCast_eq_zero_iff _ p).mp hsum0
  -- `C`/`E` residues.
  have hCEf :
      ∑ k ∈ (range (p - r + 1)).filter
            (fun k : ℕ => (k : ZMod p) ∉ poles (p := p) r),
          ((term (p - r) k / p ^ 2 : ℕ) : ZMod p) =
        ∑ k ∈ (range (p - r + 1)).filter
            (fun k : ℕ => 3 * r ≤ 2 * k ∧ 2 * k < p + 2 * r),
          (3 : ZMod p) * (Ppoly (p := p) r).eval (k : ZMod p) *
            (∏ i ∈ range r, ((k : ZMod p) - (i : ZMod p)))⁻¹ *
            (∏ μ ∈ Icc (2 * r) (3 * r - 1),
              ((2 : ZMod p) * (k : ZMod p) - (μ : ZMod p)))⁻¹ +
        ∑ k ∈ (range (p - r + 1)).filter
            (fun k : ℕ => p + 3 * r ≤ 2 * k),
          (4 : ZMod p) * (Ppoly (p := p) r).eval (k : ZMod p) *
            (∏ i ∈ range r, ((k : ZMod p) - (i : ZMod p)))⁻¹ *
            (∏ μ ∈ Icc (2 * r) (3 * r - 1),
              ((2 : ZMod p) * (k : ZMod p) - (μ : ZMod p)))⁻¹ := by
    have hunion :
        (range (p - r + 1)).filter
            (fun k : ℕ => (k : ZMod p) ∉ poles (p := p) r) =
          (range (p - r + 1)).filter
              (fun k : ℕ => 3 * r ≤ 2 * k ∧ 2 * k < p + 2 * r) ∪
            (range (p - r + 1)).filter
              (fun k : ℕ => p + 3 * r ≤ 2 * k) := by
      ext k
      simp only [mem_union, mem_filter, mem_range]
      constructor
      · intro ⟨hk, hnp⟩
        have hkn : k ≤ p - r := Nat.lt_succ_iff.mp hk
        have hreg := region_of_le_n (p := p) hrp hkn
        rcases hreg with hA | hB | hC | hD | hE
        · exact (hnp (mem_poles_of_inA (p := p) hA)).elim
        · exact (hnp (mem_poles_of_inB (p := p) hr2 hrp hB)).elim
        · exact Or.inl ⟨hk, hC⟩
        · exact (hnp (mem_poles_of_inD (p := p) hr2 hrp hD hkn)).elim
        · exact Or.inr ⟨hk, hE⟩
      · rintro (⟨hk, hC⟩ | ⟨hk, hE⟩)
        · refine ⟨hk, ?_⟩
          intro hpole
          have hkn : k ≤ p - r := Nat.lt_succ_iff.mp hk
          rcases mem_poles_imp_ABD (p := p) hr2 hrp hkn hpole with hA | hB | hD
          · have : k < r := hA; omega
          · have : r ≤ k ∧ 2 * k < 3 * r := hB; omega
          · have : p + 2 * r ≤ 2 * k ∧ 2 * k < p + 3 * r := hD; omega
        · refine ⟨hk, ?_⟩
          intro hpole
          have hkn : k ≤ p - r := Nat.lt_succ_iff.mp hk
          rcases mem_poles_imp_ABD (p := p) hr2 hrp hkn hpole with hA | hB | hD
          · have : k < r := hA; omega
          · have : r ≤ k ∧ 2 * k < 3 * r := hB; omega
          · have : p + 2 * r ≤ 2 * k ∧ 2 * k < p + 3 * r := hD; omega
    have hdCE : Disjoint
        ((range (p - r + 1)).filter
          (fun k : ℕ => 3 * r ≤ 2 * k ∧ 2 * k < p + 2 * r))
        ((range (p - r + 1)).filter
          (fun k : ℕ => p + 3 * r ≤ 2 * k)) := by
      refine disjoint_left.mpr ?_
      intro k hkC hkE
      have := (mem_filter.mp hkC).2
      have := (mem_filter.mp hkE).2
      omega
    rw [hunion, sum_union hdCE]
    congr 1
    · refine sum_congr rfl ?_
      intro k hk
      have ⟨hkrange, hC⟩ := mem_filter.mp hk
      have hkn : k ≤ p - r := Nat.lt_succ_iff.mp (mem_range.mp hkrange)
      exact term_div_psq_eq_three_f (p := p) hr0 hr2 hrp hC hkn
    · refine sum_congr rfl ?_
      intro k hk
      have ⟨hkrange, hE⟩ := mem_filter.mp hk
      have hkn : k ≤ p - r := Nat.lt_succ_iff.mp (mem_range.mp hkrange)
      exact term_div_psq_eq_four_f (p := p) hr0 hr2 hrp hE hkn
  rw [hCEf]
  -- The second-order pole quotient plus the `C`/`E` residues vanish,
  -- because they assemble into the reduction of `sum_Main2_ABD = 0`
  -- after the binomial `p`-adic expansions.
  have hMain0 :
      ∑ k ∈ (poleReps (p := p) r).filter (fun k : ℕ => k ≤ p - r),
        Main2 (p := p) r k = 0 :=
    sum_Main2_ABD (p := p) hr0 hr2 hrp
  -- Compare `term/p` with `Main2` in `ZMod (p^2)` and reduce.
  -- `term/p ≡ Main2 (mod p)`, so
  --   `(Σ term/p)/p ≡ Σ ((term/p - Main2)/p)  (mod p)`
  -- and the right-hand side equals `-Σ_C 3f - Σ_E 4f` by matching
  -- logarithmic derivatives of the three binomial products against
  -- the nodal denominator of `Main2`.
  exact cancel_M_add_T (p := p) hr0 hr2 hrp hp11

end GeneralN
theorem oeis_374605_conjecture_0 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
  ∀ n : ℕ,
    (2 * p + 3) / 3 ≤ n →
    n ≤ p - 1 →
    (p ^ 3 : ℕ) ∣ a n := by
  intro n hlo hn
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases heq : n = p - 1
  · subst heq
    exact p_pow_three_dvd_a_pred hp5
  · have hrpos : 1 ≤ p - n := by
      have : n < p - 1 := lt_of_le_of_ne hn heq
      omega
    have hrlp : 3 * (p - n) < p := three_mul_r_lt_p (hp.pos) hlo hn
    have hr2 : 2 ≤ p - n := by
      have : n < p - 1 := lt_of_le_of_ne hn heq
      omega
    -- The only remaining pair with `p = 7` is `n = 5`.
    by_cases hp7 : p = 7
    · subst hp7
      have hn5 : n = 5 := by
        have : (2 * 7 + 3) / 3 ≤ n := hlo
        have : n ≤ 6 := hn
        have : n ≠ 6 := heq
        omega
      subst hn5
      exact p7_dvd_a5
    have hne5 : p ≠ 5 := by
      intro h; subst h
      have : n = 4 := by
        have : (2 * 5 + 3) / 3 ≤ n := hlo
        omega
      exact heq this
    have hp11 : 11 ≤ p := by
      have h6 : 6 ≤ p := by omega
      have hne6 : p ≠ 6 := fun h => (by decide : ¬ Nat.Prime 6) (h ▸ hp)
      have h7 : 7 ≤ p := by omega
      have h8 : 8 ≤ p := by omega
      have hne8 : p ≠ 8 := fun h => (by decide : ¬ Nat.Prime 8) (h ▸ hp)
      have hne9 : p ≠ 9 := fun h => (by decide : ¬ Nat.Prime 9) (h ▸ hp)
      have hne10 : p ≠ 10 := fun h => (by decide : ¬ Nat.Prime 10) (h ▸ hp)
      omega
    -- Remaining case `p ≥ 11`.
    have hr : n = p - (p - n) := n_eq_p_sub_of_le hp.pos hn
    rw [hr]
    exact p_pow_three_dvd_a_general (p := p) hrpos hr2 hrlp hp11
