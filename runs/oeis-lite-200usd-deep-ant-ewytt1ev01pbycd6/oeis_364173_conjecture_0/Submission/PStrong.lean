import FormalConjectures.Util.ProblemImports
import Submission.PLog
import Submission.PKaz
import Submission.VonStaudt
import Submission.PSigma
namespace PStrong
open PLog PKaz PSigma
variable {p : ℕ} [hp : Fact p.Prime]

/-! ## Part A: the sharp per-term bound `‖a k * d k s‖ ≤ p^{-3}` -/

/-- `v + 4 ≤ p^v` for `v ≥ 1`, `p ≥ 5`. -/
lemma pow_ge4 (hp5 : 5 ≤ p) : ∀ v : ℕ, 1 ≤ v → v + 4 ≤ p ^ v := by
  intro v
  induction v with
  | zero => intro h; omega
  | succ m ih =>
    intro _
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp only [zero_add, pow_one]; omega
    · have hih := ih hm
      have hps : p ^ (m + 1) = p * p ^ m := by rw [pow_succ, mul_comm]
      have hmul := Nat.mul_le_mul hp5 hih
      rw [← hps] at hmul
      omega

/-- `v + 5 ≤ p^v` for `v ≥ 2`, `p ≥ 5`. -/
lemma pow_ge5 (hp5 : 5 ≤ p) : ∀ v : ℕ, 2 ≤ v → v + 5 ≤ p ^ v := by
  intro v hv
  induction v, hv using Nat.le_induction with
  | base =>
      have h := Nat.mul_le_mul hp5 hp5
      rw [show (2 : ℕ) = 1 + 1 from rfl, pow_add, pow_one]
      omega
  | succ n hn ih =>
      have hps : p ^ (n + 1) = p * p ^ n := by rw [pow_succ, mul_comm]
      have hmul := Nat.mul_le_mul hp5 ih
      rw [← hps] at hmul
      omega

/-- At most one of `k`, `k+1` is divisible by `p`. -/
lemma valuation_coprime (hp5 : 5 ≤ p) (k : ℕ) :
    padicValNat p k = 0 ∨ padicValNat p (k + 1) = 0 := by
  by_contra h
  push_neg at h
  obtain ⟨h1, h2⟩ := h
  have hd1 : p ∣ k := (dvd_pow_self p h1).trans pow_padicValNat_dvd
  have hd2 : p ∣ (k + 1) := (dvd_pow_self p h2).trans pow_padicValNat_dvd
  have : p ∣ 1 := by
    have := Nat.dvd_sub hd2 hd1
    simpa using this
  have := Nat.le_of_dvd (by norm_num) this
  omega

/-- The exponent bound: `3 + eB + v_p(k) + v_p(k+1) ≤ k`. -/
lemma exp_bound (hp5 : 5 ≤ p) {k : ℕ} (hk3 : 3 ≤ k) (eB : ℕ)
    (heB : eB = 0 ∨ (eB = 1 ∧ p ≤ k)) :
    3 + eB + padicValNat p k + padicValNat p (k + 1) ≤ k := by
  have hvk : p ^ (padicValNat p k) ≤ k := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
  have hvk1 : p ^ (padicValNat p (k + 1)) ≤ k + 1 := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
  have hcop := valuation_coprime hp5 k
  set vk := padicValNat p k with hvkdef
  set vk1 := padicValNat p (k + 1) with hvk1def
  have Lk : vk = 0 ∨ vk + 4 ≤ k := by
    rcases Nat.eq_zero_or_pos vk with h | h
    · left; exact h
    · right; exact le_trans (pow_ge4 hp5 vk h) hvk
  have Lk1 : vk1 = 0 ∨ vk1 + 4 ≤ k + 1 := by
    rcases Nat.eq_zero_or_pos vk1 with h | h
    · left; exact h
    · right; exact le_trans (pow_ge4 hp5 vk1 h) hvk1
  have Lk1' : vk1 = 0 ∨ vk1 = 1 ∨ vk1 + 5 ≤ k + 1 := by
    rcases Nat.eq_zero_or_pos vk1 with h | h
    · left; exact h
    · rcases Nat.lt_or_ge vk1 2 with h2 | h2
      · right; left; omega
      · right; right; exact le_trans (pow_ge5 hp5 vk1 h2) hvk1
  omega

/-- `((p:ℝ)⁻¹)^n = (p:ℝ)^(-(n:ℤ))`. -/
lemma rpow_neg (n : ℕ) : ((p : ℝ)⁻¹) ^ n = (p : ℝ) ^ (-(n : ℤ)) := by
  rw [inv_pow, ← zpow_natCast (p : ℝ) n, ← zpow_neg]

/-- `‖(k:ℚ_[p])‖⁻¹ = p^{v_p(k)}` for `k ≠ 0`. -/
lemma norm_natCast_inv_eq {k : ℕ} (hk : k ≠ 0) :
    ‖(k : ℚ_[p])‖⁻¹ = (p : ℝ) ^ (padicValNat p k : ℤ) := by
  rw [VonStaudt.norm_natCast_eq k hk, ← zpow_neg, neg_neg]

/-- `‖(n:ℚ_[p])‖ = 1` when `p ∤ n`. -/
lemma norm_natCast_eq_one {n : ℕ} (hn : ¬ p ∣ n) : ‖(n : ℚ_[p])‖ = 1 := by
  rw [← PadicInt.coe_natCast, PadicInt.padic_norm_e_of_padicInt, PKaz.norm_cast_eq_one hn]

/-- Exact norm of `a k`. -/
lemma norm_a_eq (k : ℕ) :
    ‖(a k : ℚ_[p])‖ = ((p : ℝ)⁻¹) ^ k * ‖(Hz k : ℤ_[p])‖ * ‖(k : ℚ_[p])‖⁻¹ := by
  rw [a, norm_div, norm_mul, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, Padic.norm_p, PadicInt.padic_norm_e_of_padicInt, div_eq_mul_inv]

/-- Bound on `‖d k s‖`. -/
lemma norm_d_le3 (k s : ℕ) (hs : 1 ≤ s) :
    ‖(d k s : ℚ_[p])‖ ≤ ‖((bernoulli (k + 1 - s) : ℚ) : ℚ_[p])‖ * (p : ℝ) ^ (padicValNat p (k + 1) : ℤ) := by
  rw [d, if_neg (by omega : s ≠ 0), norm_div, norm_mul, div_eq_mul_inv,
    norm_natCast_inv_eq (by omega : k + 1 ≠ 0)]
  calc ‖((bernoulli (k + 1 - s) : ℚ) : ℚ_[p])‖ * ‖((Nat.choose (k + 1) s : ℕ) : ℚ_[p])‖
          * (p : ℝ) ^ (padicValNat p (k + 1) : ℤ)
      ≤ ‖((bernoulli (k + 1 - s) : ℚ) : ℚ_[p])‖ * 1 * (p : ℝ) ^ (padicValNat p (k + 1) : ℤ) := by
        gcongr
        exact VonStaudt.norm_nat_le_one _
    _ = ‖((bernoulli (k + 1 - s) : ℚ) : ℚ_[p])‖ * (p : ℝ) ^ (padicValNat p (k + 1) : ℤ) := by ring

/-- `‖a 1‖ ≤ p^{-3}`. -/
lemma norm_a_one_le (hp5 : 5 ≤ p) : ‖(a (1 : ℕ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-3 : ℤ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  rw [norm_a_eq]
  have h1 : ‖((1 : ℕ) : ℚ_[p])‖⁻¹ = 1 := by simp
  rw [h1, mul_one, pow_one, show (p : ℝ)⁻¹ = (p : ℝ) ^ (-(1 : ℕ) : ℤ) by
    rw [← rpow_neg 1, pow_one]]
  calc (p : ℝ) ^ (-(1 : ℕ) : ℤ) * ‖(Hz 1 : ℤ_[p])‖
      ≤ (p : ℝ) ^ (-(1 : ℕ) : ℤ) * (p : ℝ) ^ (-2 : ℤ) := by
        gcongr
        exact norm_Hz_one_le hp5
    _ = (p : ℝ) ^ (-3 : ℤ) := by
        rw [← zpow_add₀ (ne_of_gt hp0)]; congr 1

/-- `‖a 2‖ ≤ p^{-3}`. -/
lemma norm_a_two_le (hp5 : 5 ≤ p) : ‖(a (2 : ℕ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-3 : ℤ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hnd2 : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  rw [norm_a_eq]
  have h1 : ‖((2 : ℕ) : ℚ_[p])‖⁻¹ = 1 := by
    rw [inv_eq_one]; exact norm_natCast_eq_one hnd2
  rw [h1, mul_one, rpow_neg 2]
  calc (p : ℝ) ^ (-(2 : ℕ) : ℤ) * ‖(Hz 2 : ℤ_[p])‖
      ≤ (p : ℝ) ^ (-(2 : ℕ) : ℤ) * (p : ℝ) ^ (-1 : ℤ) := by
        gcongr
        exact norm_Hz_two_le hp5
    _ = (p : ℝ) ^ (-3 : ℤ) := by
        rw [← zpow_add₀ (ne_of_gt hp0)]; congr 1

/-- The sharp per-term bound. -/
lemma norm_ad_le3 (hp5 : 5 ≤ p) (k s : ℕ) (hk : 1 ≤ k) (hs : 2 ≤ s) :
    ‖(a k * d k s : ℚ_[p])‖ ≤ (p : ℝ) ^ (-3 : ℤ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp0ne : (p : ℝ) ≠ 0 := ne_of_gt hp0
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_le
  by_cases hks : k + 1 < s
  · rw [d_eq_zero_of_lt hks, mul_zero, norm_zero]; positivity
  push_neg at hks
  rw [norm_mul]
  have hnd2 : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have hnd3 : ¬ p ∣ 3 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  by_cases hk1 : k = 1
  · -- k = 1, s = 2
    subst hk1
    have hs2 : s = 2 := by omega
    subst hs2
    have hd1 : ‖(d 1 2 : ℚ_[p])‖ ≤ 1 := by
      refine le_trans (norm_d_le3 1 2 (by norm_num)) ?_
      have he : (1 : ℕ) + 1 - 2 = 0 := by norm_num
      have hv2 : padicValNat p (1 + 1) = 0 :=
        padicValNat.eq_zero_of_not_dvd (by simpa using hnd2)
      rw [he, bernoulli_zero, hv2]
      simp
    calc ‖(a 1 : ℚ_[p])‖ * ‖(d 1 2 : ℚ_[p])‖ ≤ (p : ℝ) ^ (-3 : ℤ) * 1 :=
          mul_le_mul (norm_a_one_le hp5) hd1 (norm_nonneg _) (by positivity)
      _ = (p : ℝ) ^ (-3 : ℤ) := mul_one _
  by_cases hk2 : k = 2
  · -- k = 2, s ∈ {2, 3}
    subst hk2
    have hd2 : ‖(d 2 s : ℚ_[p])‖ ≤ 1 := by
      refine le_trans (norm_d_le3 2 s (by omega)) ?_
      have hv3 : padicValNat p (2 + 1) = 0 :=
        padicValNat.eq_zero_of_not_dvd (by simpa using hnd3)
      rw [hv3, Nat.cast_zero, zpow_zero, mul_one]
      interval_cases s
      · have he : (2 : ℕ) + 1 - 2 = 1 := by norm_num
        rw [he]
        refine VonStaudt.norm_bernoulli_le_one_of_not_dvd hp5 1 ?_
        intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega
      · have he : (2 : ℕ) + 1 - 3 = 0 := by norm_num
        rw [he, bernoulli_zero]; simp
    calc ‖(a 2 : ℚ_[p])‖ * ‖(d 2 s : ℚ_[p])‖ ≤ (p : ℝ) ^ (-3 : ℤ) * 1 :=
          mul_le_mul (norm_a_two_le hp5) hd2 (norm_nonneg _) (by positivity)
      _ = (p : ℝ) ^ (-3 : ℤ) := mul_one _
  -- k ≥ 3
  have hk3 : 3 ≤ k := by omega
  have ha3 : ‖(a k : ℚ_[p])‖ ≤ (p : ℝ) ^ ((padicValNat p k : ℤ) - k) := by
    rw [norm_a_eq, norm_natCast_inv_eq (by omega : k ≠ 0), rpow_neg k]
    calc (p : ℝ) ^ (-(k : ℤ)) * ‖(Hz k : ℤ_[p])‖ * (p : ℝ) ^ (padicValNat p k : ℤ)
        ≤ (p : ℝ) ^ (-(k : ℤ)) * 1 * (p : ℝ) ^ (padicValNat p k : ℤ) := by
          gcongr
          exact norm_Hz_le_one k
      _ = (p : ℝ) ^ ((padicValNat p k : ℤ) - k) := by
          rw [mul_one, ← zpow_add₀ hp0ne]; congr 1; ring
  set m := k + 1 - s with hm
  by_cases hbc : (p - 1) ∣ m ∧ 2 ≤ m
  · -- bernoulli factor ≤ p, and p ≤ k
    have hbern : ‖((bernoulli m : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (1 : ℤ) := by
      rw [zpow_one]; exact VonStaudt.norm_bernoulli_le hp5 m
    have hd3 : ‖(d k s : ℚ_[p])‖ ≤ (p : ℝ) ^ ((1 : ℤ) + padicValNat p (k + 1)) := by
      refine le_trans (norm_d_le3 k s (by omega)) ?_
      rw [← hm, zpow_add₀ hp0ne]
      exact mul_le_mul_of_nonneg_right hbern (by positivity)
    have hmpos : 0 < m := by omega
    have hge : p - 1 ≤ m := Nat.le_of_dvd hmpos hbc.1
    have hpk : p ≤ k := by omega
    calc ‖(a k : ℚ_[p])‖ * ‖d k s‖
        ≤ (p : ℝ) ^ ((padicValNat p k : ℤ) - k)
            * (p : ℝ) ^ ((1 : ℤ) + padicValNat p (k + 1)) :=
          mul_le_mul ha3 hd3 (norm_nonneg _) (by positivity)
      _ = (p : ℝ) ^ (((padicValNat p k : ℤ) - k) + ((1 : ℤ) + padicValNat p (k + 1))) := by
          rw [← zpow_add₀ hp0ne]
      _ ≤ (p : ℝ) ^ (-3 : ℤ) := by
          apply zpow_le_zpow_right₀ hp1
          have := exp_bound hp5 hk3 1 (Or.inr ⟨rfl, hpk⟩)
          omega
  · -- bernoulli factor ≤ 1
    have hbern : ‖((bernoulli m : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (0 : ℤ) := by
      rw [zpow_zero]
      by_cases hd : (p - 1) ∣ m
      · have hm0 : m = 0 := by
          rcases Nat.lt_or_ge m 2 with h2 | h2
          · interval_cases m
            · rfl
            · exact absurd hd (fun hdd => by have := Nat.le_of_dvd (by norm_num) hdd; omega)
          · exact absurd ⟨hd, h2⟩ hbc
        rw [hm0, bernoulli_zero]; simp
      · exact VonStaudt.norm_bernoulli_le_one_of_not_dvd hp5 m hd
    have hd3 : ‖(d k s : ℚ_[p])‖ ≤ (p : ℝ) ^ ((0 : ℤ) + padicValNat p (k + 1)) := by
      refine le_trans (norm_d_le3 k s (by omega)) ?_
      rw [← hm, zpow_add₀ hp0ne]
      exact mul_le_mul_of_nonneg_right hbern (by positivity)
    calc ‖(a k : ℚ_[p])‖ * ‖d k s‖
        ≤ (p : ℝ) ^ ((padicValNat p k : ℤ) - k)
            * (p : ℝ) ^ ((0 : ℤ) + padicValNat p (k + 1)) :=
          mul_le_mul ha3 hd3 (norm_nonneg _) (by positivity)
      _ = (p : ℝ) ^ (((padicValNat p k : ℤ) - k) + ((0 : ℤ) + padicValNat p (k + 1))) := by
          rw [← zpow_add₀ hp0ne]
      _ ≤ (p : ℝ) ^ (-3 : ℤ) := by
          apply zpow_le_zpow_right₀ hp1
          have := exp_bound hp5 hk3 0 (Or.inl rfl)
          omega

/-- The sharp bound on `‖Sig s‖` for `s ≥ 2`. -/
lemma norm_Sig_le3 (hp5 : 5 ≤ p) (s : ℕ) (hs : 2 ≤ s) :
    ‖Sig (p := p) s‖ ≤ (p : ℝ) ^ (-3 : ℤ) := by
  rw [Sig]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) (fun k => ?_)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [a, Nat.zero_sub, pow_zero, Nat.cast_zero, one_mul, div_zero, zero_mul, mul_zero,
      norm_zero]
    positivity
  · exact norm_ad_le3 hp5 k s hk hs

/-! ## Part B: the log-difference bound `‖L‖ ≤ p^{-3r}` -/

/-- `∑' t ‖Sig t‖` is summable. -/
lemma summable_Sig_norm (hp5 : 5 ≤ p) : Summable (fun t : ℕ => ‖Sig (p := p) t‖) := by
  refine Summable.of_nonneg_of_le (fun t => norm_nonneg _) (fun t => ?_) (summable_Sig_norm_mul hp5)
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ t := one_le_pow₀ (by norm_num)
  calc ‖Sig (p := p) t‖ = ‖Sig (p := p) t‖ * 1 := (mul_one _).symm
    _ ≤ ‖Sig (p := p) t‖ * (2 : ℝ) ^ t := by gcongr

/-- `Summable (fun t => Sig t * x^t)` for `‖x‖ ≤ 1`. -/
lemma summable_Sig_mul_pow (hp5 : 5 ≤ p) (x : ℚ_[p]) (hx : ‖x‖ ≤ 1) :
    Summable (fun t : ℕ => Sig (p := p) t * x ^ t) := by
  refine Summable.of_norm_bounded (summable_Sig_norm hp5) (fun t => ?_)
  rw [norm_mul, norm_pow]
  calc ‖Sig (p := p) t‖ * ‖x‖ ^ t ≤ ‖Sig (p := p) t‖ * 1 := by
        gcongr
        exact pow_le_one₀ (norm_nonneg _) hx
    _ = ‖Sig (p := p) t‖ := mul_one _

/-- The norm of a finite sum of `t`-th powers of naturals is `≤ 1`. -/
lemma norm_sum_pow_le {ι : Type*} (s : Finset ι) (f : ι → ℕ) (t : ℕ) :
    ‖∑ i ∈ s, ((f i : ℚ_[p])) ^ t‖ ≤ 1 := by
  rw [show (∑ i ∈ s, ((f i : ℚ_[p])) ^ t) = ((∑ i ∈ s, (f i) ^ t : ℕ) : ℚ_[p]) by push_cast; ring]
  exact VonStaudt.norm_nat_le_one _

/-- `g (↑j) = padicLog (w j)`. -/
lemma g_eq_padicLog_w (j : ℕ) : g (↑j : ℤ_[p]) = padicLog (w (p := p) j) := by
  rw [g, oneAddWx_natCast]; rfl

/-- `padicLog (Aprod s cnt - 1) = ∑ i ∈ s, G (↑(cnt i))`. -/
lemma padicLog_Aprod_eq_sum_G (hp5 : 5 ≤ p) {ι : Type*} (s : Finset ι) (cnt : ι → ℕ) :
    padicLog (Aprod (p := p) s cnt - 1) = ∑ i ∈ s, G (↑(cnt i) : ℚ_[p]) := by
  rw [padicLog_Aprod hp5, Finset.sum_sigma]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [G_natCast hp5]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact (g_eq_padicLog_w j).symm

/-- `padicLog (Aprod s cnt - 1) = ∑' t, Sig t * (∑ i ∈ s, (cnt i)^t)`. -/
lemma padicLog_Aprod_tsum (hp5 : 5 ≤ p) {ι : Type*} (s : Finset ι) (cnt : ι → ℕ) :
    padicLog (Aprod (p := p) s cnt - 1)
      = ∑' t : ℕ, Sig (p := p) t * (∑ i ∈ s, ((cnt i : ℚ_[p])) ^ t) := by
  rw [padicLog_Aprod_eq_sum_G hp5,
    show (∑ i ∈ s, G (↑(cnt i) : ℚ_[p]))
        = ∑ i ∈ s, ∑' t : ℕ, Sig (p := p) t * ((cnt i : ℚ_[p])) ^ t from
      Finset.sum_congr rfl (fun i _ => G_eq _),
    ← Summable.tsum_finsetSum
      (fun i (_ : i ∈ s) => summable_Sig_mul_pow hp5 _ (VonStaudt.norm_nat_le_one _))]
  exact tsum_congr (fun t => by rw [Finset.mul_sum])

/-- The log-difference bound. -/
lemma logdiff_le (hp5 : 5 ≤ p) {ι : Type*} (num den : Finset ι) (c : ι → ℕ)
    (n r : ℕ) (hnp : ¬ p ∣ n) (hr : 1 ≤ r)
    (hbal : ∑ i ∈ num, c i = ∑ i ∈ den, c i) :
    ‖padicLog (Aprod (p := p) num (fun i => c i * (n * p ^ (r - 1))) - 1)
        - padicLog (Aprod (p := p) den (fun i => c i * (n * p ^ (r - 1))) - 1)‖
      ≤ (p : ℝ) ^ (-((3 * r : ℕ) : ℤ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_le
  have hinv_le_one : (p : ℝ)⁻¹ ≤ 1 := by rw [inv_le_one₀ hp0]; exact hp1
  set M' := n * p ^ (r - 1) with hM'
  -- norm of M'
  have hM'norm : ‖((M' : ℕ) : ℚ_[p])‖ = ((p : ℝ)⁻¹) ^ (r - 1) := by
    rw [hM']; push_cast
    rw [norm_mul, norm_pow, norm_natCast_eq_one hnp, one_mul, Padic.norm_p]
  have hM1 : ‖((M' : ℕ) : ℚ_[p])‖ ≤ 1 := by
    rw [hM'norm]; exact pow_le_one₀ (by positivity) hinv_le_one
  -- expand both logs
  have key : ∀ s : Finset ι,
      padicLog (Aprod (p := p) s (fun i => c i * M') - 1)
        = ∑' t : ℕ, Sig (p := p) t
            * ((M' : ℚ_[p]) ^ t * (∑ i ∈ s, ((c i : ℚ_[p])) ^ t)) := by
    intro s
    rw [padicLog_Aprod_tsum hp5]
    refine tsum_congr (fun t => ?_)
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    push_cast; ring
  -- summability of the two tsum families
  have hsummand : ∀ (s : Finset ι) (t : ℕ),
      ‖Sig (p := p) t * ((M' : ℚ_[p]) ^ t * (∑ i ∈ s, ((c i : ℚ_[p])) ^ t))‖
        ≤ ‖Sig (p := p) t‖ := by
    intro s t
    rw [norm_mul, norm_mul, norm_pow]
    calc ‖Sig (p := p) t‖ * (‖((M' : ℕ) : ℚ_[p])‖ ^ t * ‖∑ i ∈ s, ((c i : ℚ_[p])) ^ t‖)
        ≤ ‖Sig (p := p) t‖ * (1 * 1) := by
          gcongr
          · exact pow_le_one₀ (norm_nonneg _) hM1
          · exact norm_sum_pow_le s c t
      _ = ‖Sig (p := p) t‖ := by ring
  have hsA : Summable (fun t : ℕ =>
      Sig (p := p) t * ((M' : ℚ_[p]) ^ t * (∑ i ∈ num, ((c i : ℚ_[p])) ^ t))) :=
    Summable.of_norm_bounded (summable_Sig_norm hp5) (fun t => hsummand num t)
  have hsB : Summable (fun t : ℕ =>
      Sig (p := p) t * ((M' : ℚ_[p]) ^ t * (∑ i ∈ den, ((c i : ℚ_[p])) ^ t))) :=
    Summable.of_norm_bounded (summable_Sig_norm hp5) (fun t => hsummand den t)
  rw [key num, key den, ← Summable.tsum_sub hsA hsB]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) (fun t => ?_)
  rcases t with _ | _ | _ | u
  · -- t = 0
    rw [Sig_zero]
    simp only [zero_mul, sub_zero, norm_zero]
    positivity
  · -- t = 1
    have h1 : (∑ i ∈ num, ((c i : ℚ_[p])) ^ 1) = ∑ i ∈ den, ((c i : ℚ_[p])) ^ 1 := by
      simp only [pow_one]
      have en : (∑ i ∈ num, (c i : ℚ_[p])) = ((∑ i ∈ num, c i : ℕ) : ℚ_[p]) := by push_cast; ring
      have ed : (∑ i ∈ den, (c i : ℚ_[p])) = ((∑ i ∈ den, c i : ℕ) : ℚ_[p]) := by push_cast; ring
      rw [en, ed, hbal]
    rw [h1, sub_self, norm_zero]; positivity
  · -- t = 2
    rw [Sig_two_eq_zero hp5]
    simp only [zero_mul, sub_zero, norm_zero]
    positivity
  · -- t = u + 3
    have hfac :
        Sig (p := p) (u + 3) * ((M' : ℚ_[p]) ^ (u + 3) * ∑ i ∈ num, ((c i : ℚ_[p])) ^ (u + 3))
          - Sig (p := p) (u + 3) * ((M' : ℚ_[p]) ^ (u + 3) * ∑ i ∈ den, ((c i : ℚ_[p])) ^ (u + 3))
        = Sig (p := p) (u + 3) * (M' : ℚ_[p]) ^ (u + 3)
            * ((∑ i ∈ num, ((c i : ℚ_[p])) ^ (u + 3)) - (∑ i ∈ den, ((c i : ℚ_[p])) ^ (u + 3))) := by
      ring
    rw [hfac, norm_mul, norm_mul, norm_pow, hM'norm]
    have hSig : ‖Sig (p := p) (u + 3)‖ ≤ ((p : ℝ)⁻¹) ^ 3 := by
      have hz3 : ((p : ℝ)⁻¹) ^ 3 = (p : ℝ) ^ (-3 : ℤ) := by rw [rpow_neg]; norm_num
      rw [hz3]; exact norm_Sig_le3 hp5 (u + 3) (by omega)
    have hdiff : ‖(∑ i ∈ num, ((c i : ℚ_[p])) ^ (u + 3))
        - (∑ i ∈ den, ((c i : ℚ_[p])) ^ (u + 3))‖ ≤ 1 := by
      rw [sub_eq_add_neg]
      refine le_trans (IsUltrametricDist.norm_add_le_max _ _) ?_
      rw [norm_neg]
      exact max_le (norm_sum_pow_le num c (u + 3)) (norm_sum_pow_le den c (u + 3))
    calc ‖Sig (p := p) (u + 3)‖ * (((p : ℝ)⁻¹) ^ (r - 1)) ^ (u + 3)
            * ‖(∑ i ∈ num, ((c i : ℚ_[p])) ^ (u + 3))
                - (∑ i ∈ den, ((c i : ℚ_[p])) ^ (u + 3))‖
        ≤ ((p : ℝ)⁻¹) ^ 3 * (((p : ℝ)⁻¹) ^ (r - 1)) ^ (u + 3) * 1 := by
          gcongr
      _ = ((p : ℝ)⁻¹) ^ (3 + (r - 1) * (u + 3)) := by rw [mul_one, ← pow_mul, ← pow_add]
      _ ≤ ((p : ℝ)⁻¹) ^ (3 * r) := by
          apply pow_le_pow_of_le_one (by positivity) hinv_le_one
          have hle : (r - 1) * 3 ≤ (r - 1) * (u + 3) :=
            Nat.mul_le_mul (le_refl (r - 1)) (by omega)
          omega
      _ = (p : ℝ) ^ (-((3 * r : ℕ) : ℤ)) := rpow_neg (3 * r)

/-! ## Part C: divisibility from a log-difference bound -/

/-- If `u, v` are close to `1` and their log-difference is divisible by `p^V`, then `p^V ∣ u - v`. -/
lemma dvd_sub_of_logdiff (hp5 : 5 ≤ p) (u v : ℤ_[p])
    (hu : ‖u - 1‖ < 1) (hv : ‖v - 1‖ < 1) (V : ℕ)
    (hL : ‖padicLog (u - 1) - padicLog (v - 1)‖ ≤ (p : ℝ) ^ (-(V : ℤ))) :
    (p : ℤ_[p]) ^ V ∣ (u - v) := by
  have hp3 : 3 ≤ p := by omega
  have hvnorm : ‖v‖ = 1 := by
    have : ‖v‖ = ‖(v - 1) + 1‖ := by ring_nf
    rw [this]
    have h1 : ‖((1 : ℤ_[p]))‖ = 1 := norm_one
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (x := v - 1) (y := (1 : ℤ_[p])) (by rw [h1]; exact ne_of_lt hv)
    rw [this, h1]; exact max_eq_right (le_of_lt hv)
  set vinv : ℤ_[p] := PadicInt.inv v with hvinv
  have hvvinv : v * vinv = 1 := PadicInt.mul_inv hvnorm
  set r : ℤ_[p] := u * vinv with hr
  have hrsub : r - 1 = (u - v) * vinv := by
    rw [hr]
    have : u * vinv - 1 = u * vinv - v * vinv := by rw [hvvinv]
    rw [this]; ring
  have hvinv_norm : ‖vinv‖ = 1 := by
    have := congrArg norm hvvinv
    rw [norm_mul, hvnorm, one_mul, norm_one] at this; exact this
  have huvnorm : ‖u - v‖ < 1 := by
    calc ‖u - v‖ = ‖(u - 1) - (v - 1)‖ := by ring_nf
      _ ≤ max ‖u - 1‖ ‖v - 1‖ := norm_sub_le_max' _ _
      _ < 1 := max_lt hu hv
  have hrsubnorm : ‖r - 1‖ < 1 := by
    rw [hrsub, norm_mul, hvinv_norm, mul_one]; exact huvnorm
  have hrv : r * v = u := by rw [hr]; rw [mul_assoc, mul_comm vinv v, hvvinv, mul_one]
  have hmul := padicLog_mul hp3 (r - 1) (v - 1) hrsubnorm hv
  have hexp : (r - 1) + (v - 1) + (r - 1) * (v - 1) = r * v - 1 := by ring
  rw [hexp, hrv] at hmul
  have hlogr : padicLog (r - 1) = padicLog (u - 1) - padicLog (v - 1) := by rw [hmul]; ring
  have hlogr_le : ‖padicLog (r - 1)‖ ≤ (p : ℝ) ^ (-(V : ℤ)) := by rw [hlogr]; exact hL
  have hdvd : (p : ℤ_[p]) ^ V ∣ (r - 1) :=
    sub_one_dvd_of_padicLog hp3 r hrsubnorm V hlogr_le
  have huv : u - v = (r - 1) * v := by
    rw [hrsub, mul_assoc]
    rw [show vinv * v = 1 from by rw [mul_comm]; exact hvvinv, mul_one]
  rw [huv]; exact hdvd.mul_right v

/-! ## The strong supercongruence mod `p^{3r}` -/

/-- **Strong balanced supercongruence (mod `p^{3r}`).** -/
theorem strong_supercongruence (hp5 : 5 ≤ p) {ι : Type*}
    (num den : Finset ι) (c : ι → ℕ) (n r : ℕ) (hnp : ¬ p ∣ n) (hr : 1 ≤ r)
    (hbal : ∑ i ∈ num, c i = ∑ i ∈ den, c i) :
    (p : ℤ_[p]) ^ (3 * r) ∣
      ((∏ i ∈ num, Wfac (c i * (n * p ^ r))) - (∏ i ∈ den, Wfac (c i * (n * p ^ r)))) := by
  have hWeq : n * p ^ r = p * (n * p ^ (r - 1)) := by
    have hpr : p ^ r = p * p ^ (r - 1) := by
      conv_lhs => rw [show r = 1 + (r - 1) from by omega]
      rw [pow_add, pow_one]
    rw [hpr]; ring
  rw [Wprod_eq (n * p ^ r) (n * p ^ (r - 1)) hWeq num c,
      Wprod_eq (n * p ^ r) (n * p ^ (r - 1)) hWeq den c]
  have hexp : (∑ i ∈ num, c i * (n * p ^ (r - 1))) = (∑ i ∈ den, c i * (n * p ^ (r - 1))) := by
    rw [← Finset.sum_mul, ← Finset.sum_mul, hbal]
  rw [hexp, ← mul_sub]
  have hdvd : (p : ℤ_[p]) ^ (3 * r) ∣
      (Aprod (p := p) num (fun i => c i * (n * p ^ (r - 1)))
        - Aprod (p := p) den (fun i => c i * (n * p ^ (r - 1)))) := by
    refine dvd_sub_of_logdiff hp5 _ _
      (norm_Aprod_sub_one_lt hp5 num _) (norm_Aprod_sub_one_lt hp5 den _) (3 * r) ?_
    exact logdiff_le hp5 num den c n r hnp hr hbal
  exact hdvd.mul_left _

end PStrong
