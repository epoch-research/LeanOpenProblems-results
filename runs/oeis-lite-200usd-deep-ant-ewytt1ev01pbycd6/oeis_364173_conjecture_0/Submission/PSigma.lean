import FormalConjectures.Util.ProblemImports
import Submission.PLog
import Submission.PKaz
import Submission.VonStaudt

/-!
# A p-adic vanishing identity: `Σ₂ = 0`

We prove the "second-order coefficient vanishes" identity underlying a
Kazandzidis-type supercongruence, namely that
`∑' m, (-1)^m p^{m+1} Hz(m+1) bernoulli(m) = 0` in `ℚ_[p]` for `p ≥ 5`.

The strategy follows a reflection/oddness argument for an entire function `G`
on `ℤ_[p]` whose power-series coefficients are the sums `Σ s`.
-/

namespace PSigma

open PLog PKaz
open scoped Topology ENNReal NNReal
open FormalMultilinearSeries

variable {p : ℕ} [hp : Fact p.Prime]

/-! ## Step 1: the reflection product identity -/

/-- The block factor as a function of a `p`-adic integer variable `x`:
`∏_{i=1}^{p-1} (1 + x·p·i⁻¹)`. -/
noncomputable def oneAddWx (x : ℤ_[p]) : ℤ_[p] :=
  ∏ i ∈ Finset.Icc 1 (p - 1), (1 + x * (p : ℤ_[p]) * iv i)

/-- Each factor rewritten as `(i + x·p)·i⁻¹`. -/
lemma oneAddWx_eq (x : ℤ_[p]) :
    oneAddWx x
      = (∏ i ∈ Finset.Icc 1 (p - 1), ((i : ℤ_[p]) + x * (p : ℤ_[p])))
        * (∏ i ∈ Finset.Icc 1 (p - 1), iv i) := by
  rw [oneAddWx, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finset.mem_Icc] at hi
  have hnd : ¬ p ∣ i := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
  have hiv : (i : ℤ_[p]) * iv i = 1 := mul_iv_cancel hnd
  linear_combination (-1 : ℤ_[p]) * hiv

/-- The reflected product `∏ (i + (-1-x)p)` equals `∏ (i + xp)` (reindex `i ↦ p - i`,
using that `p - 1` is even). -/
lemma refl_prod (hp5 : 5 ≤ p) (x : ℤ_[p]) :
    ∏ i ∈ Finset.Icc 1 (p - 1), ((i : ℤ_[p]) + (-1 - x) * (p : ℤ_[p]))
      = ∏ i ∈ Finset.Icc 1 (p - 1), ((i : ℤ_[p]) + x * (p : ℤ_[p])) := by
  have hstep :
      ∏ i ∈ Finset.Icc 1 (p - 1), ((i : ℤ_[p]) + (-1 - x) * (p : ℤ_[p]))
        = ∏ i ∈ Finset.Icc 1 (p - 1), (-((i : ℤ_[p]) + x * (p : ℤ_[p]))) := by
    refine Finset.prod_nbij' (fun i => p - i) (fun i => p - i) ?_ ?_ ?_ ?_ ?_
    · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
    · intro a ha
      simp only [Finset.mem_Icc] at ha
      have hcast : ((p - a : ℕ) : ℤ_[p]) = (p : ℤ_[p]) - (a : ℤ_[p]) := by
        rw [Nat.cast_sub (by omega)]
      rw [hcast]; ring
  rw [hstep, Finset.prod_neg]
  have hcard : (Finset.Icc 1 (p - 1)).card = p - 1 := by rw [Nat.card_Icc]; omega
  rw [hcard]
  have heven : Even (p - 1) := by
    have hodd : Odd p := hp.out.odd_of_ne_two (by omega)
    rcases hodd with ⟨m, hm⟩; exact ⟨m, by omega⟩
  rw [heven.neg_one_pow, one_mul]

/-- **Reflection identity:** `oneAddWx x = oneAddWx (-1 - x)`. -/
lemma oneAddWx_reflection (hp5 : 5 ≤ p) (x : ℤ_[p]) :
    oneAddWx x = oneAddWx (-1 - x) := by
  rw [oneAddWx_eq x, oneAddWx_eq (-1 - x), refl_prod hp5 x]

/-- Each factor `x·p·i⁻¹` has norm `< 1`. -/
lemma norm_wx_lt (hp5 : 5 ≤ p) (x : ℤ_[p]) (i : ℕ) :
    ‖x * (p : ℤ_[p]) * iv i‖ < 1 := by
  have h1 : ‖x * (p : ℤ_[p]) * iv i‖ ≤ ‖(p : ℤ_[p])‖ := by
    calc ‖x * (p : ℤ_[p]) * iv i‖ = ‖x‖ * ‖(p : ℤ_[p])‖ * ‖iv i‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ 1 * ‖(p : ℤ_[p])‖ * 1 := by
          gcongr
          · exact PadicInt.norm_le_one x
          · exact PadicInt.norm_le_one _
      _ = ‖(p : ℤ_[p])‖ := by ring
  refine lt_of_le_of_lt h1 ?_
  rw [PadicInt.norm_p, inv_lt_one₀ (by exact_mod_cast hp.out.pos)]
  exact_mod_cast (by omega : 1 < p)

lemma norm_oneAddWx_sub_one_lt (hp5 : 5 ≤ p) (x : ℤ_[p]) :
    ‖oneAddWx x - 1‖ < 1 := by
  rw [oneAddWx]
  exact norm_prod_one_add_sub_one_lt _ _ (fun i _ => norm_wx_lt hp5 x i)

/-- The function `g x = log(oneAddWx x - 1)`. -/
noncomputable def g (x : ℤ_[p]) : ℚ_[p] := padicLog (oneAddWx x - 1)

/-- **Reflection of `g`:** `g x = g (-1 - x)`. -/
lemma g_reflection (hp5 : 5 ≤ p) (x : ℤ_[p]) : g x = g (-1 - x) := by
  rw [g, g, oneAddWx_reflection hp5 x]

/-! ## Step 2: coefficients `a`, `d`, and the sums `Sig` -/

/-- The `k`-th coefficient of the power series `g`. -/
noncomputable def a (k : ℕ) : ℚ_[p] :=
  (-1) ^ (k - 1) * (p : ℚ_[p]) ^ k * ((Hz k : ℤ_[p]) : ℚ_[p]) / (k : ℚ_[p])

/-- The Faulhaber coefficient: coefficient of `N^s` in `∑_{t<N} t^k`. -/
noncomputable def d (k s : ℕ) : ℚ_[p] :=
  if s = 0 then 0
  else ((bernoulli (k + 1 - s) : ℚ) : ℚ_[p]) * ((Nat.choose (k + 1) s : ℕ) : ℚ_[p])
        / ((k + 1 : ℕ) : ℚ_[p])

lemma norm_a_le (k : ℕ) : ‖(a k : ℚ_[p])‖ ≤ (k : ℝ) * ((p : ℝ)⁻¹) ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [a]
  · rw [a, norm_div, norm_mul, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow,
      one_mul, Padic.norm_p, PadicInt.padic_norm_e_of_padicInt, div_eq_mul_inv]
    calc ((p : ℝ)⁻¹) ^ k * ‖(Hz k : ℤ_[p])‖ * ‖(k : ℚ_[p])‖⁻¹
        ≤ ((p : ℝ)⁻¹) ^ k * 1 * (k : ℝ) := by
          gcongr
          · exact norm_Hz_le_one k
          · exact norm_natCast_inv_le k
      _ = (k : ℝ) * ((p : ℝ)⁻¹) ^ k := by ring

lemma norm_d_le (hp5 : 5 ≤ p) (k s : ℕ) : ‖(d k s : ℚ_[p])‖ ≤ (p : ℝ) * ((k : ℝ) + 1) := by
  rw [d]
  split_ifs with h
  · simp only [norm_zero]; positivity
  · rw [norm_div, norm_mul, div_eq_mul_inv]
    calc ‖((bernoulli (k + 1 - s) : ℚ) : ℚ_[p])‖ * ‖((Nat.choose (k + 1) s : ℕ) : ℚ_[p])‖
            * ‖((k + 1 : ℕ) : ℚ_[p])‖⁻¹
        ≤ (p : ℝ) * 1 * ((k : ℝ) + 1) := by
          gcongr
          · exact VonStaudt.norm_bernoulli_le hp5 _
          · exact VonStaudt.norm_nat_le_one _
          · calc ‖((k + 1 : ℕ) : ℚ_[p])‖⁻¹ ≤ ((k + 1 : ℕ) : ℝ) := norm_natCast_inv_le _
              _ = (k : ℝ) + 1 := by push_cast; ring
      _ = (p : ℝ) * ((k : ℝ) + 1) := by ring

lemma norm_ad_le (hp5 : 5 ≤ p) (k s : ℕ) :
    ‖(a k * d k s : ℚ_[p])‖ ≤ (p : ℝ) * (k : ℝ) * ((k : ℝ) + 1) * ((p : ℝ)⁻¹) ^ k := by
  rw [norm_mul]
  calc ‖a k‖ * ‖d k s‖
      ≤ ((k : ℝ) * ((p : ℝ)⁻¹) ^ k) * ((p : ℝ) * ((k : ℝ) + 1)) := by
        apply mul_le_mul (norm_a_le k) (norm_d_le hp5 k s) (norm_nonneg _) (by positivity)
    _ = (p : ℝ) * (k : ℝ) * ((k : ℝ) + 1) * ((p : ℝ)⁻¹) ^ k := by ring

lemma summable_cbound :
    Summable (fun k : ℕ => (p : ℝ) * (k : ℝ) * ((k : ℝ) + 1) * ((p : ℝ)⁻¹) ^ k) := by
  have hr : ‖((p : ℝ)⁻¹)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_lt_one₀ (by exact_mod_cast hp.out.pos)]
    exact_mod_cast hp.out.one_lt
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hr
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have heq : (fun k : ℕ => (p : ℝ) * (k : ℝ) * ((k : ℝ) + 1) * ((p : ℝ)⁻¹) ^ k)
      = fun k : ℕ => (p : ℝ) * ((k : ℝ) ^ 2 * ((p : ℝ)⁻¹) ^ k)
          + (p : ℝ) * ((k : ℝ) ^ 1 * ((p : ℝ)⁻¹) ^ k) := by
    funext k; ring
  rw [heq]
  exact (h2.mul_left (p : ℝ)).add (h1.mul_left (p : ℝ))

lemma summable_ad (hp5 : 5 ≤ p) (s : ℕ) : Summable (fun k : ℕ => (a k * d k s : ℚ_[p])) :=
  Summable.of_norm_bounded summable_cbound (fun k => norm_ad_le hp5 k s)

/-- The `s`-th power-series coefficient of the summed function `G`. -/
noncomputable def Sig (s : ℕ) : ℚ_[p] := ∑' k, a k * d k s

lemma d_eq_zero_of_lt {k s : ℕ} (h : k + 1 < s) : d k s = (0 : ℚ_[p]) := by
  rw [d, if_neg (by omega : s ≠ 0), Nat.choose_eq_zero_of_lt h]
  simp

lemma Sig_zero : Sig (p := p) 0 = 0 := by
  rw [Sig]
  have : (fun k => a k * d k 0) = fun _ : ℕ => (0 : ℚ_[p]) := by
    funext k; rw [d, if_pos rfl, mul_zero]
  rw [this, tsum_zero]

/-- The uniform bound `p·k·(k+1)·p^{-k}`. -/
noncomputable def cbnd (p k : ℕ) : ℝ := (p : ℝ) * (k : ℝ) * ((k : ℝ) + 1) * ((p : ℝ)⁻¹) ^ k

lemma cbnd_nonneg (k : ℕ) : 0 ≤ cbnd p k := by rw [cbnd]; positivity

lemma norm_ad_le' (hp5 : 5 ≤ p) (k s : ℕ) : ‖(a k * d k s : ℚ_[p])‖ ≤ cbnd p k :=
  norm_ad_le hp5 k s

lemma cbnd_step (hp5 : 5 ≤ p) {k : ℕ} (hk : 1 ≤ k) : cbnd p (k + 1) ≤ cbnd p k := by
  have hr : (p : ℝ)⁻¹ ≤ 1 / 5 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp5)
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  set r := (p : ℝ)⁻¹ with hrdef
  have hr0 : 0 < r := by rw [hrdef]; positivity
  have hrk : 0 < r ^ k := by positivity
  have hkey : ((k : ℝ) + 2) * r ≤ (k : ℝ) := by
    have h1 : ((k : ℝ) + 2) * r ≤ ((k : ℝ) + 2) * (1 / 5) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    nlinarith [h1, hk1]
  rw [cbnd, cbnd, pow_succ]
  push_cast
  have hfac : 0 ≤ (p : ℝ) * ((k : ℝ) + 1) * r ^ k := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hkey hfac, hrk, hp0]

lemma cbnd_anti (hp5 : 5 ≤ p) : ∀ {m n : ℕ}, 1 ≤ m → m ≤ n → cbnd p n ≤ cbnd p m := by
  intro m n hm hmn
  induction n, hmn using Nat.le_induction with
  | base => exact le_refl _
  | succ n hmn ih => exact le_trans (cbnd_step hp5 (le_trans hm hmn)) ih

/-- Uniform-in-`k` bound giving `‖Sig s‖ ≤ cbnd (max 1 (s-1))`. -/
lemma norm_Sig_le (hp5 : 5 ≤ p) {s : ℕ} (hs : 1 ≤ s) :
    ‖Sig (p := p) s‖ ≤ cbnd p (max 1 (s - 1)) := by
  rw [Sig]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (cbnd_nonneg _) (fun k => ?_)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [a, Nat.zero_sub, pow_zero, Nat.cast_zero, one_mul, div_zero, zero_mul, mul_zero,
      norm_zero]
    exact cbnd_nonneg _
  · by_cases hks : k + 1 < s
    · rw [d_eq_zero_of_lt hks, mul_zero, norm_zero]; exact cbnd_nonneg _
    · refine le_trans (norm_ad_le' hp5 k s) ?_
      exact cbnd_anti hp5 (le_max_left _ _) (by omega)

lemma summable_Sig_norm_mul (hp5 : 5 ≤ p) :
    Summable (fun s : ℕ => ‖Sig (p := p) s‖ * (2 : ℝ) ^ s) := by
  apply Summable.comp_nat_add (k := 2)
  -- majorant M s = 4 (s+1)(s+2) (2/p)^s
  have hq : ‖((2 : ℝ) / p)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_lt_one (by exact_mod_cast hp.out.pos)]
    exact_mod_cast (by omega : 2 < p)
  have hM : Summable (fun s : ℕ => (4 : ℝ) * ((s : ℝ) + 1) * ((s : ℝ) + 2) * ((2 : ℝ) / p) ^ s) := by
    have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hq
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hq
    have h0 := summable_pow_mul_geometric_of_norm_lt_one 0 hq
    have heq : (fun s : ℕ => (4 : ℝ) * ((s : ℝ) + 1) * ((s : ℝ) + 2) * ((2 : ℝ) / p) ^ s)
        = fun s : ℕ => (4 : ℝ) * ((s : ℝ) ^ 2 * ((2 : ℝ) / p) ^ s)
            + ((12 : ℝ) * ((s : ℝ) ^ 1 * ((2 : ℝ) / p) ^ s)
              + (8 : ℝ) * ((s : ℝ) ^ 0 * ((2 : ℝ) / p) ^ s)) := by
      funext s; ring
    rw [heq]
    exact (h2.mul_left 4).add ((h1.mul_left 12).add (h0.mul_left 8))
  refine hM.of_nonneg_of_le (fun s => by positivity) (fun s => ?_)
  -- ‖Sig (s+2)‖ * 2^(s+2) ≤ 4 (s+1)(s+2) (2/p)^s
  have hb : ‖Sig (p := p) (s + 2)‖ ≤ cbnd p (s + 1) := by
    have := norm_Sig_le hp5 (s := s + 2) (by omega)
    simpa [show max 1 (s + 2 - 1) = s + 1 by omega] using this
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  calc ‖Sig (p := p) (s + 2)‖ * (2 : ℝ) ^ (s + 2)
      ≤ cbnd p (s + 1) * (2 : ℝ) ^ (s + 2) := by
        apply mul_le_mul_of_nonneg_right hb (by positivity)
    _ = (4 : ℝ) * ((s : ℝ) + 1) * ((s : ℝ) + 2) * ((2 : ℝ) / p) ^ s := by
        have hpne : (p : ℝ) ≠ 0 := ne_of_gt hp0
        rw [cbnd]
        push_cast
        rw [show ((p : ℝ)⁻¹) ^ (s + 1) = ((p : ℝ) ^ (s + 1))⁻¹ from inv_pow _ _, div_pow]
        field_simp
        ring

lemma two_le_radius (hp5 : 5 ≤ p) : (2 : ℝ≥0∞) ≤ (ofScalars ℚ_[p] (Sig (p := p))).radius := by
  have hs : Summable (fun n => ‖(ofScalars ℚ_[p] (Sig (p := p))) n‖ * ((2 : ℝ≥0) : ℝ) ^ n) := by
    have := summable_Sig_norm_mul (p := p) hp5
    refine this.congr (fun n => ?_)
    rw [ofScalars_norm]; norm_num
  have := (ofScalars ℚ_[p] (Sig (p := p))).le_radius_of_summable_norm hs
  simpa using this

/-- The entire function `G x = ∑' s, Sig s · x^s`. -/
noncomputable def G : ℚ_[p] → ℚ_[p] := (FormalMultilinearSeries.ofScalars ℚ_[p] (Sig (p := p))).sum

lemma G_eq (x : ℚ_[p]) : G x = ∑' s, Sig s * x ^ s := by
  rw [G, show (FormalMultilinearSeries.ofScalars ℚ_[p] (Sig (p := p))).sum
      = FormalMultilinearSeries.ofScalarsSum Sig from rfl,
    FormalMultilinearSeries.ofScalars_sum_eq]
  exact tsum_congr (fun s => by rw [smul_eq_mul])

lemma radius_pos (hp5 : 5 ≤ p) : 0 < (FormalMultilinearSeries.ofScalars ℚ_[p] (Sig (p := p))).radius :=
  lt_of_lt_of_le (by norm_num) (two_le_radius hp5)

lemma G_hasFPS (hp5 : 5 ≤ p) :
    HasFPowerSeriesOnBall (G (p := p)) (FormalMultilinearSeries.ofScalars ℚ_[p] (Sig (p := p))) 0
      (FormalMultilinearSeries.ofScalars ℚ_[p] (Sig (p := p))).radius :=
  (FormalMultilinearSeries.ofScalars ℚ_[p] (Sig (p := p))).hasFPowerSeriesOnBall (radius_pos hp5)

/-! ## Step 3: power series of `g` at naturals, Faulhaber, Fubini -/

lemma oneAddWx_natCast (t : ℕ) : oneAddWx (↑t : ℤ_[p]) = oneAddW t := by
  rw [oneAddWx, oneAddW]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [wfac]; push_cast; ring

/-- Summability of the `g`-power-series for any `x` in the closed unit ball. -/
lemma summable_apow (x : ℚ_[p]) (hx : ‖x‖ ≤ 1) : Summable (fun k => a k * x ^ k) := by
  have hr : ‖((p : ℝ)⁻¹)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_lt_one₀ (by exact_mod_cast hp.out.pos)]
    exact_mod_cast hp.out.one_lt
  apply Summable.of_norm_bounded (g := fun k : ℕ => (k : ℝ) * ((p : ℝ)⁻¹) ^ k)
  · have := summable_pow_mul_geometric_of_norm_lt_one 1 hr
    simpa using this
  · intro k
    rw [norm_mul, norm_pow]
    calc ‖a k‖ * ‖x‖ ^ k
        ≤ ‖a k‖ * 1 := by
          apply mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hx) (norm_nonneg _)
      _ = ‖a k‖ := mul_one _
      _ ≤ (k : ℝ) * ((p : ℝ)⁻¹) ^ k := norm_a_le k

/-- **Power series form of `g` at naturals:** `g t = ∑' k, a k · t^k`. -/
lemma g_series (hp5 : 5 ≤ p) (t : ℕ) :
    g (↑t : ℤ_[p]) = ∑' k, a k * ((t : ℚ_[p])) ^ k := by
  have hp3 : 3 ≤ p := by omega
  have hg : g (↑t : ℤ_[p]) = padicLog (oneAddW t - 1) := by rw [g, oneAddWx_natCast]
  have hlog : padicLog (oneAddW t - 1 : ℤ_[p])
      = ∑' n, ∑ i ∈ Finset.Icc 1 (p - 1), logT (wfac t i) n := by
    rw [oneAddW, padicLog_prod hp3 _ _ (fun i _ => norm_wfac_lt hp5 t i),
      show (∑ i ∈ Finset.Icc 1 (p - 1), padicLog (wfac t i))
          = ∑ i ∈ Finset.Icc 1 (p - 1), ∑' n, logT (wfac t i) n from
        Finset.sum_congr rfl (fun i _ => padicLog_eq_logT _)]
    exact (Summable.tsum_finsetSum
      (fun i _ => summable_logT (wfac t i) (norm_wfac_lt hp5 t i))).symm
  have hterm : ∀ n : ℕ, (∑ i ∈ Finset.Icc 1 (p - 1), logT (wfac t i) n)
      = a (n + 1) * ((t : ℚ_[p])) ^ (n + 1) := by
    intro n
    rw [term_val, a]
    simp only [Nat.add_sub_cancel]
    push_cast
    ring
  rw [hg, hlog, tsum_congr hterm,
    (summable_apow (t : ℚ_[p]) (VonStaudt.norm_nat_le_one t)).tsum_eq_zero_add]
  have h0 : a (0 : ℕ) * ((t : ℚ_[p])) ^ 0 = 0 := by simp [a]
  rw [h0, zero_add]

/-- **Faulhaber (cast to `ℚ_[p]`):** `∑_{t<n} t^k = ∑_{s<k+2} d k s · n^s`. -/
lemma faulhaber (n k : ℕ) :
    ∑ t ∈ Finset.range n, ((t : ℚ_[p])) ^ k
      = ∑ s ∈ Finset.range (k + 2), d k s * ((n : ℚ_[p])) ^ s := by
  have key := sum_range_pow n k
  have hL : (∑ t ∈ Finset.range n, ((t : ℚ_[p])) ^ k)
      = ((∑ t ∈ Finset.range n, ((t : ℚ)) ^ k : ℚ) : ℚ_[p]) := by
    rw [Rat.cast_sum]; exact Finset.sum_congr rfl (fun t _ => by push_cast; ring)
  rw [hL, key, Rat.cast_sum,
    Finset.sum_range_succ' (fun s => d k s * ((n : ℚ_[p])) ^ s) (k + 1),
    show d k 0 * ((n : ℚ_[p])) ^ 0 = 0 from by rw [d, if_pos rfl, zero_mul], add_zero,
    ← Finset.sum_range_reflect (fun s => d k (s + 1) * ((n : ℚ_[p])) ^ (s + 1)) (k + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [d, if_neg (by omega : (k + 1 - 1 - j) + 1 ≠ 0)]
  have e1 : (k + 1 - 1 - j) + 1 = k + 1 - j := by omega
  have e2 : k + 1 - ((k + 1 - 1 - j) + 1) = j := by omega
  have e3 : (k + 1).choose ((k + 1 - 1 - j) + 1) = (k + 1).choose j := by
    rw [e1, Nat.choose_symm (by omega : j ≤ k + 1)]
  rw [e2, e3, e1]
  push_cast
  ring

lemma summable_poly_geom (hp5 : 5 ≤ p) (j : ℕ) :
    Summable (fun k : ℕ => (k : ℝ) ^ j * ((p : ℝ)⁻¹) ^ k) := by
  have hr : ‖((p : ℝ)⁻¹)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_lt_one₀ (by exact_mod_cast hp.out.pos)]
    exact_mod_cast hp.out.one_lt
  exact summable_pow_mul_geometric_of_norm_lt_one j hr

/-- Summability over `ℕ × ℕ` of the double-indexed family used in the Fubini step. -/
lemma summable_F (hp5 : 5 ≤ p) (n : ℕ) :
    Summable (Function.uncurry (fun k s => a k * (d k s * ((n : ℚ_[p])) ^ s))) := by
  have hnn : ∀ ks : ℕ × ℕ, (0 : ℝ) ≤ if ks.2 < ks.1 + 2 then cbnd p ks.1 else 0 := by
    intro ks; split_ifs with h
    · exact cbnd_nonneg _
    · exact le_refl 0
  have hgsum : Summable (fun ks : ℕ × ℕ => if ks.2 < ks.1 + 2 then cbnd p ks.1 else 0) := by
    rw [summable_prod_of_nonneg hnn]
    refine ⟨fun k => ?_, ?_⟩
    · exact summable_of_ne_finset_zero (s := Finset.range (k + 2))
        (fun s hs => by rw [Finset.mem_range] at hs; simp [if_neg (by omega : ¬ s < k + 2)])
    · have hinner : (fun k : ℕ => ∑' s, if s < k + 2 then cbnd p k else 0)
          = fun k : ℕ => ((k : ℝ) + 2) * cbnd p k := by
        funext k
        rw [tsum_eq_sum (s := Finset.range (k + 2))
          (fun s hs => by rw [Finset.mem_range] at hs; simp [if_neg (by omega : ¬ s < k + 2)])]
        have hcongr : ∑ s ∈ Finset.range (k + 2), (if s < k + 2 then cbnd p k else 0)
            = ∑ s ∈ Finset.range (k + 2), cbnd p k := by
          apply Finset.sum_congr rfl
          intro s hs; rw [Finset.mem_range] at hs; rw [if_pos hs]
        rw [hcongr, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast; ring
      rw [hinner]
      have h3 := summable_poly_geom hp5 3
      have h2 := summable_poly_geom hp5 2
      have h1 := summable_poly_geom hp5 1
      have heq : (fun k : ℕ => ((k : ℝ) + 2) * cbnd p k)
          = fun k : ℕ => (p : ℝ) * ((k : ℝ) ^ 3 * ((p : ℝ)⁻¹) ^ k)
              + ((3 * (p : ℝ)) * ((k : ℝ) ^ 2 * ((p : ℝ)⁻¹) ^ k)
                + (2 * (p : ℝ)) * ((k : ℝ) ^ 1 * ((p : ℝ)⁻¹) ^ k)) := by
        funext k; rw [cbnd]; ring
      rw [heq]
      exact (h3.mul_left _).add ((h2.mul_left _).add (h1.mul_left _))
  apply Summable.of_norm_bounded hgsum
  rintro ⟨k, s⟩
  change ‖a k * (d k s * ((n : ℚ_[p])) ^ s)‖ ≤ (if s < k + 2 then cbnd p k else 0)
  by_cases h : s < k + 2
  · rw [if_pos h, norm_mul, norm_mul, norm_pow]
    calc ‖a k‖ * (‖d k s‖ * ‖(n : ℚ_[p])‖ ^ s)
        ≤ ‖a k‖ * (‖d k s‖ * 1) := by
          gcongr
          exact pow_le_one₀ (norm_nonneg _) (VonStaudt.norm_nat_le_one n)
      _ = ‖a k * d k s‖ := by rw [mul_one, norm_mul]
      _ ≤ cbnd p k := norm_ad_le' hp5 k s
  · rw [if_neg h, d_eq_zero_of_lt (by omega), zero_mul, mul_zero, norm_zero]

/-- **Fubini identity:** `G n = ∑_{t<n} g t` on naturals. -/
lemma G_natCast (hp5 : 5 ≤ p) (n : ℕ) :
    G (↑n : ℚ_[p]) = ∑ t ∈ Finset.range n, g (↑t : ℤ_[p]) := by
  have hs0 : ∀ k, ∀ s ∉ Finset.range (k + 2),
      d k s * ((n : ℚ_[p])) ^ s = 0 := by
    intro k s hs; rw [Finset.mem_range] at hs
    rw [d_eq_zero_of_lt (by omega), zero_mul]
  have hswap : (∑ t ∈ Finset.range n, ∑' k, a k * ((t : ℚ_[p])) ^ k)
      = ∑' k, ∑ t ∈ Finset.range n, a k * ((t : ℚ_[p])) ^ k :=
    (Summable.tsum_finsetSum (fun t (_ : t ∈ Finset.range n) =>
      summable_apow (t : ℚ_[p]) (VonStaudt.norm_nat_le_one t))).symm
  have step1 : ∑ t ∈ Finset.range n, g (↑t : ℤ_[p])
      = ∑' k, ∑' s, a k * (d k s * ((n : ℚ_[p])) ^ s) := by
    rw [show (∑ t ∈ Finset.range n, g (↑t : ℤ_[p]))
        = ∑ t ∈ Finset.range n, ∑' k, a k * ((t : ℚ_[p])) ^ k from
      Finset.sum_congr rfl (fun t _ => g_series hp5 t), hswap]
    apply tsum_congr
    intro k
    rw [← Finset.mul_sum, faulhaber n k]
    rw [show (∑ s ∈ Finset.range (k + 2), d k s * ((n : ℚ_[p])) ^ s)
        = ∑' s, d k s * ((n : ℚ_[p])) ^ s from (tsum_eq_sum (hs0 k)).symm]
    rw [← tsum_mul_left]
  have hmarg₂ : ∀ s, Summable (fun k => a k * (d k s * ((n : ℚ_[p])) ^ s)) := by
    intro s
    have := (summable_ad hp5 s).mul_right ((n : ℚ_[p]) ^ s)
    exact this.congr (fun k => by ring)
  have hmarg₁ : ∀ k, Summable (fun s => a k * (d k s * ((n : ℚ_[p])) ^ s)) := by
    intro k
    refine summable_of_ne_finset_zero (s := Finset.range (k + 2)) (fun s hs => ?_)
    simp only [Finset.mem_range, not_lt] at hs
    rw [d_eq_zero_of_lt (by omega), zero_mul, mul_zero]
  rw [step1, ← Summable.tsum_comm' (summable_F hp5 n) hmarg₁ hmarg₂, G_eq]
  apply tsum_congr
  intro s
  rw [Sig, ← tsum_mul_right]
  exact tsum_congr (fun k => by ring)

/-- `G` is continuous on the image of `ℤ_[p]`. -/
lemma continuous_G_coe (hp5 : 5 ≤ p) :
    Continuous (fun z : ℤ_[p] => G (↑z : ℚ_[p])) := by
  have hcont := (G_hasFPS (p := p) hp5).continuousOn
  refine hcont.comp_continuous (by fun_prop) (fun z => ?_)
  have hz1 : ‖(↑z : ℚ_[p])‖ ≤ 1 := by
    rw [PadicInt.padic_norm_e_of_padicInt]; exact PadicInt.norm_le_one z
  rw [EMetric.mem_ball, edist_zero_eq_enorm, ← ofReal_norm_eq_enorm]
  calc ENNReal.ofReal ‖(↑z : ℚ_[p])‖ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hz1
    _ < 2 := by rw [ENNReal.ofReal_one]; norm_num
    _ ≤ _ := two_le_radius hp5

/-! ## Step 4: difference equation, oddness, and Σ₂ = 0 -/

/-- `G` composed with a map into the closed unit ball of `ℚ_[p]` is continuous. -/
lemma continuous_G_comp (hp5 : 5 ≤ p) {h : ℤ_[p] → ℚ_[p]} (hh : Continuous h)
    (hb : ∀ z, ‖h z‖ ≤ 1) : Continuous (fun z : ℤ_[p] => G (h z)) := by
  have hcont := (G_hasFPS (p := p) hp5).continuousOn
  refine hcont.comp_continuous hh (fun z => ?_)
  rw [EMetric.mem_ball, edist_zero_eq_enorm, ← ofReal_norm_eq_enorm]
  calc ENNReal.ofReal ‖h z‖ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal (hb z)
    _ < 2 := by rw [ENNReal.ofReal_one]; norm_num
    _ ≤ _ := two_le_radius hp5

lemma G_zero (hp5 : 5 ≤ p) : G (0 : ℚ_[p]) = 0 := by
  have := G_natCast hp5 0
  simpa using this

lemma continuous_oneAddWx : Continuous (oneAddWx (p := p)) := by
  unfold oneAddWx
  exact continuous_finset_prod _ (fun i _ => by fun_prop)

lemma continuous_g (hp5 : 5 ≤ p) : Continuous (g (p := p)) := by
  have heq : (g (p := p)) = fun z : ℤ_[p] => Lfun p ((↑(oneAddWx z - 1) : ℚ_[p])) := by
    funext z; rw [g, padicLog_eq_Lfun _ (norm_oneAddWx_sub_one_lt hp5 z)]
  rw [heq]
  have hcont := (hasFPS_L (p := p)).continuousOn
  refine hcont.comp_continuous
    (continuous_subtype_val.comp (continuous_oneAddWx.sub continuous_const)) (fun z => ?_)
  have hz : ‖((↑(oneAddWx z - 1) : ℚ_[p]))‖ < 1 := by
    rw [PadicInt.padic_norm_e_of_padicInt]; exact norm_oneAddWx_sub_one_lt hp5 z
  rw [EMetric.mem_ball, edist_zero_eq_enorm, ← ofReal_norm_eq_enorm]
  calc ENNReal.ofReal ‖((↑(oneAddWx z - 1) : ℚ_[p]))‖
      < ENNReal.ofReal 1 := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)).mpr hz
    _ = 1 := ENNReal.ofReal_one
    _ ≤ _ := one_le_radius_cc

/-- **Difference equation:** `G(↑z + 1) - G(↑z) = g z` for all `z : ℤ_[p]`. -/
lemma diff_eq (hp5 : 5 ≤ p) (z : ℤ_[p]) :
    G ((↑z : ℚ_[p]) + 1) - G (↑z) = g z := by
  have hcF1 : Continuous (fun z : ℤ_[p] => G ((↑z : ℚ_[p]) + 1) - G (↑z)) := by
    refine Continuous.sub (continuous_G_comp hp5
      (continuous_subtype_val.add continuous_const) (fun z => ?_)) (continuous_G_coe hp5)
    have : (↑z : ℚ_[p]) + 1 = (↑(z + 1) : ℚ_[p]) := by push_cast; ring
    rw [this, PadicInt.padic_norm_e_of_padicInt]; exact PadicInt.norm_le_one _
  have H : (fun z : ℤ_[p] => G ((↑z : ℚ_[p]) + 1) - G (↑z)) ∘ (Nat.cast : ℕ → ℤ_[p])
      = (g (p := p)) ∘ (Nat.cast : ℕ → ℤ_[p]) := by
    funext n
    simp only [Function.comp_apply]
    have hcast1 : (↑(↑n : ℤ_[p]) : ℚ_[p]) + 1 = (↑(n + 1) : ℚ_[p]) := by push_cast; ring
    have hcast2 : (↑(↑n : ℤ_[p]) : ℚ_[p]) = (↑n : ℚ_[p]) := by push_cast; ring
    rw [hcast1, hcast2, G_natCast hp5 (n + 1), G_natCast hp5 n, Finset.sum_range_succ]
    ring
  have hFeq := PadicInt.denseRange_natCast.equalizer hcF1 (continuous_g hp5) H
  exact congrFun hFeq z

/-- **Oddness of `G`:** `G(-↑z) = -G(↑z)`. -/
lemma G_odd (hp5 : 5 ≤ p) (z : ℤ_[p]) : G (-(↑z : ℚ_[p])) = -G (↑z) := by
  set Q : ℤ_[p] → ℚ_[p] := fun z => G (↑z) + G (-(↑z : ℚ_[p])) with hQ
  have Qstep : ∀ w : ℤ_[p], Q (w + 1) = Q w := by
    intro w
    have h1 := diff_eq hp5 w
    have h2 := diff_eq hp5 (-w - 1)
    have c1 : (↑(w + 1) : ℚ_[p]) = ↑w + 1 := by push_cast; ring
    have c2 : (-(↑(w + 1) : ℚ_[p])) = -↑w - 1 := by push_cast; ring
    have c3 : (↑(-w - 1) : ℚ_[p]) = -↑w - 1 := by push_cast; ring
    have c4 : (↑(-w - 1) : ℚ_[p]) + 1 = -↑w := by push_cast; ring
    have hg : g w = g (-w - 1) := by rw [g_reflection hp5 w]; congr 1; ring
    rw [c4, c3] at h2
    simp only [hQ]
    rw [c2, c1]
    linear_combination h1 - h2 + hg
  have hQ0 : Q 0 = 0 := by
    simp only [hQ]
    rw [show ((0 : ℤ_[p]) : ℚ_[p]) = 0 from by push_cast; ring, neg_zero, G_zero hp5]
    ring
  have hQnat : ∀ n : ℕ, Q (↑n) = 0 := by
    intro n
    induction n with
    | zero => simpa using hQ0
    | succ k ih =>
        have hc : (↑(k + 1) : ℤ_[p]) = (↑k) + 1 := by push_cast; ring
        rw [hc, Qstep, ih]
  have hneg_cont : Continuous (fun z : ℤ_[p] => -(↑z : ℚ_[p])) := continuous_subtype_val.neg
  have hneg_b : ∀ z : ℤ_[p], ‖-(↑z : ℚ_[p])‖ ≤ 1 := fun z => by
    rw [norm_neg, PadicInt.padic_norm_e_of_padicInt]; exact PadicInt.norm_le_one z
  have hcQ : Continuous Q := by
    simp only [hQ]
    exact (continuous_G_coe hp5).add (continuous_G_comp hp5 hneg_cont hneg_b)
  have hQzero : Q = fun _ : ℤ_[p] => (0 : ℚ_[p]) :=
    PadicInt.denseRange_natCast.equalizer hcQ continuous_const (by funext n; simpa using hQnat n)
  have hz0 : Q z = 0 := congrFun hQzero z
  simp only [hQ] at hz0
  linear_combination hz0

/-- **Σ₂ = 0** in the form `Sig 2 = 0`. -/
lemma Sig_two_eq_zero (hp5 : 5 ≤ p) : Sig (p := p) 2 = 0 := by
  set P := FormalMultilinearSeries.ofScalars ℚ_[p] (Sig (p := p)) with hP
  have hG_at : HasFPowerSeriesAt (G (p := p)) P 0 := (G_hasFPS hp5).hasFPowerSeriesAt
  have hu0 : (-ContinuousLinearMap.id ℚ_[p] ℚ_[p]) (0 : ℚ_[p]) = 0 := by simp
  have hG_at' : HasFPowerSeriesAt (G (p := p)) P ((-ContinuousLinearMap.id ℚ_[p] ℚ_[p]) 0) := by
    rw [hu0]; exact hG_at
  have hGneg_at := hG_at'.compContinuousLinearMap (u := -ContinuousLinearMap.id ℚ_[p] ℚ_[p])
  rw [hP, FormalMultilinearSeries.ofScalars_comp_neg_id] at hGneg_at
  have hDadd := hG_at.add hGneg_at
  rw [hP, ← FormalMultilinearSeries.ofScalars_add] at hDadd
  have hD0 : (fun x : ℚ_[p] => G x + (G ∘ ⇑(-ContinuousLinearMap.id ℚ_[p] ℚ_[p])) x)
      =ᶠ[nhds 0] (0 : ℚ_[p] → ℚ_[p]) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℚ_[p]) one_pos] with x hx
    rw [Metric.mem_ball, dist_zero_right] at hx
    have hzc : (↑(⟨x, le_of_lt hx⟩ : ℤ_[p]) : ℚ_[p]) = x := rfl
    simp only [Function.comp_apply, ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply,
      Pi.zero_apply]
    rw [← hzc, G_odd hp5 ⟨x, le_of_lt hx⟩]; ring
  have hzero := hDadd.eq_zero_of_eventually hD0
  have hc0 : (Sig (p := p) + fun k => (-1) ^ k * Sig k) = 0 :=
    (FormalMultilinearSeries.ofScalars_series_eq_zero ℚ_[p]).mp hzero
  have h2 := congrFun hc0 2
  simp only [Pi.add_apply, Pi.zero_apply] at h2
  rw [show ((-1 : ℚ_[p])) ^ 2 = 1 from by norm_num, one_mul] at h2
  have hmul : (2 : ℚ_[p]) * Sig 2 = 0 := by rw [two_mul]; exact h2
  rcases mul_eq_zero.mp hmul with h | h
  · exact absurd h two_ne_zero
  · exact h

/-- **Main theorem — Σ₂ = 0:** the second-order coefficient vanishes. -/
theorem sigma2_eq_zero (hp5 : 5 ≤ p) :
    HasSum (fun m : ℕ => (-1 : ℚ_[p]) ^ m * (p : ℚ_[p]) ^ (m + 1)
        * ((Hz (m + 1) : ℤ_[p]) : ℚ_[p]) * ((bernoulli m : ℚ) : ℚ_[p])) 0 := by
  have hSig : Sig (p := p) 2 = 0 := Sig_two_eq_zero hp5
  have hHS : HasSum (fun k : ℕ => (a k * d k 2 : ℚ_[p])) 0 := by
    have hsum := (summable_ad hp5 2).hasSum
    rw [← Sig] at hsum
    rwa [hSig] at hsum
  have hf0 : (a 0 * d 0 2 : ℚ_[p]) = 0 := by simp [a]
  have hshift : HasSum (fun m : ℕ => (a (m + 1) * d (m + 1) 2 : ℚ_[p])) 0 := by
    refine (hasSum_nat_add_iff (f := fun k : ℕ => (a k * d k 2 : ℚ_[p])) 1 (g := 0)).mpr ?_
    rw [Finset.sum_range_one, zero_add, hf0]
    exact hHS
  have hmul : HasSum (fun m : ℕ => (2 * (a (m + 1) * d (m + 1) 2) : ℚ_[p])) 0 := by
    have := hshift.mul_left 2; rwa [mul_zero] at this
  have hAeq : ∀ m : ℕ, (-1 : ℚ_[p]) ^ m * (p : ℚ_[p]) ^ (m + 1)
        * ((Hz (m + 1) : ℤ_[p]) : ℚ_[p]) * ((bernoulli m : ℚ) : ℚ_[p])
      = 2 * (a (m + 1) * d (m + 1) 2) := by
    intro m
    have e1 : (m + 1) - 1 = m := by omega
    have e2 : (m + 1) + 1 - 2 = m := by omega
    have hc : ((Nat.choose (m + 1 + 1) 2 : ℕ) : ℚ_[p]) = ((m : ℚ_[p]) + 2) * ((m : ℚ_[p]) + 1) / 2 := by
      rw [Nat.cast_choose_two]; push_cast; ring
    have hm1 : (m : ℚ_[p]) + 1 ≠ 0 := by
      rw [show (m : ℚ_[p]) + 1 = ((m + 1 : ℕ) : ℚ_[p]) from by push_cast; ring]
      exact_mod_cast Nat.succ_ne_zero m
    have hm2 : (m : ℚ_[p]) + 2 ≠ 0 := by
      rw [show (m : ℚ_[p]) + 2 = ((m + 2 : ℕ) : ℚ_[p]) from by push_cast; ring]
      exact_mod_cast Nat.succ_ne_zero (m + 1)
    have h2 : (2 : ℚ_[p]) ≠ 0 := two_ne_zero
    rw [a, d, if_neg (by norm_num : (2 : ℕ) ≠ 0), e1, e2, hc,
      show ((m + 1 : ℕ) : ℚ_[p]) = (m : ℚ_[p]) + 1 from by push_cast; ring,
      show ((m + 1 + 1 : ℕ) : ℚ_[p]) = (m : ℚ_[p]) + 2 from by push_cast; ring]
    field_simp
  have hfun : (fun m : ℕ => (-1 : ℚ_[p]) ^ m * (p : ℚ_[p]) ^ (m + 1)
        * ((Hz (m + 1) : ℤ_[p]) : ℚ_[p]) * ((bernoulli m : ℚ) : ℚ_[p]))
      = (fun m : ℕ => 2 * (a (m + 1) * d (m + 1) 2)) := funext hAeq
  rw [hfun]
  exact hmul

/-- Corollary: the `tsum` version of `Σ₂ = 0`. -/
theorem sigma2_tsum (hp5 : 5 ≤ p) :
    ∑' m : ℕ, (-1 : ℚ_[p]) ^ m * (p : ℚ_[p]) ^ (m + 1)
        * ((Hz (m + 1) : ℤ_[p]) : ℚ_[p]) * ((bernoulli m : ℚ) : ℚ_[p]) = 0 :=
  (sigma2_eq_zero hp5).tsum_eq

end PSigma
