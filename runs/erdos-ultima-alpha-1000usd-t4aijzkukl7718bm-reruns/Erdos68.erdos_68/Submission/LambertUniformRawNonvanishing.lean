import Submission.LambertCyclicRowLowerBound

/-!
Uniform nonvanishing windows for the raw row-cancelling operators. These
forms have rational boundaries; no small integral form is asserted.
-/

namespace LambertUniformRawNonvanishing

open Finset Erdos68Development LambertDifferenceOperators LambertRawBounds
  LambertSharperOperatorBounds FactorialGeometricProductBound LambertTailRows
  LambertTotalBounds LambertCyclicRowLowerBound

noncomputable section

lemma rate_mono (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) : rate a ≤ rate b := by
  apply le_of_pow_le_pow_left₀ ha.ne' (rate_pos b).le
  rw [rate_pow a ha]
  exact factorial_le_rate_pow a b (by omega) hab

lemma rate_ratio_step (d : ℕ) (hd : 6 ≤ d) :
    (rate d/rate (d+1))^(d+1) ≤ 1/2 := by
  have hp := rate_pos d
  have hq := rate_pos (d+1)
  have hu := rate_upper_half d hd
  rw [div_pow, rate_pow (d+1) (by omega)]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (d+1).factorial)).mpr
  rw [pow_succ, rate_pow d (by omega), Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one]
  have hf : (0 : ℝ) < d.factorial := by positivity
  nlinarith

lemma rate_ratio_power (d n L : ℕ) (hd : 6 ≤ d) (hn : (d+1)*L ≤ n) :
    (rate d/rate (d+1))^n ≤ (1/2 : ℝ)^L := by
  have hp := rate_pos d
  have hq := rate_pos (d+1)
  have hr : rate d/rate (d+1) ≤ 1 :=
    (div_le_one hq).mpr (rate_mono d (d+1) (by omega) (by omega))
  calc
    _ ≤ (rate d/rate (d+1))^((d+1)*L) :=
      pow_le_pow_of_le_one (by positivity) hr hn
    _ = ((rate d/rate (d+1))^(d+1))^L := pow_mul _ _ _
    _ ≤ _ := pow_le_pow_left₀ (by positivity) (rate_ratio_step d hd) L

lemma summable_rows (ks : List ℕ) (a n : ℕ) :
    Summable (fun k => rawApply ks (geometricRowTail (k+a+2)) n) := by
  have hs : Summable (fun k => rawApply ks (geometricRowTail (k+2)) n) := by
    simpa only [row] using summable_rawApply ks row summable_row n
  simpa only [Nat.add_assoc] using (summable_nat_add_iff a).mpr hs

lemma rows_tail_bound (K a n : ℕ) (ha : 4 ≤ a) (hK : K ≤ a) (hn : 2 ≤ n) :
    |∑' k : ℕ, rawApply (List.range' 2 K) (geometricRowTail (k+a+2)) n| ≤
      2*Real.exp 12*3^n/((a+1 : ℕ) : ℝ)^(n-1) := by
  let C : ℝ := 2*Real.exp 12*3^n
  have hs := summable_bound C a n (by omega)
  have hb (k : ℕ) :
      ‖rawApply (List.range' 2 K) (geometricRowTail (k+a+2)) n‖ ≤
        C/((k+a+2 : ℕ) : ℝ)^n := by
    have he := rawApply_row_uniform_exp_bound K (k+a+2) n (by omega) (by omega)
    have hthree : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
    apply le_trans (by simpa only [Real.norm_eq_abs] using he)
    dsimp [C]
    gcongr
  have ht := tsum_of_norm_bounded hs.hasSum hb
  calc
    _ ≤ ∑' k : ℕ, C/((k+a+2 : ℕ) : ℝ)^n := by
      simpa only [Real.norm_eq_abs] using ht
    _ = C*(∑' k : ℕ, 1/((k+a+2 : ℕ) : ℝ)^n) := by
      simp only [div_eq_mul_inv, one_mul, tsum_mul_left]
    _ ≤ C*(1/((a+1 : ℕ) : ℝ)^(n-1)) :=
      mul_le_mul_of_nonneg_left (pseries_tail_bound a n hn) (by dsimp [C]; positivity)
    _ = _ := by dsimp [C]; ring

lemma scaled_power_identity (x : ℝ) (hx : 0 < x) (n : ℕ) (hn : 1 ≤ n) :
    (x/2)^n*3^n/(2*x)^(n-1) = 2*x*(3/4 : ℝ)^n := by
  have hp : (x/2)^n*3^n = (2*x)^n*(3/4 : ℝ)^n := by
    rw [← mul_pow, ← mul_pow]
    congr 1
    ring
  rw [hp, show n=(n-1)+1 from (Nat.sub_add_cancel hn).symm] at *
  simp only [Nat.add_sub_cancel, pow_succ]
  field_simp

/-- The rows beyond `d` are small relative to the first row's geometric rate. -/
lemma remaining_rows_bound (K d n : ℕ) (hd : 12 ≤ d) (hK : K ≤ d) (hn : 2 ≤ n) :
    rate d^n * |∑' k : ℕ,
      rawApply (List.range' 2 K) (geometricRowTail (k+d+1)) n| ≤
      2*Real.exp 12*(d : ℝ)*(rate d/rate (d+1))^n +
        4*Real.exp 12*d*(3/4 : ℝ)^n := by
  have hp := rate_pos d
  have hq := rate_pos (d+1)
  have hs : Summable (fun k => rawApply (List.range' 2 K)
      (geometricRowTail (k+d+1)) n) := by
    simpa only [show d-1+2=d+1 by omega, Nat.add_assoc] using
      summable_rows (List.range' 2 K) (d-1) n
  have hsplit := hs.sum_add_tsum_nat_add d
  rw [← hsplit]
  have hnear : (∑ k ∈ Finset.range d,
      |rawApply (List.range' 2 K) (geometricRowTail (k+d+1)) n|) ≤
      d*(2*Real.exp 12/rate (d+1)^n) := by
    calc
      _ ≤ ∑ _k ∈ Finset.range d, 2*Real.exp 12/rate (d+1)^n := by
        apply Finset.sum_le_sum
        intro k _
        apply le_trans (rawApply_row_uniform_bound K (k+d+1) n (by omega) (by omega))
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact pow_le_pow_left₀ hq.le (rate_mono (d+1) (k+d+1) (by omega) (by omega)) n
      _ = _ := by simp
  have hfar : |∑' k : ℕ, rawApply (List.range' 2 K)
      (geometricRowTail (k+d+d+1)) n| ≤ 2*Real.exp 12*3^n/(2*(d : ℝ))^(n-1) := by
    have he (k : ℕ) : k+(2*d-1)+2=k+d+d+1 := by omega
    have he2 : 2*d-1+1=2*d := by omega
    simpa only [he, he2, Nat.cast_mul, Nat.cast_ofNat] using
      rows_tail_bound K (2*d-1) n (by omega) (by omega) hn
  have hsnear : |∑ k ∈ Finset.range d, rawApply (List.range' 2 K)
      (geometricRowTail (k+d+1)) n| ≤ d*(2*Real.exp 12/rate (d+1)^n) :=
    (abs_sum_le_sum_abs _ _).trans hnear
  have hufar : rate d^n*(2*Real.exp 12*3^n/(2*(d : ℝ))^(n-1)) ≤
      4*Real.exp 12*d*(3/4 : ℝ)^n := by
    calc
      _ ≤ ((d : ℝ)/2)^n*(2*Real.exp 12*3^n/(2*(d : ℝ))^(n-1)) := by
        gcongr
        exact rate_upper_half d (by omega)
      _ = 2*Real.exp 12*(((d : ℝ)/2)^n*3^n/(2*(d : ℝ))^(n-1)) := by ring
      _ = _ := by rw [scaled_power_identity (d : ℝ) (by positivity) n (by omega)]; ring
  calc
    _ ≤ rate d^n*(|∑ k ∈ Finset.range d, rawApply (List.range' 2 K)
        (geometricRowTail (k+d+1)) n| + |∑' k : ℕ, rawApply (List.range' 2 K)
        (geometricRowTail (k+d+d+1)) n|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) (pow_nonneg hp.le _)
    _ ≤ rate d^n*(d*(2*Real.exp 12/rate (d+1)^n) +
        2*Real.exp 12*3^n/(2*(d : ℝ))^(n-1)) := by gcongr
    _ = 2*Real.exp 12*d*(rate d/rate (d+1))^n +
        rate d^n*(2*Real.exp 12*3^n/(2*(d : ℝ))^(n-1)) := by rw [div_pow]; ring
    _ ≤ _ := add_le_add le_rfl hufar

lemma three_quarters_power (n m : ℕ) (hn : 3*m ≤ n) :
    (3/4 : ℝ)^n ≤ (1/2 : ℝ)^m := by
  calc
    _ ≤ (3/4 : ℝ)^(3*m) := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    _ = ((3/4 : ℝ)^3)^m := pow_mul _ _ _
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) (by norm_num) m

lemma exponential_constant : 6*Real.exp 60 < (2 : ℝ)^130 := by
  have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
  have hp : Real.exp 60 ≤ (3 : ℝ)^60 := by
    have h := pow_le_pow_left₀ (Real.exp_pos 1).le he.le 60
    simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, mul_one] using h
  have hc : (6 : ℝ)*3^60 < 2^130 := by norm_num
  linarith

lemma remaining_rows_small (K d n L : ℕ) (hd : 12 ≤ d) (hK : K ≤ d)
    (hL : (d : ℝ)^2 ≤ 2^L) (hn : (d+1)*(L+130) ≤ n) :
    rate d^n * |∑' k : ℕ,
      rawApply (List.range' 2 K) (geometricRowTail (k+d+1)) n| <
      Real.exp (-48)/(2*rate d) := by
  have hp := rate_pos d
  have hdR : (0 : ℝ) < d := by positivity
  have hn2 : 2 ≤ n := by nlinarith
  have ht : 3*(L+130) ≤ n := by nlinarith
  have hb := remaining_rows_bound K d n hd hK hn2
  have hnear := rate_ratio_power d n (L+130) (by omega) hn
  have hfar := three_quarters_power n (L+130) ht
  have hsum : rate d^n * |∑' k : ℕ,
      rawApply (List.range' 2 K) (geometricRowTail (k+d+1)) n| ≤
      6*Real.exp 12*d*(1/2 : ℝ)^(L+130) := by
    calc
      _ ≤ _ := hb
      _ ≤ 2*Real.exp 12*d*(1/2 : ℝ)^(L+130) +
          4*Real.exp 12*d*(1/2 : ℝ)^(L+130) := by gcongr
      _ = _ := by ring
  have hbudget : 6*Real.exp 12*d*(1/2 : ℝ)^(L+130) ≤
      6*Real.exp 12/((d : ℝ)*2^130) := by
    rw [one_div_pow, pow_add, mul_one_div]
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2^L*2^130)
      (by positivity : (0 : ℝ) < (d : ℝ)*2^130)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hL (show 0 ≤ 6*Real.exp 12*2^130 by positivity)]
  have hstrict : 6*Real.exp 12/((d : ℝ)*2^130) < Real.exp (-48)/(d : ℝ) := by
    apply (div_lt_div_iff₀ (by positivity : (0 : ℝ) < (d : ℝ)*2^130) hdR).mpr
    have he : Real.exp 60*Real.exp (-48) = Real.exp 12 := by
      rw [← Real.exp_add]
      norm_num
    have hm := mul_lt_mul_of_pos_right exponential_constant (Real.exp_pos (-48))
    rw [mul_assoc, he] at hm
    nlinarith
  have hlast : Real.exp (-48)/(d : ℝ) ≤ Real.exp (-48)/(2*rate d) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    linarith [rate_upper_half d (by omega)]
  exact hsum.trans_lt (hbudget.trans_lt (hstrict.trans_le hlast))

/-- The raw affine form in the original target. Its boundary is rational. -/
def rawTail (K n : ℕ) : ℝ :=
  rawApply (List.range' 2 K)
    (fun m => (∑' k : ℕ, term k)-(prefixQ m : ℝ)) n

lemma rawTail_split (K n : ℕ) :
    rawTail K n = rawApply (List.range' 2 K) (geometricRowTail (K+2)) n +
      ∑' k : ℕ, rawApply (List.range' 2 K) (geometricRowTail (k+K+3)) n := by
  have hc : ∀ k < K, k+2 ∈ List.range' 2 K := by
    intro k hk
    exact List.mem_range'.mpr ⟨k, hk, by omega⟩
  rw [rawTail, cutoff_tail_rows _ K n hc]
  have hs := (summable_rows (List.range' 2 K) K n).sum_add_tsum_nat_add 1
  simpa only [Finset.sum_range_one, zero_add, Nat.add_assoc,
    show 1+(K+2)=K+3 by omega] using hs.symm

/-- A full-target lower bound on at least one phase in every late window.
No denominator clearing is performed in this theorem. -/
theorem raw_lower_in_every_window (K H L : ℕ) (hK : 10 ≤ K)
    (hL : ((K+2 : ℕ) : ℝ)^2 ≤ 2^L)
    (hH : (K+3)*(L+130) ≤ H) :
    ∃ n, H ≤ n ∧ n < H+(K+2) ∧
      Real.exp (-48)/(2*rate (K+2)) < rate (K+2)^n*|rawTail K n| := by
  obtain ⟨n, hn, hnu, hrow⟩ := row_lower_in_every_window K (K+2) H
    (by omega) (by omega)
  have hrest := remaining_rows_small K (K+2) n L (by omega) (by omega) hL
    (by simpa only [Nat.add_assoc] using hH.trans hn)
  have hp := rate_pos (K+2)
  let a := rawApply (List.range' 2 K) (geometricRowTail (K+2)) n
  let b := ∑' k : ℕ, rawApply (List.range' 2 K) (geometricRowTail (k+K+3)) n
  have he : rawTail K n = a+b := rawTail_split K n
  have hr : rate (K+2)^n*|b| < Real.exp (-48)/(2*rate (K+2)) := by
    simpa only [b, Nat.add_assoc] using hrest
  have ha : Real.exp (-48)/rate (K+2) ≤ rate (K+2)^n*|a| := hrow
  have ht := norm_sub_norm_le a (-b)
  simp only [Real.norm_eq_abs, abs_neg, sub_neg_eq_add] at ht
  have hm := mul_le_mul_of_nonneg_left ht (pow_nonneg hp.le n)
  refine ⟨n, hn, hnu, ?_⟩
  rw [he]
  have hh : Real.exp (-48)/rate (K+2) = 2*(Real.exp (-48)/(2*rate (K+2))) := by ring
  nlinarith

lemma square_le_two_power_log (d : ℕ) (hd : 0 < d) :
    (d : ℝ)^2 ≤ 2^(2*(d.log2+1)) := by
  have hn : d < 2^(d.log2+1) := (Nat.log2_lt hd.ne').mp (by omega)
  have hr : (d : ℝ) ≤ 2^(d.log2+1) := by exact_mod_cast hn.le
  calc
    _ ≤ ((2 : ℝ)^(d.log2+1))^2 := pow_le_pow_left₀ (by positivity) hr 2
    _ = _ := by rw [← pow_mul]; congr 1; omega

/-- Quantitative raw nonvanishing: the initial threshold is of order
`K log K`, and each later window has length `K+2`. The final value has not
been multiplied by its boundary denominator. -/
theorem raw_nonzero_in_every_window (K H : ℕ) (hK : 10 ≤ K)
    (hH : (K+3)*(2*((K+2).log2+1)+130) ≤ H) :
    ∃ n, H ≤ n ∧ n < H+(K+2) ∧ rawTail K n ≠ 0 := by
  obtain ⟨n, hn, hnu, hl⟩ := raw_lower_in_every_window K H (2*((K+2).log2+1)) hK
    (square_le_two_power_log (K+2) (by omega)) hH
  refine ⟨n, hn, hnu, ?_⟩
  intro hz
  rw [hz, abs_zero, mul_zero] at hl
  exact (not_lt_of_ge (by have := rate_pos (K+2); positivity)) hl

end
end LambertUniformRawNonvanishing

#print axioms LambertUniformRawNonvanishing.remaining_rows_small

#print axioms LambertUniformRawNonvanishing.raw_lower_in_every_window
#print axioms LambertUniformRawNonvanishing.raw_nonzero_in_every_window
