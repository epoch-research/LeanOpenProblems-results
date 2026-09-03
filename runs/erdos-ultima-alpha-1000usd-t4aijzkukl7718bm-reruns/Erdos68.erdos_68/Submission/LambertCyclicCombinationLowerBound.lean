import Submission.LambertUniformRawNonvanishing

/-!
A coefficient-norm lower bound for all combinations of fewer than one full
period of shifts. These are analytic estimates, not boundary clearing.
-/

namespace LambertCyclicCombinationLowerBound

open Finset LambertDifferenceOperators LambertRawBounds LambertTailRows
  LambertCyclicRowLowerBound FactorialGeometricProductBound

noncomputable section

variable (d : ℕ) [NeZero d]

/-- A cyclic convolution with arbitrary real coefficients. -/
def convolve (c f : ZMod d → ℝ) (h : ZMod d) : ℝ :=
  ∑ i : ZMod d, c i*f (h+i)

lemma rowModel_jump (hd : 2 ≤ d) (h : ZMod d) :
    rate d*rowModel d h-rowModel d (h+1) = if h+1=0 then 1 else 0 := by
  have hp := rate_pos d
  have hf : (2 : ℝ) ≤ d.factorial := by exact_mod_cast Nat.factorial_le hd
  have hval := ZMod.val_lt h
  have hcast : ((h.val+1 : ℕ) : ZMod d) = h+1 := by simp
  by_cases hh : h.val+1 < d
  · have hv : (h+1).val=h.val+1 := by
      rw [← hcast]
      exact ZMod.val_natCast_of_lt hh
    have hz : h+1 ≠ 0 := by
      intro hz
      have := congrArg ZMod.val hz
      simp only [hv, ZMod.val_zero] at this
      omega
    rw [if_neg hz, rowModel, rowModel, hv, pow_succ]
    ring
  · have he : h.val+1=d := by omega
    have hz : h+1=0 := by rw [← hcast, he]; simp
    rw [if_pos hz, hz, rowModel, rowModel, ZMod.val_zero, pow_zero]
    have hpw : rate d*rate d^h.val = d.factorial := by
      rw [← pow_succ', he, rate_pow d (by omega)]
    have hden : (d.factorial : ℝ)-1 ≠ 0 := by linarith
    field_simp
    nlinarith [hpw]

lemma convolve_jump (hd : 2 ≤ d) (c : ZMod d → ℝ) (h : ZMod d) :
    rate d*convolve d c (rowModel d) h-convolve d c (rowModel d) (h+1) =
      c (-h-1) := by
  classical
  have he (i : ZMod d) : h+i+1=0 ↔ i=-h-1 := by
    constructor <;> intro hi <;> linear_combination hi
  calc
    _ = ∑ i : ZMod d, c i*(rate d*rowModel d (h+i)-rowModel d (h+i+1)) := by
      simp only [convolve, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [show h+1+i=h+i+1 by ring]
      ring
    _ = ∑ i : ZMod d, c i*(if i=-h-1 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [rowModel_jump d hd, he]
    _ = _ := by simp

/-- The cyclic geometric row loses at most a factor lambda+1 when recovering
its convolution coefficients. There is no coefficient-height hypothesis. -/
theorem convolution_norm_lower (hd : 2 ≤ d) (c : ZMod d → ℝ) :
    ‖c‖/(rate d+1) ≤ ‖convolve d c (rowModel d)‖ := by
  have hp := rate_pos d
  have hnorm : ‖c‖ ≤ (rate d+1)*‖convolve d c (rowModel d)‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    have he := convolve_jump d hd c (-i-1)
    rw [show -(-i-1)-1=i by ring] at he
    rw [Real.norm_eq_abs, ← he]
    calc
      _ ≤ |rate d*convolve d c (rowModel d) (-i-1)| +
          |convolve d c (rowModel d) (-i-1+1)| := abs_sub _ _
      _ = rate d*|convolve d c (rowModel d) (-i-1)| +
          |convolve d c (rowModel d) (-i-1+1)| := by rw [abs_mul, abs_of_pos hp]
      _ ≤ rate d*‖convolve d c (rowModel d)‖+‖convolve d c (rowModel d)‖ := by
        have h1 : |convolve d c (rowModel d) (-i-1)| ≤ ‖convolve d c (rowModel d)‖ := by
          simpa only [Real.norm_eq_abs] using norm_le_pi_norm (convolve d c (rowModel d)) (-i-1)
        have h2 : |convolve d c (rowModel d) (-i-1+1)| ≤ ‖convolve d c (rowModel d)‖ := by
          simpa only [Real.norm_eq_abs] using norm_le_pi_norm (convolve d c (rowModel d)) (-i-1+1)
        exact add_le_add (mul_le_mul_of_nonneg_left h1 hp.le) h2
      _ = _ := by ring
  exact (div_le_iff₀ (by positivity)).mpr (by nlinarith [hnorm])

lemma cyclicShift_convolve (k : ℕ) (c f : ZMod d → ℝ) :
    cyclicShift d k (convolve d c f) = convolve d c (cyclicShift d k f) := by
  funext h
  simp only [cyclicShift, convolve, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [show h+(k : ZMod d)+i=h+i+k by ring]
  ring

lemma cyclicApply_convolve (ks : List ℕ) (c f : ZMod d → ℝ) :
    cyclicApply d ks (convolve d c f) = convolve d c (cyclicApply d ks f) := by
  induction ks generalizing f with
  | nil => rfl
  | cons k ks ih => rw [cyclicApply, cyclicShift_convolve, ih]; rfl

/-- Rescaled coefficients for a finite combination of raw samples. -/
def weightedCoefficients (w : ZMod d → ℝ) (i : ZMod d) : ℝ :=
  w i/rate d^i.val

omit [NeZero d] in
lemma weightedCoefficients_ne_zero (w : ZMod d → ℝ) (hw : w ≠ 0) :
    weightedCoefficients d w ≠ 0 := by
  intro hz
  apply hw
  funext i
  have he := congrFun hz i
  simp only [weightedCoefficients, Pi.zero_apply, div_eq_zero_iff] at he
  exact he.resolve_right (pow_pos (rate_pos d) _).ne'

lemma combined_raw_model (ks : List ℕ) (r : ℕ → ℝ) (f : ZMod d → ℝ)
    (hr : ∀ n, rate d^n*r n=f (n : ZMod d)) (w : ZMod d → ℝ) (n : ℕ) :
    rate d^n*(∑ i : ZMod d, w i*rawApply ks r (n+i.val)) =
      cyclicApply d ks (convolve d (weightedCoefficients d w) f) (n : ZMod d) := by
  have hp := rate_pos d
  rw [cyclicApply_convolve, convolve, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hm := rawApply_model d ks r f hr (n+i.val)
  simp only [Nat.cast_add, ZMod.natCast_zmod_val] at hm
  rw [weightedCoefficients, ← hm, pow_add]
  field_simp

/-- Uniform phase detection for an arbitrary nonzero real vector of d
consecutive weights. The bound scales with its weighted coefficient norm. -/
theorem combination_row_lower_in_every_window (K H : ℕ) (hd : 12 ≤ d)
    (hKd : K+1 < d) (w : ZMod d → ℝ) (hw : w ≠ 0) :
    ∃ n, H ≤ n ∧ n < H+d ∧
      Real.exp (-48)*‖weightedCoefficients d w‖/(rate d+1) ≤
        rate d^n * |∑ i : ZMod d,
          w i*rawApply (List.range' 2 K) (geometricRowTail d) (n+i.val)| := by
  have hp := rate_pos d
  have hcpos : 0 < ‖weightedCoefficients d w‖ :=
    norm_pos_iff.mpr (weightedCoefficients_ne_zero d w hw)
  let c := weightedCoefficients d w
  let f := cyclicApply d (List.range' 2 K) (convolve d c (rowModel d))
  have hlow : Real.exp (-48)*‖c‖/(rate d+1) ≤ ‖f‖ := by
    have ho := cyclicApply_norm_lower d (List.range' 2 K) (by
      intro k hk
      obtain ⟨i, hi, he⟩ := List.mem_range'.mp hk
      exact (normalized_factorial_le_three_quarters d k hd (by omega) (by omega)).trans
        (by norm_num)) (convolve d c (rowModel d))
    calc
      _ = Real.exp (-48)*(‖c‖/(rate d+1)) := by ring
      _ ≤ ((List.range' 2 K).map (fun k => 1-(k.factorial : ℝ)/rate d^k)).prod *
          ‖convolve d c (rowModel d)‖ :=
        mul_le_mul (lower_product_uniform K d hd hKd) (convolution_norm_lower d (by omega) c)
          (by positivity) ((Real.exp_pos _).le.trans (lower_product_uniform K d hd hKd))
      _ ≤ _ := ho
  have hapos : 0 < Real.exp (-48)*‖c‖/(rate d+1) := by dsimp [c]; positivity
  obtain ⟨h, hh⟩ := exists_norm_ge f _ hapos hlow
  let j := (h-(H : ZMod d)).val
  have hj : j < d := ZMod.val_lt _
  have he : ((H+j : ℕ) : ZMod d)=h := by
    simp only [Nat.cast_add, j, ZMod.natCast_zmod_val]
    ring
  refine ⟨H+j, by omega, by omega, ?_⟩
  have hm := combined_raw_model d (List.range' 2 K) (geometricRowTail d) (rowModel d)
    (geometricRowTail_model d (by omega)) w (H+j)
  rw [he] at hm
  change _ ≤ |cyclicApply d (List.range' 2 K)
    (convolve d (weightedCoefficients d w) (rowModel d)) h| at hh
  rw [← hm, abs_mul, abs_of_pos (pow_pos hp _)] at hh
  exact hh

open LambertUniformRawNonvanishing

omit [NeZero d] in
lemma remaining_rows_for_combinations (K n L : ℕ) (hd : 12 ≤ d) (hK : K ≤ d)
    (hL : (d : ℝ)^3 ≤ 2^L) (hn : (d+1)*(L+130) ≤ n) :
    rate d^n * |∑' k : ℕ,
      rawApply (List.range' 2 K) (geometricRowTail (k+d+1)) n| <
      Real.exp (-48)/(d : ℝ)^2 := by
  have hp := rate_pos d
  have hdR : (0 : ℝ) < d := by positivity
  have hb := remaining_rows_bound K d n hd hK (by nlinarith)
  have hnear := rate_ratio_power d n (L+130) (by omega) hn
  have hfar := three_quarters_power n (L+130) (by nlinarith)
  have hsum : rate d^n * |∑' k : ℕ,
      rawApply (List.range' 2 K) (geometricRowTail (k+d+1)) n| ≤
      6*Real.exp 12*d*(1/2 : ℝ)^(L+130) := by
    calc
      _ ≤ _ := hb
      _ ≤ 2*Real.exp 12*d*(1/2 : ℝ)^(L+130) +
          4*Real.exp 12*d*(1/2 : ℝ)^(L+130) := by gcongr
      _ = _ := by ring
  have hbudget : 6*Real.exp 12*d*(1/2 : ℝ)^(L+130) ≤
      6*Real.exp 12/((d : ℝ)^2*2^130) := by
    rw [one_div_pow, pow_add, mul_one_div]
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2^L*2^130)
      (by positivity : (0 : ℝ) < (d : ℝ)^2*2^130)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hL (show 0 ≤ 6*Real.exp 12*2^130 by positivity)]
  have hstrict : 6*Real.exp 12/((d : ℝ)^2*2^130) < Real.exp (-48)/(d : ℝ)^2 := by
    apply (div_lt_div_iff₀ (by positivity : (0 : ℝ) < (d : ℝ)^2*2^130)
      (by positivity : (0 : ℝ) < (d : ℝ)^2)).mpr
    have he : Real.exp 60*Real.exp (-48) = Real.exp 12 := by
      rw [← Real.exp_add]
      norm_num
    have hm := mul_lt_mul_of_pos_right exponential_constant (Real.exp_pos (-48))
    rw [mul_assoc, he] at hm
    have hm2 := mul_lt_mul_of_pos_right hm (sq_pos_of_pos hdR)
    nlinarith only [hm2]
  exact hsum.trans_lt (hbudget.trans_lt hstrict)

lemma combination_bound (w : ZMod d → ℝ) (r : ℕ → ℝ) (n : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hr : ∀ i : ZMod d, rate d^(n+i.val)*|r (n+i.val)| ≤ B) :
    rate d^n*|∑ i : ZMod d, w i*r (n+i.val)| ≤
      (d : ℝ)*‖weightedCoefficients d w‖*B := by
  have hp := rate_pos d
  have hc : (∑ i : ZMod d, ‖weightedCoefficients d w i‖) ≤
      (d : ℝ)*‖weightedCoefficients d w‖ := by
    simpa only [ZMod.card, nsmul_eq_mul] using
      Pi.sum_norm_apply_le_norm (weightedCoefficients d w)
  calc
    _ ≤ rate d^n*(∑ i : ZMod d, |w i*r (n+i.val)|) :=
      mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (pow_nonneg hp.le n)
    _ = ∑ i : ZMod d, ‖weightedCoefficients d w i‖*
        (rate d^(n+i.val)*|r (n+i.val)|) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [weightedCoefficients, Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hp _),
        abs_mul, pow_add]
      field_simp
    _ ≤ ∑ i : ZMod d, ‖weightedCoefficients d w i‖*B := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hr i) (norm_nonneg _)
    _ = (∑ i : ZMod d, ‖weightedCoefficients d w i‖)*B := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hB

/-- Every nonzero real combination of d consecutive raw samples is detected
in each sufficiently late d-phase window. The threshold does not depend on
the coefficient height. No integral-boundary claim is made. -/
theorem raw_combination_nonzero_in_every_window (H L : ℕ) (hd : 12 ≤ d)
    (hL : (d : ℝ)^3 ≤ 2^L) (hH : (d+1)*(L+130) ≤ H)
    (w : ZMod d → ℝ) (hw : w ≠ 0) :
    ∃ n, H ≤ n ∧ n < H+d ∧
      (∑ i : ZMod d, w i*rawTail (d-2) (n+i.val)) ≠ 0 := by
  have hp := rate_pos d
  have hdR : (0 : ℝ) < d := by positivity
  have hcpos : 0 < ‖weightedCoefficients d w‖ :=
    norm_pos_iff.mpr (weightedCoefficients_ne_zero d w hw)
  obtain ⟨n, hn, hnu, hfirst⟩ := combination_row_lower_in_every_window d (d-2) H hd
    (by omega) w hw
  let r : ℕ → ℝ := fun m => ∑' k : ℕ,
    rawApply (List.range' 2 (d-2)) (geometricRowTail (k+d+1)) m
  have hr (i : ZMod d) : rate d^(n+i.val)*|r (n+i.val)| ≤ Real.exp (-48)/(d : ℝ)^2 :=
    (remaining_rows_for_combinations d (d-2) (n+i.val) L hd (by omega) hL
      (hH.trans (by omega))).le
  have hrest := combination_bound d w r n (Real.exp (-48)/(d : ℝ)^2) (by positivity) hr
  have hrest' : rate d^n*|∑ i : ZMod d, w i*r (n+i.val)| ≤
      Real.exp (-48)*‖weightedCoefficients d w‖/(d : ℝ) := by
    convert hrest using 1
    field_simp
  have hsplit : (∑ i : ZMod d, w i*rawTail (d-2) (n+i.val)) =
      (∑ i : ZMod d, w i*rawApply (List.range' 2 (d-2)) (geometricRowTail d) (n+i.val)) +
        ∑ i : ZMod d, w i*r (n+i.val) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [rawTail_split]
    have hidx : d-2+2=d := by omega
    have he (k : ℕ) : k+(d-2)+3=k+d+1 := by omega
    simp only [hidx, he, r, mul_add]
  have hgap : Real.exp (-48)*‖weightedCoefficients d w‖/(d : ℝ) <
      Real.exp (-48)*‖weightedCoefficients d w‖/(rate d+1) := by
    apply div_lt_div_of_pos_left (by positivity) (by positivity)
    have hu := rate_upper_half d (by omega)
    have hh : (12 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  refine ⟨n, hn, hnu, ?_⟩
  intro hz
  have he : (∑ i : ZMod d, w i*rawApply (List.range' 2 (d-2))
      (geometricRowTail d) (n+i.val)) = -(∑ i : ZMod d, w i*r (n+i.val)) := by
    rw [hsplit] at hz
    linarith
  rw [he, abs_neg] at hfirst
  exact (not_lt_of_ge hfirst) (hrest'.trans_lt hgap)

omit [NeZero d] in
lemma cube_le_two_power_log (hd : 0 < d) :
    (d : ℝ)^3 ≤ 2^(3*(d.log2+1)) := by
  have hn : d < 2^(d.log2+1) := (Nat.log2_lt hd.ne').mp (by omega)
  have hr : (d : ℝ) ≤ 2^(d.log2+1) := by exact_mod_cast hn.le
  calc
    _ ≤ ((2 : ℝ)^(d.log2+1))^3 := pow_le_pow_left₀ (by positivity) hr 3
    _ = _ := by rw [← pow_mul]; congr 1; omega

/-- An explicit height-independent threshold for the preceding theorem. -/
theorem raw_combination_explicit_window (H : ℕ) (hd : 12 ≤ d)
    (hH : (d+1)*(3*(d.log2+1)+130) ≤ H)
    (w : ZMod d → ℝ) (hw : w ≠ 0) :
    ∃ n, H ≤ n ∧ n < H+d ∧
      (∑ i : ZMod d, w i*rawTail (d-2) (n+i.val)) ≠ 0 :=
  raw_combination_nonzero_in_every_window d H (3*(d.log2+1)) hd
    (cube_le_two_power_log d (by omega)) hH w hw

end
end LambertCyclicCombinationLowerBound

#print axioms LambertCyclicCombinationLowerBound.convolution_norm_lower
#print axioms LambertCyclicCombinationLowerBound.combination_row_lower_in_every_window

#print axioms LambertCyclicCombinationLowerBound.raw_combination_nonzero_in_every_window
#print axioms LambertCyclicCombinationLowerBound.raw_combination_explicit_window
