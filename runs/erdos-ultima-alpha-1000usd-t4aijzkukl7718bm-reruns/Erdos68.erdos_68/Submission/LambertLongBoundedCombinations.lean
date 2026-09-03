import Submission.LambertCyclicCombinationLowerBound

/-! Bounded integer combinations with arbitrary finite support.
No boundary-clearing or irrationality assertion is made. -/

namespace LambertLongBoundedCombinations

open Finset LambertDifferenceOperators LambertRawBounds LambertTailRows
  LambertSharperOperatorBounds FactorialGeometricProductBound
  LambertCyclicRowLowerBound LambertCyclicCombinationLowerBound
  LambertUniformRawNonvanishing

noncomputable section

lemma rate_ge_two (d : ℕ) (hd : 12 ≤ d) : (2 : ℝ) ≤ rate d := by
  have hl := rate_lower_third d (by omega)
  have h : (12 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

lemma geometric_Ico_bound (x : ℝ) (hx : 2 ≤ x) (a b : ℕ) :
    (∑ j ∈ Finset.Ico a b, 1/x^j) ≤ 2/x^a := by
  have hp : 0 < x := by linarith
  have hi : 0 ≤ 1/x := by positivity
  have hh : 1/x ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hx
  have hu : 1/x < 1 := by linarith
  have hb := geom_sum_Ico_le_of_lt_one (m := a) (n := b) hi hu
  simp only [one_div_pow] at hb
  calc
    _ ≤ _ := hb
    _ ≤ (1/x^a)/(1/2) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
    _ = _ := by ring

variable (d : ℕ) [NeZero d]

def aggregate (M : ℕ) (w : ℕ → ℤ) (h : ZMod d) : ℝ :=
  ∑ j ∈ Finset.range (M+1), if (j : ZMod d)=h then (w j : ℝ)/rate d^j else 0

lemma convolve_aggregate (M : ℕ) (w : ℕ → ℤ) (f : ZMod d → ℝ) (h : ZMod d) :
    convolve d (aggregate d M w) f h =
      ∑ j ∈ Finset.range (M+1), (w j : ℝ)/rate d^j * f (h+(j : ZMod d)) := by
  classical
  simp only [convolve, aggregate, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp

lemma aggregate_zero_lower (M Q : ℕ) (w : ℕ → ℤ) (hd : 12 ≤ d)
    (hQ : 4*Q ≤ d.factorial) (hw0 : w 0 ≠ 0)
    (hw : ∀ j ≤ M, |w j| ≤ (Q : ℤ)) :
    (1/2 : ℝ) ≤ ‖aggregate d M w‖ := by
  classical
  have hp := rate_pos d
  have h2 := rate_ge_two d hd
  let t : ℕ → ℝ := fun j => if (j : ZMod d)=0 then (w j : ℝ)/rate d^j else 0
  have hsplit : aggregate d M w 0 = (w 0 : ℝ) + ∑ j ∈ Finset.Ico 1 (M+1), t j := by
    unfold aggregate
    rw [← Finset.sum_range_add_sum_Ico (f := t) (by omega : 1 ≤ M+1)]
    simp [t]
  have hpoint (j : ℕ) (hj : j ∈ Finset.Ico 1 (M+1)) :
      |t j| ≤ if d ≤ j then (Q : ℝ)/rate d^j else 0 := by
    have hwj : |(w j : ℝ)| ≤ Q := by exact_mod_cast hw j (by have := Finset.mem_Ico.mp hj; omega)
    by_cases hdj : d ≤ j
    · rw [if_pos hdj]
      dsimp [t]
      split_ifs
      · rw [abs_div, abs_of_pos (pow_pos hp _)]
        exact div_le_div_of_nonneg_right hwj (pow_nonneg hp.le _)
      · simp only [abs_zero]; positivity
    · rw [if_neg hdj]
      have hz : (j : ZMod d) ≠ 0 := by
        intro hz
        have he := congrArg ZMod.val hz
        rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at he
        have := Finset.mem_Ico.mp hj
        omega
      simp [t, hz]
  have hsum : |∑ j ∈ Finset.Ico 1 (M+1), t j| ≤ 2*(Q : ℝ)/d.factorial := by
    calc
      _ ≤ ∑ j ∈ Finset.Ico 1 (M+1), |t j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.Ico 1 (M+1), if d ≤ j then (Q : ℝ)/rate d^j else 0 :=
        Finset.sum_le_sum hpoint
      _ = ∑ j ∈ Finset.Ico d (M+1), (Q : ℝ)/rate d^j := by
        rw [← Finset.sum_filter]
        congr 1
        ext j
        simp only [Finset.mem_filter, Finset.mem_Ico]
        omega
      _ = (Q : ℝ) * ∑ j ∈ Finset.Ico d (M+1), 1/rate d^j := by rw [Finset.mul_sum]; simp [div_eq_mul_inv]
      _ ≤ (Q : ℝ)*(2/rate d^d) :=
        mul_le_mul_of_nonneg_left (geometric_Ico_bound (rate d) h2 d (M+1)) (Nat.cast_nonneg Q)
      _ = _ := by rw [rate_pow d (by omega)]; ring
  have hhalf : 2*(Q : ℝ)/d.factorial ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < d.factorial)).mpr
    have : (4*(Q : ℝ)) ≤ d.factorial := by exact_mod_cast hQ
    linarith
  have hwone : (1 : ℝ) ≤ |(w 0 : ℝ)| := by
    exact_mod_cast Int.one_le_abs hw0
  have habs : |(w 0 : ℝ)| ≤ |aggregate d M w 0| + |∑ j ∈ Finset.Ico 1 (M+1), t j| := by
    calc
      _ = |aggregate d M w 0 - ∑ j ∈ Finset.Ico 1 (M+1), t j| := by rw [hsplit]; simp
      _ ≤ _ := abs_sub _ _
  have hn : |aggregate d M w 0| ≤ ‖aggregate d M w‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (aggregate d M w) 0
  linarith

lemma aggregate_raw_model (M : ℕ) (w : ℕ → ℤ) (ks : List ℕ)
    (r : ℕ → ℝ) (f : ZMod d → ℝ)
    (hr : ∀ n, rate d^n*r n=f (n : ZMod d)) (n : ℕ) :
    rate d^n*(∑ j ∈ Finset.range (M+1), (w j : ℝ)*rawApply ks r (n+j)) =
      cyclicApply d ks (convolve d (aggregate d M w) f) (n : ZMod d) := by
  have hp := rate_pos d
  rw [cyclicApply_convolve, convolve_aggregate, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hm := rawApply_model d ks r f hr (n+j)
  simp only [Nat.cast_add] at hm
  rw [← hm, pow_add]
  field_simp

/-- There is no bound on the support length M. The coefficient budget is
strictly below the factorial base, preventing cyclic digit cancellation. -/
theorem row_detection (M Q H : ℕ) (w : ℕ → ℤ) (hd : 12 ≤ d)
    (hQ : 4*Q ≤ d.factorial) (hw0 : w 0 ≠ 0)
    (hw : ∀ j ≤ M, |w j| ≤ (Q : ℤ)) :
    ∃ n, H ≤ n ∧ n < H+d ∧
      Real.exp (-48)/(2*(rate d+1)) ≤
        rate d^n * |∑ j ∈ Finset.range (M+1),
          (w j : ℝ)*rawApply (List.range' 2 (d-2)) (geometricRowTail d) (n+j)| := by
  have hp := rate_pos d
  let c := aggregate d M w
  let f := cyclicApply d (List.range' 2 (d-2)) (convolve d c (rowModel d))
  have hc : (1/2 : ℝ) ≤ ‖c‖ := aggregate_zero_lower d M Q w hd hQ hw0 hw
  have hlow : Real.exp (-48)/(2*(rate d+1)) ≤ ‖f‖ := by
    have ho := cyclicApply_norm_lower d (List.range' 2 (d-2)) (by
      intro k hk
      obtain ⟨i, hi, he⟩ := List.mem_range'.mp hk
      exact (normalized_factorial_le_three_quarters d k hd (by omega) (by omega)).trans
        (by norm_num)) (convolve d c (rowModel d))
    have hprod := lower_product_uniform (d-2) d hd (by omega)
    have hcn := convolution_norm_lower d (by omega) c
    calc
      _ = Real.exp (-48)*((1/2)/(rate d+1)) := by field_simp
      _ ≤ Real.exp (-48)*(‖c‖/(rate d+1)) := by gcongr
      _ ≤ ((List.range' 2 (d-2)).map (fun k => 1-(k.factorial : ℝ)/rate d^k)).prod *
          ‖convolve d c (rowModel d)‖ :=
        mul_le_mul hprod hcn (by positivity) ((Real.exp_pos _).le.trans hprod)
      _ ≤ _ := ho
  obtain ⟨h, hh⟩ := exists_norm_ge f _ (by positivity) hlow
  let j := (h-(H : ZMod d)).val
  have hj : j < d := ZMod.val_lt _
  have he : ((H+j : ℕ) : ZMod d)=h := by
    simp only [Nat.cast_add, j, ZMod.natCast_zmod_val]
    ring
  refine ⟨H+j, by omega, by omega, ?_⟩
  have hm := aggregate_raw_model d M w (List.range' 2 (d-2))
    (geometricRowTail d) (rowModel d) (geometricRowTail_model d (by omega)) (H+j)
  rw [he] at hm
  change _ ≤ |cyclicApply d (List.range' 2 (d-2))
    (convolve d (aggregate d M w) (rowModel d)) h| at hh
  rw [← hm, abs_mul, abs_of_pos (pow_pos hp _)] at hh
  exact hh

omit [NeZero d] in
lemma remaining_rows_budget (Q n L : ℕ) (hd : 12 ≤ d) (hQ : 0 < Q)
    (hL : 4*(Q : ℝ)*(d : ℝ)^2 ≤ 2^L) (hn : (d+1)*(L+130) ≤ n) :
    rate d^n * |∑' k : ℕ,
      rawApply (List.range' 2 (d-2)) (geometricRowTail (k+d+1)) n| <
      Real.exp (-48)/(4*(Q : ℝ)*(d : ℝ)) := by
  have hdR : (0 : ℝ) < d := by positivity
  have hQR : (0 : ℝ) < Q := by positivity
  have hb := remaining_rows_bound (d-2) d n hd (by omega) (by nlinarith)
  have hnear := rate_ratio_power d n (L+130) (by omega) hn
  have hfar := three_quarters_power n (L+130) (by nlinarith)
  have hsum : rate d^n * |∑' k : ℕ,
      rawApply (List.range' 2 (d-2)) (geometricRowTail (k+d+1)) n| ≤
      6*Real.exp 12*d*(1/2 : ℝ)^(L+130) := by
    calc
      _ ≤ _ := hb
      _ ≤ 2*Real.exp 12*d*(1/2 : ℝ)^(L+130) +
          4*Real.exp 12*d*(1/2 : ℝ)^(L+130) := by gcongr
      _ = _ := by ring
  have hbudget : 6*Real.exp 12*d*(1/2 : ℝ)^(L+130) ≤
      6*Real.exp 12/(4*(Q : ℝ)*d*2^130) := by
    rw [one_div_pow, pow_add, mul_one_div]
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2^L*2^130)
      (by positivity : (0 : ℝ) < 4*(Q : ℝ)*d*2^130)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hL (show 0 ≤ 6*Real.exp 12*2^130 by positivity)]
  have hstrict : 6*Real.exp 12/(4*(Q : ℝ)*d*2^130) <
      Real.exp (-48)/(4*(Q : ℝ)*d) := by
    apply (div_lt_div_iff₀ (by positivity : (0 : ℝ) < 4*(Q : ℝ)*d*2^130)
      (by positivity : (0 : ℝ) < 4*(Q : ℝ)*d)).mpr
    have he : Real.exp 60*Real.exp (-48) = Real.exp 12 := by
      rw [← Real.exp_add]
      norm_num
    have hm := mul_lt_mul_of_pos_right exponential_constant (Real.exp_pos (-48))
    rw [mul_assoc, he] at hm
    have hm2 := mul_lt_mul_of_pos_right hm (show 0 < 4*(Q : ℝ)*d by positivity)
    nlinarith only [hm2]
  exact hsum.trans_lt (hbudget.trans_lt hstrict)

omit [NeZero d] in
lemma long_combination_bound (M Q n : ℕ) (w : ℕ → ℤ) (r : ℕ → ℝ) (B : ℝ)
    (hd : 12 ≤ d) (hB : 0 ≤ B) (hw : ∀ j ≤ M, |w j| ≤ (Q : ℤ))
    (hr : ∀ j ≤ M, rate d^(n+j)*|r (n+j)| ≤ B) :
    rate d^n*|∑ j ∈ Finset.range (M+1), (w j : ℝ)*r (n+j)| ≤ 2*(Q : ℝ)*B := by
  have hp := rate_pos d
  have hweight : (∑ j ∈ Finset.range (M+1), |(w j : ℝ)|/rate d^j) ≤ 2*(Q : ℝ) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (M+1), (Q : ℝ)/rate d^j := by
        apply Finset.sum_le_sum
        intro j hj
        apply div_le_div_of_nonneg_right _ (pow_nonneg hp.le _)
        exact_mod_cast hw j (by have := Finset.mem_range.mp hj; omega)
      _ = (Q : ℝ)*(∑ j ∈ Finset.Ico 0 (M+1), 1/rate d^j) := by
        rw [Nat.Ico_zero_eq_range, Finset.mul_sum]
        simp only [mul_one_div]
      _ ≤ (Q : ℝ)*(2/rate d^0) :=
        mul_le_mul_of_nonneg_left (geometric_Ico_bound (rate d) (rate_ge_two d hd) 0 (M+1))
          (Nat.cast_nonneg Q)
      _ = _ := by simp [mul_comm]
  calc
    _ ≤ rate d^n*(∑ j ∈ Finset.range (M+1), |(w j : ℝ)*r (n+j)|) :=
      mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (pow_nonneg hp.le n)
    _ = ∑ j ∈ Finset.range (M+1), (|(w j : ℝ)|/rate d^j) *
        (rate d^(n+j)*|r (n+j)|) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [abs_mul, pow_add]
      field_simp
    _ ≤ ∑ j ∈ Finset.range (M+1), (|(w j : ℝ)|/rate d^j)*B := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hr j (by have := Finset.mem_range.mp hj; omega))
        (by positivity)
    _ = (∑ j ∈ Finset.range (M+1), |(w j : ℝ)|/rate d^j)*B := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hweight hB

/-- Arbitrarily long bounded combinations are detected in a window of d
output phases. This concerns raw errors, not integer linear forms. -/
theorem raw_detection (M Q H L : ℕ) (w : ℕ → ℤ) (hd : 12 ≤ d)
    (hQ : 4*Q ≤ d.factorial) (hw0 : w 0 ≠ 0)
    (hw : ∀ j ≤ M, |w j| ≤ (Q : ℤ))
    (hL : 4*(Q : ℝ)*(d : ℝ)^2 ≤ 2^L) (hH : (d+1)*(L+130) ≤ H) :
    ∃ n, H ≤ n ∧ n < H+d ∧
      (∑ j ∈ Finset.range (M+1), (w j : ℝ)*rawTail (d-2) (n+j)) ≠ 0 := by
  have hp := rate_pos d
  have hdR : (0 : ℝ) < d := by positivity
  have hQpos : 0 < Q := by
    have hb := hw 0 (by omega)
    have ho := Int.one_le_abs hw0
    omega
  have hQR : (0 : ℝ) < Q := by positivity
  obtain ⟨n, hn, hnu, hfirst⟩ := row_detection d M Q H w hd hQ hw0 hw
  let r : ℕ → ℝ := fun m => ∑' k : ℕ,
    rawApply (List.range' 2 (d-2)) (geometricRowTail (k+d+1)) m
  have hr (j : ℕ) (_hj : j ≤ M) :
      rate d^(n+j)*|r (n+j)| ≤ Real.exp (-48)/(4*(Q : ℝ)*d) :=
    (remaining_rows_budget d Q (n+j) L hd hQpos hL (hH.trans (by omega))).le
  have hrest := long_combination_bound d M Q n w r
    (Real.exp (-48)/(4*(Q : ℝ)*d)) hd (by positivity) hw hr
  have hrest' : rate d^n*|∑ j ∈ Finset.range (M+1), (w j : ℝ)*r (n+j)| ≤
      Real.exp (-48)/(2*(d : ℝ)) := by
    convert hrest using 1
    field_simp
    ring
  have hsplit : (∑ j ∈ Finset.range (M+1), (w j : ℝ)*rawTail (d-2) (n+j)) =
      (∑ j ∈ Finset.range (M+1),
        (w j : ℝ)*rawApply (List.range' 2 (d-2)) (geometricRowTail d) (n+j)) +
      ∑ j ∈ Finset.range (M+1), (w j : ℝ)*r (n+j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [rawTail_split]
    have hidx : d-2+2=d := by omega
    have he (k : ℕ) : k+(d-2)+3=k+d+1 := by omega
    simp only [hidx, he, r, mul_add]
  have hgap : Real.exp (-48)/(2*(d : ℝ)) < Real.exp (-48)/(2*(rate d+1)) := by
    apply div_lt_div_of_pos_left (Real.exp_pos _) (by positivity)
    have hu := rate_upper_half d (by omega)
    have hh : (12 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  refine ⟨n, hn, hnu, ?_⟩
  intro hz
  have he : (∑ j ∈ Finset.range (M+1),
      (w j : ℝ)*rawApply (List.range' 2 (d-2)) (geometricRowTail d) (n+j)) =
      -(∑ j ∈ Finset.range (M+1), (w j : ℝ)*r (n+j)) := by
    rw [hsplit] at hz
    linarith
  rw [he, abs_neg] at hfirst
  exact (not_lt_of_ge hfirst) (hrest'.trans_lt hgap)

/-- The leading coefficient may vanish: trim to the first nonzero weight.
The phase threshold remains independent of the total support length. -/
theorem raw_detection_nonzero (M Q H L : ℕ) (w : ℕ → ℤ) (hd : 12 ≤ d)
    (hQ : 4*Q ≤ d.factorial) (hne : ∃ j ≤ M, w j ≠ 0)
    (hw : ∀ j ≤ M, |w j| ≤ (Q : ℤ))
    (hL : 4*(Q : ℝ)*(d : ℝ)^2 ≤ 2^L) (hH : (d+1)*(L+130) ≤ H) :
    ∃ n, H ≤ n ∧ n < H+d ∧
      (∑ j ∈ Finset.range (M+1), (w j : ℝ)*rawTail (d-2) (n+j)) ≠ 0 := by
  classical
  let i := Nat.find hne
  have hi : i ≤ M ∧ w i ≠ 0 := Nat.find_spec hne
  have hzero (j : ℕ) (hj : j < i) : w j = 0 := by
    by_contra hjw
    have hmin := Nat.find_min hne hj
    exact hmin ⟨by omega, hjw⟩
  let v : ℕ → ℤ := fun j => w (i+j)
  have hv0 : v 0 ≠ 0 := by simpa [v] using hi.2
  have hv (j : ℕ) (hj : j ≤ M-i) : |v j| ≤ (Q : ℤ) := hw (i+j) (by omega)
  obtain ⟨N, hN, hNu, hdetect⟩ := raw_detection d (M-i) Q (H+i) L v hd hQ hv0 hv hL
    (hH.trans (by omega))
  refine ⟨N-i, by omega, by omega, ?_⟩
  have he : (∑ j ∈ Finset.range (M+1), (w j : ℝ)*rawTail (d-2) (N-i+j)) =
      ∑ j ∈ Finset.range (M-i+1), (v j : ℝ)*rawTail (d-2) (N+j) := by
    have hM : M+1=i+(M-i+1) := by omega
    rw [hM, Finset.sum_range_add]
    have hpref : (∑ j ∈ Finset.range i, (w j : ℝ)*rawTail (d-2) (N-i+j)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [hzero j (Finset.mem_range.mp hj)]
      simp
    rw [hpref, zero_add]
    apply Finset.sum_congr rfl
    intro j hj
    change (w (i+j) : ℝ)*rawTail (d-2) (N-i+(i+j)) = _
    rw [show N-i+(i+j)=N+j by omega]
  rw [he]
  exact hdetect

omit [NeZero d] in
lemma logarithmic_budget (Q : ℕ) (hd : 0 < d) (hQ : 0 < Q) :
    4*(Q : ℝ)*(d : ℝ)^2 ≤ 2^(Q.log2+2*d.log2+5) := by
  have hdN : d < 2^(d.log2+1) := (Nat.log2_lt hd.ne').mp (by omega)
  have hQN : Q < 2^(Q.log2+1) := (Nat.log2_lt hQ.ne').mp (by omega)
  have hdR : (d : ℝ) ≤ 2^(d.log2+1) := by exact_mod_cast hdN.le
  have hQR : (Q : ℝ) ≤ 2^(Q.log2+1) := by exact_mod_cast hQN.le
  calc
    _ ≤ 4*(2 : ℝ)^(Q.log2+1)*((2 : ℝ)^(d.log2+1))^2 := by gcongr
    _ = _ := by
      rw [← pow_mul, show (4 : ℝ)=(2 : ℝ)^2 by norm_num, ← pow_add, ← pow_add]
      congr 1
      omega

/-- Explicit nonvanishing for every nonzero bounded integer vector on an
arbitrary finite interval. The hypothesis bounds the weights, not the degree. -/
theorem raw_detection_explicit (M Q H : ℕ) (w : ℕ → ℤ) (hd : 12 ≤ d)
    (hQ : 4*Q ≤ d.factorial) (hne : ∃ j ≤ M, w j ≠ 0)
    (hw : ∀ j ≤ M, |w j| ≤ (Q : ℤ))
    (hH : (d+1)*(Q.log2+2*d.log2+135) ≤ H) :
    ∃ n, H ≤ n ∧ n < H+d ∧
      (∑ j ∈ Finset.range (M+1), (w j : ℝ)*rawTail (d-2) (n+j)) ≠ 0 := by
  have hQpos : 0 < Q := by
    obtain ⟨j, hj, hjw⟩ := hne
    have hb := hw j hj
    have ho := Int.one_le_abs hjw
    omega
  exact raw_detection_nonzero d M Q H (Q.log2+2*d.log2+5) w hd hQ hne hw
    (logarithmic_budget d Q (by omega) hQpos) (by convert hH using 1)

end
end LambertLongBoundedCombinations

#print axioms LambertLongBoundedCombinations.aggregate_zero_lower
#print axioms LambertLongBoundedCombinations.row_detection
#print axioms LambertLongBoundedCombinations.raw_detection
#print axioms LambertLongBoundedCombinations.raw_detection_nonzero
#print axioms LambertLongBoundedCombinations.raw_detection_explicit
