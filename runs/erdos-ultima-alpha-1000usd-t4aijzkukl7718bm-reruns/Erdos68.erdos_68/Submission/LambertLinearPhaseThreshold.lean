import Submission.LambertPhaseMassBounds

/-! Linear starting-index estimates for full-phase Lambert-tail detection.
This file does not clear the output boundaries. -/

namespace LambertLinearPhaseThreshold

open Finset LambertDifferenceOperators LambertRawBounds LambertTailRows
  LambertSharperOperatorBounds FactorialGeometricProductBound
  LambertCyclicRowLowerBound LambertCyclicCombinationLowerBound
  LambertLongBoundedCombinations LambertCyclicMass LambertUniformRawNonvanishing
  LambertPhaseMassBounds

noncomputable section

lemma rate_ratio_chain (d r H L : ℕ) (hd : 12 ≤ d) (hr : r ≤ d)
    (hH : (2*d+1)*L ≤ H) :
    (rate d/rate (d+r))^H ≤ (1/2 : ℝ)^(L*r) := by
  induction r with
  | zero => simp [(rate_pos d).ne']
  | succ r ih =>
    have hi := ih (by omega)
    have hnext := rate_ratio_power (d+r) H L (by omega) (by nlinarith)
    have hp := rate_pos d
    have hq := rate_pos (d+r)
    have hs := rate_pos (d+r+1)
    calc
      _ = (rate d/rate (d+r))^H * (rate (d+r)/rate (d+r+1))^H := by
        rw [← mul_pow, show d+(r+1)=d+r+1 by omega]
        congr 1
        field_simp
      _ ≤ (1/2 : ℝ)^(L*r)*(1/2 : ℝ)^L :=
        mul_le_mul hi hnext (by positivity) (by positivity)
      _ = _ := by rw [← pow_add]; congr 1

lemma finite_geometric_mass (d L : ℕ) (hL : 1 ≤ L) :
    (∑ k ∈ Finset.range d, (1/2 : ℝ)^(L*(k+1))) ≤ 2*(1/2 : ℝ)^L := by
  let t : ℝ := (1/2)^L
  have ht : 0 ≤ t := by positivity
  have hu : t ≤ 1/2 := by
    exact (pow_le_pow_of_le_one (by norm_num) (by norm_num) hL).trans_eq (by simp)
  have hg := geom_sum_mul_neg t d
  have hs : 0 ≤ ∑ k ∈ Finset.range d, t^k := Finset.sum_nonneg (by intros; positivity)
  have hb : (∑ k ∈ Finset.range d, t^k) ≤ 2 := by
    nlinarith [pow_nonneg ht d]
  calc
    _ = t*(∑ k ∈ Finset.range d, t^k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      dsimp [t]
      rw [← pow_mul, ← pow_add]
      congr 1
      ring
    _ ≤ _ := by nlinarith

lemma near_window_bound (d K H : ℕ) (hd : 12 ≤ d) (hK : K ≤ d)
    (hH : 420*d ≤ H) :
    (∑ h ∈ Finset.range d, rate d^(H+h) *
      |∑ k ∈ Finset.range d,
        rawApply (List.range' 2 K) (geometricRowTail (k+d+1)) (H+h)|) <
      Real.exp (-48)/(12*(d : ℝ)) := by
  have hp := rate_pos d
  have hdR : (12 : ℝ) ≤ d := by exact_mod_cast hd
  have hrate : (d : ℝ)/4 ≤ rate d-1 := by
    have hl := rate_lower_third d (by omega)
    linarith
  have hden : 0 < rate d-1 := by linarith
  have hrow (k : ℕ) (hk : k ∈ Finset.range d) :
      (∑ h ∈ Finset.range d, rate d^(H+h) *
        |rawApply (List.range' 2 K) (geometricRowTail (k+d+1)) (H+h)|) ≤
      (4*Real.exp 12/(d : ℝ))*(1/2 : ℝ)^(140*(k+1)) := by
    have hk' := Finset.mem_range.mp hk
    have heq : k+d+1=d+(k+1) := by omega
    have hr := rate_ratio_chain d (k+1) H 140 hd (by omega) (by nlinarith)
    have he := rate_mono d (k+d+1) (by omega) (by omega)
    have hde : Real.exp 12/(rate (k+d+1)-1) ≤ 4*Real.exp 12/(d : ℝ) := by
      calc
        _ ≤ Real.exp 12/((d : ℝ)/4) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
        _ = _ := by ring
    calc
      _ ≤ _ := row_window_mass_bound d (k+d+1) K H hd (by omega) (by omega)
      _ ≤ _ := mul_le_mul hde (by simpa only [heq] using hr)
        (pow_nonneg (div_nonneg (rate_pos d).le (rate_pos _).le) _) (by positivity)
  have hsum : (∑ h ∈ Finset.range d, rate d^(H+h) *
      |∑ k ∈ Finset.range d,
        rawApply (List.range' 2 K) (geometricRowTail (k+d+1)) (H+h)|) ≤
      (8*Real.exp 12/(d : ℝ))*(1/2 : ℝ)^140 := by
    calc
      _ ≤ ∑ h ∈ Finset.range d, ∑ k ∈ Finset.range d,
          rate d^(H+h)*|rawApply (List.range' 2 K) (geometricRowTail (k+d+1)) (H+h)| := by
        apply Finset.sum_le_sum
        intro h _
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (pow_nonneg hp.le _)
      _ = ∑ k ∈ Finset.range d, ∑ h ∈ Finset.range d,
          rate d^(H+h)*|rawApply (List.range' 2 K) (geometricRowTail (k+d+1)) (H+h)| :=
        Finset.sum_comm
      _ ≤ ∑ k ∈ Finset.range d,
          (4*Real.exp 12/(d : ℝ))*(1/2 : ℝ)^(140*(k+1)) := Finset.sum_le_sum hrow
      _ = (4*Real.exp 12/(d : ℝ))*(∑ k ∈ Finset.range d, (1/2 : ℝ)^(140*(k+1))) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ (4*Real.exp 12/(d : ℝ))*(2*(1/2 : ℝ)^140) :=
        mul_le_mul_of_nonneg_left (finite_geometric_mass d 140 (by omega)) (by positivity)
      _ = _ := by ring
  have hconst : 96*Real.exp 60 < (2 : ℝ)^140 := by
    have hc := mul_lt_mul_of_pos_left exponential_constant (show (0 : ℝ)<16 by norm_num)
    have he : (16 : ℝ)*2^130 ≤ 2^140 := by norm_num
    nlinarith
  have he : Real.exp 60*Real.exp (-48)=Real.exp 12 := by rw [← Real.exp_add]; norm_num
  have hb := mul_lt_mul_of_pos_right hconst (Real.exp_pos (-48))
  rw [mul_assoc, he] at hb
  apply hsum.trans_lt
  rw [one_div_pow, mul_one_div]
  apply (div_lt_div_iff₀ (by positivity : (0 : ℝ)<2^140)
    (by positivity : (0 : ℝ)<12*(d : ℝ))).mpr
  have hdpos : (0 : ℝ)<d := by positivity
  field_simp
  nlinarith

lemma far_point_bound (d K n : ℕ) (hd : 12 ≤ d) (hK : K ≤ d) (hn : 2 ≤ n) :
    rate d^n*|∑' k : ℕ,
      rawApply (List.range' 2 K) (geometricRowTail (k+2*d+1)) n| ≤
      4*Real.exp 12*d*(3/4 : ℝ)^n := by
  have hp := rate_pos d
  have hfar : |∑' k : ℕ, rawApply (List.range' 2 K)
      (geometricRowTail (k+2*d+1)) n| ≤ 2*Real.exp 12*3^n/(2*(d : ℝ))^(n-1) := by
    have he (k : ℕ) : k+(2*d-1)+2=k+2*d+1 := by omega
    have he2 : 2*d-1+1=2*d := by omega
    simpa only [he, he2, Nat.cast_mul, Nat.cast_ofNat] using
      rows_tail_bound K (2*d-1) n (by omega) (by omega) hn
  calc
    _ ≤ rate d^n*(2*Real.exp 12*3^n/(2*(d : ℝ))^(n-1)) :=
      mul_le_mul_of_nonneg_left hfar (pow_nonneg hp.le _)
    _ ≤ ((d : ℝ)/2)^n*(2*Real.exp 12*3^n/(2*(d : ℝ))^(n-1)) := by
      gcongr
      exact rate_upper_half d (by omega)
    _ = 2*Real.exp 12*(((d : ℝ)/2)^n*3^n/(2*(d : ℝ))^(n-1)) := by ring
    _ = _ := by rw [scaled_power_identity (d : ℝ) (by positivity) n (by omega)]; ring

lemma far_window_bound (d K H : ℕ) (hd : 12 ≤ d) (hK : K ≤ d)
    (hH : 420*d ≤ H) :
    (∑ h ∈ Finset.range d, rate d^(H+h) *
      |∑' k : ℕ, rawApply (List.range' 2 K) (geometricRowTail (k+2*d+1)) (H+h)|) <
      Real.exp (-48)/(12*(d : ℝ)) := by
  have hs : (∑ h ∈ Finset.range d, rate d^(H+h) *
      |∑' k : ℕ, rawApply (List.range' 2 K) (geometricRowTail (k+2*d+1)) (H+h)|) ≤
      4*Real.exp 12*(d : ℝ)^2*(1/2 : ℝ)^(140*d) := by
    calc
      _ ≤ ∑ _h ∈ Finset.range d, 4*Real.exp 12*d*(1/2 : ℝ)^(140*d) := by
        apply Finset.sum_le_sum
        intro h _
        apply (far_point_bound d K (H+h) hd hK (by nlinarith)).trans
        apply mul_le_mul_of_nonneg_left (three_quarters_power (H+h) (140*d) (by nlinarith))
        positivity
      _ = _ := by simp; ring
  have hdpow : (d : ℝ) ≤ 2^d := by exact_mod_cast (Nat.lt_two_pow_self (n := d)).le
  have hc : 48*Real.exp 60*(d : ℝ)^3 < 2^(140*d) := by
    have he : 48*Real.exp 60 < (2 : ℝ)^133 := by
      have hh := mul_lt_mul_of_pos_left exponential_constant (show (0 : ℝ)<8 by norm_num)
      convert hh using 1
      · ring
      · norm_num
    calc
      _ < (2 : ℝ)^133*(d : ℝ)^3 := mul_lt_mul_of_pos_right he (by positivity)
      _ ≤ (2 : ℝ)^133*((2 : ℝ)^d)^3 := by gcongr
      _ = (2 : ℝ)^(133+3*d) := by rw [← pow_mul, ← pow_add]; congr 1; omega
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  have he : Real.exp 60*Real.exp (-48)=Real.exp 12 := by rw [← Real.exp_add]; norm_num
  have hb := mul_lt_mul_of_pos_right hc (Real.exp_pos (-48))
  have he' : 48*Real.exp 60*(d : ℝ)^3*Real.exp (-48)=48*Real.exp 12*(d : ℝ)^3 := by
    nlinarith [congrArg (fun x : ℝ => 48*(d : ℝ)^3*x) he]
  rw [he'] at hb
  apply hs.trans_lt
  rw [one_div_pow, mul_one_div]
  apply (div_lt_div_iff₀ (by positivity : (0 : ℝ)<2^(140*d))
    (by positivity : (0 : ℝ)<12*(d : ℝ))).mpr
  nlinarith

/-- The mass of all later rows is small after a linear starting index. -/
theorem remaining_window_bound (d K H : ℕ) (hd : 12 ≤ d) (hK : K ≤ d)
    (hH : 420*d ≤ H) :
    (∑ h ∈ Finset.range d, rate d^(H+h) *
      |∑' k : ℕ, rawApply (List.range' 2 K) (geometricRowTail (k+d+1)) (H+h)|) <
      Real.exp (-48)/(6*(d : ℝ)) := by
  have hp := rate_pos d
  have hsplit (n : ℕ) : (∑' k : ℕ,
      rawApply (List.range' 2 K) (geometricRowTail (k+d+1)) n) =
      (∑ k ∈ Finset.range d, rawApply (List.range' 2 K) (geometricRowTail (k+d+1)) n) +
      ∑' k : ℕ, rawApply (List.range' 2 K) (geometricRowTail (k+2*d+1)) n := by
    have hs : Summable (fun k => rawApply (List.range' 2 K)
        (geometricRowTail (k+d+1)) n) := by
      simpa only [show d-1+2=d+1 by omega, Nat.add_assoc] using
        summable_rows (List.range' 2 K) (d-1) n
    simpa only [Nat.add_assoc, show d+(d+1)=2*d+1 by omega] using
      (hs.sum_add_tsum_nat_add d).symm
  have hs : (∑ h ∈ Finset.range d, rate d^(H+h) *
      |∑' k : ℕ, rawApply (List.range' 2 K) (geometricRowTail (k+d+1)) (H+h)|) ≤
      (∑ h ∈ Finset.range d, rate d^(H+h) *
        |∑ k ∈ Finset.range d, rawApply (List.range' 2 K) (geometricRowTail (k+d+1)) (H+h)|) +
      ∑ h ∈ Finset.range d, rate d^(H+h) *
        |∑' k : ℕ, rawApply (List.range' 2 K) (geometricRowTail (k+2*d+1)) (H+h)| := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro h _
    rw [hsplit, ← mul_add]
    exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (pow_nonneg hp.le _)
  have hn := near_window_bound d K H hd hK hH
  have hf := far_window_bound d K H hd hK hH
  have hh : Real.exp (-48)/(6*(d : ℝ))=2*(Real.exp (-48)/(12*(d : ℝ))) := by ring
  linarith


lemma weighted_window_bound (d M H : ℕ) (w : ℕ → ℤ) (r : ℕ → ℝ) (B : ℝ)
    (hr : ∀ j ≤ M, (∑ h ∈ Finset.range d, rate d^(H+j+h)*|r (H+j+h)|) ≤ B) :
    (∑ h ∈ Finset.range d, rate d^(H+h)*
      |∑ j ∈ Finset.range (M+1), (w j : ℝ)*r (H+h+j)|) ≤
      (∑ j ∈ Finset.range (M+1), |(w j : ℝ)|/rate d^j)*B := by
  have hp := rate_pos d
  calc
    _ ≤ ∑ h ∈ Finset.range d, ∑ j ∈ Finset.range (M+1),
        (|(w j : ℝ)|/rate d^j)*(rate d^(H+j+h)*|r (H+j+h)|) := by
      apply Finset.sum_le_sum
      intro h _
      apply (mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (pow_nonneg hp.le _)).trans_eq
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [show H+j+h=(H+h)+j by omega, abs_mul]
      simp only [pow_add]
      field_simp
    _ = ∑ j ∈ Finset.range (M+1), (|(w j : ℝ)|/rate d^j)*
        (∑ h ∈ Finset.range d, rate d^(H+j+h)*|r (H+j+h)|) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intros
      exact (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ j ∈ Finset.range (M+1), (|(w j : ℝ)|/rate d^j)*B := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hr j (by have := Finset.mem_range.mp hj; omega))
        (by positivity)
    _ = _ := (Finset.sum_mul _ _ _).symm

variable (d : ℕ) [NeZero d]

lemma first_combination_window_lower (M H : ℕ) (w : ℕ → ℤ) (hd : 12 ≤ d) :
    Real.exp (-48)*mass (aggregate d M w)/(rate d+1) ≤
      ∑ h ∈ Finset.range d, rate d^(H+h) *
        |∑ j ∈ Finset.range (M+1), (w j : ℝ)*
          rawApply (List.range' 2 (d-2)) (geometricRowTail d) (H+h+j)| := by
  have hp := rate_pos d
  have he : (∑ h ∈ Finset.range d, rate d^(H+h) *
      |∑ j ∈ Finset.range (M+1), (w j : ℝ)*
        rawApply (List.range' 2 (d-2)) (geometricRowTail d) (H+h+j)|) =
      mass (cyclicApply d (List.range' 2 (d-2))
        (convolve d (aggregate d M w) (rowModel d))) := by
    rw [← phase_sum_eq_mass d H]
    apply Finset.sum_congr rfl
    intro h _
    have hm := aggregate_raw_model d M w (List.range' 2 (d-2))
      (geometricRowTail d) (rowModel d) (geometricRowTail_model d (by omega)) (H+h)
    have ha := congrArg abs hm
    simpa only [abs_mul, abs_of_pos (pow_pos hp _)] using ha
  rw [he]
  exact first_row_mass_lower d (d-2) hd (by omega) _

/-- A nonzero leading coefficient is detected in d phases as soon as
H>=420*d, independent of coefficient height and support length. -/
theorem linear_raw_detection (M Q H : ℕ) (w : ℕ → ℤ) (hd : 12 ≤ d)
    (hQ : 4*Q ≤ d.factorial) (hw0 : w 0 ≠ 0)
    (hw : ∀ j ≤ M, |w j| ≤ (Q : ℤ)) (hH : 420*d ≤ H) :
    ∃ n, H ≤ n ∧ n < H+d ∧
      (∑ j ∈ Finset.range (M+1), (w j : ℝ)*rawTail (d-2) (n+j)) ≠ 0 := by
  classical
  have hp := rate_pos d
  have hnorm := aggregate_zero_lower d M Q w hd hQ hw0 hw
  have hc : 0 < mass (aggregate d M w) :=
    lt_of_lt_of_le (by linarith : (0 : ℝ) < ‖aggregate d M w‖) (norm_le_mass _)
  let r : ℕ → ℝ := fun n => ∑' k : ℕ,
    rawApply (List.range' 2 (d-2)) (geometricRowTail (k+d+1)) n
  have hr (j : ℕ) (_hj : j ≤ M) :
      (∑ h ∈ Finset.range d, rate d^(H+j+h)*|r (H+j+h)|) ≤
      Real.exp (-48)/(6*(d : ℝ)) :=
    (remaining_window_bound d (d-2) (H+j) hd (by omega) (by omega)).le
  have hb := weighted_window_bound d M H w r (Real.exp (-48)/(6*(d : ℝ))) hr
  have hmass := weighted_mass_le_three d M Q w hd hQ hw0 hw
  have hrest : (∑ h ∈ Finset.range d, rate d^(H+h)*
      |∑ j ∈ Finset.range (M+1), (w j : ℝ)*r (H+h+j)|) ≤
      Real.exp (-48)*mass (aggregate d M w)/(2*(d : ℝ)) := by
    calc
      _ ≤ _ := hb
      _ ≤ (3*mass (aggregate d M w))*(Real.exp (-48)/(6*(d : ℝ))) :=
        mul_le_mul_of_nonneg_right hmass (by positivity)
      _ = _ := by ring
  have hfirst := first_combination_window_lower d M H w hd
  have hgap : Real.exp (-48)*mass (aggregate d M w)/(2*(d : ℝ)) <
      Real.exp (-48)*mass (aggregate d M w)/(rate d+1) := by
    apply div_lt_div_of_pos_left (by positivity) (by positivity)
    have hu := rate_upper_half d (by omega)
    have hh : (12 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  by_contra hnone
  push_neg at hnone
  have heq (h : ℕ) (hh : h ∈ Finset.range d) :
      (∑ j ∈ Finset.range (M+1), (w j : ℝ)*
        rawApply (List.range' 2 (d-2)) (geometricRowTail d) (H+h+j)) =
      -(∑ j ∈ Finset.range (M+1), (w j : ℝ)*r (H+h+j)) := by
    have hz := hnone (H+h) (by omega) (by have := Finset.mem_range.mp hh; omega)
    have hsplit : (∑ j ∈ Finset.range (M+1), (w j : ℝ)*rawTail (d-2) (H+h+j)) =
        (∑ j ∈ Finset.range (M+1), (w j : ℝ)*
          rawApply (List.range' 2 (d-2)) (geometricRowTail d) (H+h+j)) +
        ∑ j ∈ Finset.range (M+1), (w j : ℝ)*r (H+h+j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [rawTail_split]
      have hidx : d-2+2=d := by omega
      have he (k : ℕ) : k+(d-2)+3=k+d+1 := by omega
      simp only [hidx, he, r, mul_add]
    rw [hsplit] at hz
    linarith
  have he : (∑ h ∈ Finset.range d, rate d^(H+h) *
      |∑ j ∈ Finset.range (M+1), (w j : ℝ)*
        rawApply (List.range' 2 (d-2)) (geometricRowTail d) (H+h+j)|) =
      ∑ h ∈ Finset.range d, rate d^(H+h)*
        |∑ j ∈ Finset.range (M+1), (w j : ℝ)*r (H+h+j)| := by
    apply Finset.sum_congr rfl
    intro h hh
    rw [heq h hh, abs_neg]
  rw [he] at hfirst
  exact (not_lt_of_ge hfirst) (hrest.trans_lt hgap)

/-- Leading zero weights are trimmed; the linear threshold is unchanged. -/
theorem linear_raw_detection_nonzero (M Q H : ℕ) (w : ℕ → ℤ) (hd : 12 ≤ d)
    (hQ : 4*Q ≤ d.factorial) (hne : ∃ j ≤ M, w j ≠ 0)
    (hw : ∀ j ≤ M, |w j| ≤ (Q : ℤ))
    (hH : 420*d ≤ H) :
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
  obtain ⟨N, hN, hNu, hdetect⟩ := linear_raw_detection d (M-i) Q (H+i) v hd hQ hv0 hv
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

end
end LambertLinearPhaseThreshold

#print axioms LambertLinearPhaseThreshold.remaining_window_bound
#print axioms LambertLinearPhaseThreshold.first_combination_window_lower
#print axioms LambertLinearPhaseThreshold.linear_raw_detection
#print axioms LambertLinearPhaseThreshold.linear_raw_detection_nonzero
