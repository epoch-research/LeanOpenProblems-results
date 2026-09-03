import Submission.LambertLongBoundedCombinations

/-! Relative norm bounds for bounded integer combinations of Lambert rows.
The phase threshold does not depend on the coefficient height. This is an
analytic detector only, not a boundary-cleared irrationality proof. -/

namespace LambertRelativeCombinationBound

open Finset LambertDifferenceOperators LambertRawBounds LambertTailRows
  LambertSharperOperatorBounds FactorialGeometricProductBound
  LambertCyclicRowLowerBound LambertCyclicCombinationLowerBound
  LambertUniformRawNonvanishing LambertLongBoundedCombinations

noncomputable section

variable (d : ℕ) [NeZero d]

omit [NeZero d] in
lemma late_mass_bound (M Q : ℕ) (w : ℕ → ℤ) (hd : 12 ≤ d)
    (hQ : 4*Q ≤ d.factorial) (hw : ∀ j ≤ M, |w j| ≤ (Q : ℤ)) :
    (∑ j ∈ Finset.Ico d (M+1), |(w j : ℝ)|/rate d^j) ≤ 1/2 := by
  have hp := rate_pos d
  calc
    _ ≤ ∑ j ∈ Finset.Ico d (M+1), (Q : ℝ)/rate d^j := by
      apply Finset.sum_le_sum
      intro j hj
      apply div_le_div_of_nonneg_right _ (pow_nonneg hp.le _)
      exact_mod_cast hw j (by have := Finset.mem_Ico.mp hj; omega)
    _ = (Q : ℝ)*(∑ j ∈ Finset.Ico d (M+1), 1/rate d^j) := by
      rw [Finset.mul_sum]; simp only [mul_one_div]
    _ ≤ (Q : ℝ)*(2/rate d^d) :=
      mul_le_mul_of_nonneg_left
        (geometric_Ico_bound (rate d) (rate_ge_two d hd) d (M+1)) (Nat.cast_nonneg Q)
    _ = 2*(Q : ℝ)/d.factorial := by rw [rate_pow d (by omega)]; ring
    _ ≤ 1/2 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < d.factorial)).mpr
      have : (4*(Q : ℝ)) ≤ d.factorial := by exact_mod_cast hQ
      linarith

omit [NeZero d] in
lemma aggregate_initial_error (M : ℕ) (w : ℕ → ℤ) (j : ℕ)
    (hj : j ≤ M) (hjd : j < d) :
    |aggregate d M w (j : ZMod d) - (w j : ℝ)/rate d^j| ≤
      ∑ k ∈ Finset.Ico d (M+1), |(w k : ℝ)|/rate d^k := by
  classical
  have hp := rate_pos d
  let t : ℕ → ℝ := fun k =>
    if (k : ZMod d)=(j : ZMod d) then (w k : ℝ)/rate d^k else 0
  have hjm : j ∈ Finset.range (M+1) := Finset.mem_range.mpr (by omega)
  have he : aggregate d M w (j : ZMod d) - (w j : ℝ)/rate d^j =
      ∑ k ∈ (Finset.range (M+1)).erase j, t k := by
    have hs := Finset.sum_erase_add (Finset.range (M+1)) t hjm
    change _ = ∑ k ∈ (Finset.range (M+1)).erase j, t k
    change (∑ k ∈ Finset.range (M+1), t k) - _ = _
    rw [← hs]
    simp [t]
  have hpoint (k : ℕ) (hk : k ∈ (Finset.range (M+1)).erase j) :
      |t k| ≤ if d ≤ k then |(w k : ℝ)|/rate d^k else 0 := by
    obtain ⟨hkj, hkm⟩ := Finset.mem_erase.mp hk
    by_cases hdk : d ≤ k
    · rw [if_pos hdk]
      dsimp [t]
      split_ifs
      · rw [abs_div, abs_of_pos (pow_pos hp _)]
      · simp only [abs_zero]; positivity
    · rw [if_neg hdk]
      have hz : (k : ZMod d) ≠ (j : ZMod d) := by
        intro hz
        have hv := congrArg ZMod.val hz
        rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt hjd] at hv
        exact hkj hv
      simp [t, hz]
  rw [he]
  calc
    _ ≤ ∑ k ∈ (Finset.range (M+1)).erase j, |t k| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ (Finset.range (M+1)).erase j,
        if d ≤ k then |(w k : ℝ)|/rate d^k else 0 := Finset.sum_le_sum hpoint
    _ ≤ ∑ k ∈ Finset.range (M+1), if d ≤ k then |(w k : ℝ)|/rate d^k else 0 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      intro k _ _
      split_ifs <;> positivity
    _ = _ := by
      rw [← Finset.sum_filter]
      congr 1
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega

/-- The weighted absolute mass is controlled by the detected cyclic norm,
not by Q. The bound is uniform in the support length. -/
theorem weighted_mass_bound (M Q : ℕ) (w : ℕ → ℤ) (hd : 12 ≤ d)
    (hQ : 4*Q ≤ d.factorial) (hw0 : w 0 ≠ 0)
    (hw : ∀ j ≤ M, |w j| ≤ (Q : ℤ)) :
    (∑ j ∈ Finset.range (M+1), |(w j : ℝ)|/rate d^j) ≤
      2*((d : ℝ)+1)*‖aggregate d M w‖ := by
  have hp := rate_pos d
  have hnorm := aggregate_zero_lower d M Q w hd hQ hw0 hw
  have hlate := late_mass_bound d M Q w hd hQ hw
  have hhead (j : ℕ) (hj : j ∈ Finset.range (min d (M+1))) :
      |(w j : ℝ)|/rate d^j ≤ ‖aggregate d M w‖+1/2 := by
    have hj' := Finset.mem_range.mp hj
    have he := aggregate_initial_error d M w j (by omega) (by omega)
    have hn : |aggregate d M w (j : ZMod d)| ≤ ‖aggregate d M w‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (aggregate d M w) (j : ZMod d)
    have ha : |(w j : ℝ)/rate d^j| ≤ |aggregate d M w (j : ZMod d)| +
        |aggregate d M w (j : ZMod d)-(w j : ℝ)/rate d^j| := by
      calc
        _ = |aggregate d M w (j : ZMod d) -
          (aggregate d M w (j : ZMod d)-(w j : ℝ)/rate d^j)| := by congr 1; ring
        _ ≤ _ := abs_sub _ _
    rw [abs_div, abs_of_pos (pow_pos hp _)] at ha
    linarith
  have he : Finset.Ico (min d (M+1)) (M+1) = Finset.Ico d (M+1) := by
    ext j
    simp only [Finset.mem_Ico]
    omega
  rw [← Finset.sum_range_add_sum_Ico (f := fun j => |(w j : ℝ)|/rate d^j)
    (min_le_right d (M+1)), he]
  have hh : (∑ j ∈ Finset.range (min d (M+1)), |(w j : ℝ)|/rate d^j) ≤
      (d : ℝ)*(‖aggregate d M w‖+1/2) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (min d (M+1)), (‖aggregate d M w‖+1/2) :=
        Finset.sum_le_sum hhead
      _ = (min d (M+1) : ℕ)*(‖aggregate d M w‖+1/2) := by simp [mul_add]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast min_le_left d (M+1)
  have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  nlinarith


/-- Detection of the first row with its actual cyclic coefficient norm. -/
lemma relative_row_detection (M H : ℕ) (w : ℕ → ℤ) (hd : 12 ≤ d)
    (hc : 0 < ‖aggregate d M w‖) :
    ∃ n, H ≤ n ∧ n < H+d ∧
      Real.exp (-48)*‖aggregate d M w‖/(rate d+1) ≤
        rate d^n * |∑ j ∈ Finset.range (M+1),
          (w j : ℝ)*rawApply (List.range' 2 (d-2)) (geometricRowTail d) (n+j)| := by
  have hp := rate_pos d
  let c := aggregate d M w
  let f := cyclicApply d (List.range' 2 (d-2)) (convolve d c (rowModel d))
  have hlow : Real.exp (-48)*‖c‖/(rate d+1) ≤ ‖f‖ := by
    have ho := cyclicApply_norm_lower d (List.range' 2 (d-2)) (by
      intro k hk
      obtain ⟨i, hi, he⟩ := List.mem_range'.mp hk
      exact (normalized_factorial_le_three_quarters d k hd (by omega) (by omega)).trans
        (by norm_num)) (convolve d c (rowModel d))
    have hprod := lower_product_uniform (d-2) d hd (by omega)
    have hcn := convolution_norm_lower d (by omega) c
    calc
      _ = Real.exp (-48)*(‖c‖/(rate d+1)) := by ring
      _ ≤ ((List.range' 2 (d-2)).map (fun k => 1-(k.factorial : ℝ)/rate d^k)).prod *
          ‖convolve d c (rowModel d)‖ :=
        mul_le_mul hprod hcn (by positivity) ((Real.exp_pos _).le.trans hprod)
      _ ≤ _ := ho
  have hc' : 0 < ‖c‖ := hc
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
lemma weighted_combination_bound (M n : ℕ) (w : ℕ → ℤ) (r : ℕ → ℝ) (B : ℝ)
    (hr : ∀ j ≤ M, rate d^(n+j)*|r (n+j)| ≤ B) :
    rate d^n*|∑ j ∈ Finset.range (M+1), (w j : ℝ)*r (n+j)| ≤
      (∑ j ∈ Finset.range (M+1), |(w j : ℝ)|/rate d^j)*B := by
  have hp := rate_pos d
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
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- The starting index is independent of Q. No integrality of any output
boundary is asserted. -/
theorem relative_raw_detection (M Q H L : ℕ) (w : ℕ → ℤ) (hd : 12 ≤ d)
    (hQ : 4*Q ≤ d.factorial) (hw0 : w 0 ≠ 0)
    (hw : ∀ j ≤ M, |w j| ≤ (Q : ℤ))
    (hL : 4*((d : ℝ)+1)*(d : ℝ)^2 ≤ 2^L) (hH : (d+1)*(L+130) ≤ H) :
    ∃ n, H ≤ n ∧ n < H+d ∧
      (∑ j ∈ Finset.range (M+1), (w j : ℝ)*rawTail (d-2) (n+j)) ≠ 0 := by
  have hp := rate_pos d
  have hnorm := aggregate_zero_lower d M Q w hd hQ hw0 hw
  have hc : 0 < ‖aggregate d M w‖ := by linarith
  obtain ⟨n, hn, hnu, hfirst⟩ := relative_row_detection d M H w hd hc
  let r : ℕ → ℝ := fun m => ∑' k : ℕ,
    rawApply (List.range' 2 (d-2)) (geometricRowTail (k+d+1)) m
  have hr (j : ℕ) (_hj : j ≤ M) :
      rate d^(n+j)*|r (n+j)| ≤ Real.exp (-48)/(4*((d : ℝ)+1)*d) := by
    simpa only [Nat.cast_add, Nat.cast_one, r] using
      (remaining_rows_budget d (d+1) (n+j) L hd (by omega)
        (by simpa only [Nat.cast_add, Nat.cast_one] using hL)
        (hH.trans (by omega))).le
  have hrest := weighted_combination_bound d M n w r
    (Real.exp (-48)/(4*((d : ℝ)+1)*d)) hr
  have hmass := weighted_mass_bound d M Q w hd hQ hw0 hw
  have hrest' : rate d^n*|∑ j ∈ Finset.range (M+1), (w j : ℝ)*r (n+j)| ≤
      Real.exp (-48)*‖aggregate d M w‖/(2*(d : ℝ)) := by
    calc
      _ ≤ _ := hrest
      _ ≤ (2*((d : ℝ)+1)*‖aggregate d M w‖) *
          (Real.exp (-48)/(4*((d : ℝ)+1)*d)) :=
        mul_le_mul_of_nonneg_right hmass (by positivity)
      _ = _ := by field_simp; ring
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
  have hgap : Real.exp (-48)*‖aggregate d M w‖/(2*(d : ℝ)) <
      Real.exp (-48)*‖aggregate d M w‖/(rate d+1) := by
    apply div_lt_div_of_pos_left (by positivity) (by positivity)
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

/-- Trim leading zeros without changing the phase threshold. -/
theorem relative_raw_detection_nonzero (M Q H L : ℕ) (w : ℕ → ℤ) (hd : 12 ≤ d)
    (hQ : 4*Q ≤ d.factorial) (hne : ∃ j ≤ M, w j ≠ 0)
    (hw : ∀ j ≤ M, |w j| ≤ (Q : ℤ))
    (hL : 4*((d : ℝ)+1)*(d : ℝ)^2 ≤ 2^L) (hH : (d+1)*(L+130) ≤ H) :
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
  obtain ⟨N, hN, hNu, hdetect⟩ := relative_raw_detection d (M-i) Q (H+i) L v hd hQ hv0 hv hL
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
lemma relative_logarithmic_budget (hd : 0 < d) :
    4*((d : ℝ)+1)*(d : ℝ)^2 ≤ 2^(3*d.log2+6) := by
  have hdN : d < 2^(d.log2+1) := (Nat.log2_lt hd.ne').mp (by omega)
  have hdR : (d : ℝ) ≤ 2^(d.log2+1) := by exact_mod_cast hdN.le
  have h1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  calc
    _ ≤ 8*(d : ℝ)^3 := by nlinarith
    _ ≤ 8*((2 : ℝ)^(d.log2+1))^3 := by gcongr
    _ = _ := by
      rw [← pow_mul, show (8 : ℝ)=(2 : ℝ)^3 by norm_num, ← pow_add]
      congr 1
      omega

/-- Every nonzero bounded integer vector, with arbitrary finite support,
is detected once H >= (d+1)*(3*log2(d)+136). -/
theorem relative_raw_detection_explicit (M Q H : ℕ) (w : ℕ → ℤ) (hd : 12 ≤ d)
    (hQ : 4*Q ≤ d.factorial) (hne : ∃ j ≤ M, w j ≠ 0)
    (hw : ∀ j ≤ M, |w j| ≤ (Q : ℤ))
    (hH : (d+1)*(3*d.log2+136) ≤ H) :
    ∃ n, H ≤ n ∧ n < H+d ∧
      (∑ j ∈ Finset.range (M+1), (w j : ℝ)*rawTail (d-2) (n+j)) ≠ 0 := by
  exact relative_raw_detection_nonzero d M Q H (3*d.log2+6) w hd hQ hne hw
    (relative_logarithmic_budget d (by omega)) (by convert hH using 1)

end
end LambertRelativeCombinationBound

#print axioms LambertRelativeCombinationBound.weighted_mass_bound
#print axioms LambertRelativeCombinationBound.relative_row_detection
#print axioms LambertRelativeCombinationBound.relative_raw_detection
#print axioms LambertRelativeCombinationBound.relative_raw_detection_nonzero
#print axioms LambertRelativeCombinationBound.relative_raw_detection_explicit
