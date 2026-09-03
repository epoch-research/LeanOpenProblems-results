import Submission.LambertLinearPhaseThreshold

/-!
Nonvanishing for the unfiltered sum of rows at and above a moving cutoff.
This removes no rows by a shift operator. Boundary arithmetic is separate.
-/
namespace LambertUnfilteredDetection

open Finset LambertDifferenceOperators LambertRawBounds LambertTailRows
  LambertSharperOperatorBounds FactorialGeometricProductBound
  LambertCyclicRowLowerBound LambertCyclicCombinationLowerBound
  LambertLongBoundedCombinations LambertCyclicMass LambertUniformRawNonvanishing
  LambertPhaseMassBounds LambertLinearPhaseThreshold

noncomputable section

def tail (d n : ℕ) : ℝ :=
  rawApply (List.range' 2 0) (geometricRowTail d) n +
    ∑' k : ℕ, rawApply (List.range' 2 0) (geometricRowTail (k+d+1)) n

lemma tail_eq (d n : ℕ) : tail d n = geometricRowTail d n +
    ∑' k : ℕ, geometricRowTail (k+d+1) n := by simp [tail, rawApply]

variable (d : ℕ) [NeZero d]

lemma first_combination_window_lower (M H : ℕ) (w : ℕ → ℤ) (hd : 12 ≤ d) :
    Real.exp (-48)*mass (aggregate d M w)/(rate d+1) ≤
      ∑ h ∈ Finset.range d, rate d^(H+h) *
        |∑ j ∈ Finset.range (M+1), (w j : ℝ)*
          rawApply (List.range' 2 0) (geometricRowTail d) (H+h+j)| := by
  have hp := rate_pos d
  have he : (∑ h ∈ Finset.range d, rate d^(H+h) *
      |∑ j ∈ Finset.range (M+1), (w j : ℝ)*
        rawApply (List.range' 2 0) (geometricRowTail d) (H+h+j)|) =
      mass (cyclicApply d (List.range' 2 0)
        (convolve d (aggregate d M w) (rowModel d))) := by
    rw [← phase_sum_eq_mass d H]
    apply Finset.sum_congr rfl
    intro h _
    have hm := aggregate_raw_model d M w (List.range' 2 0)
      (geometricRowTail d) (rowModel d) (geometricRowTail_model d (by omega)) (H+h)
    have ha := congrArg abs hm
    simpa only [abs_mul, abs_of_pos (pow_pos hp _)] using ha
  rw [he]
  exact first_row_mass_lower d 0 hd (by omega) _

/-- A nonzero leading coefficient is detected in d phases as soon as
H>=420*d, independent of coefficient height and support length. -/
theorem unfiltered_detection (M Q H : ℕ) (w : ℕ → ℤ) (hd : 12 ≤ d)
    (hQ : 4*Q ≤ d.factorial) (hw0 : w 0 ≠ 0)
    (hw : ∀ j ≤ M, |w j| ≤ (Q : ℤ)) (hH : 420*d ≤ H) :
    ∃ n, H ≤ n ∧ n < H+d ∧
      (∑ j ∈ Finset.range (M+1), (w j : ℝ)*tail d (n+j)) ≠ 0 := by
  classical
  have hp := rate_pos d
  have hnorm := aggregate_zero_lower d M Q w hd hQ hw0 hw
  have hc : 0 < mass (aggregate d M w) :=
    lt_of_lt_of_le (by linarith : (0 : ℝ) < ‖aggregate d M w‖) (norm_le_mass _)
  let r : ℕ → ℝ := fun n => ∑' k : ℕ,
    rawApply (List.range' 2 0) (geometricRowTail (k+d+1)) n
  have hr (j : ℕ) (_hj : j ≤ M) :
      (∑ h ∈ Finset.range d, rate d^(H+j+h)*|r (H+j+h)|) ≤
      Real.exp (-48)/(6*(d : ℝ)) :=
    (remaining_window_bound d 0 (H+j) hd (by omega) (by omega)).le
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
        rawApply (List.range' 2 0) (geometricRowTail d) (H+h+j)) =
      -(∑ j ∈ Finset.range (M+1), (w j : ℝ)*r (H+h+j)) := by
    have hz := hnone (H+h) (by omega) (by have := Finset.mem_range.mp hh; omega)
    have hsplit : (∑ j ∈ Finset.range (M+1), (w j : ℝ)*tail d (H+h+j)) =
        (∑ j ∈ Finset.range (M+1), (w j : ℝ)*
          rawApply (List.range' 2 0) (geometricRowTail d) (H+h+j)) +
        ∑ j ∈ Finset.range (M+1), (w j : ℝ)*r (H+h+j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      simp only [tail, r, mul_add]
    rw [hsplit] at hz
    linarith
  have he : (∑ h ∈ Finset.range d, rate d^(H+h) *
      |∑ j ∈ Finset.range (M+1), (w j : ℝ)*
        rawApply (List.range' 2 0) (geometricRowTail d) (H+h+j)|) =
      ∑ h ∈ Finset.range d, rate d^(H+h)*
        |∑ j ∈ Finset.range (M+1), (w j : ℝ)*r (H+h+j)| := by
    apply Finset.sum_congr rfl
    intro h hh
    rw [heq h hh, abs_neg]
  rw [he] at hfirst
  exact (not_lt_of_ge hfirst) (hrest.trans_lt hgap)

/-- Leading zero weights are trimmed; the linear threshold is unchanged. -/
theorem unfiltered_detection_nonzero (M Q H : ℕ) (w : ℕ → ℤ) (hd : 12 ≤ d)
    (hQ : 4*Q ≤ d.factorial) (hne : ∃ j ≤ M, w j ≠ 0)
    (hw : ∀ j ≤ M, |w j| ≤ (Q : ℤ))
    (hH : 420*d ≤ H) :
    ∃ n, H ≤ n ∧ n < H+d ∧
      (∑ j ∈ Finset.range (M+1), (w j : ℝ)*tail d (n+j)) ≠ 0 := by
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
  obtain ⟨N, hN, hNu, hdetect⟩ := unfiltered_detection d (M-i) Q (H+i) v hd hQ hv0 hv
    (hH.trans (by omega))
  refine ⟨N-i, by omega, by omega, ?_⟩
  have he : (∑ j ∈ Finset.range (M+1), (w j : ℝ)*tail d (N-i+j)) =
      ∑ j ∈ Finset.range (M-i+1), (v j : ℝ)*tail d (N+j) := by
    have hM : M+1=i+(M-i+1) := by omega
    rw [hM, Finset.sum_range_add]
    have hpref : (∑ j ∈ Finset.range i, (w j : ℝ)*tail d (N-i+j)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [hzero j (Finset.mem_range.mp hj)]
      simp
    rw [hpref, zero_add]
    apply Finset.sum_congr rfl
    intro j hj
    change (w (i+j) : ℝ)*tail d (N-i+(i+j)) = _
    rw [show N-i+(i+j)=N+j by omega]
  rw [he]
  exact hdetect

end
end LambertUnfilteredDetection

#print axioms LambertUnfilteredDetection.unfiltered_detection
#print axioms LambertUnfilteredDetection.unfiltered_detection_nonzero
