import Submission.BuchstabEulerBase
import Submission.ContinuousBuchstabSlowDeficit

/-! Quantitative all-depth comparisons of the actual finite-prime main
recurrences. The Euler-coordinate discretization is paid for by an explicit
linear-in-depth shift of log(D), with no exceptional prime prefix.
No estimate for the separate arithmetic error costs is inferred here. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Real Set Finset MeasureTheory Filter FiniteSelberg ContinuousBuchstab
set_option maxHeartbeats 2000000

def EulerUpperDomination (C B H : ℝ) (n : ℕ) : Prop :=
  ∀ k : ℕ, ∀ s : ℝ, 1 ≤ s →
    referenceUpper n k (exp (s*eulerCoordinate C k+(2*(n : ℝ)+1)*B)) ≤
      prefixDensity primeMarginal k*(1+augmentedUpper H n s)

lemma euler_lower_of_upper (C B H : ℝ) (hC : 0 < C) (hB0 : 0 ≤ B) (hH : 0 ≤ H)
    (hB : ∀ i : ℕ, |eulerCoordinate C i-log (nthPrime i : ℝ)| ≤ B)
    (n : ℕ) (hU : EulerUpperDomination C B H n) (k : ℕ) (s : ℝ) (hs : 2 ≤ s) :
    prefixDensity primeMarginal k*(1-tailIntegral (augmentedUpper H n) (s-1)/s) ≤
      referenceLower n k (exp (s*eulerCoordinate C k+(2*(n : ℝ)+2)*B)) := by
  have hb : B ≤ (2*(n : ℝ)+1)*B := by
    have hn := Nat.cast_nonneg (α := ℝ) n
    nlinarith only [hB0,hn]
  have hh := referenceLower_euler_step C B ((2*(n : ℝ)+1)*B) hC hB hb n
    (augmentedUpper H n) (augmentedUpper_antitone H hH n)
    (augmentedUpper_nonneg H hH n) (augmentedUpper_integrable H hH n) hU k s hs
  have he : s*eulerCoordinate C k+(2*(n : ℝ)+1)*B+B =
      s*eulerCoordinate C k+(2*(n : ℝ)+2)*B := by ring
  rwa [he] at hh

lemma euler_clipped_lower_of_upper (C B H : ℝ) (hC : 0 < C) (hB0 : 0 ≤ B) (hH : 0 ≤ H)
    (hB : ∀ i : ℕ, |eulerCoordinate C i-log (nthPrime i : ℝ)| ≤ B)
    (n : ℕ) (hU : EulerUpperDomination C B H n) (k : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    prefixDensity primeMarginal k*(1-slowDeficit (augmentedUpper H n) s) ≤
      referenceLower n k (exp (s*eulerCoordinate C k+(2*(n : ℝ)+2)*B)) := by
  by_cases hs2 : s < 2
  · simpa only [slowDeficit,if_pos hs2,sub_self,mul_zero] using referenceLower_nonneg n k _
  · have hh := euler_lower_of_upper C B H hC hB0 hH hB n hU k s (le_of_not_gt hs2)
    rw [slowDeficit,if_neg hs2]
    by_cases htail : tailIntegral (augmentedUpper H n) (s-1)/s ≤ 1
    · rwa [min_eq_right htail]
    · rw [min_eq_left (le_of_not_ge htail),sub_self,mul_zero]
      exact referenceLower_nonneg n k _

lemma eulerUpperDomination_succ (C B H : ℝ) (hC : 0 < C) (hB0 : 0 ≤ B) (hH : 0 ≤ H)
    (hB : ∀ i : ℕ, |eulerCoordinate C i-log (nthPrime i : ℝ)| ≤ B)
    (n : ℕ) (hU : EulerUpperDomination C B H n) : EulerUpperDomination C B H (n+1) := by
  intro k s hs
  have humeas := augmentedUpper_measurable H n
  have hu0 := augmentedUpper_nonneg H hH n
  have huB := augmentedUpper_slow_bound H hH n
  have huI := augmentedUpper_integrable H hH n
  let A : ℝ := 2000+H*(19/20 : ℝ)^n
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hh := referenceUpper_euler_step C B ((2*(n : ℝ)+2)*B) hC hB n
    (slowDeficit (augmentedUpper H n)) (slowDeficit_antitone _ huI hu0)
    (fun x hx => slowDeficit_nonneg _ hu0 x)
    (slowDeficit_integrable _ humeas A hA hu0 huB)
    (euler_clipped_lower_of_upper C B H hC hB0 hH hB n hU) k s hs
  have ht := (slowDeficit_tail_le _ humeas A hA hu0 huB s hs).trans
    (augmentedUpper_next H hH n s hs)
  have hmain := hh.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl ht)
    (nthPrime_prefix_density_pos k).le)
  have he : s*eulerCoordinate C k+(2*(n : ℝ)+2)*B+B =
      s*eulerCoordinate C k+(2*((n+1 : ℕ) : ℝ)+1)*B := by push_cast; ring
  rwa [he] at hmain

/-- Every recursion depth and every prime prefix are controlled by the same
constants. The dependence on depth is explicit in the logarithmic shift. -/
theorem referenceUpper_euler_uniform (C B H : ℝ) (hC : 0 < C) (hB0 : 0 ≤ B) (hH : 0 ≤ H)
    (hB : ∀ i : ℕ, |eulerCoordinate C i-log (nthPrime i : ℝ)| ≤ B)
    (hsource : ∀ k : ℕ, ∀ s : ℝ, 1 ≤ s →
      referenceUpper 0 k (exp (s*eulerCoordinate C k+B)) ≤
        prefixDensity primeMarginal k*(1+H*exp ((-2/3 : ℝ)*s))) (n : ℕ) :
    EulerUpperDomination C B H n := by
  induction n with
  | zero =>
      intro k s hs
      have hh := hsource k s hs
      have hextra := upperEnvelope_nonneg 0 s hs
      have hbound : 1+H*exp ((-2/3 : ℝ)*s) ≤ 1+augmentedUpper H 0 s := by
        simp only [augmentedUpper,pow_zero,mul_one]
        linarith only [hextra]
      have hmain := hh.trans (mul_le_mul_of_nonneg_left hbound (nthPrime_prefix_density_pos k).le)
      simpa only [Nat.cast_zero,mul_zero,zero_add,one_mul] using hmain
  | succ n ih => exact eulerUpperDomination_succ C B H hC hB0 hH hB n ih

/-- An explicit lower main bound. No asymptotic limit or depth-dependent
prime threshold is used, and the actual square cutoff remains satisfied. -/
theorem referenceLower_euler_quantitative (C B H : ℝ) (hC : 0 < C) (hB0 : 0 ≤ B) (hH : 0 ≤ H)
    (hB : ∀ i : ℕ, |eulerCoordinate C i-log (nthPrime i : ℝ)| ≤ B)
    (hsource : ∀ k : ℕ, ∀ s : ℝ, 1 ≤ s →
      referenceUpper 0 k (exp (s*eulerCoordinate C k+B)) ≤
        prefixDensity primeMarginal k*(1+H*exp ((-2/3 : ℝ)*s)))
    (n k : ℕ) (s : ℝ) (hs : 2 ≤ s) :
    prefixDensity primeMarginal k*((s-2-(24000+2*H)*(19/20 : ℝ)^n)/s) ≤
      referenceLower n k (exp (s*eulerCoordinate C k+(2*(n : ℝ)+2)*B)) := by
  have hU := referenceUpper_euler_uniform C B H hC hB0 hH hB hsource n
  have hh := euler_lower_of_upper C B H hC hB0 hH hB n hU k s hs
  have hs0 : 0 < s := by linarith
  have ht := div_le_div_of_nonneg_right (augmentedUpper_tail_bound H hH n s hs) hs0.le
  apply le_trans _ hh
  apply mul_le_mul_of_nonneg_left _ (nthPrime_prefix_density_pos k).le
  have he : (s-2-(24000+2*H)*(19/20 : ℝ)^n)/s =
      1-(2+(24000+2*H)*(19/20 : ℝ)^n)/s := by field_simp; ring
  rw [he]
  exact sub_le_sub_left ht 1

/-- Unconditional existence of all constants in the quantitative main bound.
This theorem does not charge the separate coefficient/error recurrence, and
therefore is not itself an interval-survivor or Jacobsthal theorem. -/
theorem exists_quantitative_euler_main : ∃ C > (0 : ℝ), ∃ B > (0 : ℝ), ∃ H > (0 : ℝ),
    (∀ k : ℕ, |eulerCoordinate C k-log (nthPrime k : ℝ)| ≤ B) ∧
    ∀ n k : ℕ, ∀ s : ℝ, 2 ≤ s →
      prefixDensity primeMarginal k*((s-2-(24000+2*H)*(19/20 : ℝ)^n)/s) ≤
        referenceLower n k (exp (s*eulerCoordinate C k+(2*(n : ℝ)+2)*B)) := by
  obtain ⟨C,hC,B,hB0,hB⟩ := exists_eulerCoordinate_log_remainder
  obtain ⟨H,hH,hsource⟩ := exists_global_euler_upper_source C B hC hB0.le hB
  exact ⟨C,hC,B,hB0,H,hH,hB,
    referenceLower_euler_quantitative C B H hC hB0.le hH.le hB hsource⟩

#print axioms referenceUpper_euler_uniform
#print axioms referenceLower_euler_quantitative
#print axioms exists_quantitative_euler_main
end Erdos970.RecursiveSieve.Buchstab
