import Submission.BuchstabSlowDescendants

/-! A uniform-in-depth bound for the complete actual sharp error recurrence.
This preserves one logarithmic saving and does not assert the quadratic
Jacobsthal endpoint. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Real Finset WeightedMertens
set_option maxHeartbeats 1800000

noncomputable def slowLogThreshold : ℝ := max 100 (100000*smoothProfileError)
noncomputable def slowFiniteIndex : ℕ := ⌈exp slowLogThreshold⌉₊
noncomputable def uniformSlowConstant : ℝ := max slowSourceConstant (4^slowFiniteIndex)

lemma uniformSlowConstant_ge_one : 1 ≤ uniformSlowConstant :=
  slowSourceConstant_ge_one.trans (le_max_left _ _)

lemma slow_small_index (k : ℕ) (hk : log (nthPrime k : ℝ) < slowLogThreshold) : k ≤ slowFiniteIndex := by
  have hp0 : (0 : ℝ) < nthPrime k := by exact_mod_cast (nthPrime_prime k).pos
  have hh := exp_lt_exp.mpr hk
  rw [exp_log hp0] at hh
  have hi : (k : ℝ) ≤ nthPrime k := by exact_mod_cast nthPrime_strictMono.id_le k
  have he : (k : ℝ) ≤ slowFiniteIndex :=
    (hi.trans hh.le).trans (Nat.le_ceil (exp slowLogThreshold))
  exact_mod_cast he

lemma large_slow_double_step (F : ℕ → ℝ → ℝ) (B : ℝ) (hB : 1 ≤ B)
    (hF : ∀ j E, (nthPrime j : ℝ) ≤ E → F j E ≤ B*slowLevelShape j E)
    (k : ℕ) (D : ℝ) (hpkD : (nthPrime k : ℝ) ≤ D)
    (hV : slowLogThreshold ≤ log (nthPrime k : ℝ)) :
    1+(∑ i : Fin k, lowerErrorStep primeMarginal (primeKeep nthPrime) F i.val (D*primeMarginal i.val)) ≤
      B*slowLevelShape k D := by
  have hp0 : (0 : ℝ) < nthPrime k := by exact_mod_cast (nthPrime_prime k).pos
  have hD0 : 0 < D := hp0.trans_le hpkD
  have h100 : 100 ≤ log (nthPrime k : ℝ) := (le_max_left _ _).trans hV
  have hVE : 100000*smoothProfileError ≤ log (nthPrime k : ℝ) := (le_max_right _ _).trans hV
  obtain ⟨hR,hVU,hUV,hRL⟩ := slowOuterCutoff_properties k D hpkD (by linarith only [h100])
  have hc := primeDoubleSlowSum_contraction (slowOuterCutoff k D) hR (log D) (log (nthPrime k : ℝ))
    (by linarith only [h100]) (log_le_log hp0 hpkD) hUV hVU hRL hVE
  have hb0 : 0 ≤ B := by linarith only [hB]
  have hm := mul_le_mul_of_nonneg_left hc (mul_nonneg hb0 hD0.le)
  have he : B*D*((24/25 : ℝ)*(exp ((-2/3 : ℝ)*log D/log (nthPrime k : ℝ))/log (nthPrime k : ℝ))) =
      (24/25 : ℝ)*B*slowLevelShape k D := by unfold slowLevelShape; ring
  rw [he] at hm
  have hu := slow_units_le k D hpkD h100
  have hs : 0 ≤ slowLevelShape k D := (by norm_num : (0 : ℝ) ≤ 1).trans (one_le_slowLevelShape k D hpkD)
  have hbs := mul_le_mul_of_nonneg_right hB hs
  have hd := slow_double_step_le F B hb0 hF k D hD0
  nlinarith only [hd,hm,hu,hbs,mul_nonneg hb0 hs]

/-- One constant controls every refinement depth, every prime prefix, and
every admissible level of the actual positive upper-error recursion. -/
theorem complete_sharp_error_le_uniform_slow (n k : ℕ) (D : ℝ)
    (hpkD : (nthPrime k : ℝ) ≤ D) :
    upperError primeMarginal (primeKeep nthPrime) (scaledSharpSelbergCost nthPrime) n k D ≤
      uniformSlowConstant*slowLevelShape k D := by
  have hB := uniformSlowConstant_ge_one
  have hs : 0 ≤ slowLevelShape k D := (by norm_num : (0 : ℝ) ≤ 1).trans (one_le_slowLevelShape k D hpkD)
  induction n generalizing k D with
  | zero =>
    exact (scaled_sharp_cost_le_slow_profile k D hpkD).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hs)
  | succ n ih =>
    by_cases hk : log (nthPrime k : ℝ) < slowLogThreshold
    · have hki := slow_small_index k hk
      have hp : (4 : ℝ)^k ≤ 4^slowFiniteIndex := pow_le_pow_right₀ (by norm_num) hki
      have hbound : (4 : ℝ)^k ≤ uniformSlowConstant := hp.trans (le_max_right _ _)
      have hm : uniformSlowConstant ≤ uniformSlowConstant*slowLevelShape k D := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_slowLevelShape k D hpkD)
          (by linarith only [hB] : 0 ≤ uniformSlowConstant)
      exact (complete_sharp_error_le_four_pow (n+1) k D).trans (hbound.trans hm)
    · apply max_le (ih k D hpkD hs)
      apply large_slow_double_step _ uniformSlowConstant hB _ k D hpkD (le_of_not_gt hk)
      intro j E hE
      exact ih j E hE ((by norm_num : (0 : ℝ) ≤ 1).trans (one_le_slowLevelShape j E hE))

#print axioms complete_sharp_error_le_uniform_slow
end Erdos970.RecursiveSieve.Buchstab
