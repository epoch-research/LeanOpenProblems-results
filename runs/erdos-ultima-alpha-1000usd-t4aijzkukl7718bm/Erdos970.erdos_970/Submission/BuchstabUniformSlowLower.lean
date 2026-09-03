import Submission.BuchstabUniformSlowError

/-! The matching lower-node cost bound, uniform in refinement depth. It is an
error estimate only; no endpoint main term is supplied. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Real Finset WeightedMertens
set_option maxHeartbeats 1800000

lemma slow_child_identity (i : ℕ) (D : ℝ) (hD : 0 < D) :
    slowLevelShape i (D*primeMarginal i) = D*exp (2/3 : ℝ)*
      (exp (-((2/3 : ℝ)*log D)/log (nthPrime i : ℝ))/
        ((nthPrime i : ℝ)*log (nthPrime i : ℝ))) := by
  have hp : (0 : ℝ) < nthPrime i := by exact_mod_cast (nthPrime_prime i).pos
  have hl : 0 < log (nthPrime i : ℝ) := log_pos (by exact_mod_cast (nthPrime_prime i).one_lt)
  unfold slowLevelShape primeMarginal
  simp only [mul_one_div,log_div hD.ne' hp.ne']
  have he : (-2/3 : ℝ)*(log D-log (nthPrime i : ℝ))/log (nthPrime i : ℝ) =
      2/3+(-((2/3 : ℝ)*log D)/log (nthPrime i : ℝ)) := by
    field_simp
    ring
  rw [he,exp_add]
  field_simp

lemma slow_child_sum_kept (k : ℕ) (D : ℝ) (hkeep : primeKeep nthPrime k D) :
    (∑ i : Fin k, slowLevelShape i.val (D*primeMarginal i.val)) ≤
      ((3/2 : ℝ)+24*smoothProfileError)*slowLevelShape k D := by
  let V := log (nthPrime k : ℝ)
  let L := log D
  have hp : (0 : ℝ) < nthPrime k := by exact_mod_cast (nthPrime_prime k).pos
  have hD : 0 < D := (sq_pos_of_pos hp).trans_le hkeep
  have hV0 : 0 < V := log_pos (by exact_mod_cast (nthPrime_prime k).one_lt)
  have hVlow : (2/3 : ℝ) < V := prime_log_gt_two_thirds k
  have hL : 2*V ≤ L := by
    have hh := log_le_log (sq_pos_of_pos hp) hkeep
    rw [log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    exact hh
  have ha : (4/3 : ℝ)*V ≤ (2/3 : ℝ)*L := by linarith only [hL]
  have hs := prime_reciprocalExpSquare_sum_upper (nthPrime k) (nthPrime_prime k).two_le ((2/3 : ℝ)*L) ha
  have hsubset : (∑ p ∈ (nthPrime k).primesBelow,
      exp (-((2/3 : ℝ)*L)/log (p : ℝ))/((p : ℝ)*log (p : ℝ))) ≤
      ∑ p ∈ (nthPrime k+1).primesBelow,
        exp (-((2/3 : ℝ)*L)/log (p : ℝ))/((p : ℝ)*log (p : ℝ)) := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpk,hpp⟩ := Nat.mem_primesBelow.mp hp
      exact Nat.mem_primesBelow.mpr ⟨by omega,hpp⟩
    · intro p hp hnot
      exact div_nonneg (exp_pos _).le (mul_nonneg (Nat.cast_nonneg _) (log_natCast_nonneg _))
  have hquarter : 1/((2/3 : ℝ)*L) ≤ (3/4 : ℝ)/V := by
    apply (div_le_div_iff₀ (by linarith only [hL,hV0] : 0 < (2/3 : ℝ)*L) hV0).mpr
    linarith only [hL]
  have hi : 1/V ≤ (3/2 : ℝ) := (div_le_iff₀ hV0).mpr (by linarith only [hVlow])
  have hm := mul_le_mul_of_nonneg_left hi (show 0 ≤ 8*smoothProfileError/V by have := smoothProfileError_pos; positivity)
  have herr : 8*smoothProfileError/V^2 ≤ 12*smoothProfileError/V := by
    convert hm using 1 <;> ring
  have hcoef : 1/((2/3 : ℝ)*L)+8*smoothProfileError/V^2 ≤ ((3/4 : ℝ)+12*smoothProfileError)/V := by
    have hh := add_le_add hquarter herr
    convert hh using 1 <;> ring
  have hexp : exp (2/3 : ℝ) ≤ 2 := by
    have hh := exp_le_exp.mpr (show (2/3 : ℝ) ≤ log 2 by linarith [log_two_gt_d9])
    simpa only [exp_log (by norm_num : (0 : ℝ) < 2)] using hh
  have hsum := (hsubset.trans hs).trans (mul_le_mul_of_nonneg_left hcoef (exp_pos _).le)
  have he : (∑ i : Fin k, slowLevelShape i.val (D*primeMarginal i.val)) ≤
      D*exp (2/3 : ℝ)*(exp (-((2/3 : ℝ)*L)/V)*(((3/4 : ℝ)+12*smoothProfileError)/V)) := by
    simp_rw [slow_child_identity _ D hD]
    rw [← mul_sum,nthPrime_prefix_sum (fun p => exp (-((2/3 : ℝ)*log D)/log (p : ℝ))/((p : ℝ)*log (p : ℝ))) k]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  have hh := mul_le_mul_of_nonneg_right hexp
    (show 0 ≤ D*(exp (-((2/3 : ℝ)*L)/V)*(((3/4 : ℝ)+12*smoothProfileError)/V)) by
      have := smoothProfileError_pos
      positivity)
  apply he.trans
  unfold slowLevelShape
  dsimp only [L,V] at hh ⊢
  have hid : -((2/3 : ℝ)*log D)/log (nthPrime k : ℝ) = (-2/3 : ℝ)*log D/log (nthPrime k : ℝ) := by ring
  rw [hid] at hh
  convert hh using 1 <;> ring

lemma lowerErrorStep_le_uniform_slow_profile (F : ℕ → ℝ → ℝ) (B : ℝ) (hB : 1 ≤ B)
    (hF : ∀ j E, (nthPrime j : ℝ) ≤ E → F j E ≤ B*slowLevelShape j E)
    (k : ℕ) (D : ℝ) (hpkD : (nthPrime k : ℝ) ≤ D) :
    lowerErrorStep primeMarginal (primeKeep nthPrime) F k D ≤
      (3+24*smoothProfileError)*B*slowLevelShape k D := by
  classical
  have hshape := one_le_slowLevelShape k D hpkD
  have hB0 : 0 ≤ B := by linarith only [hB]
  have hshape0 : 0 ≤ slowLevelShape k D := by linarith only [hshape]
  unfold lowerErrorStep
  split_ifs with hk
  · have hchild (i : Fin k) : (nthPrime i.val : ℝ) ≤ D*primeMarginal i.val := by
      have hp0 : (0 : ℝ) < nthPrime i.val := by exact_mod_cast (nthPrime_prime i.val).pos
      have hi : (nthPrime i.val : ℝ) ≤ nthPrime k := by exact_mod_cast (nthPrime_strictMono i.isLt).le
      have hki : (nthPrime k : ℝ)^2 ≤ D := hk
      simp only [primeMarginal,mul_one_div]
      apply (le_div_iff₀ hp0).mpr
      nlinarith only [hi,hki,hp0]
    have hs : (∑ i : Fin k, F i.val (D*primeMarginal i.val)) ≤
        B*(((3/2 : ℝ)+24*smoothProfileError)*slowLevelShape k D) := by
      calc
        _ ≤ ∑ i : Fin k, B*slowLevelShape i.val (D*primeMarginal i.val) :=
          sum_le_sum (fun i _ => hF i.val _ (hchild i))
        _ = B*(∑ i : Fin k, slowLevelShape i.val (D*primeMarginal i.val)) := (mul_sum ..).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left (slow_child_sum_kept k D hk) hB0
    have hunit : 1 ≤ B*slowLevelShape k D := one_le_mul_of_one_le_of_one_le hB hshape
    nlinarith only [hs,hunit]
  · have := smoothProfileError_pos
    positivity

/-- The full lower error inherits a single constant, independent of refinement
depth, from the actual uniform upper-error theorem. -/
theorem complete_sharp_lower_error_le_uniform_slow (n k : ℕ) (D : ℝ)
    (hpkD : (nthPrime k : ℝ) ≤ D) :
    lowerErrorStep primeMarginal (primeKeep nthPrime)
      (upperError primeMarginal (primeKeep nthPrime) (scaledSharpSelbergCost nthPrime) n) k D ≤
      (3+24*smoothProfileError)*uniformSlowConstant*slowLevelShape k D :=
  lowerErrorStep_le_uniform_slow_profile _ uniformSlowConstant uniformSlowConstant_ge_one
    (complete_sharp_error_le_uniform_slow n) k D hpkD

#print axioms complete_sharp_lower_error_le_uniform_slow
end Erdos970.RecursiveSieve.Buchstab
