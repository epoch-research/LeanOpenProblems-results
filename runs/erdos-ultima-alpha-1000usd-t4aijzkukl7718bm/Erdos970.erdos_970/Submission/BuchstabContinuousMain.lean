import Submission.BuchstabContinuousLowerTransfer
import Submission.ContinuousBuchstabDeficit

/-! Complete fixed-depth transfer of the continuous profiles to the actual
prime-sum refinement. This proves positivity at every fixed level s>2,
not at the critical endpoint and not a quadratic Jacobsthal bound. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real Filter FiniteSelberg ContinuousBuchstab
set_option maxHeartbeats 1000000

lemma clipped_lowerModelApprox (n : ℕ) (hn : LowerModelApprox n)
    (t δ : ℝ) (hδ : 0 < δ) : ∃ H : ℕ, ∀ k : ℕ, H ≤ nthPrime k →
    prefixDensity primeMarginal k*(1-deficitProfile n t-δ) ≤
      referenceLower n k (exp (t*log (nthPrime k : ℝ))) := by
  by_cases ht : t < 2
  · refine ⟨0,fun k hk => ?_⟩
    have he : deficitProfile n t=1 := by simp [deficitProfile,ht]
    rw [he]
    apply le_trans _ (referenceLower_nonneg n k _)
    exact mul_nonpos_of_nonneg_of_nonpos (nthPrime_prefix_density_pos k).le (by linarith)
  · have ht2 : 2 ≤ t := le_of_not_gt ht
    by_cases hl : 0 ≤ lowerProfile n t
    · obtain ⟨H,hH⟩ := hn t ht2 δ hδ
      refine ⟨H,fun k hk => ?_⟩
      rw [deficitProfile_eq_one_sub_max n t ht2,max_eq_right hl]
      convert hH k hk using 1 <;> ring
    · refine ⟨0,fun k hk => ?_⟩
      rw [deficitProfile_eq_one_sub_max n t ht2,max_eq_left (le_of_not_ge hl)]
      apply le_trans _ (referenceLower_nonneg n k _)
      exact mul_nonpos_of_nonneg_of_nonpos (nthPrime_prefix_density_pos k).le (by linarith)

/-- Clipped lower deficits transfer through a complete finite prime partition.
The compact part below level two is retained by deficitProfile. -/
theorem upperModelApprox_succ (n : ℕ) (hn : LowerModelApprox n) : UpperModelApprox (n+1) := by
  classical
  intro s hs ε hε
  have hs0 : 0 < s := by linarith
  have heps : 0 < ε*s/4 := by positivity
  obtain ⟨M,hM,hsM,hT⟩ := exists_large_small_terminalAllowance lowerTailCoefficient (ε*s/4) s
    lowerTailCoefficient_nonneg heps
  have hstart : 0 ≤ s-1 := by linarith
  have hanti : AntitoneOn (deficitProfile n) (Set.Ici (s-1)) :=
    (deficitProfile_antitoneOn n).mono (Set.Ici_subset_Ici.mpr hstart)
  have hpos : ∀ x : ℝ, s-1 ≤ x → 0 ≤ deficitProfile n x := fun x _ => deficitProfile_nonneg n x
  have hint := (deficitProfile_integrable n).mono_set (Set.Ioi_subset_Ioi hstart)
  obtain ⟨N,hN,hrect⟩ := exists_rectangular_upper (deficitProfile n) (s-1) (M-1) (ε*s/4)
    (by linarith) heps hanti hpos hint
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let h : ℝ := (M-s)/(N : ℝ)
  let v : ℕ → ℝ := fun j => s-1+h*j
  let δ : ℝ := ε*s/(4*(M-s))
  have hMs : 0 < M-s := sub_pos.mpr hsM
  have hh : 0 < h := div_pos hMs hNr
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hwidth : h*(N : ℝ) = M-s := by dsimp [h]; field_simp
  have hδwidth : δ*(M-s) = ε*s/4 := by dsimp [δ]; field_simp [hMs.ne']
  have hv : Monotone v := by
    intro i j hij
    have hijR : (i : ℝ) ≤ j := by exact_mod_cast hij
    dsimp [v]
    nlinarith only [hh,hijR]
  have hv0 : v 0=s-1 := by simp [v]
  have hvN : v N=M-1 := by dsimp [v]; linarith only [hwidth]
  have hrect' : (∑ j ∈ range N, h*deficitProfile n (v j)) <
      tailIntegral (deficitProfile n) (s-1)+ε*s/4 := by
    have he : M-1-(s-1)=M-s := by ring
    simpa only [he,h,v] using hrect
  choose H hH using (fun j : Fin N => clipped_lowerModelApprox n hn (v j.val) δ hδ)
  let J := univ.sup H
  let B : ℕ → ℝ := fun j => 1-deficitProfile n (v j)-δ
  have hgrid : ∀ k : ℕ, J ≤ nthPrime k → ∀ j ∈ range N,
      prefixDensity primeMarginal k*B j ≤ referenceLower n k (exp (v j*log (nthPrime k : ℝ))) := by
    intro k hk j hj
    exact hH ⟨j,mem_range.mp hj⟩ k ((le_sup (f := H) (mem_univ ⟨j,mem_range.mp hj⟩)).trans hk)
  obtain ⟨K,hK⟩ := exists_profile_lower_deficit_bound n J N s M hs hM v hv hv0 hvN B hgrid (ε/4) (by positivity)
  refine ⟨K,fun k hk => ?_⟩
  apply referenceUpper_succ_le_of_normalized_deficit n k
  have hsum : (∑ j ∈ range N, (1-B j)*(v (j+1)-v j)) =
      (∑ j ∈ range N, h*deficitProfile n (v j))+δ*(M-s) := by
    have he (j : ℕ) : (1-B j)*(v (j+1)-v j) = h*deficitProfile n (v j)+δ*h := by
      dsimp only [B]
      have hvdiff : v (j+1)-v j=h := by dsimp [v]; push_cast; ring
      rw [hvdiff]
      ring
    simp_rw [he]
    rw [sum_add_distrib,sum_const,card_range,nsmul_eq_mul,← hwidth]
    ring
  have hnum : terminalAllowance lowerTailCoefficient M+
      (∑ j ∈ range N, (1-B j)*(v (j+1)-v j)) <
      tailIntegral (deficitProfile n) (s-1)+3*ε*s/4 := by
    rw [hsum,hδwidth]
    linarith only [hT,hrect']
  have hdiv := div_le_div_of_nonneg_right hnum.le hs0.le
  have hraw := hK k hk
  have he : (tailIntegral (deficitProfile n) (s-1)+3*ε*s/4)/s =
      tailIntegral (deficitProfile n) (s-1)/s+3*ε/4 := by field_simp
  rw [he] at hdiv
  have hmodel := deficit_tail_le_upperEnvelope n s hs
  linarith only [hdiv,hraw,hmodel]

/-- Every fixed continuous refinement depth transfers to the actual finite-prime
upper and lower main terms, with arbitrarily small fixed error. -/
theorem continuous_model_transfer (n : ℕ) : UpperModelApprox n ∧ LowerModelApprox n := by
  induction n with
  | zero => exact ⟨upperModelApprox_zero,lowerModelApprox_of_upper 0 upperModelApprox_zero⟩
  | succ n ih =>
      have hu := upperModelApprox_succ n ih.2
      exact ⟨hu,lowerModelApprox_of_upper (n+1) hu⟩

/-- The actual lower main is uniformly positive at EVERY fixed level s>2.
The depth and prime threshold may depend on s. No endpoint assertion is made. -/
theorem exists_referenceLower_positive_above_two (s : ℝ) (hs : 2 < s) :
    ∃ n N : ℕ, ∀ k : ℕ, N ≤ nthPrime k →
      prefixDensity primeMarginal k*((s-2)/(4*s)) ≤
        referenceLower n k (exp (s*log (nthPrime k : ℝ))) := by
  have hs0 : 0 < s := by linarith
  obtain ⟨n,hn⟩ := exists_depth_uniform_positive (s-2) (by linarith)
  have hmodel := hn s (by linarith)
  have hε : 0 < (s-2)/(4*s) := div_pos (sub_pos.mpr hs) (by positivity)
  obtain ⟨N,hN⟩ := (continuous_model_transfer n).2 s hs.le ((s-2)/(4*s)) hε
  refine ⟨n,N,fun k hk => le_trans ?_ (hN k hk)⟩
  apply mul_le_mul_of_nonneg_left _ (nthPrime_prefix_density_pos k).le
  have he : (s-2)/(2*s)=2*((s-2)/(4*s)) := by ring
  rw [he] at hmodel
  linarith only [hmodel]

#print axioms continuous_model_transfer
#print axioms exists_referenceLower_positive_above_two
end Erdos970.RecursiveSieve.Buchstab
