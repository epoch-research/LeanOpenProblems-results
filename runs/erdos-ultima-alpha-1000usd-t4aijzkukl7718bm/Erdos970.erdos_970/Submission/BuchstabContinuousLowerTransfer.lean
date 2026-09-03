import Submission.BuchstabExponentialSource
import Submission.ContinuousBuchstabRectangles

/-! Transfer of a continuous upper model to the actual lower main term at any
fixed level at least two. All finite-node and terminal-tail errors are charged. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real Filter FiniteSelberg
open ContinuousBuchstab
set_option maxHeartbeats 1000000

noncomputable def UpperModelApprox (n : ℕ) : Prop :=
  ∀ s : ℝ, 1 ≤ s → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k : ℕ, N ≤ nthPrime k →
    referenceUpper n k (exp (s*log (nthPrime k : ℝ))) ≤
      prefixDensity primeMarginal k*(1+upperEnvelope n s+ε)

noncomputable def LowerModelApprox (n : ℕ) : Prop :=
  ∀ s : ℝ, 2 ≤ s → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k : ℕ, N ≤ nthPrime k →
    prefixDensity primeMarginal k*(lowerProfile n s-ε) ≤
      referenceLower n k (exp (s*log (nthPrime k : ℝ)))

lemma upperModelApprox_zero : UpperModelApprox 0 := by
  obtain ⟨N,hN⟩ := exists_referenceUpper_exponential_source
  intro s hs ε hε
  refine ⟨N,fun k hk => (hN k hk s hs).trans ?_⟩
  apply mul_le_mul_of_nonneg_left (by linarith) (nthPrime_prefix_density_pos k).le

/-- The continuous tail integral controls the complete prime excess, not merely
the finite sector sum. This lemma retains the actual square cutoff. -/
theorem lowerModelApprox_of_upper (n : ℕ) (hn : UpperModelApprox n) : LowerModelApprox n := by
  classical
  intro s hs ε hε
  have hs0 : 0 < s := by linarith
  have hs1 : 1 ≤ s := by linarith
  have heps : 0 < ε*s/4 := by positivity
  obtain ⟨M,hM,hsM,hT⟩ := exists_large_small_terminalAllowance initialTailCoefficient (ε*s/4) s
    initialTailCoefficient_nonneg heps
  have hstart : 1 ≤ s-1 := by linarith
  have hanti : AntitoneOn (upperEnvelope n) (Set.Ici (s-1)) :=
    (upperEnvelope_antitoneOn n).mono (Set.Ici_subset_Ici.mpr hstart)
  have hpos : ∀ x : ℝ, s-1 ≤ x → 0 ≤ upperEnvelope n x :=
    fun x hx => upperEnvelope_nonneg n x (hstart.trans hx)
  have hint := (upperEnvelope_integrable n).mono_set (Set.Ioi_subset_Ioi hstart)
  obtain ⟨N,hN,hrect⟩ := exists_rectangular_upper (upperEnvelope n) (s-1) (M-1) (ε*s/4)
    (by linarith) heps hanti hpos hint
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let h : ℝ := (M-s)/(N : ℝ)
  let v : ℕ → ℝ := fun j => s-1+h*j
  let δ : ℝ := ε*s/(4*(M-s))
  have hh : 0 < h := div_pos (by linarith) hNr
  have hMs : 0 < M-s := sub_pos.mpr hsM
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
  have hv1 (j : ℕ) : 1 ≤ v j := by
    have hvj := hv (Nat.zero_le j)
    rw [hv0] at hvj
    linarith only [hstart,hvj]
  have hrect' : (∑ j ∈ range N, h*upperEnvelope n (v j)) <
      tailIntegral (upperEnvelope n) (s-1)+ε*s/4 := by
    have he : M-1-(s-1)=M-s := by ring
    simpa only [he,h,v] using hrect
  choose H hH using (fun j : Fin N => hn (v j.val) (hv1 j.val) δ hδ)
  let J := univ.sup H
  let B : ℕ → ℝ := fun j => 1+upperEnvelope n (v j)+δ
  have hgrid : ∀ k : ℕ, J ≤ nthPrime k → ∀ j ∈ range N,
      referenceUpper n k (exp (v j*log (nthPrime k : ℝ))) ≤ prefixDensity primeMarginal k*B j := by
    intro k hk j hj
    exact hH ⟨j,mem_range.mp hj⟩ k ((le_sup (f := H) (mem_univ ⟨j,mem_range.mp hj⟩)).trans hk)
  obtain ⟨K,hK⟩ := exists_profile_upper_excess_bound n J N s M hs1 hM v hv hv0 hvN B hgrid (ε/4) (by positivity)
  refine ⟨K,fun k hk => ?_⟩
  apply referenceLower_ge_of_normalized_excess n k _ _ (primeKeep_exp k s hs)
  have hsum : (∑ j ∈ range N, (B j-1)*(v (j+1)-v j)) =
      (∑ j ∈ range N, h*upperEnvelope n (v j))+δ*(M-s) := by
    have he (j : ℕ) : (B j-1)*(v (j+1)-v j) = h*upperEnvelope n (v j)+δ*h := by
      dsimp only [B]
      have hvdiff : v (j+1)-v j=h := by dsimp [v]; push_cast; ring
      rw [hvdiff]
      ring
    simp_rw [he]
    rw [sum_add_distrib,sum_const,card_range,nsmul_eq_mul,← hwidth]
    ring
  have hnum : terminalAllowance initialTailCoefficient M+
      (∑ j ∈ range N, (B j-1)*(v (j+1)-v j)) <
      tailIntegral (upperEnvelope n) (s-1)+3*ε*s/4 := by
    rw [hsum,hδwidth]
    linarith only [hT,hrect']
  have hdiv := div_le_div_of_nonneg_right hnum.le hs0.le
  have hraw := hK k hk
  have he : (tailIntegral (upperEnvelope n) (s-1)+3*ε*s/4)/s =
      tailIntegral (upperEnvelope n) (s-1)/s+3*ε/4 := by field_simp
  rw [he] at hdiv
  unfold lowerProfile
  linarith only [hdiv,hraw]

#print axioms upperModelApprox_zero
#print axioms lowerModelApprox_of_upper
end Erdos970.RecursiveSieve.Buchstab
