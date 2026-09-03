import Submission.SharpPrimeBlockVariance
import Submission.CountableBandDensity
import Submission.SquarefreeColoringReduction

/-!
Countably many prime-score bands with no additive energy loss and with arbitrary
real weights. This constructs positive-density sources, not Sidon sets.
-/
namespace Erdos1206.SharpPrimeBlockBandDensity
open Finset PrimeBlockVariance MovingPrimeBlockVariance SharpPrimeBlockVariance
open scoped Classical

lemma zero_mass_deviation (P : Finset ℕ) (w : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hm : mass P w=0) {n : ℕ} (hn : 0 < n) :
    primeSum P w n-movingMean P w n=0 := by
  have hh := SharpPrimeBlockVariance.moving_variance_le n P w hP
  rw [hm,mul_zero] at hh
  have hsingle := single_le_sum (f := fun k => (primeSum P w k-movingMean P w k)^2)
    (fun k _ => sq_nonneg _) (show n ∈ Icc 1 n from mem_Icc.mpr ⟨hn,le_rfl⟩)
  nlinarith [sq_nonneg (primeSum P w n-movingMean P w n)]

/-- The variance budget now scales with the actual reciprocal-prime energy.
There is no individual bound on the real weights. -/
theorem exists_good_bands (S : Set ℕ) (hS : 0 < S.lowerDensity)
    (hpos : ∀ n ∈ S, 0 < n) :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ),
      (∀ j p, p ∈ P j → p.Prime) →
      ∃ A : Set ℕ, A ⊆ S ∧ 0 < A.lowerDensity ∧
        ∀ n ∈ A, ∀ j : ℕ,
          (primeSum (P j) (w j) n-movingMean (P j) (w j) n)^2 ≤
            K*2^j*mass (P j) (w j) := by
  obtain ⟨δ,hδ,C,hpre⟩ := prefix_bound_of_positive_lowerDensity hS
  let K : ℝ := 192/δ
  refine ⟨K,by dsimp [K]; positivity,fun P w hP => ?_⟩
  let c : ℕ → ℝ := fun j => δ/(4*2^j)
  have hc (j : ℕ) : 0 < c j := by dsimp [c]; positivity
  have hgeo := (hasSum_geometric_of_abs_lt_one (by norm_num : |(1/2:ℝ)| < 1)).mul_left (δ/4)
  have hcgeo (j : ℕ) : (δ/4)*(1/2:ℝ)^j=c j := by
    dsimp [c]
    simp only [div_pow,one_pow]
    ring
  have hcs : HasSum c (δ/2) := by
    have hh := hgeo.congr_fun (fun j => (hcgeo j).symm)
    convert hh using 1; ring
  let R : ℕ → ℝ := fun j => Real.sqrt (48*mass (P j) (w j)/c j)
  have hR2 (j : ℕ) : (R j)^2=48*mass (P j) (w j)/c j :=
    Real.sq_sqrt (div_nonneg (mul_nonneg (by norm_num) (mass_nonneg _ _)) (hc j).le)
  have hRpos (j : ℕ) (hh : mass (P j) (w j) ≠ 0) : 0 < R j := by
    apply Real.sqrt_pos.mpr
    exact div_pos (mul_pos (by norm_num) (lt_of_le_of_ne (mass_nonneg _ _) (Ne.symm hh))) (hc j)
  let f : ℕ → ℕ → ℝ := fun j n =>
    (primeSum (P j) (w j) n-movingMean (P j) (w j) n)/R j
  have hmoment (j N : ℕ) : (∑ n ∈ Icc 1 N, (f j n)^2) ≤ (N:ℝ)*c j := by
    by_cases hz : mass (P j) (w j)=0
    · have hRz : R j=0 := by simp [R,hz]
      simp only [f,hRz,div_zero,zero_pow (by decide : 2 ≠ 0),sum_const_zero]
      exact mul_nonneg (Nat.cast_nonneg N) (hc j).le
    · have hh := SharpPrimeBlockVariance.moving_variance_le N (P j) (w j) (hP j)
      dsimp only [f]
      simp_rw [div_pow]
      rw [←sum_div]
      apply (div_le_iff₀ (sq_pos_of_pos (hRpos j hz))).mpr
      rw [hR2]
      have he : (N:ℝ)*c j*(48*mass (P j) (w j)/c j)=48*N*mass (P j) (w j) := by
        field_simp [(hc j).ne']
      rwa [he]
  let A : Set ℕ := {n | n ∈ S ∧ ∀ j, |f j n| ≤ 1}
  have hA : 0 < A.lowerDensity := CountableBandDensity.lowerDensity_pos_of_prefix
    S f c hpos hpre (fun j => (hc j).le) hcs.summable hmoment (by rw [hcs.tsum_eq]; linarith)
  refine ⟨A,fun _ h => h.1,hA,fun n hn j => ?_⟩
  by_cases hz : mass (P j) (w j)=0
  · rw [zero_mass_deviation (P j) (w j) (hP j) hz (hpos n hn.1),hz]
    simp
  · have hfn := hn.2 j
    have hab : |primeSum (P j) (w j) n-movingMean (P j) (w j) n| ≤ R j := by
      apply (div_le_one (hRpos j hz)).mp
      simpa only [f,abs_div,abs_of_pos (hRpos j hz)] using hfn
    have hs := (sq_le_sq₀ (abs_nonneg _) (hRpos j hz).le).mpr hab
    rw [sq_abs,hR2] at hs
    have he : 48*mass (P j) (w j)/c j=K*2^j*mass (P j) (w j) := by
      dsimp [c,K]
      field_simp
      ring
    rwa [he] at hs

theorem exists_squarefree_good_bands :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ),
      (∀ j p, p ∈ P j → p.Prime) →
      ∃ A : Set ℕ, (∀ n ∈ A, Squarefree n) ∧ 0 < A.lowerDensity ∧
        ∀ n ∈ A, ∀ j : ℕ,
          (primeSum (P j) (w j) n-movingMean (P j) (w j) n)^2 ≤
            K*2^j*mass (P j) (w j) := by
  exact exists_good_bands {n : ℕ | Squarefree n} squarefree_lowerDensity_pos
    (fun n hn => Nat.pos_of_ne_zero hn.ne_zero)

#print axioms zero_mass_deviation
#print axioms exists_good_bands
#print axioms exists_squarefree_good_bands
end Erdos1206.SharpPrimeBlockBandDensity
