import Submission.SharpPrimeBlockBandDensity
import Submission.CountableBandDensity
import Submission.SquarefreeColoringReduction

/-!
Geometrically budgeted prime-score bands with an arbitrary growth factor b>1.
This constructs positive-density sources, not Sidon sets.
-/
namespace Erdos1206.GeometricPrimeBlockBands
open Finset PrimeBlockVariance MovingPrimeBlockVariance SharpPrimeBlockVariance
open scoped Classical

/-- The variance budget now scales with the actual reciprocal-prime energy.
There is no individual bound on the real weights. -/
theorem exists_good_bands (S : Set ℕ) (hS : 0 < S.lowerDensity)
    (hpos : ∀ n ∈ S, 0 < n) (b : ℝ) (hb : 1 < b) :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ),
      (∀ j p, p ∈ P j → p.Prime) →
      ∃ A : Set ℕ, A ⊆ S ∧ 0 < A.lowerDensity ∧
        ∀ n ∈ A, ∀ j : ℕ,
          (primeSum (P j) (w j) n-movingMean (P j) (w j) n)^2 ≤
            K*b^j*mass (P j) (w j) := by
  obtain ⟨δ,hδ,C,hpre⟩ := prefix_bound_of_positive_lowerDensity hS
  have hb0 : 0 < b := lt_trans zero_lt_one hb
  have hbm1 : 0 < b-1 := sub_pos.mpr hb
  let K : ℝ := 96*b/(δ*(b-1))
  refine ⟨K,by dsimp [K]; positivity,fun P w hP => ?_⟩
  let c : ℕ → ℝ := fun j => δ*(b-1)/(2*b*b^j)
  have hc (j : ℕ) : 0 < c j := by dsimp [c]; positivity
  have hbinv : |(1/b:ℝ)| < 1 := by
    rw [abs_of_pos (one_div_pos.mpr hb0)]
    exact (div_lt_one hb0).mpr hb
  have hgeo := (hasSum_geometric_of_abs_lt_one hbinv).mul_left (δ*(b-1)/(2*b))
  have hcgeo (j : ℕ) : (δ*(b-1)/(2*b))*(1/b:ℝ)^j=c j := by
    dsimp [c]
    simp only [div_pow,one_pow]
    ring
  have hcs : HasSum c (δ/2) := by
    have hh := hgeo.congr_fun (fun j => (hcgeo j).symm)
    convert hh using 1
    field_simp [hb0.ne',hbm1.ne']
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
  · rw [SharpPrimeBlockBandDensity.zero_mass_deviation (P j) (w j) (hP j) hz (hpos n hn.1),hz]
    simp
  · have hfn := hn.2 j
    have hab : |primeSum (P j) (w j) n-movingMean (P j) (w j) n| ≤ R j := by
      apply (div_le_one (hRpos j hz)).mp
      simpa only [f,abs_div,abs_of_pos (hRpos j hz)] using hfn
    have hs := (sq_le_sq₀ (abs_nonneg _) (hRpos j hz).le).mpr hab
    rw [sq_abs,hR2] at hs
    have he : 48*mass (P j) (w j)/c j=K*b^j*mass (P j) (w j) := by
      dsimp [c,K]
      field_simp [hb0.ne',hbm1.ne',hδ.ne']
      ring
    rwa [he] at hs

theorem exists_squarefree_good_bands (b : ℝ) (hb : 1 < b) :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ),
      (∀ j p, p ∈ P j → p.Prime) →
      ∃ A : Set ℕ, (∀ n ∈ A, Squarefree n) ∧ 0 < A.lowerDensity ∧
        ∀ n ∈ A, ∀ j : ℕ,
          (primeSum (P j) (w j) n-movingMean (P j) (w j) n)^2 ≤
            K*b^j*mass (P j) (w j) := by
  exact exists_good_bands {n : ℕ | Squarefree n} squarefree_lowerDensity_pos
    (fun n hn => Nat.pos_of_ne_zero hn.ne_zero) b hb

#print axioms exists_good_bands
#print axioms exists_squarefree_good_bands
end Erdos1206.GeometricPrimeBlockBands
