import Submission.QuadraticDivisorMoments
import Submission.SquarefreeHeadDensity

/-! Squarefree values in a fixed quadratic family can have arbitrarily small
total summable nonnegative divisor weight supported on primes and semiprimes. -/
namespace Erdos1206.SquarefreeSmallDivisorWeights
open Finset Filter QuadraticSquarefreeSieve QuadraticRootLattice QuadraticConditionalCounts
  QuadraticDivisorMoments QuadraticSemiprimeDivisibility QuadraticCompositeCounts BoxDensityLimits SquarefreeHeadDensity
open scoped Classical
set_option maxHeartbeats 2000000

/-- This is a parameter-family result. It does not assert a Sidon root set. -/
theorem exists_small_total (a b c : Fin 4 → ℕ)
    (ha : ∀ i, 0 < a i) (hc : ∀ i, 0 < c i) (hQ : ∀ i, Anisotropic (c i) (b i) (a i))
    (hD : ∀ i, (b i:ℤ)^2-4*(c i)*(a i)≠0)
    (hloc : ∀ p, p.Prime → ∃ x : ℕ × ℕ,
      ∀ i, ¬p∣quad (a i) (b i) (c i) x.1 x.2)
    (w : ℕ → ℝ) (hw : ∀ p, 0 ≤ w p)
    (hsupp : ∀ d, ¬LowComplexity d → w d=0)
    (hs : Summable (fun d : ℕ => w d/d))
    {t : ℝ} (ht : 0 < t) :
    ∃ x : ℕ × ℕ, 0 < x.1 ∧ (∀ i, Squarefree (quad (a i) (b i) (c i) x.1 x.2)) ∧
      (∑i,divisorWeight w (quad (a i) (b i) (c i) x.1 x.2)) < t := by
  have hdisc : ∀ i, (b i:ℤ)^2-4*(a i)*(c i)≠0 := by
    intro i
    convert hD i using 1; ring
  obtain ⟨γ,hγ,hγhead⟩ := relative_density a b c ha hc hQ hdisc hloc
  let K (i : Fin 4) : ℝ := constant (c i) (b i) (a i)
  let C : ℝ := ∑i,K i
  have hK (i : Fin 4) : 0 < K i := by
    dsimp [K,constant]
    have := size_pos (c i) (b i) (a i)
    positivity
  have hC : 0 < C := sum_pos (fun i _ => hK i) univ_nonempty
  obtain ⟨H,hH⟩ := QuadraticDivisorMoments.small_weight_tail w hw hs (show 0 < (γ*t)/(2*C) by positivity)
  let S := (range H).filter Nat.Prime
  have hS (p : ℕ) (hp : p∈S) : p.Prime := (mem_filter.mp hp).2
  let δ := headDensity a b c S
  have hδ : 0 < δ := head_density_pos a b c S hS hQ hloc
  let r : ℕ → ℝ := fun p => if LowComplexity p ∧ Avoids S p then w p/p else 0
  have hr (p : ℕ) : 0 ≤ r p := by
    dsimp [r]
    split_ifs
    · exact div_nonneg (hw p) (Nat.cast_nonneg p)
    · exact le_rfl
  have hrs : Summable r := by
    apply Summable.of_nonneg_of_le hr _ hs
    intro p
    dsimp [r]
    by_cases hp : LowComplexity p ∧ Avoids S p
    · simp only [if_pos hp,le_refl]
    · rw [if_neg hp]
      exact div_nonneg (hw p) (Nat.cast_nonneg p)
  have htails : Summable (fun p : ℕ => if H≤p then w p/p else 0) := by
    apply Summable.of_nonneg_of_le _ _ hs
    · intro p; split_ifs
      · exact div_nonneg (hw p) (Nat.cast_nonneg p)
      · exact le_rfl
    · intro p; split_ifs
      · exact le_rfl
      · exact div_nonneg (hw p) (Nat.cast_nonneg p)
  have hrtail : (∑'p,r p) < (γ*t)/(2*C) := by
    apply lt_of_le_of_lt (hrs.tsum_le_tsum _ htails) hH
    intro p
    by_cases hp : LowComplexity p ∧ Avoids S p
    · have hlarge := head_survivor_large hp.1.one_lt hp.2
      simp only [r,if_pos hp,if_pos hlarge,le_refl]
    · rw [show r p=0 from if_neg hp]
      split_ifs
      · exact div_nonneg (hw p) (Nat.cast_nonneg p)
      · exact le_rfl
  let l (i : Fin 4) := ∑'p,w p*frequency a b c S i p
  have hlim (i : Fin 4) := moment_tendsto a b c S hS w hw hsupp hs i (hc i) (hQ i) (hD i)
  have hls (i : Fin 4) : Summable (fun p => w p*frequency a b c S i p) := by
    apply Summable.of_nonneg_of_le
      (fun p => (frequency_bound a b c S hδ.le w hw i (hQ i) (hD i) p).1)
      (fun p => (frequency_bound a b c S hδ.le w hw i (hQ i) (hD i) p).2)
      (hrs.mul_left (δ*K i))
  have hlbound (i : Fin 4) : l i ≤ δ*K i*(∑'p,r p) := by
    have hh := (hls i).tsum_le_tsum
      (fun p => (frequency_bound a b c S hδ.le w hw i (hQ i) (hD i) p).2)
      (hrs.mul_left (δ*K i))
    simpa only [l,tsum_mul_left] using hh
  have htotal : (∑i,l i) < γ*δ*t := by
    calc
      _ ≤ ∑i,δ*K i*(∑'p,r p) := sum_le_sum (fun i _ => hlbound i)
      _ = δ*C*(∑'p,r p) := by dsimp only [C]; rw [←sum_mul,←mul_sum]
      _ < δ*C*((γ*t)/(2*C)) := mul_lt_mul_of_pos_left hrtail (mul_pos hδ hC)
      _ = γ*δ*t/2 := by field_simp
      _ < _ := by nlinarith [mul_pos (mul_pos hγ hδ) ht]
  by_contra! hnone
  have hineq : ∀ᶠ N : ℕ in atTop, γ*δ*t ≤
        ∑i,(∑x∈positiveBox N (Head a b c S),
          divisorWeight w (quad (a i) (b i) (c i) x.1 x.2))/(N:ℝ)^2 := by
    filter_upwards [hγhead S hS,eventually_gt_atTop 0] with N hN hNpos
    have hNR : (0:ℝ) < N := by exact_mod_cast hNpos
    have hh : t*((squarefreeBox a b c S N).card:ℝ) ≤
        ∑x∈positiveBox N (Head a b c S),∑i,divisorWeight w (quad (a i) (b i) (c i) x.1 x.2) := by
      calc
        _ = ∑_x∈squarefreeBox a b c S N,t := by simp [mul_comm]
        _ ≤ ∑x∈squarefreeBox a b c S N,∑i,divisorWeight w (quad (a i) (b i) (c i) x.1 x.2) := by
          apply sum_le_sum
          intro x hx
          obtain ⟨_,hxp,_,hxsf⟩ := (mem_squarefreeBox _ _ _ _ _ _).mp hx
          exact hnone x hxp hxsf
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg (squarefreeBox_subset a b c S N)
          (fun x _ _ => sum_nonneg (fun i _ => divisorWeight_nonneg hw _))
    have hh' := (mul_le_mul_of_nonneg_left hN ht.le).trans hh
    rw [sum_comm] at hh'
    rw [←sum_div]
    apply (le_div_iff₀ (sq_pos_of_pos hNR)).mpr
    convert hh' using 1; ring
  have hleft : Tendsto (fun _N : ℕ => γ*δ*t) atTop (nhds (γ*δ*t)) := tendsto_const_nhds
  have hright := tendsto_finset_sum (univ : Finset (Fin 4)) (fun i _ => hlim i)
  have hh := le_of_tendsto_of_tendsto hleft hright hineq
  change γ*δ*t ≤ ∑i,l i at hh
  exact (not_le_of_gt htotal) hh

#print axioms exists_small_total
end Erdos1206.SquarefreeSmallDivisorWeights
