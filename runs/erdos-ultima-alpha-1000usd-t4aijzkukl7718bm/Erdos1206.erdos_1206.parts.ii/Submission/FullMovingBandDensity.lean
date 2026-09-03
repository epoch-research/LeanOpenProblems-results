import Submission.FiniteShortBandSelection
import Submission.PeriodicResidueCounts
import Submission.FiniteHeadApproximation
import Submission.Compactness

/-! Every finite-square-energy strongly additive score has a positive-lower-
density short band about its moving center, with a suitable fixed shift. -/
namespace Erdos1206.FullMovingBandDensity
open Finset FullPrimeScoreVariance FiniteHeadApproximation ConicContrastMoments
open scoped Classical

lemma bad_count (f : ℕ → ℝ) {r c : ℝ} (hr : 0 < r) (N : ℕ)
    (hm : (∑n∈Icc 1 N,f n^2) ≤ c*r^2*N) :
    (((Icc 1 N).filter (fun n => r < |f n|)).card:ℝ) ≤ c*N := by
  let B := (Icc 1 N).filter (fun n => r < |f n|)
  have hh : r^2*(B.card:ℝ) ≤ c*r^2*N := by
    calc
      _ = ∑_n∈B,r^2 := by simp [mul_comm]
      _ ≤ ∑n∈B,f n^2 := by
        apply sum_le_sum
        intro n hn
        simpa only [sq_abs] using (sq_le_sq₀ hr.le (abs_nonneg _)).mpr (mem_filter.mp hn).2.le
      _ ≤ ∑n∈Icc 1 N,f n^2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)
      _ ≤ _ := hm
  nlinarith [sq_pos_of_pos hr]

/-- The shift is allowed to depend on the desired width. Neither the score
nor any resulting band is asserted to separate cubic collisions. -/
theorem exists_band (w : ℕ → ℝ)
    (hs : Summable (fun p : ℕ => if p.Prime then w p^2/p else 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ μ : ℝ,0 < ({n : ℕ | 0 < n ∧ |deviation w n-μ| < ε} : Set ℕ).lowerDensity := by
  let r := ε/2
  have hr : 0 < r := half_pos hε
  obtain ⟨δ,hδ,_,C,hC⟩ := FiniteShortBandSelection.exists_uniform_band (energy_nonneg w) hr
  obtain ⟨H,hH⟩ := tail_variance_small w hs (show 0 < (δ/2)*r^2 by positivity)
  let D := period H
  have hD : 0 < D := period_pos H
  obtain ⟨μ,_,hμ⟩ := hC (range D) (by simpa using hD.ne') (score w H)
    (by simpa only [card_range] using range_moment_le w hs H)
  let B := (range D).filter (fun n => |score w H n-μ| < r)
  have hB : B ⊆ range D := filter_subset _ _
  have hBD : δ*(D:ℝ) ≤ B.card := by simpa only [card_range] using hμ
  let M := H^2+1
  let A : Set ℕ := {n | 0 < n ∧ |deviation w n-μ| < ε}
  refine ⟨μ,?_⟩
  apply positive_lowerDensity_of_prefix_bound (A := A) (δ := δ/2) (C := (D:ℝ)+M) (half_pos hδ)
  intro N
  let T := (range N).filter (fun n => n%D ∈ B)
  let G := T.filter (fun n => M ≤ n ∧ |deviation (tailWeight w H) n| ≤ r)
  let U := (Icc 1 N).filter (fun n => r < |deviation (tailWeight w H) n|)
  let V := (range N).filter (fun n => n ∈ A)
  have hT : δ*(N:ℝ) ≤ (T.card:ℝ)+D := PeriodicResidueCounts.prefix_lower N D B hD hB hBD
  have hU : (U.card:ℝ) ≤ (δ/2)*N :=
    bad_count (fun n => deviation (tailWeight w H) n) hr N (hH N)
  have hsub : T ⊆ G ∪ range M ∪ U := by
    intro n hn
    by_cases hm : M ≤ n
    · by_cases ht : |deviation (tailWeight w H) n| ≤ r
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hn,hm,ht⟩))
      · apply mem_union_right
        refine mem_filter.mpr ⟨mem_Icc.mpr ⟨?_,(mem_range.mp (mem_filter.mp hn).1).le⟩,lt_of_not_ge ht⟩
        dsimp only [M] at hm
        omega
    · exact mem_union_left _ (mem_union_right _ (mem_range.mpr (lt_of_not_ge hm)))
  have hcard : (T.card:ℝ) ≤ (G.card:ℝ)+M+U.card := by
    have hh := (card_le_card hsub).trans
      ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _))
    simp only [card_range] at hh
    exact_mod_cast hh
  have hGV : G ⊆ V := by
    intro n hn
    obtain ⟨hnT,hm,ht⟩ := mem_filter.mp hn
    obtain ⟨hnN,hnB⟩ := mem_filter.mp hnT
    have hn0 : 0 < n := by dsimp only [M] at hm; omega
    have hnH : H^2 ≤ n := by dsimp only [M] at hm; omega
    have hhead : |score w H n-μ| < r := by
      have hh := (mem_filter.mp hnB).2
      rwa [score_mod] at hh
    have he : deviation w n-μ=(score w H n-μ)+deviation (tailWeight w H) n := by
      have hh := difference_eq_tail w hn0 hnH
      linarith
    have hab : |deviation w n-μ| < ε := by
      rw [he]
      have hh := abs_add_le (score w H n-μ) (deviation (tailWeight w H) n)
      dsimp only [r] at hr hhead ht
      linarith
    exact mem_filter.mpr ⟨hnN,hn0,hab⟩
  have hG : (G.card:ℝ) ≤ V.card := by exact_mod_cast card_le_card hGV
  have hV : A ∩ Set.Iio N=(V : Set ℕ) := by
    ext n
    simp only [V,Set.mem_inter_iff,Set.mem_Iio,mem_coe,mem_filter,mem_range]
    tauto
  rw [hV,Set.ncard_coe_finset]
  linarith

#print axioms exists_band
end Erdos1206.FullMovingBandDensity
