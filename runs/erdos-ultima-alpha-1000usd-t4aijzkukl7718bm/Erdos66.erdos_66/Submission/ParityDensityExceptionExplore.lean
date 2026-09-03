import Submission.DensityDiagonalExplore

/-! One common density-zero exceptional set for the two parity self-counts
of a hypothetical witness. This is not pointwise coefficient reduction. -/
namespace Erdos66ParityDensityException
open Erdos66DensityDiagonal Erdos66ParityDensity Erdos66ParityRepresentation Erdos66Counting
open scoped Classical Topology
open Filter AdditiveCombinatorics
set_option maxHeartbeats 1800000

/-- Both self-count ratios converge to c/2 outside one set of density zero.
The carry is retained, and no power saving or repair-cost bound is claimed. -/
theorem witness_parity_limits_off_density_zero {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    ∃ E : Set ℕ, Tendsto (fun N : ℕ ↦ (count E N : ℝ)/N) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ if n∈E then c/2 else
        (sumRep (evenSet A) (n+1) : ℝ)/Real.log ((n : ℝ)+2)) atTop (𝓝 (c/2)) ∧
      Tendsto (fun n ↦ if n∈E then c/2 else
        (sumRep (oddSet A) n : ℝ)/Real.log ((n : ℝ)+2)) atTop (𝓝 (c/2)) := by
  let f : ℕ → ℝ×ℝ := fun n ↦
    ((sumRep (evenSet A) (n+1) : ℝ)/Real.log ((n : ℝ)+2),
      (sumRep (oddSet A) n : ℝ)/Real.log ((n : ℝ)+2))
  have hbad (ε : ℝ) (hε : 0<ε) : Tendsto
      (fun N : ℕ ↦ (count {n | ε ≤ dist (f n) (c/2,c/2)} N : ℝ)/N) atTop (𝓝 0) := by
    have he : {n | ε ≤ dist (f n) (c/2,c/2)}=
        ratioBad (fun n ↦ (sumRep (evenSet A) (n+1) : ℝ)) (c/2) ε ∪
        ratioBad (fun n ↦ (sumRep (oddSet A) n : ℝ)) (c/2) ε := by
      ext n
      simp only [f,Prod.dist_eq,Real.dist_eq,Set.mem_setOf_eq,le_max_iff,
        Set.mem_union,ratioBad]
    rw [he]
    exact witness_parity_self_counts_in_density h hε
  obtain ⟨E,hE,hlim⟩ := exists_density_zero_exception f (c/2,c/2) hbad
  refine ⟨E,hE,?_,?_⟩
  · have hh := (continuous_fst.tendsto (c/2,c/2)).comp hlim
    apply hh.congr'
    filter_upwards [] with n
    dsimp [Function.comp_def,f]
    split_ifs <;> rfl
  · have hh := (continuous_snd.tendsto (c/2,c/2)).comp hlim
    apply hh.congr'
    filter_upwards [] with n
    dsimp [Function.comp_def,f]
    split_ifs <;> rfl

end Erdos66ParityDensityException
