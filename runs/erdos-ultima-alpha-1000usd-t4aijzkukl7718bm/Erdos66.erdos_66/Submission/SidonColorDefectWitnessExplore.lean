import Submission.SidonColorDefectExplore
import Submission.SidonColorWitnessExplore

/-! Every sufficiently small coloring of a hypothetical logarithmic witness
must contain a quantitatively large repeated-difference defect. -/
namespace Erdos66SidonColorDefectWitness
open Erdos66SidonColorDefect Erdos66SidonColorWitness Erdos66Counting
  Erdos66TauberianProfile Erdos66Explore AdditiveCombinatorics Filter
open scoped Topology Classical
set_option maxHeartbeats 1800000

theorem witness_requires_color_defects {A : Set ℕ} {c : ℝ} (hc : c≠0)
    (h : Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 c)) :
    ∃ δ η : ℝ, 0<δ ∧ 0<η ∧ ∃ K : ℕ, ∀ J, K≤J → ∀ m : ℕ,
      ∀ col : ℕ → Fin m, (m:ℝ)≤δ*J →
        η*(4:ℝ)^J*(J:ℝ)^2≤ m*differenceDefect (cutoff A (4^(2*J))) col (4^J) := by
  let L := 2*Real.sqrt (c/Real.pi)
  let D := L*Real.sqrt (Real.log 4)
  have hcpos := limit_pos hc h
  have hL : 0<L := by dsimp [L]; positivity
  have hD : 0<D := mul_pos hL (Real.sqrt_pos.mpr (Real.log_pos (by norm_num)))
  have hgeo : Tendsto (fun k : ℕ ↦ (count A (4^k):ℝ)/((2:ℝ)^k*Real.sqrt k))
      atTop (𝓝 D) := geometric_count_limit (witness_counting_profile hc h)
  obtain ⟨K,hK1,hbounds⟩ := geometric_count_bounds hD hgeo
  let a := D/4
  let b := 5*D/2
  let δ := min 1 (a^2/(6*b+12))
  let η := a^2/12
  have ha : 0<a := by dsimp [a]; positivity
  have hb : 0≤b := by dsimp [b]; positivity
  have hδ : 0<δ := lt_min (by norm_num) (div_pos (sq_pos_of_pos ha) (by positivity))
  have hη : 0<η := by dsimp [η]; positivity
  refine ⟨δ,η,hδ,hη,K,?_⟩
  intro J hJ m col hm
  have hJ1 := hK1.trans hJ
  have he := small_color_defect_lower (cutoff A (4^(2*J))) col J a b hb
    (annulus_profile_of_bounds A D hD K hbounds J hJ)
    (cutoff_size_of_bounds A D hD K hbounds J hJ hJ1)
    (by simpa only [Fintype.card_fin] using hm)
  simp only [Fintype.card_fin] at he
  dsimp only [η]
  nlinarith

end Erdos66SidonColorDefectWitness
