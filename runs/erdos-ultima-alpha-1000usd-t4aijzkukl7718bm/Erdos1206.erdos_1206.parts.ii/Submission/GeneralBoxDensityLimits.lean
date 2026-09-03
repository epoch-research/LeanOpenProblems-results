import Submission.BoxDensityLimits
import Submission.CoprimeBoxCRT

/-! Positive-axis CRT density limits for arbitrary pairwise coprime moduli. -/
namespace Erdos1206.GeneralBoxDensityLimits
open Finset Filter BoxDensityLimits CoprimeBoxCRT
open scoped Classical
set_option maxHeartbeats 1000000

theorem joint_positive_density (m : ℕ → ℕ) (S : Finset ℕ)
    (hpos : ∀ d∈S, 0 < m d)
    (hcop : (↑S : Set ℕ).Pairwise (fun p q => (m p).Coprime (m q)))
    (G : (d : ℕ) → Finset (ZMod (m d) × ZMod (m d))) :
    Tendsto (fun N : ℕ => ((positiveBox N (fun x =>
      ∀ d∈S, ((x.1:ZMod (m d)),(x.2:ZMod (m d)))∈G d)).card:ℝ)/(N:ℝ)^2)
      atTop (nhds (∏d∈S,localDensity m G d)) := by
  let D : ℝ := ∏d∈S,(m d:ℝ)
  apply normalized_limit _ _ (2*D+1) (D^2)
  intro N
  have hh := trimmed_discrepancy N (fun x =>
      ∀ d∈S, ((x.1:ZMod (m d)),(x.2:ZMod (m d)))∈G d)
    (∏d∈S,localDensity m G d) (2*(N:ℝ)*D+D^2) (by
      have heq : box N (fun x => ∀ d∈S, ((x.1:ZMod (m d)),(x.2:ZMod (m d)))∈G d) =
          (range N ×ˢ range N).filter
            (fun x => ∀ d∈S, ((x.1:ZMod (m d)),(x.2:ZMod (m d)))∈G d) := by
        ext x
        simp only [BoxDensityLimits.box,mem_filter]
      rw [heq,mul_comm (∏d∈S,localDensity m G d)]
      exact joint_box_discrepancy m S hpos hcop G N)
  convert hh using 1; ring

#print axioms joint_positive_density
end Erdos1206.GeneralBoxDensityLimits
