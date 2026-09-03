import Submission.ControlledSquareLinearization
import Submission.HypergraphDegreeTrim

/-!
Actual large root subsets whose collision hypergraphs are linear and have
controlled maximum degree. The degree remains polynomial in N, so the result
is not a near-linear Sidon extraction theorem.
-/
namespace Erdos773.ControlledSquareDegrees
open Finset Filter SquareCollisionCodegrees SquareCollisionLinearization
open ControlledSquareLinearization HypergraphDegreeTrim
set_option maxHeartbeats 1000000

lemma linear_mono {A B : Finset ℕ} (hBA : B ⊆ A) (hA : LinearCollisions A) :
    LinearCollisions B := by
  intro e he f hf hne
  exact hA e (edges_mono hBA he) f (edges_mono hBA hf) hne

/-- The selected family has size N^(4/5-epsilon), and every retained root
belongs to at most N^(2/5+epsilon) collision supports. No edge-free conclusion
is drawn from this polynomial degree bound. -/
theorem controlled_maximum_degree (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∃ B ⊆ Icc 1 N,
      ThreeAPFree ((B.image (fun n : ℕ => n^2)) : Set ℕ) ∧
      LinearCollisions B ∧ (N : ℝ)^(4/5-ε) ≤ B.card ∧
      ∀ a ∈ B, (degree (edges B) a : ℝ) ≤ (N : ℝ)^(2/5+ε) := by
  classical
  have ht : Tendsto (fun N : ℕ => (N : ℝ)^(3*ε/4)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < 3*ε/4)).comp tendsto_natCast_atTop_atTop
  filter_upwards [average_edge_control (ε/4) (by positivity),
    ht.eventually_ge_atTop 8,eventually_ge_atTop 1] with N hN hlarge hN1
  obtain ⟨A,hA,hAP,hlin,hcard,hE⟩ := hN
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN1
  obtain ⟨B,hBA,hBC,hdegree⟩ := trim A (edges A)
    (fun e he => mem_powerset.mp (mem_filter.mp he).1)
    (fun e he => (mem_filter.mp he).2.1)
    ((N : ℝ)^(2/5+ε/4)) (Real.rpow_pos_of_pos hNpos _) hE
  refine ⟨B,hBA.trans hA,?_,linear_mono hBA hlin,?_,?_⟩
  · exact hAP.mono (by exact_mod_cast image_subset_image hBA)
  · have hc : (A.card : ℝ) ≤ 2*B.card := by exact_mod_cast hBC
    have heq : (N : ℝ)^(4/5-ε/4) = (N : ℝ)^(4/5-ε)*(N : ℝ)^(3*ε/4) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring
    rw [heq] at hcard
    have hm := mul_le_mul_of_nonneg_left hlarge (Real.rpow_nonneg hNpos.le (4/5-ε))
    nlinarith only [hc,hcard,hm,Real.rpow_nonneg hNpos.le (4/5-ε)]
  · intro a ha
    have hmono : (degree (edges B) a : ℝ) ≤ degree (edges A) a := by
      exact_mod_cast degree_mono (edges_mono hBA) a
    calc
      _ ≤ 8*(N : ℝ)^(2/5+ε/4) := hmono.trans (hdegree a ha)
      _ ≤ (N : ℝ)^(3*ε/4)*(N : ℝ)^(2/5+ε/4) :=
        mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hNpos.le _)
      _ = _ := by rw [← Real.rpow_add hNpos]; congr 1; ring

#print axioms controlled_maximum_degree
end Erdos773.ControlledSquareDegrees
