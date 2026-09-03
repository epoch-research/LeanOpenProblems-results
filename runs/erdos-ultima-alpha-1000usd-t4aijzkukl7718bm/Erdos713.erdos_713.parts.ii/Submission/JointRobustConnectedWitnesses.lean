import FormalConjecturesUtil
import Submission.JointRobustSplitWitnesses
import Submission.ExpanderVertexConnectivity

/-! Robust split packings and growing vertex connectivity on the SAME
near-order exact hosts. Connectivity does not control split-copy interiors. -/
open SimpleGraph Finset Filter Asymptotics
namespace Erdos713JointRobustConnectedWitnesses
open Erdos713Cloning Erdos713SwitchGluing Erdos713RelativeExpansion
open Erdos713RobustRootPairs Erdos713SplitEdgePacking
open Erdos713JointRobustSplitWitnesses Erdos713ExpanderVertexConnectivity
set_option maxHeartbeats 2000000

/-- Here the sharp degree and edge-deletion coefficients are specialized
to c (which is strictly below c*alpha). The connectivity coefficient is
fixed BEFORE all size, degree, accuracy, and window parameters. -/
theorem nearby_robust_connected {W : Type*} [Fintype W] (H : SimpleGraph W)
    (hH : H.IsBipartite) (hEdge : ∃ x y, H.Adj x y) {α c : ℝ}
    (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n => c*(n : ℝ)^α)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ δ ε : ℝ, 0 < δ → 0 < ε → ∀ N D : ℕ,
      ∀ᶠ k : ℕ in atTop, ∃ (U : Type) (_ : Fintype U) (J : SimpleGraph U),
        N ≤ Fintype.card U ∧
        (1-δ)*(k : ℝ) < Fintype.card U ∧ (Fintype.card U : ℝ) < (1+δ)*k ∧
        H.Free J ∧ Nat.card J.edgeSet = extremalNumber (Fintype.card U) H ∧
        (∀ v, D ≤ Nat.card (J.neighborSet v)) ∧
        (∀ v, c*(Fintype.card U : ℝ)^(α-1) ≤ (Nat.card (J.neighborSet v) : ℝ)) ∧
        (∀ v, SingleFold H J v) ∧
        c*(Fintype.card U : ℝ)^(α-1) < (extremalNumber (Fintype.card U) H : ℝ)-
          (extremalNumber (Fintype.card U-1) H : ℝ) ∧
        (∀ A : Finset U, 2*A.card ≤ Fintype.card U →
          κ*A.card*(Fintype.card U : ℝ)^(α-1) ≤
            (Nat.card (cross J (A : Set U)).edgeSet : ℝ)) ∧
        (∀ S : Finset U, (S.card : ℝ) < κ*(Fintype.card U : ℝ)^(α-1) →
          (J.induce (S : Set U)ᶜ).Preconnected) ∧
        ∃ B : Finset (U × U), (B.card : ℝ) ≤ ε*(Fintype.card U : ℝ)^2 ∧
          (∀ u v, (u,v) ∉ B →
            RobustRoots H J u v (c*(Fintype.card U : ℝ)^(α-1)) ∧
            EdgePacking H J u v
              ⌊c*(Fintype.card U : ℝ)^(α-1)/((Fintype.card W+1).choose 2 : ℝ)⌋₊) ∧
          ∀ (j : ℕ) (p : Fin j → U × U),
            (j*(Fintype.card W+1).choose 2 : ℕ) ≤ c*(Fintype.card U : ℝ)^(α-1) →
            (∀ i, p i ∉ B) → SimultaneousPacking H J p := by
  obtain ⟨κ,hκ,hExp⟩ := eventually_expanding_exact H ha hc h
  have hUpper : ∀ᶠ n : ℕ in atTop, (extremalNumber n H : ℝ) ≤ 2*c*(n : ℝ)^α := by
    filter_upwards [(Erdos713FutureRecords.ratio_limit h).eventually_lt_const
      (show c < 2*c by linarith),eventually_gt_atTop (0 : ℕ)] with n hn hnp
    exact ((div_lt_iff₀ (Real.rpow_pos_of_pos (by exact_mod_cast hnp) α)).mp hn).le
  obtain ⟨M,hM⟩ := eventually_atTop.mp ((hExp.and hUpper).and (eventually_gt_atTop (0 : ℕ)))
  refine ⟨κ,hκ,?_⟩
  intro δ ε hd hε N D
  have hca : c < c*α := by nlinarith
  filter_upwards [nearby_joint_robust_witnesses H hH hEdge ha ha2 hc hc hca hd hε h
    (max N M) D] with k hk
  obtain ⟨U,hU,J,hnNM,hnlo,hnhi,hf,he,hD,hMin,hFold,hBack,B,hB,hPairs,hDemands⟩ := hk
  obtain ⟨⟨hEX,hUp⟩,hn⟩ := hM (Fintype.card U) ((le_max_right N M).trans hnNM)
  have hnR : (0 : ℝ) < Fintype.card U := by exact_mod_cast hn
  have hPow : (Fintype.card U : ℝ)^α = (Fintype.card U : ℝ)^(α-1)*Fintype.card U := by
    calc
      _ = (Fintype.card U : ℝ)^((α-1)+1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hnR,Real.rpow_one]
  have hrelative (v : U) : Nat.card J.edgeSet ≤
      24*Fintype.card U*Nat.card (J.neighborSet v) := by
    have hE : (Nat.card J.edgeSet : ℝ) ≤ 2*c*(Fintype.card U : ℝ)^α := by rw [he]; exact hUp
    rw [hPow] at hE
    have hmul := mul_le_mul_of_nonneg_left (hMin v) (show (0 : ℝ) ≤ 2*Fintype.card U by positivity)
    have hpos : (0 : ℝ) ≤ (Fintype.card U : ℝ)*(Nat.card (J.neighborSet v) : ℝ) := by positivity
    exact_mod_cast (show (Nat.card J.edgeSet : ℝ) ≤
      24*(Fintype.card U : ℝ)*(Nat.card (J.neighborSet v) : ℝ) by nlinarith only [hE,hmul,hpos])
  have hCut := hEX U J rfl hf he hrelative
  refine ⟨U,hU,J,(le_max_left N M).trans hnNM,hnlo,hnhi,hf,he,hD,hMin,hFold,hBack,hCut,?_,
    B,hB,hPairs,hDemands⟩
  intro S hS
  apply preconnected_after_deleting J (L := κ*(Fintype.card U : ℝ)^(α-1)) _ S hS
  intro A hA
  simpa only [mul_assoc,mul_comm,mul_left_comm] using hCut A hA

#print axioms nearby_robust_connected
end Erdos713JointRobustConnectedWitnesses
