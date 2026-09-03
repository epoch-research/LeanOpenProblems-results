import FormalConjecturesUtil
import Submission.NearOrderCloneMerge
import Submission.RobustRootPairs
import Submission.SplitSimultaneousPacking

/-! Exact near-order hosts with robust nontrivial split witnesses and
polynomial-size edge packings at almost all root pairs, on the SAME host.
This does not settle rationality. -/
open SimpleGraph Finset Filter Asymptotics
namespace Erdos713JointRobustSplitWitnesses
open Erdos713Cloning Erdos713NearOrderCloneMerge
open Erdos713RobustRootPairs Erdos713SplitEdgePacking
set_option maxHeartbeats 2000000

/-- The exceptional set is chosen for the host, BEFORE root pairs, demands, or
deleted edge sets. Any demand list within the total edge budget has a
simultaneous edge-disjoint realization. Internal vertices may overlap. -/
theorem nearby_joint_robust_witnesses {W : Type*} [Fintype W] (H : SimpleGraph W)
    (hH : H.IsBipartite) (hEdge : ∃ x y, H.Adj x y) {α c a δ ε : ℝ}
    (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c) (ha0 : 0 < a) (hac : a < c*α)
    (hd : 0 < δ) (hε : 0 < ε)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n => c*(n : ℝ)^α)) (N D : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∃ (U : Type) (_ : Fintype U) (J : SimpleGraph U),
      N ≤ Fintype.card U ∧
      (1-δ)*(k : ℝ) < Fintype.card U ∧ (Fintype.card U : ℝ) < (1+δ)*k ∧
      H.Free J ∧ Nat.card J.edgeSet = extremalNumber (Fintype.card U) H ∧
      (∀ v, D ≤ Nat.card (J.neighborSet v)) ∧
      (∀ v, a*(Fintype.card U : ℝ)^(α-1) ≤ (Nat.card (J.neighborSet v) : ℝ)) ∧
      (∀ v, SingleFold H J v) ∧
      a*(Fintype.card U : ℝ)^(α-1) < (extremalNumber (Fintype.card U) H : ℝ)-
        (extremalNumber (Fintype.card U-1) H : ℝ) ∧
      ∃ B : Finset (U × U), (B.card : ℝ) ≤ ε*(Fintype.card U : ℝ)^2 ∧
        (∀ u v, (u,v) ∉ B →
          RobustRoots H J u v (a*(Fintype.card U : ℝ)^(α-1)) ∧
          EdgePacking H J u v
            ⌊a*(Fintype.card U : ℝ)^(α-1)/((Fintype.card W+1).choose 2 : ℝ)⌋₊) ∧
        ∀ (j : ℕ) (p : Fin j → U × U),
          (j*(Fintype.card W+1).choose 2 : ℕ) ≤ a*(Fintype.card U : ℝ)^(α-1) →
          (∀ i, p i ∉ B) → SimultaneousPacking H J p := by
  let b : ℝ := (a+c*α)/2
  have hab : a < b := by dsimp [b]; linarith
  have hbc : b < c*α := by dsimp [b]; linarith
  have ht : 0 < b-a := sub_pos.mpr hab
  obtain ⟨M,hM⟩ := eventually_atTop.mp (eventually_few_badRoots H ha ha2 hc ht h hε)
  filter_upwards [nearby_joint_saturated H hH hEdge ha ha2 hc hbc h (max N M) D hd] with k hk
  obtain ⟨U,hU,J,hnNM,hnlo,hnhi,hf,he,hD,hMin,hFold,hBack⟩ := hk
  have hp : 0 ≤ (Fintype.card U : ℝ)^(α-1) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hab' : a*(Fintype.card U : ℝ)^(α-1) ≤ b*(Fintype.card U : ℝ)^(α-1) :=
    mul_le_mul_of_nonneg_right hab.le hp
  have hGap : a*(Fintype.card U : ℝ)^(α-1)+(b-a)*(Fintype.card U : ℝ)^(α-1) <
      (extremalNumber (Fintype.card U) H : ℝ)-
        (extremalNumber (Fintype.card U-1) H : ℝ) := by nlinarith only [hBack]
  refine ⟨U,hU,J,(le_max_left N M).trans hnNM,hnlo,hnhi,hf,he,hD,
    fun v => hab'.trans (hMin v),hFold,hab'.trans_lt hBack,
    badRoots J ((b-a)*(Fintype.card U : ℝ)^(α-1)),?_,?_,?_⟩
  · exact hM (Fintype.card U) ((le_max_right N M).trans hnNM) U J rfl hf
  · intro u v hgood
    exact ⟨robust_outside H J hf he hGap hgood,
      packing_outside H J hf he hEdge (mul_nonneg ha0.le hp) hGap hgood⟩

  · intro j p hj hgood
    apply simultaneous_of_backward_gap H J hf he j p
    · intro i
      have hh := outside_badRoots J _ (hgood i)
      exact ⟨hh.1,hh.2.1⟩
    · intro i
      have hh := outside_badRoots J _ (hgood i)
      exact (add_le_add hj hh.2.2).trans_lt hGap

#print axioms nearby_joint_robust_witnesses
end Erdos713JointRobustSplitWitnesses
