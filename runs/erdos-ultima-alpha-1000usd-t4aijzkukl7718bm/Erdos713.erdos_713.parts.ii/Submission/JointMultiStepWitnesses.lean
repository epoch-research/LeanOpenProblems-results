import FormalConjecturesUtil
import Submission.SaturationMultiStep
import Submission.JointRobustConnectedWitnesses
import Submission.VertexRobustSplit

/-! The bounded multi-step, vertex-cost, robust edge-packing, and
connectivity conclusions hold on ONE exact near-order host. This still
supplies no rationality implication or vertex-disjoint split packing. -/
open SimpleGraph Finset Filter Asymptotics
namespace Erdos713JointMultiStepWitnesses
open Erdos713Cloning Erdos713SwitchGluing Erdos713RelativeExpansion
open Erdos713RobustRootPairs Erdos713SplitEdgePacking
open Erdos713ExpanderVertexConnectivity Erdos713SaturationMultiStep
open Erdos713VertexRobustSplit
set_option maxHeartbeats 2000000

/-- R is fixed BEFORE the eventual order threshold. No uniform assertion
for R growing with n, and no support at the enlarged order, is made. -/
theorem nearby_multi_witnesses {W : Type*} [Fintype W] (H : SimpleGraph W)
    (hH : H.IsBipartite) (hEdge : ∃ x y, H.Adj x y) {α c : ℝ}
    (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n => c*(n : ℝ)^α)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ a δ ε : ℝ, 0 < a → a < c*α → 0 < δ → 0 < ε →
      ∀ R N D : ℕ, ∀ᶠ k : ℕ in atTop, ∃ (U : Type) (_ : Fintype U) (J : SimpleGraph U),
        N ≤ Fintype.card U ∧
        (1-δ)*(k : ℝ) < Fintype.card U ∧ (Fintype.card U : ℝ) < (1+δ)*k ∧
        H.Free J ∧ Nat.card J.edgeSet = extremalNumber (Fintype.card U) H ∧
        (∀ v, D ≤ Nat.card (J.neighborSet v)) ∧
        (∀ v, a*(Fintype.card U : ℝ)^(α-1) ≤ (Nat.card (J.neighborSet v) : ℝ)) ∧
        (∀ v, SingleFold H J v) ∧
        (∀ r : ℕ, 1 ≤ r → r ≤ R+1 →
          a*(r : ℝ)*(Fintype.card U : ℝ)^(α-1) <
            (extremalNumber (Fintype.card U) H : ℝ)-
              (extremalNumber (Fintype.card U-r) H : ℝ)) ∧
        (∀ A : Finset U, 2*A.card ≤ Fintype.card U →
          κ*A.card*(Fintype.card U : ℝ)^(α-1) ≤
            (Nat.card (cross J (A : Set U)).edgeSet : ℝ)) ∧
        (∀ S : Finset U, (S.card : ℝ) < κ*(Fintype.card U : ℝ)^(α-1) →
          (J.induce (S : Set U)ᶜ).Preconnected) ∧
        (∀ S : Finset U, S.card ≤ R → ∀ u v, u ∉ S → v ∉ S → u ≠ v → ¬ J.Adj u v →
          ¬ Avoids H J u v S →
          a*((S.card : ℝ)+1)*(Fintype.card U : ℝ)^(α-1) <
            ((∑ z ∈ S, Nat.card (J.neighborSet z)) : ℝ)+(Nat.card (J.commonNeighbors u v) : ℝ)) ∧
        ∃ B : Finset (U × U), (B.card : ℝ) ≤ ε*(Fintype.card U : ℝ)^2 ∧
          (∀ u v, (u,v) ∉ B →
            RobustRoots H J u v (a*(Fintype.card U : ℝ)^(α-1)) ∧
            EdgePacking H J u v
              ⌊a*(Fintype.card U : ℝ)^(α-1)/((Fintype.card W+1).choose 2 : ℝ)⌋₊) ∧
          ∀ (j : ℕ) (p : Fin j → U × U),
            (j*(Fintype.card W+1).choose 2 : ℕ) ≤ a*(Fintype.card U : ℝ)^(α-1) →
            (∀ i, p i ∉ B) → SimultaneousPacking H J p := by
  obtain ⟨κ,hκ,hExp⟩ := eventually_expanding_exact H ha hc h
  have hUpper : ∀ᶠ n : ℕ in atTop, (extremalNumber n H : ℝ) ≤ 2*c*(n : ℝ)^α := by
    filter_upwards [(Erdos713FutureRecords.ratio_limit h).eventually_lt_const
      (show c < 2*c by linarith),eventually_gt_atTop (0 : ℕ)] with n hn hnp
    exact ((div_lt_iff₀ (Real.rpow_pos_of_pos (by exact_mod_cast hnp) α)).mp hn).le
  refine ⟨κ,hκ,?_⟩
  intro a δ ε ha0 hac hd hε R N D
  let b : ℝ := (max a c+c*α)/2
  have hmax : max a c < c*α := max_lt hac (by nlinarith)
  have hab : a < b := by have := le_max_left a c; dsimp [b]; linarith
  have hcb : c < b := by have := le_max_right a c; dsimp [b]; linarith
  have hbc : b < c*α := by dsimp [b]; linarith
  have ht : 0 < b-a := sub_pos.mpr hab
  obtain ⟨M,hM⟩ := eventually_atTop.mp
    (((hExp.and hUpper).and (eventually_gt_atTop (0 : ℕ))).and
      (eventually_few_badRoots H ha ha2 hc ht h hε))
  filter_upwards [nearby_multi_saturated H hH hEdge ha ha2 hc hbc h (R+1) (max N M) D hd] with k hk
  obtain ⟨U,hU,J,hnNM,hnlo,hnhi,hf,he,hD,hMin,hFold,hBack,hMulti⟩ := hk
  obtain ⟨⟨⟨hEX,hUp⟩,hn⟩,hBad⟩ := hM (Fintype.card U) ((le_max_right N M).trans hnNM)
  have hnR : (0 : ℝ) < Fintype.card U := by exact_mod_cast hn
  have hp : 0 ≤ (Fintype.card U : ℝ)^(α-1) := Real.rpow_nonneg hnR.le _
  have hab' := mul_le_mul_of_nonneg_right hab.le hp
  have hPow : (Fintype.card U : ℝ)^α = (Fintype.card U : ℝ)^(α-1)*Fintype.card U := by
    calc
      _ = (Fintype.card U : ℝ)^((α-1)+1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hnR,Real.rpow_one]
  have hrelative (v : U) : Nat.card J.edgeSet ≤
      24*Fintype.card U*Nat.card (J.neighborSet v) := by
    have hE : (Nat.card J.edgeSet : ℝ) ≤ 2*c*(Fintype.card U : ℝ)^α := by rw [he]; exact hUp
    rw [hPow] at hE
    have hMinC := (mul_le_mul_of_nonneg_right hcb.le hp).trans (hMin v)
    have hmul := mul_le_mul_of_nonneg_left hMinC (show (0 : ℝ) ≤ 2*Fintype.card U by positivity)
    have hpos : (0 : ℝ) ≤ (Fintype.card U : ℝ)*(Nat.card (J.neighborSet v) : ℝ) := by positivity
    exact_mod_cast (show (Nat.card J.edgeSet : ℝ) ≤
      24*(Fintype.card U : ℝ)*(Nat.card (J.neighborSet v) : ℝ) by nlinarith only [hE,hmul,hpos])
  have hCut := hEX U J rfl hf he hrelative
  have hMultiA (r : ℕ) (hr : 1 ≤ r) (hrR : r ≤ R+1) :
      a*(r : ℝ)*(Fintype.card U : ℝ)^(α-1) <
        (extremalNumber (Fintype.card U) H : ℝ)-(extremalNumber (Fintype.card U-r) H : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hab.le (Nat.cast_nonneg r)) hp
    exact hh.trans_lt (hMulti r hr hrR)
  have hGap : a*(Fintype.card U : ℝ)^(α-1)+(b-a)*(Fintype.card U : ℝ)^(α-1) <
      (extremalNumber (Fintype.card U) H : ℝ)-
        (extremalNumber (Fintype.card U-1) H : ℝ) := by nlinarith only [hBack]
  refine ⟨U,hU,J,(le_max_left N M).trans hnNM,hnlo,hnhi,hf,he,hD,
    fun v => hab'.trans (hMin v),hFold,hMultiA,hCut,?_,?_,
    badRoots J ((b-a)*(Fintype.card U : ℝ)^(α-1)),hBad U J rfl hf,?_,?_⟩
  · intro S hS
    apply preconnected_after_deleting J (L := κ*(Fintype.card U : ℝ)^(α-1)) _ S hS
    intro A hA
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hCut A hA
  · intro S hSR u v hu hv huv hnot hblock
    have ht := transversal_degree_bound H J hf he S hu hv huv hnot hblock
    have hh := hMultiA (S.card+1) (by omega) (by omega)
    simpa only [Nat.cast_add,Nat.cast_one,Nat.sub_sub] using hh.trans_le ht
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

#print axioms nearby_multi_witnesses
end Erdos713JointMultiStepWitnesses
