import Submission.WholeBlockPacketParametersExplore
import Submission.NaturalLabeledPacketsExplore

/-! Two designated packet types per repair group, simultaneously for every
exceptional target in the useful coarse interval. -/
namespace Erdos66ExceptionalLabeledPackets
open Filter AdditiveCombinatorics Erdos66TripleDeletionParameters
  Erdos66WholeBlockPacketParameters Erdos66NaturalLabeledPackets Erdos66MultiPacket
open scoped Topology Classical
set_option maxHeartbeats 2200000

abbrev Group (T : Finset ℕ) (k : ℕ) := T × Fin k
abbrev Coord (T : Finset ℕ) (k : ℕ) := Group T k × Bool
abbrev Label (T : Finset ℕ) (k : ℕ) := Coord T k × Bool

noncomputable def multiplicity (m : ℝ) : ℕ := ⌊m^3/4⌋₊

lemma exceptional_card_bound (m ε : ℝ) (hm : 1 ≤ m) (hε : 0<ε) (T : Finset ℕ)
    (hT : (T.card : ℝ) ≤ 128*(1+Real.log (((length m+1 : ℕ) : ℝ)))^2/ε^2) :
    (T.card : ℝ) ≤ (25088/ε^2)*m^2 := by
  have ⟨hlog0,hlog⟩ := log_length_bound m (by linarith)
  have hbase : 1+Real.log (((length m+1 : ℕ) : ℝ)) ≤ 14*m := by linarith
  have hs : (1+Real.log (((length m+1 : ℕ) : ℝ)))^2 ≤ 196*m^2 := by nlinarith
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 128))
    (sq_nonneg ε)
  apply hT.trans
  convert hh using 1 <;> ring

lemma coord_card_bound (m ε : ℝ) (hm : 1 ≤ m) (hε : 0<ε) (T : Finset ℕ)
    (hT : (T.card : ℝ) ≤ 128*(1+Real.log (((length m+1 : ℕ) : ℝ)))^2/ε^2) :
    (Fintype.card (Coord T (multiplicity m)) : ℝ) ≤ (25088/ε^2+1)*m^5 := by
  have hc : (Fintype.card (Coord T (multiplicity m)) : ℝ)=2*(T.card : ℝ)*(multiplicity m : ℝ) := by
    simp [Coord,Group,Fintype.card_prod,mul_comm,mul_left_comm,mul_assoc]
  rw [hc]
  have hk : (multiplicity m : ℝ) ≤ m^3/4 := Nat.floor_le (by positivity)
  have hT' := exceptional_card_bound m ε hm hε T hT
  have h₁ : 2*(T.card : ℝ)*(multiplicity m : ℝ) ≤ (T.card : ℝ)*m^3 := by
    have hh := mul_le_mul_of_nonneg_left hk (show 0 ≤ (T.card : ℝ) by positivity)
    have hn : 0 ≤ (T.card : ℝ)*(multiplicity m : ℝ) := by positivity
    nlinarith
  have h₂ := mul_le_mul_of_nonneg_right hT' (show 0 ≤ m^3 by positivity)
  have hn : 0 ≤ m^5 := by positivity
  nlinarith only [h₁,h₂,hn]

/-- For every sufficiently large m, the same construction works for any
eligible old set and exceptional target set. New/new unintended sums are
Sidon globally and the new/old coarse mixed count is less than 28 globally. -/
theorem eventually_exception_packets (ε : ℝ) (hε : 0<ε) (hε1 : ε ≤ 1) :
    ∀ᶠ m : ℝ in atTop, ∀ D T : Finset ℕ,
      D ⊆ Finset.range (length m+1) →
      (∀ q, (sumRep (D : Set ℕ) q : ℝ) ≤ (1+ε)*m^3) →
      T ⊆ Finset.Icc (start m ε) (length m) →
      (T.card : ℝ) ≤ 128*(1+Real.log (((length m+1 : ℕ) : ℝ)))^2/ε^2 →
      ∃ d : Label T (multiplicity m) → ℕ, Function.Injective d ∧
        (∀ u, d u ≤ length m ∧ d u∉D) ∧
        (∀ g : Group T (multiplicity m), ∀ s : Bool, d ((g,s),false)+d ((g,s),true)=g.1.val) ∧
        (∀ u v w s : Label T (multiplicity m), ¬Designated u v → ¬Designated w s →
          d u+d v=d w+d s → (u=w ∧ v=s) ∨ (u=s ∧ v=w)) ∧
        (∀ q, (Erdos66NatPairAlgebra.pairs (Finset.univ.image d) D q : ℝ) < 28) := by
  let C : ℝ := 25088/ε^2+1
  have hC : 1 ≤ C := by
    have hh : 0 ≤ 25088/ε^2 := by positivity
    dsimp [C]
    linarith
  filter_upwards [eventually_ge_atTop (1 : ℝ),eventually_packet_budget C hC] with m hm hbudget
  intro D T hD hu hT hcard
  let n : Coord T (multiplicity m) → ℕ := fun i ↦ i.1.1.val
  have hn (i : Coord T (multiplicity m)) : 12*shift m+48 ≤ n i ∧ n i ≤ length m := by
    have hh := Finset.mem_Icc.mp (hT i.1.1.property)
    exact ⟨(start_width m ε hε hε1).trans hh.1,hh.2⟩
  have hu' (q : ℕ) : (sumRep (D : Set ℕ) q : ℝ) ≤ 2*m^3 := by
    have hh := mul_le_mul_of_nonneg_right (show 1+ε ≤ 2 by linarith) (show 0 ≤ m^3 by positivity)
    exact (hu q).trans hh
  have hsmall := hbudget (Fintype.card (Coord T (multiplicity m))) (2*(length m : ℝ)+1)
    (by positivity) (coord_card_bound m ε hm hε T hcard) (by positivity)
    (cutoff_prefactor m (by linarith))
  obtain ⟨d,hdi,hda,hcenter,hunique,hmixed⟩ := exists_natural_labeled_packets D (length m) (shift m)
    (shift_positive m) hD (2*m^3) hu' n hn 14 m (by norm_num) (by linarith) hsmall
  refine ⟨d,hdi,hda,(fun g s ↦ hcenter (g,s)),hunique,?_⟩
  intro q
  simpa only [show (2 : ℝ)*14=28 by norm_num] using hmixed q

end Erdos66ExceptionalLabeledPackets
