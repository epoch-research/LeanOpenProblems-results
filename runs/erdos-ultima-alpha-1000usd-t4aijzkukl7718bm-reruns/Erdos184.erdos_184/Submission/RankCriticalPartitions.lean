import Submission.RankCriticalCuts

/-!
For a connected rank-critical graph, every partition into k>=2 nonempty
parts has more than 2C(k-1) crossing edges. No spanning-tree packing theorem
or linear decomposition theorem is assumed here.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184
namespace RankCriticalPartitions
open RankCritical RankCriticalCuts
variable {V I : Type*}

def monochromatic (G : SimpleGraph V) (f : V → I) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ f u = f v
  symm := by intro u v h; exact ⟨h.1.symm,h.2.symm⟩
  loopless := by intro u h; exact h.1.ne rfl

lemma monochromatic_le (G : SimpleGraph V) (f : V → I) : monochromatic G f ≤ G :=
  fun _ _ h => h.1

lemma color_eq_of_reachable (G : SimpleGraph V) (f : V → I) {u v : V}
    (h : (monochromatic G f).Reachable u v) : f u = f v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons h p ih => exact h.2.trans ih

lemma monochromatic_closed (G : SimpleGraph V) (f : V → I) :
    IsComponentClosed G (monochromatic G f) := by
  intro u v huv hr
  exact ⟨huv,color_eq_of_reachable G f hr⟩

lemma component_card_ge_colors [Fintype V] [Fintype I] (G : SimpleGraph V)
    (f : V → I) (hf : Function.Surjective f) :
    Fintype.card I ≤ Nat.card (monochromatic G f).ConnectedComponent := by
  let q : (monochromatic G f).ConnectedComponent → I :=
    Quot.lift f (fun u v h => color_eq_of_reachable G f h)
  have hq : Function.Surjective q := by
    intro i
    obtain ⟨v,rfl⟩ := hf i
    exact ⟨(monochromatic G f).connectedComponentMk v,rfl⟩
  simpa only [Nat.card_eq_fintype_card] using Nat.card_le_card_of_surjective q hq

lemma connected_rank [Fintype V] {G : SimpleGraph V} (hc : G.Connected) :
    graphRank G + 1 = Fintype.card V := by
  letI := hc.nonempty
  letI := hc.preconnected.subsingleton_connectedComponent
  have hh : Nat.card G.ConnectedComponent = 1 := Nat.card_unique
  have hn := Fintype.card_pos_iff.mpr hc.nonempty
  unfold graphRank
  omega

lemma partition_crossing_lower [Fintype V] [Fintype I] {C : ℕ} {G : SimpleGraph V}
    (hG : IsCritical C G) (hc : G.Connected)
    (f : V → I) (hf : Function.Surjective f) (hk : 2 ≤ Fintype.card I) :
    2 * C * (Fintype.card I - 1) <
      (G.edgeSet \ (monochromatic G f).edgeSet).ncard := by
  let R := monochromatic G f
  have hpart := component_card_ge_colors G f hf
  have hcomp := component_card_le R
  have hnr : graphRank R + Fintype.card I ≤ Fintype.card V := by
    unfold graphRank
    change Fintype.card I ≤ Nat.card R.ConnectedComponent at hpart
    omega
  have hng := connected_rank hc
  have hne : R ≠ G := by
    intro h
    rw [h] at hnr
    omega
  have hbudget := closed_partition_budget hG R (monochromatic_le G f) hne
    (monochromatic_closed G f)
  have hle : graphRank R + (Fintype.card I - 1) ≤ graphRank G := by omega
  have hm := Nat.mul_le_mul_left (2*C) hle
  rw [Nat.mul_add] at hm
  change 2 * C * (Fintype.card I - 1) < (G.edgeSet \ R.edgeSet).ncard
  omega

end RankCriticalPartitions
end Erdos184
