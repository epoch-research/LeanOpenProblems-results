import Submission.WeightedPacketAlgebraExplore
import Submission.ExceptionalLabeledPacketsExplore

/-! Two balanced types of designated pairs fill each selected coarse target
by exactly 4k, with a uniform bound 116 on all unintended weighted edges. -/
namespace Erdos66BalancedWeightedPacket
open Erdos66ExceptionalLabeledPackets Erdos66WeightedPacketAlgebra Erdos66MultiPacket
open scoped Classical
set_option maxHeartbeats 2200000

lemma balanced_designated_sum (T : Finset ℕ) (k q : ℕ) (d : Label T k → ℕ)
    (w : ℕ → ℕ → ℝ) (hw : ∀ i j, w i j=w j i)
    (hbal : ∀ g : Group T k,
      w (d ((g,false),false)) (d ((g,false),true))+
        w (d ((g,true),false)) (d ((g,true),true))=2) :
    (∑ i : Coord T k, if i.1.1.val=q then
      w (d (i,false)) (d (i,true))+w (d (i,true)) (d (i,false)) else 0) =
      if q∈T then 4*(k : ℝ) else 0 := by
  have hg (g : Group T k) :
      (∑ s : Bool, if g.1.val=q then
        w (d ((g,s),false)) (d ((g,s),true))+w (d ((g,s),true)) (d ((g,s),false)) else 0) =
      if g.1.val=q then (4 : ℝ) else 0 := by
    rw [Fintype.sum_bool]
    by_cases hq : g.1.val=q
    · simp only [hq,if_true]
      rw [hw (d ((g,false),true)) (d ((g,false),false)),hw (d ((g,true),true)) (d ((g,true),false))]
      linarith [hbal g]
    · simp [hq]
  calc
    _ = ∑ g : Group T k, ∑ s : Bool, if g.1.val=q then
        w (d ((g,s),false)) (d ((g,s),true))+w (d ((g,s),true)) (d ((g,s),false)) else 0 :=
      Fintype.sum_prod_type _
    _ = ∑ g : Group T k, if g.1.val=q then (4 : ℝ) else 0 := Finset.sum_congr rfl (fun g _ ↦ hg g)
    _ = ∑ g : T, if g.val=q then (4*(k : ℝ)) else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro g hg
      by_cases hq : g.val=q <;> simp [hq,mul_comm]
    _ = ∑ g∈T, if g=q then (4*(k : ℝ)) else 0 := Finset.sum_coe_sort T (fun g : ℕ ↦ if g=q then 4*(k : ℝ) else 0)
    _ = _ := by simp

/-- All designated repairs share one collateral bound, independent of the
number of exceptional targets and of the fine-field target. -/
theorem balanced_repair_collateral (D T : Finset ℕ) (k : ℕ) (d : Label T k → ℕ)
    (hd : Function.Injective d) (havoid : ∀ u, d u∉D)
    (hcenter : ∀ g : Group T k, ∀ s : Bool, d ((g,s),false)+d ((g,s),true)=g.1.val)
    (hunique : ∀ u v w s : Label T k, ¬Designated u v → ¬Designated w s →
      d u+d v=d w+d s → (u=w ∧ v=s) ∨ (u=s ∧ v=w))
    (hmixed : ∀ q, (Erdos66NatPairAlgebra.pairs (Finset.univ.image d) D q : ℝ) < 28)
    (w : ℕ → ℕ → ℝ) (hw : ∀ i j, w i j=w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hwnew : ∀ u v, w (d u) (d v) ≤ 2) (hwmix : ∀ u i, i∈D → w (d u) i ≤ 2)
    (hbal : ∀ g : Group T k,
      w (d ((g,false),false)) (d ((g,false),true))+
        w (d ((g,true),false)) (d ((g,true),true))=2) (q : ℕ) :
    0 ≤ fiberSum (D∪Finset.univ.image d) (D∪Finset.univ.image d) w q-fiberSum D D w q-
      (if q∈T then 4*(k : ℝ) else 0) ∧
    fiberSum (D∪Finset.univ.image d) (D∪Finset.univ.image d) w q-fiberSum D D w q-
      (if q∈T then 4*(k : ℝ) else 0) < 116 := by
  let E := Finset.univ.image d
  have hDE : Disjoint D E := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hb
    exact havoid u ha
  have hnew := weighted_packet_error d hd (fun i : Coord T k ↦ i.1.1.val)
    (fun i ↦ hcenter i.1 i.2) hunique w (fun u v ↦ ⟨hw0 _ _,hwnew u v⟩) q
  rw [balanced_designated_sum T k q d w hw hbal] at hnew
  have hm0 : 0 ≤ fiberSum E D w q := fiberSum_nonneg E D w q (fun i _ j _ ↦ hw0 i j)
  have hm : fiberSum E D w q < 56 := by
    have hh := fiberSum_bound E D w q 2 (by
      intro a ha b hb
      obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp ha
      exact hwmix u b hb)
    have hh' := hmixed q
    dsimp [E] at hh
    linarith
  rw [fiberSum_union_self D E hDE w hw]
  change 0 ≤ _ ∧ _ < 116
  dsimp [E] at hm0 hm
  constructor <;> linarith [hnew.1,hnew.2]

end Erdos66BalancedWeightedPacket
