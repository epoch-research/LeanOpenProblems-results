import Submission.TwoEndpointFanRotation

/-! Single-fan rotation, retaining the support and center endpoint of each
original path. This is a local exchange, not a general decomposition theorem. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths
set_option maxHeartbeats 1200000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma Admissible.rotate_endpoint_fan {L : List (Piece G)} (hL : Admissible L)
    {v x : V} (hx : (G \ coveredGraph L).Adj v x) :
    ∃ (t : V) (M : List (Piece G)), G.Adj v t ∧ t ∉ touchingEndpoints L v ∧
      (edgeList M ++ [s(v,t)]).Nodup ∧
      (edgeList M ++ [s(v,t)]).Perm (edgeList L ++ [s(v,x)]) ∧
      (endpoints M ++ [x]).Perm (endpoints L ++ [t]) ∧
      (∀ p ∈ L, v ∉ p.walk.support → p ∈ M) ∧
      (∀ p ∈ L, ∃ q ∈ M, q.walk.support.Perm p.walk.support ∧
        (p.src = v → q.src = v) ∧ (p.dst = v → q.dst = v)) := by
  obtain ⟨n,_,hxn,hxt,hxN,_,hxi,_⟩ := hL.exists_endpoint_fan hx
  let t := (fanStep L v)^[n] x
  let A := FanRotation.fanPrefix L v x n
  have hA : A.Nodup := FanRotation.fanPrefix_nodup hxi
  have hS : A.toFinset ⊆ (touchingEndpoints L v).erase v := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := FanRotation.mem_fanPrefix.mp (List.mem_toFinset.mp ha)
    exact hxn i hi
  have hN : ∀ a ∈ A.toFinset, G.Adj v a := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := FanRotation.mem_fanPrefix.mp (List.mem_toFinset.mp ha)
    exact hxN i (by omega)
  let M := FanRotation.moveFamily hL A.toFinset hS hN
  have he : (edgeList M ++ (A.map (fanStep L v)).map (fun a => s(v,a))).Perm
      (edgeList L ++ A.map (fun a => s(v,a))) := by
    have he := FanRotation.moveFamily_edges hL A.toFinset hS hN
    have ha := FanRotation.addedStar_perm hL A hA v
    have hr := FanRotation.removedStar_perm hL A hA v
    apply List.perm_iff_count.mpr
    intro e
    have h₁ := List.Perm.count_eq he e
    have h₂ := List.Perm.count_eq ha e
    have h₃ := List.Perm.count_eq hr e
    simp only [List.count_append] at h₁ ⊢
    change (edgeList M).count e + _ = _ at h₁
    omega
  have hv : (endpoints M ++ A).Perm (endpoints L ++ A.map (fanStep L v)) := by
    have hv := FanRotation.moveFamily_endpoints hL A.toFinset hS hN
    have hc := FanRotation.endpoint_map_account L v A.toFinset (endpoints L)
    have hp := FanRotation.selected_endpoints_perm hL A hA
    apply List.perm_iff_count.mpr
    intro a
    have h₁ := List.Perm.count_eq hc a
    have h₂ := List.Perm.count_eq hp a
    have h₃ := List.Perm.count_eq (hp.map (fanStep L v)) a
    change endpoints M = _ at hv
    rw [hv]
    simp only [List.count_append] at h₁ ⊢
    omega
  have ht : (A.map (fanStep L v) ++ [x]).Perm (A ++ [t]) :=
    FanRotation.iterate_prefix_perm (fanStep L v) x n
  obtain ⟨hedges,hends⟩ := FanRotation.cancel_fan_accounting he hv ht
  have hstart : (edgeList L ++ [s(v,x)]).Nodup := by
    apply hL.1.append (by simp)
    intro e he hm
    have heq : e = s(v,x) := by simpa using hm
    subst e
    exact hx.2 ((coveredGraph_adj L v x).mpr he)
  refine ⟨t,M,hxN n (le_refl _),hxt,hedges.nodup_iff.mpr hstart,hedges,hends,
    fun p hp hpv => FanRotation.moveFamily_avoiding hL A.toFinset hS hN hp hpv,?_⟩
  intro p hp
  have hs := FanRotation.movePiece_spec hL A.toFinset hS hN hp
  refine ⟨FanRotation.movePiece hL A.toFinset hS hN p,
    List.mem_map_of_mem (f := FanRotation.movePiece hL A.toFinset hS hN) hp,hs.support,?_,?_⟩
  · intro h
    rw [hs.src,h,movedEndpoint,if_neg (fun hv => (Finset.mem_erase.mp (hS hv)).1 rfl)]
  · intro h
    rw [hs.dst,h,movedEndpoint,if_neg (fun hv => (Finset.mem_erase.mp (hS hv)).1 rfl)]

end Erdos184Work.OddPaths
#print axioms Erdos184Work.OddPaths.Admissible.rotate_endpoint_fan
