import Submission.EndpointFanAccounting

/-! Two branch fans can be rotated simultaneously in the actual path family.
This leaves the two terminal incident edges unused and records exactly which
endpoints have moved.  It is not yet an absorption statement. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths
set_option maxHeartbeats 1200000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}
namespace FanRotation

lemma cancel_lists_accounting {L M : List (Piece G)} {v : V} {A X T : List V}
    (he : (edgeList M ++ (A.map (fanStep L v)).map (fun a => s(v,a))).Perm
      (edgeList L ++ A.map (fun a => s(v,a))))
    (hv : (endpoints M ++ A).Perm (endpoints L ++ A.map (fanStep L v)))
    (ht : (A.map (fanStep L v) ++ X).Perm (A ++ T)) :
    (edgeList M ++ T.map (fun a => s(v,a))).Perm
      (edgeList L ++ X.map (fun a => s(v,a))) ∧
      (endpoints M ++ X).Perm (endpoints L ++ T) := by
  constructor
  · apply List.perm_iff_count.mpr
    intro e
    have h₁ := List.Perm.count_eq he e
    have h₂ := List.Perm.count_eq (ht.map (fun a => s(v,a))) e
    simp only [List.map_append,List.count_append] at h₁ h₂ ⊢
    omega
  · apply List.perm_iff_count.mpr
    intro a
    have h₁ := List.Perm.count_eq hv a
    have h₂ := List.Perm.count_eq ht a
    simp only [List.count_append] at h₁ h₂ ⊢
    omega

noncomputable def fanPrefix (L : List (Piece G)) (v x : V) (n : ℕ) : List V :=
  (List.range n).map (fun i => (fanStep L v)^[i] x)

lemma mem_fanPrefix {L : List (Piece G)} {v x a : V} {n : ℕ} :
    a ∈ fanPrefix L v x n ↔ ∃ i < n, (fanStep L v)^[i] x = a := by
  simp only [fanPrefix,List.mem_map,List.mem_range]

lemma fanPrefix_nodup {L : List (Piece G)} {v x : V} {n : ℕ}
    (hi : Function.Injective (fun i : Fin (n+1) => (fanStep L v)^[i.val] x)) :
    (fanPrefix L v x n).Nodup := by
  apply (List.nodup_map_iff_inj_on List.nodup_range).mpr
  intro i hi' j hj' he
  have hii : i < n := List.mem_range.mp hi'
  have hjj : j < n := List.mem_range.mp hj'
  have hf := hi (a₁ := ⟨i,by omega⟩) (a₂ := ⟨j,by omega⟩) he
  exact congrArg (fun a : Fin (n+1) => a.val) hf

end FanRotation

/-- The two terminal paths need not be different, and need not be disjoint.
Every packed path avoiding the center is retained unchanged in the new family. -/
lemma Admissible.rotate_two_endpoint_fans {L : List (Piece G)} (hL : Admissible L)
    {v x y : V} (hx : (G \ coveredGraph L).Adj v x) (hy : (G \ coveredGraph L).Adj v y)
    (hxy : x ≠ y) :
    ∃ (t z : V) (M : List (Piece G)), t ≠ z ∧ G.Adj v t ∧ G.Adj v z ∧
      t ∉ touchingEndpoints L v ∧ z ∉ touchingEndpoints L v ∧
      (edgeList M ++ [s(v,t),s(v,z)]).Nodup ∧
      (edgeList M ++ [s(v,t),s(v,z)]).Perm (edgeList L ++ [s(v,x),s(v,y)]) ∧
      (endpoints M ++ [x,y]).Perm (endpoints L ++ [t,z]) ∧
      (∀ p ∈ L, v ∉ p.walk.support → p ∈ M) := by
  obtain ⟨n,_,hxn,hxt,hxN,_,hxi,_⟩ := hL.exists_endpoint_fan hx
  obtain ⟨m,_,hym,hyt,hyN,_,hyi,_⟩ := hL.exists_endpoint_fan hy
  let t := (fanStep L v)^[n] x
  let z := (fanStep L v)^[m] y
  let A := FanRotation.fanPrefix L v x n
  let B := FanRotation.fanPrefix L v y m
  have hAB : A.Disjoint B := by
    intro a ha hb
    obtain ⟨i,hi,hia⟩ := FanRotation.mem_fanPrefix.mp ha
    obtain ⟨j,hj,hja⟩ := FanRotation.mem_fanPrefix.mp hb
    exact hL.endpoint_fans_disjoint hx hy hxy hxn hym (by omega) (by omega) (hia.trans hja.symm)
  have hnAB : (A ++ B).Nodup :=
    (FanRotation.fanPrefix_nodup hxi).append (FanRotation.fanPrefix_nodup hyi) hAB
  have hS : (A ++ B).toFinset ⊆ (touchingEndpoints L v).erase v := by
    intro a ha
    rcases List.mem_append.mp (List.mem_toFinset.mp ha) with ha | ha
    · obtain ⟨i,hi,rfl⟩ := FanRotation.mem_fanPrefix.mp ha
      exact hxn i hi
    · obtain ⟨i,hi,rfl⟩ := FanRotation.mem_fanPrefix.mp ha
      exact hym i hi
  have hN : ∀ a ∈ (A ++ B).toFinset, G.Adj v a := by
    intro a ha
    rcases List.mem_append.mp (List.mem_toFinset.mp ha) with ha | ha
    · obtain ⟨i,hi,rfl⟩ := FanRotation.mem_fanPrefix.mp ha
      exact hxN i (by omega)
    · obtain ⟨i,hi,rfl⟩ := FanRotation.mem_fanPrefix.mp ha
      exact hyN i (by omega)
  obtain ⟨M,he,hv,hkeep⟩ := FanRotation.list_rotation hL v (A ++ B) hnAB hS hN
  have ht : ((A ++ B).map (fanStep L v) ++ [x,y]).Perm (A ++ B ++ [t,z]) := by
    have h₁ := FanRotation.iterate_prefix_perm (fanStep L v) x n
    have h₂ := FanRotation.iterate_prefix_perm (fanStep L v) y m
    change (A.map (fanStep L v) ++ [x]).Perm (A ++ [t]) at h₁
    change (B.map (fanStep L v) ++ [y]).Perm (B ++ [z]) at h₂
    apply List.perm_iff_count.mpr
    intro a
    have h₁ := List.Perm.count_eq h₁ a
    have h₂ := List.Perm.count_eq h₂ a
    simp only [List.map_append,List.count_append,List.count_cons,List.count_nil] at h₁ h₂ ⊢
    omega
  obtain ⟨hedges,hends⟩ := FanRotation.cancel_lists_accounting he hv ht
  simp only [List.map_cons,List.map_nil] at hedges
  have hstart : (edgeList L ++ [s(v,x),s(v,y)]).Nodup := by
    apply hL.1.append
    · have he : s(v,x) ≠ s(v,y) := by
        intro h
        rcases Sym2.eq_iff.mp h with h | h
        · exact hxy h.2
        · exact hx.1.ne h.2.symm
      simpa using he
    · intro e he hm
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl | rfl
      · exact hx.2 ((coveredGraph_adj L v x).mpr he)
      · exact hy.2 ((coveredGraph_adj L v y).mpr he)
  exact ⟨t,z,M,hL.endpoint_fans_disjoint hx hy hxy hxn hym (le_refl n) (le_refl m),
    hxN n (le_refl _),hyN m (le_refl _),hxt,hyt,hedges.nodup_iff.mpr hstart,hedges,hends,hkeep⟩

end Erdos184Work.OddPaths
#print axioms Erdos184Work.OddPaths.Admissible.rotate_two_endpoint_fans
