import Submission.OccurrenceFamilyRotation

/-! Finite occurrence fans and their exact edge and endpoint defects. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths.OccurrenceFan
set_option maxHeartbeats 1200000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- An unused incident edge starts a branch fan.  The terminal endpoint's
packed path avoids the center; each step follows an actual branch of a path. -/
lemma exists_endpoint_fan {L : List (Piece G)} (hnodup : (edgeList L).Nodup)
    {v x : V} (hx : (G \ coveredGraph L).Adj v x) :
    ∃ n : ℕ, n ≤ ((touchingEndpoints L v).erase v).card ∧
      (∀ i < n, (step L v)^[i] x ∈ (touchingEndpoints L v).erase v) ∧
      (step L v)^[n] x ∉ touchingEndpoints L v ∧
      (∀ i ≤ n, G.Adj v ((step L v)^[i] x)) ∧
      (∀ i < n, Branch L v ((step L v)^[i] x) ((step L v)^[i+1] x)) ∧
      Function.Injective (fun i : Fin (n+1) => (step L v)^[i.val] x) := by
  have hstart : x ∉ ((touchingEndpoints L v).erase v).image (step L v) := by
    intro h
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp h
    exact hx.2 (he ▸ (step_branch ha).covered)
  obtain ⟨n,hn,hbefore,hexit,hinj⟩ := PartialInjectionFan.exists_first_exit
    ((touchingEndpoints L v).erase v) (step L v) (step_injective hnodup v) x hstart
  have hadj : ∀ i ≤ n, G.Adj v ((step L v)^[i] x) := by
    intro i hi
    cases i with
    | zero => exact hx.1
    | succ i =>
      rw [Function.iterate_succ_apply']
      exact coveredGraph_le L ((step_branch (hbefore i (by omega))).covered)
  have hnot : (step L v)^[n] x ∉ touchingEndpoints L v := by
    intro hm
    apply hexit
    exact Finset.mem_erase.mpr ⟨(hadj n (by omega)).ne.symm,hm⟩
  refine ⟨n,hn,hbefore,hnot,hadj,?_,hinj⟩
  intro i hi
  rw [Function.iterate_succ_apply']
  exact step_branch (hbefore i hi)

noncomputable def fanPrefix (L : List (Piece G)) (v x : V) (n : ℕ) : List V :=
  (List.range n).map (fun i => (step L v)^[i] x)

lemma mem_fanPrefix {L : List (Piece G)} {v x a : V} {n : ℕ} :
    a ∈ fanPrefix L v x n ↔ ∃ i < n, (step L v)^[i] x = a := by
  simp only [fanPrefix,List.mem_map,List.mem_range]

lemma fanPrefix_nodup {L : List (Piece G)} {v x : V} {n : ℕ}
    (hi : Function.Injective (fun i : Fin (n+1) => (step L v)^[i.val] x)) :
    (fanPrefix L v x n).Nodup := by
  apply (List.nodup_map_iff_inj_on List.nodup_range).mpr
  intro i hi' j hj' he
  have hii : i < n := List.mem_range.mp hi'
  have hjj : j < n := List.mem_range.mp hj'
  have hf := hi (a₁ := ⟨i,by omega⟩) (a₂ := ⟨j,by omega⟩) he
  exact congrArg (fun a : Fin (n+1) => a.val) hf
lemma cancel_fan_accounting {L M : List (Piece G)} {v x t : V} {A : List V}
    (he : (edgeList M ++ (A.map (step L v)).map (fun a => s(v,a))).Perm
      (edgeList L ++ A.map (fun a => s(v,a))))
    (hv : (endpoints M ++ A).Perm (endpoints L ++ A.map (step L v)))
    (ht : (A.map (step L v) ++ [x]).Perm (A ++ [t])) :
    (edgeList M ++ [s(v,t)]).Perm (edgeList L ++ [s(v,x)]) ∧
      (endpoints M ++ [x]).Perm (endpoints L ++ [t]) := by
  constructor
  · apply List.perm_iff_count.mpr
    intro e
    have h₁ := List.Perm.count_eq he e
    have h₂ := List.Perm.count_eq (ht.map (fun a => s(v,a))) e
    simp only [List.map_append,List.map_cons,List.map_nil,List.count_append,List.count_cons,List.count_nil] at h₁ h₂ ⊢
    omega
  · apply List.perm_iff_count.mpr
    intro a
    have h₁ := List.Perm.count_eq hv a
    have h₂ := List.Perm.count_eq ht a
    simp only [List.count_append,List.count_cons,List.count_nil] at h₁ h₂ ⊢
    omega

lemma rotate_endpoint_fan {L : List (Piece G)} (hnodup : (edgeList L).Nodup)
    {v x : V} (hx : (G \ coveredGraph L).Adj v x) :
    ∃ (t : V) (M : List (Piece G)), G.Adj v t ∧ t ∉ touchingEndpoints L v ∧
      (edgeList M ++ [s(v,t)]).Nodup ∧
      (edgeList M ++ [s(v,t)]).Perm (edgeList L ++ [s(v,x)]) ∧
      (endpoints M ++ [x]).Perm (endpoints L ++ [t]) ∧
      (∀ p ∈ L, v ∉ p.walk.support → p ∈ M) := by
  obtain ⟨n,_,hxn,hxt,hxN,_,hxi⟩ := exists_endpoint_fan hnodup hx
  let t := (step L v)^[n] x
  let A := fanPrefix L v x n
  have hA : A.Nodup := fanPrefix_nodup hxi
  have hS : A.toFinset ⊆ (touchingEndpoints L v).erase v := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := mem_fanPrefix.mp (List.mem_toFinset.mp ha)
    exact hxn i hi
  have hN : ∀ a ∈ A.toFinset, G.Adj v a := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := mem_fanPrefix.mp (List.mem_toFinset.mp ha)
    exact hxN i (by omega)
  obtain ⟨M,he,hv,hkeep⟩ := list_rotation hnodup A hA hS hN
  have ht : (A.map (step L v) ++ [x]).Perm (A ++ [t]) :=
    FanRotation.iterate_prefix_perm (step L v) x n
  obtain ⟨hedges,hends⟩ := cancel_fan_accounting he hv ht
  have hstart : (edgeList L ++ [s(v,x)]).Nodup := by
    apply hnodup.append (by simp)
    intro e he hm
    have heq : e = s(v,x) := by simpa using hm
    subst e
    exact hx.2 ((coveredGraph_adj L v x).mpr he)
  exact ⟨t,M,hxN n (le_refl _),hxt,hedges.nodup_iff.mpr hstart,hedges,hends,hkeep⟩

end Erdos184Work.OddPaths.OccurrenceFan
#print axioms Erdos184Work.OddPaths.OccurrenceFan.rotate_endpoint_fan
