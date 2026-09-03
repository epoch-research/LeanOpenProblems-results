import Submission.SameTerminalCycleRelocation

/-! Reassembly for distinct two-fan terminal paths without any vertex-disjointness
assumption. Bypassing repeated vertices may leave unused edges, and that loss
is explicitly bounded rather than silently identified with one cycle. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths
set_option maxHeartbeats 1200000
variable {V : Type*} {G : SimpleGraph V}
namespace FanRelocation

lemma join_by_bypass {L : List (Piece G)} (hL : Admissible L)
    (p q : Piece G) (hp : p ∈ L) (hq : q ∈ L) (hpq : p ≠ q)
    {v t z : V} (ht : t = p.src ∨ t = p.dst) (hz : z = q.src ∨ z = q.dst)
    (hvt : G.Adj v t) (hvz : G.Adj v z) :
    ∃ r : Piece G,
      r.walk.edges ⊆ p.walk.edges ++ q.walk.edges ++ [s(v,t),s(v,z)] ∧
      [r.src,r.dst,t,z].Perm [p.src,p.dst,q.src,q.dst] := by
  obtain ⟨a,P,hP,hPs,hPe,hPv⟩ := p.ending_at ht
  obtain ⟨b,Q,hQ,hQs,hQe,hQv⟩ := q.starting_at hz
  have hap : a = p.src ∨ a = p.dst := by
    have hh := hPv.mem_iff.mp (show a ∈ [a,t] by simp)
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hh
  have hbq : b = q.src ∨ b = q.dst := by
    have hh := hQv.mem_iff.mp (show b ∈ [z,b] by simp)
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hh
  have hab : a ≠ b := by
    intro he
    exact hpq (endpoint_owner_unique hL.2.1 hp hq hap (he.symm ▸ hbq))
  let W := (P.concat hvt.symm).append (Walk.cons hvz Q)
  let r : Piece G := ⟨a,b,W.bypass,W.bypass_isPath,hab⟩
  refine ⟨r,?_,?_⟩
  · intro e he
    have hm := W.edges_bypass_subset he
    simp only [W,Walk.edges_append,Walk.edges_concat,Walk.edges_cons,List.concat_eq_append,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false,
      show s(t,v) = s(v,t) from Sym2.eq_swap] at hm ⊢
    rcases hm with (hm | hm) | (hm | hm)
    · exact Or.inl (Or.inl (hPe.mem_iff.mp hm))
    · exact Or.inr (Or.inl hm)
    · exact Or.inr (Or.inr hm)
    · exact Or.inl (Or.inr (hQe.mem_iff.mp hm))
  · apply List.perm_iff_count.mpr
    intro w
    have h₁ := List.Perm.count_eq hPv w
    have h₂ := List.Perm.count_eq hQv w
    simp only [r,List.count_cons,List.count_nil] at h₁ h₂ ⊢
    omega

lemma distinct_terminal_exchange {L M : List (Piece G)} (hL : Admissible L)
    {v x y t z : V} (Q : G.Walk x y) (hx : G.Adj v x) (hy : G.Adj y v)
    (hC : (Walk.cons hx (Q.concat hy)).IsCycle)
    (hunused : (edgeList L).Disjoint (Walk.cons hx (Q.concat hy)).edges)
    (he : (edgeList M ++ [s(v,t),s(v,z)]).Perm (edgeList L ++ [s(v,x),s(v,y)]))
    (hv : (endpoints M ++ [x,y]).Perm (endpoints L ++ [t,z]))
    (hvt : G.Adj v t) (hvz : G.Adj v z)
    (p q : Piece G) (hp : p ∈ L) (hq : q ∈ L) (hpq : p ≠ q)
    (hpm : p ∈ M) (hqm : q ∈ M)
    (ht : t = p.src ∨ t = p.dst) (hz : z = q.src ∨ z = q.dst) :
    ∃ N : List (Piece G), Admissible N ∧ (endpoints N).Perm (endpoints L) ∧
      edgeList N ⊆ edgeList L ++ (Walk.cons hx (Q.concat hy)).edges ∧
      (edgeList L).length + (Walk.cons hx (Q.concat hy)).length ≤
        (edgeList N).length + p.walk.length + q.walk.length + 1 := by
  obtain ⟨r,hrE,hrV⟩ := join_by_bypass hL p q hp hq hpq ht hz hvt hvz
  obtain ⟨A,hA⟩ := two_at_front hpm hqm (Ne.symm hpq)
  have hedgeA := edgeList_perm hA
  have hendA := endpoints_perm hA
  have hQ : Q.IsPath := (Walk.concat_isPath_iff hy).mp
    ((Walk.cons_isCycle_iff (Q.concat hy) hx).mp hC).1 |>.1
  have hxy : x ≠ y := by
    intro hxy
    cases hxy
    have hnil := (Walk.isPath_iff_eq_nil Q).mp hQ
    have hl := hC.three_le_length
    simp only [hnil,Walk.length_cons,Walk.length_concat,Walk.length_nil] at hl
    omega
  let s : Piece G := ⟨x,y,Q,hQ,hxy⟩
  let N := r :: s :: A
  let S := p.walk.edges ++ q.walk.edges ++ [s(v,t),s(v,z)]
  have hF : (S ++ (Q.edges ++ edgeList A)).Perm
      (edgeList L ++ (Walk.cons hx (Q.concat hy)).edges) := by
    apply List.perm_iff_count.mpr
    intro e
    have h₁ := List.Perm.count_eq he e
    have h₂ := List.Perm.count_eq hedgeA e
    simp only [S,edgeList_cons,Walk.edges_cons,Walk.edges_concat,List.concat_eq_append,
      List.count_append,List.count_cons,List.count_nil,
      show s(y,v) = s(v,y) from Sym2.eq_swap] at h₁ h₂ ⊢
    omega
  have hnF := hF.nodup_iff.mpr (hL.1.append hC.isTrail.edges_nodup hunused)
  have hnN : (edgeList N).Nodup := by
    change (r.walk.edges ++ (Q.edges ++ edgeList A)).Nodup
    exact r.isPath.isTrail.edges_nodup.append hnF.of_append_right
      (fun e he hr => hnF.disjoint (hrE he) hr)
  have hNV : (endpoints N).Perm (endpoints L) := by
    apply List.perm_iff_count.mpr
    intro a
    have h₁ := List.Perm.count_eq hv a
    have h₂ := List.Perm.count_eq hendA a
    have h₃ := List.Perm.count_eq hrV a
    simp only [N,s,endpoints_cons,List.count_append,List.count_cons,List.count_nil] at h₁ h₂ h₃ ⊢
    omega
  have hN : Admissible N := ⟨hnN,hNV.nodup_iff.mpr hL.2.1,
    fun a => hNV.mem_iff.mpr (hL.2.2 a)⟩
  refine ⟨N,hN,hNV,?_,?_⟩
  · intro e he
    apply hF.mem_iff.mp
    change e ∈ r.walk.edges ++ (Q.edges ++ edgeList A) at he
    rcases List.mem_append.mp he with he | he
    · exact List.mem_append_left _ (hrE he)
    · exact List.mem_append_right _ he
  · have hlen := he.length_eq
    have hlenA := hedgeA.length_eq
    have hrpos : 0 < r.walk.length := Walk.not_nil_iff_lt_length.mp (r.walk.not_nil_of_ne r.ne)
    simp only [List.length_append,List.length_cons,List.length_nil,edgeList_cons,Walk.length_edges] at hlen hlenA
    simp only [N,s,edgeList_cons,List.length_append,Walk.length_edges,Walk.length_cons,Walk.length_concat]
    omega

lemma Maximal.distinct_terminal_length_bound {L M : List (Piece G)} (hL : Maximal L)
    {v x y t z : V} (Q : G.Walk x y) (hx : G.Adj v x) (hy : G.Adj y v)
    (hC : (Walk.cons hx (Q.concat hy)).IsCycle)
    (hunused : (edgeList L).Disjoint (Walk.cons hx (Q.concat hy)).edges)
    (he : (edgeList M ++ [s(v,t),s(v,z)]).Perm (edgeList L ++ [s(v,x),s(v,y)]))
    (hv : (endpoints M ++ [x,y]).Perm (endpoints L ++ [t,z]))
    (hvt : G.Adj v t) (hvz : G.Adj v z)
    (p q : Piece G) (hp : p ∈ L) (hq : q ∈ L) (hpq : p ≠ q)
    (hpm : p ∈ M) (hqm : q ∈ M)
    (ht : t = p.src ∨ t = p.dst) (hz : z = q.src ∨ z = q.dst) :
    (Walk.cons hx (Q.concat hy)).length ≤ p.walk.length + q.walk.length + 1 := by
  obtain ⟨N,hN,_,_,hlen⟩ := distinct_terminal_exchange hL.1 Q hx hy hC hunused he hv
    hvt hvz p q hp hq hpq hpm hqm ht hz
  have hm := hL.2 N hN
  omega

end FanRelocation
end Erdos184Work.OddPaths
#print axioms Erdos184Work.OddPaths.FanRelocation.join_by_bypass
#print axioms Erdos184Work.OddPaths.FanRelocation.distinct_terminal_exchange
#print axioms Erdos184Work.OddPaths.FanRelocation.Maximal.distinct_terminal_length_bound
