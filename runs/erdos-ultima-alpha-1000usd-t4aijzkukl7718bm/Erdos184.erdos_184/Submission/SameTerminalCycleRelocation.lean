import Submission.FanCycleMaximality

/-! An exact relocation of an unused cycle when both two-fan terminal endpoints
belong to the same packed path. This is not in general an augmentation. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths
set_option maxHeartbeats 1200000
variable {V : Type*} {G : SimpleGraph V}

namespace Piece
lemma oriented_between (p : Piece G) {t z : V} (htz : t ≠ z)
    (ht : t = p.src ∨ t = p.dst) (hz : z = p.src ∨ z = p.dst) :
    ∃ P : G.Walk t z, P.IsPath ∧ P.support.Perm p.walk.support ∧
      P.edges.Perm p.walk.edges ∧ [t,z].Perm [p.src,p.dst] := by
  obtain ⟨b,P,hP,hPs,hPe,hPv⟩ := p.starting_at ht
  have hz' : z ∈ [t,b] := hPv.mem_iff.mpr (by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hz)
  have hzb : z = b := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false,Ne.symm htz,false_or] using hz'
  cases hzb
  exact ⟨P,hP,hPs,hPe,hPv⟩

lemma cycle_through_new_vertex (p : Piece G) {v t z : V} (htz : t ≠ z)
    (ht : t = p.src ∨ t = p.dst) (hz : z = p.src ∨ z = p.dst)
    (hvt : G.Adj v t) (hvz : G.Adj v z) (hvp : v ∉ p.walk.support) :
    ∃ D : G.Walk v v, D.IsCycle ∧
      D.edges.Perm (p.walk.edges ++ [s(v,t),s(v,z)]) ∧
      D.length = p.walk.length + 2 ∧
      (∀ w, w ∈ D.support ↔ w = v ∨ w ∈ p.walk.support) ∧
      [t,z].Perm [p.src,p.dst] := by
  obtain ⟨P,hP,hPs,hPe,hPv⟩ := p.oriented_between htz ht hz
  have hvP : v ∉ P.support := fun h => hvp (hPs.mem_iff.mp h)
  let D := Walk.cons hvt (P.concat hvz.symm)
  have hD : D.IsCycle := by
    apply (Walk.cons_isCycle_iff (P.concat hvz.symm) hvt).mpr
    refine ⟨hP.concat hvP hvz.symm,?_⟩
    simp only [Walk.edges_concat,List.concat_eq_append,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false,not_or]
    constructor
    · intro h
      exact hvP (P.fst_mem_support_of_mem_edges h)
    · intro he
      rcases Sym2.eq_iff.mp he with he | he
      · exact hvt.ne he.2.symm
      · exact htz he.2
  have he : D.edges.Perm (p.walk.edges ++ [s(v,t),s(v,z)]) := by
    apply List.perm_iff_count.mpr
    intro e
    have hh := List.Perm.count_eq hPe e
    simp only [D,Walk.edges_cons,Walk.edges_concat,List.concat_eq_append,List.count_append,
      List.count_cons,List.count_nil,show s(z,v) = s(v,z) from Sym2.eq_swap] at hh ⊢
    omega
  refine ⟨D,hD,he,?_,?_,hPv⟩
  · have hh := he.length_eq
    simpa only [List.length_append,List.length_cons,List.length_nil,Walk.length_edges] using hh
  · intro w
    simp only [D,Walk.support_cons,Walk.support_concat,List.mem_cons,List.concat_eq_append,List.mem_append,
      List.not_mem_nil,or_false]
    rw [hPs.mem_iff]
    tauto
end Piece

namespace FanRelocation

/-- Replace the old cycle rim by a path and move the unused cycle onto the
single terminal path. Endpoint uniqueness is restored in the new family. -/
lemma same_terminal_path {L M : List (Piece G)} (hL : Admissible L)
    {v x y t z : V} (Q : G.Walk x y) (hx : G.Adj v x) (hy : G.Adj y v)
    (hC : (Walk.cons hx (Q.concat hy)).IsCycle)
    (hunused : (edgeList L).Disjoint (Walk.cons hx (Q.concat hy)).edges)
    (he : (edgeList M ++ [s(v,t),s(v,z)]).Perm (edgeList L ++ [s(v,x),s(v,y)]))
    (hv : (endpoints M ++ [x,y]).Perm (endpoints L ++ [t,z]))
    (htz : t ≠ z) (hvt : G.Adj v t) (hvz : G.Adj v z)
    (p : Piece G) (hp : p ∈ M)
    (ht : t = p.src ∨ t = p.dst) (hz : z = p.src ∨ z = p.dst)
    (hvp : v ∉ p.walk.support) :
    ∃ (N : List (Piece G)) (D : G.Walk v v), Admissible N ∧ D.IsCycle ∧
      (edgeList N ++ D.edges).Nodup ∧
      (edgeList N ++ D.edges).Perm (edgeList L ++ (Walk.cons hx (Q.concat hy)).edges) ∧
      (endpoints N).Perm (endpoints L) ∧ D.length = p.walk.length + 2 ∧
      (∀ w, w ∈ D.support ↔ w = v ∨ w ∈ p.walk.support) := by
  have hM := List.perm_cons_erase hp
  have hedgeM := edgeList_perm hM
  have hendM := endpoints_perm hM
  obtain ⟨D,hD,hDE,hDl,hDs,hpV⟩ := p.cycle_through_new_vertex htz ht hz hvt hvz hvp
  have hQ : Q.IsPath := (Walk.concat_isPath_iff hy).mp
    ((Walk.cons_isCycle_iff (Q.concat hy) hx).mp hC).1 |>.1
  have hxy : x ≠ y := by
    intro hxy
    cases hxy
    have hnil := (Walk.isPath_iff_eq_nil Q).mp hQ
    have hl := hC.three_le_length
    simp only [hnil,Walk.length_cons,Walk.length_concat,Walk.length_nil] at hl
    omega
  let q : Piece G := ⟨x,y,Q,hQ,hxy⟩
  let N := q :: M.erase p
  have hNE : (edgeList N ++ D.edges).Perm
      (edgeList L ++ (Walk.cons hx (Q.concat hy)).edges) := by
    apply List.perm_iff_count.mpr
    intro e
    have h₁ := List.Perm.count_eq he e
    have h₂ := List.Perm.count_eq hedgeM e
    have h₃ := List.Perm.count_eq hDE e
    simp only [N,q,edgeList_cons,Walk.edges_cons,Walk.edges_concat,List.concat_eq_append,
      List.count_append,List.count_cons,List.count_nil,
      show s(y,v) = s(v,y) from Sym2.eq_swap] at h₁ h₂ h₃ ⊢
    omega
  have hNV : (endpoints N).Perm (endpoints L) := by
    apply List.perm_iff_count.mpr
    intro a
    have h₁ := List.Perm.count_eq hv a
    have h₂ := List.Perm.count_eq hendM a
    have h₃ := List.Perm.count_eq hpV a
    simp only [N,q,endpoints_cons,List.count_append,List.count_cons,List.count_nil] at h₁ h₂ h₃ ⊢
    omega
  have hnodup := hNE.nodup_iff.mpr (hL.1.append hC.isTrail.edges_nodup hunused)
  have hN : Admissible N := ⟨hnodup.of_append_left,hNV.nodup_iff.mpr hL.2.1,
    fun a => hNV.mem_iff.mpr (hL.2.2 a)⟩
  exact ⟨N,D,hN,hD,hnodup,hNE,hNV,hDl,hDs⟩

lemma Maximal.relocated_cycle_not_shorter {L N : List (Piece G)} (hL : Maximal L)
    (hN : Admissible N) {v w : V} (C : G.Walk v v) (D : G.Walk w w)
    (he : (edgeList N ++ D.edges).Perm (edgeList L ++ C.edges)) :
    C.length ≤ D.length := by
  have hh := he.length_eq
  have hm := hL.2 N hN
  simp only [List.length_append,Walk.length_edges] at hh
  omega

end FanRelocation

variable [Fintype V]

/-- At an unused cycle, either two distinct escaping paths intersect, or
there is an actual one-cycle relocation onto a single escaping path. -/
lemma Maximal.unused_cycle_relocation_or_distinct_contact {L : List (Piece G)}
    (hL : Maximal L) {v : V} (C : G.Walk v v) (hC : C.IsCycle)
    (hunused : (edgeList L).Disjoint C.edges) :
    (∃ (p : Piece G) (N : List (Piece G)) (D : G.Walk v v),
      p ∈ L ∧ v ∉ p.walk.support ∧ Admissible N ∧ D.IsCycle ∧
      (edgeList N ++ D.edges).Nodup ∧
      (edgeList N ++ D.edges).Perm (edgeList L ++ C.edges) ∧
      (endpoints N).Perm (endpoints L) ∧ C.length ≤ D.length ∧
      D.length = p.walk.length + 2 ∧
      (∀ w, w ∈ D.support ↔ w = v ∨ w ∈ p.walk.support)) ∨
    (∃ (p q : Piece G) (w : V), p ∈ L ∧ q ∈ L ∧ p ≠ q ∧
      v ∉ p.walk.support ∧ v ∉ q.walk.support ∧
      w ∈ p.walk.support ∧ w ∈ q.walk.support) := by
  obtain ⟨x,y,Q,hx,hy,heq,hxy⟩ := FanAbsorption.cycle_as_rim C hC
  have hQcy : (Walk.cons hx (Q.concat hy)).IsCycle := heq ▸ hC
  have hdisQ : (edgeList L).Disjoint (Walk.cons hx (Q.concat hy)).edges := heq ▸ hunused
  have hxu : (G \ coveredGraph L).Adj v x := by
    refine ⟨hx,?_⟩
    intro h
    exact hdisQ ((coveredGraph_adj L v x).mp h) (by simp)
  have hyu : (G \ coveredGraph L).Adj v y := by
    refine ⟨hy.symm,?_⟩
    intro h
    apply hdisQ ((coveredGraph_adj L v y).mp h)
    simp [Walk.edges_concat,Sym2.eq_swap]
  obtain ⟨t,z,M,htz,hvt,hvz,ht,hz,_,hME,hMV,hkeep⟩ := hL.1.rotate_two_endpoint_fans hxu hyu hxy
  obtain ⟨p,hp,hpt,hpv⟩ := hL.1.endpoint_path_avoids_of_not_touching ht
  obtain ⟨q,hq,hqz,hqv⟩ := hL.1.endpoint_path_avoids_of_not_touching hz
  by_cases hpq : p = q
  · subst q
    obtain ⟨N,D,hN,hD,hn,he,hends,hl,hs⟩ := FanRelocation.same_terminal_path hL.1 Q hx hy
      hQcy hdisQ hME hMV htz hvt hvz p (hkeep p hp hpv) hpt hqz hpv
    have he' : (edgeList N ++ D.edges).Perm (edgeList L ++ C.edges) := by rwa [heq]
    have hlen := FanRelocation.Maximal.relocated_cycle_not_shorter hL hN C D he'
    exact Or.inl ⟨p,N,D,hp,hpv,hN,hD,hn,he',hends,hlen,hl,hs⟩
  · right
    have hnot : ¬ p.walk.support.Disjoint q.walk.support := by
      intro hd
      exact FanAbsorption.no_disjoint_terminal_paths hL Q hx hy hQcy hdisQ hME hMV hvt hvz
        p q (hkeep p hp hpv) (hkeep q hq hqv) hpt hqz hpv hqv hd
    have hm : ∃ w, w ∈ p.walk.support ∧ w ∈ q.walk.support := by
      by_contra! hh
      exact hnot (fun w hw hqw => hh w hw hqw)
    obtain ⟨w,hwp,hwq⟩ := hm
    exact ⟨p,q,w,hp,hq,hpq,hpv,hqv,hwp,hwq⟩

end Erdos184Work.OddPaths
#print axioms Erdos184Work.OddPaths.Piece.cycle_through_new_vertex
#print axioms Erdos184Work.OddPaths.FanRelocation.same_terminal_path
#print axioms Erdos184Work.OddPaths.FanRelocation.Maximal.relocated_cycle_not_shorter

#print axioms Erdos184Work.OddPaths.Maximal.unused_cycle_relocation_or_distinct_contact
