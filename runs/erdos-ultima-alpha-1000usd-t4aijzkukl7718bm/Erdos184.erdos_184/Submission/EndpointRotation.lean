import Submission.EndpointEscape

/-! Exact endpoint rotation about an internal contact.  This preserves the
vertex set of a path and swaps one edge.  It is not a cycle-absorption theorem. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths.Rotation
set_option maxHeartbeats 500000
variable {V : Type*} {G : SimpleGraph V}

lemma split_before {a b v : V} (p : G.Walk a b) (hv : v ∈ p.support) (hav : a ≠ v) :
    ∃ (w : V) (A : G.Walk a w) (B : G.Walk v b) (hwv : G.Adj w v),
      p = A.append (Walk.cons hwv B) := by
  induction p with
  | nil => simp only [Walk.support_nil,List.mem_singleton] at hv; exact (hav hv.symm).elim
  | @cons a x b hax p ih =>
    have hvp : v ∈ p.support := by
      simpa only [Walk.support_cons,List.mem_cons,Ne.symm hav,false_or] using hv
    by_cases hxv : x = v
    · subst x
      exact ⟨a,.nil,p,hax,rfl⟩
    · obtain ⟨w,A,B,hwv,he⟩ := ih hvp hxv
      exact ⟨w,Walk.cons hax A,B,hwv,by rw [he]; rfl⟩

lemma support_perm {a w v b : V} (A : G.Walk a w) (B : G.Walk v b)
    (hwv : G.Adj w v) (hav : G.Adj a v) :
    (A.reverse.append (Walk.cons hav B)).support.Perm
      (A.append (Walk.cons hwv B)).support := by
  simp only [Walk.support_append,Walk.support_cons,List.tail_cons,Walk.support_reverse]
  exact (List.reverse_perm A.support).append_right B.support

lemma isPath {a w v b : V} (A : G.Walk a w) (B : G.Walk v b)
    (hwv : G.Adj w v) (hav : G.Adj a v)
    (hp : (A.append (Walk.cons hwv B)).IsPath) :
    (A.reverse.append (Walk.cons hav B)).IsPath := by
  rw [Walk.isPath_def]
  exact (support_perm A B hwv hav).nodup_iff.mpr hp.support_nodup

lemma edge_perm {a w v b : V} (A : G.Walk a w) (B : G.Walk v b)
    (hwv : G.Adj w v) (hav : G.Adj a v) :
    ((A.reverse.append (Walk.cons hav B)).edges ++ [s(w,v)]).Perm
      ((A.append (Walk.cons hwv B)).edges ++ [s(a,v)]) := by
  apply List.perm_iff_count.mpr
  intro e
  simp only [Walk.edges_append,Walk.edges_reverse,Walk.edges_cons,List.count_append,
    List.count_reverse,List.count_cons,List.count_nil]
  omega

/-- Rotation at a contact swaps an unused joining edge for the incident edge
on the endpoint's branch.  The entire vertex set is preserved. -/
lemma exists_rotation {a b v : V} (p : G.Walk a b) (hp : p.IsPath)
    (hv : v ∈ p.support) (hav : G.Adj a v) :
    ∃ (w : V) (q : G.Walk w b), G.Adj w v ∧ s(w,v) ∈ p.edges ∧
      q.IsPath ∧ w ≠ b ∧ q.support.Perm p.support ∧
      (q.edges ++ [s(w,v)]).Perm (p.edges ++ [s(a,v)]) := by
  obtain ⟨w,A,B,hwv,rfl⟩ := split_before p hv hav.ne
  let q := A.reverse.append (Walk.cons hav B)
  have hq : q.IsPath := isPath A B hwv hav hp
  have hwb : w ≠ b := by
    intro he
    subst b
    have hn := hq.support_nodup
    have hnil : q = .nil := (Walk.isPath_iff_eq_nil q).mp hq
    have hl := congrArg Walk.length hnil
    simp only [q,Walk.length_append,Walk.length_reverse,Walk.length_cons,Walk.length_nil] at hl
    omega
  refine ⟨w,q,hwv,?_,hq,hwb,support_perm A B hwv hav,edge_perm A B hwv hav⟩
  simp [Walk.edges_append,Walk.edges_cons]

end Erdos184Work.OddPaths.Rotation
#print axioms Erdos184Work.OddPaths.Rotation.exists_rotation
