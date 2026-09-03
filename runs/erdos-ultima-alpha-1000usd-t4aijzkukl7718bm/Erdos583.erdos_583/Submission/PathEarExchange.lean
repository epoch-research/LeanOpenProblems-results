import Submission.ShortTriangleMixedCases

/-! Exchanging a two-edge segment of a path with a chord carried by another path. -/
namespace Erdos583PathEarExchangeDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.TailEar
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma path_ear_exchange {V : Type*} [Fintype V] {G : SimpleGraph V}
    {p q u v a x b : V} (A : G.Walk p a) (B : G.Walk b q)
    (hax : G.Adj a x) (hxb : G.Adj x b) (hab : G.Adj a b)
    (hP : (A.append (Walk.cons hax (Walk.cons hxb B))).IsPath)
    (Q : G.Walk u v) (hQ : Q.IsPath) (he : s(a,b) ∈ Q.edges) (hx : x ∉ Q.support)
    (hd : Disjoint (A.append (Walk.cons hax (Walk.cons hxb B))).toSubgraph.edgeSet Q.toSubgraph.edgeSet) :
    ∃ R : G.Walk u v, R.IsPath ∧
      Disjoint (A.append (Walk.cons hab B)).toSubgraph.edgeSet R.toSubgraph.edgeSet ∧
      (A.append (Walk.cons hab B)).toSubgraph.edgeSet ∪ R.toSubgraph.edgeSet=
        (A.append (Walk.cons hax (Walk.cons hxb B))).toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet ∧
      R.toSubgraph.edgeSet=(Q.toSubgraph.edgeSet \ {s(a,b)}) ∪ {s(a,x),s(x,b)} := by
  classical
  obtain ⟨R,hR,hRe⟩ := CycleEar.path_expand_fresh_ear Q hQ hax hxb hab.ne he hx
  let P' := A.append (Walk.cons hab B)
  have hP'x : x ∉ P'.support := shortcut_avoids_ear A B hax hxb hab hP
  let E := A.toSubgraph.edgeSet ∪ B.toSubgraph.edgeSet
  let S : Set (Sym2 V) := {s(a,x),s(x,b)}
  have hOld : (A.append (Walk.cons hax (Walk.cons hxb B))).toSubgraph.edgeSet=E ∪ S := by
    ext e
    simp only [E,S,Walk.mem_edges_toSubgraph,Walk.edges_append,Walk.edges_cons,List.mem_append,
      List.mem_cons,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff]
    tauto
  have hNew : P'.toSubgraph.edgeSet=E ∪ {s(a,b)} := by
    ext e
    simp only [P',E,Walk.mem_edges_toSubgraph,Walk.edges_append,Walk.edges_cons,List.mem_append,
      List.mem_cons,Set.mem_union,Set.mem_singleton_iff]
    tauto
  have hsep : Disjoint P'.toSubgraph.edgeSet R.toSubgraph.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e heP heR
    rw [hRe] at heR
    rcases heR with heR | heS
    · rw [hNew] at heP
      rcases heP with heE | heab
      · exact Set.disjoint_left.mp hd (hOld.symm ▸ Or.inl heE) heR.1
      · exact heR.2 heab
    · rcases heS with heax | hexb
      · rw [heax] at heP
        exact hP'x (Walk.mem_support_of_adj_toSubgraph heP.symm)
      · rw [hexb] at heP
        exact hP'x (Walk.mem_support_of_adj_toSubgraph heP)
  refine ⟨R,hR,hsep,?_,hRe⟩
  change P'.toSubgraph.edgeSet ∪ R.toSubgraph.edgeSet=_
  rw [hNew,hOld,hRe]
  have heQ : s(a,b) ∈ Q.toSubgraph.edgeSet := Q.mem_edges_toSubgraph.mpr he
  ext e
  simp only [S,Set.mem_union,Set.mem_diff,Set.mem_insert_iff,Set.mem_singleton_iff]
  by_cases heq : e=s(a,b)
  · subst e
    simp only [heQ,eq_self,or_true,true_or]
  · tauto

lemma ear_expansion_support_subset {V : Type*} {G : SimpleGraph V} {u v a x b : V}
    (P Q : G.Walk u v) (he : s(a,b) ∈ P.edges)
    (hQe : Q.toSubgraph.edgeSet=(P.toSubgraph.edgeSet \ {s(a,b)}) ∪ {s(a,x),s(x,b)}) :
    ∀ z ∈ Q.support, z=x ∨ z ∈ P.support := by
  have hax : s(a,x) ∈ Q.toSubgraph.edgeSet := hQe.symm ▸ Or.inr (Or.inl rfl)
  have hnQ : ¬Q.Nil := Walk.not_nil_of_adj_toSubgraph hax
  intro z hz
  obtain ⟨e,heQ,hze⟩ := (Walk.mem_support_iff_exists_mem_edges_of_not_nil hnQ).mp hz
  have hh : e ∈ (P.toSubgraph.edgeSet \ {s(a,b)}) ∪ {s(a,x),s(x,b)} :=
    hQe ▸ Q.mem_edges_toSubgraph.mpr heQ
  rcases hh with hh | hh | hh
  · exact Or.inr (Walk.mem_support_of_mem_edges (P.mem_edges_toSubgraph.mp hh.1) hze)
  · subst e
    rcases Sym2.mem_iff.mp hze with hz | hz
    · subst z; exact Or.inr (P.fst_mem_support_of_mem_edges he)
    · exact Or.inl hz
  · subst e
    rcases Sym2.mem_iff.mp hze with hz | hz
    · exact Or.inl hz
    · subst z; exact Or.inr (P.snd_mem_support_of_mem_edges he)

end Erdos583PathEarExchangeDevelopment
