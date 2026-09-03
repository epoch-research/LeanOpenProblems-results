import Submission.TwoSpokeSeparatedLift

/-! Two-spoke lifting for general indexed path families with distinct receiving slots. -/
namespace Erdos583GeneralTwoSpokeLiftDevelopment
open SimpleGraph Erdos583Work Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open scoped Classical
set_option maxHeartbeats 2200000
set_option Elab.async false

lemma orient_two_slots {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hp : ∀ i, (T.walk i).IsPath)
    (i j : Fin k) (hij : i ≠ j) (a b : V)
    (ha : a=T.start i ∨ a=T.finish i) (hb : b=T.start j ∨ b=T.finish j) :
    ∃ R : TrailFamily G k, (∀ l, (R.walk l).IsPath) ∧ R.start i=a ∧ R.start j=b := by
  obtain ⟨S,hSs,_,hSa,hSr,hSe⟩ := orient_endpoint_start T i a ha
  have hbS : b=S.start j ∨ b=S.finish j := by
    obtain ⟨hja,hjb⟩ := hSr j hij.symm
    rw [hja,hjb]
    exact hb
  obtain ⟨R,hRs,_,hRb,hRr,hRe⟩ := orient_endpoint_start S j b hbS
  have hRp : ∀ l, (R.walk l).IsPath := R.score_eq_edges_add_iff.mp
    (hRs.trans (hSs.trans (T.score_eq_edges_add_iff.mpr hp)))
  exact ⟨R,hRp,(hRr i hij).1.trans hSa,hRb⟩

lemma lift_two_spokes_at_distinct_slots {V : Type*} [Fintype V]
    {G : SimpleGraph V} {r : V} {k : ℕ}
    (a b : ({r}ᶜ : Set V)) (hab : a ≠ b)
    (ha : G.Adj r a.val) (hb : G.Adj r b.val)
    (hN : ∀ x, G.Adj r x → x=a.val ∨ x=b.val)
    (T : TrailFamily (G.induce ({r}ᶜ : Set V)) k)
    (hp : ∀ i, (T.walk i).IsPath) (i j : Fin k) (hij : i ≠ j)
    (hia : T.start i=a) (hjb : T.start j=b) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k := by
  classical
  let f : G.induce ({r}ᶜ : Set V) →g G :=
    { toFun := Subtype.val, map_rel' := fun h ↦ h }
  let P (l : Fin k) := (T.walk l).map f
  have hP (l : Fin k) : (P l).IsPath := Walk.map_isPath_of_injective Subtype.val_injective (hp l)
  have hrP (l : Fin k) : r ∉ (P l).support := by
    simp only [P,Walk.support_map,List.mem_map]
    rintro ⟨v,_,hv⟩
    exact v.property hv
  have hPe (l : Fin k) : (P l).toSubgraph.edgeSet=
      Sym2.map Subtype.val '' (T.walk l).toSubgraph.edgeSet := by
    simp only [P,Walk.toSubgraph_map,Subgraph.edgeSet_map]
    rfl
  have hPd : Pairwise fun l m ↦ Disjoint (P l).toSubgraph.edgeSet (P m).toSubgraph.edgeSet := by
    intro l m hlm
    rw [hPe,hPe,Set.disjoint_image_iff (Sym2.map.injective Subtype.val_injective)]
    exact T.disjoint hlm
  have hi : G.Adj r (T.start i).val := by rw [hia]; exact ha
  have hj : G.Adj r (T.start j).val := by rw [hjb]; exact hb
  let Q := Walk.cons hi (P i)
  let S := Walk.cons hj (P j)
  have hQ : Q.IsPath := (Walk.cons_isPath_iff _ _).mpr ⟨hP i,hrP i⟩
  have hS : S.IsPath := (Walk.cons_isPath_iff _ _).mpr ⟨hP j,hrP j⟩
  have hnew (l : Fin k) (v : V) : s(r,v) ∉ (P l).toSubgraph.edgeSet := by
    intro he
    exact hrP l ((P l).fst_mem_support_of_mem_edges ((P l).mem_edges_toSubgraph.mp he))
  have hene : s(r,a.val) ≠ s(r,b.val) := by
    intro he
    rcases Sym2.eq_iff.mp he with he|he
    · exact hab (Subtype.ext he.2)
    · exact hb.ne he.1
  let st (l : Fin k) : V := if l=i ∨ l=j then r else (T.start l).val
  have hwalk (l : Fin k) : ∃ q : G.Walk (st l) (T.finish l).val,
      q.IsPath ∧ q.toSubgraph.edgeSet=
        (if l=i then {s(r,a.val)} else ∅) ∪
        (if l=j then {s(r,b.val)} else ∅) ∪ (P l).toSubgraph.edgeSet := by
    by_cases hli : l=i
    · subst l
      rw [show st i=r by simp [st]]
      refine ⟨Q,hQ,?_⟩
      simp [Q,hia,hij]
    by_cases hlj : l=j
    · subst l
      rw [show st j=r by simp [st]]
      refine ⟨S,hS,?_⟩
      simp [S,hjb,hij.symm]
    · rw [show st l=(T.start l).val by simp [st,hli,hlj]]
      exact ⟨P l,hP l,by simp [hli,hlj]⟩
  choose q hq hqe using hwalk
  have heq (l : Fin k) (e : Sym2 V) : e ∈ (q l).toSubgraph.edgeSet ↔
      (l=i ∧ e=s(r,a.val)) ∨ (l=j ∧ e=s(r,b.val)) ∨ e ∈ (P l).toSubgraph.edgeSet := by
    rw [hqe]
    by_cases hli : l=i <;> by_cases hlj : l=j <;>
      simp [hli,hlj,hij,hij.symm]
  have hdis : Pairwise fun l m ↦ Disjoint (q l).toSubgraph.edgeSet (q m).toSubgraph.edgeSet := by
    intro l m hlm
    apply Set.disjoint_left.mpr
    intro e hel hem
    rcases (heq l e).mp hel with ⟨hli,rfl⟩|⟨hlj,rfl⟩|hel <;>
      rcases (heq m _).mp hem with ⟨hmi,he⟩|⟨hmj,he⟩|hem
    · exact hlm (hli.trans hmi.symm)
    · exact hene he
    · exact hnew m a.val hem
    · exact hene he.symm
    · exact hlm (hlj.trans hmj.symm)
    · exact hnew m b.val hem
    · exact hnew l a.val (he ▸ hel)
    · exact hnew l b.val (he ▸ hel)
    · exact Set.disjoint_left.mp (hPd hlm) hel hem
  have hcover (e : Sym2 V) : e ∈ G.edgeSet ↔ ∃ l, e ∈ (q l).toSubgraph.edgeSet := by
    constructor
    · intro he
      induction e using Sym2.ind with
      | h x y =>
        by_cases hx : x=r
        · subst x
          rcases hN y he with hya|hyb
          · exact ⟨i,(heq i _).mpr (Or.inl ⟨rfl,by rw [hya]⟩)⟩
          · exact ⟨j,(heq j _).mpr (Or.inr (Or.inl ⟨rfl,by rw [hyb]⟩))⟩
        by_cases hy : y=r
        · subst y
          rcases hN x he.symm with hxa|hxb
          · exact ⟨i,(heq i _).mpr (Or.inl ⟨rfl,by rw [hxa]; exact Sym2.eq_swap⟩)⟩
          · exact ⟨j,(heq j _).mpr (Or.inr (Or.inl ⟨rfl,by rw [hxb]; exact Sym2.eq_swap⟩))⟩
        · have hcore : (G.induce ({r}ᶜ : Set V)).Adj ⟨x,hx⟩ ⟨y,hy⟩ := he
          obtain ⟨l,hl⟩ := (T.cover s(⟨x,hx⟩,⟨y,hy⟩)).mp hcore
          refine ⟨l,(heq l _).mpr (Or.inr (Or.inr ?_))⟩
          rw [hPe]
          exact ⟨_,hl,rfl⟩
    · rintro ⟨l,hl⟩
      exact (q l).toSubgraph.edgeSet_subset hl
  let U : TrailFamily G k := ⟨st,(fun l ↦ (T.finish l).val),q,
    (fun l ↦ (hq l).isTrail),hdis,hcover⟩
  exact MatchingAppend.path_family_partition U hq

end Erdos583GeneralTwoSpokeLiftDevelopment
