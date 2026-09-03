import Submission.AdjacentEndpointUnpairing

/-! Lifting a normal core path family over a fresh degree-two vertex when
its two neighbors belong to different endpoint-owner classes. -/
namespace Erdos583TwoSpokeSeparatedLiftDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.NormalTrailSystem Erdos583Work.TrailNormalization
open Erdos583Work.RootedTailSystem Erdos583Work.SingletonRotation
open Erdos583Work.QuotaTrails
open Erdos583AdjacentEndpointUnpairingDevelopment
open scoped Classical
set_option maxHeartbeats 2600000
set_option Elab.async false

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {r : V} {k : ℕ}

lemma orient_separated_starts {W : Type*} [Fintype W] {H : SimpleGraph W}
    (T : NormalTrailSystem H k) (hp : ∀ i, (T.walk i).IsPath)
    (a b : W) (hsep : owner T a ≠ owner T b) :
    ∃ R : NormalTrailSystem H k, (∀ i, (R.walk i).IsPath) ∧
      ∃ i j : Fin k, i ≠ j ∧ R.start i=a ∧ R.start j=b := by
  let i := owner T a
  let j := owner T b
  obtain ⟨S,hSs,hSa,hSr,hSe⟩ := orient_receiver T i a (owner_spec T a)
  have hb : b=S.start j ∨ b=S.finish j := by
    obtain ⟨hja,hjb⟩ := hSr j hsep.symm
    rw [hja,hjb]
    exact owner_spec T b
  obtain ⟨R,hRs,hRb,hRr,hRe⟩ := orient_receiver S j b hb
  have hRp : ∀ l, (R.walk l).IsPath := R.score_eq_edges_add_iff.mp
    (hRs.trans (hSs.trans (T.score_eq_edges_add_iff.mpr hp)))
  exact ⟨R,hRp,i,j,hsep,(hRr i hsep).1.trans hSa,hRb⟩

lemma lift_two_spokes_separated
    (a b : ({r}ᶜ : Set V)) (ha : G.Adj r a.val) (hb : G.Adj r b.val)
    (hN : ∀ x, G.Adj r x → x=a.val ∨ x=b.val)
    (T : NormalTrailSystem (G.induce ({r}ᶜ : Set V)) k)
    (hp : ∀ i, (T.walk i).IsPath) (hsep : owner T a ≠ owner T b) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k := by
  classical
  obtain ⟨R,hR,i,j,hij,hia,hjb⟩ := orient_separated_starts T hp a b hsep
  have hab : a ≠ b := by intro he; exact hsep (congrArg (owner T) he)
  let f : G.induce ({r}ᶜ : Set V) →g G :=
    { toFun := Subtype.val, map_rel' := fun h ↦ h }
  let P (l : Fin k) := (R.walk l).map f
  have hP (l : Fin k) : (P l).IsPath := Walk.map_isPath_of_injective Subtype.val_injective (hR l)
  have hrP (l : Fin k) : r ∉ (P l).support := by
    simp only [P,Walk.support_map,List.mem_map]
    rintro ⟨v,_,hv⟩
    exact v.property hv
  have hPe (l : Fin k) : (P l).toSubgraph.edgeSet=
      Sym2.map Subtype.val '' (R.walk l).toSubgraph.edgeSet := by
    simp only [P,Walk.toSubgraph_map,Subgraph.edgeSet_map]
    rfl
  have hPd : Pairwise fun l m ↦ Disjoint (P l).toSubgraph.edgeSet (P m).toSubgraph.edgeSet := by
    intro l m hlm
    rw [hPe,hPe,Set.disjoint_image_iff (Sym2.map.injective Subtype.val_injective)]
    exact R.disjoint hlm
  have hi : G.Adj r (R.start i).val := by rw [hia]; exact ha
  have hj : G.Adj r (R.start j).val := by rw [hjb]; exact hb
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
  let st (l : Fin k) : V := if l=i ∨ l=j then r else (R.start l).val
  have hwalk (l : Fin k) : ∃ q : G.Walk (st l) (R.finish l).val,
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
    · rw [show st l=(R.start l).val by simp [st,hli,hlj]]
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
          obtain ⟨l,hl⟩ := (R.cover s(⟨x,hx⟩,⟨y,hy⟩)).mp hcore
          refine ⟨l,(heq l _).mpr (Or.inr (Or.inr ?_))⟩
          rw [hPe]
          exact ⟨_,hl,rfl⟩
    · rintro ⟨l,hl⟩
      exact (q l).toSubgraph.edgeSet_subset hl
  let U : TrailFamily G k := ⟨st,(fun l ↦ (R.finish l).val),q,
    (fun l ↦ (hq l).isTrail),hdis,hcover⟩
  exact MatchingAppend.path_family_partition U hq

end Erdos583TwoSpokeSeparatedLiftDevelopment
