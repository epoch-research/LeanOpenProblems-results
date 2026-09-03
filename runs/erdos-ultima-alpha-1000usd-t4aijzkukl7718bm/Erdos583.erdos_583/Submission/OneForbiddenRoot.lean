import Submission.MultiDefectForestImprovement

/-! Forest improvement while retaining one prescribed inactive label.
This is an exchange lemma, not a general endpoint-marking theorem. -/
namespace Erdos583OneForbiddenRootDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery
open Erdos583Work.DistinctTails
open Erdos583MultiDefectForestImprovementDevelopment
open scoped Classical
set_option maxHeartbeats 1800000
set_option Elab.async false

lemma tree_leaf_away {V : Type*} [Fintype V] [Nontrivial V] {G : SimpleGraph V}
    (hG : G.IsTree) (a : V) : ∃ b, b ≠ a ∧ G.degree b=1 := by
  classical
  by_contra hn
  have hpos (x : V) : 0 < G.degree x := by
    have hp := hG.isConnected.preconnected.minDegree_pos_of_nontrivial
    exact hp.trans_le (G.minDegree_le_degree x)
  have hb (x : V) (hx : x ≠ a) : 2 ≤ G.degree x := by
    have hh := hpos x
    have hne : G.degree x ≠ 1 := fun hd ↦ hn ⟨x,hx,hd⟩
    omega
  have hsum : (∑ _x : V, (2 : ℕ)) ≤ ∑ x : V, (G.degree x+(if x=a then 1 else 0)) := by
    apply Finset.sum_le_sum
    intro x _
    by_cases hx : x=a
    · subst x
      have hh := hpos a
      simp only [↓reduceIte]
      omega
    · simpa only [hx,↓reduceIte,add_zero] using hb x hx
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte,
    Finset.sum_const,Finset.card_univ,smul_eq_mul] at hsum
  have he := hG.card_edgeFinset
  have hd := G.sum_degrees_eq_twice_card_edges
  omega


lemma cycle_of_two_successors_except_one {V : Type*} [Fintype V] (G : SimpleGraph V)
    (Z : Set V) (a : V) (W : V → Prop)
    (hW : ∀ x, W x → x ∈ Z ∧ x ≠ a) (hw : ∃ r, W r)
    (hnext : ∀ r, W r → ∃ x y, x ≠ y ∧ G.Adj r x ∧ G.Adj r y ∧
      x ∈ Z ∧ y ∈ Z ∧ (W x ∨ x=a) ∧ (W y ∨ y=a)) :
    ¬(G.induce Z).IsAcyclic := by
  classical
  intro hf
  let S : Set Z := {x | W x.val ∨ x.val=a}
  let H := (G.induce Z).induce S
  obtain ⟨r,hr⟩ := hw
  obtain ⟨x,y,hxy,hrx,hry,hxZ,hyZ,hx,hy⟩ := hnext r hr
  let r' : S := ⟨⟨r,(hW r hr).1⟩,Or.inl hr⟩
  let x' : S := ⟨⟨x,hxZ⟩,hx⟩
  have hrx' : H.Adj r' x' := hrx
  let C := H.connectedComponentMk r'
  let rC : C := ⟨r',rfl⟩
  let xC : C := ⟨x',(C.mem_supp_congr_adj hrx').mp rfl⟩
  letI : Nontrivial C := ⟨⟨rC,xC,fun hh ↦ hrx'.ne (congrArg Subtype.val hh)⟩⟩
  have ht := (hf.induce S).isTree_connectedComponent C
  have hleaf : ∃ b : C, b.val.val.val ≠ a ∧ C.toSimpleGraph.degree b=1 := by
    by_cases haC : ∃ z : C, z.val.val.val=a
    · obtain ⟨z,hz⟩ := haC
      obtain ⟨b,hbz,hb⟩ := tree_leaf_away ht z
      refine ⟨b,?_,hb⟩
      intro hba
      exact hbz (Subtype.ext (Subtype.ext (Subtype.ext (hba.trans hz.symm))))
    · obtain ⟨b,hb⟩ := ht.exists_vert_degree_one_of_nontrivial
      exact ⟨b,fun hba ↦ haC ⟨b,hba⟩,hb⟩
  obtain ⟨b,hba,hb⟩ := hleaf
  have hbW : W b.val.val.val := b.val.property.resolve_right hba
  obtain ⟨u,v,huv,hbu,hbv,huZ,hvZ,hu,hv⟩ := hnext b.val.val.val hbW
  let u' : S := ⟨⟨u,huZ⟩,hu⟩
  let v' : S := ⟨⟨v,hvZ⟩,hv⟩
  have hbu' : H.Adj b.val u' := hbu
  have hbv' : H.Adj b.val v' := hbv
  let uC : C := ⟨u',C.mem_supp_of_adj_mem_supp b.property hbu'⟩
  let vC : C := ⟨v',C.mem_supp_of_adj_mem_supp b.property hbv'⟩
  obtain ⟨w,_,hw⟩ := degree_eq_one_iff_existsUnique_adj.mp hb
  have he : uC=vC := (hw uC hbu').trans (hw vC hbv').symm
  exact huv (congrArg (fun z : C ↦ z.val.val.val) he)

/-- A movable pair starting away from a prescribed zero label can gain one
unit of score without ever leaving that label active in the output. -/
lemma improve_zero_forest_avoiding {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (c : V → ℕ) (r a : V)
    (hquota : ∀ v, T.quota v=c v+2*(if r=v then 1 else 0))
    (hroot : HasRoot T r) (hr0 : c r=0) (hra : r ≠ a)
    (hforest : (G.induce {x | c x=0}).IsAcyclic) :
    ∃ r' : V, r' ≠ a ∧ c r'=0 ∧ ∃ P : TrailFamily G k,
      (∀ v, P.quota v=c v+2*(if r'=v then 1 else 0)) ∧ P.score=T.score+1 := by
  classical
  by_contra hn
  let W (s : V) : Prop := s ≠ a ∧ c s=0 ∧ ∃ U : TrailFamily G k, U.score=T.score ∧
    (∀ v, U.quota v=c v+2*(if s=v then 1 else 0)) ∧ HasRoot U s
  have hw : ∃ s, W s := ⟨r,hra,hr0,T,rfl,hquota,hroot⟩
  have hnext (s : V) (hs : W s) : ∃ x y, x ≠ y ∧ G.Adj s x ∧ G.Adj s y ∧
      c x=0 ∧ c y=0 ∧ (W x ∨ x=a) ∧ (W y ∨ y=a) := by
    obtain ⟨hsa,hs0,U,hUs,hUq,A,R,ρ,hρ,hRn⟩ := hs
    obtain ⟨B,_,x,y,hxy,hsx,hsy,hxB,hyB,hEx,hEy⟩ := R.two_root_exposures ρ hρ hRn
    have hreach (z : V) (hzB : z ∉ B) (hE : ExposedRoot U s A B z) :
        c z=0 ∧ (W z ∨ z=a) := by
      have hz0 : c z=0 := by
        by_contra hzne
        have hpos : 0 < U.quota z := by rw [hUq]; omega
        obtain ⟨P,hPq,hPs⟩ := exposedRoot_improve_positive hE hzB hpos
        exact hn ⟨s,hsa,hs0,P,fun v ↦ (hPq v).trans (hUq v),by omega⟩
      refine ⟨hz0,?_⟩
      by_cases hza : z=a
      · exact Or.inr hza
      have hpos : 2 ≤ U.quota s := by rw [hUq]; simp
      obtain ⟨P,hPq,hP⟩ := exposedRoot_move_pair_score_or_root hE hpos
      have hnewq (v : V) : P.quota v=c v+2*(if z=v then 1 else 0) := by
        have hh := hPq v
        rw [hUq] at hh
        omega
      rcases hP with hP | ⟨hPs,hPr⟩
      · exact (hn ⟨z,hza,hz0,P,hnewq,by omega⟩).elim
      · exact Or.inl ⟨hza,hz0,P,hPs.trans hUs,hnewq,hPr⟩
    obtain ⟨hx0,hWx⟩ := hreach x hxB hEx
    obtain ⟨hy0,hWy⟩ := hreach y hyB hEy
    exact ⟨x,y,hxy,hsx,hsy,hx0,hy0,hWx,hWy⟩
  exact cycle_of_two_successors_except_one G {x | c x=0} a W
    (fun _ h ↦ ⟨h.2.1,h.1⟩) hw hnext hforest

lemma normalize_zero_forest_avoiding {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (c : V → ℕ) (r a : V)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hquota : ∀ v, T.quota v=c v+2*(if r=v then 1 else 0))
    (hroot : HasRoot T r) (hr0 : c r=0) (hra : r ≠ a)
    (hforest : (G.induce {x | c x=0}).IsAcyclic) :
    ∃ r' : V, r' ≠ a ∧ c r'=0 ∧ ∃ P : TrailFamily G k,
      (∀ v, P.quota v=c v+2*(if r'=v then 1 else 0)) ∧ ∀ i, (P.walk i).IsPath := by
  obtain ⟨s,hsa,hs0,P,hPq,hPs⟩ := improve_zero_forest_avoiding T c r a hquota hroot hr0 hra hforest
  exact ⟨s,hsa,hs0,P,hPq,P.score_eq_edges_add_iff.mp (by omega)⟩

lemma restore_edge_tail_zero {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    {u v : V} (h : G.Adj v u)
    (T : TrailFamily (G.deleteEdges {s(v,u)}) k) (hp : ∀ i, (T.walk i).IsPath)
    (hu : T.quota u=1) (hv : T.quota v=1) (hbound : ∀ x, T.quota x ≤ 2)
    (hf : (G.induce {x | T.quota x=0 ∨ x=u ∨ x=v}).IsAcyclic) :
    ∃ P : TrailFamily G k, (∀ i, (P.walk i).IsPath) ∧ (∀ x, P.quota x ≤ 2) ∧ P.quota u=0 ∧
      ∀ x, 0 < T.quota x → x ≠ u → x ≠ v → P.quota x=T.quota x := by
  classical
  obtain ⟨i,hi⟩ := DeletionEndpoint.endpoint_of_positive_quota T (v := u) (by omega)
  have hc : G.edgeSet=insert s(v,u) (G.deleteEdges {s(v,u)}).edgeSet := by
    rw [edgeSet_deleteEdges,Set.insert_diff_singleton]
    exact (Set.insert_eq_of_mem (show s(v,u) ∈ G.edgeSet from h)).symm
  obtain ⟨U,hs,hq,_,hr⟩ := DeletionEndpoint.append_new_edge_tracked
    (G.deleteEdges_le _) T hp i hi h (by simp) hc
  let b (x : V) : ℕ := if x=u ∨ x=v then 0 else T.quota x
  have hquota (x : V) : U.quota x=b x+2*(if v=x then 1 else 0) := by
    have hh := hq x
    dsimp only [b]
    by_cases hxu : x=u
    · subst x
      simp only [hu,h.ne,h.ne.symm,↓reduceIte,true_or,mul_zero,add_zero] at hh ⊢
      omega
    by_cases hxv : x=v
    · subst x
      simp only [hv,h.ne,h.ne.symm,↓reduceIte,or_true,mul_one,zero_add,add_zero] at hh ⊢
      omega
    · simp only [hxu,hxv,Ne.symm hxu,Ne.symm hxv,or_self,↓reduceIte,mul_zero,add_zero] at hh ⊢
      exact hh
  have hbb (x : V) : b x ≤ 2 := by dsimp [b]; split_ifs; omega; exact hbound x
  have hzero : {x | b x=0}={x | T.quota x=0 ∨ x=u ∨ x=v} := by
    ext x
    simp only [Set.mem_setOf_eq,b]
    split_ifs <;> aesop
  have hrootzero : b v=0 := by simp [b]
  have hex : ∃ r : V, r ≠ u ∧ b r=0 ∧ ∃ P : TrailFamily G k,
      (∀ x, P.quota x=b x+2*(if r=x then 1 else 0)) ∧ ∀ i, (P.walk i).IsPath := by
    by_cases hpaths : ∀ i, (U.walk i).IsPath
    · exact ⟨v,h.ne,hrootzero,U,hquota,hpaths⟩
    · have hscore : U.score+1=G.edgeSet.ncard+k := by
        have hupper := U.score_le_edges_add
        have hne := U.score_eq_edges_add_iff.not.mpr hpaths
        omega
      exact normalize_zero_forest_avoiding U b v u hscore hquota
        (hr hpaths) hrootzero h.ne (by rwa [hzero])
  obtain ⟨r,hru,hr0,P,hPq,hP⟩ := hex
  refine ⟨P,hP,?_,?_,?_⟩
  · intro x
    rw [hPq]
    by_cases hrx : r=x
    · subst x; simp [hr0]
    · simpa [hrx] using hbb x
  · simp [hPq,b,hru]
  · intro x hx hxu hxv
    have hbx : b x=T.quota x := by simp [b,hxu,hxv]
    have hrx : r ≠ x := by rintro rfl; rw [hbx] at hr0; omega
    simp [hPq,hbx,hrx]

end Erdos583OneForbiddenRootDevelopment
