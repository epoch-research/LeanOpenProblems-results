import Submission.OneForbiddenRoot

/-! Movable-pair exchanges avoiding a connected zero subtree.
These are conditional exchange lemmas, not a Gallai decomposition theorem. -/
namespace Erdos583ForbiddenSubtreeDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery
open Erdos583MultiDefectForestImprovementDevelopment
open Erdos583OneForbiddenRootDevelopment
open scoped Classical
set_option maxHeartbeats 1800000
set_option Elab.async false

lemma tree_leaf_outside_preconnected {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : G.IsTree) (A : Set V) (hA : (G.induce A).Preconnected)
    (ha : A.Nonempty) (hr : Aᶜ.Nonempty) : ∃ b, b ∉ A ∧ G.degree b=1 := by
  classical
  obtain ⟨a,ha⟩ := ha
  let S := Finset.univ.filter fun x ↦ x ∉ A
  have hS : S.Nonempty := by
    obtain ⟨r,hr⟩ := hr
    exact ⟨r,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr⟩⟩
  obtain ⟨b,hb,hmax⟩ := S.exists_max_image (fun x ↦ G.dist a x) hS
  have hbA : b ∉ A := (Finset.mem_filter.mp hb).2
  obtain ⟨p,hp,hpl⟩ := (hG.isConnected a b).exists_path_of_dist
  have hneighbor (z : V) (hbz : G.Adj b z) : z=p.penultimate := by
    obtain ⟨q,hq,hql⟩ := (hG.isConnected a z).exists_path_of_dist
    have hzp : z ∈ p.support := by
      by_cases hzA : z ∈ A
      · obtain ⟨t,ht,_⟩ := (hA ⟨a,ha⟩ ⟨z,hzA⟩).exists_path_of_dist
        let Q : G.Walk a z := t.map (Embedding.induce A).toHom
        have hQ : Q.IsPath := Walk.map_isPath_of_injective Subtype.val_injective ht
        have hbQ : b ∉ Q.support := by
          intro hh
          rw [Walk.support_map] at hh
          obtain ⟨x,_,hx⟩ := List.mem_map.mp hh
          exact hbA (hx ▸ x.property)
        exact hG.IsAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath hp hQ hbz hbQ
      · by_contra hzp
        have he : q=p.concat hbz :=
          Subtype.mk.inj (hG.IsAcyclic.path_unique ⟨q,hq⟩ ⟨_,hp.concat hzp hbz⟩)
        have hl := congrArg Walk.length he
        rw [Walk.length_concat,hpl,hql] at hl
        have hbnd := hmax z (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hzA⟩)
        omega
    have he : p=q.concat hbz.symm := hG.IsAcyclic.path_concat hq hp hbz.symm hzp
    rw [he,Walk.penultimate_concat]
  have hab : a ≠ b := fun he ↦ hbA (he ▸ ha)
  have hpb : G.Adj b p.penultimate := (p.adj_penultimate (Walk.not_nil_of_ne hab)).symm
  exact ⟨b,hbA,degree_eq_one_iff_existsUnique_adj.mpr ⟨p.penultimate,hpb,hneighbor⟩⟩


lemma cycle_of_two_successors_except_preconnected {V : Type*} [Fintype V]
    (G : SimpleGraph V) (A : Set V) (hA : (G.induce A).Preconnected)
    (W : V → Prop) (hWA : ∀ x, W x → x ∉ A) (hw : ∃ r, W r)
    (hnext : ∀ r, W r → ∃ x y, x ≠ y ∧ G.Adj r x ∧ G.Adj r y ∧
      (W x ∨ x ∈ A) ∧ (W y ∨ y ∈ A)) : ¬G.IsAcyclic := by
  classical
  intro hf
  obtain ⟨r,hr⟩ := hw
  by_cases hreachA : ∃ a ∈ A, G.Reachable a r
  · obtain ⟨a,ha,har⟩ := hreachA
    let S := Finset.univ.filter fun x ↦ W x ∧ G.Reachable a x
    have hS : S.Nonempty := ⟨r,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr,har⟩⟩
    obtain ⟨b,hb,hmax⟩ := S.exists_max_image (fun x ↦ G.dist a x) hS
    obtain ⟨hbW,hab⟩ := (Finset.mem_filter.mp hb).2
    obtain ⟨p,hp,hpl⟩ := hab.exists_path_of_dist
    have hneighbor (z : V) (hbz : G.Adj b z) (hz : W z ∨ z ∈ A) : z=p.penultimate := by
      obtain ⟨q,hq,hql⟩ := (hab.trans hbz.reachable).exists_path_of_dist
      have hzp : z ∈ p.support := by
        rcases hz with hzW|hzA
        · by_contra hzp
          have he : q=p.concat hbz :=
            Subtype.mk.inj (hf.path_unique ⟨q,hq⟩ ⟨_,hp.concat hzp hbz⟩)
          have hl := congrArg Walk.length he
          rw [Walk.length_concat,hpl,hql] at hl
          have hbnd := hmax z (Finset.mem_filter.mpr
            ⟨Finset.mem_univ _,hzW,hab.trans hbz.reachable⟩)
          omega
        · obtain ⟨t,ht,_⟩ := (hA ⟨a,ha⟩ ⟨z,hzA⟩).exists_path_of_dist
          let Q : G.Walk a z := t.map (Embedding.induce A).toHom
          have hQ : Q.IsPath := Walk.map_isPath_of_injective Subtype.val_injective ht
          have hbQ : b ∉ Q.support := by
            intro hh
            rw [Walk.support_map] at hh
            obtain ⟨x,_,hx⟩ := List.mem_map.mp hh
            exact hWA b hbW (hx ▸ x.property)
          exact hf.mem_support_of_ne_mem_support_of_adj_of_isPath hp hQ hbz hbQ
      have he : p=q.concat hbz.symm := hf.path_concat hq hp hbz.symm hzp
      rw [he,Walk.penultimate_concat]
    obtain ⟨x,y,hxy,hbx,hby,hx,hy⟩ := hnext b hbW
    exact hxy ((hneighbor x hbx hx).trans (hneighbor y hby hy).symm)
  · let U (x : V) : Prop := W x ∧ G.Reachable r x
    have hU : ∃ x, U x := ⟨r,hr,.rfl⟩
    have hstep (b : V) (hb : U b) : ∃ x y, x ≠ y ∧ G.Adj b x ∧ G.Adj b y ∧
        x ∈ (Set.univ : Set V) ∧ y ∈ (Set.univ : Set V) ∧ U x ∧ U y := by
      obtain ⟨x,y,hxy,hbx,hby,hx,hy⟩ := hnext b hb.1
      have hvertex (z : V) (hbz : G.Adj b z) (hz : W z ∨ z ∈ A) : U z := by
        have hrz : G.Reachable r z := hb.2.trans hbz.reachable
        refine ⟨?_,hrz⟩
        exact hz.resolve_right (fun hzA ↦ hreachA ⟨z,hzA,hrz.symm⟩)
      exact ⟨x,y,hxy,hbx,hby,Set.mem_univ _,Set.mem_univ _,hvertex x hbx hx,hvertex y hby hy⟩
    exact Erdos583Work.DistinctTails.cycle_of_two_zero_successors G Set.univ U hU hstep (hf.induce Set.univ)


lemma cycle_of_two_successors_except_subtree {V : Type*} [Fintype V]
    (G : SimpleGraph V) (Z A : Set V) (hAZ : A ⊆ Z)
    (hA : (G.induce A).Preconnected) (W : V → Prop)
    (hW : ∀ x, W x → x ∈ Z ∧ x ∉ A) (hw : ∃ r, W r)
    (hnext : ∀ r, W r → ∃ x y, x ≠ y ∧ G.Adj r x ∧ G.Adj r y ∧
      x ∈ Z ∧ y ∈ Z ∧ (W x ∨ x ∈ A) ∧ (W y ∨ y ∈ A)) :
    ¬(G.induce Z).IsAcyclic := by
  classical
  let A' : Set Z := {x | x.val ∈ A}
  let f : (G.induce A) →g ((G.induce Z).induce A') :=
    { toFun := fun x ↦ ⟨⟨x.val,hAZ x.property⟩,x.property⟩
      map_rel' := fun h ↦ h }
  have hA' : ((G.induce Z).induce A').Preconnected := by
    intro x y
    exact (hA ⟨x.val.val,x.property⟩ ⟨y.val.val,y.property⟩).map f
  apply cycle_of_two_successors_except_preconnected (G.induce Z) A' hA'
    (fun x ↦ W x.val) (fun x hx ↦ (hW x.val hx).2)
    (by obtain ⟨r,hr⟩ := hw; exact ⟨⟨r,(hW r hr).1⟩,hr⟩)
  intro r hr
  obtain ⟨x,y,hxy,hrx,hry,hxZ,hyZ,hx,hy⟩ := hnext r.val hr
  exact ⟨⟨x,hxZ⟩,⟨y,hyZ⟩,fun he ↦ hxy (congrArg Subtype.val he),hrx,hry,hx,hy⟩

/-- An endpoint pair can improve the score while avoiding an entire connected
subtree of baseline-zero labels. Other defects need not disappear. -/
lemma improve_zero_forest_avoiding_subtree {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k) (c : V → ℕ) (r : V) (A : Set V)
    (hquota : ∀ v, T.quota v=c v+2*(if r=v then 1 else 0))
    (hroot : HasRoot T r) (hr0 : c r=0) (hra : r ∉ A)
    (hAZ : A ⊆ {x | c x=0}) (hA : (G.induce A).Preconnected)
    (hforest : (G.induce {x | c x=0}).IsAcyclic) :
    ∃ r' : V, r' ∉ A ∧ c r'=0 ∧ ∃ P : TrailFamily G k,
      (∀ v, P.quota v=c v+2*(if r'=v then 1 else 0)) ∧ P.score=T.score+1 := by
  classical
  by_contra hn
  let W (s : V) : Prop := s ∉ A ∧ c s=0 ∧ ∃ U : TrailFamily G k, U.score=T.score ∧
    (∀ v, U.quota v=c v+2*(if s=v then 1 else 0)) ∧ HasRoot U s
  have hw : ∃ s, W s := ⟨r,hra,hr0,T,rfl,hquota,hroot⟩
  have hnext (s : V) (hs : W s) : ∃ x y, x ≠ y ∧ G.Adj s x ∧ G.Adj s y ∧
      c x=0 ∧ c y=0 ∧ (W x ∨ x ∈ A) ∧ (W y ∨ y ∈ A) := by
    obtain ⟨hsa,hs0,U,hUs,hUq,B,R,ρ,hρ,hRn⟩ := hs
    obtain ⟨C,_,x,y,hxy,hsx,hsy,hxC,hyC,hEx,hEy⟩ := R.two_root_exposures ρ hρ hRn
    have hreach (z : V) (hzC : z ∉ C) (hE : ExposedRoot U s B C z) :
        c z=0 ∧ (W z ∨ z ∈ A) := by
      have hz0 : c z=0 := by
        by_contra hzne
        have hpos : 0 < U.quota z := by rw [hUq]; omega
        obtain ⟨P,hPq,hPs⟩ := exposedRoot_improve_positive hE hzC hpos
        exact hn ⟨s,hsa,hs0,P,fun v ↦ (hPq v).trans (hUq v),by omega⟩
      refine ⟨hz0,?_⟩
      by_cases hza : z ∈ A
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
    obtain ⟨hx0,hWx⟩ := hreach x hxC hEx
    obtain ⟨hy0,hWy⟩ := hreach y hyC hEy
    exact ⟨x,y,hxy,hsx,hsy,hx0,hy0,hWx,hWy⟩
  exact cycle_of_two_successors_except_subtree G {x | c x=0} A hAZ hA W
    (fun _ h ↦ ⟨h.2.1,h.1⟩) hw hnext hforest

lemma normalize_zero_forest_avoiding_subtree {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k) (c : V → ℕ) (r : V) (A : Set V)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hquota : ∀ v, T.quota v=c v+2*(if r=v then 1 else 0))
    (hroot : HasRoot T r) (hr0 : c r=0) (hra : r ∉ A)
    (hAZ : A ⊆ {x | c x=0}) (hA : (G.induce A).Preconnected)
    (hforest : (G.induce {x | c x=0}).IsAcyclic) :
    ∃ r' : V, r' ∉ A ∧ c r'=0 ∧ ∃ P : TrailFamily G k,
      (∀ v, P.quota v=c v+2*(if r'=v then 1 else 0)) ∧ ∀ i, (P.walk i).IsPath := by
  obtain ⟨s,hsa,hs0,P,hPq,hPs⟩ :=
    improve_zero_forest_avoiding_subtree T c r A hquota hroot hr0 hra hAZ hA hforest
  exact ⟨s,hsa,hs0,P,hPq,P.score_eq_edges_add_iff.mp (by omega)⟩


/-- Restore an even-even edge while keeping a specified connected subset of
baseline zeros inactive. The new head must lie outside the protected set. -/
lemma restore_edge_avoiding_subtree {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    {u v : V} (h : G.Adj v u)
    (T : TrailFamily (G.deleteEdges {s(v,u)}) k) (hp : ∀ i, (T.walk i).IsPath)
    (hu : T.quota u=1) (hv : T.quota v=1) (hbound : ∀ x, T.quota x ≤ 2)
    (A : Set V) (hvA : v ∉ A)
    (hAZ : A ⊆ {x | T.quota x=0 ∨ x=u ∨ x=v})
    (hA : (G.induce A).Preconnected)
    (hf : (G.induce {x | T.quota x=0 ∨ x=u ∨ x=v}).IsAcyclic) :
    ∃ P : TrailFamily G k, (∀ i, (P.walk i).IsPath) ∧ (∀ x, P.quota x ≤ 2) ∧ (∀ x ∈ A, P.quota x=0) ∧
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
  have hex : ∃ r : V, r ∉ A ∧ b r=0 ∧ ∃ P : TrailFamily G k,
      (∀ x, P.quota x=b x+2*(if r=x then 1 else 0)) ∧ ∀ i, (P.walk i).IsPath := by
    by_cases hpaths : ∀ i, (U.walk i).IsPath
    · exact ⟨v,hvA,hrootzero,U,hquota,hpaths⟩
    · have hscore : U.score+1=G.edgeSet.ncard+k := by
        have hupper := U.score_le_edges_add
        have hne := U.score_eq_edges_add_iff.not.mpr hpaths
        omega
      exact normalize_zero_forest_avoiding_subtree U b v A hscore hquota
        (hr hpaths) hrootzero hvA (by rwa [hzero]) hA (by rwa [hzero])
  obtain ⟨r,hrA,hr0,P,hPq,hP⟩ := hex
  refine ⟨P,hP,?_,?_,?_⟩
  · intro x
    rw [hPq]
    by_cases hrx : r=x
    · subst x; simp [hr0]
    · simpa [hrx] using hbb x
  · intro x hx
    have hbx : b x=0 := by
      have hh := hAZ hx
      simpa only [←hzero,Set.mem_setOf_eq] using hh
    have hrx : r ≠ x := fun he ↦ hrA (he.symm ▸ hx)
    simp [hPq,hbx,hrx]
  · intro x hx hxu hxv
    have hbx : b x=T.quota x := by simp [b,hxu,hxv]
    have hrx : r ≠ x := by rintro rfl; rw [hbx] at hr0; omega
    simp [hPq,hbx,hrx]

end Erdos583ForbiddenSubtreeDevelopment
