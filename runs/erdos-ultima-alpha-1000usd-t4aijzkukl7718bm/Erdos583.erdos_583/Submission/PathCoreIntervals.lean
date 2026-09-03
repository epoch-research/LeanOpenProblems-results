import Submission.Work

/-! Exact core counts and contiguous core intervals of a simple path. -/
namespace Erdos583PathCoreIntervalsDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.BridgeGlue
open scoped Classical
set_option maxHeartbeats 1800000
set_option Elab.async false
variable {V : Type*} {G : SimpleGraph V} {a b u : V}

def coreVerts (P : G.Walk a b) (S : Set V) : Set V := P.toSubgraph.verts ∩ S

def coreEdges (P : G.Walk a b) (S : Set V) : Set (Sym2 V) :=
  P.toSubgraph.edgeSet ∩ (within G S).edgeSet

lemma mem_coreVerts (P : G.Walk a b) (S : Set V) (x : V) :
    x ∈ coreVerts P S ↔ x ∈ P.support ∧ x ∈ S := by
  simp only [coreVerts,Set.mem_inter_iff,Walk.mem_verts_toSubgraph]

lemma mem_coreEdges (P : G.Walk a b) (S : Set V) (x y : V) :
    s(x,y) ∈ coreEdges P S ↔ s(x,y) ∈ P.edges ∧ x ∈ S ∧ y ∈ S := by
  constructor
  · rintro ⟨he,hxy⟩
    exact ⟨P.mem_edges_toSubgraph.mp he,hxy.2⟩
  · rintro ⟨he,hx,hy⟩
    exact ⟨P.mem_edges_toSubgraph.mpr he,P.edges_subset_edgeSet he,hx,hy⟩

lemma coreVerts_nil (a : V) (S : Set V) :
    coreVerts (.nil : G.Walk a a) S=if a ∈ S then {a} else ∅ := by
  ext x
  simp only [mem_coreVerts,Walk.support_nil,List.mem_singleton]
  split_ifs with ha <;> simp_all

lemma coreEdges_nil (a : V) (S : Set V) :
    coreEdges (.nil : G.Walk a a) S=∅ := by
  ext e
  induction e using Sym2.ind with
  | h x y => simp [mem_coreEdges]

lemma coreVerts_cons (h : G.Adj a u) (Q : G.Walk u b) (S : Set V) :
    coreVerts (.cons h Q) S=if a ∈ S then insert a (coreVerts Q S) else coreVerts Q S := by
  ext x
  simp only [mem_coreVerts,Walk.support_cons,List.mem_cons]
  split_ifs with ha
  · simp only [Set.mem_insert_iff,mem_coreVerts]
    aesop
  · rw [mem_coreVerts]
    aesop

lemma coreEdges_cons (h : G.Adj a u) (Q : G.Walk u b) (S : Set V) :
    coreEdges (.cons h Q) S=
      if a ∈ S ∧ u ∈ S then insert s(a,u) (coreEdges Q S) else coreEdges Q S := by
  ext e
  induction e using Sym2.ind with
  | h x y =>
    simp only [mem_coreEdges,Walk.edges_cons,List.mem_cons]
    split_ifs with hau
    · simp only [Set.mem_insert_iff,mem_coreEdges]
      constructor
      · rintro ⟨he,hx,hy⟩
        exact he.elim Or.inl (fun he ↦ Or.inr ⟨he,hx,hy⟩)
      · rintro (he | ⟨he,hx,hy⟩)
        · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
          · exact ⟨Or.inl rfl,hau⟩
          · exact ⟨Or.inl Sym2.eq_swap,hau.2,hau.1⟩
        · exact ⟨Or.inr he,hx,hy⟩
    · rw [mem_coreEdges]
      constructor
      · rintro ⟨he,hx,hy⟩
        rcases he with he | he
        · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
          · exact (hau ⟨hx,hy⟩).elim
          · exact (hau ⟨hy,hx⟩).elim
        · exact ⟨he,hx,hy⟩
      · rintro ⟨he,hx,hy⟩
        exact ⟨Or.inr he,hx,hy⟩

lemma coreEdges_empty_of_coreVerts_empty (P : G.Walk a b) (S : Set V)
    (hv : coreVerts P S=∅) : coreEdges P S=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro e he
  induction e using Sym2.ind with
  | h x y =>
    obtain ⟨he,hx,_⟩ := (mem_coreEdges P S x y).mp he
    have hx' : x ∈ coreVerts P S := (mem_coreVerts P S x).mpr
      ⟨P.fst_mem_support_of_mem_edges he,hx⟩
    rw [hv] at hx'
    exact hx'

lemma coreVerts_cons_ncard [Fintype V] (h : G.Adj a u) (Q : G.Walk u b)
    (hp : (Walk.cons h Q).IsPath) (S : Set V) :
    (coreVerts (.cons h Q) S).ncard=(coreVerts Q S).ncard+(if a ∈ S then 1 else 0) := by
  have hnot : a ∉ coreVerts Q S := fun ha ↦
    ((Walk.cons_isPath_iff h Q).mp hp).2 ((mem_coreVerts Q S a).mp ha).1
  rw [coreVerts_cons]
  split_ifs <;> simp [Set.ncard_insert_of_notMem hnot]

lemma coreEdges_cons_ncard [Fintype V] (h : G.Adj a u) (Q : G.Walk u b)
    (hp : (Walk.cons h Q).IsPath) (S : Set V) :
    (coreEdges (.cons h Q) S).ncard=(coreEdges Q S).ncard+
      (if a ∈ S ∧ u ∈ S then 1 else 0) := by
  have hn : s(a,u) ∉ Q.edges := by
    have hh := hp.isTrail.edges_nodup
    rw [Walk.edges_cons,List.nodup_cons] at hh
    exact hh.1
  have hnot : s(a,u) ∉ coreEdges Q S := fun he ↦ hn ((mem_coreEdges Q S a u).mp he).1
  rw [coreEdges_cons]
  split_ifs <;> simp [Set.ncard_insert_of_notMem hnot]

lemma core_edge_bound [Fintype V] (P : G.Walk a b) (hp : P.IsPath) (S : Set V)
    (hS : (coreVerts P S).Nonempty) :
    (coreEdges P S).ncard+1 ≤ (coreVerts P S).ncard := by
  induction P with
  | @nil a =>
    have ha : a ∈ S := by
      obtain ⟨x,hx⟩ := hS
      obtain ⟨hx,ha⟩ := (mem_coreVerts _ _ _).mp hx
      have he : x=a := by simpa only [Walk.support_nil,List.mem_singleton] using hx
      exact he ▸ ha
    simp [coreEdges_nil,coreVerts_nil,ha]
  | @cons a u b h Q ih =>
    have hv := coreVerts_cons_ncard h Q hp S
    have he := coreEdges_cons_ncard h Q hp S
    by_cases hQ : (coreVerts Q S).Nonempty
    · have hb := ih hp.of_cons hQ
      by_cases ha : a ∈ S
      · simp only [ha,if_pos,true_and] at hv he
        split_ifs at he <;> omega
      · simp only [ha,false_and,if_false,add_zero] at hv he
        omega
    · have hQv := Set.not_nonempty_iff_eq_empty.mp hQ
      have hQe := coreEdges_empty_of_coreVerts_empty Q S hQv
      have hpos := (Set.ncard_pos (Set.toFinite _)).mpr hS
      rw [hQv,Set.ncard_empty] at hv
      rw [hQe,Set.ncard_empty] at he
      have hu : u ∉ S := fun hu ↦ hQ ⟨u,(mem_coreVerts Q S u).mpr ⟨Q.start_mem_support,hu⟩⟩
      simp only [hu,and_false,if_false,add_zero] at he
      omega

/-- Zero core deficit means that all core vertices occur in one interval. -/
lemma contiguous_of_core_count [Fintype V] (P : G.Walk a b) (hp : P.IsPath) (S : Set V)
    (hS : (coreVerts P S).Nonempty)
    (hcount : (coreEdges P S).ncard+1=(coreVerts P S).ncard) :
    ∃ u v, ∃ A : G.Walk a u, ∃ Q : G.Walk u v, ∃ B : G.Walk v b,
      P=A.append (Q.append B) ∧ Q.IsPath ∧ Q.toSubgraph.verts=coreVerts P S ∧
      (∀ x ∈ A.support, x ∈ S → x=u) ∧ (∀ x ∈ B.support, x ∈ S → x=v) := by
  induction P with
  | @nil a =>
    have ha : a ∈ S := by
      obtain ⟨x,hx⟩ := hS
      obtain ⟨hx,ha⟩ := (mem_coreVerts _ _ _).mp hx
      have he : x=a := by simpa only [Walk.support_nil,List.mem_singleton] using hx
      exact he ▸ ha
    refine ⟨a,a,.nil,.nil,.nil,rfl,Walk.IsPath.nil,?_,?_,?_⟩
    · simp [coreVerts_nil,ha]
    · intro x hx _; simpa using hx
    · intro x hx _; simpa using hx
  | @cons a w b h P ih =>
    have hvc := coreVerts_cons_ncard h P hp S
    have hec := coreEdges_cons_ncard h P hp S
    by_cases hP : (coreVerts P S).Nonempty
    · have hbound := core_edge_bound P hp.of_cons S hP
      by_cases ha : a ∈ S
      · have hw : w ∈ S := by
          by_contra hw
          simp only [ha,hw,true_and,if_pos,if_false] at hvc hec
          omega
        have hcountP : (coreEdges P S).ncard+1=(coreVerts P S).ncard := by
          simp only [ha,hw,and_self,if_pos] at hvc hec
          omega
        obtain ⟨u,v,A,Q,B,hform,hQ,hQv,hA,hB⟩ := ih hp.of_cons hP hcountP
        have hwu : w=u := hA w A.start_mem_support hw
        subst u
        have hAnil : A=Walk.nil := (Walk.isPath_iff_eq_nil A).mp
          ((hform ▸ hp.of_cons).of_append_left)
        subst A
        simp only [Walk.nil_append] at hform
        have hnew : ((Walk.cons h Q).append B).IsPath := by
          simpa only [Walk.cons_append,←hform] using hp
        refine ⟨a,v,.nil,Walk.cons h Q,B,?_,hnew.of_append_left,?_,?_,hB⟩
        · simp only [Walk.nil_append,Walk.cons_append,hform]
        · have hcv : (Walk.cons h Q).toSubgraph.verts=insert a Q.toSubgraph.verts := by
            ext x
            simp only [Walk.mem_verts_toSubgraph,Walk.support_cons,List.mem_cons,Set.mem_insert_iff]
          rw [hcv,hQv,coreVerts_cons,if_pos ha]
        · intro x hx _; simpa using hx
      · have hcountP : (coreEdges P S).ncard+1=(coreVerts P S).ncard := by
          simp only [ha,false_and,if_false,add_zero] at hvc hec
          omega
        obtain ⟨u,v,A,Q,B,hform,hQ,hQv,hA,hB⟩ := ih hp.of_cons hP hcountP
        refine ⟨u,v,Walk.cons h A,Q,B,?_,hQ,?_,?_,hB⟩
        · simp only [Walk.cons_append,hform]
        · rw [coreVerts_cons,if_neg ha]
          exact hQv
        · intro x hx hxS
          rcases List.mem_cons.mp hx with rfl | hx
          · exact (ha hxS).elim
          · exact hA x hx hxS
    · have hPv := Set.not_nonempty_iff_eq_empty.mp hP
      have ha : a ∈ S := by
        by_contra ha
        rw [coreVerts_cons,if_neg ha,hPv] at hS
        exact Set.not_nonempty_empty hS
      refine ⟨a,a,.nil,.nil,Walk.cons h P,rfl,Walk.IsPath.nil,?_,?_,?_⟩
      · rw [coreVerts_cons,if_pos ha,hPv]
        simp
      · intro x hx _; simpa using hx
      · intro x hx hxS
        rcases List.mem_cons.mp hx with rfl | hx
        · rfl
        · exact (hP ⟨x,(mem_coreVerts P S x).mpr ⟨hx,hxS⟩⟩).elim

/-- One core deficit can be removed by cutting at an outside vertex. Each
half then has a single nonempty core interval. -/
lemma one_gap_split [Fintype V] (P : G.Walk a b) (hp : P.IsPath) (S : Set V)
    (hcount : (coreEdges P S).ncard+2=(coreVerts P S).ncard) :
    ∃ z, z ∉ S ∧ ∃ A : G.Walk a z, ∃ B : G.Walk z b,
      P=A.append B ∧ (coreVerts A S).Nonempty ∧ (coreVerts B S).Nonempty ∧
      (coreEdges A S).ncard+1=(coreVerts A S).ncard ∧
      (coreEdges B S).ncard+1=(coreVerts B S).ncard := by
  induction P with
  | @nil a =>
    rw [coreEdges_nil,Set.ncard_empty,coreVerts_nil] at hcount
    split_ifs at hcount <;> simp_all
  | @cons a w b h P ih =>
    have hvc := coreVerts_cons_ncard h P hp S
    have hec := coreEdges_cons_ncard h P hp S
    by_cases hbreak : a ∈ S ∧ w ∉ S
    · obtain ⟨ha,hw⟩ := hbreak
      have hcountP : (coreEdges P S).ncard+1=(coreVerts P S).ncard := by
        simp only [ha,hw,true_and,if_true,if_false,add_zero] at hvc hec
        omega
      have hPv : (coreVerts P S).Nonempty :=
        (Set.ncard_pos (Set.toFinite _)).mp (by omega)
      refine ⟨w,hw,Walk.cons h .nil,P,rfl,?_,hPv,?_,hcountP⟩
      · exact ⟨a,(mem_coreVerts _ _ _).mpr ⟨Walk.start_mem_support _,ha⟩⟩
      · simp [coreVerts_cons,coreVerts_nil,coreEdges_cons,coreEdges_nil,ha,hw]
    · have hflags : (if a ∈ S ∧ w ∈ S then 1 else 0)=(if a ∈ S then 1 else 0) := by
        by_cases ha : a ∈ S
        · have hw : w ∈ S := by tauto
          simp [ha,hw]
        · simp [ha]
      have hcountP : (coreEdges P S).ncard+2=(coreVerts P S).ncard := by
        rw [hflags] at hec
        omega
      obtain ⟨z,hz,A,B,hform,hAv,hBv,hAc,hBc⟩ := ih hp.of_cons hcountP
      have hnew : ((Walk.cons h A).append B).IsPath := by
        simpa only [Walk.cons_append,←hform] using hp
      refine ⟨z,hz,Walk.cons h A,B,?_,?_,hBv,?_,hBc⟩
      · simp only [Walk.cons_append,hform]
      · obtain ⟨x,hx⟩ := hAv
        obtain ⟨hx,hxS⟩ := (mem_coreVerts A S x).mp hx
        exact ⟨x,(mem_coreVerts _ _ _).mpr ⟨List.mem_cons_of_mem _ hx,hxS⟩⟩
      · have hv := coreVerts_cons_ncard h A hnew.of_append_left S
        have he := coreEdges_cons_ncard h A hnew.of_append_left S
        rw [hflags] at he
        omega

end Erdos583PathCoreIntervalsDevelopment
