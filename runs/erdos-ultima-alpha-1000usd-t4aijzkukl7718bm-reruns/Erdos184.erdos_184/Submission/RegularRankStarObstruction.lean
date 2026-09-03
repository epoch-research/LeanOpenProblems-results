import Submission.StarCutDegree

/-!
Six dense branches give an unbounded prescribed-root rank-charge obstruction,
even in even regular graphs without a cut vertex. This does not obstruct a
favorable global choice of root and does not settle Erdos 184.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.RegularRankStarObstruction
open StarElimination StarCutBudget RankCritical RankCriticalPartitions
set_option maxHeartbeats 1000000

abbrev Inside (s : ℕ) := (Fin s × Bool) ⊕ Fin (4*s+1)
abbrev Vert (s : ℕ) := Bool ⊕ (Fin 6 × Inside s)

def baseAdj {s : ℕ} : Inside s → Inside s → Prop
  | .inl (i,_), .inl (j,_) => i ≠ j
  | x, y => x ≠ y

def graph (s : ℕ) : SimpleGraph (Vert s) where
  Adj x y := match x,y with
    | .inl _, .inl _ => False
    | .inl b, .inr (_,x) => match x with
      | .inl (_,c) => b = c
      | .inr _ => False
    | .inr (_,x), .inl b => match x with
      | .inl (_,c) => b = c
      | .inr _ => False
    | .inr (i,x), .inr (j,y) => i = j ∧ baseAdj x y
  symm := by
    intro x y h
    cases x with
    | inl b => cases y <;> exact h
    | inr x =>
      obtain ⟨i,x⟩ := x
      cases y with
      | inl b => exact h
      | inr y =>
        obtain ⟨j,y⟩ := y
        refine ⟨h.1.symm,?_⟩
        cases x <;> cases y <;> simpa [baseAdj,ne_comm] using h.2
  loopless := by
    intro x h
    cases x with
    | inl b => exact h
    | inr x =>
      obtain ⟨i,x⟩ := x
      cases x <;> simpa [baseAdj] using h.2

lemma inside_order (s : ℕ) : Fintype.card (Inside s) = 6*s+1 := by
  simp [Inside]
  omega

lemma graph_order (s : ℕ) : Fintype.card (Vert s) = 36*s+8 := by
  simp only [Vert,Fintype.card_sum,Fintype.card_bool,Fintype.card_prod,Fintype.card_fin,inside_order]
  omega

lemma hub_degree (s : ℕ) (b : Bool) : (graph s).degree (.inl b) = 6*s := by
  have hn : (graph s).neighborFinset (.inl b) =
      Finset.univ.image (fun x : Fin 6 × Fin s => (Sum.inr (x.1,.inl (x.2,b)) : Vert s)) := by
    ext x
    cases x with
    | inl c => simp [mem_neighborFinset,graph]
    | inr x =>
      obtain ⟨i,x⟩ := x
      cases x with
      | inl x => obtain ⟨j,c⟩ := x; simp [mem_neighborFinset,graph,eq_comm]
      | inr j => simp [mem_neighborFinset,graph]
  rw [← card_neighborFinset_eq_degree,hn,Finset.card_image_of_injective _]
  · simp
  · rintro ⟨i,j⟩ ⟨k,l⟩ h
    have he := Sum.inr.inj h
    have hi : i = k := congrArg Prod.fst he
    have hj : j = l := congrArg Prod.fst (Sum.inl.inj (congrArg Prod.snd he))
    exact Prod.ext hi hj

lemma port_degree (s : ℕ) (i : Fin 6) (j : Fin s) (b : Bool) :
    (graph s).degree (.inr (i,.inl (j,b))) = 6*s := by
  let T : Finset (Inside s) := (Finset.univ.erase (.inl (j,b))).erase (.inl (j,!b))
  have hn : (graph s).neighborFinset (.inr (i,.inl (j,b))) =
      insert (.inl b) (T.image (fun x => (Sum.inr (i,x) : Vert s))) := by
    ext x
    cases x with
    | inl c => simp [mem_neighborFinset,graph,T,eq_comm]
    | inr x =>
      obtain ⟨k,x⟩ := x
      cases x with
      | inl x =>
        obtain ⟨l,c⟩ := x
        cases b <;> cases c <;> simp [mem_neighborFinset,graph,baseAdj,T,eq_comm,and_comm]
      | inr l => simp [mem_neighborFinset,graph,baseAdj,T,eq_comm]
  have hinj : Function.Injective (fun x : Inside s => (Sum.inr (i,x) : Vert s)) := by
    intro x y h
    exact congrArg Prod.snd (Sum.inr.inj h)
  have hne : (Sum.inl (j,!b) : Inside s) ≠ Sum.inl (j,b) := by cases b <;> simp
  rw [← card_neighborFinset_eq_degree,hn,Finset.card_insert_of_notMem (by simp),
    Finset.card_image_of_injective _ hinj]
  dsimp [T]
  rw [Finset.card_erase_of_mem (by simp [hne]),Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ,inside_order]
  have hj := j.isLt
  omega

lemma private_degree (s : ℕ) (i : Fin 6) (j : Fin (4*s+1)) :
    (graph s).degree (.inr (i,.inr j)) = 6*s := by
  have hn : (graph s).neighborFinset (.inr (i,.inr j)) =
      (Finset.univ.erase (.inr j : Inside s)).image (fun x => (Sum.inr (i,x) : Vert s)) := by
    ext x
    cases x with
    | inl c => simp [mem_neighborFinset,graph]
    | inr x =>
      obtain ⟨k,x⟩ := x
      cases x <;> simp [mem_neighborFinset,graph,baseAdj,eq_comm,and_comm]
  rw [← card_neighborFinset_eq_degree,hn,Finset.card_image_of_injective _]
  · rw [Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,inside_order]
    omega
  · intro x y h
    exact congrArg Prod.snd (Sum.inr.inj h)

lemma graph_degree (s : ℕ) (v : Vert s) : (graph s).degree v = 6*s := by
  cases v with
  | inl b => exact hub_degree s b
  | inr v =>
    obtain ⟨i,x⟩ := v
    cases x with
    | inl x => exact port_degree s i x.1 x.2
    | inr j => exact private_degree s i j

lemma graph_regular (s : ℕ) : (graph s).IsRegularOfDegree (6*s) := by
  intro v
  simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using graph_degree s v

lemma graph_even (s : ℕ) (v : Vert s) : Even ((graph s).degree v) := by
  rw [graph_degree]
  exact ⟨3*s,by omega⟩

lemma branch_reachable (s : ℕ) (hs : 0 < s) (i : Fin 6) (x : Inside s) (b : Bool) :
    (graph s).Reachable (.inr (i,x)) (.inl b) := by
  let j : Fin s := ⟨0,hs⟩
  let p : Inside s := .inr 0
  have hmid : (graph s).Adj (.inr (i,p)) (.inr (i,.inl (j,b))) := by
    simp [graph,baseAdj,p]
  have hlast : (graph s).Adj (.inr (i,.inl (j,b))) (.inl b) := rfl
  have hfirst : (graph s).Reachable (.inr (i,x)) (.inr (i,p)) := by
    by_cases hx : x = p
    · subst x; exact .refl _
    · apply Adj.reachable
      cases x <;> simpa [graph,baseAdj,p] using hx
  exact hfirst.trans (hmid.reachable.trans hlast.reachable)

lemma graph_connected (s : ℕ) (hs : 0 < s) : (graph s).Connected := by
  have h (v : Vert s) : (graph s).Reachable v (.inl false) := by
    cases v with
    | inl b =>
      exact (branch_reachable s hs 0 (.inr 0) b).symm.trans (branch_reachable s hs 0 (.inr 0) false)
    | inr v => exact branch_reachable s hs v.1 v.2 false
  exact ⟨fun a b => (h a).trans (h b).symm⟩

lemma branch_reachable_after_delete (s : ℕ) (hs : 2 ≤ s) (v : Vert s)
    (i : Fin 6) (x : Inside s) (b : Bool)
    (hx : (Sum.inr (i,x) : Vert s) ≠ v) (hb : (Sum.inl b : Vert s) ≠ v) :
    ((graph s).deleteIncidenceSet v).Reachable (.inr (i,x)) (.inl b) := by
  obtain ⟨j,hj⟩ : ∃ j : Fin (4*s+1), (Sum.inr (i,Sum.inr j) : Vert s) ≠ v := by
    by_cases h : (Sum.inr (i,Sum.inr (0 : Fin (4*s+1))) : Vert s) = v
    · refine ⟨⟨1,by omega⟩,?_⟩
      rw [← h]
      simp
    · exact ⟨0,h⟩
  obtain ⟨k,hk⟩ : ∃ k : Fin s, (Sum.inr (i,Sum.inl (k,b)) : Vert s) ≠ v := by
    by_cases h : (Sum.inr (i,Sum.inl (⟨0,by omega⟩,b)) : Vert s) = v
    · refine ⟨⟨1,by omega⟩,?_⟩
      rw [← h]
      simp
    · exact ⟨⟨0,by omega⟩,h⟩
  have hfirst : ((graph s).deleteIncidenceSet v).Reachable (.inr (i,x)) (.inr (i,.inr j)) := by
    by_cases he : x = .inr j
    · subst x; exact .refl _
    · apply Adj.reachable
      apply deleteIncidenceSet_adj.mpr
      refine ⟨?_,hx,hj⟩
      cases x <;> simpa [graph,baseAdj] using he
  have hmid : ((graph s).deleteIncidenceSet v).Adj (.inr (i,.inr j)) (.inr (i,.inl (k,b))) := by
    apply deleteIncidenceSet_adj.mpr
    exact ⟨by simp [graph,baseAdj],hj,hk⟩
  have hlast : ((graph s).deleteIncidenceSet v).Adj (.inr (i,.inl (k,b))) (.inl b) :=
    deleteIncidenceSet_adj.mpr ⟨rfl,hk,hb⟩
  exact hfirst.trans (hmid.reachable.trans hlast.reachable)

lemma graph_no_cut (s : ℕ) (hs : 2 ≤ s) (v a b : Vert s)
    (ha : a ≠ v) (hb : b ≠ v) : ((graph s).deleteIncidenceSet v).Reachable a b := by
  obtain ⟨c,hc⟩ : ∃ c : Bool, (Sum.inl c : Vert s) ≠ v := by
    by_cases h : (Sum.inl false : Vert s) = v
    · exact ⟨true,by rw [← h]; simp⟩
    · exact ⟨false,h⟩
  obtain ⟨j,hj⟩ : ∃ j : Fin (4*s+1), (Sum.inr (0,Sum.inr j) : Vert s) ≠ v := by
    by_cases h : (Sum.inr (0,Sum.inr (0 : Fin (4*s+1))) : Vert s) = v
    · refine ⟨⟨1,by omega⟩,?_⟩
      rw [← h]
      simp
    · exact ⟨0,h⟩
  have h (w : Vert s) (hw : w ≠ v) : ((graph s).deleteIncidenceSet v).Reachable w (.inl c) := by
    cases w with
    | inl d =>
      exact (branch_reachable_after_delete s hs v 0 (.inr j) d hj hw).symm.trans
        (branch_reachable_after_delete s hs v 0 (.inr j) c hj hc)
    | inr w => exact branch_reachable_after_delete s hs v w.1 w.2 c hw hc
  exact (h a ha).trans (h b hb).symm

def branchColor {s : ℕ} (i : Fin 6) : Vert s → Bool
  | .inl _ => false
  | .inr (j,_) => decide (j=i)

noncomputable def boundary (s : ℕ) (i : Fin 6) : Finset (Sym2 (Vert s)) :=
  Finset.univ.image (fun x : Fin s × Bool => s(Sum.inl x.2,Sum.inr (i,Sum.inl x)))

lemma branch_cut_subset (s : ℕ) (i : Fin 6) :
    (graph s).edgeSet \ (monochromatic (graph s) (branchColor i)).edgeSet ⊆ boundary s i := by
  intro e he
  induction e using Sym2.ind with
  | h x y =>
    have hxy : (graph s).Adj x y := he.1
    have hn : branchColor i x ≠ branchColor i y := by
      intro h
      exact he.2 ⟨hxy,h⟩
    cases x with
    | inl b =>
      cases y with
      | inl c => exact hxy.elim
      | inr y =>
        obtain ⟨j,y⟩ := y
        cases y with
        | inr k => exact hxy.elim
        | inl y =>
          obtain ⟨k,c⟩ := y
          have hbc : b=c := hxy
          subst c
          have hji : j=i := by simpa [branchColor] using hn
          subst j
          exact Finset.mem_image.mpr ⟨(k,b),Finset.mem_univ _,rfl⟩
    | inr x =>
      obtain ⟨j,x⟩ := x
      cases y with
      | inl b =>
        cases x with
        | inr k => exact hxy.elim
        | inl x =>
          obtain ⟨k,c⟩ := x
          have hbc : b=c := hxy
          subst c
          have hji : j=i := by simpa [branchColor] using hn
          subst j
          exact Finset.mem_image.mpr ⟨(k,b),Finset.mem_univ _,Sym2.eq_swap⟩
      | inr y =>
        obtain ⟨k,y⟩ := y
        have hjk : j=k := hxy.1
        subst k
        exact (hn rfl).elim

lemma branch_cut_bound (s : ℕ) (i : Fin 6) :
    ((graph s).edgeSet \ (monochromatic (graph s) (branchColor i)).edgeSet).ncard ≤ 2*s := by
  have hh := Set.ncard_le_ncard (branch_cut_subset s i)
  rw [Set.ncard_coe_finset] at hh
  have hb := Finset.card_image_le (s := (Finset.univ : Finset (Fin s × Bool)))
    (f := fun x : Fin s × Bool => (s(Sum.inl x.2,Sum.inr (i,Sum.inl x)) : Sym2 (Vert s)))
  simp only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at hb
  exact hh.trans (by simpa [boundary,mul_comm] using hb)

noncomputable def closure (s : ℕ) (i : Fin 6) : Finset (Vert s) :=
  insert (.inl false) (insert (.inl true) (Finset.univ.image (fun x : Inside s => .inr (i,x))))

lemma closure_card (s : ℕ) (i : Fin 6) : (closure s i).card = 6*s+3 := by
  have hi : Function.Injective (fun x : Inside s => (Sum.inr (i,x) : Vert s)) := by
    intro x y h
    exact congrArg Prod.snd (Sum.inr.inj h)
  simp [closure,Finset.card_image_of_injective _ hi,inside_order]
  omega

lemma neighbor_subset_closure (s : ℕ) (i : Fin 6) (x : Inside s)
    (R : SimpleGraph (Vert s)) (hR : R ≤ graph s) : R.neighborFinset (.inr (i,x)) ⊆ closure s i := by
  intro y hy
  have hxy : (graph s).Adj (.inr (i,x)) y := hR ((R.mem_neighborFinset _ _).mp hy)
  cases y with
  | inl b => cases b <;> simp [closure]
  | inr y =>
    obtain ⟨j,y⟩ := y
    have hij : i=j := hxy.1
    subst j
    simp [closure]

lemma residual_branch_degree (s : ℕ) (P : Finset (graph s).Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set (graph s).Subgraph) (fun H => H.edgeSet))
    (hv : ∀ H ∈ P, Sum.inl false ∈ H.verts) (i : Fin 6) (x : Inside s) :
    4*s ≤ (graph s \ unionPieces (graph s) P).degree (.inr (i,x)) := by
  have hb := packing_degree_le_cut (graph_even s) P hc hd hv
    (w := Sum.inr (i,x)) (branchColor i) (by simp [branchColor])
  have hcut := branch_cut_bound s i
  have he := degree_sdiff_of_le (unionPieces_le (graph s) P) (.inr (i,x))
  have hg := graph_degree s (.inr (i,x))
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hb he hg ⊢
  omega

lemma residual_branch_reachable (s : ℕ) (hs : 2 ≤ s) (P : Finset (graph s).Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set (graph s).Subgraph) (fun H => H.edgeSet))
    (hv : ∀ H ∈ P, Sum.inl false ∈ H.verts) (i : Fin 6) (x y : Inside s) :
    (graph s \ unionPieces (graph s) P).Reachable (.inr (i,x)) (.inr (i,y)) := by
  let R := graph s \ unionPieces (graph s) P
  have hx := residual_branch_degree s P hc hd hv i x
  have hy := residual_branch_degree s P hc hd hv i y
  have hun : R.neighborFinset (.inr (i,x)) ∪ R.neighborFinset (.inr (i,y)) ⊆ closure s i :=
    by
      apply Finset.union_subset
      · simpa only [neighborFinset, ← Set.toFinite_toFinset] using neighbor_subset_closure s i x R sdiff_le
      · simpa only [neighborFinset, ← Set.toFinite_toFinset] using neighbor_subset_closure s i y R sdiff_le
  have hb := Finset.card_le_card hun
  rw [closure_card] at hb
  have he := Finset.card_union_add_card_inter (R.neighborFinset (.inr (i,x))) (R.neighborFinset (.inr (i,y)))
  simp only [card_neighborFinset_eq_degree] at he
  have hp : 0 < (R.neighborFinset (.inr (i,x)) ∩ R.neighborFinset (.inr (i,y))).card := by
    dsimp [R] at *
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hx hy he
    omega
  obtain ⟨z,hz⟩ := Finset.card_pos.mp hp
  obtain ⟨hzx,hzy⟩ := Finset.mem_inter.mp hz
  exact ((R.mem_neighborFinset _ _).mp hzx).reachable.trans ((R.mem_neighborFinset _ _).mp hzy).symm.reachable

lemma residual_component_bound (s : ℕ) (hs : 2 ≤ s) (P : Finset (graph s).Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set (graph s).Subgraph) (fun H => H.edgeSet))
    (hv : ∀ H ∈ P, Sum.inl false ∈ H.verts) :
    Nat.card (graph s \ unionPieces (graph s) P).ConnectedComponent ≤ 8 := by
  let R := graph s \ unionPieces (graph s) P
  let rep : Bool ⊕ Fin 6 → Vert s
    | .inl b => .inl b
    | .inr i => .inr (i,.inr 0)
  let f : Bool ⊕ Fin 6 → R.ConnectedComponent := fun x => R.connectedComponentMk (rep x)
  have hf : Function.Surjective f := by
    intro c
    induction c using ConnectedComponent.ind with
    | _ v =>
      cases v with
      | inl b => exact ⟨.inl b,rfl⟩
      | inr v =>
        obtain ⟨i,x⟩ := v
        refine ⟨.inr i,?_⟩
        apply ConnectedComponent.sound
        exact residual_branch_reachable s hs P hc hd hv i (.inr 0) x
  have hb := Nat.card_le_card_of_surjective f hf
  simpa only [Nat.card_eq_fintype_card,Fintype.card_sum,Fintype.card_bool,Fintype.card_fin] using hb

lemma rank_loss_bound (s : ℕ) (hs : 2 ≤ s) (P : Finset (graph s).Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set (graph s).Subgraph) (fun H => H.edgeSet))
    (hv : ∀ H ∈ P, Sum.inl false ∈ H.verts) :
    graphRank (graph s) ≤ graphRank (graph s \ unionPieces (graph s) P) + 7 := by
  have hcomp := residual_component_bound s hs P hc hd hv
  have hfull := connected_rank (graph_connected s (by omega))
  unfold graphRank at hfull ⊢
  rw [graph_order] at *
  omega

lemma exhausting_packing_exists (s : ℕ) :
    ∃ P : Finset (graph s).Subgraph,
      (∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Set.PairwiseDisjoint (P : Set (graph s).Subgraph) (fun H => H.edgeSet) ∧
      (∀ H ∈ P, Sum.inl false ∈ H.verts) ∧
      Sum.inl false ∉ (graph s \ unionPieces (graph s) P).support := by
  obtain ⟨D,hc,hd⟩ := even_cycle_decomposition (graph s) (graph_even s)
  refine ⟨star D (.inl false),fun H hH => hc H (star_subset D _ hH),?_,?_,?_⟩
  · intro H hH K hK hne
    exact hd.1 (star_subset D _ hH) (star_subset D _ hK) hne
  · intro H hH
    exact ((mem_star D _ H).mp hH).2
  · exact (isolated_iff_star_subset D (star D _) (star_subset D _) hc hd _).mpr (fun _ h => h)

lemma no_uniform_regular_prescribed_root_rank_charge (C : ℕ)
    (P : Finset (graph (3*C+2)).Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set (graph (3*C+2)).Subgraph) (fun H => H.edgeSet))
    (hv : ∀ H ∈ P, Sum.inl false ∈ H.verts)
    (hi : Sum.inl false ∉ (graph (3*C+2) \ unionPieces (graph (3*C+2)) P).support) :
    C * graphRank (graph (3*C+2)) <
      P.card + C * graphRank (graph (3*C+2) \ unionPieces (graph (3*C+2)) P) := by
  have hcard := card_of_exhausted (graph_even (3*C+2)) P hc hd hv hi
  rw [graph_degree] at hcard
  have hrank := rank_loss_bound (3*C+2) (by omega) P hc hd hv
  have hm := Nat.mul_le_mul_left C hrank
  simp only [Nat.mul_add] at hm
  omega

end Erdos184.RegularRankStarObstruction
