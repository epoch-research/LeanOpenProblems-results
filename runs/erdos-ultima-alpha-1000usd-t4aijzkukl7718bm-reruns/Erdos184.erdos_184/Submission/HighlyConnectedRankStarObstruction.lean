import Submission.StarCutDegree

/-!
Arbitrarily high fixed connectivity does not rescue prescribed-root rank charging.
This is an auxiliary obstruction, not a disproof of the conjecture in Spec.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.HighlyConnectedRankStarObstruction
open StarElimination StarCutBudget RankCritical RankCriticalPartitions
set_option maxHeartbeats 1000000

abbrev Hub (t : ℕ) := Fin t × Bool
abbrev Port (t s : ℕ) := (Fin t × Fin s) × Bool
abbrev Inside (t s : ℕ) := Port t s ⊕ Fin (4*(t*s)+1)
abbrev Vert (t s : ℕ) := Hub t ⊕ (Fin (6*t) × Inside t s)

def owner {t s : ℕ} (x : Port t s) : Hub t := (x.1.1,x.2)

def baseAdj {t s : ℕ} : Inside t s → Inside t s → Prop
  | .inl (i,_), .inl (j,_) => i ≠ j
  | x, y => x ≠ y

def graph (t s : ℕ) : SimpleGraph (Vert t s) where
  Adj x y := match x,y with
    | .inl _, .inl _ => False
    | .inl b, .inr (_,x) => match x with
      | .inl p => b = owner p
      | .inr _ => False
    | .inr (_,x), .inl b => match x with
      | .inl p => b = owner p
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

lemma inside_order (t s : ℕ) : Fintype.card (Inside t s) = 6*(t*s)+1 := by
  simp [Inside,Port]
  omega

lemma graph_order (t s : ℕ) :
    Fintype.card (Vert t s) = (6*t)*(6*(t*s)+1)+2*t := by
  simp only [Vert,Hub,Fintype.card_sum,Fintype.card_bool,Fintype.card_prod,
    Fintype.card_fin,inside_order]
  ring

lemma hub_degree (t s : ℕ) (b : Hub t) : (graph t s).degree (.inl b) = 6*(t*s) := by
  have hn : (graph t s).neighborFinset (.inl b) =
      Finset.univ.image (fun x : Fin (6*t) × Fin s =>
        (Sum.inr (x.1,.inl ((b.1,x.2),b.2)) : Vert t s)) := by
    ext x
    cases x with
    | inl c => simp [mem_neighborFinset,graph]
    | inr x =>
      obtain ⟨i,x⟩ := x
      cases x with
      | inl x =>
        obtain ⟨⟨a,j⟩,c⟩ := x
        simp [mem_neighborFinset,graph,owner,Prod.ext_iff,eq_comm,and_left_comm,and_comm]
      | inr j => simp [mem_neighborFinset,graph]
  rw [← card_neighborFinset_eq_degree,hn,Finset.card_image_of_injective _]
  · simp [Nat.mul_assoc]
  · rintro ⟨i,j⟩ ⟨k,l⟩ h
    have he := Sum.inr.inj h
    have hi : i = k := congrArg Prod.fst he
    have hj : j = l := congrArg (fun x : Port t s => x.1.2)
      (Sum.inl.inj (congrArg Prod.snd he))
    exact Prod.ext hi hj

lemma port_degree (t s : ℕ) (i : Fin (6*t)) (j : Fin t × Fin s) (b : Bool) :
    (graph t s).degree (.inr (i,.inl (j,b))) = 6*(t*s) := by
  let T : Finset (Inside t s) := (Finset.univ.erase (.inl (j,b))).erase (.inl (j,!b))
  have hn : (graph t s).neighborFinset (.inr (i,.inl (j,b))) =
      insert (.inl (j.1,b)) (T.image (fun x => (Sum.inr (i,x) : Vert t s))) := by
    ext x
    cases x with
    | inl c => simp [mem_neighborFinset,graph,owner,T,eq_comm]
    | inr x =>
      obtain ⟨k,x⟩ := x
      cases x with
      | inl x =>
        obtain ⟨l,c⟩ := x
        cases b <;> cases c <;> simp [mem_neighborFinset,graph,baseAdj,T,eq_comm,and_comm]
      | inr l => simp [mem_neighborFinset,graph,baseAdj,T,eq_comm]
  have hinj : Function.Injective (fun x : Inside t s => (Sum.inr (i,x) : Vert t s)) := by
    intro x y h
    exact congrArg Prod.snd (Sum.inr.inj h)
  have hne : (Sum.inl (j,!b) : Inside t s) ≠ Sum.inl (j,b) := by cases b <;> simp
  rw [← card_neighborFinset_eq_degree,hn,Finset.card_insert_of_notMem (by simp),
    Finset.card_image_of_injective _ hinj]
  dsimp [T]
  rw [Finset.card_erase_of_mem (by simp [hne]),Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ,inside_order]
  have ht := j.1.isLt
  have hs := j.2.isLt
  have hpos : 0 < t*s := Nat.mul_pos (by omega) (by omega)
  omega

lemma private_degree (t s : ℕ) (i : Fin (6*t)) (j : Fin (4*(t*s)+1)) :
    (graph t s).degree (.inr (i,.inr j)) = 6*(t*s) := by
  have hn : (graph t s).neighborFinset (.inr (i,.inr j)) =
      (Finset.univ.erase (.inr j : Inside t s)).image
        (fun x => (Sum.inr (i,x) : Vert t s)) := by
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

lemma graph_degree (t s : ℕ) (v : Vert t s) : (graph t s).degree v = 6*(t*s) := by
  cases v with
  | inl b => exact hub_degree t s b
  | inr v =>
    obtain ⟨i,x⟩ := v
    cases x with
    | inl x => exact port_degree t s i x.1 x.2
    | inr j => exact private_degree t s i j

lemma graph_regular (t s : ℕ) : (graph t s).IsRegularOfDegree (6*(t*s)) := by
  intro v
  simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using graph_degree t s v

lemma graph_even (t s : ℕ) (v : Vert t s) : Even ((graph t s).degree v) := by
  rw [graph_degree]
  exact ⟨3*(t*s),by omega⟩

lemma branch_reachable (t s : ℕ) (hs : 0 < s) (i : Fin (6*t))
    (x : Inside t s) (b : Hub t) :
    (graph t s).Reachable (.inr (i,x)) (.inl b) := by
  let j : Fin s := ⟨0,hs⟩
  let p : Inside t s := .inr 0
  have hmid : (graph t s).Adj (.inr (i,p)) (.inr (i,.inl ((b.1,j),b.2))) := by
    simp [graph,baseAdj,p]
  have hlast : (graph t s).Adj (.inr (i,.inl ((b.1,j),b.2))) (.inl b) := by
    simp [graph,owner]
  have hfirst : (graph t s).Reachable (.inr (i,x)) (.inr (i,p)) := by
    by_cases hx : x = p
    · subst x; exact .refl _
    · apply Adj.reachable
      cases x <;> simpa [graph,baseAdj,p] using hx
  exact hfirst.trans (hmid.reachable.trans hlast.reachable)

lemma graph_connected (t s : ℕ) (ht : 0 < t) (hs : 0 < s) : (graph t s).Connected := by
  let b : Hub t := (⟨0,ht⟩,false)
  let i : Fin (6*t) := ⟨0,by omega⟩
  have h (v : Vert t s) : (graph t s).Reachable v (.inl b) := by
    cases v with
    | inl c =>
      exact (branch_reachable t s hs i (.inr 0) c).symm.trans
        (branch_reachable t s hs i (.inr 0) b)
    | inr v => exact branch_reachable t s hs v.1 v.2 b
  letI : Nonempty (Vert t s) := ⟨.inl b⟩
  exact ⟨fun a c => (h a).trans (h c).symm⟩

lemma exists_image_outside {A V : Type*} [Fintype A] [Fintype V]
    (S : Set V) (f : A → V) (hf : Function.Injective f)
    (hcard : S.ncard < Fintype.card A) : ∃ a, f a ∉ S := by
  by_contra! hn
  have hsub : Set.range f ⊆ S := by rintro _ ⟨a,rfl⟩; exact hn a
  have hb := Set.ncard_le_ncard hsub
  rw [Set.ncard_range_of_injective hf,Nat.card_eq_fintype_card] at hb
  omega

lemma private_available (t s : ℕ) (S : Set (Vert t s)) (i : Fin (6*t))
    (hS : S.ncard < 4*(t*s)+1) :
    ∃ j : Fin (4*(t*s)+1), (Sum.inr (i,Sum.inr j) : Vert t s) ∉ S := by
  apply exists_image_outside S (fun j => Sum.inr (i,Sum.inr j))
  · intro a b h
    exact Sum.inr.inj (congrArg Prod.snd (Sum.inr.inj h))
  · simpa using hS

lemma branch_reachable_outside (t s : ℕ) (ht : 0 < t)
    (S : Set (Vert t s)) (hS : S.ncard < s)
    (i : Fin (6*t)) (x : Inside t s) (b : Hub t)
    (hx : (Sum.inr (i,x) : Vert t s) ∉ S) (hb : (Sum.inl b : Vert t s) ∉ S) :
    ((graph t s).induce Sᶜ).Reachable ⟨.inr (i,x),hx⟩ ⟨.inl b,hb⟩ := by
  have hprivate : S.ncard < 4*(t*s)+1 := by nlinarith
  obtain ⟨j,hj⟩ := private_available t s S i hprivate
  obtain ⟨k,hk⟩ : ∃ k : Fin s,
      (Sum.inr (i,Sum.inl ((b.1,k),b.2)) : Vert t s) ∉ S := by
    apply exists_image_outside S (fun k => Sum.inr (i,Sum.inl ((b.1,k),b.2)))
    · intro a c h
      exact congrArg (fun x : Port t s => x.1.2)
        (Sum.inl.inj (congrArg Prod.snd (Sum.inr.inj h)))
    · simpa using hS
  have hfirst : ((graph t s).induce Sᶜ).Reachable
      ⟨.inr (i,x),hx⟩ ⟨.inr (i,.inr j),hj⟩ := by
    by_cases he : x = .inr j
    · subst x; exact .refl _
    · apply Adj.reachable
      change (graph t s).Adj (.inr (i,x)) (.inr (i,.inr j))
      cases x <;> simpa [graph,baseAdj] using he
  have hmid : ((graph t s).induce Sᶜ).Adj
      ⟨.inr (i,.inr j),hj⟩ ⟨.inr (i,.inl ((b.1,k),b.2)),hk⟩ := by
    change (graph t s).Adj (.inr (i,.inr j)) (.inr (i,.inl ((b.1,k),b.2)))
    simp [graph,baseAdj]
  have hlast : ((graph t s).induce Sᶜ).Adj
      ⟨.inr (i,.inl ((b.1,k),b.2)),hk⟩ ⟨.inl b,hb⟩ := by
    change (graph t s).Adj (.inr (i,.inl ((b.1,k),b.2))) (.inl b)
    simp [graph,owner]
  exact hfirst.trans (hmid.reachable.trans hlast.reachable)

/-- Deleting fewer than both `2*t` and `s` vertices leaves the graph connected
on its remaining vertices. The first bound prevents deletion of all hubs. -/
lemma outside_reachable (t s : ℕ) (S : Set (Vert t s))
    (hh : S.ncard < 2*t) (hs : S.ncard < s) (a b : ↥(Sᶜ)) :
    ((graph t s).induce Sᶜ).Reachable a b := by
  have ht : 0 < t := by omega
  obtain ⟨c,hc⟩ : ∃ c : Hub t, (Sum.inl c : Vert t s) ∉ S := by
    apply exists_image_outside S Sum.inl Sum.inl_injective
    simpa [Hub,mul_comm] using hh
  let i : Fin (6*t) := ⟨0,by omega⟩
  obtain ⟨j,hj⟩ := private_available t s S i (by nlinarith)
  have h (w : ↥(Sᶜ)) : ((graph t s).induce Sᶜ).Reachable w ⟨.inl c,hc⟩ := by
    obtain ⟨w,hw⟩ := w
    cases w with
    | inl d =>
      exact (branch_reachable_outside t s ht S hs i (.inr j) d hj hw).symm.trans
        (branch_reachable_outside t s ht S hs i (.inr j) c hj hc)
    | inr w => exact branch_reachable_outside t s ht S hs w.1 w.2 c hw hc
  exact (h a).trans (h b).symm

lemma high_connectivity (t s : ℕ) (hs : 2*t ≤ s)
    (S : Set (Vert t s)) (hS : S.ncard < 2*t) (a b : ↥(Sᶜ)) :
    ((graph t s).induce Sᶜ).Reachable a b :=
  outside_reachable t s S hS (lt_of_lt_of_le hS hs) a b

def branchColor {t s : ℕ} (i : Fin (6*t)) : Vert t s → Bool
  | .inl _ => false
  | .inr (j,_) => decide (j=i)

noncomputable def boundary (t s : ℕ) (i : Fin (6*t)) : Finset (Sym2 (Vert t s)) :=
  Finset.univ.image (fun x : Port t s => s(Sum.inl (owner x),Sum.inr (i,Sum.inl x)))

lemma branch_cut_subset (t s : ℕ) (i : Fin (6*t)) :
    (graph t s).edgeSet \ (monochromatic (graph t s) (branchColor i)).edgeSet ⊆ boundary t s i := by
  intro e he
  induction e using Sym2.ind with
  | h x y =>
    have hxy : (graph t s).Adj x y := he.1
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
          have hb : b=owner y := hxy
          subst b
          have hji : j=i := by simpa [branchColor] using hn
          subst j
          exact Finset.mem_image.mpr ⟨y,Finset.mem_univ _,rfl⟩
    | inr x =>
      obtain ⟨j,x⟩ := x
      cases y with
      | inl b =>
        cases x with
        | inr k => exact hxy.elim
        | inl x =>
          have hb : b=owner x := hxy
          subst b
          have hji : j=i := by simpa [branchColor] using hn
          subst j
          exact Finset.mem_image.mpr ⟨x,Finset.mem_univ _,Sym2.eq_swap⟩
      | inr y =>
        obtain ⟨k,y⟩ := y
        have hjk : j=k := hxy.1
        subst k
        exact (hn rfl).elim

lemma branch_cut_bound (t s : ℕ) (i : Fin (6*t)) :
    ((graph t s).edgeSet \ (monochromatic (graph t s) (branchColor i)).edgeSet).ncard ≤ 2*(t*s) := by
  have hh := Set.ncard_le_ncard (branch_cut_subset t s i)
  rw [Set.ncard_coe_finset] at hh
  have hb := Finset.card_image_le (s := (Finset.univ : Finset (Port t s)))
    (f := fun x : Port t s => (s(Sum.inl (owner x),Sum.inr (i,Sum.inl x)) : Sym2 (Vert t s)))
  simp only [Finset.card_univ,Port,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at hb
  exact hh.trans (by simpa [boundary,mul_comm] using hb)

noncomputable def closure (t s : ℕ) (i : Fin (6*t)) : Finset (Vert t s) :=
  (Finset.univ.image Sum.inl) ∪ (Finset.univ.image (fun x : Inside t s => .inr (i,x)))

lemma closure_card (t s : ℕ) (i : Fin (6*t)) : (closure t s i).card = 6*(t*s)+2*t+1 := by
  have hi : Function.Injective (fun x : Inside t s => (Sum.inr (i,x) : Vert t s)) := by
    intro x y h
    exact congrArg Prod.snd (Sum.inr.inj h)
  have hd : Disjoint (Finset.univ.image (Sum.inl : Hub t → Vert t s))
      (Finset.univ.image (fun x : Inside t s => (Sum.inr (i,x) : Vert t s))) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hx
    simpa using hy
  rw [closure,Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ Sum.inl_injective,
    Finset.card_image_of_injective _ hi,Finset.card_univ,Finset.card_univ,inside_order]
  simp [Hub]
  omega

lemma neighbor_subset_closure (t s : ℕ) (i : Fin (6*t)) (x : Inside t s)
    (R : SimpleGraph (Vert t s)) (hR : R ≤ graph t s) :
    R.neighborFinset (.inr (i,x)) ⊆ closure t s i := by
  intro y hy
  have hxy : (graph t s).Adj (.inr (i,x)) y := hR ((R.mem_neighborFinset _ _).mp hy)
  cases y with
  | inl b => simp [closure]
  | inr y =>
    obtain ⟨j,y⟩ := y
    have hij : i=j := hxy.1
    subst j
    simp [closure]

lemma residual_branch_degree (t s : ℕ) (b : Hub t) (P : Finset (graph t s).Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set (graph t s).Subgraph) (fun H => H.edgeSet))
    (hv : ∀ H ∈ P, Sum.inl b ∈ H.verts) (i : Fin (6*t)) (x : Inside t s) :
    4*(t*s) ≤ (graph t s \ unionPieces (graph t s) P).degree (.inr (i,x)) := by
  have hb := packing_degree_le_cut (graph_even t s) P hc hd hv
    (w := Sum.inr (i,x)) (branchColor i) (by simp [branchColor])
  have hcut := branch_cut_bound t s i
  have he := degree_sdiff_of_le (unionPieces_le (graph t s) P) (.inr (i,x))
  have hg := graph_degree t s (.inr (i,x))
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hb he hg ⊢
  omega

lemma residual_branch_reachable (t s : ℕ) (ht : 0 < t) (hs : 2 ≤ s)
    (b : Hub t) (P : Finset (graph t s).Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set (graph t s).Subgraph) (fun H => H.edgeSet))
    (hv : ∀ H ∈ P, Sum.inl b ∈ H.verts) (i : Fin (6*t)) (x y : Inside t s) :
    (graph t s \ unionPieces (graph t s) P).Reachable (.inr (i,x)) (.inr (i,y)) := by
  let R := graph t s \ unionPieces (graph t s) P
  have hx := residual_branch_degree t s b P hc hd hv i x
  have hy := residual_branch_degree t s b P hc hd hv i y
  have hun : R.neighborFinset (.inr (i,x)) ∪ R.neighborFinset (.inr (i,y)) ⊆ closure t s i :=
    by
      apply Finset.union_subset
      · simpa only [neighborFinset, ← Set.toFinite_toFinset] using neighbor_subset_closure t s i x R sdiff_le
      · simpa only [neighborFinset, ← Set.toFinite_toFinset] using neighbor_subset_closure t s i y R sdiff_le
  have hb := Finset.card_le_card hun
  rw [closure_card] at hb
  have he := Finset.card_union_add_card_inter (R.neighborFinset (.inr (i,x))) (R.neighborFinset (.inr (i,y)))
  simp only [card_neighborFinset_eq_degree] at he
  have hp : 0 < (R.neighborFinset (.inr (i,x)) ∩ R.neighborFinset (.inr (i,y))).card := by
    dsimp [R] at *
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hx hy he
    nlinarith
  obtain ⟨z,hz⟩ := Finset.card_pos.mp hp
  obtain ⟨hzx,hzy⟩ := Finset.mem_inter.mp hz
  exact ((R.mem_neighborFinset _ _).mp hzx).reachable.trans ((R.mem_neighborFinset _ _).mp hzy).symm.reachable

lemma residual_component_bound (t s : ℕ) (ht : 0 < t) (hs : 2 ≤ s)
    (b : Hub t) (P : Finset (graph t s).Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set (graph t s).Subgraph) (fun H => H.edgeSet))
    (hv : ∀ H ∈ P, Sum.inl b ∈ H.verts) :
    Nat.card (graph t s \ unionPieces (graph t s) P).ConnectedComponent ≤ 8*t := by
  let R := graph t s \ unionPieces (graph t s) P
  let rep : Hub t ⊕ Fin (6*t) → Vert t s
    | .inl c => .inl c
    | .inr i => .inr (i,.inr 0)
  let f : Hub t ⊕ Fin (6*t) → R.ConnectedComponent := fun x => R.connectedComponentMk (rep x)
  have hf : Function.Surjective f := by
    intro c
    induction c using ConnectedComponent.ind with
    | _ v =>
      cases v with
      | inl c => exact ⟨.inl c,rfl⟩
      | inr v =>
        obtain ⟨i,x⟩ := v
        refine ⟨.inr i,?_⟩
        apply ConnectedComponent.sound
        exact residual_branch_reachable t s ht hs b P hc hd hv i (.inr 0) x
  have hb := Nat.card_le_card_of_surjective f hf
  simp only [Nat.card_eq_fintype_card,Hub,Fintype.card_sum,Fintype.card_prod,
    Fintype.card_bool,Fintype.card_fin] at hb
  simpa only [Nat.card_eq_fintype_card] using
    (show Fintype.card R.ConnectedComponent ≤ 8*t by omega)

lemma rank_loss_bound (t s : ℕ) (ht : 0 < t) (hs : 2 ≤ s)
    (b : Hub t) (P : Finset (graph t s).Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set (graph t s).Subgraph) (fun H => H.edgeSet))
    (hv : ∀ H ∈ P, Sum.inl b ∈ H.verts) :
    graphRank (graph t s) ≤ graphRank (graph t s \ unionPieces (graph t s) P) + (8*t-1) := by
  have hcomp := residual_component_bound t s ht hs b P hc hd hv
  have hfull := connected_rank (graph_connected t s ht (by omega))
  unfold graphRank at hfull ⊢
  omega

lemma exhausting_packing_exists (t s : ℕ) (b : Hub t) :
    ∃ P : Finset (graph t s).Subgraph,
      (∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Set.PairwiseDisjoint (P : Set (graph t s).Subgraph) (fun H => H.edgeSet) ∧
      (∀ H ∈ P, Sum.inl b ∈ H.verts) ∧
      Sum.inl b ∉ (graph t s \ unionPieces (graph t s) P).support := by
  obtain ⟨D,hc,hd⟩ := even_cycle_decomposition (graph t s) (graph_even t s)
  refine ⟨StarElimination.star D (.inl b),fun H hH => hc H (star_subset D _ hH),?_,?_,?_⟩
  · intro H hH K hK hne
    exact hd.1 (star_subset D _ hH) (star_subset D _ hK) hne
  · intro H hH
    exact ((mem_star D _ H).mp hH).2
  · exact (isolated_iff_star_subset D (StarElimination.star D _) (star_subset D _) hc hd _).mpr (fun _ h => h)

lemma exhausted_card (t s : ℕ) (b : Hub t) (P : Finset (graph t s).Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set (graph t s).Subgraph) (fun H => H.edgeSet))
    (hv : ∀ H ∈ P, Sum.inl b ∈ H.verts)
    (hi : Sum.inl b ∉ (graph t s \ unionPieces (graph t s) P).support) : P.card = 3*(t*s) := by
  have hcard := card_of_exhausted (graph_even t s) P hc hd hv hi
  rw [graph_degree] at hcard
  omega

lemma prescribed_root_obstruction (t C : ℕ) (ht : 0 < t) (b : Hub t)
    (P : Finset (graph t (3*C+2*t+2)).Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set (graph t (3*C+2*t+2)).Subgraph) (fun H => H.edgeSet))
    (hv : ∀ H ∈ P, Sum.inl b ∈ H.verts)
    (hi : Sum.inl b ∉ (graph t (3*C+2*t+2) \ unionPieces (graph t (3*C+2*t+2)) P).support) :
    C * graphRank (graph t (3*C+2*t+2)) <
      P.card + C * graphRank (graph t (3*C+2*t+2) \ unionPieces (graph t (3*C+2*t+2)) P) := by
  have hcard := exhausted_card t (3*C+2*t+2) b P hc hd hv hi
  have hrank := rank_loss_bound t (3*C+2*t+2) ht (by omega) b P hc hd hv
  have hm := Nat.mul_le_mul_left C hrank
  have hle : 8*t-1 ≤ 8*t := Nat.sub_le _ _
  have hm' := Nat.mul_le_mul_left C hle
  simp only [Nat.mul_add] at hm
  nlinarith


/-- For every requested connectivity and coefficient, a concrete even regular graph
survives deletion of that many vertices, but every exhausting packing at the
specified hub violates the proposed rank charge. Such packings exist. -/
theorem arbitrary_connectivity_and_charge (k C : ℕ) :
    let t := k+1
    let s := 3*C+2*t+2
    ∃ b : Hub t,
      (graph t s).Connected ∧
      (graph t s).IsRegularOfDegree (6*(t*s)) ∧
      (∀ v, Even ((graph t s).degree v)) ∧
      (∀ S : Set (Vert t s), S.ncard ≤ k → ∀ a c : ↥(Sᶜ),
        ((graph t s).induce Sᶜ).Reachable a c) ∧
      (∃ P : Finset (graph t s).Subgraph,
        (∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
        Set.PairwiseDisjoint (P : Set (graph t s).Subgraph) (fun H => H.edgeSet) ∧
        (∀ H ∈ P, Sum.inl b ∈ H.verts) ∧
        Sum.inl b ∉ (graph t s \ unionPieces (graph t s) P).support) ∧
      (∀ P : Finset (graph t s).Subgraph,
        (∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
        Set.PairwiseDisjoint (P : Set (graph t s).Subgraph) (fun H => H.edgeSet) →
        (∀ H ∈ P, Sum.inl b ∈ H.verts) →
        Sum.inl b ∉ (graph t s \ unionPieces (graph t s) P).support →
        C * graphRank (graph t s) <
          P.card + C * graphRank (graph t s \ unionPieces (graph t s) P)) := by
  dsimp only
  let b : Hub (k+1) := (⟨0,by omega⟩,false)
  refine ⟨b,graph_connected _ _ (by omega) (by omega),graph_regular _ _,
    graph_even _ _,?_,exhausting_packing_exists _ _ b,?_⟩
  · intro S hS a c
    exact high_connectivity _ _ (by omega) S (by omega) a c
  · intro P hc hd hv hi
    exact prescribed_root_obstruction (k+1) C (by omega) b P hc hd hv hi

lemma common_neighbors_le_cut {V : Type*} [Fintype V] (G : SimpleGraph V)
    (f : V → Bool) {u v : V} (huv : f u ≠ f v) :
    (G.neighborFinset u ∩ G.neighborFinset v).card ≤
      (G.edgeSet \ (monochromatic G f).edgeSet).ncard := by
  let S := G.neighborFinset u ∩ G.neighborFinset v
  let e : V → Sym2 V := fun z => if f z = f u then s(v,z) else s(u,z)
  have hmem (z : V) (hz : z ∈ S) : e z ∈ G.edgeSet \ (monochromatic G f).edgeSet := by
    obtain ⟨hzu,hzv⟩ := Finset.mem_inter.mp hz
    have hzu := (G.mem_neighborFinset _ _).mp hzu
    have hzv := (G.mem_neighborFinset _ _).mp hzv
    by_cases h : f z = f u
    · simp only [e,if_pos h]
      exact ⟨hzv,fun hh => huv (h.symm.trans hh.2.symm)⟩
    · simp only [e,if_neg h]
      exact ⟨hzu,fun hh => h hh.2.symm⟩
  have hinj : Set.InjOn e (S : Set V) := by
    intro x hx y hy he
    obtain ⟨hxu,hxv⟩ := Finset.mem_inter.mp hx
    obtain ⟨hyu,hyv⟩ := Finset.mem_inter.mp hy
    have hxu := ((G.mem_neighborFinset _ _).mp hxu).ne
    have hxv := ((G.mem_neighborFinset _ _).mp hxv).ne
    have hyu := ((G.mem_neighborFinset _ _).mp hyu).ne
    have hyv := ((G.mem_neighborFinset _ _).mp hyv).ne
    have hne : u ≠ v := fun h => huv (congrArg f h)
    by_cases hx : f x = f u <;> by_cases hy : f y = f u <;>
      simp only [e,hx,hy,if_true,if_false,Sym2.eq_iff] at he <;> aesop
  have hsub : S.image e ⊆ (G.edgeSet \ (monochromatic G f).edgeSet).toFinset := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    exact Set.mem_toFinset.mpr (hmem x hx)
  have hb := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj] at hb
  simpa only [Set.ncard_eq_toFinset_card'] using hb

lemma branch_common_neighbors (t s : ℕ) (ht : 0 < t) (hs : 0 < s)
    (i : Fin (6*t)) (x y : Inside t s) :
    2*(t*s) ≤ ((graph t s).neighborFinset (.inr (i,x)) ∩
      (graph t s).neighborFinset (.inr (i,y))).card := by
  have hun : (graph t s).neighborFinset (.inr (i,x)) ∪
      (graph t s).neighborFinset (.inr (i,y)) ⊆ closure t s i := by
    exact Finset.union_subset (neighbor_subset_closure t s i x _ le_rfl)
      (neighbor_subset_closure t s i y _ le_rfl)
  have hb := Finset.card_le_card hun
  rw [closure_card] at hb
  have he := Finset.card_union_add_card_inter ((graph t s).neighborFinset (.inr (i,x)))
    ((graph t s).neighborFinset (.inr (i,y)))
  simp only [card_neighborFinset_eq_degree,graph_degree] at he
  nlinarith

lemma cut_bound_of_split_branch (t s : ℕ) (ht : 0 < t) (hs : 0 < s)
    (f : Vert t s → Bool) (i : Fin (6*t)) (x y : Inside t s)
    (hne : f (.inr (i,x)) ≠ f (.inr (i,y))) :
    2*(t*s) ≤ ((graph t s).edgeSet \ (monochromatic (graph t s) f).edgeSet).ncard :=
by
  have ha := branch_common_neighbors t s ht hs i x y
  have hb := common_neighbors_le_cut (graph t s) f
    (u := .inr (i,x)) (v := .inr (i,y)) hne
  simp only [← Set.ncard_coe_finset,Finset.coe_inter,coe_neighborFinset] at ha hb
  exact ha.trans hb

lemma port_cut_bound (t s : ℕ) (f : Vert t s → Bool) (j : Port t s → Fin (6*t))
    (hj : ∀ x, f (.inl (owner x)) ≠ f (.inr (j x,.inl x))) :
    2*(t*s) ≤ ((graph t s).edgeSet \ (monochromatic (graph t s) f).edgeSet).ncard := by
  let e : Port t s → Sym2 (Vert t s) := fun x => s(Sum.inl (owner x),Sum.inr (j x,.inl x))
  have hinj : Function.Injective e := by
    intro x y h
    rcases Sym2.eq_iff.mp h with h | h
    · exact Sum.inl.inj (congrArg Prod.snd (Sum.inr.inj h.2))
    · cases h.1
  have hsub : Set.range e ⊆ (graph t s).edgeSet \ (monochromatic (graph t s) f).edgeSet := by
    rintro _ ⟨x,rfl⟩
    exact ⟨rfl,fun h => hj x h.2⟩
  have hb := Set.ncard_le_ncard hsub
  rw [Set.ncard_range_of_injective hinj,Nat.card_eq_fintype_card] at hb
  simpa [Port,mul_comm] using hb

lemma all_branch_colors_cut_bound (t s : ℕ) (f : Vert t s → Bool)
    (b : Hub t) (c : Bool)
    (hbranch : ∀ i : Fin (6*t), ∀ x : Inside t s, f (.inr (i,x)) = c)
    (hb : f (.inl b) ≠ c) :
    6*(t*s) ≤ ((graph t s).edgeSet \ (monochromatic (graph t s) f).edgeSet).ncard := by
  let e : Fin (6*t) × Fin s → Sym2 (Vert t s) :=
    fun x => s(Sum.inl b,Sum.inr (x.1,.inl ((b.1,x.2),b.2)))
  have hinj : Function.Injective e := by
    rintro ⟨i,j⟩ ⟨k,l⟩ h
    rcases Sym2.eq_iff.mp h with h | h
    · have h' := Sum.inr.inj h.2
      have hi : i = k := congrArg Prod.fst h'
      have hj : j = l := congrArg (fun x : Port t s => x.1.2)
        (Sum.inl.inj (congrArg Prod.snd h'))
      exact Prod.ext hi hj
    · cases h.1
  have hsub : Set.range e ⊆ (graph t s).edgeSet \ (monochromatic (graph t s) f).edgeSet := by
    rintro _ ⟨x,rfl⟩
    refine ⟨?_,?_⟩
    · change b = owner ((b.1,x.2),b.2)
      simp [owner]
    · intro h
      exact hb (h.2.trans (hbranch _ _))
  have hcard := Set.ncard_le_ncard hsub
  rw [Set.ncard_range_of_injective hinj,Nat.card_eq_fintype_card] at hcard
  simpa [Nat.mul_assoc] using hcard

/-- Every nontrivial edge cut has at least one third of the regular degree.
The bound applies simultaneously with the arbitrarily high vertex connectivity. -/
lemma edge_cut_lower (t s : ℕ) (ht : 0 < t) (hs : 0 < s)
    (f : Vert t s → Bool) {u v : Vert t s} (huv : f u ≠ f v) :
    2*(t*s) ≤ ((graph t s).edgeSet \ (monochromatic (graph t s) f).edgeSet).ncard := by
  by_cases hsplit : ∃ i : Fin (6*t), ∃ x y : Inside t s, f (.inr (i,x)) ≠ f (.inr (i,y))
  · obtain ⟨i,x,y,hxy⟩ := hsplit
    exact cut_bound_of_split_branch t s ht hs f i x y hxy
  push_neg at hsplit
  let c : Fin (6*t) → Bool := fun i => f (.inr (i,.inr 0))
  have hbranch (i : Fin (6*t)) (x : Inside t s) : f (.inr (i,x)) = c i :=
    hsplit i x (.inr 0)
  by_cases hdiff : ∃ i j, c i ≠ c j
  · obtain ⟨i,j,hij⟩ := hdiff
    let q : Port t s → Fin (6*t) := fun x => if f (.inl (owner x)) = c i then j else i
    apply port_cut_bound t s f q
    intro x
    by_cases hx : f (.inl (owner x)) = c i
    · simpa only [q,if_pos hx,hbranch,hx] using hij
    · simpa only [q,if_neg hx,hbranch] using hx
  push_neg at hdiff
  let i : Fin (6*t) := ⟨0,by omega⟩
  have hconst (j : Fin (6*t)) (x : Inside t s) : f (.inr (j,x)) = c i :=
    (hbranch j x).trans (hdiff j i)
  obtain ⟨b,hb⟩ : ∃ b : Hub t, f (.inl b) ≠ c i := by
    by_contra! hh
    have hall (w : Vert t s) : f w = c i := by
      cases w with
      | inl b => exact hh b
      | inr w => exact hconst w.1 w.2
    exact huv ((hall u).trans (hall v).symm)
  have hbnd := all_branch_colors_cut_bound t s f b (c i) hconst hb
  omega


lemma branch_cut_exact (t s : ℕ) (ht : 0 < t) (hs : 0 < s) (i : Fin (6*t)) :
    ((graph t s).edgeSet \ (monochromatic (graph t s) (branchColor i)).edgeSet).ncard =
      2*(t*s) := by
  have hlo := edge_cut_lower t s ht hs (branchColor i)
    (u := .inl (⟨0,ht⟩,false)) (v := .inr (i,.inr 0)) (by simp [branchColor])
  exact le_antisymm (branch_cut_bound t s i) hlo

end Erdos184.HighlyConnectedRankStarObstruction
