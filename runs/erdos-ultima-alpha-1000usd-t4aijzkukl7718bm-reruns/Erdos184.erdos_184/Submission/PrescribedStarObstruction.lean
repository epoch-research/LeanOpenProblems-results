import Submission.StarCutBudget

/-!
In a connected even regular graph, an arbitrary prescribed root need not
admit a uniformly efficient eliminating star. This does not refute favorable
root selection or the original decomposition conjecture.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.PrescribedStarObstruction
open StarElimination StarCutBudget RankCriticalPartitions
set_option maxHeartbeats 1000000

abbrev Inside (r : ℕ) := Bool ⊕ Fin (2*r+3)
abbrev Vert (r : ℕ) := Bool ⊕ (Fin (2*r+4) × Inside r)

def baseAdj {r : ℕ} : Inside r → Inside r → Prop
  | .inl _, .inl _ => False
  | x, y => x ≠ y

def graph (r : ℕ) : SimpleGraph (Vert r) where
  Adj x y := match x,y with
    | .inl _, .inl _ => False
    | .inl b, .inr (_,y) => y = .inl b
    | .inr (_,x), .inl b => x = .inl b
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

lemma hub_degree (r : ℕ) (b : Bool) :
    (graph r).degree (.inl b) = 2*r+4 := by
  have hn : (graph r).neighborFinset (.inl b) =
      Finset.univ.image (fun i : Fin (2*r+4) => (Sum.inr (i,Sum.inl b) : Vert r)) := by
    ext x
    cases x with
    | inl c => simp [mem_neighborFinset,graph]
    | inr x =>
      obtain ⟨i,x⟩ := x
      simp [mem_neighborFinset,graph,eq_comm]
  rw [← card_neighborFinset_eq_degree,hn,Finset.card_image_of_injective _]
  · simp
  · intro i j h
    exact congrArg Prod.fst (Sum.inr.inj h)

lemma port_degree (r : ℕ) (i : Fin (2*r+4)) (b : Bool) :
    (graph r).degree (.inr (i,.inl b)) = 2*r+4 := by
  let T : Finset (Vert r) := Finset.univ.image
    (fun j : Fin (2*r+3) => Sum.inr (i,Sum.inr j))
  have hn : (graph r).neighborFinset (.inr (i,.inl b)) = insert (.inl b) T := by
    ext x
    cases x with
    | inl c => simp [mem_neighborFinset,graph,T,eq_comm]
    | inr x =>
      obtain ⟨k,x⟩ := x
      cases x <;> simp [mem_neighborFinset,graph,baseAdj,T,eq_comm]
  rw [← card_neighborFinset_eq_degree,hn,Finset.card_insert_of_notMem (by simp [T])]
  have hi : Function.Injective (fun j : Fin (2*r+3) => (Sum.inr (i,Sum.inr j) : Vert r)) := by
    intro j k h
    exact Sum.inr.inj (congrArg Prod.snd (Sum.inr.inj h))
  simp [T,Finset.card_image_of_injective _ hi]

lemma private_degree (r : ℕ) (i : Fin (2*r+4)) (j : Fin (2*r+3)) :
    (graph r).degree (.inr (i,.inr j)) = 2*r+4 := by
  have hn : (graph r).neighborFinset (.inr (i,.inr j)) =
      (Finset.univ.erase (Sum.inr j : Inside r)).image
        (fun x => (Sum.inr (i,x) : Vert r)) := by
    ext x
    cases x with
    | inl c => simp [mem_neighborFinset,graph]
    | inr x =>
      obtain ⟨k,x⟩ := x
      cases x <;> simp [mem_neighborFinset,graph,baseAdj,eq_comm,and_comm]
  rw [← card_neighborFinset_eq_degree,hn,Finset.card_image_of_injective _]
  · simp [Inside]
    omega
  · intro x y h
    exact congrArg Prod.snd (Sum.inr.inj h)

lemma graph_degree (r : ℕ) (v : Vert r) : (graph r).degree v = 2*r+4 := by
  cases v with
  | inl b => exact hub_degree r b
  | inr v =>
    obtain ⟨i,v⟩ := v
    cases v with
    | inl b => exact port_degree r i b
    | inr j => exact private_degree r i j

lemma graph_regular (r : ℕ) : (graph r).IsRegularOfDegree (2*r+4) := by
  intro v
  simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using graph_degree r v

lemma graph_even (r : ℕ) (v : Vert r) : Even ((graph r).degree v) := by
  rw [graph_degree]
  exact ⟨r+2,by omega⟩

lemma graph_support (r : ℕ) : (graph r).support = Set.univ := by
  apply Set.eq_univ_of_forall
  intro v
  apply ((graph r).degree_pos_iff_mem_support v).mp
  rw [graph_degree]
  omega

lemma branch_reachable (r : ℕ) (i : Fin (2*r+4)) (x : Inside r) :
    (graph r).Reachable (.inr (i,x)) (.inl false) := by
  have hlast : (graph r).Adj (.inr (i,.inl false)) (.inl false) := rfl
  have hmid : (graph r).Adj (.inr (i,.inr (0 : Fin (2*r+3)))) (.inr (i,.inl false)) := by
    simp [graph,baseAdj]
  cases x with
  | inl b =>
    have hfirst : (graph r).Adj (.inr (i,.inl b)) (.inr (i,.inr (0 : Fin (2*r+3)))) := by
      simp [graph,baseAdj]
    exact hfirst.reachable.trans (hmid.reachable.trans hlast.reachable)
  | inr j =>
    have hfirst : (graph r).Adj (.inr (i,.inr j)) (.inr (i,.inl false)) := by
      simp [graph,baseAdj]
    exact hfirst.reachable.trans hlast.reachable

lemma graph_connected (r : ℕ) : (graph r).Connected := by
  have hroot (v : Vert r) : (graph r).Reachable v (.inl false) := by
    cases v with
    | inl b =>
      have h : (graph r).Adj (.inl b) (.inr ((0 : Fin (2*r+4)),.inl b)) := rfl
      exact h.reachable.trans (branch_reachable r 0 (.inl b))
    | inr v => exact branch_reachable r v.1 v.2
  exact ⟨fun x y => (hroot x).trans (hroot y).symm⟩

lemma graph_order (r : ℕ) : Fintype.card (Vert r) = 2+(2*r+4)*(2*r+5) := by
  simp [Vert,Inside]
  ring

def branchColor {r : ℕ} (i : Fin (2*r+4)) : Vert r → Bool
  | .inl _ => false
  | .inr (j,_) => decide (j = i)

lemma branch_cut_subset (r : ℕ) (i : Fin (2*r+4)) :
    (graph r).edgeSet \ (monochromatic (graph r) (branchColor i)).edgeSet ⊆
      {s(Sum.inl false,Sum.inr (i,Sum.inl false)),
       s(Sum.inl true,Sum.inr (i,Sum.inl true))} := by
  intro e he
  induction e using Sym2.ind with
  | h x y =>
    have hxy : (graph r).Adj x y := he.1
    have hn : branchColor i x ≠ branchColor i y := by
      intro h
      exact he.2 ⟨hxy,h⟩
    cases x with
    | inl b =>
      cases y with
      | inl c => exact hxy.elim
      | inr y =>
        obtain ⟨j,y⟩ := y
        have hy : y = Sum.inl b := hxy
        subst y
        have hji : j = i := by simpa [branchColor] using hn
        subst j
        cases b <;> simp
    | inr x =>
      obtain ⟨j,x⟩ := x
      cases y with
      | inl b =>
        have hx : x = Sum.inl b := hxy
        subst x
        have hji : j = i := by simpa [branchColor] using hn
        subst j
        cases b <;> simp [Sym2.eq_swap]
      | inr y =>
        obtain ⟨k,y⟩ := y
        have hjk : j = k := hxy.1
        subst k
        exact (hn rfl).elim

lemma branch_cut_le_two (r : ℕ) (i : Fin (2*r+4)) :
    ((graph r).edgeSet \ (monochromatic (graph r) (branchColor i)).edgeSet).ncard ≤ 2 := by
  exact (Set.ncard_le_ncard (branch_cut_subset r i)).trans (by simpa using Set.ncard_insert_le _ {_})

/-- No internal branch vertex is isolated by any cycle packing through the
prescribed hub. The packing need not be greedy or minimum. -/
lemma branch_survives (r : ℕ) (P : Finset (graph r).Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set (graph r).Subgraph) (fun H => H.edgeSet))
    (hv : ∀ H ∈ P, Sum.inl false ∈ H.verts)
    (i : Fin (2*r+4)) (x : Inside r) :
    Sum.inr (i,x) ∈ (graph r \ unionPieces (graph r) P).support := by
  by_contra hi
  have hb := degree_le_cut_of_isolated (graph_even r) P hc hd hv hi
    (branchColor i) (by simp [branchColor])
  rw [graph_degree] at hb
  have hcut := branch_cut_le_two r i
  omega

lemma support_loss_le_two (r : ℕ) (P : Finset (graph r).Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set (graph r).Subgraph) (fun H => H.edgeSet))
    (hv : ∀ H ∈ P, Sum.inl false ∈ H.verts) :
    (graph r).support.ncard ≤ (graph r \ unionPieces (graph r) P).support.ncard + 2 := by
  have hs : (graph r).support \ (graph r \ unionPieces (graph r) P).support ⊆
      {Sum.inl false,Sum.inl true} := by
    intro v hv'
    cases v with
    | inl b => cases b <;> simp
    | inr v => exact (hv'.2 (branch_survives r P hc hd hv v.1 v.2)).elim
  have hp : ({Sum.inl false,Sum.inl true} : Set (Vert r)).ncard ≤ 2 := by simp
  have hb := (Set.ncard_le_ncard hs).trans hp
  have hh := Set.ncard_diff_add_ncard_of_subset
    (SimpleGraph.support_mono (show graph r \ unionPieces (graph r) P ≤ graph r from sdiff_le))
  omega


/-- The class of root-exhausting packings used by the obstruction is
nonempty, and every such star has exactly r+2 pieces. -/
lemma root_exhausting_packing_exists (r : ℕ) :
    ∃ P : Finset (graph r).Subgraph,
      (∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Set.PairwiseDisjoint (P : Set (graph r).Subgraph) (fun H => H.edgeSet) ∧
      (∀ H ∈ P, Sum.inl false ∈ H.verts) ∧
      Sum.inl false ∉ (graph r \ unionPieces (graph r) P).support ∧
      P.card = r+2 := by
  obtain ⟨D,hc,hd⟩ := even_cycle_decomposition (graph r) (graph_even r)
  let P := star D (Sum.inl false)
  have hsub : P ⊆ D := star_subset D _
  have hi : Sum.inl false ∉ (graph r \ unionPieces (graph r) P).support := by
    apply (isolated_iff_star_subset D P hsub hc hd _).mpr
    exact Finset.Subset.refl _
  have hcard := star_card D hc hd (Sum.inl false)
  rw [graph_degree] at hcard
  refine ⟨P,fun H hH => hc H (hsub hH),?_,?_,hi,?_⟩
  · intro H hH K hK hne
    exact hd.1 (hsub hH) (hsub hK) hne
  · intro H hH
    exact ((mem_star D (Sum.inl false) H).mp hH).2
  · change (star D (Sum.inl false)).card = r+2
    omega

/-- Every root-exhausting packing in this family fails any prescribed fixed
charge, when the parameter is chosen sufficiently large. -/
lemma no_uniform_prescribed_root_charge (C : ℕ) (P : Finset (graph (2*C)).Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set (graph (2*C)).Subgraph) (fun H => H.edgeSet))
    (hv : ∀ H ∈ P, Sum.inl false ∈ H.verts)
    (hi : Sum.inl false ∉ (graph (2*C) \ unionPieces (graph (2*C)) P).support) :
    C * (graph (2*C)).support.ncard <
      P.card + C * (graph (2*C) \ unionPieces (graph (2*C)) P).support.ncard := by
  have hcard := card_of_exhausted (graph_even (2*C)) P hc hd hv hi
  rw [graph_degree] at hcard
  have hloss := support_loss_le_two (2*C) P hc hd hv
  have hmul := Nat.mul_le_mul_left C hloss
  rw [Nat.mul_add] at hmul
  omega

end Erdos184.PrescribedStarObstruction
