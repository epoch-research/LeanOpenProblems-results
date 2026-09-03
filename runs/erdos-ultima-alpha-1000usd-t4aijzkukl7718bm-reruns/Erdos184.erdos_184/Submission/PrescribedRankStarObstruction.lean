import Submission.StarCutBudget
import Submission.ShiftedPackingConnectivity

/-!
An arbitrary prescribed minimum-degree root need not admit a cycle star
whose cost is bounded by a constant times its spanning-forest-rank loss.
This is NOT a counterexample to favorable root selection or to Erdos 184.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.PrescribedRankStarObstruction
open StarElimination StarCutBudget RankCritical RankCriticalPartitions
set_option maxHeartbeats 1000000

abbrev Inside (r : ℕ) := (Fin r × Bool) ⊕ Fin (2*r+3)
abbrev Vert (r : ℕ) := Option (Inside r)

def baseAdj {r : ℕ} : Inside r → Inside r → Prop
  | .inl (i,_), .inl (j,_) => i ≠ j
  | x, y => x ≠ y

def graph (r : ℕ) : SimpleGraph (Vert r) where
  Adj x y := match x,y with
    | none, none => False
    | none, some (.inl _) => True
    | some (.inl _), none => True
    | none, some (.inr _) => False
    | some (.inr _), none => False
    | some x, some y => baseAdj x y
  symm := by
    intro x y h
    cases x with
    | none => cases y with
      | none => exact h
      | some y => cases y <;> exact h
    | some x => cases y with
      | none => cases x <;> exact h
      | some y => cases x <;> cases y <;> simpa [baseAdj,ne_comm] using h
  loopless := by
    intro x h
    cases x with
    | none => exact h
    | some x => cases x <;> simpa [baseAdj] using h

lemma graph_order (r : ℕ) : Fintype.card (Vert r) = 4*r+4 := by
  simp [Vert,Inside]
  omega

lemma root_degree (r : ℕ) : (graph r).degree none = 2*r := by
  have hn : (graph r).neighborFinset none =
      Finset.univ.image (fun x : Fin r × Bool => (some (.inl x) : Vert r)) := by
    ext x
    cases x with
    | none => simp [mem_neighborFinset,graph]
    | some x => cases x <;> simp [mem_neighborFinset,graph]
  rw [← card_neighborFinset_eq_degree,hn,Finset.card_image_of_injective _]
  · simp [mul_comm]
  · intro x y h
    exact Sum.inl.inj (Option.some.inj h)

lemma paired_degree (r : ℕ) (i : Fin r) (b : Bool) :
    (graph r).degree (some (.inl (i,b))) = 4*r+2 := by
  have hn : (graph r).neighborFinset (some (.inl (i,b))) =
      (Finset.univ.erase (some (.inl (i,b)) : Vert r)).erase (some (.inl (i,!b))) := by
    ext x
    cases x with
    | none => simp [mem_neighborFinset,graph]
    | some x =>
      cases x with
      | inl x =>
        obtain ⟨j,c⟩ := x
        cases b <;> cases c <;> simp [mem_neighborFinset,graph,baseAdj,ne_comm]
      | inr j => simp [mem_neighborFinset,graph,baseAdj]
  have hne : (some (.inl (i,!b)) : Vert r) ≠ some (.inl (i,b)) := by cases b <;> simp
  rw [← card_neighborFinset_eq_degree,hn,Finset.card_erase_of_mem (by simp [hne]),
    Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,graph_order]
  omega

lemma private_degree (r : ℕ) (j : Fin (2*r+3)) :
    (graph r).degree (some (.inr j)) = 4*r+2 := by
  have hn : (graph r).neighborFinset (some (.inr j)) =
      (Finset.univ.erase (some (.inr j) : Vert r)).erase none := by
    ext x
    cases x with
    | none => simp [mem_neighborFinset,graph]
    | some x => cases x <;> simp [mem_neighborFinset,graph,baseAdj,ne_comm]
  rw [← card_neighborFinset_eq_degree,hn,Finset.card_erase_of_mem (by simp),
    Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,graph_order]
  omega

lemma nonroot_degree (r : ℕ) (x : Inside r) :
    (graph r).degree (some x) = 4*r+2 := by
  cases x with
  | inl x => exact paired_degree r x.1 x.2
  | inr j => exact private_degree r j

lemma graph_even (r : ℕ) (x : Vert r) : Even ((graph r).degree x) := by
  cases x with
  | none => rw [root_degree]; exact ⟨r,by omega⟩
  | some x => rw [nonroot_degree]; exact ⟨2*r+1,by omega⟩

lemma unique_minimum (r : ℕ) (x : Inside r) :
    (graph r).degree none < (graph r).degree (some x) := by
  rw [root_degree,nonroot_degree]
  omega

lemma nonroot_reachable (r : ℕ) (x y : Inside r) :
    (graph r).Reachable (some x) (some y) := by
  let z : Inside r := .inr 0
  have h (a : Inside r) : (graph r).Reachable (some a) (some z) := by
    by_cases ha : a = z
    · subst a; exact .refl _
    · apply Adj.reachable
      cases a <;> simpa [graph,baseAdj,z] using ha
  exact (h x).trans (h y).symm

lemma graph_connected (r : ℕ) (hr : 0 < r) : (graph r).Connected := by
  let x : Inside r := .inl (⟨0,hr⟩,false)
  have h (v : Vert r) : (graph r).Reachable v (some x) := by
    cases v with
    | none => exact (show (graph r).Adj none (some x) from trivial).reachable
    | some y => exact nonroot_reachable r y x
  exact ⟨fun a b => (h a).trans (h b).symm⟩

lemma graph_no_cut (r : ℕ) (hr : 0 < r) (v a b : Vert r)
    (ha : a ≠ v) (hb : b ≠ v) :
    ((graph r).deleteIncidenceSet v).Reachable a b := by
  obtain ⟨j,hj⟩ : ∃ j : Fin (2*r+3), (some (.inr j) : Vert r) ≠ v := by
    by_cases h : (some (.inr (0 : Fin (2*r+3))) : Vert r) = v
    · exact ⟨1,by rw [← h]; simp⟩
    · exact ⟨0,h⟩
  have hsome (x : Inside r) (hx : (some x : Vert r) ≠ v) :
      ((graph r).deleteIncidenceSet v).Reachable (some x) (some (.inr j)) := by
    by_cases he : x = .inr j
    · subst x; exact .refl _
    · apply Adj.reachable
      apply deleteIncidenceSet_adj.mpr
      refine ⟨?_,hx,hj⟩
      cases x <;> simpa [graph,baseAdj] using he
  have hroot (hv : (none : Vert r) ≠ v) :
      ((graph r).deleteIncidenceSet v).Reachable none (some (.inr j)) := by
    let i : Fin r := ⟨0,hr⟩
    obtain ⟨c,hc⟩ : ∃ c : Bool, (some (.inl (i,c)) : Vert r) ≠ v := by
      by_cases h : (some (.inl (i,false)) : Vert r) = v
      · exact ⟨true,by rw [← h]; simp⟩
      · exact ⟨false,h⟩
    have he : ((graph r).deleteIncidenceSet v).Adj none (some (.inl (i,c))) :=
      deleteIncidenceSet_adj.mpr ⟨trivial,hv,hc⟩
    exact he.reachable.trans (hsome _ hc)
  have h (x : Vert r) (hx : x ≠ v) :
      ((graph r).deleteIncidenceSet v).Reachable x (some (.inr j)) := by
    cases x with
    | none => exact hroot hx
    | some x => exact hsome x hx
  exact (h a ha).trans (h b hb).symm

variable {V : Type*} [Fintype V]

/-- An isolated vertex cannot belong to either neighbor set. Pigeonhole
therefore gives a common neighbor when their degree sum exceeds n-1. -/
lemma reachable_of_degree_sum (R : SimpleGraph V) (v a b : V)
    (hv : v ∉ R.support)
    (hdeg : Fintype.card V ≤ R.degree a + R.degree b) : R.Reachable a b := by
  have hs : R.neighborFinset a ∪ R.neighborFinset b ⊆ Finset.univ.erase v := by
    intro x hx
    apply Finset.mem_erase.mpr
    refine ⟨?_,Finset.mem_univ _⟩
    intro he
    subst x
    rcases Finset.mem_union.mp hx with ha | hb
    · exact hv ⟨a,((R.mem_neighborFinset _ _).mp ha).symm⟩
    · exact hv ⟨b,((R.mem_neighborFinset _ _).mp hb).symm⟩
  have hb := Finset.card_le_card hs
  have he := Finset.card_union_add_card_inter (R.neighborFinset a) (R.neighborFinset b)
  rw [Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ] at hb
  simp only [card_neighborFinset_eq_degree] at he
  have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  have hp : 0 < (R.neighborFinset a ∩ R.neighborFinset b).card := by omega
  obtain ⟨z,hz⟩ := Finset.card_pos.mp hp
  obtain ⟨ha,hb⟩ := Finset.mem_inter.mp hz
  exact ((R.mem_neighborFinset _ _).mp ha).reachable.trans ((R.mem_neighborFinset _ _).mp hb).symm.reachable

lemma component_card_two (R : SimpleGraph V) (v w : V) (hvw : v ≠ w)
    (hv : v ∉ R.support)
    (hc : ∀ a b, a ≠ v → b ≠ v → R.Reachable a b) :
    Nat.card R.ConnectedComponent = 2 := by
  let label : V → Bool := fun x => decide (x=v)
  have hl : ∀ a b, R.Reachable a b → label a = label b := by
    intro a b hab
    by_cases ha : a=v
    · subst a
      have hb : b=v := by
        by_contra hb
        exact hv (mem_support_of_reachable (Ne.symm hb) hab)
      simp [label,hb]
    · have hb : b≠v := by
        intro hb
        subst b
        exact hv (mem_support_of_reachable (Ne.symm ha) hab.symm)
      simp [label,ha,hb]
  let f : R.ConnectedComponent → Bool := Quot.lift label (fun a b hab => hl a b hab)
  have hi : Function.Injective f := by
    intro c d hcd
    induction c using ConnectedComponent.ind with
    | _ a =>
      induction d using ConnectedComponent.ind with
      | _ b =>
        change label a = label b at hcd
        apply ConnectedComponent.sound
        by_cases ha : a=v
        · have hb : b=v := by simpa [label,ha] using hcd.symm
          subst a; subst b; exact .refl _
        · have hb : b≠v := by simpa [label,ha] using hcd.symm
          exact hc a b ha hb
  have hs : Function.Surjective f := by
    intro b
    cases b with
    | false => exact ⟨R.connectedComponentMk w,by change label w = false; simp [label,hvw.symm]⟩
    | true => exact ⟨R.connectedComponentMk v,by change label v = true; simp [label]⟩
  simpa using Nat.card_congr (Equiv.ofBijective f ⟨hi,hs⟩)

lemma star_residual_degree (r : ℕ) (P : Finset (graph r).Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set (graph r).Subgraph) (fun H => H.edgeSet))
    (hp : P.card = r) (x : Inside r) :
    2*r+2 ≤ ((graph r) \ unionPieces (graph r) P).degree (some x) := by
  have hb := ShiftedCritical.packing_degree_le P hc hd (some x)
  have he := degree_sdiff_of_le (unionPieces_le (graph r) P) (some x)
  have hg := nonroot_degree r x
  simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hb he hg ⊢
  omega

lemma exhausted_rank_loss (r : ℕ) (hr : 0 < r) (P : Finset (graph r).Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set (graph r).Subgraph) (fun H => H.edgeSet))
    (hv : ∀ H ∈ P, none ∈ H.verts)
    (hi : none ∉ ((graph r) \ unionPieces (graph r) P).support) :
    P.card = r ∧ graphRank ((graph r) \ unionPieces (graph r) P) + 1 = graphRank (graph r) := by
  have hh := card_of_exhausted (graph_even r) P hc hd hv hi
  rw [root_degree] at hh
  have hp : P.card = r := by omega
  have hreach : ∀ a b : Vert r, a ≠ none → b ≠ none →
      ((graph r) \ unionPieces (graph r) P).Reachable a b := by
    intro a b ha hb
    cases a with
    | none => exact (ha rfl).elim
    | some a => cases b with
      | none => exact (hb rfl).elim
      | some b =>
        apply reachable_of_degree_sum _ none _ _ hi
        have hda := star_residual_degree r P hc hd hp a
        have hdb := star_residual_degree r P hc hd hp b
        rw [graph_order]
        simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hda hdb ⊢
        omega
  have hcomp := component_card_two _ none (some (.inr 0)) (by simp) hi hreach
  have hfull := connected_rank (graph_connected r hr)
  refine ⟨hp,?_⟩
  unfold graphRank at hfull ⊢
  rw [hcomp,graph_order] at *
  omega

lemma exhausting_packing_exists (r : ℕ) :
    ∃ P : Finset (graph r).Subgraph,
      (∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Set.PairwiseDisjoint (P : Set (graph r).Subgraph) (fun H => H.edgeSet) ∧
      (∀ H ∈ P, none ∈ H.verts) ∧
      none ∉ ((graph r) \ unionPieces (graph r) P).support := by
  obtain ⟨D,hc,hd⟩ := even_cycle_decomposition (graph r) (graph_even r)
  refine ⟨star D none,fun H hH => hc H (star_subset D none hH),?_,?_,?_⟩
  · intro H hH K hK hne
    exact hd.1 (star_subset D none hH) (star_subset D none hK) hne
  · intro H hH
    exact ((mem_star D none H).mp hH).2
  · exact (isolated_iff_star_subset D (star D none) (star_subset D none) hc hd none).mpr (fun _ h => h)

/-- Even optimizing all cycles at the unique minimum-degree root cannot
bound their cost by a fixed multiple of the rank loss. -/
lemma no_uniform_prescribed_root_rank_charge (C : ℕ)
    (P : Finset (graph (C+1)).Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set (graph (C+1)).Subgraph) (fun H => H.edgeSet))
    (hv : ∀ H ∈ P, none ∈ H.verts)
    (hi : none ∉ ((graph (C+1)) \ unionPieces (graph (C+1)) P).support) :
    C * graphRank (graph (C+1)) <
      P.card + C * graphRank ((graph (C+1)) \ unionPieces (graph (C+1)) P) := by
  obtain ⟨hp,hr⟩ := exhausted_rank_loss (C+1) (by omega) P hc hd hv hi
  rw [← hr,Nat.mul_add,Nat.mul_one,hp]
  omega

end Erdos184.PrescribedRankStarObstruction
