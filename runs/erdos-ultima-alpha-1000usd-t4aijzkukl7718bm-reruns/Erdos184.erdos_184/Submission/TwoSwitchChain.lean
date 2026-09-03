import Submission.OrderedCutBudget

/-!
A parameterized lower bound for the capped chain of K5-minus-two-edges
blocks. The accompanying research construction obtains this chain by one
2-switch from two Hamilton cycles. That positive transfer is not assumed
or formalized here. This file does not settle Erdos 184.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.TwoSwitchChain
open RankCriticalPartitions OrderedCutBudget

abbrev V (t : ℕ) := Fin (t+1) × Fin 5

def block : SimpleGraph (Fin 5) where
  Adj u v := u ≠ v ∧
    ¬((u=0 ∧ v=1) ∨ (u=1 ∧ v=0) ∨ (u=2 ∧ v=3) ∨ (u=3 ∧ v=2))
  symm := by intro u v h; exact ⟨h.1.symm,by tauto⟩
  loopless := by intro v h; exact h.1 rfl

def port (u v : Fin 5) : Prop := (u=2 ∧ v=0) ∨ (u=3 ∧ v=1)
def leftCap (u v : Fin 5) : Prop := (u=0 ∧ v=1) ∨ (u=1 ∧ v=0)
def rightCap (u v : Fin 5) : Prop := (u=2 ∧ v=3) ∨ (u=3 ∧ v=2)

def G (t : ℕ) : SimpleGraph (V t) where
  Adj u v := (u.1=v.1 ∧ block.Adj u.2 v.2) ∨
    (u.1.val+1=v.1.val ∧ port u.2 v.2) ∨
    (v.1.val+1=u.1.val ∧ port v.2 u.2) ∨
    (u.1=0 ∧ v.1=0 ∧ leftCap u.2 v.2) ∨
    (u.1=Fin.last t ∧ v.1=Fin.last t ∧ rightCap u.2 v.2)
  symm := by
    intro u v h
    rcases h with h | h | h | h | h
    · exact Or.inl ⟨h.1.symm,h.2.symm⟩
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h.2.1,h.1,by
        rcases h.2.2 with h | h <;> [right; left] <;> exact ⟨h.2,h.1⟩⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h.2.1,h.1,by
        rcases h.2.2 with h | h <;> [right; left] <;> exact ⟨h.2,h.1⟩⟩)))
  loopless := by
    intro u h
    rcases h with h | h | h | h | h
    · exact h.2.ne rfl
    · omega
    · omega
    · have := h.2.2
      simp [leftCap] at this
      omega
    · have := h.2.2
      simp [rightCap] at this
      omega

lemma representative_adj (t : ℕ) (i j : Fin (t+1)) (k : Fin 5) :
    (G t).Adj (i,4) (j,k) ↔ i=j ∧ k≠4 := by
  fin_cases k <;> simp [G,block,port,leftCap,rightCap]

lemma representative_degree (t : ℕ) (i : Fin (t+1)) : (G t).degree (i,4) = 4 := by
  have hn : (G t).neighborFinset (i,4) = {(i,0),(i,1),(i,2),(i,3)} := by
    ext ⟨j,k⟩
    rw [mem_neighborFinset,representative_adj]
    fin_cases k <;> simp [Prod.ext_iff,eq_comm]
  rw [← card_neighborFinset_eq_degree,hn]
  simp

def leftNeighbor (t : ℕ) (i : Fin (t+1)) (a b : Fin 5) : V t :=
  if h : i=0 then (i,a) else ((i.pred h).castSucc,b)

def rightNeighbor (t : ℕ) (i : Fin (t+1)) (a b : Fin 5) : V t :=
  if h : i=Fin.last t then (i,a) else ((i.castPred h).succ,b)

def neighbors (t : ℕ) (v : V t) : List (V t) :=
  ![[(v.1,2),(v.1,3),(v.1,4),leftNeighbor t v.1 1 2],
    [(v.1,2),(v.1,3),(v.1,4),leftNeighbor t v.1 0 3],
    [(v.1,0),(v.1,1),(v.1,4),rightNeighbor t v.1 3 0],
    [(v.1,0),(v.1,1),(v.1,4),rightNeighbor t v.1 2 1],
    [(v.1,0),(v.1,1),(v.1,2),(v.1,3)]] v.2

set_option maxHeartbeats 800000 in
lemma adj_neighbors (t : ℕ) (u v : V t) : (G t).Adj u v ↔ v ∈ neighbors t u := by
  rcases u with ⟨i,k⟩
  rcases v with ⟨j,l⟩
  fin_cases k <;> fin_cases l <;>
    simp only [neighbors] <;>
    dsimp only [leftNeighbor,rightNeighbor] <;>
    split_ifs <;>
    simp [G,block,port,leftCap,rightCap,Fin.ext_iff,Prod.ext_iff,
      Fin.val_pred,Fin.coe_castPred,-Fin.val_eq_zero_iff] at * <;>
    (try simp only [Fin.ext_iff,Fin.val_zero,Fin.val_last] at *) <;> omega

set_option maxHeartbeats 400000 in
lemma neighbors_nodup (t : ℕ) (v : V t) : (neighbors t v).Nodup := by
  rcases v with ⟨i,k⟩
  fin_cases k <;>
    simp only [neighbors] <;>
    dsimp only [leftNeighbor,rightNeighbor] <;>
    split_ifs <;>
    simp [Fin.ext_iff,Prod.ext_iff,Fin.val_pred,Fin.coe_castPred,
      -Fin.val_eq_zero_iff] at * <;>
    (try simp only [Fin.ext_iff,Fin.val_zero,Fin.val_last] at *) <;> omega

lemma neighbors_length (t : ℕ) (v : V t) : (neighbors t v).length = 4 := by
  rcases v with ⟨i,k⟩
  fin_cases k <;> rfl

lemma regular (t : ℕ) : (G t).IsRegularOfDegree 4 := by
  intro v
  have hn : (G t).neighborFinset v = (neighbors t v).toFinset := by
    ext w
    simp only [mem_neighborFinset,adj_neighbors,List.mem_toFinset]
  rw [← card_neighborFinset_eq_degree,hn,List.toFinset_card_of_nodup (neighbors_nodup t v)]
  exact neighbors_length t v

lemma even (t : ℕ) : ∀ v, Even ((G t).degree v) := by
  intro v
  have h := regular t v
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at h ⊢
  rw [h]
  decide

lemma connected (t : ℕ) : (G t).Connected := by
  have hrep (i : Fin (t+1)) : (G t).Reachable (0,4) (i,4) := by
    induction i using Fin.induction with
    | zero => exact SimpleGraph.Reachable.rfl
    | succ j ih =>
      have h1 : (G t).Adj (j.castSucc,4) (j.castSucc,2) :=
        (representative_adj t _ _ _).mpr ⟨rfl,by decide⟩
      have h2 : (G t).Adj (j.castSucc,2) (j.succ,0) :=
        Or.inr (Or.inl ⟨rfl,Or.inl ⟨rfl,rfl⟩⟩)
      have h3 : (G t).Adj (j.succ,0) (j.succ,4) :=
        ((representative_adj t _ _ _).mpr ⟨rfl,by decide⟩).symm
      exact ((ih.trans h1.reachable).trans h2.reachable).trans h3.reachable
  have hr (v : V t) : (G t).Reachable (0,4) v := by
    by_cases hv : v.2=4
    · simpa only [← hv,Prod.mk.eta] using hrep v.1
    · exact (hrep v.1).trans (((representative_adj t _ _ _).mpr ⟨rfl,hv⟩).reachable)
  exact {preconnected := fun u v => (hr u).symm.trans (hr v)}

lemma pure_decomposition_exists (t : ℕ) :
    ∃ D : Finset (G t).Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (G t) D := by
  apply even_cycle_decomposition
  intro v
  simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using even t v

abbrev label (t : ℕ) : V t → Fin (t+1) := Prod.fst

lemma cut_zero (t : ℕ) :
    (G t).edgeSet \ (monochromatic (G t) (threshold (label t) 0)).edgeSet = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro e he
  induction e using Sym2.ind with
  | h u v =>
    apply he.2
    refine ⟨he.1,?_⟩
    simp [threshold]

lemma cut_subset (t : ℕ) (j : Fin t) :
    (G t).edgeSet \ (monochromatic (G t) (threshold (label t) j.succ)).edgeSet ⊆
      {s((j.castSucc,2),(j.succ,0)),s((j.castSucc,3),(j.succ,1))} := by
  intro e he
  induction e using Sym2.ind with
  | h u v =>
    have hne : threshold (label t) j.succ u ≠ threshold (label t) j.succ v :=
      fun h => he.2 ⟨he.1,h⟩
    have hn : ¬(u.1.val < j.val+1 ↔ v.1.val < j.val+1) := by
      intro h
      apply hne
      simpa only [threshold,label,Fin.lt_def,Fin.val_succ,decide_eq_decide] using h
    have hfwd (hstep : u.1.val+1=v.1.val) (hp : port u.2 v.2) :
        s(u,v) ∈ ({s((j.castSucc,2),(j.succ,0)),s((j.castSucc,3),(j.succ,1))} : Set (Sym2 (V t))) := by
      have hu : u.1 = j.castSucc := Fin.ext (by simp only [Fin.val_castSucc]; omega)
      have hv : v.1 = j.succ := Fin.ext (by simp only [Fin.val_succ]; omega)
      rcases hp with ⟨ha,hb⟩ | ⟨ha,hb⟩
      · have hU : u = (j.castSucc,2) := Prod.ext hu ha
        have hV : v = (j.succ,0) := Prod.ext hv hb
        simp [hU,hV]
      · have hU : u = (j.castSucc,3) := Prod.ext hu ha
        have hV : v = (j.succ,1) := Prod.ext hv hb
        simp [hU,hV]
    have hback (hstep : v.1.val+1=u.1.val) (hp : port v.2 u.2) :
        s(u,v) ∈ ({s((j.castSucc,2),(j.succ,0)),s((j.castSucc,3),(j.succ,1))} : Set (Sym2 (V t))) := by
      have hu : u.1 = j.succ := Fin.ext (by simp only [Fin.val_succ]; omega)
      have hv : v.1 = j.castSucc := Fin.ext (by simp only [Fin.val_castSucc]; omega)
      rcases hp with ⟨ha,hb⟩ | ⟨ha,hb⟩
      · have hU : u = (j.succ,0) := Prod.ext hu hb
        have hV : v = (j.castSucc,2) := Prod.ext hv ha
        rw [hU,hV]
        exact Or.inl Sym2.eq_swap
      · have hU : u = (j.succ,1) := Prod.ext hu hb
        have hV : v = (j.castSucc,3) := Prod.ext hv ha
        rw [hU,hV]
        exact Or.inr Sym2.eq_swap
    rcases he.1 with h | h | h | h | h
    · exact (hn (by rw [h.1])).elim
    · exact hfwd h.1 h.2
    · exact hback h.1 h.2
    · exact (hn (by rw [h.1,h.2.1])).elim
    · exact (hn (by rw [h.1,h.2.1])).elim

lemma variation_le (t : ℕ) : variation (G t) (label t) ≤ 2*t := by
  unfold variation
  rw [Fin.sum_univ_succ,cut_zero,Set.ncard_empty,zero_add]
  calc
    _ ≤ ∑ j : Fin t, 2 := Finset.sum_le_sum (fun j _ =>
      (Set.ncard_le_ncard (cut_subset t j)).trans (by
        simpa using Set.ncard_insert_le s((j.castSucc,2),(j.succ,0))
          {s((j.castSucc,3),(j.succ,1))}))
    _ = _ := by simp [mul_comm]

/-- A chain of t+1 blocks needs at least t+2 cycle pieces. This is an
all-orders lower bound for the actual simple graph defined above. -/
theorem decomposition_lower (t : ℕ) (D : Finset (G t).Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition (G t) D) : t+2 ≤ D.card := by
  have hb := degree_budget (label t) (fun i => (i,4)) (fun _ => rfl) D hc hd
  simp only [representative_degree,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    smul_eq_mul] at hb
  have hv := variation_le t
  omega

theorem cycle_edge_decomposition_lower (t : ℕ) (D : Finset (G t).Subgraph)
    (hc : ∀ H ∈ D, IsCycleOrEdge H.coe)
    (hd : IsDecomposition (G t) D) : t+2 ≤ D.card := by
  obtain ⟨E,hcE,hdE,hcard⟩ := refine_even_decomposition (G t) (by
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using even t v)
    D hc hd
  exact (decomposition_lower t E hcE hdE).trans hcard

end Erdos184.TwoSwitchChain
