import FormalConjecturesUtil

/-! A square packing with quadratically many pieces and no clean ring intersections.
This is an obstruction to a local strategy, not a counterexample to Erdős Problem 184. -/

open SimpleGraph
namespace Erdos184Grid

variable {A B : Type*}

def gridGraph (A B : Type*) := completeBipartiteGraph (A × Bool) (B × Bool)

def gridCycle (i : A) (j : B) :
    (gridGraph A B).Walk (.inl (i, false)) (.inl (i, false)) :=
  .cons (v := Sum.inr (j, false)) (by simp [gridGraph])
    (.cons (v := Sum.inl (i, true)) (by simp [gridGraph])
      (.cons (v := Sum.inr (j, true)) (by simp [gridGraph])
        (.cons (by simp [gridGraph]) .nil)))

lemma gridCycle_isCycle (i : A) (j : B) : (gridCycle i j).IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  simp [gridCycle]

lemma gridCycle_length (i : A) (j : B) : (gridCycle i j).length = 4 := rfl

lemma gridCycle_cross_mem (i a : A) (j b : B) (x y : Bool) :
    s(Sum.inl (a,x), Sum.inr (b,y)) ∈ (gridCycle i j).edges ↔ a = i ∧ b = j := by
  cases x <;> cases y <;> simp [gridCycle, eq_comm, and_comm]

lemma gridCycle_edge_mem_iff (i : A) (j : B) (e : Sym2 ((A × Bool) ⊕ (B × Bool))) :
    e ∈ (gridCycle i j).edges ↔
      ∃ x y : Bool, e = s(Sum.inl (i,x), Sum.inr (j,y)) := by
  simp only [gridCycle, Walk.edges_cons, Walk.edges_nil, List.mem_cons,
    List.not_mem_nil, or_false, Bool.exists_bool]
  rw [Sym2.eq_swap (a := Sum.inr (j,false)) (b := Sum.inl (i,true)),
    Sym2.eq_swap (a := Sum.inr (j,true)) (b := Sum.inl (i,false))]
  tauto

lemma gridCycle_subgraph_injective : Function.Injective
    (fun p : A × B => (gridCycle p.1 p.2).toSubgraph) := by
  intro p q heq
  have he : s(Sum.inl (p.1,false), Sum.inr (p.2,false)) ∈ (gridCycle p.1 p.2).toSubgraph.edgeSet := by
    apply (gridCycle p.1 p.2).mem_edges_toSubgraph.mpr
    exact (gridCycle_cross_mem _ _ _ _ _ _).mpr ⟨rfl,rfl⟩
  dsimp only at heq
  rw [heq] at he
  have h := (gridCycle_cross_mem q.1 p.1 q.2 p.2 false false).mp
    ((gridCycle q.1 q.2).mem_edges_toSubgraph.mp he)
  exact Prod.ext h.1 h.2

lemma gridCycle_disjoint (p q : A × B) (hne : p ≠ q) :
    (gridCycle p.1 p.2).edges.Disjoint (gridCycle q.1 q.2).edges := by
  intro e hep heq
  obtain ⟨x,y,rfl⟩ := (gridCycle_edge_mem_iff _ _ _).mp hep
  have h := (gridCycle_cross_mem q.1 p.1 q.2 p.2 x y).mp heq
  exact hne (Prod.ext h.1 h.2)

def flipVertex : (A × Bool) ⊕ (B × Bool) → (A × Bool) ⊕ (B × Bool)
  | .inl (i,b) => .inl (i,!b)
  | .inr (j,b) => .inr (j,!b)

lemma flipVertex_ne (v : (A × Bool) ⊕ (B × Bool)) : flipVertex v ≠ v := by
  rcases v with ⟨i,b⟩ | ⟨j,b⟩ <;> cases b <;> simp [flipVertex]

lemma gridCycle_flip_mem (i : A) (j : B) (v : (A × Bool) ⊕ (B × Bool))
    (hv : v ∈ (gridCycle i j).support) : flipVertex v ∈ (gridCycle i j).support := by
  rcases v with ⟨a,b⟩ | ⟨a,b⟩ <;> cases b <;>
    simp_all [gridCycle, flipVertex]

lemma gridCycle_inter_not_singleton (p q : A × B) (v : (A × Bool) ⊕ (B × Bool))
    (hp : v ∈ (gridCycle p.1 p.2).support) (hq : v ∈ (gridCycle q.1 q.2).support) :
    ¬ (∀ x, x ∈ (gridCycle p.1 p.2).support → x ∈ (gridCycle q.1 q.2).support → x = v) := by
  intro h
  exact flipVertex_ne v (h _ (gridCycle_flip_mem _ _ _ hp) (gridCycle_flip_mem _ _ _ hq))

#print axioms gridCycle_inter_not_singleton
end Erdos184Grid
