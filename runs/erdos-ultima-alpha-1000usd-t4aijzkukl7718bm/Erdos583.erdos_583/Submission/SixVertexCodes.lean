import Submission.Work

/-! Finite graph encoding and explicit path-partition certificates. -/
namespace Erdos583SixVertexCodesDevelopment
open SimpleGraph Erdos583Work Erdos583Work.QuotaTrails
set_option maxHeartbeats 3000000
set_option Elab.async false

def edgeIndex (a b : Fin 6) : ℕ :=
  let x := min a.val b.val
  let y := max a.val b.val
  x*(11-x)/2+y-x-1

def graph (c : BitVec 15) : SimpleGraph (Fin 6) where
  Adj a b := a ≠ b ∧ c.getLsbD (edgeIndex a b)=true
  symm := by
    intro a b h
    exact ⟨h.1.symm,by simpa only [edgeIndex,min_comm,max_comm] using h.2⟩
  loopless := by intro a h; exact h.1 rfl

instance (c : BitVec 15) : DecidableRel (graph c).Adj := fun a b ↦
  inferInstanceAs (Decidable (a ≠ b ∧ c.getLsbD (edgeIndex a b)=true))

lemma graph_surjective (G : SimpleGraph (Fin 6)) : ∃ c : BitVec 15, graph c=G := by
  classical
  let c : BitVec 15 := BitVec.ofBoolListLE [
    decide (G.Adj 0 1),decide (G.Adj 0 2),decide (G.Adj 0 3),decide (G.Adj 0 4),decide (G.Adj 0 5),
    decide (G.Adj 1 2),decide (G.Adj 1 3),decide (G.Adj 1 4),decide (G.Adj 1 5),
    decide (G.Adj 2 3),decide (G.Adj 2 4),decide (G.Adj 2 5),
    decide (G.Adj 3 4),decide (G.Adj 3 5),decide (G.Adj 4 5)]
  refine ⟨c,?_⟩
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [graph,edgeIndex,c,BitVec.getLsbD_ofBoolListLE,G.adj_comm]
  all_goals exact G.adj_comm _ _

def Residual (c : BitVec 15) : Prop :=
  (∀ v, (graph c).degree v=2 ∨ (graph c).degree v=4) ∧
  (∀ v a b, (graph c).degree v=2 → (graph c).Adj v a →
    (graph c).Adj v b → a ≠ b → (graph c).Adj a b) ∧
  ∀ v w, (graph c).Adj v w → ¬((graph c).degree v=2 ∧ (graph c).degree w=2)

instance (c : BitVec 15) : Decidable (Residual c) := by unfold Residual; infer_instance

def listEdges {V : Type*} : List V → List (Sym2 V)
  | a::b::l => s(a,b)::listEdges (b::l)
  | _ => []

lemma walk_of_vertices {V : Type*} {G : SimpleGraph V} {a : V} (l : List V)
    (he : ∀ e ∈ listEdges (a::l), e ∈ G.edgeSet) :
    ∃ b : V, ∃ P : G.Walk a b,
      P.support=a::l ∧ P.edges=listEdges (a::l) := by
  induction l generalizing a with
  | nil => exact ⟨a,Walk.nil,rfl,rfl⟩
  | cons b l ih =>
    have hab : G.Adj a b := he s(a,b) (by simp [listEdges])
    obtain ⟨z,Q,hQs,hQe⟩ := ih (a := b) (fun e he' ↦ he e (by simp only [listEdges,List.mem_cons]; exact Or.inr he'))
    exact ⟨z,Walk.cons hab Q,by simp [hQs],by simp [listEdges,hQe]⟩

def Valid {V : Type*} (G : SimpleGraph V) (p : Fin 3 → List V) : Prop :=
  (∀ i, p i ≠ [] ∧ (p i).Nodup) ∧
  (∀ i j, i ≠ j → ∀ a b,
    s(a,b) ∈ listEdges (p i) → s(a,b) ∉ listEdges (p j)) ∧
  ∀ a b, G.Adj a b ↔ ∃ i, s(a,b) ∈ listEdges (p i)

instance (c : BitVec 15) (p : Fin 3 → List (Fin 6)) : Decidable (Valid (graph c) p) := by
  unfold Valid
  infer_instance

lemma valid_partition {V : Type*} [Fintype V] {G : SimpleGraph V}
    {p : Fin 3 → List V} (hv : Valid G p) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ 3 := by
  classical
  have hwalk (i : Fin 3) : ∃ a b : V, ∃ P : G.Walk a b,
      P.IsPath ∧ P.edges=listEdges (p i) := by
    have hne := (hv.1 i).1
    have hn := (hv.1 i).2
    cases he : p i with
    | nil => exact (hne he).elim
    | cons a l =>
      have hedges : ∀ e ∈ listEdges (a::l), e ∈ G.edgeSet := by
        intro e hm
        induction e using Sym2.ind with
        | h x y =>
          exact (hv.2.2 x y).mpr ⟨i,by rwa [he]⟩
      obtain ⟨b,P,hPs,hPe⟩ := walk_of_vertices l hedges
      have hp : P.IsPath := by rw [Walk.isPath_def,hPs]; rwa [he] at hn
      exact ⟨a,b,P,hp,hPe⟩
  choose a b P hp he using hwalk
  let T : TrailFamily G 3 := {
    start := a
    finish := b
    walk := P
    isTrail := fun i ↦ (hp i).isTrail
    disjoint := by
      intro i j hij
      apply Set.disjoint_left.mpr
      intro e hi hj
      induction e using Sym2.ind with
      | h x y =>
        rw [Walk.mem_edges_toSubgraph,he] at hi hj
        exact hv.2.1 i j hij x y hi hj
    cover := by
      intro e
      induction e using Sym2.ind with
      | h x y =>
        simp only [Walk.mem_edges_toSubgraph,he,mem_edgeSet]
        exact hv.2.2 x y
  }
  exact MatchingAppend.path_family_partition T hp

end Erdos583SixVertexCodesDevelopment
