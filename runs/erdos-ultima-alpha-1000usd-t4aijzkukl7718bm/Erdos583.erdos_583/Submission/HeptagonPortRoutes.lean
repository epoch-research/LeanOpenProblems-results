import Submission.Work

/-! Four paths in K₇ minus two edges, with the four missing-edge incidences at distinct path starts. -/
namespace Erdos583HeptagonPortRoutesDevelopment
open SimpleGraph Erdos583Work
set_option maxHeartbeats 2000000

def deleted (c : Bool) : Finset (Sym2 (Fin 7)) :=
  if c then {s(0,1),s(0,2)} else {s(0,1),s(2,3)}

def graph (c : Bool) : SimpleGraph (Fin 7) where
  Adj x y := x ≠ y ∧ s(x,y) ∉ deleted c
  symm := by
    intro x y h
    exact ⟨h.1.symm,by simpa only [Sym2.eq_swap (a := y) (b := x)] using h.2⟩
  loopless x h := h.1 rfl

instance (c : Bool) : DecidableRel (graph c).Adj := fun x y ↦
  inferInstanceAs (Decidable (x ≠ y ∧ s(x,y) ∉ deleted c))

def start (c : Bool) : Fin 4 → Fin 7 := if c then ![0,0,1,2] else ![0,1,2,3]
def finish (c : Bool) : Fin 4 → Fin 7 := if c then ![6,6,4,4] else ![6,6,1,1]

def walk (c : Bool) (i : Fin 4) : (graph c).Walk (start c i) (finish c i) := by
  cases c
  · exact Fin.cases (.cons (show (graph false).Adj 0 2 by decide) (.cons (show (graph false).Adj 2 1 by decide) (.cons (show (graph false).Adj 1 3 by decide) (.cons (show (graph false).Adj 3 4 by decide) (.cons (show (graph false).Adj 4 5 by decide) (.cons (show (graph false).Adj 5 6 by decide) (.nil))))))) (Fin.cases (.cons (show (graph false).Adj 1 4 by decide) (.cons (show (graph false).Adj 4 0 by decide) (.cons (show (graph false).Adj 0 3 by decide) (.cons (show (graph false).Adj 3 5 by decide) (.cons (show (graph false).Adj 5 2 by decide) (.cons (show (graph false).Adj 2 6 by decide) (.nil))))))) (Fin.cases (.cons (show (graph false).Adj 2 4 by decide) (.cons (show (graph false).Adj 4 6 by decide) (.cons (show (graph false).Adj 6 0 by decide) (.cons (show (graph false).Adj 0 5 by decide) (.cons (show (graph false).Adj 5 1 by decide) (.nil)))))) (Fin.cases (.cons (show (graph false).Adj 3 6 by decide) (.cons (show (graph false).Adj 6 1 by decide) (.nil))) (fun i ↦ Fin.elim0 i)))) i
  · exact Fin.cases (.cons (show (graph true).Adj 0 3 by decide) (.cons (show (graph true).Adj 3 1 by decide) (.cons (show (graph true).Adj 1 2 by decide) (.cons (show (graph true).Adj 2 4 by decide) (.cons (show (graph true).Adj 4 5 by decide) (.cons (show (graph true).Adj 5 6 by decide) (.nil))))))) (Fin.cases (.cons (show (graph true).Adj 0 4 by decide) (.cons (show (graph true).Adj 4 1 by decide) (.cons (show (graph true).Adj 1 5 by decide) (.cons (show (graph true).Adj 5 2 by decide) (.cons (show (graph true).Adj 2 3 by decide) (.cons (show (graph true).Adj 3 6 by decide) (.nil))))))) (Fin.cases (.cons (show (graph true).Adj 1 6 by decide) (.cons (show (graph true).Adj 6 0 by decide) (.cons (show (graph true).Adj 0 5 by decide) (.cons (show (graph true).Adj 5 3 by decide) (.cons (show (graph true).Adj 3 4 by decide) (.nil)))))) (Fin.cases (.cons (show (graph true).Adj 2 6 by decide) (.cons (show (graph true).Adj 6 4 by decide) (.nil))) (fun i ↦ Fin.elim0 i)))) i

lemma walk_isPath (c : Bool) (i : Fin 4) : (walk c i).IsPath := by
  cases c <;> fin_cases i <;> rw [Walk.isPath_def] <;> decide

lemma finite_disjoint : ∀ c : Bool, ∀ i j : Fin 4, ∀ x y : Fin 7,
    i ≠ j → s(x,y) ∈ (walk c i).edges → s(x,y) ∉ (walk c j).edges := by
  decide

lemma walk_disjoint (c : Bool) {i j : Fin 4} (hij : i ≠ j) :
    Disjoint (walk c i).toSubgraph.edgeSet (walk c j).toSubgraph.edgeSet := by
  apply Set.disjoint_left.mpr
  intro e he hf
  induction e using Sym2.ind with
  | h x y =>
    exact finite_disjoint c i j x y hij ((walk c i).mem_edges_toSubgraph.mp he)
      ((walk c j).mem_edges_toSubgraph.mp hf)

lemma finite_cover : ∀ c : Bool, ∀ x y : Fin 7,
    (graph c).Adj x y ↔ ∃ i : Fin 4, s(x,y) ∈ (walk c i).edges := by
  decide

lemma walk_cover (c : Bool) : ∀ e, e ∈ (graph c).edgeSet ↔ ∃ i, e ∈ (walk c i).toSubgraph.edgeSet := by
  intro e
  induction e using Sym2.ind with
  | h x y =>
    simpa only [Walk.mem_edges_toSubgraph] using finite_cover c x y

lemma port_degree (c : Bool) (v : Fin 7) :
    Fintype.card {i : Fin 4 // start c i=v}+(graph c).degree v=6 := by
  cases c <;> fin_cases v <;> decide

end Erdos583HeptagonPortRoutesDevelopment
