import Submission.Work
/-! A small diagnostic: merger intersection bounds alone do not force paths. -/
open SimpleGraph Erdos583Work Erdos583Work.QuotaTrails
namespace Erdos583MergeObstructionCheck
abbrev G : SimpleGraph (Fin 5) := ⊤
def p₀ : G.Walk 0 1 :=
  .cons (show G.Adj 0 2 by decide) (.cons (show G.Adj 2 3 by decide)
    (.cons (show G.Adj 3 0 by decide) (.cons (show G.Adj 0 1 by decide) .nil)))
def p₁ : G.Walk 1 2 :=
  .cons (show G.Adj 1 3 by decide) (.cons (show G.Adj 3 4 by decide)
    (.cons (show G.Adj 4 2 by decide) .nil))
def p₂ : G.Walk 2 0 :=
  .cons (show G.Adj 2 1 by decide) (.cons (show G.Adj 1 4 by decide)
    (.cons (show G.Adj 4 0 by decide) .nil))
lemma trail₀ : p₀.IsTrail := by
  rw [Walk.isTrail_def]
  decide
lemma trail₁ : p₁.IsTrail := by
  rw [Walk.isTrail_def]
  decide
lemma trail₂ : p₂.IsTrail := by
  rw [Walk.isTrail_def]
  decide
lemma nonpath₀ : ¬p₀.IsPath := by
  rw [Walk.isPath_def]
  decide

def starts : Fin 3 → Fin 5 := ![0,1,2]
def finishes : Fin 3 → Fin 5 := ![1,2,0]
def walks : (i : Fin 3) → G.Walk (starts i) (finishes i)
  | 0 => p₀
  | 1 => p₁
  | 2 => p₂

def family : TrailFamily G 3 where
  start := starts
  finish := finishes
  walk := walks
  isTrail := by intro i; fin_cases i <;> first | exact trail₀ | exact trail₁ | exact trail₂
  disjoint := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> try contradiction
    all_goals simp [walks,p₀,p₁,p₂,starts,finishes,Set.disjoint_left]
  cover := by
    intro e
    induction e using Sym2.ind with
    | h a b =>
      fin_cases a <;> fin_cases b <;>
        simp [walks,p₀,p₁,p₂,starts,finishes,Fin.exists_fin_succ,G]

lemma all_nonempty : ∀ i, ¬(family.walk i).Nil := by
  intro i
  fin_cases i <;> simp [family,walks,p₀,p₁,p₂]
lemma some_nonpath : ∃ i, ¬(family.walk i).IsPath := ⟨0,nonpath₀⟩
lemma no_closed : ∀ i, family.start i ≠ family.finish i := by intro i; fin_cases i <;> decide
lemma intersections : ∀ i j, i ≠ j →
    ((family.walk i).toSubgraph.verts ∩ (family.walk j).toSubgraph.verts).ncard = 3 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals
    simp [family,walks,p₀,p₁,p₂,starts,finishes,Set.ncard_eq_toFinset_card']

lemma exact_budget : (3 : ℕ) = ⌈(Fintype.card (Fin 5) : ℚ)/2⌉₊ := by norm_num

/-- Even at the conjectured budget, no nil members and large pairwise vertex
intersections do not force a particular trail partition to be a path partition.
This example does not satisfy the global maximum-score hypothesis. -/
theorem intersection_conditions_insufficient :
    ∃ T : TrailFamily G 3,
      (∀ i, ¬(T.walk i).Nil) ∧
      (∀ i, T.start i ≠ T.finish i) ∧
      (∀ i j, i ≠ j → 2 ≤ ((T.walk i).toSubgraph.verts ∩
        (T.walk j).toSubgraph.verts).ncard) ∧
      (∃ i, ¬(T.walk i).IsPath) := by
  refine ⟨family,all_nonempty,no_closed,?_,some_nonpath⟩
  intro i j hij
  rw [intersections i j hij]
  decide

#print axioms intersection_conditions_insufficient
end Erdos583MergeObstructionCheck
