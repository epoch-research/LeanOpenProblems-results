import Submission.OrderNormalizationTheory

/-! Explicit normalized cyclic-word tables up to six markers. Completeness is
checked against every recursive marked order by ordinary kernel reduction. -/

namespace Erdos184Work.SmallWordTables
open CycleSegments SmallOrderNormalization
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

def words0 : Finset (Fin 2 → Fin 2) :=
  {![0,1]}

lemma complete0 : ∀ o : Marked.Order 0, (normalized 0 o).vertex ∈ words0 := by
  decide +kernel

def words1 : Finset (Fin 3 → Fin 3) :=
  {![0,1,2]}

lemma complete1 : ∀ o : Marked.Order 1, (normalized 1 o).vertex ∈ words1 := by
  decide +kernel

def words2 : Finset (Fin 4 → Fin 4) :=
  {![0,1,2,3],
    ![0,1,3,2],
    ![0,2,1,3]}

lemma complete2 : ∀ o : Marked.Order 2, (normalized 2 o).vertex ∈ words2 := by
  decide +kernel

def words3 : Finset (Fin 5 → Fin 5) :=
  {![0,1,2,3,4],
    ![0,1,2,4,3],
    ![0,1,3,2,4],
    ![0,1,3,4,2],
    ![0,1,4,2,3],
    ![0,1,4,3,2],
    ![0,2,1,3,4],
    ![0,2,1,4,3],
    ![0,2,3,1,4],
    ![0,2,4,1,3],
    ![0,3,1,2,4],
    ![0,3,2,1,4]}

lemma complete3 : ∀ o : Marked.Order 3, (normalized 3 o).vertex ∈ words3 := by
  decide +kernel

def words4 : Finset (Fin 6 → Fin 6) :=
  {![0,1,2,3,4,5],
    ![0,1,2,3,5,4],
    ![0,1,2,4,3,5],
    ![0,1,2,4,5,3],
    ![0,1,2,5,3,4],
    ![0,1,2,5,4,3],
    ![0,1,3,2,4,5],
    ![0,1,3,2,5,4],
    ![0,1,3,4,2,5],
    ![0,1,3,4,5,2],
    ![0,1,3,5,2,4],
    ![0,1,3,5,4,2],
    ![0,1,4,2,3,5],
    ![0,1,4,2,5,3],
    ![0,1,4,3,2,5],
    ![0,1,4,3,5,2],
    ![0,1,4,5,2,3],
    ![0,1,4,5,3,2],
    ![0,1,5,2,3,4],
    ![0,1,5,2,4,3],
    ![0,1,5,3,2,4],
    ![0,1,5,3,4,2],
    ![0,1,5,4,2,3],
    ![0,1,5,4,3,2],
    ![0,2,1,3,4,5],
    ![0,2,1,3,5,4],
    ![0,2,1,4,3,5],
    ![0,2,1,4,5,3],
    ![0,2,1,5,3,4],
    ![0,2,1,5,4,3],
    ![0,2,3,1,4,5],
    ![0,2,3,1,5,4],
    ![0,2,3,4,1,5],
    ![0,2,3,5,1,4],
    ![0,2,4,1,3,5],
    ![0,2,4,1,5,3],
    ![0,2,4,3,1,5],
    ![0,2,4,5,1,3],
    ![0,2,5,1,3,4],
    ![0,2,5,1,4,3],
    ![0,2,5,3,1,4],
    ![0,2,5,4,1,3],
    ![0,3,1,2,4,5],
    ![0,3,1,2,5,4],
    ![0,3,1,4,2,5],
    ![0,3,1,5,2,4],
    ![0,3,2,1,4,5],
    ![0,3,2,1,5,4],
    ![0,3,2,4,1,5],
    ![0,3,2,5,1,4],
    ![0,3,4,1,2,5],
    ![0,3,4,2,1,5],
    ![0,3,5,1,2,4],
    ![0,3,5,2,1,4],
    ![0,4,1,2,3,5],
    ![0,4,1,3,2,5],
    ![0,4,2,1,3,5],
    ![0,4,2,3,1,5],
    ![0,4,3,1,2,5],
    ![0,4,3,2,1,5]}

lemma complete4 : ∀ o : Marked.Order 4, (normalized 4 o).vertex ∈ words4 := by
  decide +kernel

def words : (n : ℕ) → Finset (Fin (n+2) → Fin (n+2))
  | 0 => words0
  | 1 => words1
  | 2 => words2
  | 3 => words3
  | 4 => words4
  | _+5 => ∅

lemma complete {n : ℕ} (hn : n ≤ 4) (o : Marked.Order n) :
    (normalized n o).vertex ∈ words n := by
  interval_cases n
  · exact complete0 o
  · exact complete1 o
  · exact complete2 o
  · exact complete3 o
  · exact complete4 o

#print axioms complete4
end Erdos184Work.SmallWordTables
