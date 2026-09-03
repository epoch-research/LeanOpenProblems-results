import Submission.PureSevenRowModel
namespace Erdos184Work.PureSevenRowModel
lemma rows_at0 (a0 a1 a2 a3 a4 a5 x : Fin 60) : rows a0 a1 a2 a3 a4 a5 x 0 = a0 := rfl
lemma rows_at1 (a0 a1 a2 a3 a4 a5 x : Fin 60) : rows a0 a1 a2 a3 a4 a5 x 1 = a1 := rfl
lemma rows_at2 (a0 a1 a2 a3 a4 a5 x : Fin 60) : rows a0 a1 a2 a3 a4 a5 x 2 = a2 := rfl
lemma rows_at3 (a0 a1 a2 a3 a4 a5 x : Fin 60) : rows a0 a1 a2 a3 a4 a5 x 3 = a3 := rfl
lemma rows_at4 (a0 a1 a2 a3 a4 a5 x : Fin 60) : rows a0 a1 a2 a3 a4 a5 x 4 = a4 := rfl
lemma rows_at5 (a0 a1 a2 a3 a4 a5 x : Fin 60) : rows a0 a1 a2 a3 a4 a5 x 5 = a5 := rfl
lemma rows_last_irrel (a0 a1 a2 a3 a4 a5 x y : Fin 60) (i : Fin 6) :
    rows a0 a1 a2 a3 a4 a5 x i.castSucc = rows a0 a1 a2 a3 a4 a5 y i.castSucc := by
  fin_cases i
  · exact (rows_at0 a0 a1 a2 a3 a4 a5 x).trans (rows_at0 a0 a1 a2 a3 a4 a5 y).symm
  · exact (rows_at1 a0 a1 a2 a3 a4 a5 x).trans (rows_at1 a0 a1 a2 a3 a4 a5 y).symm
  · exact (rows_at2 a0 a1 a2 a3 a4 a5 x).trans (rows_at2 a0 a1 a2 a3 a4 a5 y).symm
  · exact (rows_at3 a0 a1 a2 a3 a4 a5 x).trans (rows_at3 a0 a1 a2 a3 a4 a5 y).symm
  · exact (rows_at4 a0 a1 a2 a3 a4 a5 x).trans (rows_at4 a0 a1 a2 a3 a4 a5 y).symm
  · exact (rows_at5 a0 a1 a2 a3 a4 a5 x).trans (rows_at5 a0 a1 a2 a3 a4 a5 y).symm
#print axioms rows_last_irrel
end Erdos184Work.PureSevenRowModel
