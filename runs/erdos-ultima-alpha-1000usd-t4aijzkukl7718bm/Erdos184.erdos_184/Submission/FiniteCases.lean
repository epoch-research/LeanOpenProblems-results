import Mathlib.Data.Fin.Basic

/-! Small numeral-indexed case reductions with abstract dependent motives. -/
namespace Erdos184Work.FiniteCases
universe u

lemma cases2_one {M : Fin 2 → Sort u} (z : M 0) (s : ∀ i : Fin 1, M i.succ) :
    Fin.cases (motive := M) z s (1 : Fin 2) = s 0 := rfl
lemma cases3_one {M : Fin 3 → Sort u} (z : M 0) (s : ∀ i : Fin 2, M i.succ) :
    Fin.cases (motive := M) z s (1 : Fin 3) = s 0 := rfl
lemma cases3_two {M : Fin 3 → Sort u} (z : M 0) (s : ∀ i : Fin 2, M i.succ) :
    Fin.cases (motive := M) z s (2 : Fin 3) = s 1 := rfl
lemma cases4_one {M : Fin 4 → Sort u} (z : M 0) (s : ∀ i : Fin 3, M i.succ) :
    Fin.cases (motive := M) z s (1 : Fin 4) = s 0 := rfl
lemma cases4_two {M : Fin 4 → Sort u} (z : M 0) (s : ∀ i : Fin 3, M i.succ) :
    Fin.cases (motive := M) z s (2 : Fin 4) = s 1 := rfl
lemma cases4_three {M : Fin 4 → Sort u} (z : M 0) (s : ∀ i : Fin 3, M i.succ) :
    Fin.cases (motive := M) z s (3 : Fin 4) = s 2 := rfl

#print axioms cases4_two
#print axioms cases4_three
end Erdos184Work.FiniteCases
