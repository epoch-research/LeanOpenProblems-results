import Mathlib.Data.Nat.Basic

/-! Balanced finite lookup trees, with independently checked values at leaves. -/
namespace Erdos184Work.FiniteCaseLookup
universe u

inductive Table (α : Type u) where
  | empty
  | entry (key : ℕ) (value : α)
  | branch (pivot : ℕ) (left right : Table α)

namespace Table
variable {α : Type u}

def lookup : Table α → ℕ → Option α
  | .empty, _ => none
  | .entry k a, j => if j = k then some a else none
  | .branch k L R, j => if j < k then lookup L j else lookup R j

def Correct (f : α → ℕ) : Table α → Prop
  | .empty => True
  | .entry k a => f a = k
  | .branch _ L R => Correct f L ∧ Correct f R

instance correctDecidable (f : α → ℕ) : (T : Table α) → Decidable (Correct f T)
  | .empty => isTrue trivial
  | .entry k a => inferInstanceAs (Decidable (f a = k))
  | .branch _ L R =>
    letI := correctDecidable f L
    letI := correctDecidable f R
    inferInstanceAs (Decidable (Correct f L ∧ Correct f R))

lemma lookup_sound (f : α → ℕ) (T : Table α) (hT : Correct f T)
    (j : ℕ) {a : α} (h : lookup T j = some a) : f a = j := by
  induction T generalizing a with
  | empty => simp [lookup] at h
  | entry k b =>
    by_cases hj : j = k
    · simp only [lookup, hj, ite_true, Option.some.injEq] at h
      subst a
      exact hT.trans hj.symm
    · simp [lookup, hj] at h
  | branch k L R ihL ihR =>
    by_cases hj : j < k
    · apply ihL hT.1
      simpa only [lookup, hj, ite_true] using h
    · apply ihR hT.2
      simpa only [lookup, hj, ite_false] using h

lemma exists_of_isSome (f : α → ℕ) (T : Table α) (hT : Correct f T)
    (j : ℕ) (h : (lookup T j).isSome = true) :
    ∃ a, lookup T j = some a ∧ f a = j := by
  cases he : lookup T j with
  | none => simp only [he, Option.isSome_none, Bool.false_eq_true] at h
  | some a => exact ⟨a,rfl,lookup_sound f T hT j he⟩

#print axioms lookup_sound
#print axioms exists_of_isSome
end Table
end Erdos184Work.FiniteCaseLookup
