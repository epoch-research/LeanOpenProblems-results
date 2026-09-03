import Submission.FiniteCaseLookup

/-! Leafwise certificates for balanced finite lookup tables. -/
namespace Erdos184Work.FiniteCaseLookup.Table
universe u
variable {α : Type u}

def Every (P : ℕ → α → Prop) : Table α → Prop
  | .empty => True
  | .entry k a => P k a
  | .branch _ L R => Every P L ∧ Every P R

instance everyDecidable (P : ℕ → α → Prop) [∀ k a, Decidable (P k a)] :
    (T : Table α) → Decidable (Every P T)
  | .empty => isTrue trivial
  | .entry k a => inferInstanceAs (Decidable (P k a))
  | .branch _ L R =>
    letI := everyDecidable P L
    letI := everyDecidable P R
    inferInstanceAs (Decidable (Every P L ∧ Every P R))

lemma lookup_every (P : ℕ → α → Prop) (T : Table α) (hT : Every P T)
    (j : ℕ) {a : α} (h : T.lookup j = some a) : P j a := by
  induction T generalizing a with
  | empty => simp [lookup] at h
  | entry k b =>
    by_cases hj : j = k
    · simp only [lookup,hj,ite_true,Option.some.injEq] at h
      subst a
      exact hj.symm ▸ hT
    · simp [lookup,hj] at h
  | branch k L R ihL ihR =>
    by_cases hj : j < k
    · apply ihL hT.1
      simpa only [lookup,hj,ite_true] using h
    · apply ihR hT.2
      simpa only [lookup,hj,ite_false] using h

#print axioms lookup_every
end Erdos184Work.FiniteCaseLookup.Table
