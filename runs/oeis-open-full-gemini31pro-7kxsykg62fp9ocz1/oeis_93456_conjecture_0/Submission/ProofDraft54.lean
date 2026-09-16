import FormalConjectures.Util.ProblemImports
open Nat Finset

lemma padicValNat_prod {α : Type} [DecidableEq α] (p : ℕ) [Fact p.Prime] (s : Finset α) (f : α → ℕ)
  (h : ∀ x ∈ s, f x ≠ 0) :
  padicValNat p (∏ x ∈ s, f x) = ∑ x ∈ s, padicValNat p (f x) := by
  induction' s using Finset.induction_on with b s has ih
  · simp [padicValNat.one]
  · rw [prod_insert has, sum_insert has]
    rw [padicValNat.mul]
    · rw [ih]
      intros x hx
      exact h x (mem_insert_of_mem hx)
    · exact h b (mem_insert_self b s)
    · apply prod_ne_zero_iff.mpr
      intros x hx
      exact h x (mem_insert_of_mem hx)
