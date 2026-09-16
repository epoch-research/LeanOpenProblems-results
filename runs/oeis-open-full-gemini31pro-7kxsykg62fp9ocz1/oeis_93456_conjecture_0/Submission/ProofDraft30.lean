import FormalConjectures.Util.ProblemImports
open Nat Finset

def a (n : ℕ) : ℕ :=
  let L := n.choose 2 + 1
  let R := (n + 1).choose 2
  let is_composite (k : ℕ) : Prop := 1 < k ∧ ¬ k.Prime
  (Icc L R).filter is_composite |>.prod id

lemma padicValNat_prod {α : Type} [DecidableEq α] (p : ℕ) [Fact p.Prime] (s : Finset α) (f : α → ℕ)
  (h : ∀ x ∈ s, f x ≠ 0) :
  padicValNat p (∏ x ∈ s, f x) = ∑ x ∈ s, padicValNat p (f x) := by
  induction' s using Finset.induction_on with a s has ih
  · simp [padicValNat.one]
  · rw [prod_insert has, sum_insert has]
    rw [padicValNat.mul]
    · rw [ih]
      intros x hx
      exact h x (mem_insert_of_mem hx)
    · exact h a (mem_insert_self a s)
    · apply prod_ne_zero_iff.mpr
      intros x hx
      exact h x (mem_insert_of_mem hx)
