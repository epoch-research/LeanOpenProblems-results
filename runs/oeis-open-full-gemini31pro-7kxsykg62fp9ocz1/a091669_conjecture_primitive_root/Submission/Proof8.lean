import Mathlib
import Submission.Spec

open Nat BigOperators

lemma dvd_prod_of_dvd {α β : Type} [CommMonoid α] {s : Finset β} {f : β → α} {p : α} (h : ∀ x ∈ s, p ∣ f x) :
  p ^ s.card ∣ s.prod f := by
  classical
  induction' s using Finset.induction_on with a s ha ih
  · simp
  · rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_add, pow_one, mul_comm]
    apply mul_dvd_mul
    · exact h a (Finset.mem_insert_self a s)
    · apply ih
      intro x hx
      exact h x (Finset.mem_insert_of_mem hx)
