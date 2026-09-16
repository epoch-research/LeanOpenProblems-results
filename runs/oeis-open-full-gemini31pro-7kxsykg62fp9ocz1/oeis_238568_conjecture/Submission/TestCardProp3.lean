import FormalConjectures.Util.ProblemImports
import Submission.Spec

open Finset Nat

lemma pi_fn_finite (n : ℕ) : Finite {p // Nat.Prime p ∧ p ≤ n} := by
  have : Fintype {p // Nat.Prime p ∧ p ≤ n} := by
    apply Fintype.ofFinset (Finset.filter Nat.Prime (Finset.Iic n))
    intro x
    simp only [mem_filter, mem_Iic]
    exact and_comm
  exact Finite.of_fintype _

lemma pi_fn_eq_card (n : ℕ) : pi_fn n = (Finset.filter Nat.Prime (Finset.Iic n)).card := by
  let s := Finset.filter Nat.Prime (Finset.Iic n)
  have hF : Fintype {p // Nat.Prime p ∧ p ≤ n} := by
    apply Fintype.ofFinset s
    intro x
    simp only [s, mem_filter, mem_Iic]
    exact and_comm
  unfold pi_fn
  rw [Nat.card_eq_fintype_card]
  apply Eq.trans
  · exact @Fintype.card_congr' _ _ hF (Fintype.ofFinset s (by intro x; simp [s]; exact and_comm)) (by rfl)
  · apply Fintype.card_ofFinset
