import FormalConjectures.Util.ProblemImports
import Submission.Proof

open Finset Nat

/--
A193279: Number of distinct sums of distinct proper divisors of $n$.
The count excludes an empty subset of proper divisors that would give $0$ as a sum.
-/
def A193279 (n : ℕ) : ℕ :=
  let D := properDivisors n
  -- The set of all distinct sums of subsets of D, including the sum of the empty set (0).
  let S := D.powerset.image (fun s : Finset ℕ => s.sum id)
  -- The number of distinct sums, minus the single sum 0 from the empty set.
  S.card - 1

/--
%C A193279 a(n)=n if n is an even perfect number (is the converse true?)
-/
theorem oeis_193279_conjecture_0 (n : ℕ) :
  (Nat.Perfect n ∧ Even n) → A193279 n = n := by
  intro ⟨hperf, heven⟩
  have h0 : n > 0 := by
    by_contra h
    have : n = 0 := by omega
    subst this
    have := hperf
    rw [Nat.Perfect] at this
    tauto
  unfold A193279
  let D := n.properDivisors
  let S := D.powerset.image (fun s : Finset ℕ => s.sum _root_.id)
  have hS_eq : S = Iic n := by
    ext x
    exact ⟨fun h => S_subset_Iic n hperf h, fun h => Iic_subset_S n h0 heven hperf h⟩
  have h_card_S : S.card = n + 1 := by
    rw [hS_eq]
    exact card_Iic n
  change S.card - 1 = n
  rw [h_card_S]
  rfl

theorem oeis_193279_conjecture_0.disproof : ¬ (type_of% @oeis_193279_conjecture_0) := sorry
