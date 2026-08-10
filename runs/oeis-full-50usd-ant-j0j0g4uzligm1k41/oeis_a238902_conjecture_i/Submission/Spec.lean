import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime

/--
A238902: $a(n) = |\{0 < k \le n: \pi(\pi(k \cdot n)) \text{ is a square}\}|$,
where $\pi(x)$ denotes the number of primes not exceeding $x$.
-/
def a (n : ℕ) : ℕ :=
  Finset.card $ (Finset.Icc 1 n).filter fun k : ℕ =>
    let m := π (π (k * n))
    m.sqrt ^ 2 = m

open Nat in
/-- One-step recurrence for the prime counting function. -/
theorem primeCounting_succ (m : ℕ) :
    π (m + 1) = π m + (if (m + 1).Prime then 1 else 0) := by
  unfold Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_succ]

open Nat in
/-- The iterated prime counting function `π ∘ π` has unit steps. -/
theorem primeCounting_primeCounting_step (m : ℕ) :
    π (π (m + 1)) ≤ π (π m) + 1 := by
  rcases Nat.lt_or_ge (π m) (π (m + 1)) with h | h
  · have hle : π (π (m + 1)) ≤ π (π m + 1) := by
      apply Nat.monotone_primeCounting
      have := primeCounting_succ m
      split at this <;> omega
    have h2 := primeCounting_succ (π m)
    rw [h2] at hle
    split at hle <;> omega
  · have heq : π (m + 1) = π m :=
      le_antisymm h (Nat.monotone_primeCounting (Nat.le_succ m))
    rw [heq]; omega

open Nat in
/-- The prime counting function is surjective. -/
theorem primeCounting_surjective : Function.Surjective (π : ℕ → ℕ) := by
  intro v
  obtain ⟨k, hk⟩ := Nat.surjective_primeCounting' v
  exact ⟨k - 1, by rw [Nat.primeCounting_sub_one]; exact hk⟩

open Nat in
/-- The iterated prime counting function `π ∘ π` is surjective, hence (with the
unit-step property) takes every value in any interval of its range. -/
theorem primeCounting_primeCounting_surjective :
    Function.Surjective (fun m => π (π m)) := by
  intro v
  obtain ⟨u, hu⟩ := primeCounting_surjective v
  obtain ⟨m, hm⟩ := primeCounting_surjective u
  exact ⟨m, by simp [hm, hu]⟩

/-- Reduction of positivity of `a n` to the existence of a witness `k`. -/
theorem a_pos_iff (n : ℕ) :
    0 < a n ↔ ∃ k ∈ Finset.Icc 1 n,
      (π (π (k * n))).sqrt ^ 2 = π (π (k * n)) := by
  unfold a
  rw [Finset.card_pos, Finset.filter_nonempty_iff]

/--
Conjecture (i): a(n) > 0 for all n > 0.
-/
theorem oeis_a238902_conjecture_i (n : ℕ) (hn : n > 0) : a n > 0 := by
  rw [gt_iff_lt, a_pos_iff]
  sorry
