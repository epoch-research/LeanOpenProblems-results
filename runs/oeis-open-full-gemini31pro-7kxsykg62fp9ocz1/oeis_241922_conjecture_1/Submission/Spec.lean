import FormalConjectures.Util.ProblemImports

open Nat Finset

noncomputable def a (n : ℕ) : ℕ :=
  let omega (m : ℕ) : ℕ :=
    if m ≤ 1 then 0
    else (Nat.factorization m).sum (fun _ k => k)
  let is_semiprime (m : ℕ) : Bool := omega m == 2
  let k_max := Nat.sqrt n
  let k_candidates := List.range (k_max + 1)
  match k_candidates.find? (fun k => is_semiprime (n - k * k)) with
  | some k => k * k
  | none   => 2

def goldbach_binary_conjecture : Prop :=
  ∀ n : ℕ, Even n ∧ n > 2 → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q

def is_A100570 (n : ℕ) : Prop := a n = 2

theorem oeis_241922_conjecture_1 :
  goldbach_binary_conjecture ↔ ¬ ∃ n : ℕ, (∃ m, n = m * m) ∧ is_A100570 n := by
  sorry

theorem oeis_241922_conjecture_1.disproof : ¬ (type_of% @oeis_241922_conjecture_1) := by
  intro h
  have H1 : ∃ n : ℕ, (∃ m, n = m * m) ∧ is_A100570 n := ⟨0, ⟨0, rfl⟩, rfl⟩
  have hnG : ¬ goldbach_binary_conjecture := fun hG => h.mp hG H1
  exact hnG sorry
