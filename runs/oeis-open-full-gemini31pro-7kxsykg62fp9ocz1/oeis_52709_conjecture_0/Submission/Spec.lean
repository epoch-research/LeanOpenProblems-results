import FormalConjectures.Util.ProblemImports

def A052709 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) fun k =>
    ((Nat.choose (2 * k) k) / (k + 1)) * (Nat.choose k (n - 1 - k))

namespace A052709_Conjecture
open List

def is_positive_list (l : List ℕ) : Prop := ∀ x ∈ l, 0 < x

def covers_initial_interval (l : List ℕ) : Prop :=
  is_positive_list l ∧
  let s := l.toFinset
  match s.max with
  | some max_s => ∀ m : ℕ, 0 < m → (m ∈ s ↔ m ≤ max_s)
  | none => l.isEmpty

def has_nondecreasing_pattern_3 (l : List ℕ) : Prop :=
  ∃ (i j k : Fin l.length),
    i < j ∧ j < k ∧ l.get i ≤ l.get j ∧ l.get j ≤ l.get k

def avoids_pattern_xyz (l : List ℕ) : Prop :=
  ¬ has_nondecreasing_pattern_3 l

def sequences_counted_by_A052709 (n : ℕ) : Set (List ℕ) :=
  { l : List ℕ | l.length = n - 1 ∧ covers_initial_interval l ∧ avoids_pattern_xyz l }
end A052709_Conjecture

open A052709_Conjecture
open scoped Set

theorem oeis_52709_conjecture_0 (n : ℕ) (h : 0 < n) [Fintype (sequences_counted_by_A052709 n)] :
    A052709 n = Fintype.card (sequences_counted_by_A052709 n) :=
  by sorry

theorem oeis_52709_conjecture_0.disproof : ¬ (type_of% @oeis_52709_conjecture_0) := sorry
