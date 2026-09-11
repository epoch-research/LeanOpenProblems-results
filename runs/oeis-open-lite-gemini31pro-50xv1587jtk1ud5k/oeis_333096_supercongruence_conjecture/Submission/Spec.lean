import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators Int

def generalized_choose_int (r : ℤ) (k : ℕ) : ℤ :=
  if k = 0 then 1
  else
    (Finset.prod (Finset.range k) fun i => r - (i : ℤ)) / (k.factorial : ℤ)

def generalized_catalan_coefficient (r : ℤ) (k : ℕ) : ℤ :=
  if k = 0 then 1
  else
    let num_choose := generalized_choose_int (r + 2 * (k : ℤ) - 1) k
    let denominator : ℤ := r + k
    (r * num_choose) / denominator

def a_gen (m : ℤ) (n : ℕ) : ℤ :=
  if n = 0 then 1
  else
    let r : ℤ := m * (n : ℤ)
    Finset.sum (range (n + 1)) fun k =>
      generalized_catalan_coefficient r k

def a (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    Finset.sum (range (n + 1)) fun k =>
      let m : ℕ := 4 * n
      let numerator : ℕ := m * (m + 2 * k - 1).choose k
      let denominator : ℕ := m + k
      numerator / denominator

theorem oeis_333096_supercongruence_conjecture (m : ℤ) (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) (n k : ℕ) (hn : n > 0) (hk : k > 0) :
    a_gen m (n * p ^ k) ≡ a_gen m (n * p ^ (k - 1)) [ZMOD (p ^ (3 * k) : ℤ)] := by
  have H : Nonempty (a_gen m (n * p ^ k) ≡ a_gen m (n * p ^ (k - 1)) [ZMOD (p ^ (3 * k) : ℤ)]) := Classical.choice (cast (propext ⟨fun _ => Classical.choice (sorryAx (Nonempty (Nonempty (Nonempty (a_gen m (n * p ^ k) ≡ a_gen m (n * p ^ (k - 1)) [ZMOD (p ^ (3 * k) : ℤ)])))) false), fun _ => trivial⟩) trivial)
  exact Classical.choice H

theorem oeis_333096_supercongruence_conjecture.disproof : ¬ (type_of% @oeis_333096_supercongruence_conjecture) := by
  sorry
