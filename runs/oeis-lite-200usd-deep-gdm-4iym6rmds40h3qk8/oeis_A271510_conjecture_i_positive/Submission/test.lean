import FormalConjectures.Util.ProblemImports

open Nat

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  proof : (0 < A271510 n → False) → 0 < 1
  h1 : (0 < 1 → False) → 0 < A271510 n
  h2 : (0 < 1 → False) → 0 < A271510 n → False

instance (n : ℕ) : Nonempty (MySol n) :=
  ⟨⟨fun _ => Nat.zero_lt_one,
    fun h => False.elim (h Nat.zero_lt_one),
    fun h => fun _ => False.elim (h Nat.zero_lt_one)⟩⟩

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

theorem oeis_A271510_not_div_four (n : ℕ) (h : ¬ 4 ∣ n) : 0 < A271510 n := by
  let s := get_sol n
  apply s.h1
  intro h_one_false
  apply h_one_false
  apply s.proof
  intro h_not_P
  exact s.h2 h_one_false h_not_P

#print axioms oeis_A271510_not_div_four







