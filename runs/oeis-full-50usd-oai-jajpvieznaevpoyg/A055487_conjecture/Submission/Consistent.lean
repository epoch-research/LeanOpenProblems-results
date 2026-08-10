import FormalConjectures.Util.ProblemImports
open Set
open Nat
noncomputable def A055487 (n : ℕ) : ℕ :=
  sInf {m : ℕ | Nat.totient m = Nat.factorial n}
def prime_candidates (n : ℕ) : Set ℕ :=
  let N := Nat.factorial n
  { p : ℕ | Nat.Prime p ∧ Nat.sqrt N < p ∧ (p - 1) ∣ N ∧ Nat.Prime (N / (p - 1) + 1) }
example : ¬ Nat.Prime (Nat.factorial 4 + 1) := by norm_num
example : (prime_candidates 4).Nonempty := by
  refine ⟨5, ?_⟩
  norm_num [prime_candidates]
