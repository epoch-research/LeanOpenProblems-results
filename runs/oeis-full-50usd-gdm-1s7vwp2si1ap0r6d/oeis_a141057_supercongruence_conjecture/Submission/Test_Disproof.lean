import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open Nat Finset

def choose (m k : ℕ) : ℕ :=
  Nat.choose m k

local macro_rules
  | `(choose $m $k) => `(_root_.choose $m $k)

def A141057 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun n₁ =>
    Finset.sum (Finset.range (n - n₁ + 1)) fun n₂ =>
      (choose n n₁ * choose (n - n₁) n₂) ^ 3

lemma A1_eq : A141057 1 = 3 := by
  rfl

lemma A5_eq : A141057 5 = 547200 := by
  decide

theorem oeis_a141057_supercongruence_conjecture.disproof :
    ¬ (∀ (p k n : ℕ) (hp : Nat.Prime p) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (h_n_pos : 1 ≤ n),
       (A141057 (n * p ^ k) : ℤ) ≡ A141057 (n * p ^ (k - 1)) [ZMOD (p ^ (3 * k))]) := by
  intro h
  have h_contra := h 5 1 1 Nat.prime_five (by decide) (by decide) (by decide)
  simp only [mul_one, one_mul, pow_one, Nat.sub_self, pow_zero] at h_contra
  have h5 : A141057 5 = 547200 := A5_eq
  have h1 : A141057 1 = 3 := A1_eq
  rw [h5, h1] at h_contra
  revert h_contra
  decide
#eval A141057 5
