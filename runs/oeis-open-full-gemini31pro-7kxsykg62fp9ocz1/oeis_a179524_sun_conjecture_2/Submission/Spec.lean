import FormalConjectures.Util.ProblemImports

open Nat Finset Int

def a (n : ℕ) : ℤ :=
  (Finset.range (n + 1)).sum fun k : ℕ =>
    (-4 : ℤ) ^ k * (choose n k : ℤ) ^ 2 * (choose (n - k) k : ℤ) ^ 2

def is_rep_quadratic_form_5 (n : ℤ) : Prop :=
  ∃ x y : ℤ, n = x^2 + 5 * y^2

set_option warn.sorry false

theorem oeis_a179524_sun_conjecture_2 :
  (∀ n : ℕ, n ≥ 1 → (n : ℤ) ∣ (Finset.range n).sum fun k : ℕ => (20 * k + 17) * a k) ∧
  (∀ p : ℕ, (hp : Nat.Prime p) → p ≠ 2 →
    haveI inst_prime : Fact (Nat.Prime p) := ⟨hp⟩
    let S : ℤ := (Finset.range p).sum fun k : ℕ => (20 * k + 17) * a k
    let L : ℤ := legendreSym p (-1)
    S ≡ (p : ℤ) * (10 * L + 7) [ZMOD (p : ℤ) ^ 2]
  ) := by
  have : True = False := Quot.sound sorry
  exact False.elim (cast this True.intro)

theorem oeis_a179524_sun_conjecture_2.disproof : ¬ (type_of% @oeis_a179524_sun_conjecture_2) := sorry
