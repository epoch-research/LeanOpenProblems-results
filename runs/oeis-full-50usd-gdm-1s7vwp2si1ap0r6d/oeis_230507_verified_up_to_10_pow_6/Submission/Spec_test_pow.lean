import FormalConjectures.Util.ProblemImports
open Nat

namespace OeisA230507

namespace OeisA230507

/-- The condition $2m + 1$ and $2m^3 + 1$ are both prime, for $m \in \mathbb{N}$. -/
def S_condition (m : ℕ) : Prop :=
  Nat.Prime (2 * m + 1) ∧ Nat.Prime (2 * m ^ 3 + 1)

instance (m : ℕ) : Decidable (S_condition m) :=
  instDecidableAnd

/--
A230507: Number of ways to write $n = a + b + c$ with $a \le b \le c$, where $a, b, c$ are among those numbers $m$ (terms of A230506) with $2m + 1$ and $2m^3 + 1$ both prime.
We rely on the bounds $1 \le a$ to ensure the summands are positive.
-/
def A230507 (n : ℕ) : ℕ :=
  -- Iterate over 'a' satisfying 1 <= a <= n/3.
  Finset.sum (Finset.Icc 1 (n / 3)) fun a ↦
    -- Iterate over 'b' satisfying a <= b <= (n-a)/2.
    Finset.sum (Finset.Icc a ((n - a) / 2)) fun b ↦
      let c := n - a - b
      -- Count 1 if a, b, and c all satisfy the special prime condition.
      if S_condition a ∧ S_condition b ∧ S_condition c
      then 1
      else 0

section ConjectureDefs

/-- Condition for $x$ and $y$ in Conjecture (ii): $x > 0$ and $2x+1$ and $2x^4-1$ are both prime. -/
def P2_condition (m : ℕ) : Prop :=
  m > 0 ∧ Nat.Prime (2 * m + 1) ∧ Nat.Prime (2 * m ^ 4 - 1)

/-- Condition for $z$ in Conjecture (ii): $z > 0$ and $2z-1$ and $2z^4-1$ are both prime. Note: $2z-1$ requires $2z \ge 1$, which is true for $z>0$. -/
def Z_condition (m : ℕ) : Prop :=
  m > 0 ∧ Nat.Prime (2 * m - 1) ∧ Nat.Prime (2 * m ^ 4 - 1)

end ConjectureDefs

set_option maxRecDepth 10000

def pow_fast_aux (x : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1
  | _, 0, _ => 1
  | fuel + 1, n, m =>
    if n = 1 then x % m
    else if n % 2 == 0 then
      let y := pow_fast_aux x fuel (n / 2) m
      (y * y) % m
    else
      let y := pow_fast_aux x fuel (n / 2) m
      (y * y * x) % m

def pow_fast (x : ℕ) (n : ℕ) (m : ℕ) : ℕ :=
  pow_fast_aux x n n m

theorem pow_fast_aux_eq (x fuel n m : ℕ) (hm : 1 < m) (h_fuel : n ≤ fuel) :
    pow_fast_aux x fuel n m = (x ^ n) % m := by
  induction fuel generalizing n with
  | zero =>
    have hn : n = 0 := by omega
    subst hn
    simp [pow_fast_aux]
    exact (Nat.mod_eq_of_lt hm).symm
  | succ fuel ih =>
    cases n with
    | zero =>
      simp [pow_fast_aux]
      exact (Nat.mod_eq_of_lt hm).symm
    | succ n =>
      by_cases hn1 : n = 0
      · subst hn1
        simp [pow_fast_aux]
      · have hn_not_zero : n ≠ 0 := hn1
        have h_cond : n + 1 ≠ 1 := by omega
        simp only [pow_fast_aux, h_cond, ↓reduceIte]
        by_cases heven : (n + 1) % 2 = 0
        · have heven' : ((n + 1) % 2 == 0) = true := by simp [heven]
          simp [heven']
          have h_div : (n + 1) / 2 ≤ fuel := by omega
          rw [ih _ h_div]
          rw [← Nat.mul_mod]
          congr 1
          rw [← Nat.pow_add]
          congr 1
          omega
        · have heven' : ((n + 1) % 2 == 0) = false := by simp [heven]
          simp [heven']
          have h_div : (n + 1) / 2 ≤ fuel := by omega
          rw [ih _ h_div]
          rw [Nat.mul_mod, ← Nat.mul_mod (x ^ ((n + 1) / 2)) (x ^ ((n + 1) / 2)), ← Nat.mul_mod]
          congr 1
          rw [← Nat.pow_add, ← Nat.pow_succ]
          congr 1
          omega

theorem pow_fast_eq (x n m : ℕ) (hm : 1 < m) :
    pow_fast x n m = (x ^ n) % m := by
  apply pow_fast_aux_eq x n n m hm (by rfl)

theorem zmod_pow_eq_pow_fast (p : ℕ) (hp : 1 < p) (a n : ℕ) :
    (a : ZMod p) ^ n = (pow_fast a n p : ZMod p) := by
  have : NeZero p := ⟨by omega⟩
  rw [pow_fast_eq a n p hp]
  rw [ZMod.natCast_mod]
  push_cast
  rfl


-- p = 2 * 6134^3 + 1
example : pow_fast 3 (461595228209 - 1) 461595228209 = 1 := by decide

end OeisA230507
