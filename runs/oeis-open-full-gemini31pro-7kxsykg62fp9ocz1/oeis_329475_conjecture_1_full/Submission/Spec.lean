import FormalConjectures.Util.ProblemImports

open Nat Int ZMod Finset

def T (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n / 2 + 1)) fun k => (n.choose k) * ((n - k).choose k)

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k => (n.choose k) ^ 2 * T k * T (n - k)

noncomputable def S_ZMod (p : ℕ) [Fact p.Prime] : ZMod (p^2) :=
  let R := ZMod (p^2)
  let neg_4_inv : R := (-(4 : R))⁻¹
  Finset.sum (Finset.range p) fun k => (a k : R) * (neg_4_inv ^ k)

noncomputable def S (p : ℕ) [Fact p.Prime] (h_odd : p ≠ 2) : ℤ :=
  (ZMod.val (S_ZMod p) : ℤ)

theorem oeis_329475_conjecture_1_full {p : ℕ} (hp : Fact p.Prime) (h_odd : p ≠ 2) :
  (p % 12 = 1 → (∃ (x y : ℤ), (p : ℤ) = x^2 + 9 * y^2 ∧ S p h_odd ≡ 4 * x^2 - 2 * p [ZMOD p^2])) ∧
  (p % 12 = 5 → (∃ (x y : ℤ), (p : ℤ) = x^2 + y^2 ∧ x ≡ y [ZMOD 3] ∧ S p h_odd ≡ 4 * x * y [ZMOD p^2])) ∧
  (p % 4 = 3 → S p h_odd ≡ 0 [ZMOD p^2])
:= sorry

theorem oeis_329475_conjecture_1_full.disproof : ¬ (type_of% @oeis_329475_conjecture_1_full) := sorry
