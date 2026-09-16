import FormalConjectures.Util.ProblemImports
open Nat Finset Classical

namespace OeisA230507

def S_condition (m : ℕ) : Prop :=
  Nat.Prime (2 * m + 1) ∧ Nat.Prime (2 * m ^ 3 + 1)

noncomputable def A230507 (n : ℕ) : ℕ :=
  Finset.sum (Finset.Icc 1 (n / 3)) fun a ↦
    Finset.sum (Finset.Icc a ((n - a) / 2)) fun b ↦
      let c := n - a - b
      if S_condition a ∧ S_condition b ∧ S_condition c
      then 1
      else 0

section ConjectureDefs

def P2_condition (m : ℕ) : Prop :=
  m > 0 ∧ Nat.Prime (2 * m + 1) ∧ Nat.Prime (2 * m ^ 4 - 1)

def Z_condition (m : ℕ) : Prop :=
  m > 0 ∧ Nat.Prime (2 * m - 1) ∧ Nat.Prime (2 * m ^ 4 - 1)

end ConjectureDefs

theorem oeis_230507_verified_up_to_10_pow_6 :
  (∀ n : ℕ, n > 2 ∧ n ≤ 10^6 → A230507 n > 0)
  ∧
  (∀ n : ℕ, n > 8 ∧ n ≤ 10^6 → ∃ (x y z : ℕ), n = x + y + z ∧ P2_condition x ∧ P2_condition y ∧ Z_condition z) := sorry

end OeisA230507

theorem OeisA230507.oeis_230507_verified_up_to_10_pow_6.disproof : ¬ (type_of% @OeisA230507.oeis_230507_verified_up_to_10_pow_6) := sorry
