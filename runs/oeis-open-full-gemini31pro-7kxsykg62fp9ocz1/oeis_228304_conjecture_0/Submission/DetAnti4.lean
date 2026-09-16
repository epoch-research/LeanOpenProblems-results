import Mathlib
import Mathlib.Data.Nat.Choose.Lucas

open Nat

lemma choose_zmod_eq {p n k : ℕ} [hp : Fact p.Prime] :
    (choose n k : ZMod p) = (choose (n % p) (k % p) : ZMod p) * (choose (n / p) (k / p) : ZMod p) := by
  have H := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := n) (k := k)
  have H2 : (choose n k : ZMod p) = ((choose (n % p) (k % p) * choose (n / p) (k / p) : ℕ) : ZMod p) := by
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr H
  rw [H2]
  push_cast
  rfl
