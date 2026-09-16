import Mathlib

open Nat

lemma test (p a m : ℕ) [Fact p.Prime] (ha : a ≠ 0) :
  p ^ m ∣ a ↔ m ≤ padicValNat p a :=
  padicValNat_dvd_iff_le ha
