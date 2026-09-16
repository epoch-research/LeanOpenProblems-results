import Mathlib

open Nat ZMod

theorem crt_contradiction {m u v n : ℕ} (huv : m = u * v) (hcop : Coprime u v)
    (hu : 1 < u) (hv : 1 < v) (hm_odd : Odd m) (hn : n > 0)
    (b : ZMod m) (hbn : b ^ n = -1)
    (h_pseudo : ∀ x : ZMod m, IsUnit x → x ^ n = 1 ∨ x ^ n = -1) : False := by
  subst huv
  have hu_odd : Odd u := hm_odd.of_mul_left
