import Mathlib
import Mathlib.Data.Nat.Choose.Dvd

open Nat

lemma choose_p_minus_one_mod_p (p k : ℕ) [hp : Fact p.Prime] (hk : k < p) :
    (choose (p - 1) k : ZMod p) = (-1 : ZMod p)^k := by
  induction' k with k ih
  · simp
  · have hk_lt : k < p := by omega
    have h_choose : (choose p (k + 1) : ZMod p) = (choose (p - 1) k : ZMod p) + (choose (p - 1) (k + 1) : ZMod p) := by
      have H : p = p - 1 + 1 := by omega
      have H2 : choose p (k + 1) = choose (p - 1) k + choose (p - 1) (k + 1) := by
        nth_rewrite 1 [H]
        exact rfl
      push_cast at H2 ⊢
      rw [H2]
      push_cast
      rfl
    have h_p_div : p ∣ choose p (k + 1) := Prime.dvd_choose_self hp.out (by omega) (by omega)
    have h_p_mod : (choose p (k + 1) : ZMod p) = 0 := by
      exact (CharP.cast_eq_zero_iff (ZMod p) p _).mpr h_p_div
    have eq1 : (0 : ZMod p) = (choose (p - 1) k : ZMod p) + (choose (p - 1) (k + 1) : ZMod p) := by
      rw [← h_choose, h_p_mod]
    have eq2 : (choose (p - 1) (k + 1) : ZMod p) = - (choose (p - 1) k : ZMod p) := by
      calc (choose (p - 1) (k + 1) : ZMod p) = (choose (p - 1) k : ZMod p) + (choose (p - 1) (k + 1) : ZMod p) - (choose (p - 1) k : ZMod p) := by ring
      _ = (0 : ZMod p) - (choose (p - 1) k : ZMod p) := by rw [← eq1]
      _ = - (choose (p - 1) k : ZMod p) := by ring
    rw [eq2, ih hk_lt]
    ring
