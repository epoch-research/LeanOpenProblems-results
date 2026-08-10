import Mathlib

open Finset BigOperators

/-- For an odd prime power modulus `N = p^k` with `p ≥ 5`, the sum of squares of all
units in `ZMod N` is zero.  Proof: multiplication by the unit `2` permutes the units,
so `4 * S = S`, hence `3 * S = 0`, and `3` is a unit. -/
theorem unitsq_sum_zero (N : ℕ) [NeZero N] (hN2 : IsUnit (2 : ZMod N)) (hN3 : IsUnit (3 : ZMod N)) :
    ∑ u : (ZMod N)ˣ, ((u : ZMod N))^2 = 0 := by
  set S := ∑ u : (ZMod N)ˣ, ((u : ZMod N))^2 with hS
  -- the unit 2
  obtain ⟨c, hc⟩ := hN2
  -- reindex u ↦ c * u
  have hbij : ∑ u : (ZMod N)ˣ, (((c * u : (ZMod N)ˣ) : ZMod N))^2 = S := by
    rw [hS]
    exact Equiv.sum_comp (Equiv.mulLeft c) (fun u => ((u : ZMod N))^2)
  have h4 : (4 : ZMod N) * S = S := by
    have : ∑ u : (ZMod N)ˣ, (((c * u : (ZMod N)ˣ) : ZMod N))^2
         = ∑ u : (ZMod N)ˣ, (2:ZMod N)^2 * ((u : ZMod N))^2 := by
      apply Finset.sum_congr rfl
      intro u _
      rw [Units.val_mul, hc, mul_pow]
    rw [this, ← Finset.mul_sum] at hbij
    have : (2:ZMod N)^2 = 4 := by norm_num
    rw [this] at hbij
    rw [← hS] at hbij
    exact hbij
  -- 3 * S = 0
  have h3 : (3 : ZMod N) * S = 0 := by
    have : (4 : ZMod N) * S - S = 0 := by rw [h4]; ring
    have e : (4 : ZMod N) * S - S = 3 * S := by ring
    rw [e] at this; exact this
  -- cancel 3
  obtain ⟨d, hd⟩ := hN3
  have key : ((d⁻¹ : (ZMod N)ˣ) : ZMod N) * ((3 : ZMod N) * S) = ((d⁻¹ : (ZMod N)ˣ) : ZMod N) * 0 := by
    rw [h3]
  rw [mul_zero, ← mul_assoc] at key
  rw [show ((d⁻¹ : (ZMod N)ˣ) : ZMod N) * 3 = 1 by
    rw [← hd, ← Units.val_mul]; simp] at key
  rw [one_mul] at key
  exact key
