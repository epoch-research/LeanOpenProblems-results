import FormalConjectures.Util.ProblemImports

open Nat Finset Matrix
theorem ZMod_inv_neg {n : ℕ} (x : ZMod n) : (-x)⁻¹ = -x⁻¹ := by
  -- Let's see if we can prove this using the fact that ZMod n is finite and we can do cases on IsUnit
  by_cases h : IsUnit x
  · -- x is a unit
    apply ZMod.inv_eq_of_mul_eq_one
    calc (-x) * -x⁻¹ = x * x⁻¹ := by ring
    _ = 1 := ZMod.mul_inv_of_unit x h
  · -- x is not a unit
    -- then -x is also not a unit
    sorry



noncomputable def f_entry {p : ℕ} (i j : ℕ) : ZMod (p ^ 2) :=
  let R := ZMod (p ^ 2)
  if i = j then
    1
  else
    let i_int : ℤ := i
    let j_int : ℤ := j
    let num : R := (i_int + j_int)
    let den : R := (i_int - j_int)
    num * den⁻¹

theorem f_entry_skew {p : ℕ} (i j : ℕ) (h : i ≠ j) :
  f_entry (p:=p) i j = - f_entry (p:=p) j i := by
  have h' : j ≠ i := h.symm
  unfold f_entry
  split_ifs with h1
  · contradiction
  · simp only [h1, h', ↓reduceIte]
    push_cast
    have h_num : ((i : ZMod (p^2)) + j) = (j + i) := by ring
    have h_den : ((j : ZMod (p^2)) - i) = -(i - j) := by ring
    rw [h_num]
    rw [h_den]




















