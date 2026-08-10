import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

namespace A357674dev

/-- `∏_{j ∈ Icc 1 m} (a + j) * a! = (a + m)!` (shifted factorial). -/
theorem prod_Icc_shift_factorial (a m : ℕ) :
    (∏ j ∈ Icc 1 m, (a + j)) * a ! = (a + m)! := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1)]
    rw [mul_comm (∏ j ∈ Icc 1 n, (a + j)) (a + (n+1)), mul_assoc, ih]
    rw [show a + (n + 1) = (a + n) + 1 by ring, Nat.factorial_succ]

/-- Nat identity: `C(3p,p) * (p-1)! = 3 * ∏_{i=1}^{p-1} (2p+i)`. -/
theorem choose_prod_nat (p : ℕ) (hp : 1 ≤ p) :
    (3 * p).choose p * (p - 1)! = 3 * ∏ i ∈ Icc 1 (p - 1), (2 * p + i) := by
  have key : ((3 * p).choose p * (p - 1)!) * (p * (2 * p)!)
           = (3 * ∏ i ∈ Icc 1 (p - 1), (2 * p + i)) * (p * (2 * p)!) := by
    -- LHS = (3p)!
    have hL : ((3 * p).choose p * (p - 1)!) * (p * (2 * p)!) = (3 * p)! := by
      have h1 : (p - 1)! * p = p ! := by
        rw [mul_comm]; exact Nat.mul_factorial_pred (by omega)
      calc ((3 * p).choose p * (p - 1)!) * (p * (2 * p)!)
          = (3 * p).choose p * ((p - 1)! * p) * (2 * p)! := by ring
        _ = (3 * p).choose p * p ! * (2 * p)! := by rw [h1]
        _ = (3 * p).choose p * p ! * (3 * p - p)! := by congr 2; omega
        _ = (3 * p)! := Nat.choose_mul_factorial_mul_factorial (by omega)
    -- RHS = (3p)!
    have hR : (3 * ∏ i ∈ Icc 1 (p - 1), (2 * p + i)) * (p * (2 * p)!) = (3 * p)! := by
      have hlast : ∏ i ∈ Icc 1 p, (2 * p + i)
          = (∏ i ∈ Icc 1 (p - 1), (2 * p + i)) * (2 * p + p) := by
        have h := Finset.prod_Icc_succ_top (a := 1) (b := p - 1)
          (f := fun i => 2 * p + i) (by omega)
        rw [show p - 1 + 1 = p by omega] at h
        exact h
      have hfull : (∏ i ∈ Icc 1 p, (2 * p + i)) * (2 * p)! = (3 * p)! := by
        have := prod_Icc_shift_factorial (2 * p) p
        rwa [show 2 * p + p = 3 * p by ring] at this
      calc (3 * ∏ i ∈ Icc 1 (p - 1), (2 * p + i)) * (p * (2 * p)!)
          = ((∏ i ∈ Icc 1 (p - 1), (2 * p + i)) * (2 * p + p)) * (2 * p)! := by ring_nf
        _ = (∏ i ∈ Icc 1 p, (2 * p + i)) * (2 * p)! := by rw [hlast]
        _ = (3 * p)! := hfull
    rw [hL, hR]
  exact Nat.eq_of_mul_eq_mul_right (by positivity) key

end A357674dev
