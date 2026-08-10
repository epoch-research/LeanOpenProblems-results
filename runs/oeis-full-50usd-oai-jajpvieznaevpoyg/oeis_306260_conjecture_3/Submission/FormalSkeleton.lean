import FormalConjectures.Util.ProblemImports

open Finset Nat

-- Can we at least convert signed roots in the desired residues into the target witnesses?
example (n : ℕ) (A B C D : ℤ)
    (hA : ∃ w : ℕ, A = (8*w : ℤ))
    (hB : ∃ x : ℕ, B = (8*x + 1 : ℤ))
    (hC : ∃ y : ℕ, C = (8*y - 2 : ℤ))
    (hD : ∃ z : ℕ, D = (8*z - 3 : ℤ))
    (hsq : A^2 + B^2 + C^2 + D^2 = (16*n + 14 : ℤ)) :
    ∃ w x y z : ℕ, n = 4 * w^2 + x * (4*x+1) + y*(4*y-2) + z*(4*z-3) := by
  rcases hA with ⟨w,rfl⟩
  rcases hB with ⟨x,rfl⟩
  rcases hC with ⟨y,rfl⟩
  rcases hD with ⟨z,rfl⟩
  use w,x,y,z
  -- prove by omega/nlinarith after casting. Need Nat sub issue: y=0 OK expression y*(4*y-2)=0, but int expansion y*(4y-2) also 0 if y=0? cast Nat subtraction differs from Int subtraction when y=0? y*(4*y-2) Nat =0, Int polynomial=0, OK; z too.
  have hy : ((y * (4 * y - 2) : ℕ) : ℤ) = (y : ℤ) * (4 * (y : ℤ) - 2) := by
    cases y <;> norm_num [Nat.succ_eq_add_one, Nat.mul_sub_left_distrib, Nat.add_assoc, Nat.mul_add]
  have hz : ((z * (4 * z - 3) : ℕ) : ℤ) = (z : ℤ) * (4 * (z : ℤ) - 3) := by
    cases z <;> norm_num [Nat.succ_eq_add_one, Nat.mul_sub_left_distrib, Nat.add_assoc, Nat.mul_add]
  apply Nat.cast_injective (R := ℤ)
  rw [show ((n : ℕ) : ℤ) = n by rfl]
  -- hsq is enough; ring_nf should transform
  have : (16 : ℤ) * (n : ℤ) = 16 * (4 * (w:ℤ)^2 + (x:ℤ)*(4*x+1) + (y:ℤ)*(4*y-2) + (z:ℤ)*(4*z-3)) := by
    nlinarith [hsq]
  have hdiv : (n : ℤ) = 4 * (w:ℤ)^2 + (x:ℤ)*(4*x+1) + (y:ℤ)*(4*y-2) + (z:ℤ)*(4*z-3) := by
    omega
  norm_num [hy,hz]
  exact hdiv
