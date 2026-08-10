import FormalConjectures.Util.ProblemImports

open Finset Nat

lemma cast_y (y : ℕ) : ((y * (4 * y - 2) : ℕ) : ℤ) = (y : ℤ) * (4 * (y : ℤ) - 2) := by
  cases y with
  | zero => norm_num
  | succ y =>
    have h : 2 ≤ 4 * (y + 1) := by omega
    rw [Nat.cast_mul, Nat.cast_sub h]
    push_cast
    ring

lemma cast_z (z : ℕ) : ((z * (4 * z - 3) : ℕ) : ℤ) = (z : ℤ) * (4 * (z : ℤ) - 3) := by
  cases z with
  | zero => norm_num
  | succ z =>
    have h : 3 ≤ 4 * (z + 1) := by omega
    rw [Nat.cast_mul, Nat.cast_sub h]
    push_cast
    ring

lemma refined_to_original (n : ℕ) (A B C D : ℤ)
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
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_add]
  rw [cast_y, cast_z]
  push_cast
  norm_num at hsq ⊢
  nlinarith [hsq]
