import FormalConjectures.Util.ProblemImports

open Finset Nat

lemma cast_y (y : ℕ) : ((y * (4 * y - 2) : ℕ) : ℤ) = (y : ℤ) * (4 * (y : ℤ) - 2) := by
  cases y with
  | zero => norm_num
  | succ y =>
    norm_num
    ring

lemma cast_z (z : ℕ) : ((z * (4 * z - 3) : ℕ) : ℤ) = (z : ℤ) * (4 * (z : ℤ) - 3) := by
  cases z with
  | zero => norm_num
  | succ z =>
    norm_num
    ring

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
  apply Nat.cast_injective (R := ℤ)
  rw [cast_y, cast_z]
  norm_num at hsq ⊢
  have hmain : (n : ℤ) = 4 * (w : ℤ)^2 + (x : ℤ) * (4 * (x : ℤ) + 1) + (y : ℤ) * (4 * (y : ℤ) - 2) + (z : ℤ) * (4 * (z : ℤ) - 3) := by
    nlinarith [hsq]
  exact hmain
