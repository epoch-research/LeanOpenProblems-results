import FormalConjectures.Util.ProblemImports
open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

example (n : ℕ) (h : n > 13) : A216265 n > 0 := by
  unfold A216265
  rw [Nat.sub_pos_iff_lt]
  -- Need strict monotonicity of primeCounting over interval.
  let a := (n ^ 3 - n).primeCounting + 1
  obtain ⟨x, hx⟩ := Nat.surjective_primeCounting a
  -- hx : primeCounting x = primeCounting (N-n)+1
  have hxgt : n ^ 3 - n < x := by
    by_contra hle
    have := Nat.monotone_primeCounting hle
    omega
  -- no upper bound on x
  guard_target = (n ^ 3 - n).primeCounting < (n ^ 3).primeCounting
  sorry
