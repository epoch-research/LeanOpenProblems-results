import FormalConjectures.Util.ProblemImports
open Nat Finset

-- Work only at the representation level, not unfolding A308934.
lemma witness_scale4 (n a b c d x y : ℕ)
    (heq : (2^a * 3^b)^2 + (2^c * 3^d)^2 + x^2 + 2*y^2 = n) :
    (2^(a+1) * 3^b)^2 + (2^(c+1) * 3^d)^2 + (2*x)^2 + 2*(2*y)^2 = 4*n := by
  rw [← heq]
  ring_nf
  -- ring_nf does not simplify powers with Nat maybe enough?

lemma witness_scale9 (n a b c d x y : ℕ)
    (heq : (2^a * 3^b)^2 + (2^c * 3^d)^2 + x^2 + 2*y^2 = n) :
    (2^a * 3^(b+1))^2 + (2^c * 3^(d+1))^2 + (3*x)^2 + 2*(3*y)^2 = 9*n := by
  rw [← heq]
  ring_nf

lemma witness_order_scale2 (a b c d : ℕ)
    (hge : ¬ (2^a * 3^b < 2^c * 3^d)) :
    ¬ (2^(a+1) * 3^b < 2^(c+1) * 3^d) := by
  intro h
  have hmul : 2 * (2^a * 3^b) < 2 * (2^c * 3^d) := by simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using h
  exact hge (Nat.mul_lt_mul_left (by decide : 0 < 2) |>.1 hmul)

lemma witness_order_scale3 (a b c d : ℕ)
    (hge : ¬ (2^a * 3^b < 2^c * 3^d)) :
    ¬ (2^a * 3^(b+1) < 2^c * 3^(d+1)) := by
  intro h
  have hmul : 3 * (2^a * 3^b) < 3 * (2^c * 3^d) := by simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using h
  exact hge (Nat.mul_lt_mul_left (by decide : 0 < 3) |>.1 hmul)
