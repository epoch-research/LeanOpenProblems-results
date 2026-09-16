import FormalConjectures.Util.ProblemImports
import Submission.TestPrimality3

namespace R

open Finset

theorem M_le_p2_minus_one {n p M m : ℕ} [NeZero n] [NeZero p] (h : p ∣ n) (hp : 1 < p)
    (x : R n) (hM : M = 2 * (100943 * 3^m))
    (h_pow_M : pow x M = one)
    (inv2 : R n) (h_inv2 : mul inv2 (sub (pow x (M / 2)) one) = one)
    (inv3 : R n) (h_inv3 : mul inv3 (sub (pow x (M / 3)) one) = one)
    (invp : R n) (h_invp : mul invp (sub (pow x (M / 100943)) one) = one) :
    M ≤ p^2 - 1 := by
  have h_inj : ∀ i j, i < M → j < M → i ≤ j → pow (cast h x) i = pow (cast h x) j → i = j := by
    intro i j hi hj hle heq
    have h_pow_M_p : pow (cast h x) M = one := by
      rw [←cast_pow, h_pow_M, cast_one]
    have h_sub := pow_sub (cast h x) h_pow_M_p (by omega) hle heq
    by_contra! hne
    have h_pos : 0 < j - i := by omega
    have h_lt : j - i < M := by omega
    have := order_eq_M_rp h hp x hM h_pow_M inv2 h_inv2 inv3 h_inv3 invp h_invp (j - i) h_pos h_lt
    exact this h_sub
  -- now use Finset.card
  sorry

end R
