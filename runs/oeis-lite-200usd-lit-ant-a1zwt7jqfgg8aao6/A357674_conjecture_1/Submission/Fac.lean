import Submission.Build
import Submission.Carlitz

open Nat Finset BigOperators

namespace Fac

variable {p : ℕ} [Fact p.Prime]

/-- Power sum in `R = ZMod (p^5)` over `{0,...,p-1}`. -/
noncomputable def T (p : ℕ) (l : ℕ) : ZMod (p^5) := ∑ x ∈ Finset.range p, (x : ZMod (p^5))^l

/-- The elementary power-sum recursion (telescoping + binomial). -/
lemma powsum_rec (a : ℕ) :
    ∑ l ∈ Finset.range (a+1), (Nat.choose (a+1) l : ZMod (p^5)) * T p l
      = (p : ZMod (p^5))^(a+1) := by
  have htel : ∑ x ∈ Finset.range p,
      (((x:ZMod (p^5))+1)^(a+1) - (x:ZMod (p^5))^(a+1))
      = (p : ZMod (p^5))^(a+1) - (0:ZMod (p^5))^(a+1) := by
    have := Finset.sum_range_sub (fun x => (x:ZMod (p^5))^(a+1)) p
    simpa using this
  rw [show (0:ZMod (p^5))^(a+1) = 0 from by rw [zero_pow (by omega)], sub_zero] at htel
  -- expand binomial inside
  have hbin : ∀ x : ℕ, ((x:ZMod (p^5))+1)^(a+1) - (x:ZMod (p^5))^(a+1)
      = ∑ l ∈ Finset.range (a+1), (Nat.choose (a+1) l : ZMod (p^5)) * (x:ZMod (p^5))^l := by
    intro x
    rw [add_pow]
    rw [Finset.sum_range_succ]
    simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self, pow_zero, mul_one]
    rw [add_sub_cancel_right]
    refine Finset.sum_congr rfl (fun l hl => ?_)
    rw [Finset.mem_range] at hl
    rw [one_pow, mul_one]; ring
  rw [← htel]
  rw [Finset.sum_congr rfl (fun x _ => hbin x)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [T, Finset.mul_sum]
