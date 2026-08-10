import FormalConjectures.Util.ProblemImports

open Finset

def A048153 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

def Sneg (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun k => (n - k ^ 2 % n) % n)

-- Reformulate A048153 as a sum over ZMod n
theorem A048153_zmod (n : ℕ) [NeZero n] :
    A048153 n = ∑ x : ZMod n, (x ^ 2).val := by
  unfold A048153
  rw [← Finset.sum_range fun k => ((k : ZMod n) ^ 2).val]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    congr 1
    rw [← Nat.cast_pow]
    rw [ZMod.val_natCast]
    sorry
  sorry
