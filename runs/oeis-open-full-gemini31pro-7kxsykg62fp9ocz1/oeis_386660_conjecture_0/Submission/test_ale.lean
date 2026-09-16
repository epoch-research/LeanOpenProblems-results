import Mathlib
open Nat Filter Topology

def a (n : ℕ) : ℕ := (Finset.Icc 1 n).sum fun k => (n.choose k) % (2 ^ k)
def M (n : ℕ) : ℕ := (Finset.range (n + 1)).sup (fun k => min (n.choose k) (2 ^ k))

lemma mod_le_min (A B : ℕ) (hB : 0 < B) : A % B ≤ min A B := by
  apply le_min
  · exact Nat.mod_le A B
  · exact le_of_lt (Nat.mod_lt A hB)

lemma a_le (n : ℕ) : a n ≤ n * M n := by
  dsimp [a, M]
  calc
    _ ≤ (Finset.Icc 1 n).sum (fun k => min (n.choose k) (2 ^ k)) := by
      apply Finset.sum_le_sum
      intro k hk
      apply mod_le_min
      positivity
    _ ≤ (Finset.Icc 1 n).sum (fun _ => (Finset.range (n + 1)).sup (fun k => min (n.choose k) (2 ^ k))) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.le_sup (f := fun k => min (n.choose k) (2 ^ k))
      have hk_le : k ≤ n := (Finset.mem_Icc.mp hk).2
      exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk_le)
    _ = n * (Finset.range (n + 1)).sup (fun k => min (n.choose k) (2 ^ k)) := by
      rw [Finset.sum_const]
      have : (Finset.Icc 1 n).card = n := by
        cases n <;> simp
      rw [this, smul_eq_mul]
