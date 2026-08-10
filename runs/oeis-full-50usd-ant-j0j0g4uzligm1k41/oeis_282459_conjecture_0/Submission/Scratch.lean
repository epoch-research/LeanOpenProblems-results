import Mathlib

open Nat

def A282459 (n : ℕ) : ℕ :=
  let upper_k : ℕ := log 2 (2 * n + 1)
  let s := Finset.Icc 1 upper_k
  let is_composite (m : ℕ) : Prop := 1 < m ∧ ¬ Nat.Prime m
  let seq_val (k : ℕ) : ℕ := 2 * n + 1 - 2 ^ k
  Finset.card (Finset.filter (fun k : ℕ => is_composite (seq_val k)) s)

-- Helper: a number divisible by d with 1 < d < m is not prime.
example (d m : ℕ) (hd1 : 1 < d) (hdm : d < m) (hdvd : d ∣ m) : ¬ Nat.Prime m := by
  intro hp
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp d hdvd) with h | h
  · omega
  · omega

-- Reduction: A282459 n > 0 iff there is k in [1, log 2 (2n+1)] with seq_val composite.
example (n : ℕ) (k : ℕ) (hk : k ∈ Finset.Icc 1 (log 2 (2*n+1)))
    (hcomp : 1 < 2*n+1 - 2^k ∧ ¬ Nat.Prime (2*n+1 - 2^k)) : A282459 n > 0 := by
  unfold A282459
  simp only
  rw [gt_iff_lt, Finset.card_pos]
  exact ⟨k, by rw [Finset.mem_filter]; exact ⟨hk, hcomp⟩⟩

-- log bound
example (n : ℕ) (hn : n > 52) : 6 ≤ log 2 (2*n+1) := by
  rw [← Nat.pow_le_iff_le_log (by norm_num) (by omega)]
  norm_num
  omega

-- witness lemma
theorem witness (n d k : ℕ) (hk1 : 1 ≤ k) (hk6 : k ≤ 6) (hn : n > 52)
    (hd1 : 1 < d) (hdvd : d ∣ (2*n+1 - 2^k)) (hdlt : d < 2*n+1 - 2^k) :
    A282459 n > 0 := by
  unfold A282459
  simp only
  rw [gt_iff_lt, Finset.card_pos]
  refine ⟨k, ?_⟩
  rw [Finset.mem_filter, Finset.mem_Icc]
  have hlog : 6 ≤ log 2 (2*n+1) := by
    rw [← Nat.pow_le_iff_le_log (by norm_num) (by omega)]; norm_num; omega
  refine ⟨⟨hk1, by omega⟩, by omega, ?_⟩
  intro hp
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp d hdvd) with h | h
  · omega
  · omega
