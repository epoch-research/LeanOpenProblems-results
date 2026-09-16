import Submission.Lemma
import Mathlib

open Finset

lemma abs_val_repr (b : ℕ) (hb : b ≥ 5) (n : ℕ) (d : ℕ → Int) (hd : ∀ k < n, d k = 1 ∨ d k = -1) :
  ∃ (a : ℕ → ℕ),
    (∀ k < n, a k = 0 ∨ a k = 1 ∨ a k = b - 2 ∨ a k = b - 1) ∧
    (∀ k < n, a k < b) ∧
    ((range n).sum (fun k ↦ d k * (b : Int) ^ k)).natAbs = (range n).sum (fun k ↦ a k * b ^ k) := by
  set V := (range n).sum (fun k ↦ d k * (b : Int) ^ k)
  by_cases hV : 0 ≤ V
  · rcases helper_induction b hb n d hd 0 (by tauto) with ⟨a, C, ha1, hC, ha2, heq⟩
    rw [zero_add] at heq
    have hC0 : C = 0 := by
      rcases hC with rfl | rfl
      · rfl
      · -- C = -1
        have : V < 0 := by
          calc
            V = (range n).sum (fun k ↦ (a k : Int) * (b : Int) ^ k) - (b : Int) ^ n := by linarith
            _ < 0 := by
              -- need to prove sum a k b^k < b^n
              sorry
        linarith
    sorry
  · sorry
