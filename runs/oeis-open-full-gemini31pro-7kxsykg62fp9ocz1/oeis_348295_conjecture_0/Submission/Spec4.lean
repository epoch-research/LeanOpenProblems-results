import Mathlib

lemma sum_shift (f : ℕ → ℤ) (P K : ℕ) :
  Finset.sum (Finset.Ioc P (P + K)) f = Finset.sum (Finset.Ioc 0 K) (fun k => f (P + k)) := by
  apply Finset.sum_bij (fun k _ => k - P)
  · intro k hk
    rw [Finset.mem_Ioc] at hk ⊢
    omega
  · intro k₁ hk₁ k₂ hk₂ h
    rw [Finset.mem_Ioc] at hk₁ hk₂
    omega
  · intro k hk
    refine ⟨k + P, ?_, ?_⟩
    · rw [Finset.mem_Ioc] at hk ⊢
      omega
    · omega
  · intro k hk
    rw [Finset.mem_Ioc] at hk
    have : P + (k - P) = k := by omega
    rw [this]
