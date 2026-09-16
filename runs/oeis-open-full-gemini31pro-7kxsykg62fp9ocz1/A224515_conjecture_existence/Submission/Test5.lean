import Mathlib
open Nat

def F (k : ℕ) : ℕ := k^2 ^^^ (k+1)^2

def step (T M k : ℕ) : ℕ :=
  if F k % 2^(M+3) == T % 2^(M+3) then
    k
  else
    k + 2^(M+1)

def seq (T : ℕ) : ℕ → ℕ
| 0 => 0
| m + 1 => step T m (seq T m)

lemma step_mod (T M k : ℕ) (h_mod : F k % 2^(M+2) = T % 2^(M+2))
  (hF_mod : F (k + 2^(M+1)) % 2^(M+3) = (F k + 2^(M+2)) % 2^(M+3)) :
  F (step T M k) % 2^(M+3) = T % 2^(M+3) := sorry

lemma F_mod_1 (k : ℕ) :
  F (k + 2) % 8 = (F k + 4) % 8 := sorry

lemma F_mod (k L : ℕ) (hL : 2 ≤ L) :
  F (k + 2^L) % 2^(L+2) = (F k + 2^(L+1)) % 2^(L+2) := sorry

lemma seq_mod (T : ℕ) (hT : T % 4 = 1) : ∀ m, F (seq T m) % 2^(m+2) = T % 2^(m+2)
| 0 => by
  have h_seq : seq T 0 = 0 := rfl
  rw [h_seq]
  have h_F : F 0 = 1 := rfl
  rw [h_F]
  exact hT.symm
| m + 1 => by
  have h_seq : seq T (m + 1) = step T m (seq T m) := rfl
  rw [h_seq]
  apply step_mod T m (seq T m) (seq_mod T hT m)
  rcases m with _ | m'
  · exact F_mod_1 (seq T 0)
  · have hL : 2 ≤ m' + 2 := by omega
    have := F_mod (seq T (m' + 1)) (m' + 2) hL
    exact this
