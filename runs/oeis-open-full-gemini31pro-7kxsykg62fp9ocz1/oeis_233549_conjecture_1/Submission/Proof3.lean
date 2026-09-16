import Mathlib

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card <| Finset.filter (fun p : ℕ =>
    p.Prime ∧
    let q := n - p
    Nat.Prime ((p.totient * q.totient) ^ 4 + 1)
  ) (Finset.range n)

lemma extract_p {n : ℕ} (h : 0 < a n) :
    ∃ p < n, p.Prime ∧ Nat.Prime ((p.totient * (n - p).totient) ^ 4 + 1) := by
  have h1 := Finset.card_pos.mp h
  rcases h1 with ⟨p, hp⟩
  rw [Finset.mem_filter] at hp
  rcases hp with ⟨hp_range, hp_cond⟩
  rw [Finset.mem_range] at hp_range
  exact ⟨p, hp_range, hp_cond⟩
