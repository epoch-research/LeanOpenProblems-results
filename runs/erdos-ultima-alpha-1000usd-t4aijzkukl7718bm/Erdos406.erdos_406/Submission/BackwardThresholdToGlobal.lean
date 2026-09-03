import FormalConjecturesUtil

/-! Enlarging a cover below a cutoff turns threshold-only backward closure
into global backward closure, without changing its rejected cutoff seed. -/
namespace Erdos406BackwardThresholdToGlobal

def enlarge (B : ℕ) (Q : ℕ → Prop) (n : ℕ) : Prop := (0 < n ∧ n < B) ∨ Q n

theorem backward (B : ℕ) (Q : ℕ → Prop)
    (hback : ∀ n, B ≤ n → Q (4 * n) → Q n) :
    ∀ n, enlarge B Q (4 * n) → enlarge B Q n := by
  intro n hn
  by_cases hz : n = 0
  · subst n
    simpa only [mul_zero] using hn
  by_cases hsmall : n < B
  · exact Or.inl ⟨Nat.pos_of_ne_zero hz, hsmall⟩
  rcases hn with hn | hn
  · obtain ⟨_, hb⟩ := hn
    omega
  · exact Or.inr (hback n (by omega) hn)

theorem seed (B : ℕ) (Q : ℕ → Prop) : ¬ enlarge B Q B ↔ ¬ Q B := by
  simp [enlarge]

theorem covers (B : ℕ) (Q : ℕ → Prop)
    (hcover : ∀ n, 0 < n → Nat.digits 3 n ⊆ [0, 1] → Q n) :
    ∀ n, 0 < n → Nat.digits 3 n ⊆ [0, 1] → enlarge B Q n := by
  intro n hn hg
  exact Or.inr (hcover n hn hg)

#print axioms backward
#print axioms seed
#print axioms covers
end Erdos406BackwardThresholdToGlobal
