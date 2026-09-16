import Mathlib

def P (n : Nat) : Prop := n >= 0

theorem combine {A B C : Nat} (hAB : A <= B) (hBC : B <= C)
  (h1 : ∀ n, A <= n ∧ n < B → P n)
  (h2 : ∀ n, B <= n ∧ n < C → P n) :
  ∀ n, A <= n ∧ n < C → P n := by
  intro n hn
  if h : n < B then
    exact h1 n ⟨hn.1, h⟩
  else
    have h' : B <= n := Nat.le_of_not_lt h
    exact h2 n ⟨h', hn.2⟩
