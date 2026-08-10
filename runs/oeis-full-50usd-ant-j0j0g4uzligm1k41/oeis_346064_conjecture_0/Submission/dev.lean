import Mathlib

open Nat List

/-- Value lemma (ℕ, subtraction-free): changing one digit of a list at position `i`
to `v` satisfies `ofDigits b (l.set i v) + l[i]·bⁱ = ofDigits b l + v·bⁱ`. -/
theorem ofDigits_set (b : ℕ) : ∀ (l : List ℕ) (i : ℕ) (v : ℕ) (hi : i < l.length),
    Nat.ofDigits b (l.set i v) + (l[i]'hi) * b ^ i
      = Nat.ofDigits b l + v * b ^ i := by
  intro l
  induction l with
  | nil => intro i v hi; simp at hi
  | cons a t ih =>
    intro i v hi
    cases i with
    | zero =>
      rw [List.set_cons_zero, Nat.ofDigits_cons, Nat.ofDigits_cons]
      simp only [List.getElem_cons_zero, pow_zero, mul_one]
      ring
    | succ k =>
      have hk : k < t.length := by
        simp only [List.length_cons] at hi; omega
      rw [List.set_cons_succ, Nat.ofDigits_cons, Nat.ofDigits_cons]
      simp only [List.getElem_cons_succ, pow_succ]
      have ihk := ih k v hk
      -- goal: (a + b*ofDigits b (t.set k v)) + t[k]*(b^k*b) = (a + b*ofDigits b t) + v*(b^k*b)
      nlinarith [ihk, Nat.zero_le b]
