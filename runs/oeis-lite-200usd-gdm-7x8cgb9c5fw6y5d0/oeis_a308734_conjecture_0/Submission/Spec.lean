import FormalConjectures.Util.ProblemImports

open Nat Finset

def A308734 (n : ℕ) : ℕ :=
  let M := Nat.sqrt n + 1

  Finset.sum (range M) fun a =>
  Finset.sum (range M) fun b =>
  Finset.sum (range M) fun c =>
  Finset.sum (range M) fun d =>
  Finset.sum (range M) fun x =>
  Finset.sum (range M) fun y =>
    let term1 := (2^a * 3^b)^2
    let term2 := (2^c * 5^d)^2

    if term1 + term2 + x^2 + y^2 = n ∧ x ≤ y
    then 1
    else 0

def Representable (n : ℕ) : Prop :=
  ∃ a b c d x y : ℕ,
    a < Nat.sqrt n + 1 ∧
    b < Nat.sqrt n + 1 ∧
    c < Nat.sqrt n + 1 ∧
    d < Nat.sqrt n + 1 ∧
    x < Nat.sqrt n + 1 ∧
    y < Nat.sqrt n + 1 ∧
    (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n ∧ x ≤ y

lemma Representable_pos (n : ℕ) (h : Representable n) : A308734 n > 0 := sorry

theorem oeis_a308734_conjecture_0 : ∀ n : ℕ, 1 < n → A308734 n > 0 := by
  intro n hn
  apply Representable_pos
  sorry
