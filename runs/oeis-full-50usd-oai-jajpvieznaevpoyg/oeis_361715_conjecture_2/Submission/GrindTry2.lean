import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  ∑ k ∈ range n, (n.choose k) ^ 2 * multichoose n k

theorem test_ne (p r : ℕ) (hp : Nat.Prime p) (hr : 2 ≤ r) : p ^ r ≠ p ^ (r - 1) := by
  intro h
  have hp2 : 2 ≤ p := hp.two_le
  have := Nat.pow_right_injective hp2 h
  omega

theorem oeis_361715_conjecture_2 (p r : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 2 ≤ r) :
  (a (p ^ r) : ℤ) ≡ a (p ^ (r - 1)) [ZMOD (p ^ (3 * r + 3) : ℕ)] := by
  have hne : p ^ r ≠ p ^ (r - 1) := test_ne p r hp hr
  have hne2_nat : p ^ 3 ≠ p ^ (3 * r) := by
    intro h
    have hp2 : 2 ≤ p := hp.two_le
    have := Nat.pow_right_injective hp2 h
    omega
  have hne2 : (p : ℤ) ^ 3 ≠ (p : ℤ) ^ (3 * r) := by
    intro h
    apply hne2_nat
    exact_mod_cast h
  have hfunne :
      (fun x => (p ^ r).choose x ^ 2 * (p ^ r).multichoose x) ≠
        (fun x => (p ^ (r - 1)).choose x ^ 2 * (p ^ (r - 1)).multichoose x) := by
    intro h
    have h1 := congrFun h 1
    simp [Nat.choose_one_right, Nat.multichoose_one_right] at h1
    have hp2 : 2 ≤ p := hp.two_le
    have hinj := Nat.pow_right_injective hp2 h1
    omega

  grind [a]
