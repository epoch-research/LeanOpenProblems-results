import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

def a (n : ℕ) : ℕ :=
  let A018804_n : ℕ := (Finset.Ico 1 (n + 1)).sum fun k => Nat.gcd k n
  n / Nat.gcd n (1 + A018804_n)

def S (n : ℕ) : ℕ := (Finset.Ico 1 (n + 1)).sum fun k => Nat.gcd k n

theorem a_eq (n : ℕ) : a n = n / Nat.gcd n (1 + S n) := rfl

-- reduction: for n ≥ 1, a n = 1 ↔ n ∣ 1 + S n
example (n : ℕ) (hn : 1 ≤ n) : a n = 1 ↔ n ∣ (1 + S n) := by
  rw [a_eq]
  set d := Nat.gcd n (1 + S n) with hd
  have hdvd : d ∣ n := Nat.gcd_dvd_left _ _
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left _ hn
  constructor
  · intro h
    have hdn : d = n := by
      rcases hdvd with ⟨c, hc⟩
      have hc' : n / d = c := by rw [hc]; exact Nat.mul_div_cancel_left c hdpos
      rw [hc'] at h; subst h
      have := hc; omega
    have hd_dvd : d ∣ 1 + S n := hd ▸ Nat.gcd_dvd_right n (1 + S n)
    exact hdn ▸ hd_dvd
  · intro h
    have hdn : d = n := by rw [hd]; exact Nat.gcd_eq_left h
    rw [hdn]; exact Nat.div_self hn
