import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A084046: Smallest prime $p$ such that $p + n$ is an $n$-th power, or $0$ if no such number exists.
I.e., smallest prime of the form $k^n - n$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- S_n is the set of primes p such that p + n is an n-th power, i.e., p = k^n - n.
  let S_n : Set ℕ := { p | Nat.Prime p ∧ ∃ k : ℕ, k ^ n = p + n }
  -- sInf S_n returns the smallest element of S_n. For Nat, sInf ∅ = 0, fitting the problem statement.
  sInf S_n

/-- Disproof: `27` is not an even square, but every number of the form
`x^27 - 27 = (x^9)^3 - 3^3` is composite. -/
theorem a084046_conjecture_0.disproof :
  ¬ (∀ k : ℕ, a k = 0 → ∃ m : ℕ, k = (2 * m) ^ 2) := by
  have no_candidate : ∀ x p : ℕ, Nat.Prime p → x ^ 27 = p + 27 → False := by
    intro x p hp h
    have hx2 : 2 ≤ x := by
      by_contra hxnot
      have hxle : x ≤ 1 := by omega
      interval_cases x <;> norm_num at h
    have hx9 : 3 ≤ x ^ 9 := by
      have hx9big : 2 ^ 9 ≤ x ^ 9 := Nat.pow_le_pow_left hx2 9
      norm_num at hx9big
      omega
    let d := x ^ 9 - 3
    let e := x ^ 18 + 3 * x ^ 9 + 9
    have hp_eq : p = d * e := by
      dsimp [d, e]
      have hfac : (x ^ 9 - 3) * (x ^ 18 + 3 * x ^ 9 + 9) + 27 = x ^ 27 := by
        have hx' : x ^ 9 - 3 + 3 = x ^ 9 := Nat.sub_add_cancel hx9
        nlinarith [sq_nonneg (x ^ 9 : ℤ)]
      omega
    have hdvd : d ∣ p := by
      rw [hp_eq]
      exact dvd_mul_right d e
    have hdgt1 : 1 < d := by
      dsimp [d]
      have hx9big : 2 ^ 9 ≤ x ^ 9 := Nat.pow_le_pow_left hx2 9
      norm_num at hx9big
      omega
    have hdne1 : d ≠ 1 := by omega
    have hegt1 : 1 < e := by
      dsimp [e]
      omega
    have hdp : d ≠ p := by
      intro hdp
      have hdeq : d = d * e := by
        simpa [← hdp] using hp_eq
      nlinarith
    rcases hp.eq_one_or_self_of_dvd d hdvd with h1 | hself
    · exact hdne1 h1
    · exact hdp hself
  have ha27 : a 27 = 0 := by
    unfold a
    have hEmpty : {p | Nat.Prime p ∧ ∃ x : ℕ, x ^ 27 = p + 27} = ∅ := by
      ext p
      constructor
      · intro hpS
        rcases hpS with ⟨hp, x, hx⟩
        exact False.elim (no_candidate x p hp hx)
      · intro hpEmpty
        cases hpEmpty
    simp [hEmpty, Nat.sInf_empty]
  intro hconj
  rcases hconj 27 ha27 with ⟨m, hm⟩
  have hmle : m ≤ 2 := by
    by_contra hmnot
    have hm3 : 3 ≤ m := by omega
    have hsq : 36 ≤ (2 * m) ^ 2 := by nlinarith
    omega
  interval_cases m <;> norm_num at hm
