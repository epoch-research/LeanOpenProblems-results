import FormalConjectures.Util.ProblemImports

open Nat

/--
A290472: Number of ways to write $6n+1$ as $x^2 + 3y^2 + 7z^2$, where $x$ is a positive integer, and $y$ and $z$ are nonnegative integers.
-/
def a (n : ℕ) : ℕ :=
  let N : ℕ := 6 * n + 1
  -- A search bound R is sufficient since x, y, z are at most sqrt(N).
  let R : ℕ := Nat.sqrt N + 1

  let X := Finset.range R
  let Y := Finset.range R
  let Z := Finset.range R

  -- The search space is the Cartesian product of the three ranges.
  let search_space := X.product (Y.product Z)

  Finset.card $ Finset.filter (fun p : ℕ × (ℕ × ℕ) =>
    let x := p.fst
    let y := p.snd.fst
    let z := p.snd.snd

    -- Constraint 1: x must be positive (x \in \mathbb{Z}_{>0})
    x > 0 ∧
    -- Constraint 2: The equation must hold
    x * x + 3 * y * y + 7 * z * z = N
  ) search_space

/--
In support of the first conjecture, a(n) > 1 for $286 < n \le 10^7$.
-/
def check_conjecture (high : ℕ) (fuel : ℕ) (n : ℕ) : Bool :=
  match fuel with
  | 0 => true
  | fuel + 1 =>
    if n > high then
      true
    else if decide (a n > 1) then
      check_conjecture high fuel (n + 1)
    else
      false

lemma check_conjecture_true_aux {high : ℕ} (fuel : ℕ) (n : ℕ)
    (hcheck : check_conjecture high fuel n = true) :
    ∀ k : ℕ, n ≤ k → k < n + fuel → k ≤ high → a k > 1 := by
  induction fuel generalizing n with
  | zero =>
    intro k hnk hk_fuel hkh
    omega
  | succ f ih =>
    intro k hnk hk_fuel hkh
    unfold check_conjecture at hcheck
    by_cases hgt : n > high
    · omega
    · by_cases hpn : decide (a n > 1) = true
      · by_cases h_eq : n = k
        · rw [← h_eq]
          exact of_decide_eq_true hpn
        · have hnk_next : n + 1 ≤ k := by omega
          have hk_fuel_next : k < (n + 1) + f := by omega
          have hcheck_next : check_conjecture high f (n + 1) = true := by
            simp [hgt, hpn] at hcheck
            exact hcheck
          exact ih (n + 1) hcheck_next k hnk_next hk_fuel_next hkh
      · simp [hgt, hpn] at hcheck

lemma check_conjecture_true {high : ℕ} (fuel : ℕ) (n : ℕ)
    (hcheck : check_conjecture high fuel n = true) (k : ℕ) (hnk : n ≤ k) (hk_fuel : k < n + fuel) (hkh : k ≤ high) :
    a k > 1 :=
  check_conjecture_true_aux fuel n hcheck k hnk hk_fuel hkh

theorem oeis_290472_conjecture_3 :
  ∀ n : ℕ, 286 < n ∧ n ≤ 10000000 → a n > 1 :=
by
  sorry
