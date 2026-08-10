import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false
set_option exponentiation.threshold 10000000
set_option maxRecDepth 5000000
set_option maxHeartbeats 0

open Nat Set Finset

def count_unitary_divs_sqrt_loop (n d acc : ℕ) : ℕ → ℕ
  | 0 => acc
  | fuel + 1 =>
    if d * d > n then acc
    else
      let acc' := if n % d = 0 then
                    if d.gcd (n / d) = 1 then
                      if d * d = n then acc + 1
                      else acc + 2
                    else acc
                  else acc
      count_unitary_divs_sqrt_loop n (d + 1) acc' fuel

def count_unitary_divs_sqrt (n : ℕ) : ℕ :=
  count_unitary_divs_sqrt_loop n 1 0 n

def unitary_divs_sqrt_sum (n d : ℕ) : ℕ :=
  ((((List.Ico d (Nat.sqrt n + 1)).filter fun x => n % x = 0).filter fun x => x.gcd (n / x) = 1).map fun x => if x * x = n then 1 else 2).sum

theorem count_unitary_divs_sqrt_loop_eq_sum (n d acc fuel : ℕ) (h_fuel : Nat.sqrt n + 1 - d ≤ fuel) :
  count_unitary_divs_sqrt_loop n d acc fuel = acc + unitary_divs_sqrt_sum n d := by
  induction fuel generalizing d acc with
  | zero =>
    unfold count_unitary_divs_sqrt_loop
    have hd2 : Nat.sqrt n + 1 ≤ d := by omega
    have h_gt : d * d > n := Nat.sqrt_lt.mp hd2
    -- now we show unitary_divs_sqrt_sum n d = 0
    have h_ico : List.Ico d (Nat.sqrt n + 1) = [] := List.Ico.eq_nil_of_le hd2
    unfold unitary_divs_sqrt_sum
    rw [h_ico]
    simp
  | succ fuel ih =>
    unfold count_unitary_divs_sqrt_loop
    by_cases h_gt : d * d > n
    · -- d * d > n
      rw [if_pos h_gt]
      have hd2 : Nat.sqrt n + 1 ≤ d := Nat.sqrt_lt.mpr h_gt
      have h_ico : List.Ico d (Nat.sqrt n + 1) = [] := List.Ico.eq_nil_of_le hd2
      unfold unitary_divs_sqrt_sum
      rw [h_ico]
      simp
    · -- d * d <= n
      rw [if_neg h_gt]
      have hd_le : d ≤ Nat.sqrt n := Nat.le_sqrt.mpr (Nat.le_of_not_lt h_gt)
      have hd : d < Nat.sqrt n + 1 := by omega
      have h_ico : List.Ico d (Nat.sqrt n + 1) = d :: List.Ico (d + 1) (Nat.sqrt n + 1) := List.Ico.eq_cons hd
      unfold unitary_divs_sqrt_sum
      rw [h_ico]
      simp only [List.filter_cons, List.map, List.sum_cons]
      -- unfold unitary_divs_sqrt_sum in ih to match
      unfold unitary_divs_sqrt_sum at ih
      by_cases h_mod : n % d = 0
      · rw [if_pos (by simp [h_mod])]
        by_cases h_gcd : d.gcd (n / d) = 1
        · rw [if_pos (by simp [h_gcd])]
          by_cases h_sq : d * d = n
          · rw [if_pos (by simp [h_sq])]
            have h_fuel2 : Nat.sqrt n + 1 - (d + 1) ≤ fuel := by omega
            rw [ih (d := d + 1) (acc := acc + 1) h_fuel2]
            omega
          · rw [if_neg (by simp [h_sq])]
            have h_fuel2 : Nat.sqrt n + 1 - (d + 1) ≤ fuel := by omega
            rw [ih (d := d + 1) (acc := acc + 2) h_fuel2]
            omega
        · rw [if_neg (by simp [h_gcd])]
          have h_fuel2 : Nat.sqrt n + 1 - (d + 1) ≤ fuel := by omega
          rw [ih (d := d + 1) (acc := acc) h_fuel2]
          omega
      · rw [if_neg (by simp [h_mod])]
        have h_fuel2 : Nat.sqrt n + 1 - (d + 1) ≤ fuel := by omega
        rw [ih (d := d + 1) (acc := acc) h_fuel2]
        omega

def count_unitary_divs_loop (n d acc : ℕ) : ℕ :=
  match d with
  | 0 => acc
  | d + 1 =>
    let acc' := if n % (d + 1) = 0 then
                  if (d + 1).gcd (n / (d + 1)) = 1 then acc + 1
                  else acc
                else acc
    count_unitary_divs_loop n d acc'

def count_unitary_divs (n : ℕ) : ℕ :=
  count_unitary_divs_loop n n 0

theorem count_eq_all : ∀ n < 2310, count_unitary_divs n = count_unitary_divs_sqrt n := by decide














