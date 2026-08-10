/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

open Nat ArithmeticFunction Rat

namespace Submission

set_option maxRecDepth 2000000
set_option maxHeartbeats 50000000

def sqrt_fast_aux (guess : ℕ) (n : ℕ) : ℕ :=
  match guess with
  | 0 => 0
  | g + 1 =>
    if (g + 1) * (g + 1) <= n then g + 1
    else sqrt_fast_aux g n

def sqrt_fast (n : ℕ) : ℕ :=
  sqrt_fast_aux 66 n

def sum_divisors_aux (n : ℕ) (i : ℕ) (acc : ℕ) : ℕ :=
  match i with
  | 0 => acc
  | i' + 1 =>
    if n % (i' + 1) == 0 then
      let d1 := i' + 1
      let d2 := n / d1
      if d1 == d2 then sum_divisors_aux n i' (acc + d1)
      else sum_divisors_aux n i' (acc + d1 + d2)
    else sum_divisors_aux n i' acc

def sigma_fast (n : ℕ) : ℕ :=
  sum_divisors_aux n (sqrt_fast n) 0

def gcd_fast_aux (fuel : ℕ) (a b : ℕ) : ℕ :=
  match fuel with
  | 0 => a
  | fuel' + 1 =>
    if b = 0 then a
    else gcd_fast_aux fuel' b (a % b)

def gcd_fast (a b : ℕ) : ℕ :=
  gcd_fast_aux (a + b) a b

def check_range_66 (fuel : ℕ) (current : ℕ) (limit : ℕ) : Bool :=
  match fuel with
  | 0 => true
  | fuel' + 1 =>
    if current >= limit then true
    else
      if (gcd_fast 66 current == 1 && sigma_fast current == current + 66) then false
      else check_range_66 fuel' (current + 1) limit

theorem check_range_66_sound {fuel : ℕ} {current limit : ℕ} (h : check_range_66 fuel current limit = true) :
    ∀ x, current <= x → x < limit → x < current + fuel → gcd_fast 66 x = 1 → sigma_fast x ≠ x + 66 := by
  induction fuel generalizing current with
  | zero =>
    intro x hx1 hx2 hx3
    omega
  | succ fuel' ih =>
    intro x hx1 hx2 hx3 h_gcd
    dsimp [check_range_66] at h
    split_ifs at h with h_ge
    · omega
    · split_ifs at h with h_cond
      · contradiction
      · have h_rec : check_range_66 fuel' (current + 1) limit = true := h
        by_cases h_eq : current = x
        · subst h_eq
          rw [Bool.and_eq_true, Decidable.beEq_decide_iff, Decidable.beEq_decide_iff] at h_cond
          push_neg at h_cond
          exact h_cond h_gcd
        · have h_gt : current + 1 <= x := by omega
          have h_fuel' : x < current + 1 + fuel' := by omega
          exact ih h_rec x h_gt hx2 h_fuel' h_gcd

theorem test_66_1 : check_range_66 1000 0 1000 = true := by decide
theorem test_66_2 : check_range_66 1000 1000 2000 = true := by decide
theorem test_66_3 : check_range_66 1000 2000 3000 = true := by decide
theorem test_66_4 : check_range_66 1000 3000 4000 = true := by decide
theorem test_66_5 : check_range_66 1000 4000 4226 = true := by decide

end Submission

