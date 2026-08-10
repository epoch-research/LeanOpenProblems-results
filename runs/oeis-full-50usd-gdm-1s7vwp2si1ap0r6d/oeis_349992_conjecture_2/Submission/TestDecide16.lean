import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 2000000

open Nat Finset BigOperators

def my_sqrt_fuel (n : ℕ) : ℕ → ℕ → ℕ
  | 0, k => k
  | fuel + 1, k =>
    if (k + 1) * (k + 1) ≤ n then
      my_sqrt_fuel n fuel (k + 1)
    else
      k

def my_sqrt (n : ℕ) : ℕ :=
  my_sqrt_fuel n n 0

def generalized_A349992 (a b c m n : ℕ) : ℕ :=
  if n = 0 then 0 else
  if n > 2 then 1 else
  let bound_x : ℕ := my_sqrt (my_sqrt (n / a)) + 1
  let bound_y : ℕ := my_sqrt (n / b) + 1

  (range bound_x).sum fun x =>
  (range bound_y).sum fun y =>
  (range 2).sum fun w =>
    let full_sum : ℕ := a * x ^ 4 + b * y ^ 2
    let c_term : ℕ := c * 4 ^ w

    if full_sum < n ∧ m > 0 then
      let target_z2 : ℕ := m * (n - full_sum) - c_term

      if c_term ≤ m * (n - full_sum) ∧ (my_sqrt target_z2) ^ 2 = target_z2 then
        1
      else
        0
    else
      0

theorem oeis_349992_conjecture_2 :
  let tuples : List (ℕ × ℕ × ℕ × ℕ) :=
    [(1,1,11,12), (1,1,11,60), (1,1,14,15), (1,1,23,24), (1,1,23,32),
     (1,1,23,48), (1,2,23,96), (2,1,11,60), (2,1,23,24), (2,1,23,48),
     (4,1,23,48)]
  ∀ (t : ℕ × ℕ × ℕ × ℕ) (h_t : t ∈ tuples) (n : ℕ),
    n > 0 →
    let a := t.1
    let b := t.2.1
    let c := t.2.2.1
    let m := t.2.2.2
    generalized_A349992 a b c m n > 0 := by
  intro tuples t h_t n hn
  simp only [tuples, List.mem_cons, List.not_mem_nil] at h_t
  rcases h_t with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_f
  all_goals
    dsimp only
    unfold generalized_A349992
    split_ifs with h1 h2
    · omega
    · decide
    · interval_cases n <;> decide
  · rcases h_f

#print axioms oeis_349992_conjecture_2
