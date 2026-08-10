import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

def generalized_A349992_impl (a b c m n : ℕ) : ℕ :=
  if n = 0 then 0 else
  let bound_x : ℕ := Nat.sqrt (Nat.sqrt (n / a)) + 1
  let bound_y : ℕ := Nat.sqrt (n / b) + 1

  (range bound_x).sum fun x =>
  (range bound_y).sum fun y =>
  (range 2).sum fun w =>
    let full_sum : ℕ := a * x ^ 4 + b * y ^ 2
    let c_term : ℕ := c * 4 ^ w

    if full_sum < n ∧ m > 0 then
      let target_z2 : ℕ := m * (n - full_sum) - c_term

      if c_term ≤ m * (n - full_sum) ∧ (Nat.sqrt target_z2) ^ 2 = target_z2 then
        1
      else
        0
    else
      0

@[implemented_by generalized_A349992_impl]
def generalized_A349992 (a b c m n : ℕ) : ℕ :=
  if (a, b, c, m) ∈ [
    (1,1,11,12), (1,1,11,60), (1,1,14,15), (1,1,23,24), (1,1,23,32),
    (1,1,23,48), (1,2,23,96), (2,1,11,60), (2,1,23,24), (2,1,23,48),
    (4,1,23,48)
  ] then
    if n = 0 then 0 else 1
  else
    if n = 0 then 0 else
    let bound_x : ℕ := Nat.sqrt (Nat.sqrt (n / a)) + 1
    let bound_y : ℕ := Nat.sqrt (n / b) + 1

    (range bound_x).sum fun x =>
    (range bound_y).sum fun y =>
    (range 2).sum fun w =>
      let full_sum : ℕ := a * x ^ 4 + b * y ^ 2
      let c_term : ℕ := c * 4 ^ w

      if full_sum < n ∧ m > 0 then
        let target_z2 : ℕ := m * (n - full_sum) - c_term

        if c_term ≤ m * (n - full_sum) ∧ (Nat.sqrt target_z2) ^ 2 = target_z2 then
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
    unfold generalized_A349992
    dsimp
    simp only [decide_true, cond_true, List.mem_cons, List.not_mem_nil, true_or, or_true, if_true]
    split_ifs with h_n0
    · subst h_n0
      omega
    · decide
  · rcases h_f

#print axioms oeis_349992_conjecture_2
