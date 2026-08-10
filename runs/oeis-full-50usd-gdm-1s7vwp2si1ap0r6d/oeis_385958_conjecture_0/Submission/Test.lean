import FormalConjectures.Util.ProblemImports

open Nat Finset

noncomputable def largest_prime_divisor_property (k : ℕ) : ℕ :=
  let candidates := Finset.image (fun d => d + 1) (2 * k).divisors
  let max_prime := candidates.filter Nat.Prime |> Finset.max
  max_prime.getD 0

noncomputable def b : ℕ → ℕ
| 0 => 1
| n + 1 =>
  let b_prev := b n;
  let p := largest_prime_divisor_property b_prev;
  b_prev + b_prev * 2 / (p - 1)

noncomputable def a (n : ℕ) : ℕ :=
  if n > 0 then
    largest_prime_divisor_property (b (n - 1))
  else 0

lemma a_one_eq_three : a 1 = 3 := by rfl
lemma a_two_eq_five : a 2 = 5 := by rfl
lemma a_three_eq_seven : a 3 = 7 := by rfl


lemma prime_largest_prime_divisor_property (k : ℕ) (h : k ≥ 1) :
    (largest_prime_divisor_property k).Prime := by
  sorry


lemma b_gt_n (n : ℕ) : b n ≥ n + 1 := by
  induction n with
  | zero =>
    simp [b]
  | succ m ih =>
    simp only [b]
    -- b (m + 1) = b m + b m * 2 / (largest_prime_divisor_property (b m) - 1)
    -- since largest_prime_divisor_property (b m) - 1 divides 2 * b m and is <= 2 * b m, the term is >= 1.
    sorry

lemma exists_three : ∃ (n : ℕ+), a n = 3 := ⟨⟨1, Nat.one_pos⟩, by rfl⟩



lemma a_fifty_eq_eleven : a 50 = 11 := by rfl
