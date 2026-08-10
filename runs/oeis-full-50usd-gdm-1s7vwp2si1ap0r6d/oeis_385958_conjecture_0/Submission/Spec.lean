import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A helper function to find the largest prime $p$ such that $p-1$ divides $2 \cdot k$.
This is the definition of $a(n)$ given $b(n-1)=k$.
Since $k \ge 1$, $2k \ge 2$, and the set of such primes is non-empty (it always contains $p=2$).
-/
noncomputable def largest_prime_divisor_property (k : ℕ) : ℕ :=
  -- Generate candidates p = d + 1 where d is a divisor of 2k. Filter for primes and find the max.
  let candidates := Finset.image (fun d => d + 1) (2 * k).divisors
  let max_prime := candidates.filter Nat.Prime |> Finset.max
  max_prime.getD 0

lemma three_mem_candidates (k : ℕ) (hk : k ≥ 1) : 3 ∈ (Finset.image (fun d => d + 1) (2 * k).divisors).filter Nat.Prime := by
  simp only [mem_filter]
  refine ⟨?_, Nat.prime_three⟩
  simp only [mem_image]
  use 2
  refine ⟨?_, rfl⟩
  simp only [mem_divisors]
  have h2k : 2 * k ≠ 0 := by omega
  refine ⟨?_, h2k⟩
  exact dvd_mul_right 2 k

lemma prime_largest_prime_divisor_property (k : ℕ) (hk : k ≥ 1) :
    (largest_prime_divisor_property k).Prime := by
  simp only [largest_prime_divisor_property]
  set s := (Finset.image (fun d => d + 1) (2 * k).divisors).filter Nat.Prime
  have h3 : 3 ∈ s := three_mem_candidates k hk
  have hmax := Finset.le_max h3
  rcases h_eq : s.max with _|m
  · rw [h_eq] at hmax
    cases hmax
  · simp only [Option.getD_some]
    have hm : m ∈ s := Finset.mem_of_max h_eq
    rw [mem_filter] at hm
    exact hm.2

/--
A385959: The auxiliary sequence $b(n)$.
$b(0) = 1$.
$b(n) = b(n-1) \cdot \frac{a(n)+1}{a(n)-1}$.
-/
noncomputable def b : ℕ → ℕ
| 0 => 1
| n + 1 =>
  let b_prev := b n;
  let p := largest_prime_divisor_property b_prev;
  -- b(n+1) = b_prev + b_prev * 2 / (p - 1)
  b_prev + b_prev * 2 / (p - 1)

lemma largest_prime_divisor_property_sub_one_dvd (k : ℕ) (hk : k ≥ 1) :
    largest_prime_divisor_property k - 1 ∣ 2 * k := by
  simp only [largest_prime_divisor_property]
  set s := (Finset.image (fun d => d + 1) (2 * k).divisors).filter Nat.Prime
  have h3 : 3 ∈ s := three_mem_candidates k hk
  have hmax := Finset.le_max h3
  rcases h_eq : s.max with _|m
  · rw [h_eq] at hmax
    cases hmax
  · simp only [Option.getD_some]
    have hm : m ∈ s := Finset.mem_of_max h_eq
    rw [mem_filter] at hm
    rcases hm with ⟨hm1, _⟩
    rw [mem_image] at hm1
    rcases hm1 with ⟨d, hd, rfl⟩
    rw [mem_divisors] at hd
    have h_sub : d + 1 - 1 = d := by omega
    rw [h_sub]
    exact hd.1

lemma largest_prime_divisor_property_ge_three (k : ℕ) (hk : k ≥ 1) :
    largest_prime_divisor_property k ≥ 3 := by
  simp only [largest_prime_divisor_property]
  set s := (Finset.image (fun d => d + 1) (2 * k).divisors).filter Nat.Prime
  have h3 : 3 ∈ s := three_mem_candidates k hk
  have hmax := Finset.le_max h3
  rcases h_eq : s.max with _|m
  · rw [h_eq] at hmax
    cases hmax
  · rw [h_eq] at hmax
    simp only [Option.getD_some]
    exact WithBot.coe_le_coe.mp hmax

lemma b_pos (n : ℕ) : b n ≥ 1 := by
  induction n with
  | zero => simp [b]
  | succ m ih =>
    simp only [b]
    have : b m + b m * 2 / (largest_prime_divisor_property (b m) - 1) ≥ b m := Nat.le_add_right (b m) _
    omega

lemma b_gt_n (n : ℕ) : b n ≥ n + 1 := by
  induction n with
  | zero =>
    simp [b]
  | succ m ih =>
    simp only [b]
    have h_bm_pos : b m ≥ 1 := b_pos m
    have h_div := largest_prime_divisor_property_sub_one_dvd (b m) h_bm_pos
    have h_ge3 := largest_prime_divisor_property_ge_three (b m) h_bm_pos
    have h_p_sub_one_pos : largest_prime_divisor_property (b m) - 1 > 0 := by omega
    have h_dvd_le := Nat.le_of_dvd (by omega) h_div
    have h_term_pos : b m * 2 / (largest_prime_divisor_property (b m) - 1) ≥ 1 := by
      rw [mul_comm]
      apply Nat.div_pos h_dvd_le h_p_sub_one_pos
    omega

/--
A385958: $a(n)$ is the largest prime $p$ such that $b(n) = b(n-1) \cdot \frac{p+1}{p-1}$ is an integer (A385959), where $b(0) = 1$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n > 0 then
    largest_prime_divisor_property (b (n - 1))
  else 0

/--
Conjecture: Does this sequence contain all odd primes?
Formalization: For every odd prime $p$, there exists $n \in \mathbb{N}^+$, $a(n) = p$.
-/
theorem oeis_385958_conjecture_0 : ∀ (p : ℕ), Nat.Prime p → p ≠ 2 → ∃ (n : ℕ+), a n = p := by
  sorry
