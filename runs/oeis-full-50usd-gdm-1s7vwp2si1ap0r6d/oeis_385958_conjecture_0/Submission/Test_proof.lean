import FormalConjectures.Util.ProblemImports

open Nat Finset

noncomputable def largest_prime_divisor_property (k : ℕ) : ℕ :=
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

lemma largest_prime_divisor_property_ge_three (k : ℕ) (hk : k ≥ 1) :
    largest_prime_divisor_property k ≥ 3 := by
  simp only [largest_prime_divisor_property]
  set s := (Finset.image (fun d => d + 1) (2 * k).divisors).filter Nat.Prime
  have h3 : 3 ∈ s := three_mem_candidates k hk
  have hmax := Finset.le_max h3
  -- s.max is Option ℕ
  rcases h_eq : s.max with _|m
  · rw [h_eq] at hmax
    cases hmax
  · rw [h_eq] at hmax
    simp only [Option.getD_some]
    exact WithBot.coe_le_coe.mp hmax


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

