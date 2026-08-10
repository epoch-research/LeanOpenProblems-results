import FormalConjectures.Util.ProblemImports

open Nat Finset Set

/--
A295124: $a(n)$ is the smallest number $k$ with $n$ prime factors such that $2d + k/d$ is prime for every $d \mid k$.
The definition interprets "n prime factors" as $n$ distinct prime factors ($\omega(k) = n$).
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- Define the set of candidate numbers $k$ for a given $n$.
  let S (n : ℕ) : Set ℕ :=
    {k : ℕ | k > 0 ∧
      -- $\omega(k) = n$, k has n distinct prime factors.
      (Nat.primeFactors k).card = n ∧
      -- For every divisor d of k, $2d + k/d$ is prime.
      (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))}

  -- $a(n)$ is the smallest element of this set. sInf is the infimum function on sets of ℕ.
  sInf (S n)

/-- Conjecture: the sequence is infinite. It is hard to believe!
This is formalized as the set $S(n)$ of candidate numbers being non-empty for all $n$. -/
theorem oeis_295124_conjecture_0 :
  ∀ n : ℕ, (({k : ℕ | k > 0 ∧
              (Nat.primeFactors k).card = n ∧
              (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))}) : Set ℕ).Nonempty := by
  intro n
  rcases n with _ | _ | _ | _ | _ | n
  · use 1
    refine ⟨by decide, ?_, by decide⟩
    simp [Nat.primeFactors]
  · use 3
    refine ⟨by decide, ?_, ?_⟩
    · have hpf : Nat.primeFactors 3 = {3} := by
        ext x
        rw [Nat.mem_primeFactors]
        constructor
        · rintro ⟨hp, hdvd⟩
          have hmem : x ∈ Nat.divisors 3 := by
            rw [Nat.mem_divisors]
            exact hdvd
          have hdiv : Nat.divisors 3 = {1, 3} := by decide
          rw [hdiv] at hmem
          simp at hmem
          rcases hmem with rfl | rfl
          · exfalso; exact Nat.not_prime_one hp
          · simp
        · intro h
          simp at h
          rcases h with rfl
          refine ⟨by decide, by decide, by decide⟩
      rw [hpf]
      simp
    · intro d hd
      have hdiv : Nat.divisors 3 = {1, 3} := by decide
      rw [hdiv] at hd
      simp at hd
      rcases hd with rfl | rfl <;> (simp; decide)
  · use 15
    refine ⟨by decide, ?_, ?_⟩
    · have hpf : Nat.primeFactors 15 = {3, 5} := by
        ext x
        rw [Nat.mem_primeFactors]
        constructor
        · rintro ⟨hp, hdvd⟩
          have hmem : x ∈ Nat.divisors 15 := by
            rw [Nat.mem_divisors]
            exact hdvd
          have hdiv : Nat.divisors 15 = {1, 3, 5, 15} := by decide
          rw [hdiv] at hmem
          simp at hmem
          rcases hmem with rfl | rfl | rfl | rfl
          · exfalso; exact Nat.not_prime_one hp
          · simp
          · simp
          · exfalso; exact (by decide : ¬ Nat.Prime 15) hp
        · intro h
          simp at h
          rcases h with rfl | rfl <;> refine ⟨by decide, by decide, by decide⟩
      rw [hpf]
      simp
    · intro d hd
      have hdiv : Nat.divisors 15 = {1, 3, 5, 15} := by decide
      rw [hdiv] at hd
      simp at hd
      rcases hd with rfl | rfl | rfl | rfl <;> (simp; decide)
  · use 105
    refine ⟨by decide, ?_, ?_⟩
    · have hpf : Nat.primeFactors 105 = {3, 5, 7} := by
        ext x
        rw [Nat.mem_primeFactors]
        constructor
        · rintro ⟨hp, hdvd⟩
          have hmem : x ∈ Nat.divisors 105 := by
            rw [Nat.mem_divisors]
            exact hdvd
          have hdiv : Nat.divisors 105 = {1, 3, 5, 7, 15, 21, 35, 105} := by decide
          rw [hdiv] at hmem
          simp at hmem
          rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> try simp <;> (exfalso; revert hp; decide)
        · intro h
          simp at h
          rcases h with rfl | rfl | rfl <;> refine ⟨by decide, by decide, by decide⟩
      rw [hpf]
      simp
    · intro d hd
      have hdiv : Nat.divisors 105 = {1, 3, 5, 7, 15, 21, 35, 105} := by decide
      rw [hdiv] at hd
      simp at hd
      rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
  · use 93081
    refine ⟨by decide, ?_, ?_⟩
    · have h_prod : 93081 = ∏ p ∈ ({3, 19, 23, 71} : Finset ℕ), p := by decide
      rw [h_prod]
      have hpf : Nat.primeFactors (∏ p ∈ ({3, 19, 23, 71} : Finset ℕ), p) = {3, 19, 23, 71} := Nat.primeFactors_prod (by decide)
      rw [hpf]
      decide
    · intro d hd
      have h_mul : 93081 = 3 * (19 * (23 * 71)) := by decide
      have hdiv : Nat.divisors 93081 = {1, 3, 19, 23, 57, 69, 71, 213, 437, 1311, 1349, 1633, 4047, 4899, 31027, 93081} := by
        rw [h_mul]
        rw [Nat.divisors_mul, Nat.divisors_mul, Nat.divisors_mul]
        have h3 : Nat.divisors 3 = {1, 3} := by decide
        have h19 : Nat.divisors 19 = {1, 19} := by decide
        have h23 : Nat.divisors 23 = {1, 23} := by decide
        have h71 : Nat.divisors 71 = {1, 71} := by decide
        rw [h3, h19, h23, h71]
        decide
      rw [hdiv] at hd
      simp at hd
      rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
  · sorry
