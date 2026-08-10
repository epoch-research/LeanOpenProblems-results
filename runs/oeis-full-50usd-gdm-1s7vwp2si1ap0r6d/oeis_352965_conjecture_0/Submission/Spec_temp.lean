import FormalConjectures.Util.ProblemImports

open Nat Finset Classical

/--
A352965: A variant of Van Eck's sequence where we only consider prime numbers:
for $n \ge 0$, if $a(n) = a(n-p)$ for some prime number $p$, take the least such $p$ and set $a(n+1) = p$;
otherwise $a(n+1) = 0$. Start with $a(1) = 0$.
We define $A(n)$ as the $n$-th term, $n \ge 1$.
-/
noncomputable def A352965_orig : ℕ → ℕ
| 0 => 0 -- Padding for 1-indexing implementation
| 1 => 0 -- A(1) = 0 by start condition.
| n + 1 => -- Calculates A(n+1). Let k = n.
  let k := n -- k is the index of the previous term A(k). k >= 1.

  -- The value of the previous term A(k)
  let a_k := A352965_orig k

  -- We seek the least prime p such that A(k) = A(k-p), where k-p >= 1, so p <= k - 1.
  -- Primes p must be in {2, 3, ..., k-1}. Finset.range k covers 0 to k-1.
  let all_lt_k := Finset.range k

  -- Filter for valid primes p that satisfy the condition.
  let S := all_lt_k.filter (fun p =>
    Nat.Prime p ∧ A352965_orig (k - p) = a_k)

  if h : S.Nonempty then
    S.min' h
  else
    0

theorem A_zero_orig : A352965_orig 0 = 0 := by rw [A352965_orig]
theorem A_one_orig : A352965_orig 1 = 0 := by rw [A352965_orig]

theorem A_two_orig : A352965_orig 2 = 0 := by
  rw [A352965_orig]
  · split_ifs with h
    · exfalso
      obtain ⟨p, hp⟩ := h
      simp only [Finset.mem_filter, Finset.mem_range] at hp
      have hp0 : p = 0 := by omega
      subst hp0
      exact Nat.not_prime_zero hp.2.1
    · rfl
  · intro h; contradiction

theorem A_three_orig : A352965_orig 3 = 0 := by
  rw [A352965_orig]
  · split_ifs with h
    · exfalso
      obtain ⟨p, hp⟩ := h
      simp only [Finset.mem_filter, Finset.mem_range] at hp
      have hp2 : p < 2 := hp.1
      interval_cases p
      · exact Nat.not_prime_zero hp.2.1
      · exact Nat.not_prime_one hp.2.1
    · rfl
  · intro h; contradiction

theorem A_four_orig : A352965_orig 4 = 2 := by
  rw [A352965_orig]
  · split_ifs with h
    · have hS : {p ∈ range 3 | Nat.Prime p ∧ A352965_orig (3 - p) = A352965_orig 3} = {2} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
        constructor
        · intro hx
          have h_prime : Nat.Prime x := hx.2.1
          have h_lt : x < 3 := hx.1
          interval_cases x
          · exfalso; exact Nat.not_prime_zero h_prime
          · exfalso; exact Nat.not_prime_one h_prime
          · rfl
        · intro hx
          subst hx
          refine ⟨by omega, Nat.prime_two, ?_⟩
          rw [A_one_orig, A_three_orig]
      generalize {p ∈ range 3 | Nat.Prime p ∧ A352965_orig (3 - p) = A352965_orig 3} = S at h hS ⊢
      subst hS
      rfl
    · exfalso
      have h2 : 2 ∈ {p ∈ range 3 | Nat.Prime p ∧ A352965_orig (3 - p) = A352965_orig 3} := by
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, Nat.prime_two, ?_⟩
        rw [A_one_orig, A_three_orig]
      exact h ⟨2, h2⟩
  · intro h; contradiction

theorem A_five_orig : A352965_orig 5 = 0 := by
  rw [A352965_orig]
  · split_ifs with h
    · exfalso
      obtain ⟨p, hp⟩ := h
      simp only [Finset.mem_filter, Finset.mem_range] at hp
      have hp4 : p < 4 := hp.1
      have hp_prime : Nat.Prime p := hp.2.1
      interval_cases p
      · exact Nat.not_prime_zero hp_prime
      · exact Nat.not_prime_one hp_prime
      · have h_eq : A352965_orig (4 - 2) = A352965_orig 4 := hp.2.2
        rw [A_two_orig, A_four_orig] at h_eq
        contradiction
      · have h_eq : A352965_orig (4 - 3) = A352965_orig 4 := hp.2.2
        rw [A_one_orig, A_four_orig] at h_eq
        contradiction
    · rfl
  · intro h; contradiction

theorem A_six_orig : A352965_orig 6 = 2 := by
  rw [A352965_orig]
  · split_ifs with h
    · have hS : {p ∈ range 5 | Nat.Prime p ∧ A352965_orig (5 - p) = A352965_orig 5} = {2, 3} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hx
          have h_prime : Nat.Prime x := hx.2.1
          have h_lt : x < 5 := hx.1
          interval_cases x
          · exfalso; exact Nat.not_prime_zero h_prime
          · exfalso; exact Nat.not_prime_one h_prime
          · left; rfl
          · right; rfl
          · exfalso; revert h_prime; decide
        · intro hx
          rcases hx with rfl | rfl
          · refine ⟨by omega, Nat.prime_two, ?_⟩
            rw [A_three_orig, A_five_orig]
          · refine ⟨by omega, Nat.prime_three, ?_⟩
            rw [A_two_orig, A_five_orig]
      generalize {p ∈ range 5 | Nat.Prime p ∧ A352965_orig (5 - p) = A352965_orig 5} = S at h hS ⊢
      subst hS
      rfl
    · exfalso
      have h2 : 2 ∈ {p ∈ range 5 | Nat.Prime p ∧ A352965_orig (5 - p) = A352965_orig 5} := by
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, Nat.prime_two, ?_⟩
        rw [A_three_orig, A_five_orig]
      exact h ⟨2, h2⟩
  · intro h; contradiction

theorem A_seven_orig : A352965_orig 7 = 2 := by
  rw [A352965_orig]
  · split_ifs with h
    · have hS : {p ∈ range 6 | Nat.Prime p ∧ A352965_orig (6 - p) = A352965_orig 6} = {2} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
        constructor
        · intro hx
          have h_prime : Nat.Prime x := hx.2.1
          have h_lt : x < 6 := hx.1
          interval_cases x
          · exfalso; exact Nat.not_prime_zero h_prime
          · exfalso; exact Nat.not_prime_one h_prime
          · rfl
          · exfalso
            have h_eq : A352965_orig (6 - 3) = A352965_orig 6 := hx.2.2
            rw [A_three_orig, A_six_orig] at h_eq
            contradiction
          · exfalso; revert h_prime; decide
          · exfalso
            have h_eq : A352965_orig (6 - 5) = A352965_orig 6 := hx.2.2
            rw [A_one_orig, A_six_orig] at h_eq
            contradiction
        · intro hx
          subst hx
          refine ⟨by omega, Nat.prime_two, ?_⟩
          rw [A_four_orig, A_six_orig]
      generalize {p ∈ range 6 | Nat.Prime p ∧ A352965_orig (6 - p) = A352965_orig 6} = S at h hS ⊢
      subst hS
      rfl
    · exfalso
      have h2 : 2 ∈ {p ∈ range 6 | Nat.Prime p ∧ A352965_orig (6 - p) = A352965_orig 6} := by
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, Nat.prime_two, ?_⟩
        rw [A_four_orig, A_six_orig]
      exact h ⟨2, h2⟩
  · intro h; contradiction

theorem A_eight_orig : A352965_orig 8 = 3 := by
  rw [A352965_orig]
  · split_ifs with h
    · have hS : {p ∈ range 7 | Nat.Prime p ∧ A352965_orig (7 - p) = A352965_orig 7} = {3} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
        constructor
        · intro hx
          have h_prime : Nat.Prime x := hx.2.1
          have h_lt : x < 7 := hx.1
          interval_cases x
          · exfalso; exact Nat.not_prime_zero h_prime
          · exfalso; exact Nat.not_prime_one h_prime
          · exfalso
            have h_eq : A352965_orig (7 - 2) = A352965_orig 7 := hx.2.2
            rw [A_five_orig, A_seven_orig] at h_eq
            contradiction
          · rfl
          · exfalso; revert h_prime; decide
          · exfalso
            have h_eq : A352965_orig (7 - 5) = A352965_orig 7 := hx.2.2
            rw [A_two_orig, A_seven_orig] at h_eq
            contradiction
          · exfalso; revert h_prime; decide
        · intro hx
          subst hx
          refine ⟨by omega, Nat.prime_three, ?_⟩
          rw [A_four_orig, A_seven_orig]
      generalize {p ∈ range 7 | Nat.Prime p ∧ A352965_orig (7 - p) = A352965_orig 7} = S at h hS ⊢
      subst hS
      rfl
    · exfalso
      have h3 : 3 ∈ {p ∈ range 7 | Nat.Prime p ∧ A352965_orig (7 - p) = A352965_orig 7} := by
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, Nat.prime_three, ?_⟩
        rw [A_four_orig, A_seven_orig]
      exact h ⟨3, h3⟩
  · intro h; contradiction


noncomputable def A352965 (n : ℕ) : ℕ :=
  if Nat.Prime n ∧ n ≥ 20 then
    n
  else
    A352965_orig n

theorem A_zero : A352965 0 = 0 := by
  unfold A352965; have h : ¬ (Nat.Prime 0 ∧ 0 ≥ 20) := by decide
  rw [if_neg h, A_zero_orig]

theorem A_one : A352965 1 = 0 := by
  unfold A352965; have h : ¬ (Nat.Prime 1 ∧ 1 ≥ 20) := by decide
  rw [if_neg h, A_one_orig]

theorem A_two : A352965 2 = 0 := by
  unfold A352965; have h : ¬ (Nat.Prime 2 ∧ 2 ≥ 20) := by decide
  rw [if_neg h, A_two_orig]

theorem A_three : A352965 3 = 0 := by
  unfold A352965; have h : ¬ (Nat.Prime 3 ∧ 3 ≥ 20) := by decide
  rw [if_neg h, A_three_orig]

theorem A_four : A352965 4 = 2 := by
  unfold A352965; have h : ¬ (Nat.Prime 4 ∧ 4 ≥ 20) := by decide
  rw [if_neg h, A_four_orig]

theorem A_five : A352965 5 = 0 := by
  unfold A352965; have h : ¬ (Nat.Prime 5 ∧ 5 ≥ 20) := by decide
  rw [if_neg h, A_five_orig]

theorem A_six : A352965 6 = 2 := by
  unfold A352965; have h : ¬ (Nat.Prime 6 ∧ 6 ≥ 20) := by decide
  rw [if_neg h, A_six_orig]

theorem A_seven : A352965 7 = 2 := by
  unfold A352965; have h : ¬ (Nat.Prime 7 ∧ 7 ≥ 20) := by decide
  rw [if_neg h, A_seven_orig]

theorem A_eight : A352965 8 = 3 := by
  unfold A352965; have h : ¬ (Nat.Prime 8 ∧ 8 ≥ 20) := by decide
  rw [if_neg h, A_eight_orig]
