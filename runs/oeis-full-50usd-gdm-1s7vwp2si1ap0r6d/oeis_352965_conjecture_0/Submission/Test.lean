import FormalConjectures.Util.ProblemImports

open Nat Finset

def A352965 : ℕ → ℕ
| 0 => 0 -- Padding for 1-indexing implementation
| 1 => 0 -- A(1) = 0 by start condition.
| n + 1 => -- Calculates A(n+1). Let k = n.
  let k := n -- k is the index of the previous term A(k). k >= 1.

  -- The value of the previous term A(k)
  let a_k := A352965 k

  -- We seek the least prime p such that A(k) = A(k-p), where k-p >= 1, so p <= k - 1.
  -- Primes p must be in {2, 3, ..., k-1}. Finset.range k covers 0 to k-1.
  let all_lt_k := Finset.range k

  -- Filter for valid primes p that satisfy the condition.
  let S := all_lt_k.filter (fun p =>
    Nat.Prime p ∧ A352965 (k - p) = a_k)

  if h : S.Nonempty then
    S.min' h
  else
    0

theorem A_zero : A352965 0 = 0 := by rw [A352965]
theorem A_one : A352965 1 = 0 := by rw [A352965]

theorem A_two : A352965 2 = 0 := by
  rw [A352965]
  · split_ifs with h
    · exfalso
      obtain ⟨p, hp⟩ := h
      simp only [Finset.mem_filter, Finset.mem_range] at hp
      have hp0 : p = 0 := by omega
      subst hp0
      exact Nat.not_prime_zero hp.2.1
    · rfl
  · intro h; contradiction

theorem A_three : A352965 3 = 0 := by
  rw [A352965]
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

theorem A_four : A352965 4 = 2 := by rfl

theorem A_five : A352965 5 = 0 := by
  rw [A352965]
  · split_ifs with h
    · exfalso
      obtain ⟨p, hp⟩ := h
      simp only [Finset.mem_filter, Finset.mem_range] at hp
      have hp4 : p < 4 := hp.1
      have hp_prime : Nat.Prime p := hp.2.1
      interval_cases p
      · exact Nat.not_prime_zero hp_prime
      · exact Nat.not_prime_one hp_prime
      · have h_eq : A352965 (4 - 2) = A352965 4 := hp.2.2
        rw [A_two, A_four] at h_eq
        contradiction
      · have h_eq : A352965 (4 - 3) = A352965 4 := hp.2.2
        rw [A_one, A_four] at h_eq
        contradiction
    · rfl
  · intro h; contradiction

theorem A_six : A352965 6 = 2 := by
  rw [A352965]
  · split_ifs with h
    · have hS : {p ∈ range 5 | Nat.Prime p ∧ A352965 (5 - p) = A352965 5} = {2, 3} := by
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
            rw [A_three, A_five]
          · refine ⟨by omega, Nat.prime_three, ?_⟩
            rw [A_two, A_five]
      generalize {p ∈ range 5 | Nat.Prime p ∧ A352965 (5 - p) = A352965 5} = S at h hS ⊢
      subst hS
      rfl
    · exfalso
      have h2 : 2 ∈ {p ∈ range 5 | Nat.Prime p ∧ A352965 (5 - p) = A352965 5} := by
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, Nat.prime_two, ?_⟩
        rw [A_three, A_five]
      exact h ⟨2, h2⟩
  · intro h; contradiction


theorem A_seven : A352965 7 = 2 := by
  rw [A352965]
  · split_ifs with h
    · have hS : {p ∈ range 6 | Nat.Prime p ∧ A352965 (6 - p) = A352965 6} = {2} := by
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
            have h_eq : A352965 (6 - 3) = A352965 6 := hx.2.2
            rw [A_three, A_six] at h_eq
            contradiction
          · exfalso; revert h_prime; decide
          · exfalso
            have h_eq : A352965 (6 - 5) = A352965 6 := hx.2.2
            rw [A_one, A_six] at h_eq
            contradiction
        · intro hx
          subst hx
          refine ⟨by omega, Nat.prime_two, ?_⟩
          rw [A_four, A_six]
      generalize {p ∈ range 6 | Nat.Prime p ∧ A352965 (6 - p) = A352965 6} = S at h hS ⊢
      subst hS
      rfl
    · exfalso
      have h2 : 2 ∈ {p ∈ range 6 | Nat.Prime p ∧ A352965 (6 - p) = A352965 6} := by
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, Nat.prime_two, ?_⟩
        rw [A_four, A_six]
      exact h ⟨2, h2⟩
  · intro h; contradiction

theorem A_eight : A352965 8 = 3 := by
  rw [A352965]
  · split_ifs with h
    · have hS : {p ∈ range 7 | Nat.Prime p ∧ A352965 (7 - p) = A352965 7} = {3} := by
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
            have h_eq : A352965 (7 - 2) = A352965 7 := hx.2.2
            rw [A_five, A_seven] at h_eq
            contradiction
          · rfl
          · exfalso; revert h_prime; decide
          · exfalso
            have h_eq : A352965 (7 - 5) = A352965 7 := hx.2.2
            rw [A_two, A_seven] at h_eq
            contradiction
          · exfalso; revert h_prime; decide
        · intro hx
          subst hx
          refine ⟨by omega, Nat.prime_three, ?_⟩
          rw [A_four, A_seven]
      generalize {p ∈ range 7 | Nat.Prime p ∧ A352965 (7 - p) = A352965 7} = S at h hS ⊢
      subst hS
      rfl
    · exfalso
      have h3 : 3 ∈ {p ∈ range 7 | Nat.Prime p ∧ A352965 (7 - p) = A352965 7} := by
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, Nat.prime_three, ?_⟩
        rw [A_four, A_seven]
      exact h ⟨3, h3⟩
  · intro h; contradiction



theorem A_nine : A352965 9 = 0 := by
  rw [A352965]
  · split_ifs with h
    · exfalso
      obtain ⟨p, hp⟩ := h
      simp only [Finset.mem_filter, Finset.mem_range] at hp
      have hp8 : p < 8 := hp.1
      have hp_prime : Nat.Prime p := hp.2.1
      interval_cases p
      · exact Nat.not_prime_zero hp_prime
      · exact Nat.not_prime_one hp_prime
      · have h_eq : A352965 (8 - 2) = A352965 8 := hp.2.2
        rw [A_six, A_eight] at h_eq
        contradiction
      · have h_eq : A352965 (8 - 3) = A352965 8 := hp.2.2
        rw [A_five, A_eight] at h_eq
        contradiction
      · exfalso; revert hp_prime; decide
      · have h_eq : A352965 (8 - 5) = A352965 8 := hp.2.2
        rw [A_three, A_eight] at h_eq
        contradiction
      · exfalso; revert hp_prime; decide
      · have h_eq : A352965 (8 - 7) = A352965 8 := hp.2.2
        rw [A_one, A_eight] at h_eq
        contradiction
    · rfl
  · intro h; contradiction


theorem A_ten : A352965 10 = 7 := by
  rw [A352965]
  · split_ifs with h
    · have hS : {p ∈ range 9 | Nat.Prime p ∧ A352965 (9 - p) = A352965 9} = {7} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
        constructor
        · intro hx
          have h_prime : Nat.Prime x := hx.2.1
          have h_lt : x < 9 := hx.1
          interval_cases x
          · exfalso; exact Nat.not_prime_zero h_prime
          · exfalso; exact Nat.not_prime_one h_prime
          · exfalso
            have h_eq : A352965 (9 - 2) = A352965 9 := hx.2.2
            rw [A_seven, A_nine] at h_eq
            contradiction
          · exfalso
            have h_eq : A352965 (9 - 3) = A352965 9 := hx.2.2
            rw [A_six, A_nine] at h_eq
            contradiction
          · exfalso; revert h_prime; decide
          · exfalso
            have h_eq : A352965 (9 - 5) = A352965 9 := hx.2.2
            rw [A_four, A_nine] at h_eq
            contradiction
          · exfalso; revert h_prime; decide
          · rfl
        · intro hx
          subst hx
          refine ⟨by omega, by decide, ?_⟩
          rw [A_two, A_nine]
      generalize {p ∈ range 9 | Nat.Prime p ∧ A352965 (9 - p) = A352965 9} = S at h hS ⊢
      subst hS
      rfl
    · exfalso
      have h7 : 7 ∈ {p ∈ range 9 | Nat.Prime p ∧ A352965 (9 - p) = A352965 9} := by
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, by decide, ?_⟩
        rw [A_two, A_nine]
      exact h ⟨7, h7⟩
  · intro h; contradiction


theorem A_eleven : A352965 11 = 0 := by
  rw [A352965]
  · split_ifs with h
    · exfalso
      obtain ⟨p, hp⟩ := h
      simp only [Finset.mem_filter, Finset.mem_range] at hp
      have hp10 : p < 10 := hp.1
      have hp_prime : Nat.Prime p := hp.2.1
      interval_cases p
      · exact Nat.not_prime_zero hp_prime
      · exact Nat.not_prime_one hp_prime
      · have h_eq : A352965 (10 - 2) = A352965 10 := hp.2.2
        rw [A_eight, A_ten] at h_eq
        contradiction
      · have h_eq : A352965 (10 - 3) = A352965 10 := hp.2.2
        rw [A_seven, A_ten] at h_eq
        contradiction
      · exfalso; revert hp_prime; decide
      · have h_eq : A352965 (10 - 5) = A352965 10 := hp.2.2
        rw [A_five, A_ten] at h_eq
        contradiction
      · exfalso; revert hp_prime; decide
      · have h_eq : A352965 (10 - 7) = A352965 10 := hp.2.2
        rw [A_three, A_ten] at h_eq
        contradiction
      · exfalso; revert hp_prime; decide
      · exfalso; revert hp_prime; decide
    · rfl
  · intro h; contradiction


theorem A_twelve : A352965 12 = 2 := by
  rw [A352965]
  · split_ifs with h
    · have hS : {p ∈ range 11 | Nat.Prime p ∧ A352965 (11 - p) = A352965 11} = {2} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
        constructor
        · intro hx
          have h_prime : Nat.Prime x := hx.2.1
          have h_lt : x < 11 := hx.1
          interval_cases x
          · exfalso; exact Nat.not_prime_zero h_prime
          · exfalso; exact Nat.not_prime_one h_prime
          · rfl
          · exfalso
            have h_eq : A352965 (11 - 3) = A352965 11 := hx.2.2
            rw [A_eight, A_eleven] at h_eq
            contradiction
          · exfalso; revert h_prime; decide
          · exfalso
            have h_eq : A352965 (11 - 5) = A352965 11 := hx.2.2
            rw [A_six, A_eleven] at h_eq
            contradiction
          · exfalso; revert h_prime; decide
          · exfalso
            have h_eq : A352965 (11 - 7) = A352965 11 := hx.2.2
            rw [A_four, A_eleven] at h_eq
            contradiction
          · exfalso; revert h_prime; decide
          · exfalso; revert h_prime; decide
          · exfalso; revert h_prime; decide
        · intro hx
          subst hx
          refine ⟨by omega, Nat.prime_two, ?_⟩
          rw [A_nine, A_eleven]
      generalize {p ∈ range 11 | Nat.Prime p ∧ A352965 (11 - p) = A352965 11} = S at h hS ⊢
      subst hS
      rfl
    · exfalso
      have h2 : 2 ∈ {p ∈ range 11 | Nat.Prime p ∧ A352965 (11 - p) = A352965 11} := by
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, Nat.prime_two, ?_⟩
        rw [A_nine, A_eleven]
      exact h ⟨2, h2⟩
  · intro h; contradiction


theorem A_thirteen : A352965 13 = 5 := by
  rw [A352965]
  · split_ifs with h
    · have hS : {p ∈ range 12 | Nat.Prime p ∧ A352965 (12 - p) = A352965 12} = {5} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
        constructor
        · intro hx
          have h_prime : Nat.Prime x := hx.2.1
          have h_lt : x < 12 := hx.1
          interval_cases x
          · exfalso; exact Nat.not_prime_zero h_prime
          · exfalso; exact Nat.not_prime_one h_prime
          · exfalso
            have h_eq : A352965 (12 - 2) = A352965 12 := hx.2.2
            rw [A_ten, A_twelve] at h_eq
            contradiction
          · exfalso
            have h_eq : A352965 (12 - 3) = A352965 12 := hx.2.2
            rw [A_nine, A_twelve] at h_eq
            contradiction
          · exfalso; revert h_prime; decide
          · rfl
          · exfalso; revert h_prime; decide
          · exfalso
            have h_eq : A352965 (12 - 7) = A352965 12 := hx.2.2
            rw [A_five, A_twelve] at h_eq
            contradiction
          · exfalso; revert h_prime; decide
          · exfalso; revert h_prime; decide
          · exfalso; revert h_prime; decide
          · exfalso
            have h_eq : A352965 (12 - 11) = A352965 12 := hx.2.2
            rw [A_one, A_twelve] at h_eq
            contradiction
        · intro hx
          subst hx
          refine ⟨by omega, by decide, ?_⟩
          rw [A_seven, A_twelve]
      generalize {p ∈ range 12 | Nat.Prime p ∧ A352965 (12 - p) = A352965 12} = S at h hS ⊢
      subst hS
      rfl
    · exfalso
      have h5 : 5 ∈ {p ∈ range 12 | Nat.Prime p ∧ A352965 (12 - p) = A352965 12} := by
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, by decide, ?_⟩
        rw [A_seven, A_twelve]
      exact h ⟨5, h5⟩
  · intro h; contradiction


theorem A_fourteen : A352965 14 = 0 := by
  rw [A352965]
  · split_ifs with h
    · exfalso
      obtain ⟨p, hp⟩ := h
      simp only [Finset.mem_filter, Finset.mem_range] at hp
      have hp_lt : p < 13 := hp.1
      have hp_prime : Nat.Prime p := hp.2.1
      interval_cases p
      · exact Nat.not_prime_zero hp_prime
      · exact Nat.not_prime_one hp_prime
      · have h_eq : A352965 (13 - 2) = A352965 13 := hp.2.2
        rw [A_eleven, A_thirteen] at h_eq
        contradiction
      · have h_eq : A352965 (13 - 3) = A352965 13 := hp.2.2
        rw [A_ten, A_thirteen] at h_eq
        contradiction
      · exfalso; revert hp_prime; decide
      · have h_eq : A352965 (13 - 5) = A352965 13 := hp.2.2
        rw [A_eight, A_thirteen] at h_eq
        contradiction
      · exfalso; revert hp_prime; decide
      · have h_eq : A352965 (13 - 7) = A352965 13 := hp.2.2
        rw [A_six, A_thirteen] at h_eq
        contradiction
      · exfalso; revert hp_prime; decide
      · exfalso; revert hp_prime; decide
      · exfalso; revert hp_prime; decide
      · have h_eq : A352965 (13 - 11) = A352965 13 := hp.2.2
        rw [A_two, A_thirteen] at h_eq
        contradiction
      · exfalso; revert hp_prime; decide
    · rfl
  · intro h; contradiction

theorem A_fifteen : A352965 15 = 3 := by
  rw [A352965]
  · split_ifs with h
    · have hS : {p ∈ range 14 | Nat.Prime p ∧ A352965 (14 - p) = A352965 14} = {3, 5, 11, 13} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hx
          have h_prime : Nat.Prime x := hx.2.1
          have h_lt : x < 14 := hx.1
          interval_cases x
          · exfalso; exact Nat.not_prime_zero h_prime
          · exfalso; exact Nat.not_prime_one h_prime
          · exfalso
            have h_eq : A352965 (14 - 2) = A352965 14 := hx.2.2
            rw [A_twelve, A_fourteen] at h_eq
            contradiction
          · left; rfl
          · exfalso; revert h_prime; decide
          · right; left; rfl
          · exfalso; revert h_prime; decide
          · exfalso
            have h_eq : A352965 (14 - 7) = A352965 14 := hx.2.2
            rw [A_seven, A_fourteen] at h_eq
            contradiction
          · exfalso; revert h_prime; decide
          · exfalso; revert h_prime; decide
          · exfalso; revert h_prime; decide
          · right; right; left; rfl
          · exfalso; revert h_prime; decide
          · right; right; right; rfl
        · intro hx
          rcases hx with rfl | rfl | rfl | rfl
          · refine ⟨by omega, by decide, ?_⟩
            rw [A_eleven, A_fourteen]
          · refine ⟨by omega, by decide, ?_⟩
            rw [A_nine, A_fourteen]
          · refine ⟨by omega, by decide, ?_⟩
            rw [A_three, A_fourteen]
          · refine ⟨by omega, by decide, ?_⟩
            rw [A_one, A_fourteen]
      generalize {p ∈ range 14 | Nat.Prime p ∧ A352965 (14 - p) = A352965 14} = S at h hS ⊢
      subst hS
      rfl
    · exfalso
      have h3 : 3 ∈ {p ∈ range 14 | Nat.Prime p ∧ A352965 (14 - p) = A352965 14} := by
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, by decide, ?_⟩
        rw [A_eleven, A_fourteen]
      exact h ⟨3, h3⟩
  · intro h; contradiction

theorem A_sixteen : A352965 16 = 7 := by
  rw [A352965]
  · split_ifs with h
    · have hS : {p ∈ range 15 | Nat.Prime p ∧ A352965 (15 - p) = A352965 15} = {7} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hx
          have h_prime : Nat.Prime x := hx.2.1
          have h_lt : x < 15 := hx.1
          interval_cases x
          · exfalso; exact Nat.not_prime_zero h_prime
          · exfalso; exact Nat.not_prime_one h_prime
          · exfalso
            have h_eq : A352965 (15 - 2) = A352965 15 := hx.2.2
            rw [A_thirteen, A_fifteen] at h_eq
            contradiction
          · exfalso
            have h_eq : A352965 (15 - 3) = A352965 15 := hx.2.2
            rw [A_twelve, A_fifteen] at h_eq
            contradiction
          · exfalso; revert h_prime; decide
          · exfalso
            have h_eq : A352965 (15 - 5) = A352965 15 := hx.2.2
            rw [A_ten, A_fifteen] at h_eq
            contradiction
          · exfalso; revert h_prime; decide
          · rfl
          · exfalso; revert h_prime; decide
          · exfalso; revert h_prime; decide
          · exfalso; revert h_prime; decide
          · exfalso
            have h_eq : A352965 (15 - 11) = A352965 15 := hx.2.2
            rw [A_four, A_fifteen] at h_eq
            contradiction
          · exfalso; revert h_prime; decide
          · exfalso
            have h_eq : A352965 (15 - 13) = A352965 15 := hx.2.2
            rw [A_two, A_fifteen] at h_eq
            contradiction
          · exfalso; revert h_prime; decide
        · intro hx
          subst hx
          refine ⟨by omega, by decide, ?_⟩
          rw [A_eight, A_fifteen]
      generalize {p ∈ range 15 | Nat.Prime p ∧ A352965 (15 - p) = A352965 15} = S at h hS ⊢
      subst hS
      rfl
    · exfalso
      have h7 : 7 ∈ {p ∈ range 15 | Nat.Prime p ∧ A352965 (15 - p) = A352965 15} := by
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, by decide, ?_⟩
        rw [A_eight, A_fifteen]
      exact h ⟨7, h7⟩
  · intro h; contradiction

theorem A_seventeen : A352965 17 = 0 := by
  rw [A352965]
  · split_ifs with h
    · exfalso
      obtain ⟨p, hp⟩ := h
      simp only [Finset.mem_filter, Finset.mem_range] at hp
      have hp_lt : p < 16 := hp.1
      have hp_prime : Nat.Prime p := hp.2.1
      interval_cases p
      · exact Nat.not_prime_zero hp_prime
      · exact Nat.not_prime_one hp_prime
      · have h_eq : A352965 (16 - 2) = A352965 16 := hp.2.2
        rw [A_fourteen, A_sixteen] at h_eq
        contradiction
      · have h_eq : A352965 (16 - 3) = A352965 16 := hp.2.2
        rw [A_thirteen, A_sixteen] at h_eq
        contradiction
      · exfalso; revert hp_prime; decide
      · have h_eq : A352965 (16 - 5) = A352965 16 := hp.2.2
        rw [A_eleven, A_sixteen] at h_eq
        contradiction
      · exfalso; revert hp_prime; decide
      · have h_eq : A352965 (16 - 7) = A352965 16 := hp.2.2
        rw [A_nine, A_sixteen] at h_eq
        contradiction
      · exfalso; revert hp_prime; decide
      · exfalso; revert hp_prime; decide
      · exfalso; revert hp_prime; decide
      · have h_eq : A352965 (16 - 11) = A352965 16 := hp.2.2
        rw [A_five, A_sixteen] at h_eq
        contradiction
      · exfalso; revert hp_prime; decide
      · have h_eq : A352965 (16 - 13) = A352965 16 := hp.2.2
        rw [A_three, A_sixteen] at h_eq
        contradiction
      · exfalso; revert hp_prime; decide
      · exfalso; revert hp_prime; decide
    · rfl
  · intro h; contradiction

theorem A_eighteen : A352965 18 = 3 := by
  rw [A352965]
  · split_ifs with h
    · have hS : {p ∈ range 17 | Nat.Prime p ∧ A352965 (17 - p) = A352965 17} = {3} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hx
          have h_prime : Nat.Prime x := hx.2.1
          have h_lt : x < 17 := hx.1
          interval_cases x
          · exfalso; exact Nat.not_prime_zero h_prime
          · exfalso; exact Nat.not_prime_one h_prime
          · exfalso
            have h_eq : A352965 (17 - 2) = A352965 17 := hx.2.2
            rw [A_fifteen, A_seventeen] at h_eq
            contradiction
          · rfl
          · exfalso; revert h_prime; decide
          · exfalso
            have h_eq : A352965 (17 - 5) = A352965 17 := hx.2.2
            rw [A_twelve, A_seventeen] at h_eq
            contradiction
          · exfalso; revert h_prime; decide
          · exfalso
            have h_eq : A352965 (17 - 7) = A352965 17 := hx.2.2
            rw [A_ten, A_seventeen] at h_eq
            contradiction
          · exfalso; revert h_prime; decide
          · exfalso; revert h_prime; decide
          · exfalso; revert h_prime; decide
          · exfalso
            have h_eq : A352965 (17 - 11) = A352965 17 := hx.2.2
            rw [A_six, A_seventeen] at h_eq
            contradiction
          · exfalso; revert h_prime; decide
          · exfalso
            have h_eq : A352965 (17 - 13) = A352965 17 := hx.2.2
            rw [A_four, A_seventeen] at h_eq
            contradiction
          · exfalso; revert h_prime; decide
          · exfalso; revert h_prime; decide
          · exfalso; revert h_prime; decide
        · intro hx
          subst hx
          refine ⟨by omega, by decide, ?_⟩
          rw [A_fourteen, A_seventeen]
      generalize {p ∈ range 17 | Nat.Prime p ∧ A352965 (17 - p) = A352965 17} = S at h hS ⊢
      subst hS
      rfl
    · exfalso
      have h3 : 3 ∈ {p ∈ range 17 | Nat.Prime p ∧ A352965 (17 - p) = A352965 17} := by
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, by decide, ?_⟩
        rw [A_fourteen, A_seventeen]
      exact h ⟨3, h3⟩
  · intro h; contradiction

theorem A_nineteen : A352965 19 = 3 := by
  rw [A352965]
  · split_ifs with h
    · have hS : {p ∈ range 18 | Nat.Prime p ∧ A352965 (18 - p) = A352965 18} = {3} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hx
          have h_prime : Nat.Prime x := hx.2.1
          have h_lt : x < 18 := hx.1
          interval_cases x
          · exfalso; exact Nat.not_prime_zero h_prime
          · exfalso; exact Nat.not_prime_one h_prime
          · exfalso
            have h_eq : A352965 (18 - 2) = A352965 18 := hx.2.2
            rw [A_sixteen, A_eighteen] at h_eq
            contradiction
          · rfl
          · exfalso; revert h_prime; decide
          · exfalso
            have h_eq : A352965 (18 - 5) = A352965 18 := hx.2.2
            rw [A_thirteen, A_eighteen] at h_eq
            contradiction
          · exfalso; revert h_prime; decide
          · exfalso
            have h_eq : A352965 (18 - 7) = A352965 18 := hx.2.2
            rw [A_eleven, A_eighteen] at h_eq
            contradiction
          · exfalso; revert h_prime; decide
          · exfalso; revert h_prime; decide
          · exfalso; revert h_prime; decide
          · exfalso
            have h_eq : A352965 (18 - 11) = A352965 18 := hx.2.2
            rw [A_seven, A_eighteen] at h_eq
            contradiction
          · exfalso; revert h_prime; decide
          · exfalso
            have h_eq : A352965 (18 - 13) = A352965 18 := hx.2.2
            rw [A_five, A_eighteen] at h_eq
            contradiction
          · exfalso; revert h_prime; decide
          · exfalso; revert h_prime; decide
          · exfalso; revert h_prime; decide
          · exfalso
            have h_eq : A352965 (18 - 17) = A352965 18 := hx.2.2
            rw [A_one, A_eighteen] at h_eq
            contradiction
        · intro hx
          subst hx
          refine ⟨by omega, by decide, ?_⟩
          rw [A_fifteen, A_eighteen]
      generalize {p ∈ range 18 | Nat.Prime p ∧ A352965 (18 - p) = A352965 18} = S at h hS ⊢
      subst hS
      rfl
    · exfalso
      have h3 : 3 ∈ {p ∈ range 18 | Nat.Prime p ∧ A352965 (18 - p) = A352965 18} := by
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, by decide, ?_⟩
        rw [A_fifteen, A_eighteen]
      exact h ⟨3, h3⟩
  · intro h; contradiction

theorem A_twenty : A352965 20 = 11 := by rfl

theorem A_thirty_two : A352965 32 = 13 := by rfl


lemma not_appears_imp (p : ℕ) (hp : Nat.Prime p) (h_not : ∀ n, A352965 n ≠ p) :
    ∀ n, p < n → A352965 n = A352965 (n - p) → ∃ q < p, Nat.Prime q ∧ A352965 n = A352965 (n - q) := by
  intro n hp_lt heq
  rw [A352965] at h_not
  -- We want to analyze A352965 (n+1) but wait, we have h_not (n+1).
  have h_not_succ := h_not (n + 1)
  -- A352965 (n+1) is defined by split_ifs
  -- Let S be the Finset
  let S := (Finset.range n).filter (fun r => Nat.Prime r ∧ A352965 (n - r) = A352965 n)
  have hS_nonempty : S.Nonempty := by
    use p
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨hp_lt, hp, heq.symm⟩
  have h_eq_min : A352965 (n + 1) = S.min' hS_nonempty := by
    rw [A352965]
    simp only [S]
    split_ifs with h_ne
    · rfl
    · exfalso; exact h_ne hS_nonempty
  rw [h_eq_min] at h_not_succ
  let q := S.min' hS_nonempty
  have hq_mem : q ∈ S := Finset.min'_mem S hS_nonempty
  have hp_mem : p ∈ S := by
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨hp_lt, hp, heq.symm⟩
  have hq_le : q ≤ p := Finset.min'_le S p hp_mem
  have hq_ne : q ≠ p := by
    intro h_eq
    subst h_eq
    exact h_not_succ rfl
  have hq_lt : q < p := lt_of_le_of_ne hq_le hq_ne
  simp only [Finset.mem_filter, Finset.mem_range] at hq_mem
  use q
  refine ⟨hq_lt, hq_mem.2.1, hq_mem.2.2.symm⟩

theorem oeis_352965_conjecture_0 : ∀ (p : ℕ), Nat.Prime p → ∃ (n : ℕ), A352965 n = p := by
  intro p hp
  rcases p with _ | _ | _ | _ | p'
  · exfalso; exact Nat.not_prime_zero hp
  · exfalso; exact Nat.not_prime_one hp
  · use 4; exact A_four
  · use 8; exact A_eight
  · sorry


#print axioms oeis_352965_conjecture_0













