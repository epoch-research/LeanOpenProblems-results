import FormalConjectures.Util.ProblemImports

open Nat

/--
A007918: Least prime $\ge n$ (version 1 of the "next prime" function).
-/
noncomputable def a (n : ℕ) : ℕ :=
  @Nat.find (fun p => Nat.Prime p ∧ n ≤ p) (by infer_instance) (by
    rcases Nat.exists_infinite_primes n with ⟨p, h_le, h_prime⟩
    exact ⟨p, h_prime, h_le⟩
  )

/--
The initial term $p_0$ and common difference $d$ form an arithmetic progression of
length `n` consisting entirely of prime numbers.
We require $d > 0$ for it to be an increasing progression.
-/
def is_ap_of_n_primes (n p0 d : ℕ) : Prop :=
  d > 0 ∧ ∀ k < n, Nat.Prime (p0 + k * d)

lemma le_of_mem_S (n : ℕ) (hn : n > 0) (p0 : ℕ) (h : ∃ d, is_ap_of_n_primes n p0 d) : a n ≤ p0 := by
  rcases h with ⟨d, hd_gt, hd_prime⟩
  have hp0_prime : Nat.Prime p0 := by
    have h0 : 0 < n := hn
    have := hd_prime 0 h0
    simp at this
    exact this
  have hp0_ge_n : n ≤ p0 := by
    by_contra h_lt
    push_neg at h_lt
    have hk : p0 < n := h_lt
    have h_comp := hd_prime p0 hk
    have h_eq : p0 + p0 * d = p0 * (1 + d) := by ring
    rw [h_eq] at h_comp
    have hp0_ge_2 : p0 ≥ 2 := hp0_prime.two_le
    have hd_ge_2 : 1 + d ≥ 2 := by linarith
    have hp0_ne_1 : p0 ≠ 1 := by linarith
    have hd_ne_1 : 1 + d ≠ 1 := by linarith
    have h_not_prime := Nat.not_prime_mul hp0_ne_1 hd_ne_1
    exact h_not_prime h_comp
  have h_prop : Nat.Prime p0 ∧ n ≤ p0 := ⟨hp0_prime, hp0_ge_n⟩
  exact Nat.find_le h_prop

lemma a_four : a 4 = 5 := by
  have h_le : a 4 ≤ 5 := by
    have H : ∃ p, Nat.Prime p ∧ 4 ≤ p := by
      rcases Nat.exists_infinite_primes 4 with ⟨p, h_le, h_prime⟩
      exact ⟨p, h_prime, h_le⟩
    have h_p : Nat.Prime 5 ∧ 4 ≤ 5 := ⟨by decide, by decide⟩
    exact Nat.find_le h_p
  have h_ge : 5 ≤ a 4 := by
    have h_spec : Nat.Prime (a 4) ∧ 4 ≤ a 4 := by
      have H : ∃ p, Nat.Prime p ∧ 4 ≤ p := by
        rcases Nat.exists_infinite_primes 4 with ⟨p, h_le, h_prime⟩
        exact ⟨p, h_prime, h_le⟩
      exact Nat.find_spec H
    have h_prime := h_spec.1
    have h_ge4 := h_spec.2
    by_contra! h_lt
    have : a 4 = 4 := by omega
    rw [this] at h_prime
    have h_not : ¬ Nat.Prime 4 := by decide
    exact h_not h_prime
  exact le_antisymm h_le h_ge

theorem oeis_7918_conjecture_0 (n : ℕ) (hn : n > 0) :
    a n = sInf { p0 : ℕ | ∃ d : ℕ, is_ap_of_n_primes n p0 d } := by
  rcases le_or_gt n 4 with hn4 | hn4
  · interval_cases n
    · symm
      apply IsLeast.csInf_eq
      constructor
      · show ∃ d, is_ap_of_n_primes 1 (a 1) d
        use 1
        constructor
        · exact zero_lt_one
        · intro k hk
          simp at hk
          subst hk
          simp
          have H : ∃ p, Nat.Prime p ∧ 1 ≤ p := by
            rcases Nat.exists_infinite_primes 1 with ⟨p, h_le, h_prime⟩
            exact ⟨p, h_prime, h_le⟩
          exact Nat.find_spec H |>.1
      · intro p0 hp0
        exact le_of_mem_S 1 (by decide) p0 hp0
    · symm
      apply IsLeast.csInf_eq
      constructor
      · show ∃ d, is_ap_of_n_primes 2 (a 2) d
        use 1
        constructor
        · exact zero_lt_one
        · intro k hk
          interval_cases k
          · simp
            have H : ∃ p, Nat.Prime p ∧ 2 ≤ p := by
              rcases Nat.exists_infinite_primes 2 with ⟨p, h_le, h_prime⟩
              exact ⟨p, h_prime, h_le⟩
            exact Nat.find_spec H |>.1
          · simp
            have : a 2 = 2 := by
              have h_le : a 2 ≤ 2 := by
                have H : ∃ p, Nat.Prime p ∧ 2 ≤ p := by
                  rcases Nat.exists_infinite_primes 2 with ⟨p, h_le, h_prime⟩
                  exact ⟨p, h_prime, h_le⟩
                have h_p : Nat.Prime 2 ∧ 2 ≤ 2 := ⟨Nat.prime_two, le_rfl⟩
                exact Nat.find_le h_p
              have h_ge : 2 ≤ a 2 := by
                have H : ∃ p, Nat.Prime p ∧ 2 ≤ p := by
                  rcases Nat.exists_infinite_primes 2 with ⟨p, h_le, h_prime⟩
                  exact ⟨p, h_prime, h_le⟩
                exact Nat.find_spec H |>.2
              exact le_antisymm h_le h_ge
            rw [this]
            exact Nat.prime_three
      · intro p0 hp0
        exact le_of_mem_S 2 (by decide) p0 hp0
    · symm
      apply IsLeast.csInf_eq
      constructor
      · show ∃ d, is_ap_of_n_primes 3 (a 3) d
        use 2
        constructor
        · exact zero_lt_two
        · intro k hk
          interval_cases k
          · simp
            have H : ∃ p, Nat.Prime p ∧ 3 ≤ p := by
              rcases Nat.exists_infinite_primes 3 with ⟨p, h_le, h_prime⟩
              exact ⟨p, h_prime, h_le⟩
            exact Nat.find_spec H |>.1
          · simp
            have : a 3 = 3 := by
              have h_le : a 3 ≤ 3 := by
                have H : ∃ p, Nat.Prime p ∧ 3 ≤ p := by
                  rcases Nat.exists_infinite_primes 3 with ⟨p, h_le, h_prime⟩
                  exact ⟨p, h_prime, h_le⟩
                have h_p : Nat.Prime 3 ∧ 3 ≤ 3 := ⟨Nat.prime_three, le_rfl⟩
                exact Nat.find_le h_p
              have h_ge : 3 ≤ a 3 := by
                have H : ∃ p, Nat.Prime p ∧ 3 ≤ p := by
                  rcases Nat.exists_infinite_primes 3 with ⟨p, h_le, h_prime⟩
                  exact ⟨p, h_prime, h_le⟩
                exact Nat.find_spec H |>.2
              exact le_antisymm h_le h_ge
            rw [this]
            exact Nat.prime_five
          · simp
            have : a 3 = 3 := by
              have h_le : a 3 ≤ 3 := by
                have H : ∃ p, Nat.Prime p ∧ 3 ≤ p := by
                  rcases Nat.exists_infinite_primes 3 with ⟨p, h_le, h_prime⟩
                  exact ⟨p, h_prime, h_le⟩
                have h_p : Nat.Prime 3 ∧ 3 ≤ 3 := ⟨Nat.prime_three, le_rfl⟩
                exact Nat.find_le h_p
              have h_ge : 3 ≤ a 3 := by
                have H : ∃ p, Nat.Prime p ∧ 3 ≤ p := by
                  rcases Nat.exists_infinite_primes 3 with ⟨p, h_le, h_prime⟩
                  exact ⟨p, h_prime, h_le⟩
                exact Nat.find_spec H |>.2
              exact le_antisymm h_le h_ge
            rw [this]
            exact Nat.prime_seven
      · intro p0 hp0
        exact le_of_mem_S 3 (by decide) p0 hp0
    · symm
      apply IsLeast.csInf_eq
      constructor
      · show ∃ d, is_ap_of_n_primes 4 (a 4) d
        use 6
        constructor
        · exact (by decide : 6 > 0)
        · intro k hk
          interval_cases k
          · simp
            have H : ∃ p, Nat.Prime p ∧ 4 ≤ p := by
              rcases Nat.exists_infinite_primes 4 with ⟨p, h_le, h_prime⟩
              exact ⟨p, h_prime, h_le⟩
            exact Nat.find_spec H |>.1
          · simp [a_four]
            exact (by decide : Nat.Prime 11)
          · simp [a_four]
            exact (by decide : Nat.Prime 17)
          · simp [a_four]
            exact (by decide : Nat.Prime 23)
      · intro p0 hp0
        exact le_of_mem_S 4 (by decide) p0 hp0
  · symm
    apply IsLeast.csInf_eq
    constructor
    · show ∃ d, is_ap_of_n_primes n (a n) d
      sorry
    · intro p0 hp0
      exact le_of_mem_S n hn p0 hp0


#print axioms oeis_7918_conjecture_0
