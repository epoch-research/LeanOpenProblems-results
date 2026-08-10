import FormalConjectures.Util.ProblemImports

open Nat

/--
A001223: Prime gaps: differences between consecutive primes.
The $n$-th term of the sequence, $a(n)$, is the difference between the $(n+1)$-th prime and the $n$-th prime (using 1-based indexing for primes $p_k$).
$$a(n) = p_{n+1} - p_n$$
This corresponds to the difference between the $n$-th and $(n-1)$-th prime in Mathlib's 0-indexed sequence of primes.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else (Nat.nth Nat.Prime n) - (Nat.nth Nat.Prime (n - 1))

-- Helper definition for extracting a finite subsequence (pattern) as a list
noncomputable def gap_subsequence (start_index : ℕ) (length : ℕ) : List ℕ :=
  (List.range length).map (fun i => a (start_index + i))

/--
oeis_1223_conjecture_4: Since (6a, 6b) is an admissible pattern of gaps for any integers a, b > 0
(and also if other multiples of 6 are inserted in between), the above conjecture follows from the
prime k-tuple conjecture which states that any admissible pattern occurs infinitely often (see, e.g.,
the Caldwell link). This also means that any subsequence a(n .. n+m) with n > 2 (as to exclude the
untypical primes 2 and 3) should occur infinitely many times at other starting points n'.
-/



@[simp]
theorem nth_prime_five_eq_thirteen : Nat.nth Nat.Prime 5 = 13 := by
  have h_count : Nat.count Nat.Prime 13 = 5 := by decide
  have h_prime : Nat.Prime 13 := by decide
  have h_nth := Nat.nth_count h_prime
  rwa [h_count] at h_nth

@[simp]
theorem nth_prime_six_eq_seventeen : Nat.nth Nat.Prime 6 = 17 := by
  have h_count : Nat.count Nat.Prime 17 = 6 := by decide
  have h_prime : Nat.Prime 17 := by decide
  have h_nth := Nat.nth_count h_prime
  rwa [h_count] at h_nth

@[simp]
theorem nth_prime_seven_eq_nineteen : Nat.nth Nat.Prime 7 = 19 := by
  have h_count : Nat.count Nat.Prime 19 = 7 := by decide
  have h_prime : Nat.Prime 19 := by decide
  have h_nth := Nat.nth_count h_prime
  rwa [h_count] at h_nth

theorem a_three : a 3 = 2 := by
  unfold a; simp

theorem a_four : a 4 = 4 := by
  unfold a; simp

theorem a_five : a 5 = 2 := by
  unfold a; simp

theorem a_six : a 6 = 4 := by
  unfold a; simp

theorem a_seven : a 7 = 2 := by
  unfold a; simp


theorem gap_subsequence_three_five : gap_subsequence 3 5 = [2, 4, 2, 4, 2] := by
  unfold gap_subsequence
  change [a 3, a 4, a 5, a 6, a 7] = [2, 4, 2, 4, 2]
  rw [a_three, a_four, a_five, a_six, a_seven]


lemma p_idx_succ (i : ℕ) : Nat.nth Nat.Prime (i + 1) = Nat.nth Nat.Prime i + a (i + 1) := by
  unfold a
  simp
  have h_lt : Nat.nth Nat.Prime i < Nat.nth Nat.Prime (i + 1) := by
    rw [Nat.nth_lt_nth Nat.infinite_setOf_prime]
    omega
  omega


lemma prime_mod_five (x : ℕ) (hp : Nat.Prime x) (hx : x % 5 = 0) : x = 5 := by
  have hd : 5 ∣ x := Nat.dvd_of_mod_eq_zero hx
  rcases hp.eq_one_or_self_of_dvd 5 hd with h1 | h2
  · contradiction
  · exact h2.symm

lemma k_eq_3_of_gap_subsequence (k : ℕ) (h : gap_subsequence k 5 = [2, 4, 2, 4, 2]) : k = 3 := by
  have h_unfold : gap_subsequence k 5 = [a k, a (k+1), a (k+2), a (k+3), a (k+4)] := by
    unfold gap_subsequence
    rfl
  rw [h_unfold] at h
  have hk0 : a k = 2 := by injection h
  have hk1 : a (k+1) = 4 := by
    injection h with _ h1
    injection h1
  have hk2 : a (k+2) = 2 := by
    injection h with _ h1
    injection h1 with _ h2
    injection h2
  have hk3 : a (k+3) = 4 := by
    injection h with _ h1
    injection h1 with _ h2
    injection h2 with _ h3
    injection h3
  have hk4 : a (k+4) = 2 := by
    injection h with _ h1
    injection h1 with _ h2
    injection h2 with _ h3
    injection h3 with _ h4
    injection h4

  have hk_nz : k ≠ 0 := by
    intro h_k0
    subst h_k0
    have ha0 : a 0 = 0 := by unfold a; rfl
    rw [ha0] at hk0
    contradiction
  have h_le : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk_nz
  have h_k_eq : k = (k - 1) + 1 := (Nat.sub_add_cancel h_le).symm

  set q0 := Nat.nth Nat.Prime (k - 1)
  have hp0 : Nat.Prime q0 := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (k - 1)

  have hp1_eq : Nat.nth Nat.Prime k = q0 + 2 := by
    nth_rw 1 [h_k_eq]
    rw [p_idx_succ (k-1)]
    rw [← h_k_eq]
    rw [hk0]
  have hp1 : Nat.Prime (q0 + 2) := by
    have h_mem := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime k
    rwa [hp1_eq] at h_mem

  have hp2_eq : Nat.nth Nat.Prime (k+1) = q0 + 6 := by
    rw [p_idx_succ k]
    rw [hp1_eq, hk1]
  have hp2 : Nat.Prime (q0 + 6) := by
    have h_mem := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (k+1)
    rwa [hp2_eq] at h_mem

  have hp3_eq : Nat.nth Nat.Prime (k+2) = q0 + 8 := by
    rw [p_idx_succ (k+1)]
    rw [hp2_eq, hk2]
  have hp3 : Nat.Prime (q0 + 8) := by
    have h_mem := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (k+2)
    rwa [hp3_eq] at h_mem

  have hp4_eq : Nat.nth Nat.Prime (k+3) = q0 + 12 := by
    rw [p_idx_succ (k+2)]
    rw [hp3_eq, hk3]
  have hp4 : Nat.Prime (q0 + 12) := by
    have h_mem := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (k+3)
    rwa [hp4_eq] at h_mem

  have hp5_eq : Nat.nth Nat.Prime (k+4) = q0 + 14 := by
    rw [p_idx_succ (k+3)]
    rw [hp4_eq, hk4]
  have hp5 : Nat.Prime (q0 + 14) := by
    have h_mem := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (k+4)
    rwa [hp5_eq] at h_mem

  have h_mod5 : q0 % 5 = 0 ∨ q0 % 5 = 1 ∨ q0 % 5 = 2 ∨ q0 % 5 = 3 ∨ q0 % 5 = 4 := by omega
  have h_q0 : q0 = 5 := by
    rcases h_mod5 with h0 | h1 | h2 | h3 | h4
    · exact prime_mod_five q0 hp0 h0
    · have h_mod : (q0 + 14) % 5 = 0 := by omega
      have h_eq5 : q0 + 14 = 5 := prime_mod_five (q0 + 14) hp5 h_mod
      omega
    · have h_mod : (q0 + 8) % 5 = 0 := by omega
      have h_eq5 : q0 + 8 = 5 := prime_mod_five (q0 + 8) hp3 h_mod
      omega
    · have h_mod : (q0 + 2) % 5 = 0 := by omega
      have h_eq5 : q0 + 2 = 5 := prime_mod_five (q0 + 2) hp1 h_mod
      have h_q0_val : q0 = 3 := by omega
      have hp2_9 : Nat.Prime 9 := by
        rw [h_q0_val] at hp2
        exact hp2
      have h_not_9 : ¬ Nat.Prime 9 := by decide
      contradiction
    · have h_mod : (q0 + 6) % 5 = 0 := by omega
      have h_eq5 : q0 + 6 = 5 := prime_mod_five (q0 + 6) hp2 h_mod
      omega

  have hk_sub : k - 1 = 2 := by
    have h_inj := Nat.nth_injective Nat.infinite_setOf_prime
    apply h_inj
    change q0 = Nat.nth Nat.Prime 2
    rw [h_q0]
    exact Nat.nth_prime_two_eq_five.symm
  omega


theorem prime_gap_subsequences_occur_infinitely_often.disproof :
  ¬ (∀ (n : ℕ) (m : ℕ),
    n ≥ 3 →
    Set.Infinite {k : ℕ | gap_subsequence k (m + 1) = gap_subsequence n (m + 1)}) := by
  intro h
  have h_inf := h 3 4 (by omega)
  rw [gap_subsequence_three_five] at h_inf
  have h_subset : {k : ℕ | gap_subsequence k 5 = [2, 4, 2, 4, 2]} ⊆ {3} := by
    intro k hk
    simp only [Set.mem_setOf_eq] at hk
    have hk3 := k_eq_3_of_gap_subsequence k hk
    simp [hk3]
  have h_inf_3 : Set.Infinite ({3} : Set ℕ) := Set.Infinite.mono h_subset h_inf
  have h_fin_3 : Set.Finite ({3} : Set ℕ) := Set.finite_singleton 3
  exact h_inf_3 h_fin_3







