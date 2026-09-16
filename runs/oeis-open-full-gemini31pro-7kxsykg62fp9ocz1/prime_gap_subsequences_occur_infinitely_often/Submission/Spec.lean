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
theorem prime_gap_subsequences_occur_infinitely_often :
  ∀ (n : ℕ) (m : ℕ),
    n ≥ 3 →
    Set.Infinite {k : ℕ | gap_subsequence k (m + 1) = gap_subsequence n (m + 1)} :=
by sorry

lemma p_nth (n k : ℕ) (h1 : count Nat.Prime k = n := by rfl) (h2 : Nat.Prime k := by decide) :
  nth Nat.Prime n = k := by
  rw [← h1]
  exact nth_count h2

lemma p_2 : nth Nat.Prime 2 = 5 := p_nth 2 5
lemma p_3 : nth Nat.Prime 3 = 7 := p_nth 3 7
lemma p_4 : nth Nat.Prime 4 = 11 := p_nth 4 11
lemma p_5 : nth Nat.Prime 5 = 13 := p_nth 5 13
lemma p_6 : nth Nat.Prime 6 = 17 := p_nth 6 17
lemma p_7 : nth Nat.Prime 7 = 19 := p_nth 7 19

lemma a_3 : a 3 = 2 := by unfold a; rw [if_neg (by decide), p_3, p_2]
lemma a_4 : a 4 = 4 := by unfold a; rw [if_neg (by decide), p_4, p_3]
lemma a_5 : a 5 = 2 := by unfold a; rw [if_neg (by decide), p_5, p_4]
lemma a_6 : a 6 = 4 := by unfold a; rw [if_neg (by decide), p_6, p_5]
lemma a_7 : a 7 = 2 := by unfold a; rw [if_neg (by decide), p_7, p_6]

lemma gap_3_5 : gap_subsequence 3 5 = [2, 4, 2, 4, 2] := by
  unfold gap_subsequence
  change [a 3, a 4, a 5, a 6, a 7] = _
  rw [a_3, a_4, a_5, a_6, a_7]

lemma nth_prime_of_a {n d : ℕ} (h : a n = d) (hn : n > 0) :
  nth Nat.Prime n = nth Nat.Prime (n - 1) + d := by
  unfold a at h
  rw [if_neg (_root_.ne_of_gt hn)] at h
  have H : nth Nat.Prime (n - 1) ≤ nth Nat.Prime n := by
    apply nth_monotone Nat.infinite_setOf_prime
    exact tsub_le_self
  omega

lemma primes_of_gap (k : ℕ) (hk : k > 0) (h : gap_subsequence k 5 = [2, 4, 2, 4, 2]) :
  let P := nth Nat.Prime (k - 1)
  nth Nat.Prime k = P + 2 ∧
  nth Nat.Prime (k + 1) = P + 6 ∧
  nth Nat.Prime (k + 2) = P + 8 ∧
  nth Nat.Prime (k + 3) = P + 12 ∧
  nth Nat.Prime (k + 4) = P + 14 := by
  unfold gap_subsequence at h
  change [a (k+0), a (k+1), a (k+2), a (k+3), a (k+4)] = [2, 4, 2, 4, 2] at h
  simp only [add_zero, List.cons.injEq, and_true] at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  have eq0 : nth Nat.Prime k = nth Nat.Prime (k - 1) + 2 := nth_prime_of_a h0 hk
  have eq1 : nth Nat.Prime (k + 1) = nth Nat.Prime k + 4 := nth_prime_of_a h1 (by omega)
  have eq2 : nth Nat.Prime (k + 2) = nth Nat.Prime (k + 1) + 2 := nth_prime_of_a h2 (by omega)
  have eq3 : nth Nat.Prime (k + 3) = nth Nat.Prime (k + 2) + 4 := nth_prime_of_a h3 (by omega)
  have eq4 : nth Nat.Prime (k + 4) = nth Nat.Prime (k + 3) + 2 := nth_prime_of_a h4 (by omega)
  have e1 : nth Nat.Prime (k + 1) = nth Nat.Prime (k - 1) + 6 := by omega
  have e2 : nth Nat.Prime (k + 2) = nth Nat.Prime (k - 1) + 8 := by omega
  have e3 : nth Nat.Prime (k + 3) = nth Nat.Prime (k - 1) + 12 := by omega
  have e4 : nth Nat.Prime (k + 4) = nth Nat.Prime (k - 1) + 14 := by omega
  exact ⟨eq0, e1, e2, e3, e4⟩

lemma prime_mod_5 (P : ℕ) (hP : Nat.Prime P) (h1 : Nat.Prime (P+2)) (h2 : Nat.Prime (P+6)) (h3 : Nat.Prime (P+8)) (h4 : Nat.Prime (P+14)) : P = 5 := by
  have hP2 : P ≥ 2 := hP.two_le
  have mod_cases : P % 5 = 0 ∨ P % 5 = 1 ∨ P % 5 = 2 ∨ P % 5 = 3 ∨ P % 5 = 4 := by omega
  rcases mod_cases with h0 | h1_mod | h2_mod | h3_mod | h4_mod
  · have h_dvd : 5 ∣ P := dvd_of_mod_eq_zero h0
    rcases (Nat.dvd_prime hP).mp h_dvd with h51 | h5P
    · contradiction
    · exact h5P.symm
  · have : (P + 14) % 5 = 0 := by omega
    have h_dvd : 5 ∣ P + 14 := dvd_of_mod_eq_zero this
    rcases (Nat.dvd_prime h4).mp h_dvd with h51 | h5P
    · contradiction
    · omega
  · have : (P + 8) % 5 = 0 := by omega
    have h_dvd : 5 ∣ P + 8 := dvd_of_mod_eq_zero this
    rcases (Nat.dvd_prime h3).mp h_dvd with h51 | h5P
    · contradiction
    · omega
  · have : (P + 2) % 5 = 0 := by omega
    have h_dvd : 5 ∣ P + 2 := dvd_of_mod_eq_zero this
    rcases (Nat.dvd_prime h1).mp h_dvd with h51 | h5P
    · contradiction
    · have : P = 3 := by omega
      subst this
      have : Nat.Prime 9 := h2
      contradiction
  · have : (P + 6) % 5 = 0 := by omega
    have h_dvd : 5 ∣ P + 6 := dvd_of_mod_eq_zero this
    rcases (Nat.dvd_prime h2).mp h_dvd with h51 | h5P
    · contradiction
    · omega

lemma k_eq_3 {k : ℕ} (hk : nth Nat.Prime (k - 1) = 5) : k = 3 := by
  have H : nth Nat.Prime (k - 1) = nth Nat.Prime 2 := by rw [hk, p_2]
  have H2 : k - 1 = 2 := StrictMono.injective (nth_strictMono Nat.infinite_setOf_prime) H
  omega

lemma k_ne_0 (h : gap_subsequence 0 5 = [2, 4, 2, 4, 2]) : False := by
  unfold gap_subsequence at h
  change [a 0, a 1, a 2, a 3, a 4] = [2, 4, 2, 4, 2] at h
  simp only [List.cons.injEq] at h
  have h0 : a 0 = 2 := h.1
  unfold a at h0
  rw [if_pos rfl] at h0
  contradiction

lemma k_of_gap_eq (k : ℕ) (h : gap_subsequence k 5 = gap_subsequence 3 5) : k = 3 := by
  rw [gap_3_5] at h
  by_cases hk : k = 0
  · subst hk
    exfalso
    exact k_ne_0 h
  · have hk_pos : k > 0 := by omega
    have h_primes := primes_of_gap k hk_pos h
    rcases h_primes with ⟨e1, e2, e3, e4, e5⟩
    have P_eq : nth Nat.Prime (k - 1) = 5 := by
      apply prime_mod_5
      · exact nth_mem_of_infinite Nat.infinite_setOf_prime _
      · rw [← e1]
        exact nth_mem_of_infinite Nat.infinite_setOf_prime _
      · rw [← e2]
        exact nth_mem_of_infinite Nat.infinite_setOf_prime _
      · rw [← e3]
        exact nth_mem_of_infinite Nat.infinite_setOf_prime _
      · rw [← e5]
        exact nth_mem_of_infinite Nat.infinite_setOf_prime _
    exact k_eq_3 P_eq

theorem prime_gap_subsequences_occur_infinitely_often.disproof : ¬ (type_of% @prime_gap_subsequences_occur_infinitely_often) := by
  intro H
  have H34 := H 3 4 (by omega)
  have subset : {k : ℕ | gap_subsequence k (4 + 1) = gap_subsequence 3 (4 + 1)} ⊆ {3} := by
    intro k hk
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hk ⊢
    exact k_of_gap_eq k hk
  have fin : {k : ℕ | gap_subsequence k (4 + 1) = gap_subsequence 3 (4 + 1)}.Finite :=
    Set.Finite.subset (Set.finite_singleton 3) subset
  exact Set.Infinite.not_finite H34 fin
