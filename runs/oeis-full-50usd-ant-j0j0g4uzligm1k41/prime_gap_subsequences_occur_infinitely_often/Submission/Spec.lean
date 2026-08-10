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

/-
oeis_1223_conjecture_4: Since (6a, 6b) is an admissible pattern of gaps for any integers a, b > 0
(and also if other multiples of 6 are inserted in between), the above conjecture follows from the
prime k-tuple conjecture which states that any admissible pattern occurs infinitely often (see, e.g.,
the Caldwell link). This also means that any subsequence a(n .. n+m) with n > 2 (as to exclude the
untypical primes 2 and 3) should occur infinitely many times at other starting points n'.

This conjecture is FALSE as stated: it is too strong.  The pattern of gaps occurring at `n = 3`
(and length `m + 1 = 5`) is `[2, 4, 2, 4, 2]`, corresponding to the six consecutive primes
`5, 7, 11, 13, 17, 19`.  Reading these as offsets `0, 2, 6, 8, 12, 14` from the first prime, they
cover *all* residue classes modulo `5`.  Hence in *any* occurrence of this gap pattern, one of the
six primes is divisible by `5`, forcing it to equal `5`.  Therefore the first prime of the run is
at most `5`, and the pattern can only occur for finitely many starting indices `k` (in fact only
`k = 3`).  In particular the set of occurrences is finite, not infinite.

The conjecture's appeal to the prime `k`-tuple conjecture is flawed precisely because patterns
straddling the small primes (here, the prime `5`) can be *inadmissible*, so they need not — and do
not — recur infinitely often.
-/

/-- Helper: for `k ≥ 1`, the `k`-th gap equals the difference of consecutive `nth` primes. -/
private lemma a_succ (i : ℕ) :
    a (i + 1) = Nat.nth Nat.Prime (i + 1) - Nat.nth Nat.Prime i := by
  simp [a]

/-- The gap pattern starting at index `3` of length `5` is `[2, 4, 2, 4, 2]`. -/
private lemma gap_subsequence_three_five : gap_subsequence 3 5 = [2, 4, 2, 4, 2] := by
  have p5 : Nat.nth Nat.Prime 5 = 13 := by
    have h : Nat.count Nat.Prime 13 = 5 := by decide
    simpa [h] using Nat.nth_count (p := Nat.Prime) (show Nat.Prime 13 by norm_num)
  have p6 : Nat.nth Nat.Prime 6 = 17 := by
    have h : Nat.count Nat.Prime 17 = 6 := by decide
    simpa [h] using Nat.nth_count (p := Nat.Prime) (show Nat.Prime 17 by norm_num)
  have p7 : Nat.nth Nat.Prime 7 = 19 := by
    have h : Nat.count Nat.Prime 19 = 7 := by decide
    simpa [h] using Nat.nth_count (p := Nat.Prime) (show Nat.Prime 19 by norm_num)
  simp only [gap_subsequence, List.range_succ, List.map_cons, List.map_nil,
    List.range_zero, List.cons_append, List.nil_append, a]
  norm_num [p5, p6, p7]

/-- Any starting index `k` realising the pattern `[2, 4, 2, 4, 2]` satisfies `k ≤ 3`. -/
private lemma pattern_bound (k : ℕ) (hk : gap_subsequence k 5 = [2, 4, 2, 4, 2]) : k ≤ 3 := by
  have hmono : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono Nat.infinite_setOf_prime
  have hprime : ∀ n, Nat.Prime (Nat.nth Nat.Prime n) := Nat.prime_nth_prime
  rcases k with _ | j
  · omega
  · simp only [gap_subsequence, List.range_succ, List.map_cons, List.map_nil,
      List.range_zero, List.cons_append, List.nil_append, List.cons.injEq] at hk
    obtain ⟨d0, d1, d2, d3, d4, _⟩ := hk
    -- restate canonically (definitionally `j + 1 + i = j + (i + 1)`)
    have d0' : a (j + 1) = 2 := d0
    have d1' : a (j + 2) = 4 := d1
    have d2' : a (j + 3) = 2 := d2
    have d3' : a (j + 4) = 4 := d3
    have d4' : a (j + 5) = 2 := d4
    have g0 := a_succ j
    have g1 : a (j + 2) = Nat.nth Nat.Prime (j + 2) - Nat.nth Nat.Prime (j + 1) := a_succ (j + 1)
    have g2 : a (j + 3) = Nat.nth Nat.Prime (j + 3) - Nat.nth Nat.Prime (j + 2) := a_succ (j + 2)
    have g3 : a (j + 4) = Nat.nth Nat.Prime (j + 4) - Nat.nth Nat.Prime (j + 3) := a_succ (j + 3)
    have g4 : a (j + 5) = Nat.nth Nat.Prime (j + 5) - Nat.nth Nat.Prime (j + 4) := a_succ (j + 4)
    rw [g0] at d0'; rw [g1] at d1'; rw [g2] at d2'; rw [g3] at d3'; rw [g4] at d4'
    have m0 := hmono (show j < j + 1 by omega)
    have m1 := hmono (show j + 1 < j + 2 by omega)
    have m2 := hmono (show j + 2 < j + 3 by omega)
    have m3 := hmono (show j + 3 < j + 4 by omega)
    have m4 := hmono (show j + 4 < j + 5 by omega)
    set q := Nat.nth Nat.Prime j with hq
    have e1 : Nat.nth Nat.Prime (j + 1) = q + 2 := by omega
    have e2 : Nat.nth Nat.Prime (j + 2) = q + 6 := by omega
    have e3 : Nat.nth Nat.Prime (j + 3) = q + 8 := by omega
    have e4 : Nat.nth Nat.Prime (j + 4) = q + 12 := by omega
    have e5 : Nat.nth Nat.Prime (j + 5) = q + 14 := by omega
    have pr0 : Nat.Prime q := hprime j
    have pr1 : Nat.Prime (q + 2) := e1 ▸ hprime (j + 1)
    have pr2 : Nat.Prime (q + 6) := e2 ▸ hprime (j + 2)
    have pr3 : Nat.Prime (q + 8) := e3 ▸ hprime (j + 3)
    have pr5 : Nat.Prime (q + 14) := e5 ▸ hprime (j + 5)
    -- the six offsets `0,2,6,8,12,14` cover every residue mod 5, so one prime is `5`
    have hq5 : q ≤ 5 := by
      have hcase : q % 5 = 0 ∨ q % 5 = 1 ∨ q % 5 = 2 ∨ q % 5 = 3 ∨ q % 5 = 4 := by omega
      rcases hcase with h | h | h | h | h
      · have hd : (5 : ℕ) ∣ q := by omega
        rcases pr0.eq_one_or_self_of_dvd 5 hd with h5 | h5 <;> omega
      · have hd : (5 : ℕ) ∣ (q + 14) := by omega
        rcases pr5.eq_one_or_self_of_dvd 5 hd with h5 | h5 <;> omega
      · have hd : (5 : ℕ) ∣ (q + 8) := by omega
        rcases pr3.eq_one_or_self_of_dvd 5 hd with h5 | h5 <;> omega
      · have hd : (5 : ℕ) ∣ (q + 2) := by omega
        rcases pr1.eq_one_or_self_of_dvd 5 hd with h5 | h5 <;> omega
      · have hd : (5 : ℕ) ∣ (q + 6) := by omega
        rcases pr2.eq_one_or_self_of_dvd 5 hd with h5 | h5 <;> omega
    -- `q = nth Prime j ≤ 5 < 7 = nth Prime 3`, so `j ≤ 2` and `k = j + 1 ≤ 3`
    have hj : j ≤ 2 := by
      by_contra hcon
      push_neg at hcon
      have hh := hmono.monotone (show (3 : ℕ) ≤ j by omega)
      rw [Nat.nth_prime_three_eq_seven] at hh
      omega
    omega

theorem prime_gap_subsequences_occur_infinitely_often.disproof :
    ¬ ∀ (n : ℕ) (m : ℕ),
      n ≥ 3 →
      Set.Infinite {k : ℕ | gap_subsequence k (m + 1) = gap_subsequence n (m + 1)} := by
  intro h
  -- specialise to `n = 3`, `m = 4` (pattern length `5`)
  have hinf := h 3 4 (by norm_num)
  apply hinf
  -- the occurrence set is contained in `{k | k ≤ 3}`, hence finite
  apply Set.Finite.subset (Set.finite_Iic 3)
  intro k hk
  simp only [Set.mem_setOf_eq] at hk
  have hk5 : gap_subsequence k 5 = gap_subsequence 3 5 := hk
  rw [gap_subsequence_three_five] at hk5
  exact pattern_bound k hk5
