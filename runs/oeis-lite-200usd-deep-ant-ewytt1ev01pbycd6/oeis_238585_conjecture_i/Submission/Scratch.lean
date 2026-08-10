import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators
open scoped Nat.Prime

set_option maxRecDepth 100000

noncomputable def a (n : ℕ) : ℕ :=
  Finset.Ico 1 n |>.sum fun k : ℕ =>
    let P_k := Nat.nth Nat.Prime (k - 1)
    let P_n := Nat.nth Nat.Prime (n - 1)
    if k.Prime ∧ (P_k ^ 2 + (P_n - 1) ^ 2).Prime then 1 else 0

-- nth prime values beyond what's in Mathlib (which has 0..4)
theorem nth5 : Nat.nth Nat.Prime 5 = 13 := nth_count (p := Nat.Prime) (n := 13) (by norm_num)
theorem nth6 : Nat.nth Nat.Prime 6 = 17 := nth_count (p := Nat.Prime) (n := 17) (by norm_num)
theorem nth7 : Nat.nth Nat.Prime 7 = 19 := nth_count (p := Nat.Prime) (n := 19) (by norm_num)
theorem nth8 : Nat.nth Nat.Prime 8 = 23 := nth_count (p := Nat.Prime) (n := 23) (by norm_num)
theorem nth9 : Nat.nth Nat.Prime 9 = 29 := nth_count (p := Nat.Prime) (n := 29) (by norm_num)

attribute [local simp] Nat.nth_prime_zero_eq_two Nat.nth_prime_one_eq_three
  Nat.nth_prime_two_eq_five Nat.nth_prime_three_eq_seven Nat.nth_prime_four_eq_eleven
  nth5 nth6 nth7 nth8 nth9

example : a 1 = 0 := by unfold a; simp
example : a 2 = 0 := by
  unfold a
  rw [show Finset.Ico 1 2 = ({1} : Finset ℕ) from by decide, Finset.sum_singleton]
  norm_num
example : a 3 = 0 := by
  unfold a
  rw [show Finset.Ico 1 3 = ({1,2} : Finset ℕ) from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num
example : a 4 = 1 := by
  unfold a
  rw [show Finset.Ico 1 4 = ({1,2,3} : Finset ℕ) from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num
example : a 5 = 1 := by
  unfold a
  rw [show Finset.Ico 1 5 = ({1,2,3,4} : Finset ℕ) from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  norm_num
example : a 6 = 0 := by
  unfold a
  rw [show Finset.Ico 1 6 = ({1,2,3,4,5} : Finset ℕ) from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num
example : a 7 = 1 := by
  unfold a
  rw [show Finset.Ico 1 7 = ({1,2,3,4,5,6} : Finset ℕ) from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num

-- lemma: the individual zero facts
theorem a1 : a 1 = 0 := by unfold a; simp
theorem a2 : a 2 = 0 := by
  unfold a
  rw [show Finset.Ico 1 2 = ({1} : Finset ℕ) from by decide, Finset.sum_singleton]; norm_num
theorem a3 : a 3 = 0 := by
  unfold a
  rw [show Finset.Ico 1 3 = ({1,2} : Finset ℕ) from by decide,
      Finset.sum_insert (by decide), Finset.sum_singleton]; norm_num
theorem a6 : a 6 = 0 := by
  unfold a
  rw [show Finset.Ico 1 6 = ({1,2,3,4,5} : Finset ℕ) from by decide,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]; norm_num

theorem nth10 : Nat.nth Nat.Prime 10 = 31 := nth_count (p := Nat.Prime) (n := 31) (by norm_num)
theorem nth11 : Nat.nth Nat.Prime 11 = 37 := nth_count (p := Nat.Prime) (n := 37) (by norm_num)
attribute [local simp] nth10 nth11

-- More listed values of part (ii) reverse direction, machine-checked:
example : a 10 = 1 := by
  unfold a
  rw [show Finset.Ico 1 10 = ({1,2,3,4,5,6,7,8,9} : Finset ℕ) from by decide]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]; norm_num
example : a 11 = 1 := by
  unfold a
  rw [show Finset.Ico 1 11 = ({1,2,3,4,5,6,7,8,9,10} : Finset ℕ) from by decide]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]; norm_num
example : a 12 = 1 := by
  unfold a
  rw [show Finset.Ico 1 12 = ({1,2,3,4,5,6,7,8,9,10,11} : Finset ℕ) from by decide]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]; norm_num

-- COMPLETE reverse direction of part (i): n ∣ 6 → a n = 0
theorem part_i_reverse (n : ℕ) (hn : n > 0) (h : n ∣ 6) : a n = 0 := by
  have hle : n ≤ 6 := Nat.le_of_dvd (by norm_num) h
  interval_cases n
  · exact a1
  · exact a2
  · exact a3
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact a6

-- Remaining nth prime values, up to index 43 (= 193)
theorem nth12 : Nat.nth Nat.Prime 12 = 41 := nth_count (p := Nat.Prime) (n := 41) (by norm_num)
theorem nth13 : Nat.nth Nat.Prime 13 = 43 := nth_count (p := Nat.Prime) (n := 43) (by norm_num)
theorem nth14 : Nat.nth Nat.Prime 14 = 47 := nth_count (p := Nat.Prime) (n := 47) (by norm_num)
theorem nth15 : Nat.nth Nat.Prime 15 = 53 := nth_count (p := Nat.Prime) (n := 53) (by norm_num)
theorem nth16 : Nat.nth Nat.Prime 16 = 59 := nth_count (p := Nat.Prime) (n := 59) (by norm_num)
theorem nth17 : Nat.nth Nat.Prime 17 = 61 := nth_count (p := Nat.Prime) (n := 61) (by norm_num)
theorem nth18 : Nat.nth Nat.Prime 18 = 67 := nth_count (p := Nat.Prime) (n := 67) (by norm_num)
theorem nth19 : Nat.nth Nat.Prime 19 = 71 := nth_count (p := Nat.Prime) (n := 71) (by norm_num)
theorem nth20 : Nat.nth Nat.Prime 20 = 73 := nth_count (p := Nat.Prime) (n := 73) (by norm_num)
theorem nth21 : Nat.nth Nat.Prime 21 = 79 := nth_count (p := Nat.Prime) (n := 79) (by norm_num)
theorem nth22 : Nat.nth Nat.Prime 22 = 83 := nth_count (p := Nat.Prime) (n := 83) (by norm_num)
theorem nth23 : Nat.nth Nat.Prime 23 = 89 := nth_count (p := Nat.Prime) (n := 89) (by norm_num)
theorem nth24 : Nat.nth Nat.Prime 24 = 97 := nth_count (p := Nat.Prime) (n := 97) (by norm_num)
theorem nth25 : Nat.nth Nat.Prime 25 = 101 := nth_count (p := Nat.Prime) (n := 101) (by norm_num)
theorem nth26 : Nat.nth Nat.Prime 26 = 103 := nth_count (p := Nat.Prime) (n := 103) (by norm_num)
theorem nth27 : Nat.nth Nat.Prime 27 = 107 := nth_count (p := Nat.Prime) (n := 107) (by norm_num)
theorem nth28 : Nat.nth Nat.Prime 28 = 109 := nth_count (p := Nat.Prime) (n := 109) (by norm_num)
theorem nth29 : Nat.nth Nat.Prime 29 = 113 := nth_count (p := Nat.Prime) (n := 113) (by norm_num)
theorem nth30 : Nat.nth Nat.Prime 30 = 127 := nth_count (p := Nat.Prime) (n := 127) (by norm_num)
theorem nth31 : Nat.nth Nat.Prime 31 = 131 := nth_count (p := Nat.Prime) (n := 131) (by norm_num)
theorem nth32 : Nat.nth Nat.Prime 32 = 137 := nth_count (p := Nat.Prime) (n := 137) (by norm_num)
theorem nth33 : Nat.nth Nat.Prime 33 = 139 := nth_count (p := Nat.Prime) (n := 139) (by norm_num)
theorem nth34 : Nat.nth Nat.Prime 34 = 149 := nth_count (p := Nat.Prime) (n := 149) (by norm_num)
theorem nth35 : Nat.nth Nat.Prime 35 = 151 := nth_count (p := Nat.Prime) (n := 151) (by norm_num)
theorem nth36 : Nat.nth Nat.Prime 36 = 157 := nth_count (p := Nat.Prime) (n := 157) (by norm_num)
theorem nth37 : Nat.nth Nat.Prime 37 = 163 := nth_count (p := Nat.Prime) (n := 163) (by norm_num)
theorem nth38 : Nat.nth Nat.Prime 38 = 167 := nth_count (p := Nat.Prime) (n := 167) (by norm_num)
theorem nth39 : Nat.nth Nat.Prime 39 = 173 := nth_count (p := Nat.Prime) (n := 173) (by norm_num)
theorem nth40 : Nat.nth Nat.Prime 40 = 179 := nth_count (p := Nat.Prime) (n := 179) (by norm_num)
theorem nth41 : Nat.nth Nat.Prime 41 = 181 := nth_count (p := Nat.Prime) (n := 181) (by norm_num)
theorem nth42 : Nat.nth Nat.Prime 42 = 191 := nth_count (p := Nat.Prime) (n := 191) (by norm_num)
theorem nth43 : Nat.nth Nat.Prime 43 = 193 := nth_count (p := Nat.Prime) (n := 193) (by norm_num)

attribute [local simp] nth12 nth13 nth14 nth15 nth16 nth17 nth18 nth19 nth20 nth21 nth22 nth23
  nth24 nth25 nth26 nth27 nth28 nth29 nth30 nth31 nth32 nth33 nth34 nth35 nth36 nth37 nth38 nth39
  nth40 nth41 nth42 nth43

theorem av19 : a 19 = 1 := by
  unfold a
  rw [show Finset.Ico 1 19 = ({1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18} : Finset ℕ) from by decide]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]; norm_num
theorem av21 : a 21 = 1 := by
  unfold a
  rw [show Finset.Ico 1 21 = ({1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20} : Finset ℕ) from by decide]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]; norm_num
theorem av22 : a 22 = 1 := by
  unfold a
  rw [show Finset.Ico 1 22 = ({1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21} : Finset ℕ) from by decide]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]; norm_num
theorem av31 : a 31 = 1 := by
  unfold a
  rw [show Finset.Ico 1 31 = ({1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30} : Finset ℕ) from by decide]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]; norm_num
theorem av42 : a 42 = 1 := by
  unfold a
  rw [show Finset.Ico 1 42 = ({1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41} : Finset ℕ) from by decide]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]; norm_num
theorem av44 : a 44 = 1 := by
  unfold a
  rw [show Finset.Ico 1 44 = ({1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43} : Finset ℕ) from by decide]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]; norm_num

-- named versions of the small listed values
theorem av4 : a 4 = 1 := by
  unfold a
  rw [show Finset.Ico 1 4 = ({1,2,3} : Finset ℕ) from by decide]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]; norm_num
theorem av5 : a 5 = 1 := by
  unfold a
  rw [show Finset.Ico 1 5 = ({1,2,3,4} : Finset ℕ) from by decide]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]; norm_num
theorem av7 : a 7 = 1 := by
  unfold a
  rw [show Finset.Ico 1 7 = ({1,2,3,4,5,6} : Finset ℕ) from by decide]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]; norm_num
theorem av10 : a 10 = 1 := by
  unfold a
  rw [show Finset.Ico 1 10 = ({1,2,3,4,5,6,7,8,9} : Finset ℕ) from by decide]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]; norm_num
theorem av11 : a 11 = 1 := by
  unfold a
  rw [show Finset.Ico 1 11 = ({1,2,3,4,5,6,7,8,9,10} : Finset ℕ) from by decide]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]; norm_num
theorem av12 : a 12 = 1 := by
  unfold a
  rw [show Finset.Ico 1 12 = ({1,2,3,4,5,6,7,8,9,10,11} : Finset ℕ) from by decide]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]; norm_num

-- COMPLETE reverse direction of part (ii)
theorem part_ii_reverse (n : ℕ)
    (h : n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 19 ∨ n = 21 ∨ n = 22 ∨
         n = 31 ∨ n = 42 ∨ n = 44) : a n = 1 := by
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h <;> subst h
  · exact av4
  · exact av5
  · exact av7
  · exact av10
  · exact av11
  · exact av12
  · exact av19
  · exact av21
  · exact av22
  · exact av31
  · exact av42
  · exact av44

/-- The full conjecture, with BOTH reverse directions fully proven and the two
    forward directions isolated as the only remaining goals.  Each `sorry` below is
    exactly an instance of Bunyakovsky's conjecture / Landau's 4th problem (primes of
    the form x²+m²), which is unsolved and blocked by the sieve-theoretic parity problem. -/
theorem conjecture_structure :
    (∀ n : ℕ, n > 0 → (a n > 0 ↔ ¬ (n ∣ 6))) ∧
    (∀ n : ℕ, n > 0 → (a n = 1 ↔ n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨
        n = 19 ∨ n = 21 ∨ n = 22 ∨ n = 31 ∨ n = 42 ∨ n = 44)) := by
  refine ⟨fun n hn => ⟨?_, ?_⟩, fun n hn => ⟨?_, ?_⟩⟩
  · -- PROVEN: a n > 0 → ¬(n ∣ 6)   (contrapositive of part_i_reverse)
    intro hpos hdvd
    have h0 : a n = 0 := part_i_reverse n hn hdvd
    omega
  · -- OPEN: ¬(n ∣ 6) → a n > 0   (Bunyakovsky/Landau, parity barrier)
    sorry
  · -- OPEN: a n = 1 → n ∈ list   (Bunyakovsky/Landau, parity barrier)
    sorry
  · -- PROVEN: n ∈ list → a n = 1   (part_ii_reverse)
    exact part_ii_reverse n
