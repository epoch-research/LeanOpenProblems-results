import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else (Nat.nth Nat.Prime n) - (Nat.nth Nat.Prime (n - 1))

noncomputable def gap_subsequence (start_index : ℕ) (length : ℕ) : List ℕ :=
  (List.range length).map (fun i => a (start_index + i))

example : Nat.nth Nat.Prime 5 = 13 := by
  rw [← show Nat.count Nat.Prime 13 = 5 by native_decide]
  exact Nat.nth_count (p := Nat.Prime) (n := 13) (by norm_num)

example : Nat.nth Nat.Prime 6 = 17 := by
  rw [← show Nat.count Nat.Prime 17 = 6 by native_decide]
  exact Nat.nth_count (p := Nat.Prime) (n := 17) (by norm_num)

example : Nat.nth Nat.Prime 7 = 19 := by
  rw [← show Nat.count Nat.Prime 19 = 7 by native_decide]
  exact Nat.nth_count (p := Nat.Prime) (n := 19) (by norm_num)

example : gap_subsequence 3 5 = [2,4,2,4,2] := by
  have h5 : Nat.nth Nat.Prime 5 = 13 := by
    rw [← show Nat.count Nat.Prime 13 = 5 by native_decide]
    exact Nat.nth_count (p := Nat.Prime) (n := 13) (by norm_num)
  have h6 : Nat.nth Nat.Prime 6 = 17 := by
    rw [← show Nat.count Nat.Prime 17 = 6 by native_decide]
    exact Nat.nth_count (p := Nat.Prime) (n := 17) (by norm_num)
  have h7 : Nat.nth Nat.Prime 7 = 19 := by
    rw [← show Nat.count Nat.Prime 19 = 7 by native_decide]
    exact Nat.nth_count (p := Nat.Prime) (n := 19) (by norm_num)
  change [a 3, a 4, a 5, a 6, a 7] = [2, 4, 2, 4, 2]
  norm_num [a, h5, h6, h7]


example (k : ℕ) (h : gap_subsequence k 5 = [2,4,2,4,2]) : a k = 2 := by
  have := congrArg (fun l : List ℕ => l.getD 0 0) h
  simpa [gap_subsequence] using this

example (k : ℕ) (h : gap_subsequence k 5 = [2,4,2,4,2]) : a (k+1) = 4 := by
  have := congrArg (fun l : List ℕ => l.getD 1 0) h
  simpa [gap_subsequence, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this



lemma gap3_test : gap_subsequence 3 5 = [2,4,2,4,2] := by
  have h5 : Nat.nth Nat.Prime 5 = 13 := by
    rw [← show Nat.count Nat.Prime 13 = 5 by native_decide]
    exact Nat.nth_count (p := Nat.Prime) (n := 13) (by norm_num)
  have h6 : Nat.nth Nat.Prime 6 = 17 := by
    rw [← show Nat.count Nat.Prime 17 = 6 by native_decide]
    exact Nat.nth_count (p := Nat.Prime) (n := 17) (by norm_num)
  have h7 : Nat.nth Nat.Prime 7 = 19 := by
    rw [← show Nat.count Nat.Prime 19 = 7 by native_decide]
    exact Nat.nth_count (p := Nat.Prime) (n := 19) (by norm_num)
  change [a 3, a 4, a 5, a 6, a 7] = [2, 4, 2, 4, 2]
  norm_num [a, h5, h6, h7]

lemma occurrence_eq_three_test {k : ℕ}
    (h : gap_subsequence k 5 = gap_subsequence 3 5) : k = 3 := by
  have hpat : gap_subsequence k 5 = [2,4,2,4,2] := by
    simpa [gap3_test] using h
  have h0 : a k = 2 := by
    have := congrArg (fun l : List ℕ => l.getD 0 0) hpat
    simpa [gap_subsequence] using this
  have h1 : a (k+1) = 4 := by
    have := congrArg (fun l : List ℕ => l.getD 1 0) hpat
    simpa [gap_subsequence, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
  have h2 : a (k+2) = 2 := by
    have := congrArg (fun l : List ℕ => l.getD 2 0) hpat
    simpa [gap_subsequence, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
  have h3 : a (k+3) = 4 := by
    have := congrArg (fun l : List ℕ => l.getD 3 0) hpat
    simpa [gap_subsequence, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
  have h4 : a (k+4) = 2 := by
    have := congrArg (fun l : List ℕ => l.getD 4 0) hpat
    simpa [gap_subsequence, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
  have hk_ne0 : k ≠ 0 := by
    rintro rfl
    norm_num [a] at h0
  let q := Nat.nth Nat.Prime (k - 1)
  have hle0 : q ≤ Nat.nth Nat.Prime k := by
    dsimp [q]
    exact (Nat.nth_le_nth Nat.infinite_setOf_prime).2 (Nat.pred_le k)
  have hn0 : Nat.nth Nat.Prime k = q + 2 := by
    have hs : Nat.nth Nat.Prime k - q = 2 := by
      simpa [a, hk_ne0, q] using h0
    exact (Nat.sub_eq_iff_eq_add' hle0).1 hs
  have hle1 : Nat.nth Nat.Prime k ≤ Nat.nth Nat.Prime (k+1) := by
    exact (Nat.nth_le_nth Nat.infinite_setOf_prime).2 (by omega)
  have hn1 : Nat.nth Nat.Prime (k+1) = q + 6 := by
    have hs : Nat.nth Nat.Prime (k+1) - Nat.nth Nat.Prime k = 4 := by
      simpa [a] using h1
    have heq := (Nat.sub_eq_iff_eq_add' hle1).1 hs
    rw [hn0] at heq
    omega
  have hle2 : Nat.nth Nat.Prime (k+1) ≤ Nat.nth Nat.Prime (k+2) := by
    exact (Nat.nth_le_nth Nat.infinite_setOf_prime).2 (by omega)
  have hn2 : Nat.nth Nat.Prime (k+2) = q + 8 := by
    have hs : Nat.nth Nat.Prime (k+2) - Nat.nth Nat.Prime (k+1) = 2 := by
      simpa [a] using h2
    have heq := (Nat.sub_eq_iff_eq_add' hle2).1 hs
    rw [hn1] at heq
    omega
  have hle3 : Nat.nth Nat.Prime (k+2) ≤ Nat.nth Nat.Prime (k+3) := by
    exact (Nat.nth_le_nth Nat.infinite_setOf_prime).2 (by omega)
  have hn3 : Nat.nth Nat.Prime (k+3) = q + 12 := by
    have hs : Nat.nth Nat.Prime (k+3) - Nat.nth Nat.Prime (k+2) = 4 := by
      simpa [a] using h3
    have heq := (Nat.sub_eq_iff_eq_add' hle3).1 hs
    rw [hn2] at heq
    omega
  have hle4 : Nat.nth Nat.Prime (k+3) ≤ Nat.nth Nat.Prime (k+4) := by
    exact (Nat.nth_le_nth Nat.infinite_setOf_prime).2 (by omega)
  have hn4 : Nat.nth Nat.Prime (k+4) = q + 14 := by
    have hs : Nat.nth Nat.Prime (k+4) - Nat.nth Nat.Prime (k+3) = 2 := by
      simpa [a] using h4
    have heq := (Nat.sub_eq_iff_eq_add' hle4).1 hs
    rw [hn3] at heq
    omega
  have hp0 : Nat.Prime q := by
    dsimp [q]
    exact Nat.prime_nth_prime (k-1)
  have hp2 : Nat.Prime (q+2) := by simpa [hn0] using Nat.prime_nth_prime k
  have hp6 : Nat.Prime (q+6) := by simpa [hn1] using Nat.prime_nth_prime (k+1)
  have hp8 : Nat.Prime (q+8) := by simpa [hn2] using Nat.prime_nth_prime (k+2)
  have hp12 : Nat.Prime (q+12) := by simpa [hn3] using Nat.prime_nth_prime (k+3)
  have hp14 : Nat.Prime (q+14) := by simpa [hn4] using Nat.prime_nth_prime (k+4)
  have hdiv : 5 ∣ q ∨ 5 ∣ q + 2 ∨ 5 ∣ q + 6 ∨ 5 ∣ q + 8 ∨ 5 ∣ q + 12 ∨ 5 ∣ q + 14 := by
    omega
  have hq5 : q = 5 := by
    rcases hdiv with hd | hd | hd | hd | hd | hd
    · exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hp0).1 hd).symm
    · have heq : q + 2 = 5 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hp2).1 hd).symm
      have hq3 : q = 3 := by omega
      have : Nat.Prime 9 := by simpa [hq3] using hp6
      norm_num at this
    · have heq : 5 = q + 6 := (Nat.prime_dvd_prime_iff_eq Nat.prime_five hp6).1 hd
      omega
    · have heq : 5 = q + 8 := (Nat.prime_dvd_prime_iff_eq Nat.prime_five hp8).1 hd
      omega
    · have heq : 5 = q + 12 := (Nat.prime_dvd_prime_iff_eq Nat.prime_five hp12).1 hd
      omega
    · have heq : 5 = q + 14 := (Nat.prime_dvd_prime_iff_eq Nat.prime_five hp14).1 hd
      omega
  have hpred : k - 1 = 2 := by
    apply Nat.nth_injective Nat.infinite_setOf_prime
    dsimp [q] at hq5
    simpa [hq5]
  omega


example (s : Set ℕ) (h : s ⊆ ({3} : Set ℕ)) : ¬ s.Infinite := by
  intro hs
  exact (Set.finite_singleton 3).not_infinite (hs.mono h)

example (s : Set ℕ) (h : s ⊆ ({3} : Set ℕ)) : ¬ s.Infinite := by
  exact fun hs => (Set.finite_singleton 3).not_infinite (hs.mono h)

#check Set.Finite.not_infinite

#check Nat.eq_add_of_sub_eq
#check Nat.sub_eq_iff_eq_add
#check Nat.sub_eq_iff_eq_add'
#check Nat.sub_add_cancel
#check Nat.add_sub_cancel'


example (q : ℕ) : 5 ∣ q ∨ 5 ∣ q + 2 ∨ 5 ∣ q + 6 ∨ 5 ∣ q + 8 ∨ 5 ∣ q + 12 ∨ 5 ∣ q + 14 := by
  omega



#check Set.Infinite.mono
#check Nat.prime_nth_prime
#check Nat.nth_strictMono
#check Nat.infinite_setOf_prime
#check Nat.nth_lt_nth
#check Nat.nth_le_nth
