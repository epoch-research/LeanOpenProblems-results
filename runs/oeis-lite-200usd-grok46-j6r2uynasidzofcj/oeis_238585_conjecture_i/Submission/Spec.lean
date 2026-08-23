import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

open scoped Nat.Prime

set_option maxRecDepth 20000
set_option maxHeartbeats 80000000

/--
A238585: Number of primes $p < n$ with $\text{prime}(p)^2 + (\text{prime}(n)-1)^2$ prime.
(where $\text{prime}(i)$ is the $i$-th prime number, 1-indexed).
-/
noncomputable def a (n : ℕ) : ℕ :=
  Finset.Ico 1 n |>.sum fun k : ℕ =>
    -- P_k is the k-th prime (1-indexed), using Nat.nth Nat.Prime (k - 1).
    let P_k := Nat.nth Nat.Prime (k - 1)
    let P_n := Nat.nth Nat.Prime (n - 1)

    -- Count if the index k is prime AND the expression is prime.
    if k.Prime ∧ (P_k ^ 2 + (P_n - 1) ^ 2).Prime then 1 else 0

lemma nth_of_count {p n : ℕ} (hp : Nat.Prime p) (hc : Nat.count Nat.Prime p = n) :
    Nat.nth Nat.Prime n = p := by
  simpa [hc] using Nat.nth_count hp

lemma nthP0 : Nat.nth Nat.Prime 0 = 2 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP1 : Nat.nth Nat.Prime 1 = 3 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP2 : Nat.nth Nat.Prime 2 = 5 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP3 : Nat.nth Nat.Prime 3 = 7 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP4 : Nat.nth Nat.Prime 4 = 11 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP5 : Nat.nth Nat.Prime 5 = 13 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP6 : Nat.nth Nat.Prime 6 = 17 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP7 : Nat.nth Nat.Prime 7 = 19 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP8 : Nat.nth Nat.Prime 8 = 23 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP9 : Nat.nth Nat.Prime 9 = 29 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP10 : Nat.nth Nat.Prime 10 = 31 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP11 : Nat.nth Nat.Prime 11 = 37 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP12 : Nat.nth Nat.Prime 12 = 41 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP13 : Nat.nth Nat.Prime 13 = 43 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP14 : Nat.nth Nat.Prime 14 = 47 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP15 : Nat.nth Nat.Prime 15 = 53 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP16 : Nat.nth Nat.Prime 16 = 59 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP17 : Nat.nth Nat.Prime 17 = 61 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP18 : Nat.nth Nat.Prime 18 = 67 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP19 : Nat.nth Nat.Prime 19 = 71 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP20 : Nat.nth Nat.Prime 20 = 73 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP21 : Nat.nth Nat.Prime 21 = 79 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP22 : Nat.nth Nat.Prime 22 = 83 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP23 : Nat.nth Nat.Prime 23 = 89 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP24 : Nat.nth Nat.Prime 24 = 97 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP25 : Nat.nth Nat.Prime 25 = 101 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP26 : Nat.nth Nat.Prime 26 = 103 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP27 : Nat.nth Nat.Prime 27 = 107 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP28 : Nat.nth Nat.Prime 28 = 109 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP29 : Nat.nth Nat.Prime 29 = 113 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP30 : Nat.nth Nat.Prime 30 = 127 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP31 : Nat.nth Nat.Prime 31 = 131 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP32 : Nat.nth Nat.Prime 32 = 137 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP33 : Nat.nth Nat.Prime 33 = 139 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP34 : Nat.nth Nat.Prime 34 = 149 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP35 : Nat.nth Nat.Prime 35 = 151 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP36 : Nat.nth Nat.Prime 36 = 157 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP37 : Nat.nth Nat.Prime 37 = 163 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP38 : Nat.nth Nat.Prime 38 = 167 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP39 : Nat.nth Nat.Prime 39 = 173 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP40 : Nat.nth Nat.Prime 40 = 179 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP41 : Nat.nth Nat.Prime 41 = 181 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP42 : Nat.nth Nat.Prime 42 = 191 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP43 : Nat.nth Nat.Prime 43 = 193 :=
  nth_of_count (by norm_num) (by decide)

lemma filter_prime_Ico_succ (n : ℕ) (hn : 1 ≤ n) :
    (Ico 1 (n + 1)).filter Nat.Prime =
      if Nat.Prime n then insert n ((Ico 1 n).filter Nat.Prime)
      else (Ico 1 n).filter Nat.Prime := by
  apply Finset.ext
  intro x
  by_cases hPn : Nat.Prime n
  · simp only [hPn, ite_true, mem_filter, mem_Ico, mem_insert]
    constructor
    · intro ⟨⟨hx1, hx2⟩, hp⟩
      have hx2' : x ≤ n := Nat.lt_succ_iff.mp hx2
      rcases eq_or_lt_of_le hx2' with rfl | hlt
      · exact Or.inl rfl
      · exact Or.inr ⟨⟨hx1, hlt⟩, hp⟩
    · intro h
      rcases h with rfl | ⟨⟨hx1, hx2⟩, hp⟩
      · exact ⟨⟨hn, Nat.lt_succ_self _⟩, hPn⟩
      · exact ⟨⟨hx1, Nat.lt_succ_of_lt hx2⟩, hp⟩
  · simp only [hPn, ite_false, mem_filter, mem_Ico]
    constructor
    · intro ⟨⟨hx1, hx2⟩, hp⟩
      have hx2' : x ≤ n := Nat.lt_succ_iff.mp hx2
      rcases eq_or_lt_of_le hx2' with rfl | hlt
      · exact (hPn hp).elim
      · exact ⟨⟨hx1, hlt⟩, hp⟩
    · intro ⟨⟨hx1, hx2⟩, hp⟩
      exact ⟨⟨hx1, Nat.lt_succ_of_lt hx2⟩, hp⟩

lemma primes_lt_1 : (Ico 1 1).filter Nat.Prime = (∅ : Finset ℕ) := rfl

lemma primes_lt_2 : (Ico 1 2).filter Nat.Prime = (∅ : Finset ℕ) := by
  have h := filter_prime_Ico_succ 1 (by decide)
  rw [show 1 + 1 = 2 from rfl] at h
  rw [h, primes_lt_1]
  have : ¬ Nat.Prime 1 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_3 : (Ico 1 3).filter Nat.Prime = {2} := by
  have h := filter_prime_Ico_succ 2 (by decide)
  rw [show 2 + 1 = 3 from rfl] at h
  rw [h, primes_lt_2]
  have : Nat.Prime 2 := by norm_num
  simp only [this, ite_true]
  decide

lemma primes_lt_4 : (Ico 1 4).filter Nat.Prime = {2, 3} := by
  have h := filter_prime_Ico_succ 3 (by decide)
  rw [show 3 + 1 = 4 from rfl] at h
  rw [h, primes_lt_3]
  have : Nat.Prime 3 := by norm_num
  simp only [this, ite_true]
  decide

lemma primes_lt_5 : (Ico 1 5).filter Nat.Prime = {2, 3} := by
  have h := filter_prime_Ico_succ 4 (by decide)
  rw [show 4 + 1 = 5 from rfl] at h
  rw [h, primes_lt_4]
  have : ¬ Nat.Prime 4 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_6 : (Ico 1 6).filter Nat.Prime = {2, 3, 5} := by
  have h := filter_prime_Ico_succ 5 (by decide)
  rw [show 5 + 1 = 6 from rfl] at h
  rw [h, primes_lt_5]
  have : Nat.Prime 5 := by norm_num
  simp only [this, ite_true]
  decide

lemma primes_lt_7 : (Ico 1 7).filter Nat.Prime = {2, 3, 5} := by
  have h := filter_prime_Ico_succ 6 (by decide)
  rw [show 6 + 1 = 7 from rfl] at h
  rw [h, primes_lt_6]
  have : ¬ Nat.Prime 6 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_8 : (Ico 1 8).filter Nat.Prime = {2, 3, 5, 7} := by
  have h := filter_prime_Ico_succ 7 (by decide)
  rw [show 7 + 1 = 8 from rfl] at h
  rw [h, primes_lt_7]
  have : Nat.Prime 7 := by norm_num
  simp only [this, ite_true]
  decide

lemma primes_lt_9 : (Ico 1 9).filter Nat.Prime = {2, 3, 5, 7} := by
  have h := filter_prime_Ico_succ 8 (by decide)
  rw [show 8 + 1 = 9 from rfl] at h
  rw [h, primes_lt_8]
  have : ¬ Nat.Prime 8 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_10 : (Ico 1 10).filter Nat.Prime = {2, 3, 5, 7} := by
  have h := filter_prime_Ico_succ 9 (by decide)
  rw [show 9 + 1 = 10 from rfl] at h
  rw [h, primes_lt_9]
  have : ¬ Nat.Prime 9 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_11 : (Ico 1 11).filter Nat.Prime = {2, 3, 5, 7} := by
  have h := filter_prime_Ico_succ 10 (by decide)
  rw [show 10 + 1 = 11 from rfl] at h
  rw [h, primes_lt_10]
  have : ¬ Nat.Prime 10 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_12 : (Ico 1 12).filter Nat.Prime = {2, 3, 5, 7, 11} := by
  have h := filter_prime_Ico_succ 11 (by decide)
  rw [show 11 + 1 = 12 from rfl] at h
  rw [h, primes_lt_11]
  have : Nat.Prime 11 := by norm_num
  simp only [this, ite_true]
  decide

lemma primes_lt_13 : (Ico 1 13).filter Nat.Prime = {2, 3, 5, 7, 11} := by
  have h := filter_prime_Ico_succ 12 (by decide)
  rw [show 12 + 1 = 13 from rfl] at h
  rw [h, primes_lt_12]
  have : ¬ Nat.Prime 12 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_14 : (Ico 1 14).filter Nat.Prime = {2, 3, 5, 7, 11, 13} := by
  have h := filter_prime_Ico_succ 13 (by decide)
  rw [show 13 + 1 = 14 from rfl] at h
  rw [h, primes_lt_13]
  have : Nat.Prime 13 := by norm_num
  simp only [this, ite_true]
  decide

lemma primes_lt_15 : (Ico 1 15).filter Nat.Prime = {2, 3, 5, 7, 11, 13} := by
  have h := filter_prime_Ico_succ 14 (by decide)
  rw [show 14 + 1 = 15 from rfl] at h
  rw [h, primes_lt_14]
  have : ¬ Nat.Prime 14 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_16 : (Ico 1 16).filter Nat.Prime = {2, 3, 5, 7, 11, 13} := by
  have h := filter_prime_Ico_succ 15 (by decide)
  rw [show 15 + 1 = 16 from rfl] at h
  rw [h, primes_lt_15]
  have : ¬ Nat.Prime 15 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_17 : (Ico 1 17).filter Nat.Prime = {2, 3, 5, 7, 11, 13} := by
  have h := filter_prime_Ico_succ 16 (by decide)
  rw [show 16 + 1 = 17 from rfl] at h
  rw [h, primes_lt_16]
  have : ¬ Nat.Prime 16 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_18 : (Ico 1 18).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17} := by
  have h := filter_prime_Ico_succ 17 (by decide)
  rw [show 17 + 1 = 18 from rfl] at h
  rw [h, primes_lt_17]
  have : Nat.Prime 17 := by norm_num
  simp only [this, ite_true]
  decide

lemma primes_lt_19 : (Ico 1 19).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17} := by
  have h := filter_prime_Ico_succ 18 (by decide)
  rw [show 18 + 1 = 19 from rfl] at h
  rw [h, primes_lt_18]
  have : ¬ Nat.Prime 18 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_20 : (Ico 1 20).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19} := by
  have h := filter_prime_Ico_succ 19 (by decide)
  rw [show 19 + 1 = 20 from rfl] at h
  rw [h, primes_lt_19]
  have : Nat.Prime 19 := by norm_num
  simp only [this, ite_true]
  decide

lemma primes_lt_21 : (Ico 1 21).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19} := by
  have h := filter_prime_Ico_succ 20 (by decide)
  rw [show 20 + 1 = 21 from rfl] at h
  rw [h, primes_lt_20]
  have : ¬ Nat.Prime 20 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_22 : (Ico 1 22).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19} := by
  have h := filter_prime_Ico_succ 21 (by decide)
  rw [show 21 + 1 = 22 from rfl] at h
  rw [h, primes_lt_21]
  have : ¬ Nat.Prime 21 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_23 : (Ico 1 23).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19} := by
  have h := filter_prime_Ico_succ 22 (by decide)
  rw [show 22 + 1 = 23 from rfl] at h
  rw [h, primes_lt_22]
  have : ¬ Nat.Prime 22 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_24 : (Ico 1 24).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23} := by
  have h := filter_prime_Ico_succ 23 (by decide)
  rw [show 23 + 1 = 24 from rfl] at h
  rw [h, primes_lt_23]
  have : Nat.Prime 23 := by norm_num
  simp only [this, ite_true]
  decide

lemma primes_lt_25 : (Ico 1 25).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23} := by
  have h := filter_prime_Ico_succ 24 (by decide)
  rw [show 24 + 1 = 25 from rfl] at h
  rw [h, primes_lt_24]
  have : ¬ Nat.Prime 24 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_26 : (Ico 1 26).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23} := by
  have h := filter_prime_Ico_succ 25 (by decide)
  rw [show 25 + 1 = 26 from rfl] at h
  rw [h, primes_lt_25]
  have : ¬ Nat.Prime 25 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_27 : (Ico 1 27).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23} := by
  have h := filter_prime_Ico_succ 26 (by decide)
  rw [show 26 + 1 = 27 from rfl] at h
  rw [h, primes_lt_26]
  have : ¬ Nat.Prime 26 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_28 : (Ico 1 28).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23} := by
  have h := filter_prime_Ico_succ 27 (by decide)
  rw [show 27 + 1 = 28 from rfl] at h
  rw [h, primes_lt_27]
  have : ¬ Nat.Prime 27 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_29 : (Ico 1 29).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23} := by
  have h := filter_prime_Ico_succ 28 (by decide)
  rw [show 28 + 1 = 29 from rfl] at h
  rw [h, primes_lt_28]
  have : ¬ Nat.Prime 28 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_30 : (Ico 1 30).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29} := by
  have h := filter_prime_Ico_succ 29 (by decide)
  rw [show 29 + 1 = 30 from rfl] at h
  rw [h, primes_lt_29]
  have : Nat.Prime 29 := by norm_num
  simp only [this, ite_true]
  decide

lemma primes_lt_31 : (Ico 1 31).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29} := by
  have h := filter_prime_Ico_succ 30 (by decide)
  rw [show 30 + 1 = 31 from rfl] at h
  rw [h, primes_lt_30]
  have : ¬ Nat.Prime 30 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_32 : (Ico 1 32).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} := by
  have h := filter_prime_Ico_succ 31 (by decide)
  rw [show 31 + 1 = 32 from rfl] at h
  rw [h, primes_lt_31]
  have : Nat.Prime 31 := by norm_num
  simp only [this, ite_true]
  decide

lemma primes_lt_33 : (Ico 1 33).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} := by
  have h := filter_prime_Ico_succ 32 (by decide)
  rw [show 32 + 1 = 33 from rfl] at h
  rw [h, primes_lt_32]
  have : ¬ Nat.Prime 32 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_34 : (Ico 1 34).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} := by
  have h := filter_prime_Ico_succ 33 (by decide)
  rw [show 33 + 1 = 34 from rfl] at h
  rw [h, primes_lt_33]
  have : ¬ Nat.Prime 33 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_35 : (Ico 1 35).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} := by
  have h := filter_prime_Ico_succ 34 (by decide)
  rw [show 34 + 1 = 35 from rfl] at h
  rw [h, primes_lt_34]
  have : ¬ Nat.Prime 34 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_36 : (Ico 1 36).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} := by
  have h := filter_prime_Ico_succ 35 (by decide)
  rw [show 35 + 1 = 36 from rfl] at h
  rw [h, primes_lt_35]
  have : ¬ Nat.Prime 35 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_37 : (Ico 1 37).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} := by
  have h := filter_prime_Ico_succ 36 (by decide)
  rw [show 36 + 1 = 37 from rfl] at h
  rw [h, primes_lt_36]
  have : ¬ Nat.Prime 36 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_38 : (Ico 1 38).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37} := by
  have h := filter_prime_Ico_succ 37 (by decide)
  rw [show 37 + 1 = 38 from rfl] at h
  rw [h, primes_lt_37]
  have : Nat.Prime 37 := by norm_num
  simp only [this, ite_true]
  decide

lemma primes_lt_39 : (Ico 1 39).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37} := by
  have h := filter_prime_Ico_succ 38 (by decide)
  rw [show 38 + 1 = 39 from rfl] at h
  rw [h, primes_lt_38]
  have : ¬ Nat.Prime 38 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_40 : (Ico 1 40).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37} := by
  have h := filter_prime_Ico_succ 39 (by decide)
  rw [show 39 + 1 = 40 from rfl] at h
  rw [h, primes_lt_39]
  have : ¬ Nat.Prime 39 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_41 : (Ico 1 41).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37} := by
  have h := filter_prime_Ico_succ 40 (by decide)
  rw [show 40 + 1 = 41 from rfl] at h
  rw [h, primes_lt_40]
  have : ¬ Nat.Prime 40 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_42 : (Ico 1 42).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41} := by
  have h := filter_prime_Ico_succ 41 (by decide)
  rw [show 41 + 1 = 42 from rfl] at h
  rw [h, primes_lt_41]
  have : Nat.Prime 41 := by norm_num
  simp only [this, ite_true]
  decide

lemma primes_lt_43 : (Ico 1 43).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41} := by
  have h := filter_prime_Ico_succ 42 (by decide)
  rw [show 42 + 1 = 43 from rfl] at h
  rw [h, primes_lt_42]
  have : ¬ Nat.Prime 42 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_44 : (Ico 1 44).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43} := by
  have h := filter_prime_Ico_succ 43 (by decide)
  rw [show 43 + 1 = 44 from rfl] at h
  rw [h, primes_lt_43]
  have : Nat.Prime 43 := by norm_num
  simp only [this, ite_true]
  decide

lemma a_eq_card (n : ℕ) :
    a n = (((Ico 1 n).filter Nat.Prime).filter (fun k =>
      Nat.Prime (Nat.nth Nat.Prime (k - 1) ^ 2 +
        (Nat.nth Nat.Prime (n - 1) - 1) ^ 2))).card := by
  unfold a
  rw [sum_boole]
  simp [filter_filter]

lemma a_val_1 : a 1 = 0 := by simp [a]

lemma a_val_2 : a 2 = 0 := by
  rw [a_eq_card, primes_lt_2]
  simp

lemma a_filter_3 :
    {x ∈ ({2} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (5 - 1) ^ 2)} = (∅ : Finset ℕ) := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl
    · rw [nthP1] at hp; norm_num at hp
  · intro h
    simp at h

lemma a_val_3 : a 3 = 0 := by
  rw [a_eq_card, primes_lt_3, nthP2, a_filter_3]
  decide

lemma a_filter_4 :
    {x ∈ ({2, 3} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (7 - 1) ^ 2)} = {3} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · rfl
  · intro h
    rcases h with rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP2]; norm_num

lemma a_val_4 : a 4 = 1 := by
  rw [a_eq_card, primes_lt_4, nthP3, a_filter_4]
  decide

lemma a_filter_5 :
    {x ∈ ({2, 3} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (11 - 1) ^ 2)} = {2} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl
    · rfl
    · rw [nthP2] at hp; norm_num at hp
  · intro h
    rcases h with rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP1]; norm_num

lemma a_val_5 : a 5 = 1 := by
  rw [a_eq_card, primes_lt_5, nthP4, a_filter_5]
  decide

lemma a_filter_6 :
    {x ∈ ({2, 3, 5} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (13 - 1) ^ 2)} = (∅ : Finset ℕ) := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · rw [nthP2] at hp; norm_num at hp
    · rw [nthP4] at hp; norm_num at hp
  · intro h
    simp at h

lemma a_val_6 : a 6 = 0 := by
  rw [a_eq_card, primes_lt_6, nthP5, a_filter_6]
  decide

lemma a_filter_7 :
    {x ∈ ({2, 3, 5} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (17 - 1) ^ 2)} = {3} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · rfl
    · rw [nthP4] at hp; norm_num at hp
  · intro h
    rcases h with rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP2]; norm_num

lemma a_val_7 : a 7 = 1 := by
  rw [a_eq_card, primes_lt_7, nthP6, a_filter_7]
  decide

lemma a_filter_10 :
    {x ∈ ({2, 3, 5, 7} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (29 - 1) ^ 2)} = {3} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · rfl
    · rw [nthP4] at hp; norm_num at hp
    · rw [nthP6] at hp; norm_num at hp
  · intro h
    rcases h with rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP2]; norm_num

lemma a_val_10 : a 10 = 1 := by
  rw [a_eq_card, primes_lt_10, nthP9, a_filter_10]
  decide

lemma a_filter_11 :
    {x ∈ ({2, 3, 5, 7} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (31 - 1) ^ 2)} = {5} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · rw [nthP2] at hp; norm_num at hp
    · rfl
    · rw [nthP6] at hp; norm_num at hp
  · intro h
    rcases h with rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP4]; norm_num

lemma a_val_11 : a 11 = 1 := by
  rw [a_eq_card, primes_lt_11, nthP10, a_filter_11]
  decide

lemma a_filter_12 :
    {x ∈ ({2, 3, 5, 7, 11} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (37 - 1) ^ 2)} = {3} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · rfl
    · rw [nthP4] at hp; norm_num at hp
    · rw [nthP6] at hp; norm_num at hp
    · rw [nthP10] at hp; norm_num at hp
  · intro h
    rcases h with rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP2]; norm_num

lemma a_val_12 : a 12 = 1 := by
  rw [a_eq_card, primes_lt_12, nthP11, a_filter_12]
  decide

lemma a_filter_19 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (67 - 1) ^ 2)} = {13} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · rw [nthP2] at hp; norm_num at hp
    · rw [nthP4] at hp; norm_num at hp
    · rw [nthP6] at hp; norm_num at hp
    · rw [nthP10] at hp; norm_num at hp
    · rfl
    · rw [nthP16] at hp; norm_num at hp
  · intro h
    rcases h with rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP12]; norm_num

lemma a_val_19 : a 19 = 1 := by
  rw [a_eq_card, primes_lt_19, nthP18, a_filter_19]
  decide

lemma a_filter_21 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (73 - 1) ^ 2)} = {3} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · rfl
    · rw [nthP4] at hp; norm_num at hp
    · rw [nthP6] at hp; norm_num at hp
    · rw [nthP10] at hp; norm_num at hp
    · rw [nthP12] at hp; norm_num at hp
    · rw [nthP16] at hp; norm_num at hp
    · rw [nthP18] at hp; norm_num at hp
  · intro h
    rcases h with rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP2]; norm_num

lemma a_val_21 : a 21 = 1 := by
  rw [a_eq_card, primes_lt_21, nthP20, a_filter_21]
  decide

lemma a_filter_22 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (79 - 1) ^ 2)} = {7} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · rw [nthP2] at hp; norm_num at hp
    · rw [nthP4] at hp; norm_num at hp
    · rfl
    · rw [nthP10] at hp; norm_num at hp
    · rw [nthP12] at hp; norm_num at hp
    · rw [nthP16] at hp; norm_num at hp
    · rw [nthP18] at hp; norm_num at hp
  · intro h
    rcases h with rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP6]; norm_num

lemma a_val_22 : a 22 = 1 := by
  rw [a_eq_card, primes_lt_22, nthP21, a_filter_22]
  decide

lemma a_filter_31 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (127 - 1) ^ 2)} = {3} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · rfl
    · rw [nthP4] at hp; norm_num at hp
    · rw [nthP6] at hp; norm_num at hp
    · rw [nthP10] at hp; norm_num at hp
    · rw [nthP12] at hp; norm_num at hp
    · rw [nthP16] at hp; norm_num at hp
    · rw [nthP18] at hp; norm_num at hp
    · rw [nthP22] at hp; norm_num at hp
    · rw [nthP28] at hp; norm_num at hp
  · intro h
    rcases h with rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP2]; norm_num

lemma a_val_31 : a 31 = 1 := by
  rw [a_eq_card, primes_lt_31, nthP30, a_filter_31]
  decide

lemma a_filter_42 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (181 - 1) ^ 2)} = {29} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · rw [nthP2] at hp; norm_num at hp
    · rw [nthP4] at hp; norm_num at hp
    · rw [nthP6] at hp; norm_num at hp
    · rw [nthP10] at hp; norm_num at hp
    · rw [nthP12] at hp; norm_num at hp
    · rw [nthP16] at hp; norm_num at hp
    · rw [nthP18] at hp; norm_num at hp
    · rw [nthP22] at hp; norm_num at hp
    · rfl
    · rw [nthP30] at hp; norm_num at hp
    · rw [nthP36] at hp; norm_num at hp
    · rw [nthP40] at hp; norm_num at hp
  · intro h
    rcases h with rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP28]; norm_num

lemma a_val_42 : a 42 = 1 := by
  rw [a_eq_card, primes_lt_42, nthP41, a_filter_42]
  decide

lemma a_filter_44 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (193 - 1) ^ 2)} = {23} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · rw [nthP2] at hp; norm_num at hp
    · rw [nthP4] at hp; norm_num at hp
    · rw [nthP6] at hp; norm_num at hp
    · rw [nthP10] at hp; norm_num at hp
    · rw [nthP12] at hp; norm_num at hp
    · rw [nthP16] at hp; norm_num at hp
    · rw [nthP18] at hp; norm_num at hp
    · rfl
    · rw [nthP28] at hp; norm_num at hp
    · rw [nthP30] at hp; norm_num at hp
    · rw [nthP36] at hp; norm_num at hp
    · rw [nthP40] at hp; norm_num at hp
    · rw [nthP42] at hp; norm_num at hp
  · intro h
    rcases h with rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP22]; norm_num

lemma a_val_44 : a 44 = 1 := by
  rw [a_eq_card, primes_lt_44, nthP43, a_filter_44]
  decide

lemma dvd_six_iff {n : ℕ} (hn : n > 0) : n ∣ 6 ↔ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6 := by
  constructor
  · intro h
    have : n ≤ 6 := Nat.le_of_dvd (by decide) h
    interval_cases n <;> omega
  · rintro (rfl | rfl | rfl | rfl) <;> decide

lemma pair_card {x y : ℕ} (h : x ≠ y) : #({x, y} : Finset ℕ) = 2 := by
  simp [h]

lemma a_ge_two_of_hits (n k₁ k₂ : ℕ) (hne : k₁ ≠ k₂)
    (hk1 : k₁ ∈ Ico 1 n) (hk2 : k₂ ∈ Ico 1 n)
    (hp1 : Nat.Prime k₁) (hp2 : Nat.Prime k₂)
    (hq1 : Nat.Prime (Nat.nth Nat.Prime (k₁ - 1) ^ 2 +
      (Nat.nth Nat.Prime (n - 1) - 1) ^ 2))
    (hq2 : Nat.Prime (Nat.nth Nat.Prime (k₂ - 1) ^ 2 +
      (Nat.nth Nat.Prime (n - 1) - 1) ^ 2)) :
    2 ≤ a n := by
  rw [a_eq_card]
  have hsub : {k₁, k₂} ⊆ ((Ico 1 n).filter Nat.Prime).filter (fun k =>
      Nat.Prime (Nat.nth Nat.Prime (k - 1) ^ 2 +
        (Nat.nth Nat.Prime (n - 1) - 1) ^ 2)) := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · simp [mem_filter, hk1, hp1, hq1]
    · simp [mem_filter, hk2, hp2, hq2]
  have := card_mono hsub
  have hc : #({k₁, k₂} : Finset ℕ) = 2 := pair_card hne
  omega


lemma a_ge_two_8 : 2 ≤ a 8 :=
  a_ge_two_of_hits 8 3 7 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP7]; norm_num)
    (by rw [nthP6, nthP7]; norm_num)

lemma a_ge_two_9 : 2 ≤ a 9 :=
  a_ge_two_of_hits 9 3 7 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP8]; norm_num)
    (by rw [nthP6, nthP8]; norm_num)

lemma a_ge_two_13 : 2 ≤ a 13 :=
  a_ge_two_of_hits 13 2 5 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP1, nthP12]; norm_num)
    (by rw [nthP4, nthP12]; norm_num)

lemma a_ge_two_14 : 2 ≤ a 14 :=
  a_ge_two_of_hits 14 3 7 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP13]; norm_num)
    (by rw [nthP6, nthP13]; norm_num)

lemma a_ge_two_15 : 2 ≤ a 15 :=
  a_ge_two_of_hits 15 3 5 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP14]; norm_num)
    (by rw [nthP4, nthP14]; norm_num)

lemma a_ge_two_16 : 2 ≤ a 16 :=
  a_ge_two_of_hits 16 2 3 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP1, nthP15]; norm_num)
    (by rw [nthP2, nthP15]; norm_num)

lemma a_ge_two_17 : 2 ≤ a 17 :=
  a_ge_two_of_hits 17 2 3 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP1, nthP16]; norm_num)
    (by rw [nthP2, nthP16]; norm_num)

lemma a_ge_two_18 : 2 ≤ a 18 :=
  a_ge_two_of_hits 18 7 11 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP6, nthP17]; norm_num)
    (by rw [nthP10, nthP17]; norm_num)

lemma a_ge_two_20 : 2 ≤ a 20 :=
  a_ge_two_of_hits 20 2 5 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP1, nthP19]; norm_num)
    (by rw [nthP4, nthP19]; norm_num)

lemma a_ge_two_23 : 2 ≤ a 23 :=
  a_ge_two_of_hits 23 2 7 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP1, nthP22]; norm_num)
    (by rw [nthP6, nthP22]; norm_num)

lemma a_ge_two_24 : 2 ≤ a 24 :=
  a_ge_two_of_hits 24 2 23 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP1, nthP23]; norm_num)
    (by rw [nthP22, nthP23]; norm_num)

lemma a_ge_two_25 : 2 ≤ a 25 :=
  a_ge_two_of_hits 25 3 5 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP24]; norm_num)
    (by rw [nthP4, nthP24]; norm_num)

lemma a_ge_two_26 : 2 ≤ a 26 :=
  a_ge_two_of_hits 26 2 7 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP1, nthP25]; norm_num)
    (by rw [nthP6, nthP25]; norm_num)

lemma a_ge_two_27 : 2 ≤ a 27 :=
  a_ge_two_of_hits 27 3 23 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP26]; norm_num)
    (by rw [nthP22, nthP26]; norm_num)

lemma a_ge_two_28 : 2 ≤ a 28 :=
  a_ge_two_of_hits 28 3 11 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP27]; norm_num)
    (by rw [nthP10, nthP27]; norm_num)

lemma a_ge_two_29 : 2 ≤ a 29 :=
  a_ge_two_of_hits 29 3 7 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP28]; norm_num)
    (by rw [nthP6, nthP28]; norm_num)

lemma a_ge_two_30 : 2 ≤ a 30 :=
  a_ge_two_of_hits 30 2 3 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP1, nthP29]; norm_num)
    (by rw [nthP2, nthP29]; norm_num)

lemma a_ge_two_32 : 2 ≤ a 32 :=
  a_ge_two_of_hits 32 5 7 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP4, nthP31]; norm_num)
    (by rw [nthP6, nthP31]; norm_num)

lemma a_ge_two_33 : 2 ≤ a 33 :=
  a_ge_two_of_hits 33 3 5 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP32]; norm_num)
    (by rw [nthP4, nthP32]; norm_num)

lemma a_ge_two_34 : 2 ≤ a 34 :=
  a_ge_two_of_hits 34 3 7 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP33]; norm_num)
    (by rw [nthP6, nthP33]; norm_num)

lemma a_ge_two_35 : 2 ≤ a 35 :=
  a_ge_two_of_hits 35 3 7 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP34]; norm_num)
    (by rw [nthP6, nthP34]; norm_num)

lemma a_ge_two_36 : 2 ≤ a 36 :=
  a_ge_two_of_hits 36 5 13 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP4, nthP35]; norm_num)
    (by rw [nthP12, nthP35]; norm_num)

lemma a_ge_two_37 : 2 ≤ a 37 :=
  a_ge_two_of_hits 37 13 17 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP12, nthP36]; norm_num)
    (by rw [nthP16, nthP36]; norm_num)

lemma a_ge_two_38 : 2 ≤ a 38 :=
  a_ge_two_of_hits 38 31 37 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP30, nthP37]; norm_num)
    (by rw [nthP36, nthP37]; norm_num)

lemma a_ge_two_39 : 2 ≤ a 39 :=
  a_ge_two_of_hits 39 3 11 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP38]; norm_num)
    (by rw [nthP10, nthP38]; norm_num)

lemma a_ge_two_40 : 2 ≤ a 40 :=
  a_ge_two_of_hits 40 7 23 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP6, nthP39]; norm_num)
    (by rw [nthP22, nthP39]; norm_num)

lemma a_ge_two_41 : 2 ≤ a 41 :=
  a_ge_two_of_hits 41 7 37 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP6, nthP40]; norm_num)
    (by rw [nthP36, nthP40]; norm_num)

lemma a_ge_two_43 : 2 ≤ a 43 :=
  a_ge_two_of_hits 43 2 7 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP1, nthP42]; norm_num)
    (by rw [nthP6, nthP42]; norm_num)



lemma a_ge_two_8_to_18 (n : ℕ) (h1 : 8 ≤ n) (h2 : n ≤ 18)
    (hns : n ≠ 10 ∧ n ≠ 11 ∧ n ≠ 12) : 2 ≤ a n := by
  interval_cases n
  · exact a_ge_two_8
  · exact a_ge_two_9
  · omega
  · omega
  · omega
  · exact a_ge_two_13
  · exact a_ge_two_14
  · exact a_ge_two_15
  · exact a_ge_two_16
  · exact a_ge_two_17
  · exact a_ge_two_18

lemma a_ge_two_20_to_30 (n : ℕ) (h1 : 20 ≤ n) (h2 : n ≤ 30)
    (hns : n ≠ 21 ∧ n ≠ 22) : 2 ≤ a n := by
  interval_cases n
  · exact a_ge_two_20
  · omega
  · omega
  · exact a_ge_two_23
  · exact a_ge_two_24
  · exact a_ge_two_25
  · exact a_ge_two_26
  · exact a_ge_two_27
  · exact a_ge_two_28
  · exact a_ge_two_29
  · exact a_ge_two_30

lemma a_ge_two_32_to_43 (n : ℕ) (h1 : 32 ≤ n) (h2 : n ≤ 43)
    (hns : n ≠ 31 ∧ n ≠ 42 ∧ n ≠ 44) : 2 ≤ a n := by
  interval_cases n
  · exact a_ge_two_32
  · exact a_ge_two_33
  · exact a_ge_two_34
  · exact a_ge_two_35
  · exact a_ge_two_36
  · exact a_ge_two_37
  · exact a_ge_two_38
  · exact a_ge_two_39
  · exact a_ge_two_40
  · exact a_ge_two_41
  · omega
  · exact a_ge_two_43

lemma a_ge_two_nonspecial_le_44 (n : ℕ) (hn : 8 ≤ n) (hle : n ≤ 44)
    (hns : ¬ (n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨
      n = 19 ∨ n = 21 ∨ n = 22 ∨ n = 31 ∨ n = 42 ∨ n = 44)) : 2 ≤ a n := by
  if h18 : n ≤ 18 then
    exact a_ge_two_8_to_18 n hn h18 (by omega)
  else if h30 : n ≤ 30 then
    have : 20 ≤ n := by omega
    exact a_ge_two_20_to_30 n this h30 (by omega)
  else
    have : 32 ≤ n := by omega
    have : n ≤ 43 := by omega
    exact a_ge_two_32_to_43 n ‹32 ≤ n› this (by omega)

lemma a_eq_zero_of_dvd_six {n : ℕ} (hz : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6) : a n = 0 := by
  rcases hz with rfl | rfl | rfl | rfl <;> simp [a_val_1, a_val_2, a_val_3, a_val_6]

lemma a_eq_one_of_listed {n : ℕ}
    (hone : n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨
      n = 19 ∨ n = 21 ∨ n = 22 ∨ n = 31 ∨ n = 42 ∨ n = 44) : a n = 1 := by
  rcases hone with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    <;> simp [a_val_4, a_val_5, a_val_7, a_val_10, a_val_11, a_val_12,
      a_val_19, a_val_21, a_val_22, a_val_31, a_val_42, a_val_44]

lemma a_pos_iff_of_le_44 (n : ℕ) (hn : 0 < n) (h : n ≤ 44) :
    a n > 0 ↔ ¬ n ∣ 6 := by
  have hdiv : n ∣ 6 ↔ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6 := dvd_six_iff hn
  if hz : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6 then
    have ha := a_eq_zero_of_dvd_six hz
    have : n ∣ 6 := hdiv.mpr hz
    simp [this, ha]
  else
    have hnd : ¬ n ∣ 6 := fun hd => hz (hdiv.mp hd)
    have hpos : 0 < a n := by
      if hone : n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨
          n = 19 ∨ n = 21 ∨ n = 22 ∨ n = 31 ∨ n = 42 ∨ n = 44 then
        have := a_eq_one_of_listed hone
        omega
      else
        have hn8 : 8 ≤ n := by omega
        have := a_ge_two_nonspecial_le_44 n hn8 h hone
        omega
    simp [hnd, hpos]

lemma a_eq_one_iff_of_le_44 (n : ℕ) (hn : 0 < n) (h : n ≤ 44) :
    a n = 1 ↔ n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨
      n = 19 ∨ n = 21 ∨ n = 22 ∨ n = 31 ∨ n = 42 ∨ n = 44 := by
  constructor
  · intro ha
    by_contra hns
    if hz : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6 then
      have := a_eq_zero_of_dvd_six hz
      omega
    else
      have hn8 : 8 ≤ n := by omega
      have := a_ge_two_nonspecial_le_44 n hn8 h hns
      omega
  · exact a_eq_one_of_listed


lemma nthP44 : Nat.nth Nat.Prime 44 = 197 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP45 : Nat.nth Nat.Prime 45 = 199 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP46 : Nat.nth Nat.Prime 46 = 211 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP47 : Nat.nth Nat.Prime 47 = 223 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP48 : Nat.nth Nat.Prime 48 = 227 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP49 : Nat.nth Nat.Prime 49 = 229 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP50 : Nat.nth Nat.Prime 50 = 233 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP51 : Nat.nth Nat.Prime 51 = 239 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP52 : Nat.nth Nat.Prime 52 = 241 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP53 : Nat.nth Nat.Prime 53 = 251 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP54 : Nat.nth Nat.Prime 54 = 257 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP55 : Nat.nth Nat.Prime 55 = 263 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP56 : Nat.nth Nat.Prime 56 = 269 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP57 : Nat.nth Nat.Prime 57 = 271 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP58 : Nat.nth Nat.Prime 58 = 277 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP59 : Nat.nth Nat.Prime 59 = 281 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP60 : Nat.nth Nat.Prime 60 = 283 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP61 : Nat.nth Nat.Prime 61 = 293 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP62 : Nat.nth Nat.Prime 62 = 307 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP63 : Nat.nth Nat.Prime 63 = 311 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP64 : Nat.nth Nat.Prime 64 = 313 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP65 : Nat.nth Nat.Prime 65 = 317 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP66 : Nat.nth Nat.Prime 66 = 331 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP67 : Nat.nth Nat.Prime 67 = 337 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP68 : Nat.nth Nat.Prime 68 = 347 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP69 : Nat.nth Nat.Prime 69 = 349 :=
  nth_of_count (by norm_num) (by decide)

lemma a_ge_two_45 : 2 ≤ a 45 :=
  a_ge_two_of_hits 45 17 41 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP16, nthP44]; norm_num)
    (by rw [nthP40, nthP44]; norm_num)

lemma a_ge_two_46 : 2 ≤ a 46 :=
  a_ge_two_of_hits 46 3 23 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP45]; norm_num)
    (by rw [nthP22, nthP45]; norm_num)

lemma a_ge_two_47 : 2 ≤ a 47 :=
  a_ge_two_of_hits 47 5 7 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP4, nthP46]; norm_num)
    (by rw [nthP6, nthP46]; norm_num)

lemma a_ge_two_48 : 2 ≤ a 48 :=
  a_ge_two_of_hits 48 19 31 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP18, nthP47]; norm_num)
    (by rw [nthP30, nthP47]; norm_num)

lemma a_ge_two_49 : 2 ≤ a 49 :=
  a_ge_two_of_hits 49 5 13 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP4, nthP48]; norm_num)
    (by rw [nthP12, nthP48]; norm_num)

lemma a_ge_two_50 : 2 ≤ a 50 :=
  a_ge_two_of_hits 50 3 19 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP49]; norm_num)
    (by rw [nthP18, nthP49]; norm_num)

lemma a_ge_two_51 : 2 ≤ a 51 :=
  a_ge_two_of_hits 51 3 19 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP50]; norm_num)
    (by rw [nthP18, nthP50]; norm_num)

lemma a_ge_two_52 : 2 ≤ a 52 :=
  a_ge_two_of_hits 52 23 37 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP22, nthP51]; norm_num)
    (by rw [nthP36, nthP51]; norm_num)

lemma a_ge_two_53 : 2 ≤ a 53 :=
  a_ge_two_of_hits 53 13 23 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP12, nthP52]; norm_num)
    (by rw [nthP22, nthP52]; norm_num)

lemma a_ge_two_54 : 2 ≤ a 54 :=
  a_ge_two_of_hits 54 17 23 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP16, nthP53]; norm_num)
    (by rw [nthP22, nthP53]; norm_num)

lemma a_ge_two_55 : 2 ≤ a 55 :=
  a_ge_two_of_hits 55 5 13 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP4, nthP54]; norm_num)
    (by rw [nthP12, nthP54]; norm_num)

lemma a_ge_two_56 : 2 ≤ a 56 :=
  a_ge_two_of_hits 56 3 19 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP55]; norm_num)
    (by rw [nthP18, nthP55]; norm_num)

lemma a_ge_two_57 : 2 ≤ a 57 :=
  a_ge_two_of_hits 57 3 23 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP56]; norm_num)
    (by rw [nthP22, nthP56]; norm_num)

lemma a_ge_two_58 : 2 ≤ a 58 :=
  a_ge_two_of_hits 58 7 37 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP6, nthP57]; norm_num)
    (by rw [nthP36, nthP57]; norm_num)

lemma a_ge_two_59 : 2 ≤ a 59 :=
  a_ge_two_of_hits 59 11 17 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP10, nthP58]; norm_num)
    (by rw [nthP16, nthP58]; norm_num)

lemma a_ge_two_60 : 2 ≤ a 60 :=
  a_ge_two_of_hits 60 19 29 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP18, nthP59]; norm_num)
    (by rw [nthP28, nthP59]; norm_num)

lemma a_ge_two_61 : 2 ≤ a 61 :=
  a_ge_two_of_hits 61 3 7 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP60]; norm_num)
    (by rw [nthP6, nthP60]; norm_num)

lemma a_ge_two_62 : 2 ≤ a 62 :=
  a_ge_two_of_hits 62 19 23 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP18, nthP61]; norm_num)
    (by rw [nthP22, nthP61]; norm_num)

lemma a_ge_two_63 : 2 ≤ a 63 :=
  a_ge_two_of_hits 63 11 13 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP10, nthP62]; norm_num)
    (by rw [nthP12, nthP62]; norm_num)

lemma a_ge_two_64 : 2 ≤ a 64 :=
  a_ge_two_of_hits 64 5 17 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP4, nthP63]; norm_num)
    (by rw [nthP16, nthP63]; norm_num)

lemma a_ge_two_65 : 2 ≤ a 65 :=
  a_ge_two_of_hits 65 3 19 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP64]; norm_num)
    (by rw [nthP18, nthP64]; norm_num)

lemma a_ge_two_66 : 2 ≤ a 66 :=
  a_ge_two_of_hits 66 3 13 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP65]; norm_num)
    (by rw [nthP12, nthP65]; norm_num)

lemma a_ge_two_67 : 2 ≤ a 67 :=
  a_ge_two_of_hits 67 13 31 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP12, nthP66]; norm_num)
    (by rw [nthP30, nthP66]; norm_num)

lemma a_ge_two_68 : 2 ≤ a 68 :=
  a_ge_two_of_hits 68 3 5 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP67]; norm_num)
    (by rw [nthP4, nthP67]; norm_num)

lemma a_ge_two_69 : 2 ≤ a 69 :=
  a_ge_two_of_hits 69 11 53 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP10, nthP68]; norm_num)
    (by rw [nthP52, nthP68]; norm_num)

lemma a_ge_two_70 : 2 ≤ a 70 :=
  a_ge_two_of_hits 70 37 61 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP36, nthP69]; norm_num)
    (by rw [nthP60, nthP69]; norm_num)


lemma a_ge_two_45_to_56 (n : ℕ) (h1 : 45 ≤ n) (h2 : n ≤ 56) : 2 ≤ a n := by
  interval_cases n
  · exact a_ge_two_45
  · exact a_ge_two_46
  · exact a_ge_two_47
  · exact a_ge_two_48
  · exact a_ge_two_49
  · exact a_ge_two_50
  · exact a_ge_two_51
  · exact a_ge_two_52
  · exact a_ge_two_53
  · exact a_ge_two_54
  · exact a_ge_two_55
  · exact a_ge_two_56

lemma a_ge_two_57_to_70 (n : ℕ) (h1 : 57 ≤ n) (h2 : n ≤ 70) : 2 ≤ a n := by
  interval_cases n
  · exact a_ge_two_57
  · exact a_ge_two_58
  · exact a_ge_two_59
  · exact a_ge_two_60
  · exact a_ge_two_61
  · exact a_ge_two_62
  · exact a_ge_two_63
  · exact a_ge_two_64
  · exact a_ge_two_65
  · exact a_ge_two_66
  · exact a_ge_two_67
  · exact a_ge_two_68
  · exact a_ge_two_69
  · exact a_ge_two_70

lemma a_ge_two_45_70 (n : ℕ) (h1 : 45 ≤ n) (h2 : n ≤ 70) : 2 ≤ a n := by
  if h : n ≤ 56 then
    exact a_ge_two_45_to_56 n h1 h
  else
    have : 57 ≤ n := by omega
    exact a_ge_two_57_to_70 n this h2

lemma nthP70 : Nat.nth Nat.Prime 70 = 353 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP71 : Nat.nth Nat.Prime 71 = 359 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP72 : Nat.nth Nat.Prime 72 = 367 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP73 : Nat.nth Nat.Prime 73 = 373 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP74 : Nat.nth Nat.Prime 74 = 379 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP75 : Nat.nth Nat.Prime 75 = 383 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP76 : Nat.nth Nat.Prime 76 = 389 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP77 : Nat.nth Nat.Prime 77 = 397 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP78 : Nat.nth Nat.Prime 78 = 401 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP79 : Nat.nth Nat.Prime 79 = 409 :=
  nth_of_count (by norm_num) (by decide)

lemma a_ge_two_71 : 2 ≤ a 71 :=
  a_ge_two_of_hits 71 7 19 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP6, nthP70]; norm_num)
    (by rw [nthP18, nthP70]; norm_num)

lemma a_ge_two_72 : 2 ≤ a 72 :=
  a_ge_two_of_hits 72 2 3 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP1, nthP71]; norm_num)
    (by rw [nthP2, nthP71]; norm_num)

lemma a_ge_two_73 : 2 ≤ a 73 :=
  a_ge_two_of_hits 73 3 5 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP72]; norm_num)
    (by rw [nthP4, nthP72]; norm_num)

lemma a_ge_two_74 : 2 ≤ a 74 :=
  a_ge_two_of_hits 74 19 73 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP18, nthP73]; norm_num)
    (by rw [nthP72, nthP73]; norm_num)

lemma a_ge_two_75 : 2 ≤ a 75 :=
  a_ge_two_of_hits 75 31 59 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP30, nthP74]; norm_num)
    (by rw [nthP58, nthP74]; norm_num)

lemma a_ge_two_76 : 2 ≤ a 76 :=
  a_ge_two_of_hits 76 2 3 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP1, nthP75]; norm_num)
    (by rw [nthP2, nthP75]; norm_num)

lemma a_ge_two_77 : 2 ≤ a 77 :=
  a_ge_two_of_hits 77 7 23 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP6, nthP76]; norm_num)
    (by rw [nthP22, nthP76]; norm_num)

lemma a_ge_two_78 : 2 ≤ a 78 :=
  a_ge_two_of_hits 78 3 29 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP77]; norm_num)
    (by rw [nthP28, nthP77]; norm_num)

lemma a_ge_two_79 : 2 ≤ a 79 :=
  a_ge_two_of_hits 79 2 17 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP1, nthP78]; norm_num)
    (by rw [nthP16, nthP78]; norm_num)

lemma a_ge_two_80 : 2 ≤ a 80 :=
  a_ge_two_of_hits 80 19 31 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP18, nthP79]; norm_num)
    (by rw [nthP30, nthP79]; norm_num)

lemma a_ge_two_71_80 (n : ℕ) (h1 : 71 ≤ n) (h2 : n ≤ 80) : 2 ≤ a n := by
  interval_cases n
  · exact a_ge_two_71
  · exact a_ge_two_72
  · exact a_ge_two_73
  · exact a_ge_two_74
  · exact a_ge_two_75
  · exact a_ge_two_76
  · exact a_ge_two_77
  · exact a_ge_two_78
  · exact a_ge_two_79
  · exact a_ge_two_80

lemma a_pos_iff_of_le_70 (n : ℕ) (hn : 0 < n) (h : n ≤ 70) :
    a n > 0 ↔ ¬ n ∣ 6 := by
  if h44 : n ≤ 44 then
    exact a_pos_iff_of_le_44 n hn h44
  else
    have : 45 ≤ n := by omega
    have hge : 2 ≤ a n := a_ge_two_45_70 n this h
    have hnd : ¬ n ∣ 6 := by
      intro hd
      have : n ≤ 6 := Nat.le_of_dvd (by decide) hd
      omega
    simp [hnd]
    omega

lemma a_eq_one_iff_of_le_70 (n : ℕ) (hn : 0 < n) (h : n ≤ 70) :
    a n = 1 ↔ n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨
      n = 19 ∨ n = 21 ∨ n = 22 ∨ n = 31 ∨ n = 42 ∨ n = 44 := by
  if h44 : n ≤ 44 then
    exact a_eq_one_iff_of_le_44 n hn h44
  else
    have : 45 ≤ n := by omega
    have hge : 2 ≤ a n := a_ge_two_45_70 n this h
    constructor
    · intro ha; omega
    · intro hl
      rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        <;> omega


lemma nthP80 : Nat.nth Nat.Prime 80 = 419 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP81 : Nat.nth Nat.Prime 81 = 421 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP82 : Nat.nth Nat.Prime 82 = 431 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP83 : Nat.nth Nat.Prime 83 = 433 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP84 : Nat.nth Nat.Prime 84 = 439 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP85 : Nat.nth Nat.Prime 85 = 443 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP86 : Nat.nth Nat.Prime 86 = 449 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP87 : Nat.nth Nat.Prime 87 = 457 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP88 : Nat.nth Nat.Prime 88 = 461 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP89 : Nat.nth Nat.Prime 89 = 463 :=
  nth_of_count (by norm_num) (by decide)

lemma a_ge_two_81 : 2 ≤ a 81 :=
  a_ge_two_of_hits 81 3 7 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP80]; norm_num)
    (by rw [nthP6, nthP80]; norm_num)

lemma a_ge_two_82 : 2 ≤ a 82 :=
  a_ge_two_of_hits 82 5 23 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP4, nthP81]; norm_num)
    (by rw [nthP22, nthP81]; norm_num)

lemma a_ge_two_83 : 2 ≤ a 83 :=
  a_ge_two_of_hits 83 5 7 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP4, nthP82]; norm_num)
    (by rw [nthP6, nthP82]; norm_num)

lemma a_ge_two_84 : 2 ≤ a 84 :=
  a_ge_two_of_hits 84 3 23 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP83]; norm_num)
    (by rw [nthP22, nthP83]; norm_num)

lemma a_ge_two_85 : 2 ≤ a 85 :=
  a_ge_two_of_hits 85 7 23 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP6, nthP84]; norm_num)
    (by rw [nthP22, nthP84]; norm_num)

lemma a_ge_two_86 : 2 ≤ a 86 :=
  a_ge_two_of_hits 86 3 19 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP85]; norm_num)
    (by rw [nthP18, nthP85]; norm_num)

lemma a_ge_two_87 : 2 ≤ a 87 :=
  a_ge_two_of_hits 87 2 23 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP1, nthP86]; norm_num)
    (by rw [nthP22, nthP86]; norm_num)

lemma a_ge_two_88 : 2 ≤ a 88 :=
  a_ge_two_of_hits 88 5 41 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP4, nthP87]; norm_num)
    (by rw [nthP40, nthP87]; norm_num)

lemma a_ge_two_89 : 2 ≤ a 89 :=
  a_ge_two_of_hits 89 7 11 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP6, nthP88]; norm_num)
    (by rw [nthP10, nthP88]; norm_num)

lemma a_ge_two_90 : 2 ≤ a 90 :=
  a_ge_two_of_hits 90 19 23 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP18, nthP89]; norm_num)
    (by rw [nthP22, nthP89]; norm_num)

lemma a_ge_two_81_90 (n : ℕ) (h1 : 81 ≤ n) (h2 : n ≤ 90) : 2 ≤ a n := by
  interval_cases n
  · exact a_ge_two_81
  · exact a_ge_two_82
  · exact a_ge_two_83
  · exact a_ge_two_84
  · exact a_ge_two_85
  · exact a_ge_two_86
  · exact a_ge_two_87
  · exact a_ge_two_88
  · exact a_ge_two_89
  · exact a_ge_two_90

lemma a_pos_iff_of_le_80 (n : ℕ) (hn : 0 < n) (h : n ≤ 80) :
    a n > 0 ↔ ¬ n ∣ 6 := by
  if h70 : n ≤ 70 then
    exact a_pos_iff_of_le_70 n hn h70
  else
    have : 71 ≤ n := by omega
    have hge : 2 ≤ a n := a_ge_two_71_80 n this h
    have hnd : ¬ n ∣ 6 := by
      intro hd
      have : n ≤ 6 := Nat.le_of_dvd (by decide) hd
      omega
    simp [hnd]
    omega

lemma a_eq_one_iff_of_le_80 (n : ℕ) (hn : 0 < n) (h : n ≤ 80) :
    a n = 1 ↔ n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨
      n = 19 ∨ n = 21 ∨ n = 22 ∨ n = 31 ∨ n = 42 ∨ n = 44 := by
  if h70 : n ≤ 70 then
    exact a_eq_one_iff_of_le_70 n hn h70
  else
    have : 71 ≤ n := by omega
    have hge : 2 ≤ a n := a_ge_two_71_80 n this h
    constructor
    · intro ha; omega
    · intro hl
      rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        <;> omega


lemma nthP90 : Nat.nth Nat.Prime 90 = 467 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP91 : Nat.nth Nat.Prime 91 = 479 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP92 : Nat.nth Nat.Prime 92 = 487 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP93 : Nat.nth Nat.Prime 93 = 491 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP94 : Nat.nth Nat.Prime 94 = 499 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP95 : Nat.nth Nat.Prime 95 = 503 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP96 : Nat.nth Nat.Prime 96 = 509 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP97 : Nat.nth Nat.Prime 97 = 521 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP98 : Nat.nth Nat.Prime 98 = 523 :=
  nth_of_count (by norm_num) (by decide)

lemma nthP99 : Nat.nth Nat.Prime 99 = 541 :=
  nth_of_count (by norm_num) (by decide)

lemma a_ge_two_91 : 2 ≤ a 91 :=
  a_ge_two_of_hits 91 11 29 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP10, nthP90]; norm_num)
    (by rw [nthP28, nthP90]; norm_num)

lemma a_ge_two_92 : 2 ≤ a 92 :=
  a_ge_two_of_hits 92 3 7 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP91]; norm_num)
    (by rw [nthP6, nthP91]; norm_num)

lemma a_ge_two_93 : 2 ≤ a 93 :=
  a_ge_two_of_hits 93 11 13 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP10, nthP92]; norm_num)
    (by rw [nthP12, nthP92]; norm_num)

lemma a_ge_two_94 : 2 ≤ a 94 :=
  a_ge_two_of_hits 94 2 11 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP1, nthP93]; norm_num)
    (by rw [nthP10, nthP93]; norm_num)

lemma a_ge_two_95 : 2 ≤ a 95 :=
  a_ge_two_of_hits 95 7 31 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP6, nthP94]; norm_num)
    (by rw [nthP30, nthP94]; norm_num)

lemma a_ge_two_96 : 2 ≤ a 96 :=
  a_ge_two_of_hits 96 2 3 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP1, nthP95]; norm_num)
    (by rw [nthP2, nthP95]; norm_num)

lemma a_ge_two_97 : 2 ≤ a 97 :=
  a_ge_two_of_hits 97 7 19 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP6, nthP96]; norm_num)
    (by rw [nthP18, nthP96]; norm_num)

lemma a_ge_two_98 : 2 ≤ a 98 :=
  a_ge_two_of_hits 98 7 17 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP6, nthP97]; norm_num)
    (by rw [nthP16, nthP97]; norm_num)

lemma a_ge_two_99 : 2 ≤ a 99 :=
  a_ge_two_of_hits 99 37 71 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP36, nthP98]; norm_num)
    (by rw [nthP70, nthP98]; norm_num)

lemma a_ge_two_100 : 2 ≤ a 100 :=
  a_ge_two_of_hits 100 5 11 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP4, nthP99]; norm_num)
    (by rw [nthP10, nthP99]; norm_num)

lemma a_ge_two_91_100 (n : ℕ) (h1 : 91 ≤ n) (h2 : n ≤ 100) : 2 ≤ a n := by
  interval_cases n
  · exact a_ge_two_91
  · exact a_ge_two_92
  · exact a_ge_two_93
  · exact a_ge_two_94
  · exact a_ge_two_95
  · exact a_ge_two_96
  · exact a_ge_two_97
  · exact a_ge_two_98
  · exact a_ge_two_99
  · exact a_ge_two_100

lemma a_pos_iff_of_le_90 (n : ℕ) (hn : 0 < n) (h : n ≤ 90) :
    a n > 0 ↔ ¬ n ∣ 6 := by
  if hold : n ≤ 80 then
    exact a_pos_iff_of_le_80 n hn hold
  else
    have : 81 ≤ n := by omega
    have hge : 2 ≤ a n := a_ge_two_81_90 n this h
    have hnd : ¬ n ∣ 6 := by
      intro hd
      have : n ≤ 6 := Nat.le_of_dvd (by decide) hd
      omega
    simp [hnd]
    omega

lemma a_eq_one_iff_of_le_90 (n : ℕ) (hn : 0 < n) (h : n ≤ 90) :
    a n = 1 ↔ n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨
      n = 19 ∨ n = 21 ∨ n = 22 ∨ n = 31 ∨ n = 42 ∨ n = 44 := by
  if hold : n ≤ 80 then
    exact a_eq_one_iff_of_le_80 n hn hold
  else
    have : 81 ≤ n := by omega
    have hge : 2 ≤ a n := a_ge_two_81_90 n this h
    constructor
    · intro ha; omega
    · intro hl
      rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        <;> omega


lemma a_pos_iff_of_le_100 (n : ℕ) (hn : 0 < n) (h : n ≤ 100) :
    a n > 0 ↔ ¬ n ∣ 6 := by
  if hold : n ≤ 90 then
    exact a_pos_iff_of_le_90 n hn hold
  else
    have : 91 ≤ n := by omega
    have hge : 2 ≤ a n := a_ge_two_91_100 n this h
    have hnd : ¬ n ∣ 6 := by
      intro hd
      have : n ≤ 6 := Nat.le_of_dvd (by decide) hd
      omega
    simp [hnd]
    omega

lemma a_eq_one_iff_of_le_100 (n : ℕ) (hn : 0 < n) (h : n ≤ 100) :
    a n = 1 ↔ n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨
      n = 19 ∨ n = 21 ∨ n = 22 ∨ n = 31 ∨ n = 42 ∨ n = 44 := by
  if hold : n ≤ 90 then
    exact a_eq_one_iff_of_le_90 n hn hold
  else
    have : 91 ≤ n := by omega
    have hge : 2 ≤ a n := a_ge_two_91_100 n this h
    constructor
    · intro ha; omega
    · intro hl
      rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        <;> omega



lemma nthPrime_ge_two (i : ℕ) : 2 ≤ Nat.nth Nat.Prime i :=
  Nat.Prime.two_le (Nat.prime_nth_prime i)

lemma dvd_C_of_dvd_m {q m : ℕ} (hdiv : q ∣ m) : q ∣ q ^ 2 + m ^ 2 :=
  dvd_add (dvd_pow_self q (by decide)) (dvd_pow hdiv (by decide : 2 ≠ 0))

lemma not_prime_C_of_dvd_m {q m : ℕ} (hq : Nat.Prime q) (hdiv : q ∣ m)
    (hm : 0 < m) : ¬ Nat.Prime (q ^ 2 + m ^ 2) := by
  refine Nat.not_prime_of_dvd_of_lt (dvd_C_of_dvd_m hdiv) hq.two_le ?_
  have : 0 < m ^ 2 := Nat.pow_pos hm
  have hle : q ≤ q ^ 2 := by
    have hq2 : 2 ≤ q := hq.two_le
    exact Nat.le_self_pow (by decide : 2 ≠ 0) q
  omega

lemma count_prime_101 : Nat.count Nat.Prime 101 = 25 := by
  have h97 : Nat.count Nat.Prime 97 = 24 := by
    have := Nat.primeCounting'_nth_eq 24
    rw [nthP24] at this
    simpa [Nat.primeCounting'] using this
  have hsucc : ∀ n, Nat.count Nat.Prime (n + 1) =
      Nat.count Nat.Prime n + if Nat.Prime n then 1 else 0 :=
    fun n => Nat.count_succ (p := Nat.Prime) n
  rw [show 101 = 97 + 1 + 1 + 1 + 1 from rfl, hsucc, hsucc, hsucc, hsucc, h97]
  norm_num

lemma primes_card_lt_101 : #((Ico 1 101).filter Nat.Prime) = 25 := by
  have hrange : (range 101).filter Nat.Prime = (Ico 1 101).filter Nat.Prime := by
    ext k
    simp only [mem_filter, mem_range, mem_Ico]
    constructor
    · intro ⟨hk, hp⟩
      exact ⟨⟨Nat.Prime.one_lt hp |>.le, hk⟩, hp⟩
    · intro ⟨⟨_, hk⟩, hp⟩
      exact ⟨hk, hp⟩
  rw [← hrange, ← Nat.count_eq_card_filter_range]
  exact count_prime_101

lemma many_prime_indices {n : ℕ} (hn : 100 < n) :
    25 ≤ #((Ico 1 n).filter Nat.Prime) := by
  have hsub : (Ico 1 101).filter Nat.Prime ⊆ (Ico 1 n).filter Nat.Prime := by
    intro k hk
    simp only [mem_filter, mem_Ico] at hk ⊢
    refine ⟨⟨hk.1.1, ?_⟩, hk.2⟩
    omega
  exact primes_card_lt_101 ▸ card_mono hsub

lemma count_541 : Nat.count Nat.Prime 541 = 99 := by
  have := Nat.primeCounting'_nth_eq 99
  rw [nthP99] at this
  simpa [Nat.primeCounting'] using this

lemma count_succ_prime (n : ℕ) :
    Nat.count Nat.Prime (n + 1) =
      Nat.count Nat.Prime n + if Nat.Prime n then 1 else 0 :=
  Nat.count_succ (p := Nat.Prime) n

lemma count_542 : Nat.count Nat.Prime 542 = 100 := by
  rw [count_succ_prime, count_541]; norm_num

lemma count_543 : Nat.count Nat.Prime 543 = 100 := by
  rw [count_succ_prime, count_542]; norm_num

lemma count_544 : Nat.count Nat.Prime 544 = 100 := by
  rw [count_succ_prime, count_543]; norm_num

lemma count_545 : Nat.count Nat.Prime 545 = 100 := by
  rw [count_succ_prime, count_544]; norm_num

lemma count_546 : Nat.count Nat.Prime 546 = 100 := by
  rw [count_succ_prime, count_545]; norm_num

lemma count_547 : Nat.count Nat.Prime 547 = 100 := by
  rw [count_succ_prime, count_546]; norm_num

lemma count_548 : Nat.count Nat.Prime 548 = 101 := by
  rw [count_succ_prime, count_547]; norm_num

lemma count_549 : Nat.count Nat.Prime 549 = 101 := by
  rw [count_succ_prime, count_548]; norm_num

lemma count_550 : Nat.count Nat.Prime 550 = 101 := by
  rw [count_succ_prime, count_549]; norm_num

lemma count_551 : Nat.count Nat.Prime 551 = 101 := by
  rw [count_succ_prime, count_550]; norm_num

lemma count_552 : Nat.count Nat.Prime 552 = 101 := by
  rw [count_succ_prime, count_551]; norm_num

lemma count_553 : Nat.count Nat.Prime 553 = 101 := by
  rw [count_succ_prime, count_552]; norm_num

lemma count_554 : Nat.count Nat.Prime 554 = 101 := by
  rw [count_succ_prime, count_553]; norm_num

lemma count_555 : Nat.count Nat.Prime 555 = 101 := by
  rw [count_succ_prime, count_554]; norm_num

lemma count_556 : Nat.count Nat.Prime 556 = 101 := by
  rw [count_succ_prime, count_555]; norm_num

lemma count_557 : Nat.count Nat.Prime 557 = 101 := by
  rw [count_succ_prime, count_556]; norm_num

lemma count_558 : Nat.count Nat.Prime 558 = 102 := by
  rw [count_succ_prime, count_557]; norm_num

lemma count_559 : Nat.count Nat.Prime 559 = 102 := by
  rw [count_succ_prime, count_558]; norm_num

lemma count_560 : Nat.count Nat.Prime 560 = 102 := by
  rw [count_succ_prime, count_559]; norm_num

lemma count_561 : Nat.count Nat.Prime 561 = 102 := by
  rw [count_succ_prime, count_560]; norm_num

lemma count_562 : Nat.count Nat.Prime 562 = 102 := by
  rw [count_succ_prime, count_561]; norm_num

lemma count_563 : Nat.count Nat.Prime 563 = 102 := by
  rw [count_succ_prime, count_562]; norm_num

lemma count_564 : Nat.count Nat.Prime 564 = 103 := by
  rw [count_succ_prime, count_563]; norm_num

lemma count_565 : Nat.count Nat.Prime 565 = 103 := by
  rw [count_succ_prime, count_564]; norm_num

lemma count_566 : Nat.count Nat.Prime 566 = 103 := by
  rw [count_succ_prime, count_565]; norm_num

lemma count_567 : Nat.count Nat.Prime 567 = 103 := by
  rw [count_succ_prime, count_566]; norm_num

lemma count_568 : Nat.count Nat.Prime 568 = 103 := by
  rw [count_succ_prime, count_567]; norm_num

lemma count_569 : Nat.count Nat.Prime 569 = 103 := by
  rw [count_succ_prime, count_568]; norm_num

lemma count_570 : Nat.count Nat.Prime 570 = 104 := by
  rw [count_succ_prime, count_569]; norm_num

lemma count_571 : Nat.count Nat.Prime 571 = 104 := by
  rw [count_succ_prime, count_570]; norm_num

lemma count_572 : Nat.count Nat.Prime 572 = 105 := by
  rw [count_succ_prime, count_571]; norm_num

lemma count_573 : Nat.count Nat.Prime 573 = 105 := by
  rw [count_succ_prime, count_572]; norm_num

lemma count_574 : Nat.count Nat.Prime 574 = 105 := by
  rw [count_succ_prime, count_573]; norm_num

lemma count_575 : Nat.count Nat.Prime 575 = 105 := by
  rw [count_succ_prime, count_574]; norm_num

lemma count_576 : Nat.count Nat.Prime 576 = 105 := by
  rw [count_succ_prime, count_575]; norm_num

lemma count_577 : Nat.count Nat.Prime 577 = 105 := by
  rw [count_succ_prime, count_576]; norm_num

lemma count_578 : Nat.count Nat.Prime 578 = 106 := by
  rw [count_succ_prime, count_577]; norm_num

lemma count_579 : Nat.count Nat.Prime 579 = 106 := by
  rw [count_succ_prime, count_578]; norm_num

lemma count_580 : Nat.count Nat.Prime 580 = 106 := by
  rw [count_succ_prime, count_579]; norm_num

lemma count_581 : Nat.count Nat.Prime 581 = 106 := by
  rw [count_succ_prime, count_580]; norm_num

lemma count_582 : Nat.count Nat.Prime 582 = 106 := by
  rw [count_succ_prime, count_581]; norm_num

lemma count_583 : Nat.count Nat.Prime 583 = 106 := by
  rw [count_succ_prime, count_582]; norm_num

lemma count_584 : Nat.count Nat.Prime 584 = 106 := by
  rw [count_succ_prime, count_583]; norm_num

lemma count_585 : Nat.count Nat.Prime 585 = 106 := by
  rw [count_succ_prime, count_584]; norm_num

lemma count_586 : Nat.count Nat.Prime 586 = 106 := by
  rw [count_succ_prime, count_585]; norm_num

lemma count_587 : Nat.count Nat.Prime 587 = 106 := by
  rw [count_succ_prime, count_586]; norm_num

lemma count_588 : Nat.count Nat.Prime 588 = 107 := by
  rw [count_succ_prime, count_587]; norm_num

lemma count_589 : Nat.count Nat.Prime 589 = 107 := by
  rw [count_succ_prime, count_588]; norm_num

lemma count_590 : Nat.count Nat.Prime 590 = 107 := by
  rw [count_succ_prime, count_589]; norm_num

lemma count_591 : Nat.count Nat.Prime 591 = 107 := by
  rw [count_succ_prime, count_590]; norm_num

lemma count_592 : Nat.count Nat.Prime 592 = 107 := by
  rw [count_succ_prime, count_591]; norm_num

lemma count_593 : Nat.count Nat.Prime 593 = 107 := by
  rw [count_succ_prime, count_592]; norm_num

lemma count_594 : Nat.count Nat.Prime 594 = 108 := by
  rw [count_succ_prime, count_593]; norm_num

lemma count_595 : Nat.count Nat.Prime 595 = 108 := by
  rw [count_succ_prime, count_594]; norm_num

lemma count_596 : Nat.count Nat.Prime 596 = 108 := by
  rw [count_succ_prime, count_595]; norm_num

lemma count_597 : Nat.count Nat.Prime 597 = 108 := by
  rw [count_succ_prime, count_596]; norm_num

lemma count_598 : Nat.count Nat.Prime 598 = 108 := by
  rw [count_succ_prime, count_597]; norm_num

lemma count_599 : Nat.count Nat.Prime 599 = 108 := by
  rw [count_succ_prime, count_598]; norm_num

lemma count_600 : Nat.count Nat.Prime 600 = 109 := by
  rw [count_succ_prime, count_599]; norm_num

lemma count_601 : Nat.count Nat.Prime 601 = 109 := by
  rw [count_succ_prime, count_600]; norm_num

lemma count_602 : Nat.count Nat.Prime 602 = 110 := by
  rw [count_succ_prime, count_601]; norm_num

lemma count_603 : Nat.count Nat.Prime 603 = 110 := by
  rw [count_succ_prime, count_602]; norm_num

lemma count_604 : Nat.count Nat.Prime 604 = 110 := by
  rw [count_succ_prime, count_603]; norm_num

lemma count_605 : Nat.count Nat.Prime 605 = 110 := by
  rw [count_succ_prime, count_604]; norm_num

lemma count_606 : Nat.count Nat.Prime 606 = 110 := by
  rw [count_succ_prime, count_605]; norm_num

lemma count_607 : Nat.count Nat.Prime 607 = 110 := by
  rw [count_succ_prime, count_606]; norm_num

lemma count_608 : Nat.count Nat.Prime 608 = 111 := by
  rw [count_succ_prime, count_607]; norm_num

lemma count_609 : Nat.count Nat.Prime 609 = 111 := by
  rw [count_succ_prime, count_608]; norm_num

lemma count_610 : Nat.count Nat.Prime 610 = 111 := by
  rw [count_succ_prime, count_609]; norm_num

lemma count_611 : Nat.count Nat.Prime 611 = 111 := by
  rw [count_succ_prime, count_610]; norm_num

lemma count_612 : Nat.count Nat.Prime 612 = 111 := by
  rw [count_succ_prime, count_611]; norm_num

lemma count_613 : Nat.count Nat.Prime 613 = 111 := by
  rw [count_succ_prime, count_612]; norm_num

lemma count_614 : Nat.count Nat.Prime 614 = 112 := by
  rw [count_succ_prime, count_613]; norm_num

lemma count_615 : Nat.count Nat.Prime 615 = 112 := by
  rw [count_succ_prime, count_614]; norm_num

lemma count_616 : Nat.count Nat.Prime 616 = 112 := by
  rw [count_succ_prime, count_615]; norm_num

lemma count_617 : Nat.count Nat.Prime 617 = 112 := by
  rw [count_succ_prime, count_616]; norm_num

lemma count_618 : Nat.count Nat.Prime 618 = 113 := by
  rw [count_succ_prime, count_617]; norm_num

lemma count_619 : Nat.count Nat.Prime 619 = 113 := by
  rw [count_succ_prime, count_618]; norm_num

lemma count_620 : Nat.count Nat.Prime 620 = 114 := by
  rw [count_succ_prime, count_619]; norm_num

lemma count_621 : Nat.count Nat.Prime 621 = 114 := by
  rw [count_succ_prime, count_620]; norm_num

lemma count_622 : Nat.count Nat.Prime 622 = 114 := by
  rw [count_succ_prime, count_621]; norm_num

lemma count_623 : Nat.count Nat.Prime 623 = 114 := by
  rw [count_succ_prime, count_622]; norm_num

lemma count_624 : Nat.count Nat.Prime 624 = 114 := by
  rw [count_succ_prime, count_623]; norm_num

lemma count_625 : Nat.count Nat.Prime 625 = 114 := by
  rw [count_succ_prime, count_624]; norm_num

lemma count_626 : Nat.count Nat.Prime 626 = 114 := by
  rw [count_succ_prime, count_625]; norm_num

lemma count_627 : Nat.count Nat.Prime 627 = 114 := by
  rw [count_succ_prime, count_626]; norm_num

lemma count_628 : Nat.count Nat.Prime 628 = 114 := by
  rw [count_succ_prime, count_627]; norm_num

lemma count_629 : Nat.count Nat.Prime 629 = 114 := by
  rw [count_succ_prime, count_628]; norm_num

lemma count_630 : Nat.count Nat.Prime 630 = 114 := by
  rw [count_succ_prime, count_629]; norm_num

lemma count_631 : Nat.count Nat.Prime 631 = 114 := by
  rw [count_succ_prime, count_630]; norm_num

lemma count_632 : Nat.count Nat.Prime 632 = 115 := by
  rw [count_succ_prime, count_631]; norm_num

lemma count_633 : Nat.count Nat.Prime 633 = 115 := by
  rw [count_succ_prime, count_632]; norm_num

lemma count_634 : Nat.count Nat.Prime 634 = 115 := by
  rw [count_succ_prime, count_633]; norm_num

lemma count_635 : Nat.count Nat.Prime 635 = 115 := by
  rw [count_succ_prime, count_634]; norm_num

lemma count_636 : Nat.count Nat.Prime 636 = 115 := by
  rw [count_succ_prime, count_635]; norm_num

lemma count_637 : Nat.count Nat.Prime 637 = 115 := by
  rw [count_succ_prime, count_636]; norm_num

lemma count_638 : Nat.count Nat.Prime 638 = 115 := by
  rw [count_succ_prime, count_637]; norm_num

lemma count_639 : Nat.count Nat.Prime 639 = 115 := by
  rw [count_succ_prime, count_638]; norm_num

lemma count_640 : Nat.count Nat.Prime 640 = 115 := by
  rw [count_succ_prime, count_639]; norm_num

lemma count_641 : Nat.count Nat.Prime 641 = 115 := by
  rw [count_succ_prime, count_640]; norm_num

lemma count_642 : Nat.count Nat.Prime 642 = 116 := by
  rw [count_succ_prime, count_641]; norm_num

lemma count_643 : Nat.count Nat.Prime 643 = 116 := by
  rw [count_succ_prime, count_642]; norm_num

lemma count_644 : Nat.count Nat.Prime 644 = 117 := by
  rw [count_succ_prime, count_643]; norm_num

lemma count_645 : Nat.count Nat.Prime 645 = 117 := by
  rw [count_succ_prime, count_644]; norm_num

lemma count_646 : Nat.count Nat.Prime 646 = 117 := by
  rw [count_succ_prime, count_645]; norm_num

lemma count_647 : Nat.count Nat.Prime 647 = 117 := by
  rw [count_succ_prime, count_646]; norm_num

lemma count_648 : Nat.count Nat.Prime 648 = 118 := by
  rw [count_succ_prime, count_647]; norm_num

lemma count_649 : Nat.count Nat.Prime 649 = 118 := by
  rw [count_succ_prime, count_648]; norm_num

lemma count_650 : Nat.count Nat.Prime 650 = 118 := by
  rw [count_succ_prime, count_649]; norm_num

lemma count_651 : Nat.count Nat.Prime 651 = 118 := by
  rw [count_succ_prime, count_650]; norm_num

lemma count_652 : Nat.count Nat.Prime 652 = 118 := by
  rw [count_succ_prime, count_651]; norm_num

lemma count_653 : Nat.count Nat.Prime 653 = 118 := by
  rw [count_succ_prime, count_652]; norm_num

lemma count_654 : Nat.count Nat.Prime 654 = 119 := by
  rw [count_succ_prime, count_653]; norm_num

lemma count_655 : Nat.count Nat.Prime 655 = 119 := by
  rw [count_succ_prime, count_654]; norm_num

lemma count_656 : Nat.count Nat.Prime 656 = 119 := by
  rw [count_succ_prime, count_655]; norm_num

lemma count_657 : Nat.count Nat.Prime 657 = 119 := by
  rw [count_succ_prime, count_656]; norm_num

lemma count_658 : Nat.count Nat.Prime 658 = 119 := by
  rw [count_succ_prime, count_657]; norm_num

lemma count_659 : Nat.count Nat.Prime 659 = 119 := by
  rw [count_succ_prime, count_658]; norm_num

lemma count_660 : Nat.count Nat.Prime 660 = 120 := by
  rw [count_succ_prime, count_659]; norm_num

lemma count_661 : Nat.count Nat.Prime 661 = 120 := by
  rw [count_succ_prime, count_660]; norm_num

lemma count_662 : Nat.count Nat.Prime 662 = 121 := by
  rw [count_succ_prime, count_661]; norm_num

lemma count_663 : Nat.count Nat.Prime 663 = 121 := by
  rw [count_succ_prime, count_662]; norm_num

lemma count_664 : Nat.count Nat.Prime 664 = 121 := by
  rw [count_succ_prime, count_663]; norm_num

lemma count_665 : Nat.count Nat.Prime 665 = 121 := by
  rw [count_succ_prime, count_664]; norm_num

lemma count_666 : Nat.count Nat.Prime 666 = 121 := by
  rw [count_succ_prime, count_665]; norm_num

lemma count_667 : Nat.count Nat.Prime 667 = 121 := by
  rw [count_succ_prime, count_666]; norm_num

lemma count_668 : Nat.count Nat.Prime 668 = 121 := by
  rw [count_succ_prime, count_667]; norm_num

lemma count_669 : Nat.count Nat.Prime 669 = 121 := by
  rw [count_succ_prime, count_668]; norm_num

lemma count_670 : Nat.count Nat.Prime 670 = 121 := by
  rw [count_succ_prime, count_669]; norm_num

lemma count_671 : Nat.count Nat.Prime 671 = 121 := by
  rw [count_succ_prime, count_670]; norm_num

lemma count_672 : Nat.count Nat.Prime 672 = 121 := by
  rw [count_succ_prime, count_671]; norm_num

lemma count_673 : Nat.count Nat.Prime 673 = 121 := by
  rw [count_succ_prime, count_672]; norm_num

lemma count_674 : Nat.count Nat.Prime 674 = 122 := by
  rw [count_succ_prime, count_673]; norm_num

lemma count_675 : Nat.count Nat.Prime 675 = 122 := by
  rw [count_succ_prime, count_674]; norm_num

lemma count_676 : Nat.count Nat.Prime 676 = 122 := by
  rw [count_succ_prime, count_675]; norm_num

lemma count_677 : Nat.count Nat.Prime 677 = 122 := by
  rw [count_succ_prime, count_676]; norm_num

lemma count_678 : Nat.count Nat.Prime 678 = 123 := by
  rw [count_succ_prime, count_677]; norm_num

lemma count_679 : Nat.count Nat.Prime 679 = 123 := by
  rw [count_succ_prime, count_678]; norm_num

lemma count_680 : Nat.count Nat.Prime 680 = 123 := by
  rw [count_succ_prime, count_679]; norm_num

lemma count_681 : Nat.count Nat.Prime 681 = 123 := by
  rw [count_succ_prime, count_680]; norm_num

lemma count_682 : Nat.count Nat.Prime 682 = 123 := by
  rw [count_succ_prime, count_681]; norm_num

lemma count_683 : Nat.count Nat.Prime 683 = 123 := by
  rw [count_succ_prime, count_682]; norm_num

lemma count_684 : Nat.count Nat.Prime 684 = 124 := by
  rw [count_succ_prime, count_683]; norm_num

lemma count_685 : Nat.count Nat.Prime 685 = 124 := by
  rw [count_succ_prime, count_684]; norm_num

lemma count_686 : Nat.count Nat.Prime 686 = 124 := by
  rw [count_succ_prime, count_685]; norm_num

lemma count_687 : Nat.count Nat.Prime 687 = 124 := by
  rw [count_succ_prime, count_686]; norm_num

lemma count_688 : Nat.count Nat.Prime 688 = 124 := by
  rw [count_succ_prime, count_687]; norm_num

lemma count_689 : Nat.count Nat.Prime 689 = 124 := by
  rw [count_succ_prime, count_688]; norm_num

lemma count_690 : Nat.count Nat.Prime 690 = 124 := by
  rw [count_succ_prime, count_689]; norm_num

lemma count_691 : Nat.count Nat.Prime 691 = 124 := by
  rw [count_succ_prime, count_690]; norm_num

lemma count_692 : Nat.count Nat.Prime 692 = 125 := by
  rw [count_succ_prime, count_691]; norm_num

lemma count_693 : Nat.count Nat.Prime 693 = 125 := by
  rw [count_succ_prime, count_692]; norm_num

lemma count_694 : Nat.count Nat.Prime 694 = 125 := by
  rw [count_succ_prime, count_693]; norm_num

lemma count_695 : Nat.count Nat.Prime 695 = 125 := by
  rw [count_succ_prime, count_694]; norm_num

lemma count_696 : Nat.count Nat.Prime 696 = 125 := by
  rw [count_succ_prime, count_695]; norm_num

lemma count_697 : Nat.count Nat.Prime 697 = 125 := by
  rw [count_succ_prime, count_696]; norm_num

lemma count_698 : Nat.count Nat.Prime 698 = 125 := by
  rw [count_succ_prime, count_697]; norm_num

lemma count_699 : Nat.count Nat.Prime 699 = 125 := by
  rw [count_succ_prime, count_698]; norm_num

lemma count_700 : Nat.count Nat.Prime 700 = 125 := by
  rw [count_succ_prime, count_699]; norm_num

lemma count_701 : Nat.count Nat.Prime 701 = 125 := by
  rw [count_succ_prime, count_700]; norm_num

lemma count_702 : Nat.count Nat.Prime 702 = 126 := by
  rw [count_succ_prime, count_701]; norm_num

lemma count_703 : Nat.count Nat.Prime 703 = 126 := by
  rw [count_succ_prime, count_702]; norm_num

lemma count_704 : Nat.count Nat.Prime 704 = 126 := by
  rw [count_succ_prime, count_703]; norm_num

lemma count_705 : Nat.count Nat.Prime 705 = 126 := by
  rw [count_succ_prime, count_704]; norm_num

lemma count_706 : Nat.count Nat.Prime 706 = 126 := by
  rw [count_succ_prime, count_705]; norm_num

lemma count_707 : Nat.count Nat.Prime 707 = 126 := by
  rw [count_succ_prime, count_706]; norm_num

lemma count_708 : Nat.count Nat.Prime 708 = 126 := by
  rw [count_succ_prime, count_707]; norm_num

lemma count_709 : Nat.count Nat.Prime 709 = 126 := by
  rw [count_succ_prime, count_708]; norm_num

lemma count_710 : Nat.count Nat.Prime 710 = 127 := by
  rw [count_succ_prime, count_709]; norm_num

lemma count_711 : Nat.count Nat.Prime 711 = 127 := by
  rw [count_succ_prime, count_710]; norm_num

lemma count_712 : Nat.count Nat.Prime 712 = 127 := by
  rw [count_succ_prime, count_711]; norm_num

lemma count_713 : Nat.count Nat.Prime 713 = 127 := by
  rw [count_succ_prime, count_712]; norm_num

lemma count_714 : Nat.count Nat.Prime 714 = 127 := by
  rw [count_succ_prime, count_713]; norm_num

lemma count_715 : Nat.count Nat.Prime 715 = 127 := by
  rw [count_succ_prime, count_714]; norm_num

lemma count_716 : Nat.count Nat.Prime 716 = 127 := by
  rw [count_succ_prime, count_715]; norm_num

lemma count_717 : Nat.count Nat.Prime 717 = 127 := by
  rw [count_succ_prime, count_716]; norm_num

lemma count_718 : Nat.count Nat.Prime 718 = 127 := by
  rw [count_succ_prime, count_717]; norm_num

lemma count_719 : Nat.count Nat.Prime 719 = 127 := by
  rw [count_succ_prime, count_718]; norm_num

lemma count_720 : Nat.count Nat.Prime 720 = 128 := by
  rw [count_succ_prime, count_719]; norm_num

lemma count_721 : Nat.count Nat.Prime 721 = 128 := by
  rw [count_succ_prime, count_720]; norm_num

lemma count_722 : Nat.count Nat.Prime 722 = 128 := by
  rw [count_succ_prime, count_721]; norm_num

lemma count_723 : Nat.count Nat.Prime 723 = 128 := by
  rw [count_succ_prime, count_722]; norm_num

lemma count_724 : Nat.count Nat.Prime 724 = 128 := by
  rw [count_succ_prime, count_723]; norm_num

lemma count_725 : Nat.count Nat.Prime 725 = 128 := by
  rw [count_succ_prime, count_724]; norm_num

lemma count_726 : Nat.count Nat.Prime 726 = 128 := by
  rw [count_succ_prime, count_725]; norm_num

lemma count_727 : Nat.count Nat.Prime 727 = 128 := by
  rw [count_succ_prime, count_726]; norm_num

lemma count_728 : Nat.count Nat.Prime 728 = 129 := by
  rw [count_succ_prime, count_727]; norm_num

lemma count_729 : Nat.count Nat.Prime 729 = 129 := by
  rw [count_succ_prime, count_728]; norm_num

lemma count_730 : Nat.count Nat.Prime 730 = 129 := by
  rw [count_succ_prime, count_729]; norm_num

lemma count_731 : Nat.count Nat.Prime 731 = 129 := by
  rw [count_succ_prime, count_730]; norm_num

lemma count_732 : Nat.count Nat.Prime 732 = 129 := by
  rw [count_succ_prime, count_731]; norm_num

lemma count_733 : Nat.count Nat.Prime 733 = 129 := by
  rw [count_succ_prime, count_732]; norm_num

lemma count_734 : Nat.count Nat.Prime 734 = 130 := by
  rw [count_succ_prime, count_733]; norm_num

lemma count_735 : Nat.count Nat.Prime 735 = 130 := by
  rw [count_succ_prime, count_734]; norm_num

lemma count_736 : Nat.count Nat.Prime 736 = 130 := by
  rw [count_succ_prime, count_735]; norm_num

lemma count_737 : Nat.count Nat.Prime 737 = 130 := by
  rw [count_succ_prime, count_736]; norm_num

lemma count_738 : Nat.count Nat.Prime 738 = 130 := by
  rw [count_succ_prime, count_737]; norm_num

lemma count_739 : Nat.count Nat.Prime 739 = 130 := by
  rw [count_succ_prime, count_738]; norm_num

lemma count_740 : Nat.count Nat.Prime 740 = 131 := by
  rw [count_succ_prime, count_739]; norm_num

lemma count_741 : Nat.count Nat.Prime 741 = 131 := by
  rw [count_succ_prime, count_740]; norm_num

lemma count_742 : Nat.count Nat.Prime 742 = 131 := by
  rw [count_succ_prime, count_741]; norm_num

lemma count_743 : Nat.count Nat.Prime 743 = 131 := by
  rw [count_succ_prime, count_742]; norm_num

lemma count_744 : Nat.count Nat.Prime 744 = 132 := by
  rw [count_succ_prime, count_743]; norm_num

lemma count_745 : Nat.count Nat.Prime 745 = 132 := by
  rw [count_succ_prime, count_744]; norm_num

lemma count_746 : Nat.count Nat.Prime 746 = 132 := by
  rw [count_succ_prime, count_745]; norm_num

lemma count_747 : Nat.count Nat.Prime 747 = 132 := by
  rw [count_succ_prime, count_746]; norm_num

lemma count_748 : Nat.count Nat.Prime 748 = 132 := by
  rw [count_succ_prime, count_747]; norm_num

lemma count_749 : Nat.count Nat.Prime 749 = 132 := by
  rw [count_succ_prime, count_748]; norm_num

lemma count_750 : Nat.count Nat.Prime 750 = 132 := by
  rw [count_succ_prime, count_749]; norm_num

lemma count_751 : Nat.count Nat.Prime 751 = 132 := by
  rw [count_succ_prime, count_750]; norm_num

lemma count_752 : Nat.count Nat.Prime 752 = 133 := by
  rw [count_succ_prime, count_751]; norm_num

lemma count_753 : Nat.count Nat.Prime 753 = 133 := by
  rw [count_succ_prime, count_752]; norm_num

lemma count_754 : Nat.count Nat.Prime 754 = 133 := by
  rw [count_succ_prime, count_753]; norm_num

lemma count_755 : Nat.count Nat.Prime 755 = 133 := by
  rw [count_succ_prime, count_754]; norm_num

lemma count_756 : Nat.count Nat.Prime 756 = 133 := by
  rw [count_succ_prime, count_755]; norm_num

lemma count_757 : Nat.count Nat.Prime 757 = 133 := by
  rw [count_succ_prime, count_756]; norm_num

lemma count_758 : Nat.count Nat.Prime 758 = 134 := by
  rw [count_succ_prime, count_757]; norm_num

lemma count_759 : Nat.count Nat.Prime 759 = 134 := by
  rw [count_succ_prime, count_758]; norm_num

lemma count_760 : Nat.count Nat.Prime 760 = 134 := by
  rw [count_succ_prime, count_759]; norm_num

lemma count_761 : Nat.count Nat.Prime 761 = 134 := by
  rw [count_succ_prime, count_760]; norm_num

lemma count_762 : Nat.count Nat.Prime 762 = 135 := by
  rw [count_succ_prime, count_761]; norm_num

lemma count_763 : Nat.count Nat.Prime 763 = 135 := by
  rw [count_succ_prime, count_762]; norm_num

lemma count_764 : Nat.count Nat.Prime 764 = 135 := by
  rw [count_succ_prime, count_763]; norm_num

lemma count_765 : Nat.count Nat.Prime 765 = 135 := by
  rw [count_succ_prime, count_764]; norm_num

lemma count_766 : Nat.count Nat.Prime 766 = 135 := by
  rw [count_succ_prime, count_765]; norm_num

lemma count_767 : Nat.count Nat.Prime 767 = 135 := by
  rw [count_succ_prime, count_766]; norm_num

lemma count_768 : Nat.count Nat.Prime 768 = 135 := by
  rw [count_succ_prime, count_767]; norm_num

lemma count_769 : Nat.count Nat.Prime 769 = 135 := by
  rw [count_succ_prime, count_768]; norm_num

lemma count_770 : Nat.count Nat.Prime 770 = 136 := by
  rw [count_succ_prime, count_769]; norm_num

lemma count_771 : Nat.count Nat.Prime 771 = 136 := by
  rw [count_succ_prime, count_770]; norm_num

lemma count_772 : Nat.count Nat.Prime 772 = 136 := by
  rw [count_succ_prime, count_771]; norm_num

lemma count_773 : Nat.count Nat.Prime 773 = 136 := by
  rw [count_succ_prime, count_772]; norm_num

lemma count_774 : Nat.count Nat.Prime 774 = 137 := by
  rw [count_succ_prime, count_773]; norm_num

lemma count_775 : Nat.count Nat.Prime 775 = 137 := by
  rw [count_succ_prime, count_774]; norm_num

lemma count_776 : Nat.count Nat.Prime 776 = 137 := by
  rw [count_succ_prime, count_775]; norm_num

lemma count_777 : Nat.count Nat.Prime 777 = 137 := by
  rw [count_succ_prime, count_776]; norm_num

lemma count_778 : Nat.count Nat.Prime 778 = 137 := by
  rw [count_succ_prime, count_777]; norm_num

lemma count_779 : Nat.count Nat.Prime 779 = 137 := by
  rw [count_succ_prime, count_778]; norm_num

lemma count_780 : Nat.count Nat.Prime 780 = 137 := by
  rw [count_succ_prime, count_779]; norm_num

lemma count_781 : Nat.count Nat.Prime 781 = 137 := by
  rw [count_succ_prime, count_780]; norm_num

lemma count_782 : Nat.count Nat.Prime 782 = 137 := by
  rw [count_succ_prime, count_781]; norm_num

lemma count_783 : Nat.count Nat.Prime 783 = 137 := by
  rw [count_succ_prime, count_782]; norm_num

lemma count_784 : Nat.count Nat.Prime 784 = 137 := by
  rw [count_succ_prime, count_783]; norm_num

lemma count_785 : Nat.count Nat.Prime 785 = 137 := by
  rw [count_succ_prime, count_784]; norm_num

lemma count_786 : Nat.count Nat.Prime 786 = 137 := by
  rw [count_succ_prime, count_785]; norm_num

lemma count_787 : Nat.count Nat.Prime 787 = 137 := by
  rw [count_succ_prime, count_786]; norm_num

lemma count_788 : Nat.count Nat.Prime 788 = 138 := by
  rw [count_succ_prime, count_787]; norm_num

lemma count_789 : Nat.count Nat.Prime 789 = 138 := by
  rw [count_succ_prime, count_788]; norm_num

lemma count_790 : Nat.count Nat.Prime 790 = 138 := by
  rw [count_succ_prime, count_789]; norm_num

lemma count_791 : Nat.count Nat.Prime 791 = 138 := by
  rw [count_succ_prime, count_790]; norm_num

lemma count_792 : Nat.count Nat.Prime 792 = 138 := by
  rw [count_succ_prime, count_791]; norm_num

lemma count_793 : Nat.count Nat.Prime 793 = 138 := by
  rw [count_succ_prime, count_792]; norm_num

lemma count_794 : Nat.count Nat.Prime 794 = 138 := by
  rw [count_succ_prime, count_793]; norm_num

lemma count_795 : Nat.count Nat.Prime 795 = 138 := by
  rw [count_succ_prime, count_794]; norm_num

lemma count_796 : Nat.count Nat.Prime 796 = 138 := by
  rw [count_succ_prime, count_795]; norm_num

lemma count_797 : Nat.count Nat.Prime 797 = 138 := by
  rw [count_succ_prime, count_796]; norm_num

lemma count_798 : Nat.count Nat.Prime 798 = 139 := by
  rw [count_succ_prime, count_797]; norm_num

lemma count_799 : Nat.count Nat.Prime 799 = 139 := by
  rw [count_succ_prime, count_798]; norm_num

lemma count_800 : Nat.count Nat.Prime 800 = 139 := by
  rw [count_succ_prime, count_799]; norm_num

lemma count_801 : Nat.count Nat.Prime 801 = 139 := by
  rw [count_succ_prime, count_800]; norm_num

lemma count_802 : Nat.count Nat.Prime 802 = 139 := by
  rw [count_succ_prime, count_801]; norm_num

lemma count_803 : Nat.count Nat.Prime 803 = 139 := by
  rw [count_succ_prime, count_802]; norm_num

lemma count_804 : Nat.count Nat.Prime 804 = 139 := by
  rw [count_succ_prime, count_803]; norm_num

lemma count_805 : Nat.count Nat.Prime 805 = 139 := by
  rw [count_succ_prime, count_804]; norm_num

lemma count_806 : Nat.count Nat.Prime 806 = 139 := by
  rw [count_succ_prime, count_805]; norm_num

lemma count_807 : Nat.count Nat.Prime 807 = 139 := by
  rw [count_succ_prime, count_806]; norm_num

lemma count_808 : Nat.count Nat.Prime 808 = 139 := by
  rw [count_succ_prime, count_807]; norm_num

lemma count_809 : Nat.count Nat.Prime 809 = 139 := by
  rw [count_succ_prime, count_808]; norm_num

lemma count_810 : Nat.count Nat.Prime 810 = 140 := by
  rw [count_succ_prime, count_809]; norm_num

lemma count_811 : Nat.count Nat.Prime 811 = 140 := by
  rw [count_succ_prime, count_810]; norm_num

lemma count_812 : Nat.count Nat.Prime 812 = 141 := by
  rw [count_succ_prime, count_811]; norm_num

lemma count_813 : Nat.count Nat.Prime 813 = 141 := by
  rw [count_succ_prime, count_812]; norm_num

lemma count_814 : Nat.count Nat.Prime 814 = 141 := by
  rw [count_succ_prime, count_813]; norm_num

lemma count_815 : Nat.count Nat.Prime 815 = 141 := by
  rw [count_succ_prime, count_814]; norm_num

lemma count_816 : Nat.count Nat.Prime 816 = 141 := by
  rw [count_succ_prime, count_815]; norm_num

lemma count_817 : Nat.count Nat.Prime 817 = 141 := by
  rw [count_succ_prime, count_816]; norm_num

lemma count_818 : Nat.count Nat.Prime 818 = 141 := by
  rw [count_succ_prime, count_817]; norm_num

lemma count_819 : Nat.count Nat.Prime 819 = 141 := by
  rw [count_succ_prime, count_818]; norm_num

lemma count_820 : Nat.count Nat.Prime 820 = 141 := by
  rw [count_succ_prime, count_819]; norm_num

lemma count_821 : Nat.count Nat.Prime 821 = 141 := by
  rw [count_succ_prime, count_820]; norm_num

lemma count_822 : Nat.count Nat.Prime 822 = 142 := by
  rw [count_succ_prime, count_821]; norm_num

lemma count_823 : Nat.count Nat.Prime 823 = 142 := by
  rw [count_succ_prime, count_822]; norm_num

lemma count_824 : Nat.count Nat.Prime 824 = 143 := by
  rw [count_succ_prime, count_823]; norm_num

lemma count_825 : Nat.count Nat.Prime 825 = 143 := by
  rw [count_succ_prime, count_824]; norm_num

lemma count_826 : Nat.count Nat.Prime 826 = 143 := by
  rw [count_succ_prime, count_825]; norm_num

lemma count_827 : Nat.count Nat.Prime 827 = 143 := by
  rw [count_succ_prime, count_826]; norm_num

lemma count_828 : Nat.count Nat.Prime 828 = 144 := by
  rw [count_succ_prime, count_827]; norm_num

lemma count_829 : Nat.count Nat.Prime 829 = 144 := by
  rw [count_succ_prime, count_828]; norm_num

lemma count_830 : Nat.count Nat.Prime 830 = 145 := by
  rw [count_succ_prime, count_829]; norm_num

lemma count_831 : Nat.count Nat.Prime 831 = 145 := by
  rw [count_succ_prime, count_830]; norm_num

lemma count_832 : Nat.count Nat.Prime 832 = 145 := by
  rw [count_succ_prime, count_831]; norm_num

lemma count_833 : Nat.count Nat.Prime 833 = 145 := by
  rw [count_succ_prime, count_832]; norm_num

lemma count_834 : Nat.count Nat.Prime 834 = 145 := by
  rw [count_succ_prime, count_833]; norm_num

lemma count_835 : Nat.count Nat.Prime 835 = 145 := by
  rw [count_succ_prime, count_834]; norm_num

lemma count_836 : Nat.count Nat.Prime 836 = 145 := by
  rw [count_succ_prime, count_835]; norm_num

lemma count_837 : Nat.count Nat.Prime 837 = 145 := by
  rw [count_succ_prime, count_836]; norm_num

lemma count_838 : Nat.count Nat.Prime 838 = 145 := by
  rw [count_succ_prime, count_837]; norm_num

lemma count_839 : Nat.count Nat.Prime 839 = 145 := by
  rw [count_succ_prime, count_838]; norm_num

lemma count_840 : Nat.count Nat.Prime 840 = 146 := by
  rw [count_succ_prime, count_839]; norm_num

lemma count_841 : Nat.count Nat.Prime 841 = 146 := by
  rw [count_succ_prime, count_840]; norm_num

lemma count_842 : Nat.count Nat.Prime 842 = 146 := by
  rw [count_succ_prime, count_841]; norm_num

lemma count_843 : Nat.count Nat.Prime 843 = 146 := by
  rw [count_succ_prime, count_842]; norm_num

lemma count_844 : Nat.count Nat.Prime 844 = 146 := by
  rw [count_succ_prime, count_843]; norm_num

lemma count_845 : Nat.count Nat.Prime 845 = 146 := by
  rw [count_succ_prime, count_844]; norm_num

lemma count_846 : Nat.count Nat.Prime 846 = 146 := by
  rw [count_succ_prime, count_845]; norm_num

lemma count_847 : Nat.count Nat.Prime 847 = 146 := by
  rw [count_succ_prime, count_846]; norm_num

lemma count_848 : Nat.count Nat.Prime 848 = 146 := by
  rw [count_succ_prime, count_847]; norm_num

lemma count_849 : Nat.count Nat.Prime 849 = 146 := by
  rw [count_succ_prime, count_848]; norm_num

lemma count_850 : Nat.count Nat.Prime 850 = 146 := by
  rw [count_succ_prime, count_849]; norm_num

lemma count_851 : Nat.count Nat.Prime 851 = 146 := by
  rw [count_succ_prime, count_850]; norm_num

lemma count_852 : Nat.count Nat.Prime 852 = 146 := by
  rw [count_succ_prime, count_851]; norm_num

lemma count_853 : Nat.count Nat.Prime 853 = 146 := by
  rw [count_succ_prime, count_852]; norm_num

lemma count_854 : Nat.count Nat.Prime 854 = 147 := by
  rw [count_succ_prime, count_853]; norm_num

lemma count_855 : Nat.count Nat.Prime 855 = 147 := by
  rw [count_succ_prime, count_854]; norm_num

lemma count_856 : Nat.count Nat.Prime 856 = 147 := by
  rw [count_succ_prime, count_855]; norm_num

lemma count_857 : Nat.count Nat.Prime 857 = 147 := by
  rw [count_succ_prime, count_856]; norm_num

lemma count_858 : Nat.count Nat.Prime 858 = 148 := by
  rw [count_succ_prime, count_857]; norm_num

lemma count_859 : Nat.count Nat.Prime 859 = 148 := by
  rw [count_succ_prime, count_858]; norm_num

lemma count_860 : Nat.count Nat.Prime 860 = 149 := by
  rw [count_succ_prime, count_859]; norm_num

lemma count_861 : Nat.count Nat.Prime 861 = 149 := by
  rw [count_succ_prime, count_860]; norm_num

lemma count_862 : Nat.count Nat.Prime 862 = 149 := by
  rw [count_succ_prime, count_861]; norm_num

lemma count_863 : Nat.count Nat.Prime 863 = 149 := by
  rw [count_succ_prime, count_862]; norm_num

lemma count_864 : Nat.count Nat.Prime 864 = 150 := by
  rw [count_succ_prime, count_863]; norm_num

lemma count_865 : Nat.count Nat.Prime 865 = 150 := by
  rw [count_succ_prime, count_864]; norm_num

lemma count_866 : Nat.count Nat.Prime 866 = 150 := by
  rw [count_succ_prime, count_865]; norm_num

lemma count_867 : Nat.count Nat.Prime 867 = 150 := by
  rw [count_succ_prime, count_866]; norm_num

lemma count_868 : Nat.count Nat.Prime 868 = 150 := by
  rw [count_succ_prime, count_867]; norm_num

lemma count_869 : Nat.count Nat.Prime 869 = 150 := by
  rw [count_succ_prime, count_868]; norm_num

lemma count_870 : Nat.count Nat.Prime 870 = 150 := by
  rw [count_succ_prime, count_869]; norm_num

lemma count_871 : Nat.count Nat.Prime 871 = 150 := by
  rw [count_succ_prime, count_870]; norm_num

lemma count_872 : Nat.count Nat.Prime 872 = 150 := by
  rw [count_succ_prime, count_871]; norm_num

lemma count_873 : Nat.count Nat.Prime 873 = 150 := by
  rw [count_succ_prime, count_872]; norm_num

lemma count_874 : Nat.count Nat.Prime 874 = 150 := by
  rw [count_succ_prime, count_873]; norm_num

lemma count_875 : Nat.count Nat.Prime 875 = 150 := by
  rw [count_succ_prime, count_874]; norm_num

lemma count_876 : Nat.count Nat.Prime 876 = 150 := by
  rw [count_succ_prime, count_875]; norm_num

lemma count_877 : Nat.count Nat.Prime 877 = 150 := by
  rw [count_succ_prime, count_876]; norm_num

lemma count_878 : Nat.count Nat.Prime 878 = 151 := by
  rw [count_succ_prime, count_877]; norm_num

lemma count_879 : Nat.count Nat.Prime 879 = 151 := by
  rw [count_succ_prime, count_878]; norm_num

lemma count_880 : Nat.count Nat.Prime 880 = 151 := by
  rw [count_succ_prime, count_879]; norm_num

lemma count_881 : Nat.count Nat.Prime 881 = 151 := by
  rw [count_succ_prime, count_880]; norm_num

lemma count_882 : Nat.count Nat.Prime 882 = 152 := by
  rw [count_succ_prime, count_881]; norm_num

lemma count_883 : Nat.count Nat.Prime 883 = 152 := by
  rw [count_succ_prime, count_882]; norm_num

lemma count_884 : Nat.count Nat.Prime 884 = 153 := by
  rw [count_succ_prime, count_883]; norm_num

lemma count_885 : Nat.count Nat.Prime 885 = 153 := by
  rw [count_succ_prime, count_884]; norm_num

lemma count_886 : Nat.count Nat.Prime 886 = 153 := by
  rw [count_succ_prime, count_885]; norm_num

lemma count_887 : Nat.count Nat.Prime 887 = 153 := by
  rw [count_succ_prime, count_886]; norm_num

lemma nthP100 : Nat.nth Nat.Prime 100 = 547 :=
  nth_of_count (by norm_num) count_547

lemma nthP101 : Nat.nth Nat.Prime 101 = 557 :=
  nth_of_count (by norm_num) count_557

lemma nthP102 : Nat.nth Nat.Prime 102 = 563 :=
  nth_of_count (by norm_num) count_563

lemma nthP103 : Nat.nth Nat.Prime 103 = 569 :=
  nth_of_count (by norm_num) count_569

lemma nthP104 : Nat.nth Nat.Prime 104 = 571 :=
  nth_of_count (by norm_num) count_571

lemma nthP105 : Nat.nth Nat.Prime 105 = 577 :=
  nth_of_count (by norm_num) count_577

lemma nthP106 : Nat.nth Nat.Prime 106 = 587 :=
  nth_of_count (by norm_num) count_587

lemma nthP107 : Nat.nth Nat.Prime 107 = 593 :=
  nth_of_count (by norm_num) count_593

lemma nthP108 : Nat.nth Nat.Prime 108 = 599 :=
  nth_of_count (by norm_num) count_599

lemma nthP109 : Nat.nth Nat.Prime 109 = 601 :=
  nth_of_count (by norm_num) count_601

lemma nthP110 : Nat.nth Nat.Prime 110 = 607 :=
  nth_of_count (by norm_num) count_607

lemma nthP111 : Nat.nth Nat.Prime 111 = 613 :=
  nth_of_count (by norm_num) count_613

lemma nthP112 : Nat.nth Nat.Prime 112 = 617 :=
  nth_of_count (by norm_num) count_617

lemma nthP113 : Nat.nth Nat.Prime 113 = 619 :=
  nth_of_count (by norm_num) count_619

lemma nthP114 : Nat.nth Nat.Prime 114 = 631 :=
  nth_of_count (by norm_num) count_631

lemma nthP115 : Nat.nth Nat.Prime 115 = 641 :=
  nth_of_count (by norm_num) count_641

lemma nthP116 : Nat.nth Nat.Prime 116 = 643 :=
  nth_of_count (by norm_num) count_643

lemma nthP117 : Nat.nth Nat.Prime 117 = 647 :=
  nth_of_count (by norm_num) count_647

lemma nthP118 : Nat.nth Nat.Prime 118 = 653 :=
  nth_of_count (by norm_num) count_653

lemma nthP119 : Nat.nth Nat.Prime 119 = 659 :=
  nth_of_count (by norm_num) count_659

lemma nthP120 : Nat.nth Nat.Prime 120 = 661 :=
  nth_of_count (by norm_num) count_661

lemma nthP121 : Nat.nth Nat.Prime 121 = 673 :=
  nth_of_count (by norm_num) count_673

lemma nthP122 : Nat.nth Nat.Prime 122 = 677 :=
  nth_of_count (by norm_num) count_677

lemma nthP123 : Nat.nth Nat.Prime 123 = 683 :=
  nth_of_count (by norm_num) count_683

lemma nthP124 : Nat.nth Nat.Prime 124 = 691 :=
  nth_of_count (by norm_num) count_691

lemma nthP125 : Nat.nth Nat.Prime 125 = 701 :=
  nth_of_count (by norm_num) count_701

lemma nthP126 : Nat.nth Nat.Prime 126 = 709 :=
  nth_of_count (by norm_num) count_709

lemma nthP127 : Nat.nth Nat.Prime 127 = 719 :=
  nth_of_count (by norm_num) count_719

lemma nthP128 : Nat.nth Nat.Prime 128 = 727 :=
  nth_of_count (by norm_num) count_727

lemma nthP129 : Nat.nth Nat.Prime 129 = 733 :=
  nth_of_count (by norm_num) count_733

lemma nthP130 : Nat.nth Nat.Prime 130 = 739 :=
  nth_of_count (by norm_num) count_739

lemma nthP131 : Nat.nth Nat.Prime 131 = 743 :=
  nth_of_count (by norm_num) count_743

lemma nthP132 : Nat.nth Nat.Prime 132 = 751 :=
  nth_of_count (by norm_num) count_751

lemma nthP133 : Nat.nth Nat.Prime 133 = 757 :=
  nth_of_count (by norm_num) count_757

lemma nthP134 : Nat.nth Nat.Prime 134 = 761 :=
  nth_of_count (by norm_num) count_761

lemma nthP135 : Nat.nth Nat.Prime 135 = 769 :=
  nth_of_count (by norm_num) count_769

lemma nthP136 : Nat.nth Nat.Prime 136 = 773 :=
  nth_of_count (by norm_num) count_773

lemma nthP137 : Nat.nth Nat.Prime 137 = 787 :=
  nth_of_count (by norm_num) count_787

lemma nthP138 : Nat.nth Nat.Prime 138 = 797 :=
  nth_of_count (by norm_num) count_797

lemma nthP139 : Nat.nth Nat.Prime 139 = 809 :=
  nth_of_count (by norm_num) count_809

lemma nthP140 : Nat.nth Nat.Prime 140 = 811 :=
  nth_of_count (by norm_num) count_811

lemma nthP141 : Nat.nth Nat.Prime 141 = 821 :=
  nth_of_count (by norm_num) count_821

lemma nthP142 : Nat.nth Nat.Prime 142 = 823 :=
  nth_of_count (by norm_num) count_823

lemma nthP143 : Nat.nth Nat.Prime 143 = 827 :=
  nth_of_count (by norm_num) count_827

lemma nthP144 : Nat.nth Nat.Prime 144 = 829 :=
  nth_of_count (by norm_num) count_829

lemma nthP145 : Nat.nth Nat.Prime 145 = 839 :=
  nth_of_count (by norm_num) count_839

lemma nthP146 : Nat.nth Nat.Prime 146 = 853 :=
  nth_of_count (by norm_num) count_853

lemma nthP147 : Nat.nth Nat.Prime 147 = 857 :=
  nth_of_count (by norm_num) count_857

lemma nthP148 : Nat.nth Nat.Prime 148 = 859 :=
  nth_of_count (by norm_num) count_859

lemma nthP149 : Nat.nth Nat.Prime 149 = 863 :=
  nth_of_count (by norm_num) count_863

lemma nthP150 : Nat.nth Nat.Prime 150 = 877 :=
  nth_of_count (by norm_num) count_877

lemma nthP151 : Nat.nth Nat.Prime 151 = 881 :=
  nth_of_count (by norm_num) count_881

lemma nthP152 : Nat.nth Nat.Prime 152 = 883 :=
  nth_of_count (by norm_num) count_883

lemma nthP153 : Nat.nth Nat.Prime 153 = 887 :=
  nth_of_count (by norm_num) count_887

lemma a_ge_two_101 : 2 ≤ a 101 :=
  a_ge_two_of_hits 101 5 53 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP4, nthP100]; norm_num)
    (by rw [nthP52, nthP100]; norm_num)

lemma a_ge_two_102 : 2 ≤ a 102 :=
  a_ge_two_of_hits 102 17 29 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP16, nthP101]; norm_num)
    (by rw [nthP28, nthP101]; norm_num)

lemma a_ge_two_103 : 2 ≤ a 103 :=
  a_ge_two_of_hits 103 7 31 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP6, nthP102]; norm_num)
    (by rw [nthP30, nthP102]; norm_num)

lemma a_ge_two_104 : 2 ≤ a 104 :=
  a_ge_two_of_hits 104 2 3 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP1, nthP103]; norm_num)
    (by rw [nthP2, nthP103]; norm_num)

lemma a_ge_two_105 : 2 ≤ a 105 :=
  a_ge_two_of_hits 105 5 7 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP4, nthP104]; norm_num)
    (by rw [nthP6, nthP104]; norm_num)

lemma a_ge_two_106 : 2 ≤ a 106 :=
  a_ge_two_of_hits 106 3 5 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP105]; norm_num)
    (by rw [nthP4, nthP105]; norm_num)

lemma a_ge_two_107 : 2 ≤ a 107 :=
  a_ge_two_of_hits 107 5 17 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP4, nthP106]; norm_num)
    (by rw [nthP16, nthP106]; norm_num)

lemma a_ge_two_108 : 2 ≤ a 108 :=
  a_ge_two_of_hits 108 19 23 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP18, nthP107]; norm_num)
    (by rw [nthP22, nthP107]; norm_num)

lemma a_ge_two_109 : 2 ≤ a 109 :=
  a_ge_two_of_hits 109 2 19 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP1, nthP108]; norm_num)
    (by rw [nthP18, nthP108]; norm_num)

lemma a_ge_two_110 : 2 ≤ a 110 :=
  a_ge_two_of_hits 110 7 17 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP6, nthP109]; norm_num)
    (by rw [nthP16, nthP109]; norm_num)

lemma a_ge_two_111 : 2 ≤ a 111 :=
  a_ge_two_of_hits 111 3 5 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP110]; norm_num)
    (by rw [nthP4, nthP110]; norm_num)

lemma a_ge_two_112 : 2 ≤ a 112 :=
  a_ge_two_of_hits 112 19 31 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP18, nthP111]; norm_num)
    (by rw [nthP30, nthP111]; norm_num)

lemma a_ge_two_113 : 2 ≤ a 113 :=
  a_ge_two_of_hits 113 11 29 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP10, nthP112]; norm_num)
    (by rw [nthP28, nthP112]; norm_num)

lemma a_ge_two_114 : 2 ≤ a 114 :=
  a_ge_two_of_hits 114 3 19 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP113]; norm_num)
    (by rw [nthP18, nthP113]; norm_num)

lemma a_ge_two_115 : 2 ≤ a 115 :=
  a_ge_two_of_hits 115 13 17 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP12, nthP114]; norm_num)
    (by rw [nthP16, nthP114]; norm_num)

lemma a_ge_two_116 : 2 ≤ a 116 :=
  a_ge_two_of_hits 116 2 7 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP1, nthP115]; norm_num)
    (by rw [nthP6, nthP115]; norm_num)

lemma a_ge_two_117 : 2 ≤ a 117 :=
  a_ge_two_of_hits 117 3 23 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP116]; norm_num)
    (by rw [nthP22, nthP116]; norm_num)

lemma a_ge_two_118 : 2 ≤ a 118 :=
  a_ge_two_of_hits 118 5 13 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP4, nthP117]; norm_num)
    (by rw [nthP12, nthP117]; norm_num)

lemma a_ge_two_119 : 2 ≤ a 119 :=
  a_ge_two_of_hits 119 7 23 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP6, nthP118]; norm_num)
    (by rw [nthP22, nthP118]; norm_num)

lemma a_ge_two_120 : 2 ≤ a 120 :=
  a_ge_two_of_hits 120 3 7 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP119]; norm_num)
    (by rw [nthP6, nthP119]; norm_num)

lemma a_ge_two_121 : 2 ≤ a 121 :=
  a_ge_two_of_hits 121 7 17 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP6, nthP120]; norm_num)
    (by rw [nthP16, nthP120]; norm_num)

lemma a_ge_two_122 : 2 ≤ a 122 :=
  a_ge_two_of_hits 122 3 7 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP121]; norm_num)
    (by rw [nthP6, nthP121]; norm_num)

lemma a_ge_two_123 : 2 ≤ a 123 :=
  a_ge_two_of_hits 123 3 5 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP122]; norm_num)
    (by rw [nthP4, nthP122]; norm_num)

lemma a_ge_two_124 : 2 ≤ a 124 :=
  a_ge_two_of_hits 124 2 19 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP1, nthP123]; norm_num)
    (by rw [nthP18, nthP123]; norm_num)

lemma a_ge_two_125 : 2 ≤ a 125 :=
  a_ge_two_of_hits 125 17 43 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP16, nthP124]; norm_num)
    (by rw [nthP42, nthP124]; norm_num)

lemma a_ge_two_126 : 2 ≤ a 126 :=
  a_ge_two_of_hits 126 5 17 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP4, nthP125]; norm_num)
    (by rw [nthP16, nthP125]; norm_num)

lemma a_ge_two_127 : 2 ≤ a 127 :=
  a_ge_two_of_hits 127 31 37 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP30, nthP126]; norm_num)
    (by rw [nthP36, nthP126]; norm_num)

lemma a_ge_two_128 : 2 ≤ a 128 :=
  a_ge_two_of_hits 128 7 23 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP6, nthP127]; norm_num)
    (by rw [nthP22, nthP127]; norm_num)

lemma a_ge_two_129 : 2 ≤ a 129 :=
  a_ge_two_of_hits 129 83 127 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP82, nthP128]; norm_num)
    (by rw [nthP126, nthP128]; norm_num)

lemma a_ge_two_130 : 2 ≤ a 130 :=
  a_ge_two_of_hits 130 3 23 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP129]; norm_num)
    (by rw [nthP22, nthP129]; norm_num)

lemma a_ge_two_131 : 2 ≤ a 131 :=
  a_ge_two_of_hits 131 73 103 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP72, nthP130]; norm_num)
    (by rw [nthP102, nthP130]; norm_num)

lemma a_ge_two_132 : 2 ≤ a 132 :=
  a_ge_two_of_hits 132 19 31 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP18, nthP131]; norm_num)
    (by rw [nthP30, nthP131]; norm_num)

lemma a_ge_two_133 : 2 ≤ a 133 :=
  a_ge_two_of_hits 133 5 7 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP4, nthP132]; norm_num)
    (by rw [nthP6, nthP132]; norm_num)

lemma a_ge_two_134 : 2 ≤ a 134 :=
  a_ge_two_of_hits 134 5 11 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP4, nthP133]; norm_num)
    (by rw [nthP10, nthP133]; norm_num)

lemma a_ge_two_135 : 2 ≤ a 135 :=
  a_ge_two_of_hits 135 5 13 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP4, nthP134]; norm_num)
    (by rw [nthP12, nthP134]; norm_num)

lemma a_ge_two_136 : 2 ≤ a 136 :=
  a_ge_two_of_hits 136 19 31 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP18, nthP135]; norm_num)
    (by rw [nthP30, nthP135]; norm_num)

lemma a_ge_two_137 : 2 ≤ a 137 :=
  a_ge_two_of_hits 137 3 7 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP136]; norm_num)
    (by rw [nthP6, nthP136]; norm_num)

lemma a_ge_two_138 : 2 ≤ a 138 :=
  a_ge_two_of_hits 138 5 13 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP4, nthP137]; norm_num)
    (by rw [nthP12, nthP137]; norm_num)

lemma a_ge_two_139 : 2 ≤ a 139 :=
  a_ge_two_of_hits 139 11 17 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP10, nthP138]; norm_num)
    (by rw [nthP16, nthP138]; norm_num)

lemma a_ge_two_140 : 2 ≤ a 140 :=
  a_ge_two_of_hits 140 7 71 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP6, nthP139]; norm_num)
    (by rw [nthP70, nthP139]; norm_num)

lemma a_ge_two_141 : 2 ≤ a 141 :=
  a_ge_two_of_hits 141 5 7 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP4, nthP140]; norm_num)
    (by rw [nthP6, nthP140]; norm_num)

lemma a_ge_two_142 : 2 ≤ a 142 :=
  a_ge_two_of_hits 142 5 17 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP4, nthP141]; norm_num)
    (by rw [nthP16, nthP141]; norm_num)

lemma a_ge_two_143 : 2 ≤ a 143 :=
  a_ge_two_of_hits 143 7 31 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP6, nthP142]; norm_num)
    (by rw [nthP30, nthP142]; norm_num)

lemma a_ge_two_144 : 2 ≤ a 144 :=
  a_ge_two_of_hits 144 13 47 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP12, nthP143]; norm_num)
    (by rw [nthP46, nthP143]; norm_num)

lemma a_ge_two_145 : 2 ≤ a 145 :=
  a_ge_two_of_hits 145 3 19 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP144]; norm_num)
    (by rw [nthP18, nthP144]; norm_num)

lemma a_ge_two_146 : 2 ≤ a 146 :=
  a_ge_two_of_hits 146 3 19 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP145]; norm_num)
    (by rw [nthP18, nthP145]; norm_num)

lemma a_ge_two_147 : 2 ≤ a 147 :=
  a_ge_two_of_hits 147 3 37 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP146]; norm_num)
    (by rw [nthP36, nthP146]; norm_num)

lemma a_ge_two_148 : 2 ≤ a 148 :=
  a_ge_two_of_hits 148 3 11 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP147]; norm_num)
    (by rw [nthP10, nthP147]; norm_num)

lemma a_ge_two_149 : 2 ≤ a 149 :=
  a_ge_two_of_hits 149 19 31 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP18, nthP148]; norm_num)
    (by rw [nthP30, nthP148]; norm_num)

lemma a_ge_two_150 : 2 ≤ a 150 :=
  a_ge_two_of_hits 150 3 7 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP149]; norm_num)
    (by rw [nthP6, nthP149]; norm_num)

lemma a_ge_two_151 : 2 ≤ a 151 :=
  a_ge_two_of_hits 151 13 41 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP12, nthP150]; norm_num)
    (by rw [nthP40, nthP150]; norm_num)

lemma a_ge_two_152 : 2 ≤ a 152 :=
  a_ge_two_of_hits 152 11 31 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP10, nthP151]; norm_num)
    (by rw [nthP30, nthP151]; norm_num)

lemma a_ge_two_153 : 2 ≤ a 153 :=
  a_ge_two_of_hits 153 7 37 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP6, nthP152]; norm_num)
    (by rw [nthP36, nthP152]; norm_num)

lemma a_ge_two_154 : 2 ≤ a 154 :=
  a_ge_two_of_hits 154 29 43 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP28, nthP153]; norm_num)
    (by rw [nthP42, nthP153]; norm_num)

lemma a_ge_two_101_110 (n : ℕ) (h1 : 101 ≤ n) (h2 : n ≤ 110) : 2 ≤ a n := by
  interval_cases n
  · exact a_ge_two_101
  · exact a_ge_two_102
  · exact a_ge_two_103
  · exact a_ge_two_104
  · exact a_ge_two_105
  · exact a_ge_two_106
  · exact a_ge_two_107
  · exact a_ge_two_108
  · exact a_ge_two_109
  · exact a_ge_two_110

lemma a_ge_two_111_120 (n : ℕ) (h1 : 111 ≤ n) (h2 : n ≤ 120) : 2 ≤ a n := by
  interval_cases n
  · exact a_ge_two_111
  · exact a_ge_two_112
  · exact a_ge_two_113
  · exact a_ge_two_114
  · exact a_ge_two_115
  · exact a_ge_two_116
  · exact a_ge_two_117
  · exact a_ge_two_118
  · exact a_ge_two_119
  · exact a_ge_two_120

lemma a_ge_two_121_130 (n : ℕ) (h1 : 121 ≤ n) (h2 : n ≤ 130) : 2 ≤ a n := by
  interval_cases n
  · exact a_ge_two_121
  · exact a_ge_two_122
  · exact a_ge_two_123
  · exact a_ge_two_124
  · exact a_ge_two_125
  · exact a_ge_two_126
  · exact a_ge_two_127
  · exact a_ge_two_128
  · exact a_ge_two_129
  · exact a_ge_two_130

lemma a_ge_two_131_140 (n : ℕ) (h1 : 131 ≤ n) (h2 : n ≤ 140) : 2 ≤ a n := by
  interval_cases n
  · exact a_ge_two_131
  · exact a_ge_two_132
  · exact a_ge_two_133
  · exact a_ge_two_134
  · exact a_ge_two_135
  · exact a_ge_two_136
  · exact a_ge_two_137
  · exact a_ge_two_138
  · exact a_ge_two_139
  · exact a_ge_two_140

lemma a_ge_two_141_154 (n : ℕ) (h1 : 141 ≤ n) (h2 : n ≤ 154) : 2 ≤ a n := by
  interval_cases n
  · exact a_ge_two_141
  · exact a_ge_two_142
  · exact a_ge_two_143
  · exact a_ge_two_144
  · exact a_ge_two_145
  · exact a_ge_two_146
  · exact a_ge_two_147
  · exact a_ge_two_148
  · exact a_ge_two_149
  · exact a_ge_two_150
  · exact a_ge_two_151
  · exact a_ge_two_152
  · exact a_ge_two_153
  · exact a_ge_two_154

lemma a_ge_two_101_154 (n : ℕ) (h1 : 101 ≤ n) (h2 : n ≤ 154) : 2 ≤ a n := by
  if h : n ≤ 110 then
    exact a_ge_two_101_110 n h1 h
  else if h2' : n ≤ 120 then
    exact a_ge_two_111_120 n (by omega) h2'
  else if h3 : n ≤ 130 then
    exact a_ge_two_121_130 n (by omega) h3
  else if h4 : n ≤ 140 then
    exact a_ge_two_131_140 n (by omega) h4
  else
    exact a_ge_two_141_154 n (by omega) h2

lemma count_888 : Nat.count Nat.Prime 888 = 154 := by
  rw [count_succ_prime, count_887]; norm_num

lemma count_889 : Nat.count Nat.Prime 889 = 154 := by
  rw [count_succ_prime, count_888]; norm_num

lemma count_890 : Nat.count Nat.Prime 890 = 154 := by
  rw [count_succ_prime, count_889]; norm_num

lemma count_891 : Nat.count Nat.Prime 891 = 154 := by
  rw [count_succ_prime, count_890]; norm_num

lemma count_892 : Nat.count Nat.Prime 892 = 154 := by
  rw [count_succ_prime, count_891]; norm_num

lemma count_893 : Nat.count Nat.Prime 893 = 154 := by
  rw [count_succ_prime, count_892]; norm_num

lemma count_894 : Nat.count Nat.Prime 894 = 154 := by
  rw [count_succ_prime, count_893]; norm_num

lemma count_895 : Nat.count Nat.Prime 895 = 154 := by
  rw [count_succ_prime, count_894]; norm_num

lemma count_896 : Nat.count Nat.Prime 896 = 154 := by
  rw [count_succ_prime, count_895]; norm_num

lemma count_897 : Nat.count Nat.Prime 897 = 154 := by
  rw [count_succ_prime, count_896]; norm_num

lemma count_898 : Nat.count Nat.Prime 898 = 154 := by
  rw [count_succ_prime, count_897]; norm_num

lemma count_899 : Nat.count Nat.Prime 899 = 154 := by
  rw [count_succ_prime, count_898]; norm_num

lemma count_900 : Nat.count Nat.Prime 900 = 154 := by
  rw [count_succ_prime, count_899]; norm_num

lemma count_901 : Nat.count Nat.Prime 901 = 154 := by
  rw [count_succ_prime, count_900]; norm_num

lemma count_902 : Nat.count Nat.Prime 902 = 154 := by
  rw [count_succ_prime, count_901]; norm_num

lemma count_903 : Nat.count Nat.Prime 903 = 154 := by
  rw [count_succ_prime, count_902]; norm_num

lemma count_904 : Nat.count Nat.Prime 904 = 154 := by
  rw [count_succ_prime, count_903]; norm_num

lemma count_905 : Nat.count Nat.Prime 905 = 154 := by
  rw [count_succ_prime, count_904]; norm_num

lemma count_906 : Nat.count Nat.Prime 906 = 154 := by
  rw [count_succ_prime, count_905]; norm_num

lemma count_907 : Nat.count Nat.Prime 907 = 154 := by
  rw [count_succ_prime, count_906]; norm_num

lemma count_908 : Nat.count Nat.Prime 908 = 155 := by
  rw [count_succ_prime, count_907]; norm_num

lemma count_909 : Nat.count Nat.Prime 909 = 155 := by
  rw [count_succ_prime, count_908]; norm_num

lemma count_910 : Nat.count Nat.Prime 910 = 155 := by
  rw [count_succ_prime, count_909]; norm_num

lemma count_911 : Nat.count Nat.Prime 911 = 155 := by
  rw [count_succ_prime, count_910]; norm_num

lemma count_912 : Nat.count Nat.Prime 912 = 156 := by
  rw [count_succ_prime, count_911]; norm_num

lemma count_913 : Nat.count Nat.Prime 913 = 156 := by
  rw [count_succ_prime, count_912]; norm_num

lemma count_914 : Nat.count Nat.Prime 914 = 156 := by
  rw [count_succ_prime, count_913]; norm_num

lemma count_915 : Nat.count Nat.Prime 915 = 156 := by
  rw [count_succ_prime, count_914]; norm_num

lemma count_916 : Nat.count Nat.Prime 916 = 156 := by
  rw [count_succ_prime, count_915]; norm_num

lemma count_917 : Nat.count Nat.Prime 917 = 156 := by
  rw [count_succ_prime, count_916]; norm_num

lemma count_918 : Nat.count Nat.Prime 918 = 156 := by
  rw [count_succ_prime, count_917]; norm_num

lemma count_919 : Nat.count Nat.Prime 919 = 156 := by
  rw [count_succ_prime, count_918]; norm_num

lemma count_920 : Nat.count Nat.Prime 920 = 157 := by
  rw [count_succ_prime, count_919]; norm_num

lemma count_921 : Nat.count Nat.Prime 921 = 157 := by
  rw [count_succ_prime, count_920]; norm_num

lemma count_922 : Nat.count Nat.Prime 922 = 157 := by
  rw [count_succ_prime, count_921]; norm_num

lemma count_923 : Nat.count Nat.Prime 923 = 157 := by
  rw [count_succ_prime, count_922]; norm_num

lemma count_924 : Nat.count Nat.Prime 924 = 157 := by
  rw [count_succ_prime, count_923]; norm_num

lemma count_925 : Nat.count Nat.Prime 925 = 157 := by
  rw [count_succ_prime, count_924]; norm_num

lemma count_926 : Nat.count Nat.Prime 926 = 157 := by
  rw [count_succ_prime, count_925]; norm_num

lemma count_927 : Nat.count Nat.Prime 927 = 157 := by
  rw [count_succ_prime, count_926]; norm_num

lemma count_928 : Nat.count Nat.Prime 928 = 157 := by
  rw [count_succ_prime, count_927]; norm_num

lemma count_929 : Nat.count Nat.Prime 929 = 157 := by
  rw [count_succ_prime, count_928]; norm_num

lemma count_930 : Nat.count Nat.Prime 930 = 158 := by
  rw [count_succ_prime, count_929]; norm_num

lemma count_931 : Nat.count Nat.Prime 931 = 158 := by
  rw [count_succ_prime, count_930]; norm_num

lemma count_932 : Nat.count Nat.Prime 932 = 158 := by
  rw [count_succ_prime, count_931]; norm_num

lemma count_933 : Nat.count Nat.Prime 933 = 158 := by
  rw [count_succ_prime, count_932]; norm_num

lemma count_934 : Nat.count Nat.Prime 934 = 158 := by
  rw [count_succ_prime, count_933]; norm_num

lemma count_935 : Nat.count Nat.Prime 935 = 158 := by
  rw [count_succ_prime, count_934]; norm_num

lemma count_936 : Nat.count Nat.Prime 936 = 158 := by
  rw [count_succ_prime, count_935]; norm_num

lemma count_937 : Nat.count Nat.Prime 937 = 158 := by
  rw [count_succ_prime, count_936]; norm_num

lemma count_938 : Nat.count Nat.Prime 938 = 159 := by
  rw [count_succ_prime, count_937]; norm_num

lemma count_939 : Nat.count Nat.Prime 939 = 159 := by
  rw [count_succ_prime, count_938]; norm_num

lemma count_940 : Nat.count Nat.Prime 940 = 159 := by
  rw [count_succ_prime, count_939]; norm_num

lemma count_941 : Nat.count Nat.Prime 941 = 159 := by
  rw [count_succ_prime, count_940]; norm_num

lemma count_942 : Nat.count Nat.Prime 942 = 160 := by
  rw [count_succ_prime, count_941]; norm_num

lemma count_943 : Nat.count Nat.Prime 943 = 160 := by
  rw [count_succ_prime, count_942]; norm_num

lemma count_944 : Nat.count Nat.Prime 944 = 160 := by
  rw [count_succ_prime, count_943]; norm_num

lemma count_945 : Nat.count Nat.Prime 945 = 160 := by
  rw [count_succ_prime, count_944]; norm_num

lemma count_946 : Nat.count Nat.Prime 946 = 160 := by
  rw [count_succ_prime, count_945]; norm_num

lemma count_947 : Nat.count Nat.Prime 947 = 160 := by
  rw [count_succ_prime, count_946]; norm_num

lemma count_948 : Nat.count Nat.Prime 948 = 161 := by
  rw [count_succ_prime, count_947]; norm_num

lemma count_949 : Nat.count Nat.Prime 949 = 161 := by
  rw [count_succ_prime, count_948]; norm_num

lemma count_950 : Nat.count Nat.Prime 950 = 161 := by
  rw [count_succ_prime, count_949]; norm_num

lemma count_951 : Nat.count Nat.Prime 951 = 161 := by
  rw [count_succ_prime, count_950]; norm_num

lemma count_952 : Nat.count Nat.Prime 952 = 161 := by
  rw [count_succ_prime, count_951]; norm_num

lemma count_953 : Nat.count Nat.Prime 953 = 161 := by
  rw [count_succ_prime, count_952]; norm_num

lemma count_954 : Nat.count Nat.Prime 954 = 162 := by
  rw [count_succ_prime, count_953]; norm_num

lemma count_955 : Nat.count Nat.Prime 955 = 162 := by
  rw [count_succ_prime, count_954]; norm_num

lemma count_956 : Nat.count Nat.Prime 956 = 162 := by
  rw [count_succ_prime, count_955]; norm_num

lemma count_957 : Nat.count Nat.Prime 957 = 162 := by
  rw [count_succ_prime, count_956]; norm_num

lemma count_958 : Nat.count Nat.Prime 958 = 162 := by
  rw [count_succ_prime, count_957]; norm_num

lemma count_959 : Nat.count Nat.Prime 959 = 162 := by
  rw [count_succ_prime, count_958]; norm_num

lemma count_960 : Nat.count Nat.Prime 960 = 162 := by
  rw [count_succ_prime, count_959]; norm_num

lemma count_961 : Nat.count Nat.Prime 961 = 162 := by
  rw [count_succ_prime, count_960]; norm_num

lemma count_962 : Nat.count Nat.Prime 962 = 162 := by
  rw [count_succ_prime, count_961]; norm_num

lemma count_963 : Nat.count Nat.Prime 963 = 162 := by
  rw [count_succ_prime, count_962]; norm_num

lemma count_964 : Nat.count Nat.Prime 964 = 162 := by
  rw [count_succ_prime, count_963]; norm_num

lemma count_965 : Nat.count Nat.Prime 965 = 162 := by
  rw [count_succ_prime, count_964]; norm_num

lemma count_966 : Nat.count Nat.Prime 966 = 162 := by
  rw [count_succ_prime, count_965]; norm_num

lemma count_967 : Nat.count Nat.Prime 967 = 162 := by
  rw [count_succ_prime, count_966]; norm_num

lemma count_968 : Nat.count Nat.Prime 968 = 163 := by
  rw [count_succ_prime, count_967]; norm_num

lemma count_969 : Nat.count Nat.Prime 969 = 163 := by
  rw [count_succ_prime, count_968]; norm_num

lemma count_970 : Nat.count Nat.Prime 970 = 163 := by
  rw [count_succ_prime, count_969]; norm_num

lemma count_971 : Nat.count Nat.Prime 971 = 163 := by
  rw [count_succ_prime, count_970]; norm_num

lemma count_972 : Nat.count Nat.Prime 972 = 164 := by
  rw [count_succ_prime, count_971]; norm_num

lemma count_973 : Nat.count Nat.Prime 973 = 164 := by
  rw [count_succ_prime, count_972]; norm_num

lemma count_974 : Nat.count Nat.Prime 974 = 164 := by
  rw [count_succ_prime, count_973]; norm_num

lemma count_975 : Nat.count Nat.Prime 975 = 164 := by
  rw [count_succ_prime, count_974]; norm_num

lemma count_976 : Nat.count Nat.Prime 976 = 164 := by
  rw [count_succ_prime, count_975]; norm_num

lemma count_977 : Nat.count Nat.Prime 977 = 164 := by
  rw [count_succ_prime, count_976]; norm_num

lemma count_978 : Nat.count Nat.Prime 978 = 165 := by
  rw [count_succ_prime, count_977]; norm_num

lemma count_979 : Nat.count Nat.Prime 979 = 165 := by
  rw [count_succ_prime, count_978]; norm_num

lemma count_980 : Nat.count Nat.Prime 980 = 165 := by
  rw [count_succ_prime, count_979]; norm_num

lemma count_981 : Nat.count Nat.Prime 981 = 165 := by
  rw [count_succ_prime, count_980]; norm_num

lemma count_982 : Nat.count Nat.Prime 982 = 165 := by
  rw [count_succ_prime, count_981]; norm_num

lemma count_983 : Nat.count Nat.Prime 983 = 165 := by
  rw [count_succ_prime, count_982]; norm_num

lemma count_984 : Nat.count Nat.Prime 984 = 166 := by
  rw [count_succ_prime, count_983]; norm_num

lemma count_985 : Nat.count Nat.Prime 985 = 166 := by
  rw [count_succ_prime, count_984]; norm_num

lemma count_986 : Nat.count Nat.Prime 986 = 166 := by
  rw [count_succ_prime, count_985]; norm_num

lemma count_987 : Nat.count Nat.Prime 987 = 166 := by
  rw [count_succ_prime, count_986]; norm_num

lemma count_988 : Nat.count Nat.Prime 988 = 166 := by
  rw [count_succ_prime, count_987]; norm_num

lemma count_989 : Nat.count Nat.Prime 989 = 166 := by
  rw [count_succ_prime, count_988]; norm_num

lemma count_990 : Nat.count Nat.Prime 990 = 166 := by
  rw [count_succ_prime, count_989]; norm_num

lemma count_991 : Nat.count Nat.Prime 991 = 166 := by
  rw [count_succ_prime, count_990]; norm_num

lemma count_992 : Nat.count Nat.Prime 992 = 167 := by
  rw [count_succ_prime, count_991]; norm_num

lemma count_993 : Nat.count Nat.Prime 993 = 167 := by
  rw [count_succ_prime, count_992]; norm_num

lemma count_994 : Nat.count Nat.Prime 994 = 167 := by
  rw [count_succ_prime, count_993]; norm_num

lemma count_995 : Nat.count Nat.Prime 995 = 167 := by
  rw [count_succ_prime, count_994]; norm_num

lemma count_996 : Nat.count Nat.Prime 996 = 167 := by
  rw [count_succ_prime, count_995]; norm_num

lemma count_997 : Nat.count Nat.Prime 997 = 167 := by
  rw [count_succ_prime, count_996]; norm_num

lemma count_998 : Nat.count Nat.Prime 998 = 168 := by
  rw [count_succ_prime, count_997]; norm_num

lemma count_999 : Nat.count Nat.Prime 999 = 168 := by
  rw [count_succ_prime, count_998]; norm_num

lemma count_1000 : Nat.count Nat.Prime 1000 = 168 := by
  rw [count_succ_prime, count_999]; norm_num

lemma count_1001 : Nat.count Nat.Prime 1001 = 168 := by
  rw [count_succ_prime, count_1000]; norm_num

lemma count_1002 : Nat.count Nat.Prime 1002 = 168 := by
  rw [count_succ_prime, count_1001]; norm_num

lemma count_1003 : Nat.count Nat.Prime 1003 = 168 := by
  rw [count_succ_prime, count_1002]; norm_num

lemma count_1004 : Nat.count Nat.Prime 1004 = 168 := by
  rw [count_succ_prime, count_1003]; norm_num

lemma count_1005 : Nat.count Nat.Prime 1005 = 168 := by
  rw [count_succ_prime, count_1004]; norm_num

lemma count_1006 : Nat.count Nat.Prime 1006 = 168 := by
  rw [count_succ_prime, count_1005]; norm_num

lemma count_1007 : Nat.count Nat.Prime 1007 = 168 := by
  rw [count_succ_prime, count_1006]; norm_num

lemma count_1008 : Nat.count Nat.Prime 1008 = 168 := by
  rw [count_succ_prime, count_1007]; norm_num

lemma count_1009 : Nat.count Nat.Prime 1009 = 168 := by
  rw [count_succ_prime, count_1008]; norm_num

lemma count_1010 : Nat.count Nat.Prime 1010 = 169 := by
  rw [count_succ_prime, count_1009]; norm_num

lemma count_1011 : Nat.count Nat.Prime 1011 = 169 := by
  rw [count_succ_prime, count_1010]; norm_num

lemma count_1012 : Nat.count Nat.Prime 1012 = 169 := by
  rw [count_succ_prime, count_1011]; norm_num

lemma count_1013 : Nat.count Nat.Prime 1013 = 169 := by
  rw [count_succ_prime, count_1012]; norm_num

lemma count_1014 : Nat.count Nat.Prime 1014 = 170 := by
  rw [count_succ_prime, count_1013]; norm_num

lemma count_1015 : Nat.count Nat.Prime 1015 = 170 := by
  rw [count_succ_prime, count_1014]; norm_num

lemma count_1016 : Nat.count Nat.Prime 1016 = 170 := by
  rw [count_succ_prime, count_1015]; norm_num

lemma count_1017 : Nat.count Nat.Prime 1017 = 170 := by
  rw [count_succ_prime, count_1016]; norm_num

lemma count_1018 : Nat.count Nat.Prime 1018 = 170 := by
  rw [count_succ_prime, count_1017]; norm_num

lemma count_1019 : Nat.count Nat.Prime 1019 = 170 := by
  rw [count_succ_prime, count_1018]; norm_num

lemma count_1020 : Nat.count Nat.Prime 1020 = 171 := by
  rw [count_succ_prime, count_1019]; norm_num

lemma count_1021 : Nat.count Nat.Prime 1021 = 171 := by
  rw [count_succ_prime, count_1020]; norm_num

lemma count_1022 : Nat.count Nat.Prime 1022 = 172 := by
  rw [count_succ_prime, count_1021]; norm_num

lemma count_1023 : Nat.count Nat.Prime 1023 = 172 := by
  rw [count_succ_prime, count_1022]; norm_num

lemma count_1024 : Nat.count Nat.Prime 1024 = 172 := by
  rw [count_succ_prime, count_1023]; norm_num

lemma count_1025 : Nat.count Nat.Prime 1025 = 172 := by
  rw [count_succ_prime, count_1024]; norm_num

lemma count_1026 : Nat.count Nat.Prime 1026 = 172 := by
  rw [count_succ_prime, count_1025]; norm_num

lemma count_1027 : Nat.count Nat.Prime 1027 = 172 := by
  rw [count_succ_prime, count_1026]; norm_num

lemma count_1028 : Nat.count Nat.Prime 1028 = 172 := by
  rw [count_succ_prime, count_1027]; norm_num

lemma count_1029 : Nat.count Nat.Prime 1029 = 172 := by
  rw [count_succ_prime, count_1028]; norm_num

lemma count_1030 : Nat.count Nat.Prime 1030 = 172 := by
  rw [count_succ_prime, count_1029]; norm_num

lemma count_1031 : Nat.count Nat.Prime 1031 = 172 := by
  rw [count_succ_prime, count_1030]; norm_num

lemma count_1032 : Nat.count Nat.Prime 1032 = 173 := by
  rw [count_succ_prime, count_1031]; norm_num

lemma count_1033 : Nat.count Nat.Prime 1033 = 173 := by
  rw [count_succ_prime, count_1032]; norm_num

lemma count_1034 : Nat.count Nat.Prime 1034 = 174 := by
  rw [count_succ_prime, count_1033]; norm_num

lemma count_1035 : Nat.count Nat.Prime 1035 = 174 := by
  rw [count_succ_prime, count_1034]; norm_num

lemma count_1036 : Nat.count Nat.Prime 1036 = 174 := by
  rw [count_succ_prime, count_1035]; norm_num

lemma count_1037 : Nat.count Nat.Prime 1037 = 174 := by
  rw [count_succ_prime, count_1036]; norm_num

lemma count_1038 : Nat.count Nat.Prime 1038 = 174 := by
  rw [count_succ_prime, count_1037]; norm_num

lemma count_1039 : Nat.count Nat.Prime 1039 = 174 := by
  rw [count_succ_prime, count_1038]; norm_num

lemma count_1040 : Nat.count Nat.Prime 1040 = 175 := by
  rw [count_succ_prime, count_1039]; norm_num

lemma count_1041 : Nat.count Nat.Prime 1041 = 175 := by
  rw [count_succ_prime, count_1040]; norm_num

lemma count_1042 : Nat.count Nat.Prime 1042 = 175 := by
  rw [count_succ_prime, count_1041]; norm_num

lemma count_1043 : Nat.count Nat.Prime 1043 = 175 := by
  rw [count_succ_prime, count_1042]; norm_num

lemma count_1044 : Nat.count Nat.Prime 1044 = 175 := by
  rw [count_succ_prime, count_1043]; norm_num

lemma count_1045 : Nat.count Nat.Prime 1045 = 175 := by
  rw [count_succ_prime, count_1044]; norm_num

lemma count_1046 : Nat.count Nat.Prime 1046 = 175 := by
  rw [count_succ_prime, count_1045]; norm_num

lemma count_1047 : Nat.count Nat.Prime 1047 = 175 := by
  rw [count_succ_prime, count_1046]; norm_num

lemma count_1048 : Nat.count Nat.Prime 1048 = 175 := by
  rw [count_succ_prime, count_1047]; norm_num

lemma count_1049 : Nat.count Nat.Prime 1049 = 175 := by
  rw [count_succ_prime, count_1048]; norm_num

lemma count_1050 : Nat.count Nat.Prime 1050 = 176 := by
  rw [count_succ_prime, count_1049]; norm_num

lemma count_1051 : Nat.count Nat.Prime 1051 = 176 := by
  rw [count_succ_prime, count_1050]; norm_num

lemma count_1052 : Nat.count Nat.Prime 1052 = 177 := by
  rw [count_succ_prime, count_1051]; norm_num

lemma count_1053 : Nat.count Nat.Prime 1053 = 177 := by
  rw [count_succ_prime, count_1052]; norm_num

lemma count_1054 : Nat.count Nat.Prime 1054 = 177 := by
  rw [count_succ_prime, count_1053]; norm_num

lemma count_1055 : Nat.count Nat.Prime 1055 = 177 := by
  rw [count_succ_prime, count_1054]; norm_num

lemma count_1056 : Nat.count Nat.Prime 1056 = 177 := by
  rw [count_succ_prime, count_1055]; norm_num

lemma count_1057 : Nat.count Nat.Prime 1057 = 177 := by
  rw [count_succ_prime, count_1056]; norm_num

lemma count_1058 : Nat.count Nat.Prime 1058 = 177 := by
  rw [count_succ_prime, count_1057]; norm_num

lemma count_1059 : Nat.count Nat.Prime 1059 = 177 := by
  rw [count_succ_prime, count_1058]; norm_num

lemma count_1060 : Nat.count Nat.Prime 1060 = 177 := by
  rw [count_succ_prime, count_1059]; norm_num

lemma count_1061 : Nat.count Nat.Prime 1061 = 177 := by
  rw [count_succ_prime, count_1060]; norm_num

lemma count_1062 : Nat.count Nat.Prime 1062 = 178 := by
  rw [count_succ_prime, count_1061]; norm_num

lemma count_1063 : Nat.count Nat.Prime 1063 = 178 := by
  rw [count_succ_prime, count_1062]; norm_num

lemma count_1064 : Nat.count Nat.Prime 1064 = 179 := by
  rw [count_succ_prime, count_1063]; norm_num

lemma count_1065 : Nat.count Nat.Prime 1065 = 179 := by
  rw [count_succ_prime, count_1064]; norm_num

lemma count_1066 : Nat.count Nat.Prime 1066 = 179 := by
  rw [count_succ_prime, count_1065]; norm_num

lemma count_1067 : Nat.count Nat.Prime 1067 = 179 := by
  rw [count_succ_prime, count_1066]; norm_num

lemma count_1068 : Nat.count Nat.Prime 1068 = 179 := by
  rw [count_succ_prime, count_1067]; norm_num

lemma count_1069 : Nat.count Nat.Prime 1069 = 179 := by
  rw [count_succ_prime, count_1068]; norm_num

lemma count_1070 : Nat.count Nat.Prime 1070 = 180 := by
  rw [count_succ_prime, count_1069]; norm_num

lemma count_1071 : Nat.count Nat.Prime 1071 = 180 := by
  rw [count_succ_prime, count_1070]; norm_num

lemma count_1072 : Nat.count Nat.Prime 1072 = 180 := by
  rw [count_succ_prime, count_1071]; norm_num

lemma count_1073 : Nat.count Nat.Prime 1073 = 180 := by
  rw [count_succ_prime, count_1072]; norm_num

lemma count_1074 : Nat.count Nat.Prime 1074 = 180 := by
  rw [count_succ_prime, count_1073]; norm_num

lemma count_1075 : Nat.count Nat.Prime 1075 = 180 := by
  rw [count_succ_prime, count_1074]; norm_num

lemma count_1076 : Nat.count Nat.Prime 1076 = 180 := by
  rw [count_succ_prime, count_1075]; norm_num

lemma count_1077 : Nat.count Nat.Prime 1077 = 180 := by
  rw [count_succ_prime, count_1076]; norm_num

lemma count_1078 : Nat.count Nat.Prime 1078 = 180 := by
  rw [count_succ_prime, count_1077]; norm_num

lemma count_1079 : Nat.count Nat.Prime 1079 = 180 := by
  rw [count_succ_prime, count_1078]; norm_num

lemma count_1080 : Nat.count Nat.Prime 1080 = 180 := by
  rw [count_succ_prime, count_1079]; norm_num

lemma count_1081 : Nat.count Nat.Prime 1081 = 180 := by
  rw [count_succ_prime, count_1080]; norm_num

lemma count_1082 : Nat.count Nat.Prime 1082 = 180 := by
  rw [count_succ_prime, count_1081]; norm_num

lemma count_1083 : Nat.count Nat.Prime 1083 = 180 := by
  rw [count_succ_prime, count_1082]; norm_num

lemma count_1084 : Nat.count Nat.Prime 1084 = 180 := by
  rw [count_succ_prime, count_1083]; norm_num

lemma count_1085 : Nat.count Nat.Prime 1085 = 180 := by
  rw [count_succ_prime, count_1084]; norm_num

lemma count_1086 : Nat.count Nat.Prime 1086 = 180 := by
  rw [count_succ_prime, count_1085]; norm_num

lemma count_1087 : Nat.count Nat.Prime 1087 = 180 := by
  rw [count_succ_prime, count_1086]; norm_num

lemma count_1088 : Nat.count Nat.Prime 1088 = 181 := by
  rw [count_succ_prime, count_1087]; norm_num

lemma count_1089 : Nat.count Nat.Prime 1089 = 181 := by
  rw [count_succ_prime, count_1088]; norm_num

lemma count_1090 : Nat.count Nat.Prime 1090 = 181 := by
  rw [count_succ_prime, count_1089]; norm_num

lemma count_1091 : Nat.count Nat.Prime 1091 = 181 := by
  rw [count_succ_prime, count_1090]; norm_num

lemma count_1092 : Nat.count Nat.Prime 1092 = 182 := by
  rw [count_succ_prime, count_1091]; norm_num

lemma count_1093 : Nat.count Nat.Prime 1093 = 182 := by
  rw [count_succ_prime, count_1092]; norm_num

lemma count_1094 : Nat.count Nat.Prime 1094 = 183 := by
  rw [count_succ_prime, count_1093]; norm_num

lemma count_1095 : Nat.count Nat.Prime 1095 = 183 := by
  rw [count_succ_prime, count_1094]; norm_num

lemma count_1096 : Nat.count Nat.Prime 1096 = 183 := by
  rw [count_succ_prime, count_1095]; norm_num

lemma count_1097 : Nat.count Nat.Prime 1097 = 183 := by
  rw [count_succ_prime, count_1096]; norm_num

lemma count_1098 : Nat.count Nat.Prime 1098 = 184 := by
  rw [count_succ_prime, count_1097]; norm_num

lemma count_1099 : Nat.count Nat.Prime 1099 = 184 := by
  rw [count_succ_prime, count_1098]; norm_num

lemma count_1100 : Nat.count Nat.Prime 1100 = 184 := by
  rw [count_succ_prime, count_1099]; norm_num

lemma count_1101 : Nat.count Nat.Prime 1101 = 184 := by
  rw [count_succ_prime, count_1100]; norm_num

lemma count_1102 : Nat.count Nat.Prime 1102 = 184 := by
  rw [count_succ_prime, count_1101]; norm_num

lemma count_1103 : Nat.count Nat.Prime 1103 = 184 := by
  rw [count_succ_prime, count_1102]; norm_num

lemma count_1104 : Nat.count Nat.Prime 1104 = 185 := by
  rw [count_succ_prime, count_1103]; norm_num

lemma count_1105 : Nat.count Nat.Prime 1105 = 185 := by
  rw [count_succ_prime, count_1104]; norm_num

lemma count_1106 : Nat.count Nat.Prime 1106 = 185 := by
  rw [count_succ_prime, count_1105]; norm_num

lemma count_1107 : Nat.count Nat.Prime 1107 = 185 := by
  rw [count_succ_prime, count_1106]; norm_num

lemma count_1108 : Nat.count Nat.Prime 1108 = 185 := by
  rw [count_succ_prime, count_1107]; norm_num

lemma count_1109 : Nat.count Nat.Prime 1109 = 185 := by
  rw [count_succ_prime, count_1108]; norm_num

lemma count_1110 : Nat.count Nat.Prime 1110 = 186 := by
  rw [count_succ_prime, count_1109]; norm_num

lemma count_1111 : Nat.count Nat.Prime 1111 = 186 := by
  rw [count_succ_prime, count_1110]; norm_num

lemma count_1112 : Nat.count Nat.Prime 1112 = 186 := by
  rw [count_succ_prime, count_1111]; norm_num

lemma count_1113 : Nat.count Nat.Prime 1113 = 186 := by
  rw [count_succ_prime, count_1112]; norm_num

lemma count_1114 : Nat.count Nat.Prime 1114 = 186 := by
  rw [count_succ_prime, count_1113]; norm_num

lemma count_1115 : Nat.count Nat.Prime 1115 = 186 := by
  rw [count_succ_prime, count_1114]; norm_num

lemma count_1116 : Nat.count Nat.Prime 1116 = 186 := by
  rw [count_succ_prime, count_1115]; norm_num

lemma count_1117 : Nat.count Nat.Prime 1117 = 186 := by
  rw [count_succ_prime, count_1116]; norm_num

lemma count_1118 : Nat.count Nat.Prime 1118 = 187 := by
  rw [count_succ_prime, count_1117]; norm_num

lemma count_1119 : Nat.count Nat.Prime 1119 = 187 := by
  rw [count_succ_prime, count_1118]; norm_num

lemma count_1120 : Nat.count Nat.Prime 1120 = 187 := by
  rw [count_succ_prime, count_1119]; norm_num

lemma count_1121 : Nat.count Nat.Prime 1121 = 187 := by
  rw [count_succ_prime, count_1120]; norm_num

lemma count_1122 : Nat.count Nat.Prime 1122 = 187 := by
  rw [count_succ_prime, count_1121]; norm_num

lemma count_1123 : Nat.count Nat.Prime 1123 = 187 := by
  rw [count_succ_prime, count_1122]; norm_num

lemma count_1124 : Nat.count Nat.Prime 1124 = 188 := by
  rw [count_succ_prime, count_1123]; norm_num

lemma count_1125 : Nat.count Nat.Prime 1125 = 188 := by
  rw [count_succ_prime, count_1124]; norm_num

lemma count_1126 : Nat.count Nat.Prime 1126 = 188 := by
  rw [count_succ_prime, count_1125]; norm_num

lemma count_1127 : Nat.count Nat.Prime 1127 = 188 := by
  rw [count_succ_prime, count_1126]; norm_num

lemma count_1128 : Nat.count Nat.Prime 1128 = 188 := by
  rw [count_succ_prime, count_1127]; norm_num

lemma count_1129 : Nat.count Nat.Prime 1129 = 188 := by
  rw [count_succ_prime, count_1128]; norm_num

lemma count_1130 : Nat.count Nat.Prime 1130 = 189 := by
  rw [count_succ_prime, count_1129]; norm_num

lemma count_1131 : Nat.count Nat.Prime 1131 = 189 := by
  rw [count_succ_prime, count_1130]; norm_num

lemma count_1132 : Nat.count Nat.Prime 1132 = 189 := by
  rw [count_succ_prime, count_1131]; norm_num

lemma count_1133 : Nat.count Nat.Prime 1133 = 189 := by
  rw [count_succ_prime, count_1132]; norm_num

lemma count_1134 : Nat.count Nat.Prime 1134 = 189 := by
  rw [count_succ_prime, count_1133]; norm_num

lemma count_1135 : Nat.count Nat.Prime 1135 = 189 := by
  rw [count_succ_prime, count_1134]; norm_num

lemma count_1136 : Nat.count Nat.Prime 1136 = 189 := by
  rw [count_succ_prime, count_1135]; norm_num

lemma count_1137 : Nat.count Nat.Prime 1137 = 189 := by
  rw [count_succ_prime, count_1136]; norm_num

lemma count_1138 : Nat.count Nat.Prime 1138 = 189 := by
  rw [count_succ_prime, count_1137]; norm_num

lemma count_1139 : Nat.count Nat.Prime 1139 = 189 := by
  rw [count_succ_prime, count_1138]; norm_num

lemma count_1140 : Nat.count Nat.Prime 1140 = 189 := by
  rw [count_succ_prime, count_1139]; norm_num

lemma count_1141 : Nat.count Nat.Prime 1141 = 189 := by
  rw [count_succ_prime, count_1140]; norm_num

lemma count_1142 : Nat.count Nat.Prime 1142 = 189 := by
  rw [count_succ_prime, count_1141]; norm_num

lemma count_1143 : Nat.count Nat.Prime 1143 = 189 := by
  rw [count_succ_prime, count_1142]; norm_num

lemma count_1144 : Nat.count Nat.Prime 1144 = 189 := by
  rw [count_succ_prime, count_1143]; norm_num

lemma count_1145 : Nat.count Nat.Prime 1145 = 189 := by
  rw [count_succ_prime, count_1144]; norm_num

lemma count_1146 : Nat.count Nat.Prime 1146 = 189 := by
  rw [count_succ_prime, count_1145]; norm_num

lemma count_1147 : Nat.count Nat.Prime 1147 = 189 := by
  rw [count_succ_prime, count_1146]; norm_num

lemma count_1148 : Nat.count Nat.Prime 1148 = 189 := by
  rw [count_succ_prime, count_1147]; norm_num

lemma count_1149 : Nat.count Nat.Prime 1149 = 189 := by
  rw [count_succ_prime, count_1148]; norm_num

lemma count_1150 : Nat.count Nat.Prime 1150 = 189 := by
  rw [count_succ_prime, count_1149]; norm_num

lemma count_1151 : Nat.count Nat.Prime 1151 = 189 := by
  rw [count_succ_prime, count_1150]; norm_num

lemma count_1152 : Nat.count Nat.Prime 1152 = 190 := by
  rw [count_succ_prime, count_1151]; norm_num

lemma count_1153 : Nat.count Nat.Prime 1153 = 190 := by
  rw [count_succ_prime, count_1152]; norm_num

lemma count_1154 : Nat.count Nat.Prime 1154 = 191 := by
  rw [count_succ_prime, count_1153]; norm_num

lemma count_1155 : Nat.count Nat.Prime 1155 = 191 := by
  rw [count_succ_prime, count_1154]; norm_num

lemma count_1156 : Nat.count Nat.Prime 1156 = 191 := by
  rw [count_succ_prime, count_1155]; norm_num

lemma count_1157 : Nat.count Nat.Prime 1157 = 191 := by
  rw [count_succ_prime, count_1156]; norm_num

lemma count_1158 : Nat.count Nat.Prime 1158 = 191 := by
  rw [count_succ_prime, count_1157]; norm_num

lemma count_1159 : Nat.count Nat.Prime 1159 = 191 := by
  rw [count_succ_prime, count_1158]; norm_num

lemma count_1160 : Nat.count Nat.Prime 1160 = 191 := by
  rw [count_succ_prime, count_1159]; norm_num

lemma count_1161 : Nat.count Nat.Prime 1161 = 191 := by
  rw [count_succ_prime, count_1160]; norm_num

lemma count_1162 : Nat.count Nat.Prime 1162 = 191 := by
  rw [count_succ_prime, count_1161]; norm_num

lemma count_1163 : Nat.count Nat.Prime 1163 = 191 := by
  rw [count_succ_prime, count_1162]; norm_num

lemma count_1164 : Nat.count Nat.Prime 1164 = 192 := by
  rw [count_succ_prime, count_1163]; norm_num

lemma count_1165 : Nat.count Nat.Prime 1165 = 192 := by
  rw [count_succ_prime, count_1164]; norm_num

lemma count_1166 : Nat.count Nat.Prime 1166 = 192 := by
  rw [count_succ_prime, count_1165]; norm_num

lemma count_1167 : Nat.count Nat.Prime 1167 = 192 := by
  rw [count_succ_prime, count_1166]; norm_num

lemma count_1168 : Nat.count Nat.Prime 1168 = 192 := by
  rw [count_succ_prime, count_1167]; norm_num

lemma count_1169 : Nat.count Nat.Prime 1169 = 192 := by
  rw [count_succ_prime, count_1168]; norm_num

lemma count_1170 : Nat.count Nat.Prime 1170 = 192 := by
  rw [count_succ_prime, count_1169]; norm_num

lemma count_1171 : Nat.count Nat.Prime 1171 = 192 := by
  rw [count_succ_prime, count_1170]; norm_num

lemma count_1172 : Nat.count Nat.Prime 1172 = 193 := by
  rw [count_succ_prime, count_1171]; norm_num

lemma count_1173 : Nat.count Nat.Prime 1173 = 193 := by
  rw [count_succ_prime, count_1172]; norm_num

lemma count_1174 : Nat.count Nat.Prime 1174 = 193 := by
  rw [count_succ_prime, count_1173]; norm_num

lemma count_1175 : Nat.count Nat.Prime 1175 = 193 := by
  rw [count_succ_prime, count_1174]; norm_num

lemma count_1176 : Nat.count Nat.Prime 1176 = 193 := by
  rw [count_succ_prime, count_1175]; norm_num

lemma count_1177 : Nat.count Nat.Prime 1177 = 193 := by
  rw [count_succ_prime, count_1176]; norm_num

lemma count_1178 : Nat.count Nat.Prime 1178 = 193 := by
  rw [count_succ_prime, count_1177]; norm_num

lemma count_1179 : Nat.count Nat.Prime 1179 = 193 := by
  rw [count_succ_prime, count_1178]; norm_num

lemma count_1180 : Nat.count Nat.Prime 1180 = 193 := by
  rw [count_succ_prime, count_1179]; norm_num

lemma count_1181 : Nat.count Nat.Prime 1181 = 193 := by
  rw [count_succ_prime, count_1180]; norm_num

lemma count_1182 : Nat.count Nat.Prime 1182 = 194 := by
  rw [count_succ_prime, count_1181]; norm_num

lemma count_1183 : Nat.count Nat.Prime 1183 = 194 := by
  rw [count_succ_prime, count_1182]; norm_num

lemma count_1184 : Nat.count Nat.Prime 1184 = 194 := by
  rw [count_succ_prime, count_1183]; norm_num

lemma count_1185 : Nat.count Nat.Prime 1185 = 194 := by
  rw [count_succ_prime, count_1184]; norm_num

lemma count_1186 : Nat.count Nat.Prime 1186 = 194 := by
  rw [count_succ_prime, count_1185]; norm_num

lemma count_1187 : Nat.count Nat.Prime 1187 = 194 := by
  rw [count_succ_prime, count_1186]; norm_num

lemma count_1188 : Nat.count Nat.Prime 1188 = 195 := by
  rw [count_succ_prime, count_1187]; norm_num

lemma count_1189 : Nat.count Nat.Prime 1189 = 195 := by
  rw [count_succ_prime, count_1188]; norm_num

lemma count_1190 : Nat.count Nat.Prime 1190 = 195 := by
  rw [count_succ_prime, count_1189]; norm_num

lemma count_1191 : Nat.count Nat.Prime 1191 = 195 := by
  rw [count_succ_prime, count_1190]; norm_num

lemma count_1192 : Nat.count Nat.Prime 1192 = 195 := by
  rw [count_succ_prime, count_1191]; norm_num

lemma count_1193 : Nat.count Nat.Prime 1193 = 195 := by
  rw [count_succ_prime, count_1192]; norm_num

lemma count_1194 : Nat.count Nat.Prime 1194 = 196 := by
  rw [count_succ_prime, count_1193]; norm_num

lemma count_1195 : Nat.count Nat.Prime 1195 = 196 := by
  rw [count_succ_prime, count_1194]; norm_num

lemma count_1196 : Nat.count Nat.Prime 1196 = 196 := by
  rw [count_succ_prime, count_1195]; norm_num

lemma count_1197 : Nat.count Nat.Prime 1197 = 196 := by
  rw [count_succ_prime, count_1196]; norm_num

lemma count_1198 : Nat.count Nat.Prime 1198 = 196 := by
  rw [count_succ_prime, count_1197]; norm_num

lemma count_1199 : Nat.count Nat.Prime 1199 = 196 := by
  rw [count_succ_prime, count_1198]; norm_num

lemma count_1200 : Nat.count Nat.Prime 1200 = 196 := by
  rw [count_succ_prime, count_1199]; norm_num

lemma count_1201 : Nat.count Nat.Prime 1201 = 196 := by
  rw [count_succ_prime, count_1200]; norm_num

lemma count_1202 : Nat.count Nat.Prime 1202 = 197 := by
  rw [count_succ_prime, count_1201]; norm_num

lemma count_1203 : Nat.count Nat.Prime 1203 = 197 := by
  rw [count_succ_prime, count_1202]; norm_num

lemma count_1204 : Nat.count Nat.Prime 1204 = 197 := by
  rw [count_succ_prime, count_1203]; norm_num

lemma count_1205 : Nat.count Nat.Prime 1205 = 197 := by
  rw [count_succ_prime, count_1204]; norm_num

lemma count_1206 : Nat.count Nat.Prime 1206 = 197 := by
  rw [count_succ_prime, count_1205]; norm_num

lemma count_1207 : Nat.count Nat.Prime 1207 = 197 := by
  rw [count_succ_prime, count_1206]; norm_num

lemma count_1208 : Nat.count Nat.Prime 1208 = 197 := by
  rw [count_succ_prime, count_1207]; norm_num

lemma count_1209 : Nat.count Nat.Prime 1209 = 197 := by
  rw [count_succ_prime, count_1208]; norm_num

lemma count_1210 : Nat.count Nat.Prime 1210 = 197 := by
  rw [count_succ_prime, count_1209]; norm_num

lemma count_1211 : Nat.count Nat.Prime 1211 = 197 := by
  rw [count_succ_prime, count_1210]; norm_num

lemma count_1212 : Nat.count Nat.Prime 1212 = 197 := by
  rw [count_succ_prime, count_1211]; norm_num

lemma count_1213 : Nat.count Nat.Prime 1213 = 197 := by
  rw [count_succ_prime, count_1212]; norm_num

lemma count_1214 : Nat.count Nat.Prime 1214 = 198 := by
  rw [count_succ_prime, count_1213]; norm_num

lemma count_1215 : Nat.count Nat.Prime 1215 = 198 := by
  rw [count_succ_prime, count_1214]; norm_num

lemma count_1216 : Nat.count Nat.Prime 1216 = 198 := by
  rw [count_succ_prime, count_1215]; norm_num

lemma count_1217 : Nat.count Nat.Prime 1217 = 198 := by
  rw [count_succ_prime, count_1216]; norm_num

lemma count_1218 : Nat.count Nat.Prime 1218 = 199 := by
  rw [count_succ_prime, count_1217]; norm_num

lemma count_1219 : Nat.count Nat.Prime 1219 = 199 := by
  rw [count_succ_prime, count_1218]; norm_num

lemma count_1220 : Nat.count Nat.Prime 1220 = 199 := by
  rw [count_succ_prime, count_1219]; norm_num

lemma count_1221 : Nat.count Nat.Prime 1221 = 199 := by
  rw [count_succ_prime, count_1220]; norm_num

lemma count_1222 : Nat.count Nat.Prime 1222 = 199 := by
  rw [count_succ_prime, count_1221]; norm_num

lemma count_1223 : Nat.count Nat.Prime 1223 = 199 := by
  rw [count_succ_prime, count_1222]; norm_num

lemma nthP154 : Nat.nth Nat.Prime 154 = 907 :=
  nth_of_count (by norm_num) count_907

lemma nthP155 : Nat.nth Nat.Prime 155 = 911 :=
  nth_of_count (by norm_num) count_911

lemma nthP156 : Nat.nth Nat.Prime 156 = 919 :=
  nth_of_count (by norm_num) count_919

lemma nthP157 : Nat.nth Nat.Prime 157 = 929 :=
  nth_of_count (by norm_num) count_929

lemma nthP158 : Nat.nth Nat.Prime 158 = 937 :=
  nth_of_count (by norm_num) count_937

lemma nthP159 : Nat.nth Nat.Prime 159 = 941 :=
  nth_of_count (by norm_num) count_941

lemma nthP160 : Nat.nth Nat.Prime 160 = 947 :=
  nth_of_count (by norm_num) count_947

lemma nthP161 : Nat.nth Nat.Prime 161 = 953 :=
  nth_of_count (by norm_num) count_953

lemma nthP162 : Nat.nth Nat.Prime 162 = 967 :=
  nth_of_count (by norm_num) count_967

lemma nthP163 : Nat.nth Nat.Prime 163 = 971 :=
  nth_of_count (by norm_num) count_971

lemma nthP164 : Nat.nth Nat.Prime 164 = 977 :=
  nth_of_count (by norm_num) count_977

lemma nthP165 : Nat.nth Nat.Prime 165 = 983 :=
  nth_of_count (by norm_num) count_983

lemma nthP166 : Nat.nth Nat.Prime 166 = 991 :=
  nth_of_count (by norm_num) count_991

lemma nthP167 : Nat.nth Nat.Prime 167 = 997 :=
  nth_of_count (by norm_num) count_997

lemma nthP168 : Nat.nth Nat.Prime 168 = 1009 :=
  nth_of_count (by norm_num) count_1009

lemma nthP169 : Nat.nth Nat.Prime 169 = 1013 :=
  nth_of_count (by norm_num) count_1013

lemma nthP170 : Nat.nth Nat.Prime 170 = 1019 :=
  nth_of_count (by norm_num) count_1019

lemma nthP171 : Nat.nth Nat.Prime 171 = 1021 :=
  nth_of_count (by norm_num) count_1021

lemma nthP172 : Nat.nth Nat.Prime 172 = 1031 :=
  nth_of_count (by norm_num) count_1031

lemma nthP173 : Nat.nth Nat.Prime 173 = 1033 :=
  nth_of_count (by norm_num) count_1033

lemma nthP174 : Nat.nth Nat.Prime 174 = 1039 :=
  nth_of_count (by norm_num) count_1039

lemma nthP175 : Nat.nth Nat.Prime 175 = 1049 :=
  nth_of_count (by norm_num) count_1049

lemma nthP176 : Nat.nth Nat.Prime 176 = 1051 :=
  nth_of_count (by norm_num) count_1051

lemma nthP177 : Nat.nth Nat.Prime 177 = 1061 :=
  nth_of_count (by norm_num) count_1061

lemma nthP178 : Nat.nth Nat.Prime 178 = 1063 :=
  nth_of_count (by norm_num) count_1063

lemma nthP179 : Nat.nth Nat.Prime 179 = 1069 :=
  nth_of_count (by norm_num) count_1069

lemma nthP180 : Nat.nth Nat.Prime 180 = 1087 :=
  nth_of_count (by norm_num) count_1087

lemma nthP181 : Nat.nth Nat.Prime 181 = 1091 :=
  nth_of_count (by norm_num) count_1091

lemma nthP182 : Nat.nth Nat.Prime 182 = 1093 :=
  nth_of_count (by norm_num) count_1093

lemma nthP183 : Nat.nth Nat.Prime 183 = 1097 :=
  nth_of_count (by norm_num) count_1097

lemma nthP184 : Nat.nth Nat.Prime 184 = 1103 :=
  nth_of_count (by norm_num) count_1103

lemma nthP185 : Nat.nth Nat.Prime 185 = 1109 :=
  nth_of_count (by norm_num) count_1109

lemma nthP186 : Nat.nth Nat.Prime 186 = 1117 :=
  nth_of_count (by norm_num) count_1117

lemma nthP187 : Nat.nth Nat.Prime 187 = 1123 :=
  nth_of_count (by norm_num) count_1123

lemma nthP188 : Nat.nth Nat.Prime 188 = 1129 :=
  nth_of_count (by norm_num) count_1129

lemma nthP189 : Nat.nth Nat.Prime 189 = 1151 :=
  nth_of_count (by norm_num) count_1151

lemma nthP190 : Nat.nth Nat.Prime 190 = 1153 :=
  nth_of_count (by norm_num) count_1153

lemma nthP191 : Nat.nth Nat.Prime 191 = 1163 :=
  nth_of_count (by norm_num) count_1163

lemma nthP192 : Nat.nth Nat.Prime 192 = 1171 :=
  nth_of_count (by norm_num) count_1171

lemma nthP193 : Nat.nth Nat.Prime 193 = 1181 :=
  nth_of_count (by norm_num) count_1181

lemma nthP194 : Nat.nth Nat.Prime 194 = 1187 :=
  nth_of_count (by norm_num) count_1187

lemma nthP195 : Nat.nth Nat.Prime 195 = 1193 :=
  nth_of_count (by norm_num) count_1193

lemma nthP196 : Nat.nth Nat.Prime 196 = 1201 :=
  nth_of_count (by norm_num) count_1201

lemma nthP197 : Nat.nth Nat.Prime 197 = 1213 :=
  nth_of_count (by norm_num) count_1213

lemma nthP198 : Nat.nth Nat.Prime 198 = 1217 :=
  nth_of_count (by norm_num) count_1217

lemma nthP199 : Nat.nth Nat.Prime 199 = 1223 :=
  nth_of_count (by norm_num) count_1223

lemma a_ge_two_155 : 2 ≤ a 155 :=
  a_ge_two_of_hits 155 5 13 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP4, nthP154]; norm_num)
    (by rw [nthP12, nthP154]; norm_num)

lemma a_ge_two_156 : 2 ≤ a 156 :=
  a_ge_two_of_hits 156 2 5 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP1, nthP155]; norm_num)
    (by rw [nthP4, nthP155]; norm_num)

lemma a_ge_two_157 : 2 ≤ a 157 :=
  a_ge_two_of_hits 157 19 61 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP18, nthP156]; norm_num)
    (by rw [nthP60, nthP156]; norm_num)

lemma a_ge_two_158 : 2 ≤ a 158 :=
  a_ge_two_of_hits 158 23 31 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP22, nthP157]; norm_num)
    (by rw [nthP30, nthP157]; norm_num)

lemma a_ge_two_159 : 2 ≤ a 159 :=
  a_ge_two_of_hits 159 3 11 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP158]; norm_num)
    (by rw [nthP10, nthP158]; norm_num)

lemma a_ge_two_160 : 2 ≤ a 160 :=
  a_ge_two_of_hits 160 5 7 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP4, nthP159]; norm_num)
    (by rw [nthP6, nthP159]; norm_num)

lemma a_ge_two_161 : 2 ≤ a 161 :=
  a_ge_two_of_hits 161 41 53 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP40, nthP160]; norm_num)
    (by rw [nthP52, nthP160]; norm_num)

lemma a_ge_two_162 : 2 ≤ a 162 :=
  a_ge_two_of_hits 162 2 3 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP1, nthP161]; norm_num)
    (by rw [nthP2, nthP161]; norm_num)

lemma a_ge_two_163 : 2 ≤ a 163 :=
  a_ge_two_of_hits 163 11 13 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP10, nthP162]; norm_num)
    (by rw [nthP12, nthP162]; norm_num)

lemma a_ge_two_164 : 2 ≤ a 164 :=
  a_ge_two_of_hits 164 11 19 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP10, nthP163]; norm_num)
    (by rw [nthP18, nthP163]; norm_num)

lemma a_ge_two_165 : 2 ≤ a 165 :=
  a_ge_two_of_hits 165 13 17 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP12, nthP164]; norm_num)
    (by rw [nthP16, nthP164]; norm_num)

lemma a_ge_two_166 : 2 ≤ a 166 :=
  a_ge_two_of_hits 166 2 71 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP1, nthP165]; norm_num)
    (by rw [nthP70, nthP165]; norm_num)

lemma a_ge_two_167 : 2 ≤ a 167 :=
  a_ge_two_of_hits 167 11 17 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP10, nthP166]; norm_num)
    (by rw [nthP16, nthP166]; norm_num)

lemma a_ge_two_168 : 2 ≤ a 168 :=
  a_ge_two_of_hits 168 29 47 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP28, nthP167]; norm_num)
    (by rw [nthP46, nthP167]; norm_num)

lemma a_ge_two_169 : 2 ≤ a 169 :=
  a_ge_two_of_hits 169 3 31 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP168]; norm_num)
    (by rw [nthP30, nthP168]; norm_num)

lemma a_ge_two_170 : 2 ≤ a 170 :=
  a_ge_two_of_hits 170 7 37 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP6, nthP169]; norm_num)
    (by rw [nthP36, nthP169]; norm_num)

lemma a_ge_two_171 : 2 ≤ a 171 :=
  a_ge_two_of_hits 171 3 7 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP170]; norm_num)
    (by rw [nthP6, nthP170]; norm_num)

lemma a_ge_two_172 : 2 ≤ a 172 :=
  a_ge_two_of_hits 172 5 13 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP4, nthP171]; norm_num)
    (by rw [nthP12, nthP171]; norm_num)

lemma a_ge_two_173 : 2 ≤ a 173 :=
  a_ge_two_of_hits 173 7 23 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP6, nthP172]; norm_num)
    (by rw [nthP22, nthP172]; norm_num)

lemma a_ge_two_174 : 2 ≤ a 174 :=
  a_ge_two_of_hits 174 7 31 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP6, nthP173]; norm_num)
    (by rw [nthP30, nthP173]; norm_num)

lemma a_ge_two_175 : 2 ≤ a 175 :=
  a_ge_two_of_hits 175 3 7 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP174]; norm_num)
    (by rw [nthP6, nthP174]; norm_num)

lemma a_ge_two_176 : 2 ≤ a 176 :=
  a_ge_two_of_hits 176 2 7 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP1, nthP175]; norm_num)
    (by rw [nthP6, nthP175]; norm_num)

lemma a_ge_two_177 : 2 ≤ a 177 :=
  a_ge_two_of_hits 177 11 29 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP10, nthP176]; norm_num)
    (by rw [nthP28, nthP176]; norm_num)

lemma a_ge_two_178 : 2 ≤ a 178 :=
  a_ge_two_of_hits 178 11 17 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP10, nthP177]; norm_num)
    (by rw [nthP16, nthP177]; norm_num)

lemma a_ge_two_179 : 2 ≤ a 179 :=
  a_ge_two_of_hits 179 19 37 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP18, nthP178]; norm_num)
    (by rw [nthP36, nthP178]; norm_num)

lemma a_ge_two_180 : 2 ≤ a 180 :=
  a_ge_two_of_hits 180 7 37 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP6, nthP179]; norm_num)
    (by rw [nthP36, nthP179]; norm_num)

lemma a_ge_two_181 : 2 ≤ a 181 :=
  a_ge_two_of_hits 181 3 29 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP180]; norm_num)
    (by rw [nthP28, nthP180]; norm_num)

lemma a_ge_two_182 : 2 ≤ a 182 :=
  a_ge_two_of_hits 182 7 11 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP6, nthP181]; norm_num)
    (by rw [nthP10, nthP181]; norm_num)

lemma a_ge_two_183 : 2 ≤ a 183 :=
  a_ge_two_of_hits 183 7 37 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP6, nthP182]; norm_num)
    (by rw [nthP36, nthP182]; norm_num)

lemma a_ge_two_184 : 2 ≤ a 184 :=
  a_ge_two_of_hits 184 3 5 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP183]; norm_num)
    (by rw [nthP4, nthP183]; norm_num)

lemma a_ge_two_185 : 2 ≤ a 185 :=
  a_ge_two_of_hits 185 2 103 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP1, nthP184]; norm_num)
    (by rw [nthP102, nthP184]; norm_num)

lemma a_ge_two_186 : 2 ≤ a 186 :=
  a_ge_two_of_hits 186 31 61 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP30, nthP185]; norm_num)
    (by rw [nthP60, nthP185]; norm_num)

lemma a_ge_two_187 : 2 ≤ a 187 :=
  a_ge_two_of_hits 187 43 53 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP42, nthP186]; norm_num)
    (by rw [nthP52, nthP186]; norm_num)

lemma a_ge_two_188 : 2 ≤ a 188 :=
  a_ge_two_of_hits 188 19 71 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP18, nthP187]; norm_num)
    (by rw [nthP70, nthP187]; norm_num)

lemma a_ge_two_189 : 2 ≤ a 189 :=
  a_ge_two_of_hits 189 3 7 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP188]; norm_num)
    (by rw [nthP6, nthP188]; norm_num)

lemma a_ge_two_190 : 2 ≤ a 190 :=
  a_ge_two_of_hits 190 5 11 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP4, nthP189]; norm_num)
    (by rw [nthP10, nthP189]; norm_num)

lemma a_ge_two_191 : 2 ≤ a 191 :=
  a_ge_two_of_hits 191 23 31 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP22, nthP190]; norm_num)
    (by rw [nthP30, nthP190]; norm_num)

lemma a_ge_two_192 : 2 ≤ a 192 :=
  a_ge_two_of_hits 192 7 103 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP6, nthP191]; norm_num)
    (by rw [nthP102, nthP191]; norm_num)

lemma a_ge_two_193 : 2 ≤ a 193 :=
  a_ge_two_of_hits 193 5 11 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP4, nthP192]; norm_num)
    (by rw [nthP10, nthP192]; norm_num)

lemma a_ge_two_194 : 2 ≤ a 194 :=
  a_ge_two_of_hits 194 11 31 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP10, nthP193]; norm_num)
    (by rw [nthP30, nthP193]; norm_num)

lemma a_ge_two_195 : 2 ≤ a 195 :=
  a_ge_two_of_hits 195 11 17 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP10, nthP194]; norm_num)
    (by rw [nthP16, nthP194]; norm_num)

lemma a_ge_two_196 : 2 ≤ a 196 :=
  a_ge_two_of_hits 196 7 23 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP6, nthP195]; norm_num)
    (by rw [nthP22, nthP195]; norm_num)

lemma a_ge_two_197 : 2 ≤ a 197 :=
  a_ge_two_of_hits 197 11 13 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP10, nthP196]; norm_num)
    (by rw [nthP12, nthP196]; norm_num)

lemma a_ge_two_198 : 2 ≤ a 198 :=
  a_ge_two_of_hits 198 3 23 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP2, nthP197]; norm_num)
    (by rw [nthP22, nthP197]; norm_num)

lemma a_ge_two_199 : 2 ≤ a 199 :=
  a_ge_two_of_hits 199 5 11 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP4, nthP198]; norm_num)
    (by rw [nthP10, nthP198]; norm_num)

lemma a_ge_two_200 : 2 ≤ a 200 :=
  a_ge_two_of_hits 200 2 7 (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by rw [nthP1, nthP199]; norm_num)
    (by rw [nthP6, nthP199]; norm_num)

lemma a_ge_two_155_164 (n : ℕ) (h1 : 155 ≤ n) (h2 : n ≤ 164) : 2 ≤ a n := by
  interval_cases n
  · exact a_ge_two_155
  · exact a_ge_two_156
  · exact a_ge_two_157
  · exact a_ge_two_158
  · exact a_ge_two_159
  · exact a_ge_two_160
  · exact a_ge_two_161
  · exact a_ge_two_162
  · exact a_ge_two_163
  · exact a_ge_two_164

lemma a_ge_two_165_174 (n : ℕ) (h1 : 165 ≤ n) (h2 : n ≤ 174) : 2 ≤ a n := by
  interval_cases n
  · exact a_ge_two_165
  · exact a_ge_two_166
  · exact a_ge_two_167
  · exact a_ge_two_168
  · exact a_ge_two_169
  · exact a_ge_two_170
  · exact a_ge_two_171
  · exact a_ge_two_172
  · exact a_ge_two_173
  · exact a_ge_two_174

lemma a_ge_two_175_184 (n : ℕ) (h1 : 175 ≤ n) (h2 : n ≤ 184) : 2 ≤ a n := by
  interval_cases n
  · exact a_ge_two_175
  · exact a_ge_two_176
  · exact a_ge_two_177
  · exact a_ge_two_178
  · exact a_ge_two_179
  · exact a_ge_two_180
  · exact a_ge_two_181
  · exact a_ge_two_182
  · exact a_ge_two_183
  · exact a_ge_two_184

lemma a_ge_two_185_194 (n : ℕ) (h1 : 185 ≤ n) (h2 : n ≤ 194) : 2 ≤ a n := by
  interval_cases n
  · exact a_ge_two_185
  · exact a_ge_two_186
  · exact a_ge_two_187
  · exact a_ge_two_188
  · exact a_ge_two_189
  · exact a_ge_two_190
  · exact a_ge_two_191
  · exact a_ge_two_192
  · exact a_ge_two_193
  · exact a_ge_two_194

lemma a_ge_two_195_200 (n : ℕ) (h1 : 195 ≤ n) (h2 : n ≤ 200) : 2 ≤ a n := by
  interval_cases n
  · exact a_ge_two_195
  · exact a_ge_two_196
  · exact a_ge_two_197
  · exact a_ge_two_198
  · exact a_ge_two_199
  · exact a_ge_two_200

lemma a_ge_two_155_200 (n : ℕ) (h1 : 155 ≤ n) (h2 : n ≤ 200) : 2 ≤ a n := by
  if h : n ≤ 164 then
    exact a_ge_two_155_164 n h1 h
  else if h2' : n ≤ 174 then
    exact a_ge_two_165_174 n (by omega) h2'
  else if h3 : n ≤ 184 then
    exact a_ge_two_175_184 n (by omega) h3
  else if h4 : n ≤ 194 then
    exact a_ge_two_185_194 n (by omega) h4
  else
    exact a_ge_two_195_200 n (by omega) h2


/-- The tail of both halves of the conjecture reduces to `2 ≤ a n` for `n > 100`. -/
lemma a_ge_two_of_gt_100 (n : ℕ) (hn : 100 < n) : 2 ≤ a n := by
  if hle : n ≤ 154 then
    exact a_ge_two_101_154 n (by omega) hle
  else if hle2 : n ≤ 200 then
    exact a_ge_two_155_200 n (by omega) hle2
  else
    -- Remaining infinite tail n > 200.
    have hmany := many_prime_indices hn
    have hp : Nat.Prime (Nat.nth Nat.Prime (n - 1)) := Nat.prime_nth_prime (n - 1)
    have hmpos : 0 < Nat.nth Nat.Prime (n - 1) - 1 := by
      have : 2 ≤ Nat.nth Nat.Prime (n - 1) := nthPrime_ge_two (n - 1)
      omega
    rw [a_eq_card]
    have : 2 ≤ #(((Ico 1 n).filter Nat.Prime).filter (fun k =>
        Nat.Prime (Nat.nth Nat.Prime (k - 1) ^ 2 +
          (Nat.nth Nat.Prime (n - 1) - 1) ^ 2))) := by
      have := hmany
      have := hp
      have := hmpos
      sorry
    exact this


theorem oeis_238585_conjecture_i :
  (∀ n : ℕ, n > 0 → (a n > 0 ↔ ¬ (n ∣ 6))) ∧
  (∀ n : ℕ, n > 0 → (a n = 1 ↔ n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 19 ∨ n = 21 ∨ n = 22 ∨ n = 31 ∨ n = 42 ∨ n = 44)) := by
  constructor
  · intro n hn
    by_cases h : n ≤ 100
    · exact a_pos_iff_of_le_100 n hn h
    · have hB : 100 < n := Nat.not_le.mp h
      have hnd : ¬ n ∣ 6 := by
        intro hd
        have : n ≤ 6 := Nat.le_of_dvd (by decide) hd
        omega
      simp [hnd]
      have : 2 ≤ a n := a_ge_two_of_gt_100 n hB
      omega
  · intro n hn
    by_cases h : n ≤ 100
    · exact a_eq_one_iff_of_le_100 n hn h
    · have hB : 100 < n := Nat.not_le.mp h
      have hnot : ¬ (n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨
        n = 19 ∨ n = 21 ∨ n = 22 ∨ n = 31 ∨ n = 42 ∨ n = 44) := by omega
      simp [hnot]
      have : 2 ≤ a n := a_ge_two_of_gt_100 n hB
      omega
