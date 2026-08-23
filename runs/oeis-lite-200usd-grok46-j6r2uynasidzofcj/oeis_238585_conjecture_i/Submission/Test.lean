import FormalConjectures.Util.ProblemImports

open Nat Finset

set_option maxRecDepth 20000
set_option maxHeartbeats 80000000

/--
A238585: Number of primes $p < n$ with $\text{prime}(p)^2 + (\text{prime}(n)-1)^2$ prime.
(where $\text{prime}(i)$ is the $i$-th prime number, 1-indexed).
-/
noncomputable def a (n : ℕ) : ℕ :=
  Finset.Ico 1 n |>.sum fun k : ℕ =>
    let P_k := Nat.nth Nat.Prime (k - 1)
    let P_n := Nat.nth Nat.Prime (n - 1)
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
  simp only [mem_filter, mem_insert, mem_singleton]
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

lemma a_filter_8 :
    {x ∈ ({2, 3, 5, 7} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (19 - 1) ^ 2)} = {3, 7} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · simp
    · rw [nthP4] at hp; norm_num at hp
    · simp
  · intro h
    rcases h with rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP2]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP6]; norm_num

lemma a_val_8 : a 8 = 2 := by
  rw [a_eq_card, primes_lt_8, nthP7, a_filter_8]
  decide

lemma a_filter_9 :
    {x ∈ ({2, 3, 5, 7} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (23 - 1) ^ 2)} = {3, 7} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · simp
    · rw [nthP4] at hp; norm_num at hp
    · simp
  · intro h
    rcases h with rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP2]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP6]; norm_num

lemma a_val_9 : a 9 = 2 := by
  rw [a_eq_card, primes_lt_9, nthP8, a_filter_9]
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

lemma a_filter_13 :
    {x ∈ ({2, 3, 5, 7, 11} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (41 - 1) ^ 2)} = {2, 5, 7} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl
    · simp
    · rw [nthP2] at hp; norm_num at hp
    · simp
    · simp
    · rw [nthP10] at hp; norm_num at hp
  · intro h
    rcases h with rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP1]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP4]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP6]; norm_num

lemma a_val_13 : a 13 = 3 := by
  rw [a_eq_card, primes_lt_13, nthP12, a_filter_13]
  decide

lemma a_filter_14 :
    {x ∈ ({2, 3, 5, 7, 11, 13} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (43 - 1) ^ 2)} = {3, 7} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · simp
    · rw [nthP4] at hp; norm_num at hp
    · simp
    · rw [nthP10] at hp; norm_num at hp
    · rw [nthP12] at hp; norm_num at hp
  · intro h
    rcases h with rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP2]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP6]; norm_num

lemma a_val_14 : a 14 = 2 := by
  rw [a_eq_card, primes_lt_14, nthP13, a_filter_14]
  decide

lemma a_filter_15 :
    {x ∈ ({2, 3, 5, 7, 11, 13} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (47 - 1) ^ 2)} = {3, 5, 13} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · simp
    · simp
    · rw [nthP6] at hp; norm_num at hp
    · rw [nthP10] at hp; norm_num at hp
    · simp
  · intro h
    rcases h with rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP2]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP4]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP12]; norm_num

lemma a_val_15 : a 15 = 3 := by
  rw [a_eq_card, primes_lt_15, nthP14, a_filter_15]
  decide

lemma a_filter_16 :
    {x ∈ ({2, 3, 5, 7, 11, 13} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (53 - 1) ^ 2)} = {2, 3} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · rw [nthP4] at hp; norm_num at hp
    · rw [nthP6] at hp; norm_num at hp
    · rw [nthP10] at hp; norm_num at hp
    · rw [nthP12] at hp; norm_num at hp
  · intro h
    rcases h with rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP1]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP2]; norm_num

lemma a_val_16 : a 16 = 2 := by
  rw [a_eq_card, primes_lt_16, nthP15, a_filter_16]
  decide

lemma a_filter_17 :
    {x ∈ ({2, 3, 5, 7, 11, 13} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (59 - 1) ^ 2)} = {2, 3} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · rw [nthP4] at hp; norm_num at hp
    · rw [nthP6] at hp; norm_num at hp
    · rw [nthP10] at hp; norm_num at hp
    · rw [nthP12] at hp; norm_num at hp
  · intro h
    rcases h with rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP1]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP2]; norm_num

lemma a_val_17 : a 17 = 2 := by
  rw [a_eq_card, primes_lt_17, nthP16, a_filter_17]
  decide

lemma a_filter_18 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (61 - 1) ^ 2)} = {7, 11, 13} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · rw [nthP2] at hp; norm_num at hp
    · rw [nthP4] at hp; norm_num at hp
    · simp
    · simp
    · simp
    · rw [nthP16] at hp; norm_num at hp
  · intro h
    rcases h with rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP6]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP10]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP12]; norm_num

lemma a_val_18 : a 18 = 3 := by
  rw [a_eq_card, primes_lt_18, nthP17, a_filter_18]
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

lemma a_filter_20 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (71 - 1) ^ 2)} = {2, 5, 7, 11, 13} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · rw [nthP2] at hp; norm_num at hp
    · simp
    · simp
    · simp
    · simp
    · rw [nthP16] at hp; norm_num at hp
    · rw [nthP18] at hp; norm_num at hp
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP1]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP4]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP6]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP10]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP12]; norm_num

lemma a_val_20 : a 20 = 5 := by
  rw [a_eq_card, primes_lt_20, nthP19, a_filter_20]
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

lemma a_filter_23 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (83 - 1) ^ 2)} = {2, 7, 19} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · rw [nthP2] at hp; norm_num at hp
    · rw [nthP4] at hp; norm_num at hp
    · simp
    · rw [nthP10] at hp; norm_num at hp
    · rw [nthP12] at hp; norm_num at hp
    · rw [nthP16] at hp; norm_num at hp
    · simp
  · intro h
    rcases h with rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP1]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP6]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP18]; norm_num

lemma a_val_23 : a 23 = 3 := by
  rw [a_eq_card, primes_lt_23, nthP22, a_filter_23]
  decide

lemma a_filter_24 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (89 - 1) ^ 2)} = {2, 23} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · rw [nthP2] at hp; norm_num at hp
    · rw [nthP4] at hp; norm_num at hp
    · rw [nthP6] at hp; norm_num at hp
    · rw [nthP10] at hp; norm_num at hp
    · rw [nthP12] at hp; norm_num at hp
    · rw [nthP16] at hp; norm_num at hp
    · rw [nthP18] at hp; norm_num at hp
    · simp
  · intro h
    rcases h with rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP1]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP22]; norm_num

lemma a_val_24 : a 24 = 2 := by
  rw [a_eq_card, primes_lt_24, nthP23, a_filter_24]
  decide

lemma a_filter_25 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (97 - 1) ^ 2)} = {3, 5, 11, 17} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · simp
    · simp
    · rw [nthP6] at hp; norm_num at hp
    · simp
    · rw [nthP12] at hp; norm_num at hp
    · simp
    · rw [nthP18] at hp; norm_num at hp
    · rw [nthP22] at hp; norm_num at hp
  · intro h
    rcases h with rfl | rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP2]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP4]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP10]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP16]; norm_num

lemma a_val_25 : a 25 = 4 := by
  rw [a_eq_card, primes_lt_25, nthP24, a_filter_25]
  decide

lemma a_filter_26 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (101 - 1) ^ 2)} = {2, 7, 13, 19, 23} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · rw [nthP2] at hp; norm_num at hp
    · rw [nthP4] at hp; norm_num at hp
    · simp
    · rw [nthP10] at hp; norm_num at hp
    · simp
    · rw [nthP16] at hp; norm_num at hp
    · simp
    · simp
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP1]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP6]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP12]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP18]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP22]; norm_num

lemma a_val_26 : a 26 = 5 := by
  rw [a_eq_card, primes_lt_26, nthP25, a_filter_26]
  decide

lemma a_filter_27 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (103 - 1) ^ 2)} = {3, 23} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · simp
    · rw [nthP4] at hp; norm_num at hp
    · rw [nthP6] at hp; norm_num at hp
    · rw [nthP10] at hp; norm_num at hp
    · rw [nthP12] at hp; norm_num at hp
    · rw [nthP16] at hp; norm_num at hp
    · rw [nthP18] at hp; norm_num at hp
    · simp
  · intro h
    rcases h with rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP2]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP22]; norm_num

lemma a_val_27 : a 27 = 2 := by
  rw [a_eq_card, primes_lt_27, nthP26, a_filter_27]
  decide

lemma a_filter_28 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (107 - 1) ^ 2)} = {3, 11, 13, 17} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · simp
    · rw [nthP4] at hp; norm_num at hp
    · rw [nthP6] at hp; norm_num at hp
    · simp
    · simp
    · simp
    · rw [nthP18] at hp; norm_num at hp
    · rw [nthP22] at hp; norm_num at hp
  · intro h
    rcases h with rfl | rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP2]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP10]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP12]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP16]; norm_num

lemma a_val_28 : a 28 = 4 := by
  rw [a_eq_card, primes_lt_28, nthP27, a_filter_28]
  decide

lemma a_filter_29 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (109 - 1) ^ 2)} = {3, 7, 23} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · simp
    · rw [nthP4] at hp; norm_num at hp
    · simp
    · rw [nthP10] at hp; norm_num at hp
    · rw [nthP12] at hp; norm_num at hp
    · rw [nthP16] at hp; norm_num at hp
    · rw [nthP18] at hp; norm_num at hp
    · simp
  · intro h
    rcases h with rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP2]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP6]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP22]; norm_num

lemma a_val_29 : a 29 = 3 := by
  rw [a_eq_card, primes_lt_29, nthP28, a_filter_29]
  decide

lemma a_filter_30 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (113 - 1) ^ 2)} = {2, 3, 19, 23} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · rw [nthP4] at hp; norm_num at hp
    · rw [nthP6] at hp; norm_num at hp
    · rw [nthP10] at hp; norm_num at hp
    · rw [nthP12] at hp; norm_num at hp
    · rw [nthP16] at hp; norm_num at hp
    · simp
    · simp
    · rw [nthP28] at hp; norm_num at hp
  · intro h
    rcases h with rfl | rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP1]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP2]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP18]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP22]; norm_num

lemma a_val_30 : a 30 = 4 := by
  rw [a_eq_card, primes_lt_30, nthP29, a_filter_30]
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

lemma a_filter_32 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (131 - 1) ^ 2)} = {5, 7, 23, 31} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · rw [nthP2] at hp; norm_num at hp
    · simp
    · simp
    · rw [nthP10] at hp; norm_num at hp
    · rw [nthP12] at hp; norm_num at hp
    · rw [nthP16] at hp; norm_num at hp
    · rw [nthP18] at hp; norm_num at hp
    · simp
    · rw [nthP28] at hp; norm_num at hp
    · simp
  · intro h
    rcases h with rfl | rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP4]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP6]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP22]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP30]; norm_num

lemma a_val_32 : a 32 = 4 := by
  rw [a_eq_card, primes_lt_32, nthP31, a_filter_32]
  decide

lemma a_filter_33 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (137 - 1) ^ 2)} = {3, 5, 11, 13, 17} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · simp
    · simp
    · rw [nthP6] at hp; norm_num at hp
    · simp
    · simp
    · simp
    · rw [nthP18] at hp; norm_num at hp
    · rw [nthP22] at hp; norm_num at hp
    · rw [nthP28] at hp; norm_num at hp
    · rw [nthP30] at hp; norm_num at hp
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP2]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP4]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP10]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP12]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP16]; norm_num

lemma a_val_33 : a 33 = 5 := by
  rw [a_eq_card, primes_lt_33, nthP32, a_filter_33]
  decide

lemma a_filter_34 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (139 - 1) ^ 2)} = {3, 7, 23} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · simp
    · rw [nthP4] at hp; norm_num at hp
    · simp
    · rw [nthP10] at hp; norm_num at hp
    · rw [nthP12] at hp; norm_num at hp
    · rw [nthP16] at hp; norm_num at hp
    · rw [nthP18] at hp; norm_num at hp
    · simp
    · rw [nthP28] at hp; norm_num at hp
    · rw [nthP30] at hp; norm_num at hp
  · intro h
    rcases h with rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP2]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP6]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP22]; norm_num

lemma a_val_34 : a 34 = 3 := by
  rw [a_eq_card, primes_lt_34, nthP33, a_filter_34]
  decide

lemma a_filter_35 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (149 - 1) ^ 2)} = {3, 7, 19, 23} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · simp
    · rw [nthP4] at hp; norm_num at hp
    · simp
    · rw [nthP10] at hp; norm_num at hp
    · rw [nthP12] at hp; norm_num at hp
    · rw [nthP16] at hp; norm_num at hp
    · simp
    · simp
    · rw [nthP28] at hp; norm_num at hp
    · rw [nthP30] at hp; norm_num at hp
  · intro h
    rcases h with rfl | rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP2]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP6]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP18]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP22]; norm_num

lemma a_val_35 : a 35 = 4 := by
  rw [a_eq_card, primes_lt_35, nthP34, a_filter_35]
  decide

lemma a_filter_36 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (151 - 1) ^ 2)} = {5, 13, 17, 23, 29, 31} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · rw [nthP2] at hp; norm_num at hp
    · simp
    · rw [nthP6] at hp; norm_num at hp
    · rw [nthP10] at hp; norm_num at hp
    · simp
    · simp
    · rw [nthP18] at hp; norm_num at hp
    · simp
    · simp
    · simp
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP4]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP12]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP16]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP22]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP28]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP30]; norm_num

lemma a_val_36 : a 36 = 6 := by
  rw [a_eq_card, primes_lt_36, nthP35, a_filter_36]
  decide

lemma a_filter_37 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (157 - 1) ^ 2)} = {13, 17, 29} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · rw [nthP2] at hp; norm_num at hp
    · rw [nthP4] at hp; norm_num at hp
    · rw [nthP6] at hp; norm_num at hp
    · rw [nthP10] at hp; norm_num at hp
    · simp
    · simp
    · rw [nthP18] at hp; norm_num at hp
    · rw [nthP22] at hp; norm_num at hp
    · simp
    · rw [nthP30] at hp; norm_num at hp
  · intro h
    rcases h with rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP12]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP16]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP28]; norm_num

lemma a_val_37 : a 37 = 3 := by
  rw [a_eq_card, primes_lt_37, nthP36, a_filter_37]
  decide

lemma a_filter_38 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (163 - 1) ^ 2)} = {31, 37} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · rw [nthP2] at hp; norm_num at hp
    · rw [nthP4] at hp; norm_num at hp
    · rw [nthP6] at hp; norm_num at hp
    · rw [nthP10] at hp; norm_num at hp
    · rw [nthP12] at hp; norm_num at hp
    · rw [nthP16] at hp; norm_num at hp
    · rw [nthP18] at hp; norm_num at hp
    · rw [nthP22] at hp; norm_num at hp
    · rw [nthP28] at hp; norm_num at hp
    · simp
    · simp
  · intro h
    rcases h with rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP30]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP36]; norm_num

lemma a_val_38 : a 38 = 2 := by
  rw [a_eq_card, primes_lt_38, nthP37, a_filter_38]
  decide

lemma a_filter_39 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (167 - 1) ^ 2)} = {3, 11} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · simp
    · rw [nthP4] at hp; norm_num at hp
    · rw [nthP6] at hp; norm_num at hp
    · simp
    · rw [nthP12] at hp; norm_num at hp
    · rw [nthP16] at hp; norm_num at hp
    · rw [nthP18] at hp; norm_num at hp
    · rw [nthP22] at hp; norm_num at hp
    · rw [nthP28] at hp; norm_num at hp
    · rw [nthP30] at hp; norm_num at hp
    · rw [nthP36] at hp; norm_num at hp
  · intro h
    rcases h with rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP2]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP10]; norm_num

lemma a_val_39 : a 39 = 2 := by
  rw [a_eq_card, primes_lt_39, nthP38, a_filter_39]
  decide

lemma a_filter_40 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (173 - 1) ^ 2)} = {7, 23} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · rw [nthP2] at hp; norm_num at hp
    · rw [nthP4] at hp; norm_num at hp
    · simp
    · rw [nthP10] at hp; norm_num at hp
    · rw [nthP12] at hp; norm_num at hp
    · rw [nthP16] at hp; norm_num at hp
    · rw [nthP18] at hp; norm_num at hp
    · simp
    · rw [nthP28] at hp; norm_num at hp
    · rw [nthP30] at hp; norm_num at hp
    · rw [nthP36] at hp; norm_num at hp
  · intro h
    rcases h with rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP6]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP22]; norm_num

lemma a_val_40 : a 40 = 2 := by
  rw [a_eq_card, primes_lt_40, nthP39, a_filter_40]
  decide

lemma a_filter_41 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (179 - 1) ^ 2)} = {7, 37} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · rw [nthP2] at hp; norm_num at hp
    · rw [nthP4] at hp; norm_num at hp
    · simp
    · rw [nthP10] at hp; norm_num at hp
    · rw [nthP12] at hp; norm_num at hp
    · rw [nthP16] at hp; norm_num at hp
    · rw [nthP18] at hp; norm_num at hp
    · rw [nthP22] at hp; norm_num at hp
    · rw [nthP28] at hp; norm_num at hp
    · rw [nthP30] at hp; norm_num at hp
    · simp
  · intro h
    rcases h with rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP6]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP36]; norm_num

lemma a_val_41 : a 41 = 2 := by
  rw [a_eq_card, primes_lt_41, nthP40, a_filter_41]
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

lemma a_filter_43 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (191 - 1) ^ 2)} = {2, 7, 11, 13, 17, 23, 29, 41} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · rw [nthP2] at hp; norm_num at hp
    · rw [nthP4] at hp; norm_num at hp
    · simp
    · simp
    · simp
    · simp
    · rw [nthP18] at hp; norm_num at hp
    · simp
    · simp
    · rw [nthP30] at hp; norm_num at hp
    · rw [nthP36] at hp; norm_num at hp
    · simp
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP1]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP6]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP10]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP12]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP16]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP22]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP28]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP40]; norm_num

lemma a_val_43 : a 43 = 8 := by
  rw [a_eq_card, primes_lt_43, nthP42, a_filter_43]
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

lemma a_le_44 (n : ℕ) (hn : 0 < n) (hle : n ≤ 44) :
    (a n > 0 ↔ ¬ n ∣ 6) ∧
    (a n = 1 ↔ n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨
      n = 19 ∨ n = 21 ∨ n = 22 ∨ n = 31 ∨ n = 42 ∨ n = 44) := by
  interval_cases n <;> simp [a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6,
    a_val_7, a_val_8, a_val_9, a_val_10, a_val_11, a_val_12, a_val_13, a_val_14,
    a_val_15, a_val_16, a_val_17, a_val_18, a_val_19, a_val_20, a_val_21, a_val_22,
    a_val_23, a_val_24, a_val_25, a_val_26, a_val_27, a_val_28, a_val_29, a_val_30,
    a_val_31, a_val_32, a_val_33, a_val_34, a_val_35, a_val_36, a_val_37, a_val_38,
    a_val_39, a_val_40, a_val_41, a_val_42, a_val_43, a_val_44]
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

lemma primes_lt_45 : (Ico 1 45).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43} := by
  have h := filter_prime_Ico_succ 44 (by decide)
  rw [show 44 + 1 = 45 from rfl] at h
  rw [h, primes_lt_44]
  have : ¬ Nat.Prime 44 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_46 : (Ico 1 46).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43} := by
  have h := filter_prime_Ico_succ 45 (by decide)
  rw [show 45 + 1 = 46 from rfl] at h
  rw [h, primes_lt_45]
  have : ¬ Nat.Prime 45 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_47 : (Ico 1 47).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43} := by
  have h := filter_prime_Ico_succ 46 (by decide)
  rw [show 46 + 1 = 47 from rfl] at h
  rw [h, primes_lt_46]
  have : ¬ Nat.Prime 46 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_48 : (Ico 1 48).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47} := by
  have h := filter_prime_Ico_succ 47 (by decide)
  rw [show 47 + 1 = 48 from rfl] at h
  rw [h, primes_lt_47]
  have : Nat.Prime 47 := by norm_num
  simp only [this, ite_true]
  decide

lemma primes_lt_49 : (Ico 1 49).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47} := by
  have h := filter_prime_Ico_succ 48 (by decide)
  rw [show 48 + 1 = 49 from rfl] at h
  rw [h, primes_lt_48]
  have : ¬ Nat.Prime 48 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_50 : (Ico 1 50).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47} := by
  have h := filter_prime_Ico_succ 49 (by decide)
  rw [show 49 + 1 = 50 from rfl] at h
  rw [h, primes_lt_49]
  have : ¬ Nat.Prime 49 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_51 : (Ico 1 51).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47} := by
  have h := filter_prime_Ico_succ 50 (by decide)
  rw [show 50 + 1 = 51 from rfl] at h
  rw [h, primes_lt_50]
  have : ¬ Nat.Prime 50 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_52 : (Ico 1 52).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47} := by
  have h := filter_prime_Ico_succ 51 (by decide)
  rw [show 51 + 1 = 52 from rfl] at h
  rw [h, primes_lt_51]
  have : ¬ Nat.Prime 51 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_53 : (Ico 1 53).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47} := by
  have h := filter_prime_Ico_succ 52 (by decide)
  rw [show 52 + 1 = 53 from rfl] at h
  rw [h, primes_lt_52]
  have : ¬ Nat.Prime 52 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_54 : (Ico 1 54).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53} := by
  have h := filter_prime_Ico_succ 53 (by decide)
  rw [show 53 + 1 = 54 from rfl] at h
  rw [h, primes_lt_53]
  have : Nat.Prime 53 := by norm_num
  simp only [this, ite_true]
  decide

lemma primes_lt_55 : (Ico 1 55).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53} := by
  have h := filter_prime_Ico_succ 54 (by decide)
  rw [show 54 + 1 = 55 from rfl] at h
  rw [h, primes_lt_54]
  have : ¬ Nat.Prime 54 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_56 : (Ico 1 56).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53} := by
  have h := filter_prime_Ico_succ 55 (by decide)
  rw [show 55 + 1 = 56 from rfl] at h
  rw [h, primes_lt_55]
  have : ¬ Nat.Prime 55 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_57 : (Ico 1 57).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53} := by
  have h := filter_prime_Ico_succ 56 (by decide)
  rw [show 56 + 1 = 57 from rfl] at h
  rw [h, primes_lt_56]
  have : ¬ Nat.Prime 56 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_58 : (Ico 1 58).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53} := by
  have h := filter_prime_Ico_succ 57 (by decide)
  rw [show 57 + 1 = 58 from rfl] at h
  rw [h, primes_lt_57]
  have : ¬ Nat.Prime 57 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_59 : (Ico 1 59).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53} := by
  have h := filter_prime_Ico_succ 58 (by decide)
  rw [show 58 + 1 = 59 from rfl] at h
  rw [h, primes_lt_58]
  have : ¬ Nat.Prime 58 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_60 : (Ico 1 60).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59} := by
  have h := filter_prime_Ico_succ 59 (by decide)
  rw [show 59 + 1 = 60 from rfl] at h
  rw [h, primes_lt_59]
  have : Nat.Prime 59 := by norm_num
  simp only [this, ite_true]
  decide

lemma primes_lt_61 : (Ico 1 61).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59} := by
  have h := filter_prime_Ico_succ 60 (by decide)
  rw [show 60 + 1 = 61 from rfl] at h
  rw [h, primes_lt_60]
  have : ¬ Nat.Prime 60 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_62 : (Ico 1 62).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61} := by
  have h := filter_prime_Ico_succ 61 (by decide)
  rw [show 61 + 1 = 62 from rfl] at h
  rw [h, primes_lt_61]
  have : Nat.Prime 61 := by norm_num
  simp only [this, ite_true]
  decide

lemma primes_lt_63 : (Ico 1 63).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61} := by
  have h := filter_prime_Ico_succ 62 (by decide)
  rw [show 62 + 1 = 63 from rfl] at h
  rw [h, primes_lt_62]
  have : ¬ Nat.Prime 62 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_64 : (Ico 1 64).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61} := by
  have h := filter_prime_Ico_succ 63 (by decide)
  rw [show 63 + 1 = 64 from rfl] at h
  rw [h, primes_lt_63]
  have : ¬ Nat.Prime 63 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_65 : (Ico 1 65).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61} := by
  have h := filter_prime_Ico_succ 64 (by decide)
  rw [show 64 + 1 = 65 from rfl] at h
  rw [h, primes_lt_64]
  have : ¬ Nat.Prime 64 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_66 : (Ico 1 66).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61} := by
  have h := filter_prime_Ico_succ 65 (by decide)
  rw [show 65 + 1 = 66 from rfl] at h
  rw [h, primes_lt_65]
  have : ¬ Nat.Prime 65 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_67 : (Ico 1 67).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61} := by
  have h := filter_prime_Ico_succ 66 (by decide)
  rw [show 66 + 1 = 67 from rfl] at h
  rw [h, primes_lt_66]
  have : ¬ Nat.Prime 66 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_68 : (Ico 1 68).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67} := by
  have h := filter_prime_Ico_succ 67 (by decide)
  rw [show 67 + 1 = 68 from rfl] at h
  rw [h, primes_lt_67]
  have : Nat.Prime 67 := by norm_num
  simp only [this, ite_true]
  decide

lemma primes_lt_69 : (Ico 1 69).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67} := by
  have h := filter_prime_Ico_succ 68 (by decide)
  rw [show 68 + 1 = 69 from rfl] at h
  rw [h, primes_lt_68]
  have : ¬ Nat.Prime 68 := by norm_num
  simp only [this, ite_false]

lemma primes_lt_70 : (Ico 1 70).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67} := by
  have h := filter_prime_Ico_succ 69 (by decide)
  rw [show 69 + 1 = 70 from rfl] at h
  rw [h, primes_lt_69]
  have : ¬ Nat.Prime 69 := by norm_num
  simp only [this, ite_false]

lemma a_filter_45 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (197 - 1) ^ 2)} = {17, 41, 43} := by
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
    · simp
    · rw [nthP18] at hp; norm_num at hp
    · rw [nthP22] at hp; norm_num at hp
    · rw [nthP28] at hp; norm_num at hp
    · rw [nthP30] at hp; norm_num at hp
    · rw [nthP36] at hp; norm_num at hp
    · simp
    · simp
  · intro h
    rcases h with rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP16]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP40]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP42]; norm_num

lemma a_val_45 : a 45 = 3 := by
  rw [a_eq_card, primes_lt_45, nthP44, a_filter_45]
  decide

lemma a_filter_46 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (199 - 1) ^ 2)} = {3, 23, 31, 37} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · simp
    · rw [nthP4] at hp; norm_num at hp
    · rw [nthP6] at hp; norm_num at hp
    · rw [nthP10] at hp; norm_num at hp
    · rw [nthP12] at hp; norm_num at hp
    · rw [nthP16] at hp; norm_num at hp
    · rw [nthP18] at hp; norm_num at hp
    · simp
    · rw [nthP28] at hp; norm_num at hp
    · simp
    · simp
    · rw [nthP40] at hp; norm_num at hp
    · rw [nthP42] at hp; norm_num at hp
  · intro h
    rcases h with rfl | rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP2]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP22]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP30]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP36]; norm_num

lemma a_val_46 : a 46 = 4 := by
  rw [a_eq_card, primes_lt_46, nthP45, a_filter_46]
  decide

lemma a_filter_47 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (211 - 1) ^ 2)} = {5, 7, 11, 17, 19, 23, 37} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · rw [nthP2] at hp; norm_num at hp
    · simp
    · simp
    · simp
    · rw [nthP12] at hp; norm_num at hp
    · simp
    · simp
    · simp
    · rw [nthP28] at hp; norm_num at hp
    · rw [nthP30] at hp; norm_num at hp
    · simp
    · rw [nthP40] at hp; norm_num at hp
    · rw [nthP42] at hp; norm_num at hp
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP4]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP6]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP10]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP16]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP18]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP22]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP36]; norm_num

lemma a_val_47 : a 47 = 7 := by
  rw [a_eq_card, primes_lt_47, nthP46, a_filter_47]
  decide

lemma a_filter_48 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (223 - 1) ^ 2)} = {19, 31} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · rw [nthP2] at hp; norm_num at hp
    · rw [nthP4] at hp; norm_num at hp
    · rw [nthP6] at hp; norm_num at hp
    · rw [nthP10] at hp; norm_num at hp
    · rw [nthP12] at hp; norm_num at hp
    · rw [nthP16] at hp; norm_num at hp
    · simp
    · rw [nthP22] at hp; norm_num at hp
    · rw [nthP28] at hp; norm_num at hp
    · simp
    · rw [nthP36] at hp; norm_num at hp
    · rw [nthP40] at hp; norm_num at hp
    · rw [nthP42] at hp; norm_num at hp
    · rw [nthP46] at hp; norm_num at hp
  · intro h
    rcases h with rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP18]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP30]; norm_num

lemma a_val_48 : a 48 = 2 := by
  rw [a_eq_card, primes_lt_48, nthP47, a_filter_48]
  decide

lemma a_filter_49 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (227 - 1) ^ 2)} = {5, 13, 41, 43, 47} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · rw [nthP2] at hp; norm_num at hp
    · simp
    · rw [nthP6] at hp; norm_num at hp
    · rw [nthP10] at hp; norm_num at hp
    · simp
    · rw [nthP16] at hp; norm_num at hp
    · rw [nthP18] at hp; norm_num at hp
    · rw [nthP22] at hp; norm_num at hp
    · rw [nthP28] at hp; norm_num at hp
    · rw [nthP30] at hp; norm_num at hp
    · rw [nthP36] at hp; norm_num at hp
    · simp
    · simp
    · simp
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP4]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP12]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP40]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP42]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP46]; norm_num

lemma a_val_49 : a 49 = 5 := by
  rw [a_eq_card, primes_lt_49, nthP48, a_filter_49]
  decide

lemma a_filter_50 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (229 - 1) ^ 2)} = {3, 19, 31} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · simp
    · rw [nthP4] at hp; norm_num at hp
    · rw [nthP6] at hp; norm_num at hp
    · rw [nthP10] at hp; norm_num at hp
    · rw [nthP12] at hp; norm_num at hp
    · rw [nthP16] at hp; norm_num at hp
    · simp
    · rw [nthP22] at hp; norm_num at hp
    · rw [nthP28] at hp; norm_num at hp
    · simp
    · rw [nthP36] at hp; norm_num at hp
    · rw [nthP40] at hp; norm_num at hp
    · rw [nthP42] at hp; norm_num at hp
    · rw [nthP46] at hp; norm_num at hp
  · intro h
    rcases h with rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP2]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP18]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP30]; norm_num

lemma a_val_50 : a 50 = 3 := by
  rw [a_eq_card, primes_lt_50, nthP49, a_filter_50]
  decide

lemma a_filter_51 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (233 - 1) ^ 2)} = {3, 19} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · simp
    · rw [nthP4] at hp; norm_num at hp
    · rw [nthP6] at hp; norm_num at hp
    · rw [nthP10] at hp; norm_num at hp
    · rw [nthP12] at hp; norm_num at hp
    · rw [nthP16] at hp; norm_num at hp
    · simp
    · rw [nthP22] at hp; norm_num at hp
    · rw [nthP28] at hp; norm_num at hp
    · rw [nthP30] at hp; norm_num at hp
    · rw [nthP36] at hp; norm_num at hp
    · rw [nthP40] at hp; norm_num at hp
    · rw [nthP42] at hp; norm_num at hp
    · rw [nthP46] at hp; norm_num at hp
  · intro h
    rcases h with rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP2]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP18]; norm_num

lemma a_val_51 : a 51 = 2 := by
  rw [a_eq_card, primes_lt_51, nthP50, a_filter_51]
  decide

lemma a_filter_52 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (239 - 1) ^ 2)} = {23, 37} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · rw [nthP2] at hp; norm_num at hp
    · rw [nthP4] at hp; norm_num at hp
    · rw [nthP6] at hp; norm_num at hp
    · rw [nthP10] at hp; norm_num at hp
    · rw [nthP12] at hp; norm_num at hp
    · rw [nthP16] at hp; norm_num at hp
    · rw [nthP18] at hp; norm_num at hp
    · simp
    · rw [nthP28] at hp; norm_num at hp
    · rw [nthP30] at hp; norm_num at hp
    · simp
    · rw [nthP40] at hp; norm_num at hp
    · rw [nthP42] at hp; norm_num at hp
    · rw [nthP46] at hp; norm_num at hp
  · intro h
    rcases h with rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP22]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP36]; norm_num

lemma a_val_52 : a 52 = 2 := by
  rw [a_eq_card, primes_lt_52, nthP51, a_filter_52]
  decide

lemma a_filter_53 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (241 - 1) ^ 2)} = {13, 23, 29, 47} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · rw [nthP2] at hp; norm_num at hp
    · rw [nthP4] at hp; norm_num at hp
    · rw [nthP6] at hp; norm_num at hp
    · rw [nthP10] at hp; norm_num at hp
    · simp
    · rw [nthP16] at hp; norm_num at hp
    · rw [nthP18] at hp; norm_num at hp
    · simp
    · simp
    · rw [nthP30] at hp; norm_num at hp
    · rw [nthP36] at hp; norm_num at hp
    · rw [nthP40] at hp; norm_num at hp
    · rw [nthP42] at hp; norm_num at hp
    · simp
  · intro h
    rcases h with rfl | rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP12]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP22]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP28]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP46]; norm_num

lemma a_val_53 : a 53 = 4 := by
  rw [a_eq_card, primes_lt_53, nthP52, a_filter_53]
  decide

lemma a_filter_54 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (251 - 1) ^ 2)} = {17, 23, 29, 37, 41, 43, 47} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · rw [nthP2] at hp; norm_num at hp
    · rw [nthP4] at hp; norm_num at hp
    · rw [nthP6] at hp; norm_num at hp
    · rw [nthP10] at hp; norm_num at hp
    · rw [nthP12] at hp; norm_num at hp
    · simp
    · rw [nthP18] at hp; norm_num at hp
    · simp
    · simp
    · rw [nthP30] at hp; norm_num at hp
    · simp
    · simp
    · simp
    · simp
    · rw [nthP52] at hp; norm_num at hp
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP16]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP22]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP28]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP36]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP40]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP42]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP46]; norm_num

lemma a_val_54 : a 54 = 7 := by
  rw [a_eq_card, primes_lt_54, nthP53, a_filter_54]
  decide

lemma a_filter_55 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (257 - 1) ^ 2)} = {5, 13, 29, 41} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · rw [nthP2] at hp; norm_num at hp
    · simp
    · rw [nthP6] at hp; norm_num at hp
    · rw [nthP10] at hp; norm_num at hp
    · simp
    · rw [nthP16] at hp; norm_num at hp
    · rw [nthP18] at hp; norm_num at hp
    · rw [nthP22] at hp; norm_num at hp
    · simp
    · rw [nthP30] at hp; norm_num at hp
    · rw [nthP36] at hp; norm_num at hp
    · simp
    · rw [nthP42] at hp; norm_num at hp
    · rw [nthP46] at hp; norm_num at hp
    · rw [nthP52] at hp; norm_num at hp
  · intro h
    rcases h with rfl | rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP4]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP12]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP28]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP40]; norm_num

lemma a_val_55 : a 55 = 4 := by
  rw [a_eq_card, primes_lt_55, nthP54, a_filter_55]
  decide

lemma a_filter_56 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (263 - 1) ^ 2)} = {3, 19, 23} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · simp
    · rw [nthP4] at hp; norm_num at hp
    · rw [nthP6] at hp; norm_num at hp
    · rw [nthP10] at hp; norm_num at hp
    · rw [nthP12] at hp; norm_num at hp
    · rw [nthP16] at hp; norm_num at hp
    · simp
    · simp
    · rw [nthP28] at hp; norm_num at hp
    · rw [nthP30] at hp; norm_num at hp
    · rw [nthP36] at hp; norm_num at hp
    · rw [nthP40] at hp; norm_num at hp
    · rw [nthP42] at hp; norm_num at hp
    · rw [nthP46] at hp; norm_num at hp
    · rw [nthP52] at hp; norm_num at hp
  · intro h
    rcases h with rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP2]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP18]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP22]; norm_num

lemma a_val_56 : a 56 = 3 := by
  rw [a_eq_card, primes_lt_56, nthP55, a_filter_56]
  decide

lemma a_filter_57 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (269 - 1) ^ 2)} = {3, 23} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · simp
    · rw [nthP4] at hp; norm_num at hp
    · rw [nthP6] at hp; norm_num at hp
    · rw [nthP10] at hp; norm_num at hp
    · rw [nthP12] at hp; norm_num at hp
    · rw [nthP16] at hp; norm_num at hp
    · rw [nthP18] at hp; norm_num at hp
    · simp
    · rw [nthP28] at hp; norm_num at hp
    · rw [nthP30] at hp; norm_num at hp
    · rw [nthP36] at hp; norm_num at hp
    · rw [nthP40] at hp; norm_num at hp
    · rw [nthP42] at hp; norm_num at hp
    · rw [nthP46] at hp; norm_num at hp
    · rw [nthP52] at hp; norm_num at hp
  · intro h
    rcases h with rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP2]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP22]; norm_num

lemma a_val_57 : a 57 = 2 := by
  rw [a_eq_card, primes_lt_57, nthP56, a_filter_57]
  decide

lemma a_filter_58 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (271 - 1) ^ 2)} = {7, 37, 53} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · rw [nthP2] at hp; norm_num at hp
    · rw [nthP4] at hp; norm_num at hp
    · simp
    · rw [nthP10] at hp; norm_num at hp
    · rw [nthP12] at hp; norm_num at hp
    · rw [nthP16] at hp; norm_num at hp
    · rw [nthP18] at hp; norm_num at hp
    · rw [nthP22] at hp; norm_num at hp
    · rw [nthP28] at hp; norm_num at hp
    · rw [nthP30] at hp; norm_num at hp
    · simp
    · rw [nthP40] at hp; norm_num at hp
    · rw [nthP42] at hp; norm_num at hp
    · rw [nthP46] at hp; norm_num at hp
    · simp
  · intro h
    rcases h with rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP6]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP36]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP52]; norm_num

lemma a_val_58 : a 58 = 3 := by
  rw [a_eq_card, primes_lt_58, nthP57, a_filter_58]
  decide

lemma a_filter_59 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (277 - 1) ^ 2)} = {11, 17, 41, 43, 53} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · rw [nthP2] at hp; norm_num at hp
    · rw [nthP4] at hp; norm_num at hp
    · rw [nthP6] at hp; norm_num at hp
    · simp
    · rw [nthP12] at hp; norm_num at hp
    · simp
    · rw [nthP18] at hp; norm_num at hp
    · rw [nthP22] at hp; norm_num at hp
    · rw [nthP28] at hp; norm_num at hp
    · rw [nthP30] at hp; norm_num at hp
    · rw [nthP36] at hp; norm_num at hp
    · simp
    · simp
    · rw [nthP46] at hp; norm_num at hp
    · simp
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP10]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP16]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP40]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP42]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP52]; norm_num

lemma a_val_59 : a 59 = 5 := by
  rw [a_eq_card, primes_lt_59, nthP58, a_filter_59]
  decide

lemma a_filter_60 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (281 - 1) ^ 2)} = {19, 29, 31, 37, 41, 47, 53} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · rw [nthP2] at hp; norm_num at hp
    · rw [nthP4] at hp; norm_num at hp
    · rw [nthP6] at hp; norm_num at hp
    · rw [nthP10] at hp; norm_num at hp
    · rw [nthP12] at hp; norm_num at hp
    · rw [nthP16] at hp; norm_num at hp
    · simp
    · rw [nthP22] at hp; norm_num at hp
    · simp
    · simp
    · simp
    · simp
    · rw [nthP42] at hp; norm_num at hp
    · simp
    · simp
    · rw [nthP58] at hp; norm_num at hp
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP18]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP28]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP30]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP36]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP40]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP46]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP52]; norm_num

lemma a_val_60 : a 60 = 7 := by
  rw [a_eq_card, primes_lt_60, nthP59, a_filter_60]
  decide

lemma a_filter_61 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (283 - 1) ^ 2)} = {3, 7, 23, 37, 59} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · simp
    · rw [nthP4] at hp; norm_num at hp
    · simp
    · rw [nthP10] at hp; norm_num at hp
    · rw [nthP12] at hp; norm_num at hp
    · rw [nthP16] at hp; norm_num at hp
    · rw [nthP18] at hp; norm_num at hp
    · simp
    · rw [nthP28] at hp; norm_num at hp
    · rw [nthP30] at hp; norm_num at hp
    · simp
    · rw [nthP40] at hp; norm_num at hp
    · rw [nthP42] at hp; norm_num at hp
    · rw [nthP46] at hp; norm_num at hp
    · rw [nthP52] at hp; norm_num at hp
    · simp
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP2]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP6]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP22]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP36]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP58]; norm_num

lemma a_val_61 : a 61 = 5 := by
  rw [a_eq_card, primes_lt_61, nthP60, a_filter_61]
  decide

lemma a_filter_62 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (293 - 1) ^ 2)} = {19, 23, 37} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · rw [nthP2] at hp; norm_num at hp
    · rw [nthP4] at hp; norm_num at hp
    · rw [nthP6] at hp; norm_num at hp
    · rw [nthP10] at hp; norm_num at hp
    · rw [nthP12] at hp; norm_num at hp
    · rw [nthP16] at hp; norm_num at hp
    · simp
    · simp
    · rw [nthP28] at hp; norm_num at hp
    · rw [nthP30] at hp; norm_num at hp
    · simp
    · rw [nthP40] at hp; norm_num at hp
    · rw [nthP42] at hp; norm_num at hp
    · rw [nthP46] at hp; norm_num at hp
    · rw [nthP52] at hp; norm_num at hp
    · rw [nthP58] at hp; norm_num at hp
    · rw [nthP60] at hp; norm_num at hp
  · intro h
    rcases h with rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP18]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP22]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP36]; norm_num

lemma a_val_62 : a 62 = 3 := by
  rw [a_eq_card, primes_lt_62, nthP61, a_filter_62]
  decide

lemma a_filter_63 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (307 - 1) ^ 2)} = {11, 13, 17, 29, 47, 53} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · rw [nthP2] at hp; norm_num at hp
    · rw [nthP4] at hp; norm_num at hp
    · rw [nthP6] at hp; norm_num at hp
    · simp
    · simp
    · simp
    · rw [nthP18] at hp; norm_num at hp
    · rw [nthP22] at hp; norm_num at hp
    · simp
    · rw [nthP30] at hp; norm_num at hp
    · rw [nthP36] at hp; norm_num at hp
    · rw [nthP40] at hp; norm_num at hp
    · rw [nthP42] at hp; norm_num at hp
    · simp
    · simp
    · rw [nthP58] at hp; norm_num at hp
    · rw [nthP60] at hp; norm_num at hp
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP10]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP12]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP16]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP28]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP46]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP52]; norm_num

lemma a_val_63 : a 63 = 6 := by
  rw [a_eq_card, primes_lt_63, nthP62, a_filter_63]
  decide

lemma a_filter_64 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (311 - 1) ^ 2)} = {5, 17, 29, 37, 53, 59} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · rw [nthP2] at hp; norm_num at hp
    · simp
    · rw [nthP6] at hp; norm_num at hp
    · rw [nthP10] at hp; norm_num at hp
    · rw [nthP12] at hp; norm_num at hp
    · simp
    · rw [nthP18] at hp; norm_num at hp
    · rw [nthP22] at hp; norm_num at hp
    · simp
    · rw [nthP30] at hp; norm_num at hp
    · simp
    · rw [nthP40] at hp; norm_num at hp
    · rw [nthP42] at hp; norm_num at hp
    · rw [nthP46] at hp; norm_num at hp
    · simp
    · simp
    · rw [nthP60] at hp; norm_num at hp
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP4]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP16]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP28]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP36]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP52]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP58]; norm_num

lemma a_val_64 : a 64 = 6 := by
  rw [a_eq_card, primes_lt_64, nthP63, a_filter_64]
  decide

lemma a_filter_65 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (313 - 1) ^ 2)} = {3, 19, 23, 37, 61} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · simp
    · rw [nthP4] at hp; norm_num at hp
    · rw [nthP6] at hp; norm_num at hp
    · rw [nthP10] at hp; norm_num at hp
    · rw [nthP12] at hp; norm_num at hp
    · rw [nthP16] at hp; norm_num at hp
    · simp
    · simp
    · rw [nthP28] at hp; norm_num at hp
    · rw [nthP30] at hp; norm_num at hp
    · simp
    · rw [nthP40] at hp; norm_num at hp
    · rw [nthP42] at hp; norm_num at hp
    · rw [nthP46] at hp; norm_num at hp
    · rw [nthP52] at hp; norm_num at hp
    · rw [nthP58] at hp; norm_num at hp
    · simp
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP2]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP18]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP22]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP36]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP60]; norm_num

lemma a_val_65 : a 65 = 5 := by
  rw [a_eq_card, primes_lt_65, nthP64, a_filter_65]
  decide

lemma a_filter_66 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (317 - 1) ^ 2)} = {3, 13, 43} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · simp
    · rw [nthP4] at hp; norm_num at hp
    · rw [nthP6] at hp; norm_num at hp
    · rw [nthP10] at hp; norm_num at hp
    · simp
    · rw [nthP16] at hp; norm_num at hp
    · rw [nthP18] at hp; norm_num at hp
    · rw [nthP22] at hp; norm_num at hp
    · rw [nthP28] at hp; norm_num at hp
    · rw [nthP30] at hp; norm_num at hp
    · rw [nthP36] at hp; norm_num at hp
    · rw [nthP40] at hp; norm_num at hp
    · simp
    · rw [nthP46] at hp; norm_num at hp
    · rw [nthP52] at hp; norm_num at hp
    · rw [nthP58] at hp; norm_num at hp
    · rw [nthP60] at hp; norm_num at hp
  · intro h
    rcases h with rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP2]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP12]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP42]; norm_num

lemma a_val_66 : a 66 = 3 := by
  rw [a_eq_card, primes_lt_66, nthP65, a_filter_66]
  decide

lemma a_filter_67 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (331 - 1) ^ 2)} = {13, 31, 43, 47} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · rw [nthP2] at hp; norm_num at hp
    · rw [nthP4] at hp; norm_num at hp
    · rw [nthP6] at hp; norm_num at hp
    · rw [nthP10] at hp; norm_num at hp
    · simp
    · rw [nthP16] at hp; norm_num at hp
    · rw [nthP18] at hp; norm_num at hp
    · rw [nthP22] at hp; norm_num at hp
    · rw [nthP28] at hp; norm_num at hp
    · simp
    · rw [nthP36] at hp; norm_num at hp
    · rw [nthP40] at hp; norm_num at hp
    · simp
    · simp
    · rw [nthP52] at hp; norm_num at hp
    · rw [nthP58] at hp; norm_num at hp
    · rw [nthP60] at hp; norm_num at hp
  · intro h
    rcases h with rfl | rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP12]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP30]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP42]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP46]; norm_num

lemma a_val_67 : a 67 = 4 := by
  rw [a_eq_card, primes_lt_67, nthP66, a_filter_67]
  decide

lemma a_filter_68 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (337 - 1) ^ 2)} = {3, 5, 13, 29, 43} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · simp
    · simp
    · rw [nthP6] at hp; norm_num at hp
    · rw [nthP10] at hp; norm_num at hp
    · simp
    · rw [nthP16] at hp; norm_num at hp
    · rw [nthP18] at hp; norm_num at hp
    · rw [nthP22] at hp; norm_num at hp
    · simp
    · rw [nthP30] at hp; norm_num at hp
    · rw [nthP36] at hp; norm_num at hp
    · rw [nthP40] at hp; norm_num at hp
    · simp
    · rw [nthP46] at hp; norm_num at hp
    · rw [nthP52] at hp; norm_num at hp
    · rw [nthP58] at hp; norm_num at hp
    · rw [nthP60] at hp; norm_num at hp
    · rw [nthP66] at hp; norm_num at hp
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP2]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP4]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP12]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP28]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP42]; norm_num

lemma a_val_68 : a 68 = 5 := by
  rw [a_eq_card, primes_lt_68, nthP67, a_filter_68]
  decide

lemma a_filter_69 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (347 - 1) ^ 2)} = {11, 53} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · rw [nthP2] at hp; norm_num at hp
    · rw [nthP4] at hp; norm_num at hp
    · rw [nthP6] at hp; norm_num at hp
    · simp
    · rw [nthP12] at hp; norm_num at hp
    · rw [nthP16] at hp; norm_num at hp
    · rw [nthP18] at hp; norm_num at hp
    · rw [nthP22] at hp; norm_num at hp
    · rw [nthP28] at hp; norm_num at hp
    · rw [nthP30] at hp; norm_num at hp
    · rw [nthP36] at hp; norm_num at hp
    · rw [nthP40] at hp; norm_num at hp
    · rw [nthP42] at hp; norm_num at hp
    · rw [nthP46] at hp; norm_num at hp
    · simp
    · rw [nthP58] at hp; norm_num at hp
    · rw [nthP60] at hp; norm_num at hp
    · rw [nthP66] at hp; norm_num at hp
  · intro h
    rcases h with rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP10]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP52]; norm_num

lemma a_val_69 : a 69 = 2 := by
  rw [a_eq_card, primes_lt_69, nthP68, a_filter_69]
  decide

lemma a_filter_70 :
    {x ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67} : Finset ℕ) |
      Nat.Prime (Nat.nth Nat.Prime (x - 1) ^ 2 + (349 - 1) ^ 2)} = {37, 61} := by
  apply Finset.ext
  intro x
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · intro ⟨hmem, hp⟩
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nthP1] at hp; norm_num at hp
    · rw [nthP2] at hp; norm_num at hp
    · rw [nthP4] at hp; norm_num at hp
    · rw [nthP6] at hp; norm_num at hp
    · rw [nthP10] at hp; norm_num at hp
    · rw [nthP12] at hp; norm_num at hp
    · rw [nthP16] at hp; norm_num at hp
    · rw [nthP18] at hp; norm_num at hp
    · rw [nthP22] at hp; norm_num at hp
    · rw [nthP28] at hp; norm_num at hp
    · rw [nthP30] at hp; norm_num at hp
    · simp
    · rw [nthP40] at hp; norm_num at hp
    · rw [nthP42] at hp; norm_num at hp
    · rw [nthP46] at hp; norm_num at hp
    · rw [nthP52] at hp; norm_num at hp
    · rw [nthP58] at hp; norm_num at hp
    · simp
    · rw [nthP66] at hp; norm_num at hp
  · intro h
    rcases h with rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP36]; norm_num
    · refine ⟨?_, ?_⟩
      · simp
      · rw [nthP60]; norm_num

lemma a_val_70 : a 70 = 2 := by
  rw [a_eq_card, primes_lt_70, nthP69, a_filter_70]
  decide

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

lemma a_ge_two_45_70 (n : ℕ) (h1 : 45 ≤ n) (h2 : n ≤ 70) : 2 ≤ a n := by
  interval_cases n <;> simp only [a_val_45, a_val_46, a_val_47, a_val_48, a_val_49,
    a_val_50, a_val_51, a_val_52, a_val_53, a_val_54, a_val_55, a_val_56, a_val_57,
    a_val_58, a_val_59, a_val_60, a_val_61, a_val_62, a_val_63, a_val_64, a_val_65,
    a_val_66, a_val_67, a_val_68, a_val_69, a_val_70] <;> decide
