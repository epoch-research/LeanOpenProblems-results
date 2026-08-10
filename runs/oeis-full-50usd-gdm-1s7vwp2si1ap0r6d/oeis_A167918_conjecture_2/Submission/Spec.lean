import FormalConjectures.Util.ProblemImports

open Nat Set

-- P i is the i-th prime, 1-indexed: p(i).
/-- P i is the i-th prime, 1-indexed: p(i). -/
noncomputable def P (i : ℕ) : ℕ := Nat.nth Nat.Prime (i - 1)

-- S i is $p_i + p_{i+1}$.
/-- S i is $p_i + p_{i+1}$. -/
noncomputable def S (i : ℕ) : ℕ := P i + P (i + 1)

/--
A167918: $a(n)$ is smallest index $k > n$ of $k$-th prime with $f(n,k):=(p(k)+p(k+1))/(p(n)+p(n+1))$ an integer $\ge 2$ ($n=1,2,...$).
-/
noncomputable def A167918 (n : ℕ) : ℕ :=
  if n = 0 then 0 -- The sequence is 1-indexed.
  else
    let D_n := S n
    -- The set of indices $k$ that satisfy the condition.
    -- Since $k > n$, the ratio of the sums must be $\ge 2$ if divisibility holds.
    let k_set : Set ℕ := { k : ℕ | k > n ∧ D_n ∣ S k }

    -- sInf returns the smallest element of the set.
    sInf k_set


theorem P_strictMonoOn : StrictMonoOn P (Ici 1) := by
  intro x hx y hy hxy
  rw [mem_Ici] at hx hy
  simp only [P]
  have hx1 : x - 1 < y - 1 := by omega
  exact (Nat.nth_lt_nth Nat.infinite_setOf_prime).mpr hx1

theorem S_strictMonoOn : StrictMonoOn S (Ici 1) := by
  intro x hx y hy hxy
  rw [mem_Ici] at hx hy
  simp only [S]
  have h1 : P x < P y := P_strictMonoOn (mem_Ici.mpr hx) (mem_Ici.mpr hy) hxy
  have h2 : P (x + 1) < P (y + 1) := by
    have hx1 : x + 1 ∈ Ici 1 := by
      rw [mem_Ici]
      omega
    have hy1 : y + 1 ∈ Ici 1 := by
      rw [mem_Ici]
      omega
    have hlt : x + 1 < y + 1 := by omega
    exact P_strictMonoOn hx1 hy1 hlt
  exact Nat.add_lt_add h1 h2

theorem S_zero : S 0 = 4 := by
  change P 0 + P 1 = 4
  change Nat.nth Nat.Prime 0 + Nat.nth Nat.Prime 0 = 4
  rw [nth_prime_zero_eq_two]

theorem S_one : S 1 = 5 := by
  change P 1 + P 2 = 5
  change Nat.nth Nat.Prime 0 + Nat.nth Nat.Prime 1 = 5
  rw [nth_prime_zero_eq_two, nth_prime_one_eq_three]

theorem S_ge_five (n : ℕ) (hn : n ≥ 1) : S n ≥ 5 := by
  have h_mono : S 1 ≤ S n := by
    rcases hn.eq_or_lt with rfl | h_lt
    · rfl
    · have h_lt2 : S 1 < S n := S_strictMonoOn (mem_Ici.mpr (by decide)) (mem_Ici.mpr hn) h_lt
      omega
  rw [S_one] at h_mono
  exact h_mono

theorem A167918_eq_of_S_eq {n k : ℕ} (hn : n > 0) (hk : k > n) (h_eq : S k = 2 * S n) : A167918 n = k := by
  have h_ne : n ≠ 0 := by omega
  change (if n = 0 then 0 else sInf { k : ℕ | k > n ∧ S n ∣ S k }) = k
  rw [if_neg h_ne]
  let k_set := { k : ℕ | k > n ∧ S n ∣ S k }
  have h_mem : k ∈ k_set := by
    change k > n ∧ S n ∣ S k
    refine ⟨hk, ?_⟩
    rw [h_eq]
    exact dvd_mul_left (S n) 2
  have h_nonempty : k_set.Nonempty := ⟨k, h_mem⟩
  have h_le : sInf k_set ≤ k := Nat.sInf_le h_mem
  have h_ge : sInf k_set ≥ k := by
    by_contra hc
    push_neg at hc
    have h_sinf_mem := Nat.sInf_mem h_nonempty
    change sInf k_set > n ∧ S n ∣ S (sInf k_set) at h_sinf_mem
    have hj_gt : sInf k_set > n := h_sinf_mem.1
    have hj_dvd : S n ∣ S (sInf k_set) := h_sinf_mem.2
    rcases hj_dvd with ⟨d, hd⟩
    have h_S_n_pos : S n > 0 := by
      have h_ge_five : S n ≥ 5 := S_ge_five n hn
      omega
    have h_S_j_pos : S (sInf k_set) > 0 := by
      have h_j_ge1 : sInf k_set ∈ Ici 1 := by
        simp only [mem_Ici]
        omega
      have h_ge_five : S (sInf k_set) ≥ 5 := S_ge_five (sInf k_set) (by omega)
      omega
    have hd_pos : d > 0 := by
      by_contra h_d_zero
      have : d = 0 := by omega
      subst this
      omega
    have h_S_j_gt : S (sInf k_set) > S n := by
      have hn_in : n ∈ Ici 1 := by simp [mem_Ici]; omega
      have hj_in : sInf k_set ∈ Ici 1 := by simp [mem_Ici]; omega
      exact S_strictMonoOn hn_in hj_in hj_gt
    have hd_ge_two : d ≥ 2 := by
      by_contra hc2
      have : d = 1 := by omega
      subst this
      omega
    have h_S_j_ge : S (sInf k_set) ≥ 2 * S n := by
      rw [hd]
      nlinarith
    have h_S_j_lt : S (sInf k_set) < S k := by
      have hj_in : sInf k_set ∈ Ici 1 := by simp [mem_Ici]; omega
      have hk_in : k ∈ Ici 1 := by simp [mem_Ici]; omega
      exact S_strictMonoOn hj_in hk_in hc
    rw [h_eq] at h_S_j_lt
    omega
  exact le_antisymm h_le h_ge

theorem S_A167918_eq_two_S_iff {n : ℕ} (hn : n > 0) : S (A167918 n) = 2 * S n ↔ ∃ k > n, S k = 2 * S n := by
  constructor
  · intro h
    have h_ne : n ≠ 0 := by omega
    use A167918 n
    constructor
    · change (if n = 0 then 0 else sInf { k | k > n ∧ S n ∣ S k }) > n
      rw [if_neg h_ne]
      let k_set := { k | k > n ∧ S n ∣ S k }
      have h_nonempty : k_set.Nonempty := by
        use A167918 n
        change (if n = 0 then 0 else sInf k_set) ∈ k_set
        rw [if_neg h_ne]
        apply Nat.sInf_mem
        by_contra hc
        have h_empty : k_set = ∅ := Set.not_nonempty_iff_eq_empty.mp hc
        have h_inf_eq_zero : sInf k_set = 0 := by
          rw [h_empty]
          exact Nat.sInf_empty
        have h_A_eq_zero : A167918 n = 0 := by
          change (if n = 0 then 0 else sInf k_set) = 0
          rw [if_neg h_ne, h_inf_eq_zero]
        rw [h_A_eq_zero] at h
        have h_S_zero : S 0 = 4 := S_zero
        have h_S_n : S n ≥ 5 := S_ge_five n hn
        omega
      have h_mem := Nat.sInf_mem h_nonempty
      change sInf k_set > n ∧ S n ∣ S (sInf k_set) at h_mem
      exact h_mem.1
    · exact h
  · rintro ⟨k, hk_gt, hk_eq⟩
    have h_eq_k : A167918 n = k := A167918_eq_of_S_eq hn hk_gt hk_eq
    rw [h_eq_k, hk_eq]

-- 13 is prime
theorem prime_thirteen : Nat.Prime 13 := by decide

-- count Prime 13 is 5
theorem count_prime_thirteen : Nat.count Nat.Prime 13 = 5 := by decide

theorem nth_prime_five : Nat.nth Nat.Prime 5 = 13 := by
  have h1 : Nat.nth Nat.Prime (Nat.count Nat.Prime 13) = 13 := Nat.nth_count prime_thirteen
  rw [count_prime_thirteen] at h1
  exact h1

theorem test_S3 : S 3 = 12 := by
  change P 3 + P 4 = 12
  change Nat.nth Nat.Prime 2 + Nat.nth Nat.Prime 3 = 12
  rw [nth_prime_two_eq_five, nth_prime_three_eq_seven]

theorem test_S4 : S 4 = 18 := by
  change P 4 + P 5 = 18
  change Nat.nth Nat.Prime 3 + Nat.nth Nat.Prime 4 = 18
  rw [nth_prime_three_eq_seven, nth_prime_four_eq_eleven]

theorem test_S5 : S 5 = 24 := by
  change P 5 + P 6 = 24
  change Nat.nth Nat.Prime 4 + Nat.nth Nat.Prime 5 = 24
  rw [nth_prime_four_eq_eleven, nth_prime_five]

theorem five_mem_k_set3 : 5 ∈ { k : ℕ | k > 3 ∧ S 3 ∣ S k } := by
  simp only [mem_setOf_eq]
  refine ⟨by decide, ?_⟩
  rw [test_S3, test_S5]
  use 2

theorem four_not_mem_k_set3 : 4 ∉ { k : ℕ | k > 3 ∧ S 3 ∣ S k } := by
  simp only [mem_setOf_eq, not_and]
  intro _
  rw [test_S3, test_S4]
  decide

theorem k_set3_nonempty : { k : ℕ | k > 3 ∧ S 3 ∣ S k }.Nonempty := by
  exact ⟨5, five_mem_k_set3⟩

theorem A167918_three_eq_five : A167918 3 = 5 := by
  change (if 3 = 0 then 0 else sInf { k | k > 3 ∧ S 3 ∣ S k }) = 5
  have h_ne : ¬3 = 0 := by decide
  rw [if_neg h_ne]
  have h_le : sInf { k | k > 3 ∧ S 3 ∣ S k } ≤ 5 := Nat.sInf_le five_mem_k_set3
  have h_ge : sInf { k | k > 3 ∧ S 3 ∣ S k } ≥ 5 := by
    by_contra hc
    push_neg at hc
    have h_mem := Nat.sInf_mem k_set3_nonempty
    simp only [mem_setOf_eq] at h_mem
    have h_gt : sInf { k | k > 3 ∧ S 3 ∣ S k } > 3 := h_mem.1
    have h_eq_four : sInf { k | k > 3 ∧ S 3 ∣ S k } = 4 := by omega
    rw [h_eq_four] at h_mem
    exact four_not_mem_k_set3 h_mem
  exact le_antisymm h_le h_ge

theorem solution_three : S (A167918 3) = 2 * S 3 := by
  rw [A167918_three_eq_five, test_S5, test_S3]


theorem prime_seventeen : Nat.Prime 17 := by decide
theorem count_prime_seventeen : Nat.count Nat.Prime 17 = 6 := by decide
theorem nth_prime_six : Nat.nth Nat.Prime 6 = 17 := by
  have h1 : Nat.nth Nat.Prime (Nat.count Nat.Prime 17) = 17 := Nat.nth_count prime_seventeen
  rw [count_prime_seventeen] at h1
  exact h1

theorem prime_nineteen : Nat.Prime 19 := by decide
theorem count_prime_nineteen : Nat.count Nat.Prime 19 = 7 := by decide
theorem nth_prime_seven : Nat.nth Nat.Prime 7 = 19 := by
  have h1 : Nat.nth Nat.Prime (Nat.count Nat.Prime 19) = 19 := Nat.nth_count prime_nineteen
  rw [count_prime_nineteen] at h1
  exact h1

theorem prime_twenty_three : Nat.Prime 23 := by decide
theorem count_prime_twenty_three : Nat.count Nat.Prime 23 = 8 := by decide
theorem nth_prime_eight : Nat.nth Nat.Prime 8 = 23 := by
  have h1 : Nat.nth Nat.Prime (Nat.count Nat.Prime 23) = 23 := Nat.nth_count prime_twenty_three
  rw [count_prime_twenty_three] at h1
  exact h1

theorem prime_twenty_nine : Nat.Prime 29 := by decide
theorem count_prime_twenty_nine : Nat.count Nat.Prime 29 = 9 := by decide
theorem nth_prime_nine : Nat.nth Nat.Prime 9 = 29 := by
  have h1 : Nat.nth Nat.Prime (Nat.count Nat.Prime 29) = 29 := Nat.nth_count prime_twenty_nine
  rw [count_prime_twenty_nine] at h1
  exact h1

theorem prime_thirty_one : Nat.Prime 31 := by decide
theorem count_prime_thirty_one : Nat.count Nat.Prime 31 = 10 := by decide
theorem nth_prime_ten : Nat.nth Nat.Prime 10 = 31 := by
  have h1 : Nat.nth Nat.Prime (Nat.count Nat.Prime 31) = 31 := Nat.nth_count prime_thirty_one
  rw [count_prime_thirty_one] at h1
  exact h1

theorem test_S6 : S 6 = 30 := by
  change P 6 + P 7 = 30
  change Nat.nth Nat.Prime 5 + Nat.nth Nat.Prime 6 = 30
  rw [nth_prime_five, nth_prime_six]

theorem test_S7 : S 7 = 36 := by
  change P 7 + P 8 = 36
  change Nat.nth Nat.Prime 6 + Nat.nth Nat.Prime 7 = 36
  rw [nth_prime_six, nth_prime_seven]

theorem test_S8 : S 8 = 42 := by
  change P 8 + P 9 = 42
  change Nat.nth Nat.Prime 7 + Nat.nth Nat.Prime 8 = 42
  rw [nth_prime_seven, nth_prime_eight]

theorem test_S9 : S 9 = 52 := by
  change P 9 + P 10 = 52
  change Nat.nth Nat.Prime 8 + Nat.nth Nat.Prime 9 = 52
  rw [nth_prime_eight, nth_prime_nine]

theorem test_S10 : S 10 = 60 := by
  change P 10 + P 11 = 60
  change Nat.nth Nat.Prime 9 + Nat.nth Nat.Prime 10 = 60
  rw [nth_prime_nine, nth_prime_ten]

theorem ten_mem_k_set6 : 10 ∈ { k : ℕ | k > 6 ∧ S 6 ∣ S k } := by
  simp only [mem_setOf_eq]
  refine ⟨by decide, ?_⟩
  rw [test_S6, test_S10]
  use 2

theorem seven_not_mem_k_set6 : 7 ∉ { k : ℕ | k > 6 ∧ S 6 ∣ S k } := by
  simp only [mem_setOf_eq, not_and]
  intro _
  rw [test_S6, test_S7]
  decide

theorem eight_not_mem_k_set6 : 8 ∉ { k : ℕ | k > 6 ∧ S 6 ∣ S k } := by
  simp only [mem_setOf_eq, not_and]
  intro _
  rw [test_S6, test_S8]
  decide

theorem nine_not_mem_k_set6 : 9 ∉ { k : ℕ | k > 6 ∧ S 6 ∣ S k } := by
  simp only [mem_setOf_eq, not_and]
  intro _
  rw [test_S6, test_S9]
  decide

theorem k_set6_nonempty : { k : ℕ | k > 6 ∧ S 6 ∣ S k }.Nonempty := by
  exact ⟨10, ten_mem_k_set6⟩

theorem A167918_six_eq_ten : A167918 6 = 10 := by
  change (if 6 = 0 then 0 else sInf { k | k > 6 ∧ S 6 ∣ S k }) = 10
  have h_ne : ¬6 = 0 := by decide
  rw [if_neg h_ne]
  have h_le : sInf { k | k > 6 ∧ S 6 ∣ S k } ≤ 10 := Nat.sInf_le ten_mem_k_set6
  have h_ge : sInf { k | k > 6 ∧ S 6 ∣ S k } ≥ 10 := by
    by_contra hc
    push_neg at hc
    have h_mem := Nat.sInf_mem k_set6_nonempty
    simp only [mem_setOf_eq] at h_mem
    have h_gt : sInf { k | k > 6 ∧ S 6 ∣ S k } > 6 := h_mem.1
    have h_eq : sInf { k | k > 6 ∧ S 6 ∣ S k } = 7 ∨ sInf { k | k > 6 ∧ S 6 ∣ S k } = 8 ∨ sInf { k | k > 6 ∧ S 6 ∣ S k } = 9 := by omega
    rcases h_eq with h_eq_seven | h_eq_eight | h_eq_nine
    · rw [h_eq_seven] at h_mem
      exact seven_not_mem_k_set6 h_mem
    · rw [h_eq_eight] at h_mem
      exact eight_not_mem_k_set6 h_mem
    · rw [h_eq_nine] at h_mem
      exact nine_not_mem_k_set6 h_mem
  exact le_antisymm h_le h_ge

theorem solution_six : S (A167918 6) = 2 * S 6 := by
  rw [A167918_six_eq_ten, test_S10, test_S6]


theorem seven_mem_k_set4 : 7 ∈ { k : ℕ | k > 4 ∧ S 4 ∣ S k } := by
  simp only [mem_setOf_eq]
  refine ⟨by decide, ?_⟩
  rw [test_S4, test_S7]
  use 2

theorem five_not_mem_k_set4 : 5 ∉ { k : ℕ | k > 4 ∧ S 4 ∣ S k } := by
  simp only [mem_setOf_eq, not_and]
  intro _
  rw [test_S4, test_S5]
  decide

theorem six_not_mem_k_set4 : 6 ∉ { k : ℕ | k > 4 ∧ S 4 ∣ S k } := by
  simp only [mem_setOf_eq, not_and]
  intro _
  rw [test_S4, test_S6]
  decide

theorem k_set4_nonempty : { k : ℕ | k > 4 ∧ S 4 ∣ S k }.Nonempty := by
  exact ⟨7, seven_mem_k_set4⟩

theorem A167918_four_eq_seven : A167918 4 = 7 := by
  change (if 4 = 0 then 0 else sInf { k | k > 4 ∧ S 4 ∣ S k }) = 7
  have h_ne : ¬4 = 0 := by decide
  rw [if_neg h_ne]
  have h_le : sInf { k | k > 4 ∧ S 4 ∣ S k } ≤ 7 := Nat.sInf_le seven_mem_k_set4
  have h_ge : sInf { k | k > 4 ∧ S 4 ∣ S k } ≥ 7 := by
    by_contra hc
    push_neg at hc
    have h_mem := Nat.sInf_mem k_set4_nonempty
    simp only [mem_setOf_eq] at h_mem
    have h_gt : sInf { k | k > 4 ∧ S 4 ∣ S k } > 4 := h_mem.1
    have h_eq : sInf { k | k > 4 ∧ S 4 ∣ S k } = 5 ∨ sInf { k | k > 4 ∧ S 4 ∣ S k } = 6 := by omega
    rcases h_eq with h_eq_five | h_eq_six
    · rw [h_eq_five] at h_mem
      exact five_not_mem_k_set4 h_mem
    · rw [h_eq_six] at h_mem
      exact six_not_mem_k_set4 h_mem
  exact le_antisymm h_le h_ge

theorem solution_four : S (A167918 4) = 2 * S 4 := by
  rw [A167918_four_eq_seven, test_S7, test_S4]

/--
Conjecture (2): It is conjectured that $f(n,k)=2$ for infinite many cases.
Where $f(n,k) = (p(k)+p(k+1))/(p(n)+p(n+1))$ and $k = \text{A167918}(n)$.
The value $f(n, k)$ is $S(\text{A167918}(n)) / S(n)$.
The conjecture is formalized as: for any bound $M$, there exists an index $n > M$ such that this ratio is 2.
-/
theorem oeis_A167918_conjecture_2 :
  (∀ M : ℕ, ∃ n : ℕ, n ≥ M ∧ n > 0 ∧ S (A167918 n) = 2 * S n) := answer(sorry)
#print axioms oeis_A167918_conjecture_2
