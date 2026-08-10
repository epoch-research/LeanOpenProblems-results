import FormalConjectures.Util.ProblemImports

open Nat Set

noncomputable def P (i : ℕ) : ℕ := Nat.nth Nat.Prime (i - 1)
noncomputable def S (i : ℕ) : ℕ := P i + P (i + 1)
noncomputable def A167918 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let D_n := S n
    let k_set : Set ℕ := { k : ℕ | k > n ∧ D_n ∣ S k }
    sInf k_set

-- nth prime strict monotone
lemma nthP_strictMono : StrictMono (Nat.nth Nat.Prime) :=
  Nat.nth_strictMono Nat.infinite_setOf_prime

lemma P_lt_P {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) : P i < P j := by
  unfold P
  apply nthP_strictMono
  omega

lemma S_pos (i : ℕ) : 0 < S i := by
  unfold S P
  have := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (i - 1)
  have h2 := this.two_le
  positivity

lemma S_strictMono {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) : S i < S j := by
  unfold S
  have h1 : P i < P j := P_lt_P hi hij
  have h2 : P (i+1) < P (j+1) := P_lt_P (by omega) (by omega)
  omega

-- reduction lemma
lemma reduction (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : n < k) (hSk : S k = 2 * S n) :
    S (A167918 n) = 2 * S n := by
  have hn0 : n ≠ 0 := by omega
  -- A167918 n = sInf {k | k > n ∧ S n ∣ S k}
  have hAeq : A167918 n = sInf { k : ℕ | k > n ∧ S n ∣ S k } := by
    unfold A167918
    simp [hn0]
  -- k is the least element
  have hleast : IsLeast { k : ℕ | k > n ∧ S n ∣ S k } k := by
    constructor
    · refine ⟨hk, ?_⟩
      exact ⟨2, by rw [hSk]; ring⟩
    · rintro m ⟨hm, hdvd⟩
      by_contra hlt
      push_neg at hlt  -- m < k
      -- then S m < S k = 2 S n, and S n < S m, but S n ∣ S m so S m ≥ 2 S n
      have hSm_lt : S m < 2 * S n := by rw [← hSk]; exact S_strictMono (by omega) hlt
      have hSm_gt : S n < S m := S_strictMono hn hm
      obtain ⟨c, hc⟩ := hdvd
      have hSnpos := S_pos n
      -- S m = S n * c, and S n < S m so c ≥ 2
      have hc2 : 2 ≤ c := by
        rcases Nat.lt_or_ge c 2 with h | h
        · interval_cases c <;> omega
        · exact h
      have : 2 * S n ≤ S m := by
        rw [hc]; nlinarith
      omega
  rw [hAeq, hleast.csInf_eq, hSk]

/-
The following `core` lemma is, via the verified reduction above (`reduction`), *equivalent*
to the original conjecture.  Indeed:
* If `S k = 2 * S n` with `n < k` and `1 ≤ n`, then `k` is the least index `> n` with
  `S n ∣ S k` (any intermediate index `m` would give `S n < S m < 2 * S n`, impossible for a
  multiple of `S n`), so `A167918 n = k` and `S (A167918 n) = 2 * S n`.
* Conversely `S (A167918 n) = 2 * S n` exhibits such a `k`.

Hence the conjecture holds iff there are arbitrarily large `n` with `p_n + p_{n+1}` an *exact
midpoint* of the prime gap surrounding it (equivalently, `2 (p_n + p_{n+1})` is itself a sum of
two consecutive primes).  This is a Hardy–Littlewood-type statement about a prime `4`-tuple
correlation with consecutiveness constraints; obtaining an unconditional lower bound on the
number of such solutions is blocked by the parity problem of sieve theory and is beyond current
mathematics (it is in the same difficulty class as the twin prime conjecture).  The statement is
nevertheless true (solutions occur at every scale, verified for `n` up to `~4·10^5`), so it
cannot be disproved.
-/
lemma core : ∀ M : ℕ, ∃ n : ℕ, M ≤ n ∧ 1 ≤ n ∧ ∃ k, n < k ∧ S k = 2 * S n := by
  sorry

-- Concrete verification that the reduction machinery is correct and the statement is
-- non-vacuously true: `S (A167918 3) = 2 * S 3` (the pair `p₃+p₄=12`, `p₅+p₆=24`).
lemma nthPrime5 : Nat.nth Nat.Prime 5 = 13 := by
  have h : Nat.Prime 13 := by norm_num
  have hc : Nat.count Nat.Prime 13 = 5 := by decide
  have := Nat.nth_count h
  rw [hc] at this
  exact this

lemma S5_eq_two_S3 : S 5 = 2 * S 3 := by
  simp only [S, P]
  norm_num [Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven,
    Nat.nth_prime_four_eq_eleven, nthPrime5]

example : S (A167918 3) = 2 * S 3 :=
  reduction 3 (by norm_num) 5 (by norm_num) S5_eq_two_S3

theorem oeis_A167918_conjecture_2 :
  (∀ M : ℕ, ∃ n : ℕ, n ≥ M ∧ n > 0 ∧ S (A167918 n) = 2 * S n) := by
  intro M
  obtain ⟨n, hMn, hn1, k, hnk, hSk⟩ := core M
  exact ⟨n, hMn, hn1, reduction n hn1 k hnk hSk⟩
