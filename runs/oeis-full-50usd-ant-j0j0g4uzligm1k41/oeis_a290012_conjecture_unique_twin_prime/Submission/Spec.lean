import FormalConjectures.Util.ProblemImports

open Nat Set Finset

/--
A290012: $a(n)$ is the smallest prime number $p$ satisfying
$$p^2 \ge \sum_{1 \le k \le n} \mathrm{prime}(k)^2$$
where $\mathrm{prime}(k)$ is the $k$-th prime number.
-/
noncomputable def A290012 (n : ℕ) : ℕ :=
  let S_n : ℕ := (Finset.range n).sum (fun k => (Nat.nth Nat.Prime k) ^ 2)
  -- sInf finds the smallest element of the set of primes p that satisfy the condition.
  sInf { p : ℕ | p.Prime ∧ S_n ≤ p ^ 2 }

/-- `A290012 1 = 2`, since `S_1 = 2^2 = 4` and `2` is the least prime with `4 ≤ 2^2`. -/
private lemma a290012_one : A290012 1 = 2 := by
  unfold A290012
  have hS : (Finset.range 1).sum (fun k => (Nat.nth Nat.Prime k) ^ 2) = 4 := by
    rw [Finset.sum_range_succ, Finset.sum_range_zero, Nat.nth_prime_zero_eq_two]; norm_num
  simp only [hS]
  apply le_antisymm
  · apply Nat.sInf_le; exact ⟨by norm_num, by norm_num⟩
  · apply le_csInf
    · exact ⟨2, ⟨by norm_num, by norm_num⟩⟩
    · intro b hb; obtain ⟨hp, _⟩ := hb; exact hp.two_le

/-- `A290012 2 = 5`, since `S_2 = 2^2 + 3^2 = 13` and `5` is the least prime with `13 ≤ p^2`. -/
private lemma a290012_two : A290012 2 = 5 := by
  unfold A290012
  have hS : (Finset.range 2).sum (fun k => (Nat.nth Nat.Prime k) ^ 2) = 13 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
        Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]; norm_num
  simp only [hS]
  apply le_antisymm
  · apply Nat.sInf_le; exact ⟨by norm_num, by norm_num⟩
  · apply le_csInf
    · exact ⟨5, ⟨by norm_num, by norm_num⟩⟩
    · intro b hb; obtain ⟨hp, hb2⟩ := hb
      by_contra h; push_neg at h
      interval_cases b <;> simp_all (config := {decide := true})

/-- `A290012 3 = 7`, since `S_3 = 2^2 + 3^2 + 5^2 = 38` and `7` is the least prime with
`38 ≤ p^2`. -/
private lemma a290012_three : A290012 3 = 7 := by
  unfold A290012
  have hS : (Finset.range 3).sum (fun k => (Nat.nth Nat.Prime k) ^ 2) = 38 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three,
        Nat.nth_prime_two_eq_five]; norm_num
  simp only [hS]
  apply le_antisymm
  · apply Nat.sInf_le; exact ⟨by norm_num, by norm_num⟩
  · apply le_csInf
    · exact ⟨7, ⟨by norm_num, by norm_num⟩⟩
    · intro b hb; obtain ⟨hp, hb2⟩ := hb
      by_contra h; push_neg at h
      interval_cases b <;> simp_all (config := {decide := true})

/-- Fully-proved reduction (no `sorry`): the inequality `(A290012 n + 2)^2 < S_{n+1}`
implies there is no twin at step `n`. -/
private lemma no_twin_of_lt (n : ℕ)
    (hkey : (A290012 n + 2) ^ 2
      < (Finset.range (n+1)).sum (fun k => (Nat.nth Nat.Prime k) ^ 2)) :
    A290012 (n + 1) ≠ A290012 n + 2 := by
  intro hEq
  set S' : ℕ := (Finset.range (n+1)).sum (fun k => (Nat.nth Nat.Prime k) ^ 2) with hS'
  have hne : {p : ℕ | p.Prime ∧ S' ≤ p ^ 2}.Nonempty := by
    obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes S'
    exact ⟨p, hp2, le_trans hp1 (Nat.le_self_pow (by norm_num) p)⟩
  have hmem : A290012 (n + 1) ∈ {p : ℕ | p.Prime ∧ S' ≤ p ^ 2} := by
    have : A290012 (n+1) = sInf {p : ℕ | p.Prime ∧ S' ≤ p ^ 2} := rfl
    rw [this]; exact Nat.sInf_mem hne
  rw [hEq] at hmem
  obtain ⟨_, hle⟩ := hmem
  exact absurd hle (not_le.mpr hkey)

/-- Conjecture: The only twin prime pair in the sequence is (5, 7).
This means the property A290012(n+1) = A290012(n) + 2 holds if and only if n = 2. -/
theorem oeis_a290012_conjecture_unique_twin_prime :
  ∀ n : ℕ, 1 ≤ n → (A290012 (n + 1) = A290012 n + 2 ↔ n = 2) :=
by
  intro n hn
  match n, hn with
  | 1, _ =>
    rw [show (1 : ℕ) + 1 = 2 from rfl, a290012_two, a290012_one]
    constructor
    · intro h; omega
    · intro h; omega
  | 2, _ =>
    rw [show (2 : ℕ) + 1 = 3 from rfl, a290012_three, a290012_two]
    constructor
    · intro _; rfl
    · intro _; rfl
  | (m + 3), _ =>
    apply iff_of_false
    · apply no_twin_of_lt
      -- OPEN: (A290012 (m+3) + 2)^2 < S_{m+4}.  Equivalent to a prime existing in
      -- [√S_{m+3}, √S_{m+4}), an interval of length ~ x^{1/3}(log x)^{2/3}: beyond
      -- the Baker–Harman–Pintz short-interval bound x^{0.525}.
      sorry
    · omega
