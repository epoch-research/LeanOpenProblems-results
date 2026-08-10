import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 8000

open Int

/--
Helper function for A382590, computing the pair $(a(n), b(n))$ such that:
$a(n) = a(n-1)b(n-2) + a(n-2)b(n-1)$
$b(n) = a(n-1)b(n-2) - a(n-2)b(n-1)$
-/
def A382590_pair : ℕ → ℤ × ℤ
| 0 => (1, 1)
| 1 => (2, 1)
| n + 2 =>
  let (a_n_plus_1, b_n_plus_1) := A382590_pair (n + 1)
  let (a_n, b_n) := A382590_pair n
  (a_n_plus_1 * b_n + a_n * b_n_plus_1, a_n_plus_1 * b_n - a_n * b_n_plus_1)

/--
A382590: $a(n)$ is the sequence defined by the mutual recurrence relations:
$a(n) = a(n-1)b(n-2) + a(n-2)b(n-1)$ and $b(n) = a(n-1)b(n-2) - a(n-2)b(n-1)$
starting with $a(0) = b(0) = b(1) = 1$ and a(1) = 2.
The terms are in $\mathbb{Z}$ due to negative values.
-/
def A382590 (n : ℕ) : ℤ := (A382590_pair n).fst

open Nat

/--
The k-th prime factor of an integer n (where k>=1), counted with multiplicity.
This is defined as the k-th element (0-indexed k-1) of `Nat.primeFactorsList n.natAbs`.
Returns 1 if n has fewer than k prime factors or if n is 0, 1, or -1, following the informal convention.
-/
def kth_prime_factor (k : ℕ) (n : ℤ) : ℕ :=
  if h₀ : k = 0 then 1 else
  let n_abs := Int.natAbs n
  let L := primeFactorsList n_abs
  -- prime factors list length is L.length. We look for k-th element, index k-1.
  if h_len : k - 1 ≥ L.length then 1 else
  L[k - 1]

/-!
## Proof of the conjecture

The key observation is that the 2-adic valuation of `a(n)` grows without bound
(in fact `2 ^ (n - 4)` divides `a(n)`). Together with the fact that `a(n)` is never
zero, this means that for any fixed `k`, the `k`-th prime factor of `a(n)` is
eventually always `2`. Hence the sequence of `k`-th prime factors is eventually
constant (period `1`), and in particular eventually periodic.
-/

/-- Recurrence for the first component. -/
private lemma A382590_rec_fst (k : ℕ) :
    (A382590_pair (k + 2)).1
      = (A382590_pair (k + 1)).1 * (A382590_pair k).2
        + (A382590_pair k).1 * (A382590_pair (k + 1)).2 := rfl

/-- Recurrence for the second component. -/
private lemma A382590_rec_snd (k : ℕ) :
    (A382590_pair (k + 2)).2
      = (A382590_pair (k + 1)).1 * (A382590_pair k).2
        - (A382590_pair k).1 * (A382590_pair (k + 1)).2 := rfl

/-- The 2-adic valuation of both components grows at least linearly:
`2 ^ (n - 4)` divides both `a(n)` and `b(n)`. -/
private lemma A382590_val :
    ∀ n, (2 : ℤ) ^ (n - 4) ∣ (A382590_pair n).1 ∧ (2 : ℤ) ^ (n - 4) ∣ (A382590_pair n).2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_or_ge n 7 with h | h
    · interval_cases n <;> decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
      have h1 := ih (m + 6) (by omega)
      have h2 := ih (m + 5) (by omega)
      have a6 : (2 : ℤ) ^ (m + 2) ∣ (A382590_pair (m + 6)).1 := h1.1
      have b6 : (2 : ℤ) ^ (m + 2) ∣ (A382590_pair (m + 6)).2 := h1.2
      have a5 : (2 : ℤ) ^ (m + 1) ∣ (A382590_pair (m + 5)).1 := h2.1
      have b5 : (2 : ℤ) ^ (m + 1) ∣ (A382590_pair (m + 5)).2 := h2.2
      have d1 : (2 : ℤ) ^ (m + 3) ∣ (A382590_pair (m + 6)).1 * (A382590_pair (m + 5)).2 := by
        refine dvd_trans ?_ (mul_dvd_mul a6 b5)
        rw [← pow_add]; exact pow_dvd_pow 2 (by omega)
      have d2 : (2 : ℤ) ^ (m + 3) ∣ (A382590_pair (m + 5)).1 * (A382590_pair (m + 6)).2 := by
        refine dvd_trans ?_ (mul_dvd_mul a5 b6)
        rw [← pow_add]; exact pow_dvd_pow 2 (by omega)
      have e1 : (A382590_pair (m + 7)).1
          = (A382590_pair (m + 6)).1 * (A382590_pair (m + 5)).2
            + (A382590_pair (m + 5)).1 * (A382590_pair (m + 6)).2 := A382590_rec_fst (m + 5)
      have e2 : (A382590_pair (m + 7)).2
          = (A382590_pair (m + 6)).1 * (A382590_pair (m + 5)).2
            - (A382590_pair (m + 5)).1 * (A382590_pair (m + 6)).2 := A382590_rec_snd (m + 5)
      refine ⟨?_, ?_⟩
      · rw [show (m + 7) - 4 = m + 3 from rfl, e1]; exact dvd_add d1 d2
      · rw [show (m + 7) - 4 = m + 3 from rfl, e2]; exact dvd_sub d1 d2

/-- Periodicity of the sequence modulo `5`, with period `12` starting from `n = 3`. -/
private lemma A382590_per5 : ∀ n, 3 ≤ n →
    (A382590_pair (n + 12)).1 ≡ (A382590_pair n).1 [ZMOD 5] ∧
    (A382590_pair (n + 12)).2 ≡ (A382590_pair n).2 [ZMOD 5] := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases lt_or_ge n 5 with h | h
    · interval_cases n
      · decide
      · decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
      have ih3 := ih (m + 3) (by omega) (by omega)
      have ih4 := ih (m + 4) (by omega) (by omega)
      refine ⟨?_, ?_⟩
      · have e1 : (A382590_pair (m + 5 + 12)).1
            = (A382590_pair (m + 16)).1 * (A382590_pair (m + 15)).2
              + (A382590_pair (m + 15)).1 * (A382590_pair (m + 16)).2 := A382590_rec_fst (m + 15)
        have e2 : (A382590_pair (m + 5)).1
            = (A382590_pair (m + 4)).1 * (A382590_pair (m + 3)).2
              + (A382590_pair (m + 3)).1 * (A382590_pair (m + 4)).2 := A382590_rec_fst (m + 3)
        rw [e1, e2]
        exact Int.ModEq.add (Int.ModEq.mul ih4.1 ih3.2) (Int.ModEq.mul ih3.1 ih4.2)
      · have e1 : (A382590_pair (m + 5 + 12)).2
            = (A382590_pair (m + 16)).1 * (A382590_pair (m + 15)).2
              - (A382590_pair (m + 15)).1 * (A382590_pair (m + 16)).2 := A382590_rec_snd (m + 15)
        have e2 : (A382590_pair (m + 5)).2
            = (A382590_pair (m + 4)).1 * (A382590_pair (m + 3)).2
              - (A382590_pair (m + 3)).1 * (A382590_pair (m + 4)).2 := A382590_rec_snd (m + 3)
        rw [e1, e2]
        exact Int.ModEq.sub (Int.ModEq.mul ih4.1 ih3.2) (Int.ModEq.mul ih3.1 ih4.2)

/-- Periodicity of the sequence modulo `7`, with period `24` starting from `n = 7`. -/
private lemma A382590_per7 : ∀ n, 7 ≤ n →
    (A382590_pair (n + 24)).1 ≡ (A382590_pair n).1 [ZMOD 7] ∧
    (A382590_pair (n + 24)).2 ≡ (A382590_pair n).2 [ZMOD 7] := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases lt_or_ge n 9 with h | h
    · interval_cases n
      · decide
      · decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
      have ih7 := ih (m + 7) (by omega) (by omega)
      have ih8 := ih (m + 8) (by omega) (by omega)
      refine ⟨?_, ?_⟩
      · have e1 : (A382590_pair (m + 9 + 24)).1
            = (A382590_pair (m + 32)).1 * (A382590_pair (m + 31)).2
              + (A382590_pair (m + 31)).1 * (A382590_pair (m + 32)).2 := A382590_rec_fst (m + 31)
        have e2 : (A382590_pair (m + 9)).1
            = (A382590_pair (m + 8)).1 * (A382590_pair (m + 7)).2
              + (A382590_pair (m + 7)).1 * (A382590_pair (m + 8)).2 := A382590_rec_fst (m + 7)
        rw [e1, e2]
        exact Int.ModEq.add (Int.ModEq.mul ih8.1 ih7.2) (Int.ModEq.mul ih7.1 ih8.2)
      · have e1 : (A382590_pair (m + 9 + 24)).2
            = (A382590_pair (m + 32)).1 * (A382590_pair (m + 31)).2
              - (A382590_pair (m + 31)).1 * (A382590_pair (m + 32)).2 := A382590_rec_snd (m + 31)
        have e2 : (A382590_pair (m + 9)).2
            = (A382590_pair (m + 8)).1 * (A382590_pair (m + 7)).2
              - (A382590_pair (m + 7)).1 * (A382590_pair (m + 8)).2 := A382590_rec_snd (m + 7)
        rw [e1, e2]
        exact Int.ModEq.sub (Int.ModEq.mul ih8.1 ih7.2) (Int.ModEq.mul ih7.1 ih8.2)

/-- For `n ≡ 1 (mod 3)`, the term `a(n)` is not divisible by `5`. -/
private lemma A382590_ne5 : ∀ n, n % 3 = 1 → ¬ ((5 : ℤ) ∣ (A382590_pair n).1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h3
    rcases lt_or_ge n 15 with h | h
    · interval_cases n <;> first | (exfalso; omega) | decide
    · intro hdvd
      have hrw : (n - 12) + 12 = n := by omega
      have hper := (A382590_per5 (n - 12) (by omega)).1
      rw [hrw] at hper
      have hz : (A382590_pair (n - 12)).1 ≡ 0 [ZMOD 5] :=
        hper.symm.trans (Int.modEq_zero_iff_dvd.2 hdvd)
      exact ih (n - 12) (by omega) (by omega) (Int.modEq_zero_iff_dvd.1 hz)

/-- For `n ≢ 1 (mod 3)`, the term `a(n)` is not divisible by `7`. -/
private lemma A382590_ne7 : ∀ n, n % 3 ≠ 1 → ¬ ((7 : ℤ) ∣ (A382590_pair n).1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h3
    rcases lt_or_ge n 31 with h | h
    · interval_cases n <;> first | (exfalso; omega) | decide
    · intro hdvd
      have hrw : (n - 24) + 24 = n := by omega
      have hper := (A382590_per7 (n - 24) (by omega)).1
      rw [hrw] at hper
      have hz : (A382590_pair (n - 24)).1 ≡ 0 [ZMOD 7] :=
        hper.symm.trans (Int.modEq_zero_iff_dvd.2 hdvd)
      exact ih (n - 24) (by omega) (by omega) (Int.modEq_zero_iff_dvd.1 hz)

/-- Every term `a(n)` is nonzero: if `n ≡ 1 (mod 3)` it is coprime to `5`, otherwise to `7`. -/
private lemma A382590_ne_zero (n : ℕ) : (A382590_pair n).1 ≠ 0 := by
  rcases eq_or_ne (n % 3) 1 with h | h
  · exact fun hz => A382590_ne5 n h (by rw [hz]; exact dvd_zero 5)
  · exact fun hz => A382590_ne7 n h (by rw [hz]; exact dvd_zero 7)

/-- In a list sorted in ascending order whose elements are all at least `c`, the
first `count c` entries are all equal to `c`. -/
private lemma sorted_run {c : ℕ} : ∀ (L : List ℕ), L.Pairwise (· ≤ ·) → (∀ x ∈ L, c ≤ x) →
    ∀ i (_ : i < L.length), i < L.count c → L[i] = c := by
  intro L
  induction L with
  | nil => intro _ _ i hi _; simp at hi
  | cons x t ih =>
    intro hpw hmin i hi hcnt
    rw [List.pairwise_cons] at hpw
    obtain ⟨hx, htw⟩ := hpw
    have hminx : c ≤ x := hmin x (List.mem_cons_self)
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero]
      by_contra hne
      have hcx : c < x := lt_of_le_of_ne hminx (Ne.symm hne)
      have hct0 : t.count c = 0 := by
        rw [List.count_eq_zero]; intro hmem; have := hx c hmem; omega
      rw [List.count_cons, hct0] at hcnt
      rw [if_neg (by simpa [beq_iff_eq] using hne)] at hcnt
      simp at hcnt
    | succ j =>
      simp only [List.getElem_cons_succ]
      rw [List.count_cons] at hcnt
      have hif : (if (x == c) then 1 else 0) ≤ 1 := by split <;> omega
      apply ih htw (fun y hy => hmin y (List.mem_cons_of_mem _ hy)) j
        (by have := hi; simp only [List.length_cons] at this; omega)
      omega

/-- If `2 ^ k` divides a nonzero integer `m` (with `k ≥ 2`), then its `k`-th prime factor is `2`. -/
private lemma kpf_eq_two {k : ℕ} (hk : 2 ≤ k) {m : ℤ} (hd : (2 : ℤ) ^ k ∣ m) (hm : m ≠ 0) :
    kth_prime_factor k m = 2 := by
  have hNne : m.natAbs ≠ 0 := by simpa [Int.natAbs_eq_zero] using hm
  have hdN : 2 ^ k ∣ m.natAbs := by
    have h1 : ((2 ^ k : ℕ) : ℤ) ∣ m := by push_cast; exact hd
    have h2 := Int.natAbs_dvd_natAbs.2 h1
    simpa using h2
  have hcount : k ≤ (primeFactorsList m.natAbs).count 2 := by
    rw [Nat.primeFactorsList_count_eq]
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hNne).1 hdN
  have hlen : k - 1 < (primeFactorsList m.natAbs).length := by
    have : (primeFactorsList m.natAbs).count 2 ≤ (primeFactorsList m.natAbs).length :=
      List.count_le_length
    omega
  unfold kth_prime_factor
  rw [dif_neg (show ¬ k = 0 by omega),
    dif_neg (show ¬ k - 1 ≥ (primeFactorsList m.natAbs).length by omega)]
  apply sorted_run (primeFactorsList m.natAbs) (Nat.primeFactorsList_sorted m.natAbs).pairwise
  · intro x hx
    exact (Nat.prime_of_mem_primeFactorsList hx).two_le
  · omega

/--
A382590 This sequence appears to have a very peculiar (conjectured) property.
For any k > 1, if you take the k-th prime factor of each term, you get an eventually periodic sequence.
This seems to hold even when we change a(1) as long as it is an integer > 1.
-/
theorem A382590_conjecture_kth_prime_factor_is_eventually_periodic :
  ∀ k : ℕ, k ≥ 2 →
    ∃ N₀ p : ℕ, p > 0 ∧ ∀ n : ℕ, n ≥ N₀ →
      kth_prime_factor k (A382590 (n + p)) = kth_prime_factor k (A382590 n) :=
  by
    intro k hk
    refine ⟨k + 4, 1, by omega, ?_⟩
    intro n hn
    have key : ∀ j : ℕ, j ≥ k + 4 → kth_prime_factor k (A382590 j) = 2 := by
      intro j hj
      have hdvd : (2 : ℤ) ^ k ∣ (A382590_pair j).1 :=
        dvd_trans (pow_dvd_pow 2 (show k ≤ j - 4 by omega)) (A382590_val j).1
      exact kpf_eq_two hk hdvd (A382590_ne_zero j)
    rw [key (n + 1) (by omega), key n (by omega)]
