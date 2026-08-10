import FormalConjectures.Util.ProblemImports

open Nat Set Finset

/-- A384237: Number of divisors $d$ of $n$ such that $d^d \equiv d \pmod n$. -/
def A384237 (n : ℕ) : ℕ :=
  (n.divisors.filter fun d : ℕ => (d ^ d) % n = d % n).card

/--
A385391: $a(n)$ is the smallest integer $k$ such that $A384237(k) = n$.
This is formalized using the set infimum ($\mathrm{sInf}$) of the preimage of $n$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | A384237 k = n}

/-- A002110(n): The primorial $p_n\#$. Product of the first $n$ primes (0-indexed).
  Note: Nat.nth Nat.Prime 0 = 2, Nat.nth Nat.Prime 1 = 3, etc. -/
noncomputable def A002110 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else (Finset.range n).prod fun i => Nat.nth Nat.Prime i

/-! ### Auxiliary machinery for computing `A384237`

The naive definition of `A384237` scans all integers up to `n` to find divisors,
which is too slow for kernel reduction (`decide`) at the scales required below
(values up to `2310`). We provide a `√n`-time divisor enumeration `fastCount`,
prove it equals `A384237`, and use it for the decidable computations. -/

/-- Indicator that `d^d ≡ d (mod n)`. -/
def gd (n d : ℕ) : ℕ := if (d ^ d) % n = d % n then 1 else 0

theorem A384237_eq_sum (n : ℕ) : A384237 n = ∑ d ∈ n.divisors, gd n d := by
  rw [A384237, Finset.card_filter]; simp only [gd]

/-- Decomposition of the divisor sum into "small" divisors (`d ≤ √n`) and the
reindexed "large" divisors (via `d ↦ n / d`). -/
theorem decomp (n : ℕ) :
    ∑ d ∈ n.divisors, gd n d =
      (∑ i ∈ Finset.Icc 1 (Nat.sqrt n), if i ∣ n then gd n i else 0)
      + (∑ i ∈ Finset.Icc 1 (Nat.sqrt n),
          if (i ∣ n ∧ i * i < n) then gd n (n / i) else 0) := by
  rw [← Finset.sum_filter_add_sum_filter_not n.divisors (fun d => d * d ≤ n) (gd n)]
  congr 1
  · rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hd, hn⟩, hdd⟩
      have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hn)
      exact ⟨⟨hd1, (Nat.le_sqrt).2 hdd⟩, hd⟩
    · rintro ⟨⟨hd1, hds⟩, hd⟩
      have hn : n ≠ 0 := by
        have h1 : 1 ≤ Nat.sqrt n := le_trans hd1 hds
        have := (Nat.le_sqrt).1 h1
        omega
      exact ⟨⟨hd, hn⟩, (Nat.le_sqrt).1 hds⟩
  · rw [← Finset.sum_filter (s := Finset.Icc 1 (Nat.sqrt n))
        (p := fun i => i ∣ n ∧ i * i < n)]
    apply Finset.sum_nbij' (i := fun d => n / d) (j := fun e => n / e)
    · intro a ha
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc] at ha ⊢
      obtain ⟨⟨had, hn⟩, hnot⟩ := ha
      have hn0 := Nat.pos_of_ne_zero hn
      have ha1 : 0 < a := Nat.pos_of_dvd_of_pos had hn0
      have hb1 : 1 ≤ n / a := (Nat.one_le_div_iff ha1).2 (Nat.le_of_dvd hn0 had)
      have hmul : a * (n / a) = n := Nat.mul_div_cancel' had
      have haa : n < a * a := Nat.not_le.1 hnot
      have hlt : (n / a) * (n / a) < n := by nlinarith [hmul, haa, hb1]
      exact ⟨⟨hb1, (Nat.le_sqrt).2 (le_of_lt hlt)⟩, Nat.div_dvd_of_dvd had, hlt⟩
    · intro e he
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc] at he ⊢
      obtain ⟨⟨he1, hes⟩, hed, hee⟩ := he
      have hn : n ≠ 0 := by omega
      have hn0 := Nat.pos_of_ne_zero hn
      have he0 : 0 < e := he1
      have hmul : e * (n / e) = n := Nat.mul_div_cancel' hed
      have hgt : n < (n / e) * (n / e) := by nlinarith [hmul, hee, he0]
      exact ⟨⟨Nat.div_dvd_of_dvd hed, hn⟩, Nat.not_le.2 hgt⟩
    · intro a ha
      simp only [Finset.mem_filter, Nat.mem_divisors] at ha
      exact Nat.div_div_self ha.1.1 ha.1.2
    · intro e he
      simp only [Finset.mem_filter, Finset.mem_Icc] at he
      obtain ⟨⟨he1, hes⟩, hed, hee⟩ := he
      have hn : n ≠ 0 := by omega
      exact Nat.div_div_self hed hn
    · intro a ha
      simp only [Finset.mem_filter, Nat.mem_divisors] at ha
      rw [Nat.div_div_self ha.1.1 ha.1.2]

/-- Per-`i` contribution: count the divisor `i` (if it satisfies the congruence)
and, when `i ≠ n / i`, its cofactor `n / i`. -/
def term (n i : ℕ) : ℕ :=
  (if i ∣ n ∧ (i ^ i) % n = i % n then 1 else 0)
  + (if i ∣ n ∧ i * i < n ∧ ((n / i) ^ (n / i)) % n = (n / i) % n then 1 else 0)

/-- Fuel-bounded loop summing `term n i` over `1 ≤ i ≤ √n`. The loop terminates
early (when `i * i > n`), so only `O(√n)` iterations occur. -/
def fcLoop : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | (fuel + 1), i, n =>
      if i * i ≤ n then term n i + fcLoop fuel (i + 1) n
      else 0

def fastCount (n : ℕ) : ℕ := fcLoop (n + 1) 1 n

theorem fcLoop_eq (n : ℕ) : ∀ fuel i, Nat.sqrt n + 1 ≤ i + fuel →
    fcLoop fuel i n = ∑ j ∈ Finset.Icc i (Nat.sqrt n), term n j := by
  intro fuel
  induction fuel with
  | zero =>
    intro i hi
    rw [fcLoop, Finset.Icc_eq_empty (by omega)]; simp
  | succ fuel ih =>
    intro i hi
    rw [fcLoop]
    by_cases hik : i * i ≤ n
    · simp only [hik, if_true]
      have hisqrt : i ≤ Nat.sqrt n := (Nat.le_sqrt).2 hik
      have hsplit : Finset.Icc i (Nat.sqrt n) = insert i (Finset.Icc (i + 1) (Nat.sqrt n)) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hsplit, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
      rw [ih (i + 1) (by omega)]
    · simp only [hik, if_false]
      have : Nat.sqrt n < i := by
        by_contra h
        exact hik ((Nat.le_sqrt).1 (by omega))
      rw [Finset.Icc_eq_empty (by omega)]; simp

theorem fastCount_eq (n : ℕ) : fastCount n = A384237 n := by
  rw [A384237_eq_sum, decomp, fastCount, fcLoop_eq n (n + 1) 1 (by
    have := Nat.sqrt_le_self n; omega)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [term]
  congr 1
  · by_cases hj : j ∣ n <;> simp [hj, gd]
  · rcases Classical.em (j ∣ n ∧ j * j < n) with ⟨h1, h2⟩ | hc
    · simp only [h1, h2, true_and, if_true, gd]
    · rw [if_neg (fun h => hc ⟨h.1, h.2.1⟩), if_neg hc]

/-- If `A384237 M = N` and no smaller `k` achieves `N`, then `a N = M`. -/
theorem a_eq (N M : ℕ) (hmem : A384237 M = N) (hlb : ∀ k, k < M → A384237 k ≠ N) :
    a N = M := by
  apply le_antisymm
  · exact Nat.sInf_le hmem
  · by_contra h
    push_neg at h
    have hne : {k : ℕ | A384237 k = N}.Nonempty := ⟨M, hmem⟩
    have hmem2 := Nat.sInf_mem hne
    exact hlb _ h hmem2

/-! ### Values of the primorial `A002110` -/

theorem A002110_0 : A002110 0 = 1 := by simp [A002110]
theorem A002110_1 : A002110 1 = 2 := by
  simp [A002110, Finset.prod_range_succ, Nat.nth_prime_zero_eq_two]
theorem A002110_2 : A002110 2 = 6 := by
  simp [A002110, Finset.prod_range_succ, Nat.nth_prime_zero_eq_two,
    Nat.nth_prime_one_eq_three]
theorem A002110_3 : A002110 3 = 30 := by
  simp [A002110, Finset.prod_range_succ, Nat.nth_prime_zero_eq_two,
    Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five]
theorem A002110_4 : A002110 4 = 210 := by
  simp [A002110, Finset.prod_range_succ, Nat.nth_prime_zero_eq_two,
    Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven]
theorem A002110_5 : A002110 5 = 2310 := by
  simp [A002110, Finset.prod_range_succ, Nat.nth_prime_zero_eq_two,
    Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven,
    Nat.nth_prime_four_eq_eleven]

set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000
set_option maxRecDepth 100000

/--
oeis_385391_conjecture_0: A385391 a(1) = A002110(0), a(2) = A002110(1), a(3) = A002110(2), a(6) = A002110(3), a(7) = A002110(4), a(10) = A002110(5), ...?
This conjecture is formalized as a conjunction of the listed equalities, implying a general pattern related to A065295.
-/
theorem oeis_385391_conjecture_0 :
  a 1 = A002110 0 ∧
  a 2 = A002110 1 ∧
  a 3 = A002110 2 ∧
  a 6 = A002110 3 ∧
  a 7 = A002110 4 ∧
  a 10 = A002110 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [A002110_0]
    refine a_eq 1 1 (by rw [← fastCount_eq]; decide) ?_
    intro k hk; rw [← fastCount_eq]
    have : ∀ k < 1, fastCount k ≠ 1 := by decide
    exact this k hk
  · rw [A002110_1]
    refine a_eq 2 2 (by rw [← fastCount_eq]; decide) ?_
    intro k hk; rw [← fastCount_eq]
    have : ∀ k < 2, fastCount k ≠ 2 := by decide
    exact this k hk
  · rw [A002110_2]
    refine a_eq 3 6 (by rw [← fastCount_eq]; decide) ?_
    intro k hk; rw [← fastCount_eq]
    have : ∀ k < 6, fastCount k ≠ 3 := by decide
    exact this k hk
  · rw [A002110_3]
    refine a_eq 6 30 (by rw [← fastCount_eq]; decide) ?_
    intro k hk; rw [← fastCount_eq]
    have : ∀ k < 30, fastCount k ≠ 6 := by decide
    exact this k hk
  · rw [A002110_4]
    refine a_eq 7 210 (by rw [← fastCount_eq]; decide) ?_
    intro k hk; rw [← fastCount_eq]
    have : ∀ k < 210, fastCount k ≠ 7 := by decide
    exact this k hk
  · rw [A002110_5]
    refine a_eq 10 2310 (by rw [← fastCount_eq]; decide) ?_
    have d0 : ∀ j < 330, fastCount (330 * 0 + j) ≠ 10 := by decide
    have d1 : ∀ j < 330, fastCount (330 * 1 + j) ≠ 10 := by decide
    have d2 : ∀ j < 330, fastCount (330 * 2 + j) ≠ 10 := by decide
    have d3 : ∀ j < 330, fastCount (330 * 3 + j) ≠ 10 := by decide
    have d4 : ∀ j < 330, fastCount (330 * 4 + j) ≠ 10 := by decide
    have d5 : ∀ j < 330, fastCount (330 * 5 + j) ≠ 10 := by decide
    have d6 : ∀ j < 330, fastCount (330 * 6 + j) ≠ 10 := by decide
    intro k hk
    rw [← fastCount_eq]
    obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 330 ∧ k = 330 * q + r :=
      ⟨k / 330, k % 330, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod k 330).symm⟩
    have hq : q < 7 := by omega
    interval_cases q
    · exact d0 r hr
    · exact d1 r hr
    · exact d2 r hr
    · exact d3 r hr
    · exact d4 r hr
    · exact d5 r hr
    · exact d6 r hr
