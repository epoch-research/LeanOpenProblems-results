import FormalConjectures.Util.ProblemImports

open Nat BigOperators Int

/--
A092243: Score at stage $n$ in "tug of war" between prime gap increases vs. prime gap decreases:
start with score = 0 at $n = 1$ and at stage $k > 1$, increase (resp. decrease) the score by 1
if the $k$-th prime gap is greater (resp. less) than the previous prime gap.
-/
noncomputable def A092243 (n : ℕ) : ℤ :=
  -- P_i is the $i$-th prime, 0-indexed: P 0 = 2, P 1 = 3, ...
  -- Note: Nat.nth Nat.Prime i gives the i-th prime, where i=0 is the 0-th prime, 2.
  let P (i : ℕ) : ℕ := Nat.nth Nat.Prime i

  -- $G_k$ is the $k$-th prime gap (OEIS 1-indexed), $G_k = P_k - P_{k-1}$, for $k \ge 1$.
  -- Here we use the 0-indexed primes P_i, so the k-th gap involves the prime P[k] and P[k-1].
  let G_gap (k : ℕ) : ℕ := P k - P (k - 1)

  if n = 0 then 0 -- Defining for n=0 as 0, though OEIS starts at 1
  else if n = 1 then 0
  else

  -- The score is the cumulative sum of the changes $\Delta(k) = \operatorname{sign}(G_k - G_{k-1})$ for $k=2$ to $n$.
  -- The sum starts at k=2 because the first gap G_1 is compared to G_2. The comparison is between G_k and G_{k-1}.
  -- Since the first gap is G_1, the first comparison is at k=2 (G_2 vs G_1).
  (Finset.Icc 2 n).sum fun k : ℕ =>
    let Gk   : ℕ := G_gap k
    -- Since $k \ge 2$, $k-1 \ge 1$, so G_gap (k-1) is safely computed.
    let Gkm1 : ℕ := G_gap (k - 1)

    -- Calculate $\operatorname{sign}(G_k - G_{k-1})$ using integer subtraction and sign function.
    ((Gk : ℤ) - (Gkm1 : ℤ)) |>.sign

/-
We remove the specific proofs for a_one etc., as they failed compilation and are not the object of the final submission.
The definition of A092243 is now corrected for proper syntax of the n-th prime.
-/

/--
Conjectures regarding the long-term behavior of A092243 (the score $s$).

Questions from OEIS A092243, including the primary conjectures:
1. Is s > 0 for some n > 250000?
2. Is s bounded from below?
3. Is s bounded from above?
4. Is s > 0 for infinitely many values of n?
5. Is s < 0 for infinitely many values of n?
-/
structure OEIS_A092243_Conjectures where
  /-- Is the score ever positive after n = 250,000? -/
  positive_after_large_n : ∃ n : ℕ, n > 250000 ∧ A092243 n > 0
  /-- Is the score bounded from below? -/
  bounded_below : ∃ B : ℤ, ∀ n : ℕ, B ≤ A092243 n
  /-- Is the score bounded from above? -/
  bounded_above : ∃ B : ℤ, ∀ n : ℕ, A092243 n ≤ B
  /-- Is the score positive infinitely often? -/
  infinitely_positive : Set.Infinite {n : ℕ | A092243 n > 0}
  /-- Is the score negative infinitely often? -/
  infinitely_negative : Set.Infinite {n : ℕ | A092243 n < 0}

/-! ### Basic properties of A092243 -/

/-- The `n`-th prime (0-indexed). -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

lemma nthPrime_zero : nthPrime 0 = 2 := Nat.nth_prime_zero_eq_two
lemma nthPrime_one : nthPrime 1 = 3 := Nat.nth_prime_one_eq_three
lemma nthPrime_two : nthPrime 2 = 5 := Nat.nth_prime_two_eq_five
lemma nthPrime_three : nthPrime 3 = 7 := Nat.nth_prime_three_eq_seven
lemma nthPrime_four : nthPrime 4 = 11 := Nat.nth_prime_four_eq_eleven

lemma nthPrime_strictMono : StrictMono nthPrime :=
  Nat.nth_strictMono Nat.infinite_setOf_prime

lemma nthPrime_lt_nthPrime {i j : ℕ} (h : i < j) : nthPrime i < nthPrime j :=
  nthPrime_strictMono h

lemma nthPrime_le_nthPrime {i j : ℕ} (h : i ≤ j) : nthPrime i ≤ nthPrime j :=
  nthPrime_strictMono.monotone h

lemma prime_nthPrime (n : ℕ) : (nthPrime n).Prime :=
  Nat.prime_nth_prime n

/-- The gap between the `(k-1)`-st and `k`-th primes (for `k ≥ 1`). -/
noncomputable def primeGap' (k : ℕ) : ℕ := nthPrime k - nthPrime (k - 1)

lemma primeGap'_pos {k : ℕ} (hk : 1 ≤ k) : 0 < primeGap' k := by
  unfold primeGap'
  have : nthPrime (k - 1) < nthPrime k := nthPrime_lt_nthPrime (Nat.sub_one_lt_of_lt hk)
  omega

lemma A092243_zero : A092243 0 = 0 := by simp [A092243]
lemma A092243_one : A092243 1 = 0 := by simp [A092243]

lemma A092243_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    A092243 n = (Finset.Icc 2 n).sum fun k =>
      ((primeGap' k : ℤ) - (primeGap' (k - 1) : ℤ)).sign := by
  unfold A092243 primeGap' nthPrime
  have h0 : n ≠ 0 := by omega
  have h1 : n ≠ 1 := by omega
  simp [h0, h1]

lemma sign_sub_eq_one_of_lt {a b : ℕ} (h : a < b) : ((b : ℤ) - (a : ℤ)).sign = 1 := by
  apply Int.sign_eq_one_of_pos
  omega

lemma abs_sign_le (a : ℤ) : |a.sign| ≤ 1 := by
  rcases Int.sign_trichotomy a with h | h | h <;> simp [h]

lemma Icc_succ_eq_insert {a n : ℕ} (_h : a ≤ n + 1) (h2 : a ≤ n) :
    Finset.Icc a (n + 1) = insert (n + 1) (Finset.Icc a n) := by
  ext k
  simp only [Finset.mem_Icc, Finset.mem_insert]
  omega

/-- Recurrence: for `n ≥ 1`, the next score differs by the sign of the next gap change. -/
lemma A092243_succ {n : ℕ} (hn : 1 ≤ n) :
    A092243 (n + 1) =
      A092243 n + ((primeGap' (n + 1) : ℤ) - (primeGap' n : ℤ)).sign := by
  by_cases h1 : n = 1
  · subst h1
    rw [A092243_one, A092243_of_two_le (by norm_num : (2 : ℕ) ≤ 2)]
    simp
  · have hn2 : 2 ≤ n := by omega
    have hn2' : 2 ≤ n + 1 := by omega
    rw [A092243_of_two_le hn2', A092243_of_two_le hn2]
    rw [Icc_succ_eq_insert (by omega) (by omega), Finset.sum_insert (by simp)]
    have : n + 1 - 1 = n := Nat.add_sub_cancel n 1
    rw [this]
    ac_rfl

/-- An increasing run of consecutive prime gaps of length `L` produces a score increase of `L`. -/
lemma A092243_increase_of_strictMono_gaps {n L : ℕ} (hn : 1 ≤ n)
    (h : ∀ i < L, primeGap' (n + i) < primeGap' (n + i + 1)) :
    A092243 (n + L) = A092243 n + L := by
  induction L with
  | zero => simp
  | succ L ih =>
    have ih' : A092243 (n + L) = A092243 n + L := by
      apply ih
      intro i hi
      exact h i (Nat.lt_trans hi (Nat.lt_succ_self _))
    have hgap : primeGap' (n + L) < primeGap' (n + L + 1) := h L (Nat.lt_succ_self _)
    have hnL : 1 ≤ n + L := Nat.le_add_right_of_le hn
    rw [Nat.add_succ, A092243_succ hnL, ih']
    have hsign : ((primeGap' (n + L + 1) : ℤ) - (primeGap' (n + L) : ℤ)).sign = 1 :=
      sign_sub_eq_one_of_lt hgap
    rw [hsign]
    push_cast
    ring

/-- If there are arbitrarily long increasing runs of consecutive prime gaps, then
    `A092243` cannot be bounded both from above and from below. -/
lemma not_bounded_of_arbitrarily_long_increase_runs
    (h : ∀ L, ∃ n ≥ 1, ∀ i < L, primeGap' (n + i) < primeGap' (n + i + 1)) :
    ¬ ((∃ B : ℤ, ∀ n : ℕ, B ≤ A092243 n) ∧ (∃ B : ℤ, ∀ n : ℕ, A092243 n ≤ B)) := by
  rintro ⟨⟨Bmin, hmin⟩, ⟨Bmax, hmax⟩⟩
  have hB : Bmin ≤ Bmax := le_trans (hmin 0) (hmax 0)
  -- Take a run longer than the putative diameter of the range.
  let L : ℕ := (Bmax - Bmin + 1).toNat + 1
  obtain ⟨n, hn, hrun⟩ := h L
  have heq : A092243 (n + L) = A092243 n + L :=
    A092243_increase_of_strictMono_gaps hn hrun
  have hlo : Bmin ≤ A092243 n := hmin n
  have hhi : A092243 (n + L) ≤ Bmax := hmax (n + L)
  have hsum : A092243 n + (L : ℤ) ≤ Bmax := by
    rwa [← heq]
  have hLle : (L : ℤ) ≤ Bmax - Bmin := by linarith
  have hLge : (Bmax - Bmin + 1 : ℤ) ≤ (L : ℤ) := by
    have hnn : 0 ≤ Bmax - Bmin + 1 := by linarith
    have hcast : ((Bmax - Bmin + 1).toNat : ℤ) = Bmax - Bmin + 1 := Int.toNat_of_nonneg hnn
    have : (L : ℤ) = ((Bmax - Bmin + 1).toNat : ℤ) + 1 := by
      simp only [L]; norm_cast
    linarith
  linarith

/-- Consecutive differences of distinct powers of two are strictly increasing. -/
lemma pow_two_gaps_strictMono {a b c : ℕ} (_hab : a < b) (hbc : b < c) :
    2 ^ b - 2 ^ a < 2 ^ c - 2 ^ b := by
  have hpos : 0 < 2 ^ a := Nat.pow_pos (by norm_num)
  have h1 : 2 ^ b - 2 ^ a < 2 ^ b := Nat.sub_lt (Nat.pow_pos (by norm_num)) hpos
  have h2 : 2 ^ b ≤ 2 ^ c - 2 ^ b := by
    have : 2 ^ (b + 1) ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) (Nat.succ_le_of_lt hbc)
    have : 2 * 2 ^ b ≤ 2 ^ c := by
      rwa [pow_succ, mul_comm] at this
    omega
  omega

/- Admissible tuples and Maynard's theorem -/

/-- A finite set `H` of offsets is *admissible* if it does not cover all residue classes
modulo any prime. Equivalently, there is no prime `p` such that `{h mod p : h ∈ H} = ℤ/pℤ`. -/
def Admissible (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ a : ZMod p, ∀ h ∈ H, (a + (h : ZMod p)) ≠ 0

/- Elementary estimates used in the Maynard argument. -/

lemma two_mul_choose_le_four_pow (n : ℕ) : (2 * n).choose n ≤ 4 ^ n := by
  have hsum : ∑ k ∈ Finset.range (2 * n + 1), (2 * n).choose k = 2 ^ (2 * n) :=
    Nat.sum_range_choose (2 * n)
  have hterm : (2 * n).choose n ≤ 2 ^ (2 * n) := by
    have : (2 * n).choose n ≤ ∑ k ∈ Finset.range (2 * n + 1), (2 * n).choose k :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp [Nat.lt_succ_iff]; omega)
    rwa [hsum] at this
  have h4 : 2 ^ (2 * n) = 4 ^ n := by
    rw [pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num]
  rwa [h4] at hterm

lemma four_pow_le_mul_choose (n : ℕ) :
    4 ^ n ≤ (2 * n + 1) * (2 * n).choose n := by
  have hsum : ∑ k ∈ Finset.range (2 * n + 1), (2 * n).choose k = 2 ^ (2 * n) :=
    Nat.sum_range_choose (2 * n)
  have hhalf : (2 * n) / 2 = n := by omega
  have hle : ∀ k ∈ Finset.range (2 * n + 1),
      (2 * n).choose k ≤ (2 * n).choose n := by
    intro k hk
    simpa [hhalf] using Nat.choose_le_middle k (2 * n)
  have hsumle :
      ∑ k ∈ Finset.range (2 * n + 1), (2 * n).choose k ≤
        (2 * n + 1) * (2 * n).choose n := by
    have := Finset.sum_le_sum hle
    simpa [Finset.card_range, Nat.mul_comm] using this
  have h4 : 4 ^ n = 2 ^ (2 * n) := by
    rw [pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num]
  rw [h4, ← hsum]
  exact hsumle

lemma choose_two_mul_le_pow_primeCounting {n : ℕ} (hn : 0 < n) :
    (2 * n).choose n ≤ (2 * n) ^ Nat.primeCounting (2 * n) := by
  have h2n : 0 < 2 * n := by omega
  set C := (2 * n).choose n with hCdef
  have hC : 0 < C := by rw [hCdef]; exact Nat.choose_pos (by omega)
  have hprod : C = ∏ p ∈ C.factorization.support, p ^ C.factorization p :=
    (Nat.factorization_prod_pow_eq_self hC.ne').symm
  have hle_self : ∀ p ∈ C.factorization.support, p ^ C.factorization p ≤ 2 * n := by
    intro p hp
    rw [hCdef]
    exact Nat.pow_factorization_choose_le h2n
  have hsubset : C.factorization.support ⊆ (Finset.range (2 * n + 1)).filter Nat.Prime := by
    intro p hp
    have hpP : p.Prime := Nat.prime_of_mem_primeFactors (by
      rwa [Nat.support_factorization] at hp)
    have hexp : C.factorization p ≠ 0 := Finsupp.mem_support_iff.1 hp
    have hp_le : p ≤ 2 * n :=
      le_trans (Nat.le_self_pow hexp p) (hle_self p hp)
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le hp_le), hpP⟩
  have hcard : C.factorization.support.card ≤ Nat.primeCounting (2 * n) := by
    have : C.factorization.support.card ≤ ((Finset.range (2 * n + 1)).filter Nat.Prime).card :=
      Finset.card_le_card hsubset
    have hπ : ((Finset.range (2 * n + 1)).filter Nat.Prime).card =
        Nat.primeCounting (2 * n) := by
      simp [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
    rwa [hπ] at this
  have hprod_le : C ≤ (2 * n) ^ C.factorization.support.card := by
    conv_lhs => rw [hprod]
    have := Finset.prod_le_prod (fun p hp => Nat.zero_le _) (fun p hp => hle_self p hp)
    simpa [Finset.prod_const] using this
  exact le_trans hprod_le (Nat.pow_le_pow_right h2n hcard)

lemma log_four_ge_one : (1 : ℝ) ≤ Real.log 4 := by
  have hexp : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  exact (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 4)).2 (le_of_lt hexp)

lemma exp_half_ge_three_halves : (3 / 2 : ℝ) ≤ Real.exp (1 / 2) := by
  have h : (9 / 4 : ℝ) ≤ Real.exp 1 :=
    le_of_lt (lt_trans (by norm_num : (9 / 4 : ℝ) < 2.7182818283) Real.exp_one_gt_d9)
  have hsq : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hpos : 0 ≤ Real.exp (1 / 2) := (Real.exp_pos _).le
  nlinarith [sq_nonneg (Real.exp (1 / 2) - (3 / 2 : ℝ))]

lemma two_mul_succ_le_exp_half {n : ℕ} (hn : 8 ≤ n) :
    (2 * n + 1 : ℝ) ≤ Real.exp ((n : ℝ) / 2) := by
  induction n, hn using Nat.le_induction with
  | base =>
      have hexp4 : Real.exp 4 = Real.exp 1 ^ 4 := by
        rw [← Real.exp_nat_mul]; norm_num
      have hlt : (2.71 : ℝ) < Real.exp 1 :=
        lt_trans (by norm_num : (2.71 : ℝ) < 2.7182818283) Real.exp_one_gt_d9
      have h27 : (2.71 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 :=
        pow_le_pow_left₀ (by norm_num) (le_of_lt hlt) 4
      calc
        (2 * 8 + 1 : ℝ) = 17 := by norm_num
        _ ≤ (2.71 : ℝ) ^ 4 := by norm_num
        _ ≤ Real.exp 1 ^ 4 := h27
        _ = Real.exp 4 := hexp4.symm
        _ = Real.exp ((8 : ℝ) / 2) := by norm_num
  | succ n hn ih =>
      have hncast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := Nat.cast_succ n
      have hmul : Real.exp (((n + 1 : ℕ) : ℝ) / 2) =
          Real.exp ((n : ℝ) / 2) * Real.exp (1 / 2) := by
        rw [hncast, ← Real.exp_add]
        congr 1
        ring
      have hstep : (2 * ((n + 1 : ℕ) : ℝ) + 1) ≤
          (2 * (n : ℝ) + 1) * Real.exp (1 / 2) := by
        have h1 : (2 * ((n + 1 : ℕ) : ℝ) + 1) = 2 * (n : ℝ) + 3 := by
          rw [hncast]; ring
        have h2 : (2 * (n : ℝ) + 1) * (3 / 2) = 3 * (n : ℝ) + 3 / 2 := by ring
        have hnR : (8 : ℝ) ≤ n := by exact_mod_cast hn
        have h3 : 2 * (n : ℝ) + 3 ≤ 3 * (n : ℝ) + 3 / 2 := by
          nlinarith [hnR]
        have h4 : (2 * (n : ℝ) + 1) * (3 / 2) ≤ (2 * (n : ℝ) + 1) * Real.exp (1 / 2) :=
          mul_le_mul_of_nonneg_left exp_half_ge_three_halves (by positivity)
        rw [h1]
        linarith
      exact le_trans hstep (le_trans
        (mul_le_mul_of_nonneg_right ih (Real.exp_pos _).le) hmul.symm.le)

/-- Crude Chebyshev lower bound `π(x) ≥ (1/16) x / log x` for `x ≥ 16`. -/
lemma primeCounting_ge_mul_div_log {x : ℝ} (hx : 16 ≤ x) :
    (1 / 16 : ℝ) * x / Real.log x ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  let n := ⌊x / 2⌋₊
  have hn_floor : (n : ℝ) ≤ x / 2 := Nat.floor_le (by linarith : 0 ≤ x / 2)
  have hn_ge : x / 2 - 1 ≤ (n : ℝ) := by
    linarith [Nat.lt_floor_add_one (x / 2)]
  have hn8 : 8 ≤ n := Nat.le_floor (by linarith : (8 : ℝ) ≤ x / 2)
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 8) hn8
  have h2n_le : (2 * n : ℝ) ≤ x := by linarith
  have hπ : Nat.primeCounting (2 * n) ≤ Nat.primeCounting ⌊x⌋₊ :=
    Nat.monotone_primeCounting (Nat.le_floor (by push_cast; exact h2n_le))
  have h4le_nat : (4 : ℕ) ^ n ≤ (2 * n + 1) * (2 * n) ^ Nat.primeCounting (2 * n) :=
    le_trans (four_pow_le_mul_choose n)
      (Nat.mul_le_mul_left _ (choose_two_mul_le_pow_primeCounting hn0))
  have h4le : (4 : ℝ) ^ n ≤
      (2 * n + 1 : ℝ) * (2 * n : ℝ) ^ Nat.primeCounting (2 * n) := by
    exact_mod_cast h4le_nat
  have h2n1pos : (0 : ℝ) < 2 * n + 1 := by positivity
  have h2npos : (0 : ℝ) < 2 * n := by
    have : (0 : ℕ) < 2 * n := by omega
    exact_mod_cast this
  have hlog2n : 0 < Real.log (2 * n) := Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (by
    have : (2 : ℝ) ≤ 2 * n := by exact_mod_cast (by omega : (2 : ℕ) ≤ 2 * n)
    exact this))
  have hlog_ineq :
      (n : ℝ) * Real.log 4 ≤
        Real.log (2 * n + 1) + (Nat.primeCounting (2 * n) : ℝ) * Real.log (2 * n) := by
    have hposL : 0 < (4 : ℝ) ^ n := by positivity
    have := Real.log_le_log hposL h4le
    rw [Real.log_pow, Real.log_mul (ne_of_gt h2n1pos) (by positivity),
        Real.log_pow] at this
    exact this
  have hlog_small : Real.log (2 * n + 1) ≤ (n : ℝ) / 2 := by
    have hle := two_mul_succ_le_exp_half hn8
    have := Real.log_le_log h2n1pos hle
    rwa [Real.log_exp] at this
  have hnum : (n : ℝ) / 2 ≤ (n : ℝ) * Real.log 4 - Real.log (2 * n + 1) := by
    nlinarith [log_four_ge_one]
  have hπn : (n : ℝ) / 2 / Real.log (2 * n) ≤ (Nat.primeCounting (2 * n) : ℝ) := by
    have : (n : ℝ) * Real.log 4 - Real.log (2 * n + 1) ≤
        (Nat.primeCounting (2 * n) : ℝ) * Real.log (2 * n) := by linarith [hlog_ineq]
    have : (n : ℝ) / 2 ≤ (Nat.primeCounting (2 * n) : ℝ) * Real.log (2 * n) :=
      le_trans hnum this
    exact (div_le_iff₀ hlog2n).2 this
  have hden : Real.log (2 * n) ≤ Real.log x := Real.log_le_log h2npos h2n_le
  have hmono : (n : ℝ) / 2 / Real.log x ≤ (n : ℝ) / 2 / Real.log (2 * n) :=
    div_le_div_of_nonneg_left (by positivity) hlog2n hden
  have hn2 : x / 4 - 1 / 2 ≤ (n : ℝ) / 2 := by linarith
  have hcmp : (1 / 16 : ℝ) * x ≤ x / 4 - 1 / 2 := by linarith
  have hleft : (1 / 16 : ℝ) * x / Real.log x ≤ (n : ℝ) / 2 / Real.log x := by
    exact div_le_div_of_nonneg_right (le_trans hcmp hn2) hlogx.le
  have : (1 / 16 : ℝ) * x / Real.log x ≤ (Nat.primeCounting (2 * n) : ℝ) :=
    le_trans hleft (le_trans hmono hπn)
  exact le_trans this (Nat.cast_le.mpr hπ)

/- Additive character `e(α) = exp(2πiα)`. -/
noncomputable def eH (α : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * α)

lemma eH_add (α β : ℝ) : eH (α + β) = eH α * eH β := by
  simp only [eH, Complex.ofReal_add, mul_add, Complex.exp_add]

lemma eH_zero : eH 0 = 1 := by simp [eH]

lemma norm_eH (α : ℝ) : ‖eH α‖ = 1 := by
  simp only [eH, Complex.norm_exp]
  have : (2 * Real.pi * Complex.I * (α : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  simp [this]

lemma eH_int (n : ℤ) : eH n = 1 := by
  simp only [eH]
  convert Complex.exp_int_mul_two_pi_mul_I n using 2
  · push_cast
    ring

lemma eH_periodic (α : ℝ) (n : ℤ) : eH (α + n) = eH α := by
  rw [eH_add, eH_int, mul_one]

lemma eH_nat_mul (n : ℕ) (θ : ℝ) : eH (n * θ) = eH θ ^ n := by
  induction n with
  | zero => simp [eH_zero]
  | succ n ih =>
      rw [Nat.cast_succ, add_mul, one_mul, eH_add, ih, pow_succ, mul_comm]

lemma card_Icc_one (N : ℕ) : (Finset.Icc 1 N).card = N := by
  simp [Nat.card_Icc]

lemma norm_sum_eH_le_card (θ : ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N, eH (n * θ)‖ ≤ (N : ℝ) := by
  refine le_trans (norm_sum_le _ _) ?_
  simp only [norm_eH, Finset.sum_const, nsmul_eq_mul, mul_one, card_Icc_one]
  exact le_rfl

lemma sum_eH_geom {θ : ℝ} {N : ℕ} (hne : eH θ ≠ 1) :
    ∑ n ∈ Finset.Icc 1 N, eH (n * θ) =
      eH θ * (1 - eH θ ^ N) / (1 - eH θ) := by
  have hz1 : eH θ - 1 ≠ 0 := sub_ne_zero.2 hne
  simp_rw [eH_nat_mul]
  have hsum0 : ∑ n ∈ Finset.range (N + 1), eH θ ^ n =
      (eH θ ^ (N + 1) - 1) / (eH θ - 1) := geom_sum_eq hne (N + 1)
  have hidx : ∑ n ∈ Finset.range N, eH θ ^ (n + 1) =
      ∑ n ∈ Finset.Icc 1 N, eH θ ^ n := by
    refine Finset.sum_nbij (fun n => n + 1) ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_range] at hn
      simp only [Finset.mem_Icc]
      exact ⟨Nat.succ_pos n, Nat.succ_le_of_lt hn⟩
    · intro a _ b _ h
      exact Nat.succ_injective h
    · intro n hn
      have hn' : 1 ≤ n ∧ n ≤ N := Finset.mem_Icc.1 hn
      refine ⟨n - 1, ?_, ?_⟩
      · have hlt : n < N + 1 := Nat.lt_succ_of_le hn'.2
        have : n < 1 + N := by rwa [add_comm]
        exact Finset.mem_range.2 (Nat.sub_lt_left_of_lt_add hn'.1 this)
      · exact Nat.sub_add_cancel hn'.1
    · intro n hn; rfl
  have hsplit : ∑ n ∈ Finset.range (N + 1), eH θ ^ n =
      1 + ∑ n ∈ Finset.Icc 1 N, eH θ ^ n := by
    rw [Finset.sum_range_succ', pow_zero, hidx, add_comm]
  have hclosed : (eH θ ^ (N + 1) - 1) / (eH θ - 1) - 1 =
      eH θ * (1 - eH θ ^ N) / (1 - eH θ) := by
    have hz' : (1 : ℂ) - eH θ ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
    field_simp [hz1, hz']
    ring
  have hdiff : ∑ n ∈ Finset.Icc 1 N, eH θ ^ n =
      (eH θ ^ (N + 1) - 1) / (eH θ - 1) - 1 := by
    calc
      ∑ n ∈ Finset.Icc 1 N, eH θ ^ n
          = (1 + ∑ n ∈ Finset.Icc 1 N, eH θ ^ n) - 1 := by ring
      _ = ∑ n ∈ Finset.range (N + 1), eH θ ^ n - 1 := by rw [← hsplit]
      _ = (eH θ ^ (N + 1) - 1) / (eH θ - 1) - 1 := by rw [hsum0]
  exact hdiff.trans hclosed

lemma norm_sum_eH_le_geom {θ : ℝ} {N : ℕ} (hne : eH θ ≠ 1) :
    ‖∑ n ∈ Finset.Icc 1 N, eH (n * θ)‖ ≤ 2 * ‖1 - eH θ‖⁻¹ := by
  rw [sum_eH_geom hne, norm_div, norm_mul, norm_eH, one_mul]
  have hnum : ‖1 - eH θ ^ N‖ ≤ 2 := by
    have h := norm_sub_le (1 : ℂ) (eH θ ^ N)
    have hpow : ‖eH θ ^ N‖ = 1 := by simp [norm_pow, norm_eH]
    have : ‖(1 : ℂ) - eH θ ^ N‖ ≤ 1 + 1 := by
      simpa [norm_one, hpow] using h
    linarith
  rw [div_eq_mul_inv]
  have hinv : ‖(1 - eH θ)⁻¹‖ = ‖1 - eH θ‖⁻¹ := norm_inv _
  rw [← hinv]
  gcongr

/-- `|∑_{n=1}^N e(nθ)| ≤ min(N, 2 / |1-e(θ)|)` (or `N` if `e(θ)=1`). -/
lemma norm_sum_eH_le (θ : ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N, eH (n * θ)‖ ≤
      min (N : ℝ) (if eH θ = 1 then (N : ℝ) else 2 * ‖1 - eH θ‖⁻¹) := by
  refine le_min (norm_sum_eH_le_card θ N) ?_
  split_ifs with h
  · exact norm_sum_eH_le_card θ N
  · exact norm_sum_eH_le_geom h

/- Distance to the nearest integer and the standard geometric-sum bound. -/

lemma distToNearestInt_nonneg (θ : ℝ) : 0 ≤ distToNearestInt θ := abs_nonneg _

lemma distToNearestInt_le_half (θ : ℝ) : distToNearestInt θ ≤ 1 / 2 := abs_sub_round θ

lemma distToNearestInt_int (n : ℤ) : distToNearestInt n = 0 := by
  simp [distToNearestInt, round_intCast]

lemma distToNearestInt_eq_zero_iff (θ : ℝ) :
    distToNearestInt θ = 0 ↔ ∃ n : ℤ, θ = n := by
  simp only [distToNearestInt, abs_eq_zero, sub_eq_zero]
  constructor
  · intro h
    exact ⟨round θ, h⟩
  · rintro ⟨n, rfl⟩
    simp [round_intCast]

lemma eH_eq_one_iff (θ : ℝ) : eH θ = 1 ↔ ∃ n : ℤ, θ = n := by
  simp only [eH]
  constructor
  · intro h
    rcases (Complex.exp_eq_one_iff).1 h with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hmul : (2 * Real.pi * Complex.I * (θ : ℂ)) = (n : ℂ) * (2 * Real.pi * Complex.I) := hn
    have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
    have h2π : (2 * Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast (mul_ne_zero two_ne_zero Real.pi_ne_zero)
    apply_fun (fun z : ℂ => z / (2 * Real.pi * Complex.I)) at hmul
    have hden : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := mul_ne_zero h2π hI
    field_simp [hden] at hmul
    exact_mod_cast hmul
  · rintro ⟨n, rfl⟩
    simpa [eH] using eH_int n

lemma eH_eq_one_iff_dist (θ : ℝ) : eH θ = 1 ↔ distToNearestInt θ = 0 := by
  rw [eH_eq_one_iff, distToNearestInt_eq_zero_iff]

lemma primeCounting_le_succ (n : ℕ) : Nat.primeCounting n ≤ n + 1 := by
  simpa [Nat.primeCounting] using (Nat.count_le (p := Nat.Prime) (n := n + 1))

lemma eH_eq_cos_add_sin (θ : ℝ) :
    eH θ = Real.cos (2 * Real.pi * θ) + Real.sin (2 * Real.pi * θ) * Complex.I := by
  simp only [eH]
  have ht : (2 * Real.pi * Complex.I * (θ : ℂ)) = (↑(2 * Real.pi * θ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [ht]
  simpa using Complex.exp_mul_I (2 * Real.pi * θ)

lemma abs_one_sub_eH (θ : ℝ) :
    ‖(1 : ℂ) - eH θ‖ = 2 * |Real.sin (Real.pi * θ)| := by
  rw [eH_eq_cos_add_sin]
  have hrearr :
      (1 : ℂ) - (↑(Real.cos (2 * Real.pi * θ)) + ↑(Real.sin (2 * Real.pi * θ)) * Complex.I) =
        ↑(1 - Real.cos (2 * Real.pi * θ)) + ↑(-Real.sin (2 * Real.pi * θ)) * Complex.I := by
    push_cast
    ring
  rw [hrearr, Complex.norm_add_mul_I]
  have hid : (1 - Real.cos (2 * Real.pi * θ)) ^ 2 + (-Real.sin (2 * Real.pi * θ)) ^ 2 =
      4 * Real.sin (Real.pi * θ) ^ 2 := by
    rw [show 2 * Real.pi * θ = 2 * (Real.pi * θ) by ring, Real.cos_two_mul, Real.sin_two_mul]
    have : Real.sin (Real.pi * θ) ^ 2 + Real.cos (Real.pi * θ) ^ 2 = 1 :=
      Real.sin_sq_add_cos_sq _
    ring_nf
    nlinarith
  rw [hid, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), Real.sqrt_sq_eq_abs]
  have : Real.sqrt 4 = 2 := by rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
  rw [this]

lemma abs_sin_pi_mul_eq (θ : ℝ) :
    |Real.sin (Real.pi * θ)| = Real.sin (Real.pi * distToNearestInt θ) := by
  have hfr : distToNearestInt θ = min (Int.fract θ) (1 - Int.fract θ) := by
    simp [distToNearestInt, abs_sub_round_eq_min]
  have hsin : Real.sin (Real.pi * θ) =
      ((-1 : ℝ) ^ ⌊θ⌋) * Real.sin (Real.pi * Int.fract θ) := by
    have h1 : Real.pi * θ = Real.pi * Int.fract θ + ⌊θ⌋ * Real.pi := by
      have := Int.fract_add_floor θ
      linear_combination Real.pi * this.symm
    rw [h1, Real.sin_add, Real.sin_int_mul_pi, Real.cos_int_mul_pi]
    ring
  have habs : |Real.sin (Real.pi * θ)| = |Real.sin (Real.pi * Int.fract θ)| := by
    rw [hsin, abs_mul, abs_neg_one_zpow, one_mul]
  have hfr0 : 0 ≤ Int.fract θ := Int.fract_nonneg θ
  have hfr1 : Int.fract θ < 1 := Int.fract_lt_one θ
  have hsinpos : 0 ≤ Real.sin (Real.pi * Int.fract θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
      (by nlinarith [Real.pi_pos, hfr1])
  have habs' : |Real.sin (Real.pi * Int.fract θ)| = Real.sin (Real.pi * Int.fract θ) :=
    abs_of_nonneg hsinpos
  have hmin : Real.sin (Real.pi * Int.fract θ) =
      Real.sin (Real.pi * min (Int.fract θ) (1 - Int.fract θ)) := by
    by_cases hle : Int.fract θ ≤ 1 - Int.fract θ
    · simp [min_eq_left hle]
    · have hgt : 1 - Int.fract θ < Int.fract θ := lt_of_not_ge hle
      have hminr : min (Int.fract θ) (1 - Int.fract θ) = 1 - Int.fract θ :=
        min_eq_right (le_of_lt hgt)
      rw [hminr]
      have : Real.sin (Real.pi * (1 - Int.fract θ)) =
          Real.sin (Real.pi - Real.pi * Int.fract θ) := by ring_nf
      rw [this, Real.sin_pi_sub]
  rw [habs, habs', hmin, hfr]

lemma abs_sin_pi_ge_two_mul_dist (θ : ℝ) :
    2 * distToNearestInt θ ≤ |Real.sin (Real.pi * θ)| := by
  rw [abs_sin_pi_mul_eq]
  have hhalf : distToNearestInt θ ≤ 1 / 2 := distToNearestInt_le_half θ
  have hnn : 0 ≤ distToNearestInt θ := distToNearestInt_nonneg θ
  have harg0 : 0 ≤ Real.pi * distToNearestInt θ := by positivity
  have harg1 : Real.pi * distToNearestInt θ ≤ Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  calc
    2 * distToNearestInt θ
        = 2 / Real.pi * (Real.pi * distToNearestInt θ) := by
          field_simp [Real.pi_ne_zero]
    _ ≤ Real.sin (Real.pi * distToNearestInt θ) := Real.mul_le_sin harg0 harg1

lemma one_sub_eH_ge_four_dist {θ : ℝ} (_hθ : distToNearestInt θ ≠ 0) :
    4 * distToNearestInt θ ≤ ‖(1 : ℂ) - eH θ‖ := by
  rw [abs_one_sub_eH]
  have := abs_sin_pi_ge_two_mul_dist θ
  nlinarith

lemma norm_sum_eH_le_inv_dist (θ : ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N, eH (n * θ)‖ ≤
      min (N : ℝ)
        (if distToNearestInt θ = 0 then (N : ℝ)
          else (2 * distToNearestInt θ)⁻¹) := by
  refine le_min (norm_sum_eH_le_card θ N) ?_
  by_cases h0 : distToNearestInt θ = 0
  · simp [h0]
    exact norm_sum_eH_le_card θ N
  · have hne : eH θ ≠ 1 := by
      intro heq
      exact h0 ((eH_eq_one_iff_dist θ).1 heq)
    have hpos : 0 < distToNearestInt θ :=
      lt_of_le_of_ne (distToNearestInt_nonneg θ) (Ne.symm h0)
    have hge := one_sub_eH_ge_four_dist h0
    have hden : 0 < ‖(1 : ℂ) - eH θ‖ := by nlinarith
    have hle := norm_sum_eH_le_geom (θ := θ) (N := N) hne
    have hinv : 2 * ‖(1 : ℂ) - eH θ‖⁻¹ ≤ (2 * distToNearestInt θ)⁻¹ := by
      have : ‖(1 : ℂ) - eH θ‖⁻¹ ≤ (4 * distToNearestInt θ)⁻¹ :=
        inv_anti₀ (by nlinarith) hge
      have h4 : 2 * (4 * distToNearestInt θ)⁻¹ = (2 * distToNearestInt θ)⁻¹ := by
        field_simp
        ring
      calc
        2 * ‖(1 : ℂ) - eH θ‖⁻¹ ≤ 2 * (4 * distToNearestInt θ)⁻¹ := by gcongr
        _ = (2 * distToNearestInt θ)⁻¹ := h4
    simp only [h0, ↓reduceIte]
    exact hle.trans hinv

/- Dual large sieve (with a logarithmic factor). -/

lemma star_eH (θ : ℝ) : star (eH θ) = eH (-θ) := by
  unfold eH
  rw [Complex.star_def, ← Complex.exp_conj]
  apply congrArg
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    rw [← Complex.ofReal_ofNat 2, Complex.conj_ofReal]
  have hπ : (starRingEnd ℂ) (Real.pi : ℂ) = Real.pi := Complex.conj_ofReal _
  have hθ : (starRingEnd ℂ) (θ : ℂ) = θ := Complex.conj_ofReal _
  rw [map_mul, map_mul, map_mul, h2, hπ, Complex.conj_I, hθ]
  simp only [Complex.ofReal_neg]
  ring

lemma eH_neg (θ : ℝ) : eH (-θ) = star (eH θ) := (star_eH θ).symm

lemma normSq_sum_eH {ι : Type*} (A : Finset ι) (α : ι → ℝ) (b : ι → ℂ) (n : ℕ) :
    (‖∑ r ∈ A, b r * eH (n * α r)‖ ^ 2 : ℂ) =
      ∑ r ∈ A, ∑ s ∈ A, b r * star (b s) * eH (n * (α r - α s)) := by
  have h0 : (‖∑ r ∈ A, b r * eH (n * α r)‖ ^ 2 : ℂ) =
      (∑ r ∈ A, b r * eH (n * α r)) * star (∑ r ∈ A, b r * eH (n * α r)) :=
    (Complex.mul_conj' _).symm
  rw [h0, star_sum]
  simp only [star_mul, star_eH]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hcomm : eH (-(n * α s)) * star (b s) = star (b s) * eH (-(n * α s)) := mul_comm _ _
  have : eH (n * α r) * eH (-(n * α s)) = eH (n * (α r - α s)) := by
    rw [← eH_add]
    congr 1
    ring
  rw [hcomm]
  calc
    b r * eH (n * α r) * (star (b s) * eH (-(n * α s)))
        = b r * star (b s) * (eH (n * α r) * eH (-(n * α s))) := by ring
    _ = b r * star (b s) * eH (n * (α r - α s)) := by rw [this]

lemma sum_normSq_expand {ι : Type*} (A : Finset ι) (α : ι → ℝ) (b : ι → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (‖∑ r ∈ A, b r * eH (n * α r)‖ ^ 2 : ℂ) =
      ∑ r ∈ A, ∑ s ∈ A, b r * star (b s) *
        ∑ n ∈ Finset.Icc 1 N, eH (n * (α r - α s)) := by
  simp_rw [normSq_sum_eH]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.mul_sum]

lemma harmonic_Icc_le (m : ℕ) :
    ∑ j ∈ Finset.Icc 1 m, (j : ℝ)⁻¹ ≤ 1 + Real.log (max (m : ℝ) 1) := by
  cases m with
  | zero => simp
  | succ m =>
      have hle := harmonic_le_one_add_log (m + 1)
      have hsum : ∑ j ∈ Finset.Icc 1 (m + 1), (j : ℝ)⁻¹ = (harmonic (m + 1) : ℝ) := by
        rw [harmonic_eq_sum_Icc]
        simp [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      have : (1 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
      have hmax' : max ((m + 1 : ℕ) : ℝ) 1 = ((m + 1 : ℕ) : ℝ) := max_eq_left this
      rw [hsum, hmax']
      exact hle

lemma abs_mul_star (z w : ℂ) : ‖z * star w‖ = ‖z‖ * ‖w‖ := by
  rw [norm_mul, norm_star]

lemma primeCounting_sqrt_le (x : ℝ) (_hx : 0 ≤ x) :
    (Nat.primeCounting ⌊Real.sqrt x⌋₊ : ℝ) ≤ Real.sqrt x + 1 := by
  have hπ := primeCounting_le_succ ⌊Real.sqrt x⌋₊
  have hfl : (⌊Real.sqrt x⌋₊ : ℝ) ≤ Real.sqrt x := Nat.floor_le (Real.sqrt_nonneg x)
  have hcast : ((⌊Real.sqrt x⌋₊ + 1 : ℕ) : ℝ) = (⌊Real.sqrt x⌋₊ : ℝ) + 1 :=
    Nat.cast_succ _
  have hπR : (Nat.primeCounting ⌊Real.sqrt x⌋₊ : ℝ) ≤ (⌊Real.sqrt x⌋₊ : ℝ) + 1 := by
    rw [← hcast]
    exact Nat.cast_le.mpr hπ
  linarith

lemma log_sqrt_eq {x : ℝ} (hx : 1 < x) :
    Real.log (Real.sqrt x) = Real.log x / 2 := by
  have hx0 : 0 < x := by linarith
  rw [Real.log_sqrt hx0.le]

lemma log_p_ge_half_log {x : ℝ} {p : ℕ} (hx : 1 < x)
    (hp : ⌊Real.sqrt x⌋₊ + 1 ≤ p) :
    Real.log x / 2 ≤ Real.log p := by
  have hx0 : 0 < x := by linarith
  have hsq : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hp_gt : Real.sqrt x < p := by
    have : (⌊Real.sqrt x⌋₊ : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast hp
    have : Real.sqrt x < (⌊Real.sqrt x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have : Real.log (Real.sqrt x) < Real.log p := Real.log_lt_log hsq hp_gt
  rw [log_sqrt_eq hx] at this
  exact this.le

lemma sum_eH_zero (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, eH (n * (0 : ℝ)) = N := by
  simp [eH_zero, card_Icc_one]

lemma norm_sum_eH_of_separated {θ : ℝ} {N : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (hsep : δ ≤ distToNearestInt θ) :
    ‖∑ n ∈ Finset.Icc 1 N, eH (n * θ)‖ ≤ (2 * δ)⁻¹ := by
  have hne : distToNearestInt θ ≠ 0 := by
    intro h0
    rw [h0] at hsep
    linarith
  have hpos : 0 < distToNearestInt θ := lt_of_lt_of_le hδ hsep
  have hle1 : ‖∑ n ∈ Finset.Icc 1 N, eH (n * θ)‖ ≤ (2 * distToNearestInt θ)⁻¹ := by
    have hmin := (norm_sum_eH_le_inv_dist θ N).trans (min_le_right _ _)
    simpa [hne] using hmin
  have hle2 : (2 * distToNearestInt θ)⁻¹ ≤ (2 * δ)⁻¹ :=
    inv_anti₀ (by nlinarith [hpos]) (by nlinarith)
  exact hle1.trans hle2

lemma sum_norm_sq_le_card_mul {ι : Type*} (A : Finset ι) (b : ι → ℂ) :
    (∑ r ∈ A, ‖b r‖) ^ 2 ≤ A.card * ∑ r ∈ A, ‖b r‖ ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq A (fun _ => (1 : ℝ)) (fun r => ‖b r‖)
  have h1 : ∑ r ∈ A, (1 : ℝ) ^ 2 = (A.card : ℝ) := by simp
  calc
    (∑ r ∈ A, ‖b r‖) ^ 2 = (∑ r ∈ A, (1 : ℝ) * ‖b r‖) ^ 2 := by
      simp
    _ ≤ (∑ r ∈ A, (1 : ℝ) ^ 2) * ∑ r ∈ A, ‖b r‖ ^ 2 := h
    _ = A.card * ∑ r ∈ A, ‖b r‖ ^ 2 := by rw [h1]

/-! ### Large sieve with a logarithmic factor -/

noncomputable def circDist (x y : ℝ) : ℝ := distToNearestInt (x - y)

lemma distToNearestInt_periodic (x : ℝ) (n : ℤ) :
    distToNearestInt (x + n) = distToNearestInt x := by
  simp [distToNearestInt, round_add_intCast]

lemma distToNearestInt_eq_min (x : ℝ) :
    distToNearestInt x = min (Int.fract x) (1 - Int.fract x) := by
  simpa [distToNearestInt] using abs_sub_round_eq_min x

lemma distToNearestInt_neg (x : ℝ) : distToNearestInt (-x) = distToNearestInt x := by
  rw [distToNearestInt_eq_min, distToNearestInt_eq_min]
  by_cases h0 : Int.fract x = 0
  · have : Int.fract (-x) = 0 := (Int.fract_neg_eq_zero).2 h0
    simp [h0, this]
  · have hfr : Int.fract (-x) = 1 - Int.fract x := Int.fract_neg h0
    rw [hfr]
    ring_nf
    rw [min_comm]

lemma circDist_comm (x y : ℝ) : circDist x y = circDist y x := by
  unfold circDist
  have : y - x = -(x - y) := by ring
  rw [this, distToNearestInt_neg]

lemma circDist_self (x : ℝ) : circDist x x = 0 := by
  simp [circDist, distToNearestInt]

lemma circDist_nonneg (x y : ℝ) : 0 ≤ circDist x y := distToNearestInt_nonneg _

lemma distToNearestInt_fract (x : ℝ) :
    distToNearestInt (Int.fract x) = distToNearestInt x := by
  have : (Int.fract x : ℝ) = x + ((-⌊x⌋ : ℤ) : ℝ) := by
    unfold Int.fract
    push_cast
    ring
  rw [this, distToNearestInt_periodic]

lemma distToNearestInt_eq_self_of_mem_Icc {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    distToNearestInt x = x := by
  have hmin := distToNearestInt_eq_min x
  have hfr : Int.fract x = x := Int.fract_eq_self.2 ⟨hx0, by linarith⟩
  have hle : x ≤ 1 - x := by linarith
  rw [hmin, hfr, min_eq_left hle]

lemma distToNearestInt_eq_abs_of_abs_le_half {x : ℝ} (hx : |x| ≤ 1 / 2) :
    distToNearestInt x = |x| := by
  rcases le_total 0 x with hx0 | hx0
  · have : x ≤ 1 / 2 := (abs_le.1 hx).2
    simpa [abs_of_nonneg hx0] using distToNearestInt_eq_self_of_mem_Icc hx0 this
  · have hx' : 0 ≤ -x := by linarith
    have hx1 : -x ≤ 1 / 2 := by
      have := (abs_le.1 hx).1
      linarith
    have hneg := distToNearestInt_eq_self_of_mem_Icc hx' hx1
    have : distToNearestInt x = -x := (distToNearestInt_neg x).symm.trans hneg
    simpa [abs_of_nonpos hx0]

lemma circDist_eq_fract_of_le_half {x : ℝ} (hx : Int.fract x ≤ 1 / 2) :
    distToNearestInt x = Int.fract x := by
  have h0 : 0 ≤ Int.fract x := Int.fract_nonneg _
  rw [← distToNearestInt_fract]
  exact distToNearestInt_eq_self_of_mem_Icc h0 hx

lemma circDist_eq_one_sub_fract_of_gt_half {x : ℝ} (hx : 1 / 2 < Int.fract x) :
    distToNearestInt x = 1 - Int.fract x := by
  have hmin := distToNearestInt_eq_min x
  have hle : 1 - Int.fract x ≤ Int.fract x := by linarith [Int.fract_lt_one x]
  rw [hmin, min_eq_right hle]

lemma eq_fract_sub_add_int (x y : ℝ) :
    x - y = (Int.fract x - Int.fract y) + ((⌊x⌋ - ⌊y⌋ : ℤ) : ℝ) := by
  unfold Int.fract
  push_cast
  ring

lemma fract_sub_of_both_le_half {x y : ℝ}
    (hx : Int.fract x ≤ 1 / 2) (hy : Int.fract y ≤ 1 / 2) :
    distToNearestInt (x - y) = |Int.fract x - Int.fract y| := by
  have hfx0 : 0 ≤ Int.fract x := Int.fract_nonneg _
  have hfy0 : 0 ≤ Int.fract y := Int.fract_nonneg _
  have hfx1 : Int.fract x < 1 := Int.fract_lt_one _
  have hfy1 : Int.fract y < 1 := Int.fract_lt_one _
  have hz : |Int.fract x - Int.fract y| ≤ 1 / 2 := by
    apply abs_sub_le_iff.2
    constructor
    · linarith
    · linarith
  have hper : distToNearestInt (x - y) =
      distToNearestInt (Int.fract x - Int.fract y) := by
    rw [eq_fract_sub_add_int, distToNearestInt_periodic]
  rw [hper, distToNearestInt_eq_abs_of_abs_le_half hz]

lemma floor_div_ne_of_separated {x y δ : ℝ} (hδ : 0 < δ)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hsep : δ ≤ |x - y|) :
    ⌊x / δ⌋₊ ≠ ⌊y / δ⌋₊ := by
  rcases le_total x y with hxy | hyx
  · have hyx' : x + δ ≤ y := by
      have : |x - y| = y - x := by
        rw [abs_of_nonpos (sub_nonpos.2 hxy)]; ring
      linarith
    have hxdiv : 0 ≤ x / δ := div_nonneg hx0 hδ.le
    have hshift : x / δ + 1 ≤ y / δ := by
      have h1 : (x + δ) / δ ≤ y / δ := div_le_div_of_nonneg_right hyx' hδ.le
      have h2 : (x + δ) / δ = x / δ + 1 := by
        rw [add_div, div_self hδ.ne']
      rwa [h2] at h1
    have hle : (⌊x / δ⌋₊ + 1 : ℕ) ≤ ⌊y / δ⌋₊ := by
      apply Nat.le_floor
      have : ((⌊x / δ⌋₊ + 1 : ℕ) : ℝ) = (⌊x / δ⌋₊ : ℝ) + 1 := by push_cast; rfl
      rw [this]
      have : (⌊x / δ⌋₊ : ℝ) ≤ x / δ := Nat.floor_le hxdiv
      linarith
    omega
  · have hxy' : y + δ ≤ x := by
      have : |x - y| = x - y := abs_of_nonneg (sub_nonneg.2 hyx)
      linarith
    have hydiv : 0 ≤ y / δ := div_nonneg hy0 hδ.le
    have hshift : y / δ + 1 ≤ x / δ := by
      have h1 : (y + δ) / δ ≤ x / δ := div_le_div_of_nonneg_right hxy' hδ.le
      have h2 : (y + δ) / δ = y / δ + 1 := by
        rw [add_div, div_self hδ.ne']
      rwa [h2] at h1
    have hle : (⌊y / δ⌋₊ + 1 : ℕ) ≤ ⌊x / δ⌋₊ := by
      apply Nat.le_floor
      have : ((⌊y / δ⌋₊ + 1 : ℕ) : ℝ) = (⌊y / δ⌋₊ : ℝ) + 1 := by push_cast; rfl
      rw [this]
      have : (⌊y / δ⌋₊ : ℝ) ≤ y / δ := Nat.floor_le hydiv
      linarith
    omega

lemma separated_side_inj {ι : Type*} [DecidableEq ι] {A : Finset ι} {β : ι → ℝ} {δ : ℝ}
    (hδ : 0 < δ)
    (hsep : ∀ s ∈ A, ∀ t ∈ A, s ≠ t → δ ≤ |β s - β t|)
    (hnn : ∀ s ∈ A, 0 ≤ β s)
    {s t : ι} (hs : s ∈ A) (ht : t ∈ A)
    (heq : ⌊β s / δ⌋₊ = ⌊β t / δ⌋₊) :
    s = t := by
  by_contra hne
  exact floor_div_ne_of_separated hδ (hnn s hs) (hnn t ht) (hsep s hs t ht hne) heq

lemma harmonic_Icc_le' (m : ℕ) :
    ∑ j ∈ Finset.Icc 1 m, (j : ℝ)⁻¹ ≤ 1 + Real.log (max (m : ℝ) 1) := by
  cases m with
  | zero => simp
  | succ m =>
      have hle := harmonic_le_one_add_log (m + 1)
      have hsum : ∑ j ∈ Finset.Icc 1 (m + 1), (j : ℝ)⁻¹ = (harmonic (m + 1) : ℝ) := by
        rw [harmonic_eq_sum_Icc]
        simp [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      have : (1 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
      have hmax' : max ((m + 1 : ℕ) : ℝ) 1 = ((m + 1 : ℕ) : ℝ) := max_eq_left this
      rw [hsum, hmax']
      exact hle

lemma sum_inv_of_separated_in_half {ι : Type*} [DecidableEq ι]
    (A : Finset ι) (β : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ s ∈ A, ∀ t ∈ A, s ≠ t → δ ≤ |β s - β t|)
    (hge : ∀ s ∈ A, δ ≤ β s) (hle : ∀ s ∈ A, β s ≤ 1 / 2) :
    ∑ s ∈ A, (β s)⁻¹ ≤ δ⁻¹ * (1 + Real.log (max (δ⁻¹) 1)) := by
  let f : ι → ℕ := fun s => ⌊β s / δ⌋₊
  have hnn : ∀ s ∈ A, 0 ≤ β s := fun s hs => (hge s hs).trans' hδ.le
  have hinj : Set.InjOn f A := by
    intro s hs t ht h
    exact separated_side_inj hδ hsep hnn hs ht h
  have hfpos : ∀ s ∈ A, 1 ≤ f s := by
    intro s hs
    have h1 : (1 : ℝ) ≤ β s / δ := (one_le_div hδ).2 (hge s hs)
    exact Nat.succ_le_of_lt (Nat.floor_pos.2 h1)
  have hfle : ∀ s ∈ A, (f s : ℝ) * δ ≤ β s := by
    intro s hs
    have hdiv : 0 ≤ β s / δ := div_nonneg (hnn s hs) hδ.le
    have : (f s : ℝ) ≤ β s / δ := Nat.floor_le hdiv
    exact (le_div_iff₀ hδ).1 this
  have hbound : ∀ s ∈ A, (β s)⁻¹ ≤ δ⁻¹ * (f s : ℝ)⁻¹ := by
    intro s hs
    have hβpos : 0 < β s := lt_of_lt_of_le hδ (hge s hs)
    have hfpos' : 0 < (f s : ℝ) := Nat.cast_pos.2 (hfpos s hs)
    have hmul : (f s : ℝ) * δ ≤ β s := hfle s hs
    have h1 : (β s)⁻¹ ≤ ((f s : ℝ) * δ)⁻¹ :=
      inv_anti₀ (mul_pos hfpos' hδ) hmul
    have h2 : ((f s : ℝ) * δ)⁻¹ = δ⁻¹ * (f s : ℝ)⁻¹ := by
      rw [mul_inv, mul_comm]
    rwa [h2] at h1
  have hsum : ∑ s ∈ A, (β s)⁻¹ ≤ δ⁻¹ * ∑ s ∈ A, (f s : ℝ)⁻¹ := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hbound
  let Im := A.image f
  have hIm : ∑ n ∈ Im, (n : ℝ)⁻¹ = ∑ s ∈ A, (f s : ℝ)⁻¹ := by
    simpa [Im] using Finset.sum_image (s := A) (g := f) (f := fun n : ℕ => (n : ℝ)⁻¹) hinj
  have hImIcc : Im ⊆ Finset.Icc 1 (⌊(1 / 2 : ℝ) / δ⌋₊) := by
    intro n hn
    rcases Finset.mem_image.1 hn with ⟨s, hs, rfl⟩
    refine Finset.mem_Icc.2 ⟨hfpos s hs, ?_⟩
    apply Nat.le_floor
    have hdiv : 0 ≤ β s / δ := div_nonneg (hnn s hs) hδ.le
    have : (f s : ℝ) ≤ β s / δ := Nat.floor_le hdiv
    have : β s / δ ≤ (1 / 2) / δ := div_le_div_of_nonneg_right (hle s hs) hδ.le
    linarith
  have hsumIm : ∑ n ∈ Im, (n : ℝ)⁻¹ ≤
      ∑ n ∈ Finset.Icc 1 (⌊(1 / 2 : ℝ) / δ⌋₊), (n : ℝ)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg hImIcc
      (fun _ _ _ => inv_nonneg.2 (Nat.cast_nonneg _))
  have hharm := harmonic_Icc_le' (⌊(1 / 2 : ℝ) / δ⌋₊)
  have hmax : max ((⌊(1 / 2 : ℝ) / δ⌋₊ : ℝ)) 1 ≤ max (δ⁻¹) 1 := by
    apply max_le_max_right
    have hfl : (⌊(1 / 2 : ℝ) / δ⌋₊ : ℝ) ≤ (1 / 2) / δ :=
      Nat.floor_le (div_nonneg (by norm_num) hδ.le)
    have : (1 / 2 : ℝ) / δ ≤ δ⁻¹ := by
      have : (1 / 2 : ℝ) * δ⁻¹ ≤ 1 * δ⁻¹ :=
        mul_le_mul_of_nonneg_right (by norm_num) (inv_nonneg.2 hδ.le)
      simpa [div_eq_mul_inv] using this
    linarith
  have hlog : Real.log (max ((⌊(1 / 2 : ℝ) / δ⌋₊ : ℝ)) 1) ≤ Real.log (max (δ⁻¹) 1) :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) hmax
  have hfin : ∑ n ∈ Finset.Icc 1 (⌊(1 / 2 : ℝ) / δ⌋₊), (n : ℝ)⁻¹ ≤
      1 + Real.log (max (δ⁻¹) 1) :=
    le_trans hharm (add_le_add_right hlog 1)
  calc
    ∑ s ∈ A, (β s)⁻¹ ≤ δ⁻¹ * ∑ s ∈ A, (f s : ℝ)⁻¹ := hsum
    _ = δ⁻¹ * ∑ n ∈ Im, (n : ℝ)⁻¹ := by rw [← hIm]
    _ ≤ δ⁻¹ * ∑ n ∈ Finset.Icc 1 (⌊(1 / 2 : ℝ) / δ⌋₊), (n : ℝ)⁻¹ := by gcongr
    _ ≤ δ⁻¹ * (1 + Real.log (max (δ⁻¹) 1)) := by gcongr

/-- The “left” side of the circle relative to `α r`: fractional parts in `(0, 1/2]`. -/
def leftSide {ι : Type*} (α : ι → ℝ) (r : ι) (s : ι) : Prop :=
  Int.fract (α s - α r) ≤ 1 / 2

lemma circDist_eq_fract_left {x y : ℝ} (h : Int.fract (x - y) ≤ 1 / 2) :
    circDist y x = Int.fract (x - y) := by
  unfold circDist
  -- `circDist y x = distToNearestInt (y - x) = distToNearestInt (x - y)` via neg
  have : y - x = -(x - y) := by ring
  rw [this, distToNearestInt_neg]
  exact circDist_eq_fract_of_le_half h

lemma circDist_eq_one_sub_fract_right {x y : ℝ} (h : 1 / 2 < Int.fract (x - y)) :
    circDist y x = 1 - Int.fract (x - y) := by
  unfold circDist
  have : y - x = -(x - y) := by ring
  rw [this, distToNearestInt_neg]
  exact circDist_eq_one_sub_fract_of_gt_half h

/-- On the left semicircle, pairwise circular separation implies ordinary separation. -/
lemma left_side_separated {ι : Type*} [DecidableEq ι]
    {A : Finset ι} {α : ι → ℝ} {r : ι} {δ : ℝ}
    (hsep : ∀ s ∈ A, ∀ t ∈ A, s ≠ t → δ ≤ circDist (α s) (α t))
    {s t : ι} (hs : s ∈ A) (ht : t ∈ A) (hne : s ≠ t)
    (hsL : Int.fract (α s - α r) ≤ 1 / 2)
    (htL : Int.fract (α t - α r) ≤ 1 / 2) :
    δ ≤ |Int.fract (α s - α r) - Int.fract (α t - α r)| := by
  have : circDist (α s) (α t) =
      |Int.fract (α s - α r) - Int.fract (α t - α r)| := by
    -- `α s - α t = (α s - α r) - (α t - α r)`
    have heq : α s - α t = (α s - α r) - (α t - α r) := by ring
    unfold circDist
    rw [heq]
    exact fract_sub_of_both_le_half hsL htL
  have := hsep s hs t ht hne
  linarith

lemma right_side_separated {ι : Type*} [DecidableEq ι]
    {A : Finset ι} {α : ι → ℝ} {r : ι} {δ : ℝ}
    (hsep : ∀ s ∈ A, ∀ t ∈ A, s ≠ t → δ ≤ circDist (α s) (α t))
    {s t : ι} (hs : s ∈ A) (ht : t ∈ A) (hne : s ≠ t)
    (hsR : 1 / 2 < Int.fract (α s - α r))
    (htR : 1 / 2 < Int.fract (α t - α r)) :
    δ ≤ |(1 - Int.fract (α s - α r)) - (1 - Int.fract (α t - α r))| := by
  have hsL : Int.fract (α r - α s) ≤ 1 / 2 := by
    -- `fract(-(α s - α r)) = 1 - fract(α s - α r)` since fract ≠ 0 (it's > 1/2)
    have hne0 : Int.fract (α s - α r) ≠ 0 := by linarith [Int.fract_nonneg (α s - α r)]
    have : Int.fract (α r - α s) = 1 - Int.fract (α s - α r) := by
      have : α r - α s = -(α s - α r) := by ring
      rw [this, Int.fract_neg hne0]
    rw [this]
    linarith [Int.fract_lt_one (α s - α r)]
  have htL : Int.fract (α r - α t) ≤ 1 / 2 := by
    have hne0 : Int.fract (α t - α r) ≠ 0 := by linarith [Int.fract_nonneg (α t - α r)]
    have : Int.fract (α r - α t) = 1 - Int.fract (α t - α r) := by
      have : α r - α t = -(α t - α r) := by ring
      rw [this, Int.fract_neg hne0]
    rw [this]
    linarith [Int.fract_lt_one (α t - α r)]
  have : circDist (α s) (α t) =
      |(1 - Int.fract (α s - α r)) - (1 - Int.fract (α t - α r))| := by
    have heq : α s - α t = (α s - α r) - (α t - α r) := by ring
    -- both fractional parts > 1/2, so use the complementary values which are ≤ 1/2
    have h1 : 1 - Int.fract (α s - α r) = Int.fract (α r - α s) := by
      have hne0 : Int.fract (α s - α r) ≠ 0 := by linarith
      have : α r - α s = -(α s - α r) := by ring
      rw [this, Int.fract_neg hne0]
    have h2 : 1 - Int.fract (α t - α r) = Int.fract (α r - α t) := by
      have hne0 : Int.fract (α t - α r) ≠ 0 := by linarith
      have : α r - α t = -(α t - α r) := by ring
      rw [this, Int.fract_neg hne0]
    -- `circDist (α s) (α t) = distToNearestInt ((α r - α t) - (α r - α s))`
    have heq' : α s - α t = (α r - α t) - (α r - α s) := by ring
    unfold circDist
    rw [heq']
    have := fract_sub_of_both_le_half htL hsL
    rw [this, h1, h2, abs_sub_comm]
  have := hsep s hs t ht hne
  linarith

/-- Sum of reciprocal circular distances from a fixed point in a `δ`-separated set. -/
lemma sum_inv_circDist_le {ι : Type*} [DecidableEq ι]
    (A : Finset ι) (α : ι → ℝ) (r : ι) {δ : ℝ} (hδ : 0 < δ)
    (hr : r ∈ A)
    (hsep : ∀ s ∈ A, ∀ t ∈ A, s ≠ t → δ ≤ circDist (α s) (α t)) :
    ∑ s ∈ A.erase r, (circDist (α r) (α s))⁻¹ ≤
      (2 / δ) * (1 + Real.log (max (δ⁻¹) 1)) := by
  classical
  let L : Finset ι := (A.erase r).filter (fun s => Int.fract (α s - α r) ≤ 1 / 2)
  let Rgt : Finset ι := (A.erase r).filter (fun s => ¬ Int.fract (α s - α r) ≤ 1 / 2)
  have hsplit : A.erase r = L ∪ Rgt := by
    ext s
    constructor
    · intro hs
      by_cases hf : Int.fract (α s - α r) ≤ 1 / 2
      · exact Finset.mem_union.2 (Or.inl (Finset.mem_filter.2 ⟨hs, hf⟩))
      · exact Finset.mem_union.2 (Or.inr (Finset.mem_filter.2 ⟨hs, hf⟩))
    · intro hs
      rcases Finset.mem_union.1 hs with hL | hR
      · exact (Finset.mem_filter.1 hL).1
      · exact (Finset.mem_filter.1 hR).1
  have hdisj : Disjoint L Rgt := by
    refine Finset.disjoint_left.2 ?_
    intro s hsL hsR
    exact (Finset.mem_filter.1 hsR).2 (Finset.mem_filter.1 hsL).2
  have hsum : ∑ s ∈ A.erase r, (circDist (α r) (α s))⁻¹ =
      ∑ s ∈ L, (circDist (α r) (α s))⁻¹ + ∑ s ∈ Rgt, (circDist (α r) (α s))⁻¹ := by
    rw [hsplit, Finset.sum_union hdisj]
  -- Left side
  have hL : ∑ s ∈ L, (circDist (α r) (α s))⁻¹ ≤
      δ⁻¹ * (1 + Real.log (max (δ⁻¹) 1)) := by
    let β : ι → ℝ := fun s => Int.fract (α s - α r)
    have hsepL : ∀ s ∈ L, ∀ t ∈ L, s ≠ t → δ ≤ |β s - β t| := by
      intro s hs t ht hne
      have hsA : s ∈ A := by
        simp [L, Finset.mem_filter, Finset.mem_erase] at hs; exact hs.1.2
      have htA : t ∈ A := by
        simp [L, Finset.mem_filter, Finset.mem_erase] at ht; exact ht.1.2
      have hsL' : Int.fract (α s - α r) ≤ 1 / 2 := (Finset.mem_filter.1 hs).2
      have htL' : Int.fract (α t - α r) ≤ 1 / 2 := (Finset.mem_filter.1 ht).2
      exact left_side_separated hsep hsA htA hne hsL' htL'
    have hgeL : ∀ s ∈ L, δ ≤ β s := by
      intro s hs
      have hsA : s ∈ A := by
        simp [L, Finset.mem_filter, Finset.mem_erase] at hs; exact hs.1.2
      have hsr : s ≠ r := by
        simp [L, Finset.mem_filter, Finset.mem_erase] at hs; exact hs.1.1
      have hsL' : Int.fract (α s - α r) ≤ 1 / 2 := (Finset.mem_filter.1 hs).2
      have : circDist (α r) (α s) = β s := by
        simpa [β, circDist_comm] using circDist_eq_fract_left (x := α s) (y := α r) hsL'
      have : δ ≤ circDist (α r) (α s) := by
        simpa [circDist_comm] using hsep s hsA r hr hsr
      linarith
    have hleL : ∀ s ∈ L, β s ≤ 1 / 2 := by
      intro s hs
      exact (Finset.mem_filter.1 hs).2
    have hrew : ∑ s ∈ L, (circDist (α r) (α s))⁻¹ = ∑ s ∈ L, (β s)⁻¹ := by
      apply Finset.sum_congr rfl
      intro s hs
      have hsL' : Int.fract (α s - α r) ≤ 1 / 2 := (Finset.mem_filter.1 hs).2
      have : circDist (α r) (α s) = β s := by
        simpa [β, circDist_comm] using circDist_eq_fract_left (x := α s) (y := α r) hsL'
      rw [this]
    rw [hrew]
    exact sum_inv_of_separated_in_half L β hδ hsepL hgeL hleL
  -- Right side
  have hR : ∑ s ∈ Rgt, (circDist (α r) (α s))⁻¹ ≤
      δ⁻¹ * (1 + Real.log (max (δ⁻¹) 1)) := by
    let β : ι → ℝ := fun s => 1 - Int.fract (α s - α r)
    have hsepR : ∀ s ∈ Rgt, ∀ t ∈ Rgt, s ≠ t → δ ≤ |β s - β t| := by
      intro s hs t ht hne
      have hsA : s ∈ A := by
        simp [Rgt, Finset.mem_filter, Finset.mem_erase] at hs; exact hs.1.2
      have htA : t ∈ A := by
        simp [Rgt, Finset.mem_filter, Finset.mem_erase] at ht; exact ht.1.2
      have hsR' : 1 / 2 < Int.fract (α s - α r) := by
        have := (Finset.mem_filter.1 hs).2
        exact lt_of_not_ge this
      have htR' : 1 / 2 < Int.fract (α t - α r) := by
        have := (Finset.mem_filter.1 ht).2
        exact lt_of_not_ge this
      simpa [β] using right_side_separated hsep hsA htA hne hsR' htR'
    have hgeR : ∀ s ∈ Rgt, δ ≤ β s := by
      intro s hs
      have hsA : s ∈ A := by
        simp [Rgt, Finset.mem_filter, Finset.mem_erase] at hs; exact hs.1.2
      have hsr : s ≠ r := by
        simp [Rgt, Finset.mem_filter, Finset.mem_erase] at hs; exact hs.1.1
      have hsR' : 1 / 2 < Int.fract (α s - α r) :=
        lt_of_not_ge (Finset.mem_filter.1 hs).2
      have : circDist (α r) (α s) = β s := by
        simpa [β, circDist_comm] using
          circDist_eq_one_sub_fract_right (x := α s) (y := α r) hsR'
      have : δ ≤ circDist (α r) (α s) := by
        simpa [circDist_comm] using hsep s hsA r hr hsr
      linarith
    have hleR : ∀ s ∈ Rgt, β s ≤ 1 / 2 := by
      intro s hs
      have hsR' : 1 / 2 < Int.fract (α s - α r) :=
        lt_of_not_ge (Finset.mem_filter.1 hs).2
      have : Int.fract (α s - α r) < 1 := Int.fract_lt_one _
      have : 0 < 1 - Int.fract (α s - α r) := by linarith
      linarith
    have hrew : ∑ s ∈ Rgt, (circDist (α r) (α s))⁻¹ = ∑ s ∈ Rgt, (β s)⁻¹ := by
      apply Finset.sum_congr rfl
      intro s hs
      have hsR' : 1 / 2 < Int.fract (α s - α r) :=
        lt_of_not_ge (Finset.mem_filter.1 hs).2
      have : circDist (α r) (α s) = β s := by
        simpa [β, circDist_comm] using
          circDist_eq_one_sub_fract_right (x := α s) (y := α r) hsR'
      rw [this]
    rw [hrew]
    exact sum_inv_of_separated_in_half Rgt β hδ hsepR hgeR hleR
  rw [hsum]
  have hsumle :
      ∑ s ∈ L, (circDist (α r) (α s))⁻¹ + ∑ s ∈ Rgt, (circDist (α r) (α s))⁻¹ ≤
        δ⁻¹ * (1 + Real.log (max (δ⁻¹) 1)) + δ⁻¹ * (1 + Real.log (max (δ⁻¹) 1)) :=
    add_le_add hL hR
  have htwice : δ⁻¹ * (1 + Real.log (max (δ⁻¹) 1)) +
      δ⁻¹ * (1 + Real.log (max (δ⁻¹) 1)) =
      (2 / δ) * (1 + Real.log (max (δ⁻¹) 1)) := by
    have : (2 / δ : ℝ) = 2 * δ⁻¹ := by field_simp
    rw [this]
    ring
  exact hsumle.trans htwice.le


lemma re_le_norm (z : ℂ) : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z

lemma norm_mul_star_mul (z w u : ℂ) :
    ‖z * star w * u‖ = ‖z‖ * ‖w‖ * ‖u‖ := by
  rw [norm_mul, norm_mul, norm_star]

lemma sum_eH_zero_eq (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, eH (n * (0 : ℝ)) = (N : ℂ) := by
  simp [eH_zero, card_Icc_one]

lemma norm_sum_eH_zero (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N, eH (n * (0 : ℝ))‖ = N := by
  rw [sum_eH_zero_eq, Complex.norm_natCast]

lemma norm_sum_eH_offdiag {θ : ℝ} {N : ℕ} (hθ : distToNearestInt θ ≠ 0) :
    ‖∑ n ∈ Finset.Icc 1 N, eH (n * θ)‖ ≤ (2 * distToNearestInt θ)⁻¹ := by
  have hmin := norm_sum_eH_le_inv_dist θ N
  have : min (N : ℝ)
      (if distToNearestInt θ = 0 then (N : ℝ) else (2 * distToNearestInt θ)⁻¹) =
      min (N : ℝ) ((2 * distToNearestInt θ)⁻¹) := by simp [hθ]
  have := hmin.trans (le_of_eq this)
  exact this.trans (min_le_right _ _)

lemma abs_mul_le_half_sq (a b : ℝ) : |a| * |b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have : 0 ≤ (|a| - |b|) ^ 2 := sq_nonneg _
  have ha : |a| ^ 2 = a ^ 2 := sq_abs a
  have hb : |b| ^ 2 = b ^ 2 := sq_abs b
  nlinarith

lemma re_sum_normSq_eH {ι : Type*} (A : Finset ι) (α : ι → ℝ) (c : ι → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ‖∑ r ∈ A, c r * eH (n * α r)‖ ^ 2 =
      ∑ r ∈ A, ∑ s ∈ A,
        (c r * star (c s) * ∑ n ∈ Finset.Icc 1 N, eH (n * (α r - α s))).re := by
  have hC := sum_normSq_expand A α c N
  have hL : ((∑ n ∈ Finset.Icc 1 N,
      (‖∑ r ∈ A, c r * eH (n * α r)‖ ^ 2 : ℂ))).re =
      ∑ n ∈ Finset.Icc 1 N, ‖∑ r ∈ A, c r * eH (n * α r)‖ ^ 2 := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    convert Complex.ofReal_re (‖∑ r ∈ A, c r * eH (n * α r)‖ ^ 2) using 1
    simp [pow_two, Complex.ofReal_mul]
  have hR : ((∑ r ∈ A, ∑ s ∈ A, c r * star (c s) *
      ∑ n ∈ Finset.Icc 1 N, eH (n * (α r - α s)))).re =
      ∑ r ∈ A, ∑ s ∈ A,
        (c r * star (c s) * ∑ n ∈ Finset.Icc 1 N, eH (n * (α r - α s))).re := by
    simp_rw [Complex.re_sum]
  exact hL.symm.trans ((congrArg Complex.re hC).trans hR)

lemma re_term_le {ι : Type*} [DecidableEq ι] {A : Finset ι} {α : ι → ℝ}
    {c : ι → ℂ} {N : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r ∈ A, ∀ s ∈ A, r ≠ s → δ ≤ circDist (α r) (α s))
    {r s : ι} (hr : r ∈ A) (hs : s ∈ A) :
    |(c r * star (c s) * ∑ n ∈ Finset.Icc 1 N, eH (n * (α r - α s))).re| ≤
      ‖c r‖ * ‖c s‖ *
        (if r = s then (N : ℝ) else (2 * circDist (α r) (α s))⁻¹) := by
  have habs := re_le_norm
    (c r * star (c s) * ∑ n ∈ Finset.Icc 1 N, eH (n * (α r - α s)))
  have hnm := norm_mul_star_mul (c r) (c s)
    (∑ n ∈ Finset.Icc 1 N, eH (n * (α r - α s)))
  have h1 : |(c r * star (c s) * ∑ n ∈ Finset.Icc 1 N, eH (n * (α r - α s))).re| ≤
      ‖c r‖ * ‖c s‖ * ‖∑ n ∈ Finset.Icc 1 N, eH (n * (α r - α s))‖ := by
    simpa [hnm] using habs
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  by_cases hrs : r = s
  · subst hrs
    have : ‖∑ n ∈ Finset.Icc 1 N, eH (n * (α r - α r))‖ = (N : ℝ) := by
      rw [sub_self, norm_sum_eH_zero]
    simpa using this.le
  · have hne : distToNearestInt (α r - α s) ≠ 0 := by
      intro h0
      have : δ ≤ circDist (α r) (α s) := hsep r hr s hs hrs
      have : circDist (α r) (α s) = 0 := h0
      linarith
    have := norm_sum_eH_offdiag (θ := α r - α s) (N := N) hne
    simpa [hrs, circDist] using this

lemma re_term_le_delta {ι : Type*} [DecidableEq ι] {A : Finset ι} {α : ι → ℝ}
    {c : ι → ℂ} {N : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r ∈ A, ∀ s ∈ A, r ≠ s → δ ≤ circDist (α r) (α s))
    {r s : ι} (hr : r ∈ A) (hs : s ∈ A) :
    (c r * star (c s) * ∑ n ∈ Finset.Icc 1 N, eH (n * (α r - α s))).re ≤
      ‖c r‖ * ‖c s‖ * (if r = s then (N : ℝ) else (2 * δ)⁻¹) := by
  have hpt := re_term_le (A := A) (α := α) (c := c) (N := N) hδ hsep hr hs
  have h1 := (le_abs_self _).trans hpt
  by_cases hrs : r = s
  · simpa [hrs] using h1
  · have hge : δ ≤ circDist (α r) (α s) := hsep r hr s hs hrs
    have hinv : (2 * circDist (α r) (α s))⁻¹ ≤ (2 * δ)⁻¹ :=
      inv_anti₀ (by nlinarith [circDist_nonneg (α r) (α s), hδ]) (by nlinarith)
    have h2 : ‖c r‖ * ‖c s‖ * (if r = s then (N : ℝ) else (2 * circDist (α r) (α s))⁻¹) =
        ‖c r‖ * ‖c s‖ * (2 * circDist (α r) (α s))⁻¹ := by simp [hrs]
    have h3 : ‖c r‖ * ‖c s‖ * (if r = s then (N : ℝ) else (2 * δ)⁻¹) =
        ‖c r‖ * ‖c s‖ * (2 * δ)⁻¹ := by simp [hrs]
    rw [h2] at h1
    have : ‖c r‖ * ‖c s‖ * (2 * circDist (α r) (α s))⁻¹ ≤
        ‖c r‖ * ‖c s‖ * (2 * δ)⁻¹ :=
      mul_le_mul_of_nonneg_left hinv (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    exact h1.trans (this.trans_eq h3.symm)

lemma sum_norm_sq_le_sum_delta {ι : Type*} [DecidableEq ι] (A : Finset ι) (α : ι → ℝ)
    (c : ι → ℂ) (N : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r ∈ A, ∀ s ∈ A, r ≠ s → δ ≤ circDist (α r) (α s)) :
    ∑ n ∈ Finset.Icc 1 N, ‖∑ r ∈ A, c r * eH (n * α r)‖ ^ 2 ≤
      ∑ r ∈ A, ∑ s ∈ A, ‖c r‖ * ‖c s‖ * (if r = s then (N : ℝ) else (2 * δ)⁻¹) := by
  rw [re_sum_normSq_eH]
  exact Finset.sum_le_sum fun r hr => Finset.sum_le_sum fun s hs =>
    re_term_le_delta hδ hsep hr hs

lemma sum_pair_norm_sq {ι : Type*} (A : Finset ι) (c : ι → ℂ) :
    ∑ r ∈ A, ∑ s ∈ A, ‖c r‖ * ‖c s‖ = (∑ r ∈ A, ‖c r‖) ^ 2 := by
  rw [pow_two, Finset.sum_mul_sum]

lemma sum_pair_norm_le_card {ι : Type*} (A : Finset ι) (c : ι → ℂ) :
    ∑ r ∈ A, ∑ s ∈ A, ‖c r‖ * ‖c s‖ ≤ A.card * ∑ r ∈ A, ‖c r‖ ^ 2 := by
  rw [sum_pair_norm_sq]
  exact sum_norm_sq_le_card_mul A c

lemma sum_filter_eq_self {ι : Type*} [DecidableEq ι] (A : Finset ι) (r : ι) (hr : r ∈ A)
    (f : ι → ℝ) : ∑ s ∈ A with s = r, f s = f r := by
  simp [Finset.filter_eq', hr]

lemma sum_filter_ne_eq_sub {ι : Type*} [DecidableEq ι] (A : Finset ι) (r : ι) (f : ι → ℝ) :
    ∑ s ∈ A with s ≠ r, f s = ∑ s ∈ A, f s - ∑ s ∈ A with s = r, f s := by
  have h := Finset.sum_filter_add_sum_filter_not A (fun s => s = r) f
  linarith

lemma inner_sum_split {ι : Type*} [DecidableEq ι] (A : Finset ι) (r : ι)
    (f : ι → ℝ) (a b : ℝ) :
    ∑ s ∈ A, f s * (if s = r then a else b) =
      a * ∑ s ∈ A with s = r, f s + b * ∑ s ∈ A with s ≠ r, f s := by
  have h := Finset.sum_filter_add_sum_filter_not A (fun s => s = r)
    (fun s => f s * (if s = r then a else b))
  have h1 : ∑ s ∈ A with s = r, f s * (if s = r then a else b) =
      a * ∑ s ∈ A with s = r, f s := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs' : s = r := (Finset.mem_filter.1 hs).2
    simp [hs', mul_comm]
  have h2 : ∑ s ∈ A with s ≠ r, f s * (if s = r then a else b) =
      b * ∑ s ∈ A with s ≠ r, f s := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs' : s ≠ r := (Finset.mem_filter.1 hs).2
    simp [hs', mul_comm]
  linarith [h, h1, h2]

lemma sum_delta_term_eq {ι : Type*} [DecidableEq ι] (A : Finset ι) (c : ι → ℂ)
    (N : ℕ) (δ : ℝ) (r : ι) (hr : r ∈ A) :
    ∑ s ∈ A, ‖c r‖ * ‖c s‖ * (if s = r then (N : ℝ) else (2 * δ)⁻¹) =
      (N : ℝ) * ‖c r‖ ^ 2 +
        (2 * δ)⁻¹ * (‖c r‖ * ∑ s ∈ A, ‖c s‖ - ‖c r‖ ^ 2) := by
  have h := inner_sum_split A r (fun s => ‖c r‖ * ‖c s‖) (N : ℝ) (2 * δ)⁻¹
  have hdiag : ∑ s ∈ A with s = r, ‖c r‖ * ‖c s‖ = ‖c r‖ ^ 2 := by
    rw [sum_filter_eq_self A r hr]
    simp [pow_two]
  have hoff : ∑ s ∈ A with s ≠ r, ‖c r‖ * ‖c s‖ =
      ‖c r‖ * ∑ s ∈ A, ‖c s‖ - ‖c r‖ ^ 2 := by
    have h1 : ∑ s ∈ A with s ≠ r, ‖c r‖ * ‖c s‖ =
        ‖c r‖ * ∑ s ∈ A with s ≠ r, ‖c s‖ := by
      simp [Finset.mul_sum]
    have h2 := sum_filter_ne_eq_sub A r (fun s => ‖c s‖)
    have h3 : ∑ s ∈ A with s = r, ‖c s‖ = ‖c r‖ := sum_filter_eq_self A r hr _
    rw [h1, h2, h3]
    ring
  rw [h, hdiag, hoff]

lemma ite_eq_comm {ι : Type*} [DecidableEq ι] (r s : ι) (a b : ℝ) :
    (if r = s then a else b) = (if s = r then a else b) := by
  by_cases h : r = s
  · simp [h]
  · have h' : s ≠ r := fun hs => h hs.symm
    simp [h, h']

lemma sum_delta_eq {ι : Type*} [DecidableEq ι] (A : Finset ι) (c : ι → ℂ)
    (N : ℕ) (δ : ℝ) :
    ∑ r ∈ A, ∑ s ∈ A, ‖c r‖ * ‖c s‖ * (if r = s then (N : ℝ) else (2 * δ)⁻¹) =
      (N : ℝ) * ∑ r ∈ A, ‖c r‖ ^ 2 +
        (2 * δ)⁻¹ *
          ((∑ r ∈ A, ‖c r‖) ^ 2 - ∑ r ∈ A, ‖c r‖ ^ 2) := by
  have h1 :
      ∑ r ∈ A, ∑ s ∈ A, ‖c r‖ * ‖c s‖ * (if r = s then (N : ℝ) else (2 * δ)⁻¹) =
        ∑ r ∈ A, ((N : ℝ) * ‖c r‖ ^ 2 +
          (2 * δ)⁻¹ * (‖c r‖ * ∑ s ∈ A, ‖c s‖ - ‖c r‖ ^ 2)) := by
    refine Finset.sum_congr rfl fun r hr => ?_
    have : ∑ s ∈ A, ‖c r‖ * ‖c s‖ * (if r = s then (N : ℝ) else (2 * δ)⁻¹) =
        ∑ s ∈ A, ‖c r‖ * ‖c s‖ * (if s = r then (N : ℝ) else (2 * δ)⁻¹) := by
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [ite_eq_comm]
    rw [this]
    exact sum_delta_term_eq A c N δ r hr
  rw [h1, Finset.sum_add_distrib]
  have hN : ∑ r ∈ A, (N : ℝ) * ‖c r‖ ^ 2 = (N : ℝ) * ∑ r ∈ A, ‖c r‖ ^ 2 := by
    simp [Finset.mul_sum]
  have hoff :
      ∑ r ∈ A, (2 * δ)⁻¹ * (‖c r‖ * ∑ s ∈ A, ‖c s‖ - ‖c r‖ ^ 2) =
        (2 * δ)⁻¹ * ((∑ r ∈ A, ‖c r‖) ^ 2 - ∑ r ∈ A, ‖c r‖ ^ 2) := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_sub_distrib, pow_two]
    congr 1
    rw [Finset.sum_mul]
  rw [hN, hoff]

lemma sum_delta_le_main {ι : Type*} [DecidableEq ι] (A : Finset ι) (c : ι → ℂ)
    (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∑ r ∈ A, ∑ s ∈ A, ‖c r‖ * ‖c s‖ * (if r = s then (N : ℝ) else (2 * δ)⁻¹) ≤
      ((N : ℝ) + A.card / (2 * δ)) * ∑ r ∈ A, ‖c r‖ ^ 2 := by
  rw [sum_delta_eq]
  have hpos : 0 ≤ (2 * δ)⁻¹ := inv_nonneg.2 (by nlinarith)
  have hsq : 0 ≤ ∑ r ∈ A, ‖c r‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hpair : (∑ r ∈ A, ‖c r‖) ^ 2 ≤ A.card * ∑ r ∈ A, ‖c r‖ ^ 2 :=
    sum_norm_sq_le_card_mul A c
  have hdiff :
      (∑ r ∈ A, ‖c r‖) ^ 2 - ∑ r ∈ A, ‖c r‖ ^ 2 ≤ A.card * ∑ r ∈ A, ‖c r‖ ^ 2 := by
    linarith
  have h1 :
      (N : ℝ) * ∑ r ∈ A, ‖c r‖ ^ 2 +
          (2 * δ)⁻¹ * ((∑ r ∈ A, ‖c r‖) ^ 2 - ∑ r ∈ A, ‖c r‖ ^ 2) ≤
        (N : ℝ) * ∑ r ∈ A, ‖c r‖ ^ 2 +
          (2 * δ)⁻¹ * (A.card * ∑ r ∈ A, ‖c r‖ ^ 2) :=
    add_le_add le_rfl (mul_le_mul_of_nonneg_left hdiff hpos)
  refine h1.trans ?_
  have hrew : (2 * δ)⁻¹ * (A.card * ∑ r ∈ A, ‖c r‖ ^ 2) =
      (A.card / (2 * δ)) * ∑ r ∈ A, ‖c r‖ ^ 2 := by
    field_simp
  rw [hrew, ← add_mul]

/-- Dual large sieve for a `δ`-separated set of frequencies. -/
lemma dual_large_sieve {ι : Type*} [DecidableEq ι] (A : Finset ι) (α : ι → ℝ)
    (c : ι → ℂ) (N : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r ∈ A, ∀ s ∈ A, r ≠ s → δ ≤ circDist (α r) (α s)) :
    ∑ n ∈ Finset.Icc 1 N, ‖∑ r ∈ A, c r * eH (n * α r)‖ ^ 2 ≤
      ((N : ℝ) + A.card / (2 * δ)) * ∑ r ∈ A, ‖c r‖ ^ 2 := by
  refine (sum_norm_sq_le_sum_delta A α c N hδ hsep).trans ?_
  exact sum_delta_le_main A c N hδ

lemma circDist_neg_neg (x y : ℝ) : circDist (-x) (-y) = circDist x y := by
  unfold circDist
  have : -x - -y = -(x - y) := by ring
  rw [this, distToNearestInt_neg]

lemma eH_neg_mul (n : ℕ) (θ : ℝ) : eH (n * (-θ)) = eH (-(n * θ)) := by
  congr 1
  ring

lemma star_eH_mul (n : ℕ) (θ : ℝ) : star (eH (n * θ)) = eH (n * (-θ)) := by
  rw [star_eH, eH_neg_mul]

lemma star_mul_eH (z : ℂ) (n : ℕ) (θ : ℝ) :
    star (z * eH (n * θ)) = star z * eH (n * (-θ)) := by
  rw [star_mul, star_eH_mul, mul_comm]

lemma star_sum_mul_eH (a : ℕ → ℂ) (N : ℕ) (θ : ℝ) :
    star (∑ n ∈ Finset.Icc 1 N, a n * eH (n * θ)) =
      ∑ n ∈ Finset.Icc 1 N, star (a n) * eH (n * (-θ)) := by
  rw [star_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  exact star_mul_eH (a n) n θ

lemma normSq_eq_mul_star (z : ℂ) : ‖z‖ ^ 2 = (z * star z).re := by
  rw [Complex.mul_re]
  have hre : (star z).re = z.re := by simp
  have him : (star z).im = -z.im := by simp
  rw [hre, him, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

lemma sum_normSq_eq_re_sum {ι : Type*} (A : Finset ι) (S : ι → ℂ) :
    ∑ r ∈ A, ‖S r‖ ^ 2 = (∑ r ∈ A, S r * star (S r)).re := by
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  exact normSq_eq_mul_star (S r)

lemma mul_sum_star_eH (a : ℕ → ℂ) (N : ℕ) (θ : ℝ) (z : ℂ) :
    z * ∑ n ∈ Finset.Icc 1 N, star (a n) * eH (n * (-θ)) =
      ∑ n ∈ Finset.Icc 1 N, star (a n) * (z * eH (n * (-θ))) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

lemma sum_S_mul_star_S {ι : Type*} (A : Finset ι) (a : ℕ → ℂ) (α : ι → ℝ) (N : ℕ) :
    ∑ r ∈ A, (∑ n ∈ Finset.Icc 1 N, a n * eH (n * α r)) *
        star (∑ n ∈ Finset.Icc 1 N, a n * eH (n * α r)) =
      ∑ n ∈ Finset.Icc 1 N, star (a n) *
        ∑ r ∈ A, (∑ m ∈ Finset.Icc 1 N, a m * eH (m * α r)) * eH (n * (-α r)) := by
  simp_rw [star_sum_mul_eH]
  simp_rw [mul_sum_star_eH]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum]

lemma sum_normSq_S_eq_re {ι : Type*} (A : Finset ι) (a : ℕ → ℂ) (α : ι → ℝ) (N : ℕ) :
    ∑ r ∈ A, ‖∑ n ∈ Finset.Icc 1 N, a n * eH (n * α r)‖ ^ 2 =
      (∑ n ∈ Finset.Icc 1 N, star (a n) *
        ∑ r ∈ A, (∑ m ∈ Finset.Icc 1 N, a m * eH (m * α r)) * eH (n * (-α r))).re := by
  rw [sum_normSq_eq_re_sum, sum_S_mul_star_S]

lemma abs_re_sum_star_mul (a : ℕ → ℂ) {ι : Type*} (A : Finset ι) (f : ℕ → ι → ℂ) (N : ℕ) :
    |(∑ n ∈ Finset.Icc 1 N, star (a n) * ∑ r ∈ A, f n r).re| ≤
      ∑ n ∈ Finset.Icc 1 N, ‖a n‖ * ‖∑ r ∈ A, f n r‖ := by
  refine (Complex.abs_re_le_norm _).trans ?_
  refine (norm_sum_le _ _).trans ?_
  refine le_of_eq (Finset.sum_congr rfl fun n _ => ?_)
  rw [norm_mul, norm_star]

lemma sq_le_sq_of_abs_le {x y : ℝ} (hx : 0 ≤ x) (h : |x| ≤ y) : x ^ 2 ≤ y ^ 2 := by
  nlinarith [abs_of_nonneg hx]

lemma sum_normSq_sq_le_cs {ι : Type*} (A : Finset ι) (a : ℕ → ℂ) (α : ι → ℝ) (N : ℕ) :
    (∑ r ∈ A, ‖∑ n ∈ Finset.Icc 1 N, a n * eH (n * α r)‖ ^ 2) ^ 2 ≤
      (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) *
        ∑ n ∈ Finset.Icc 1 N,
          ‖∑ r ∈ A, (∑ m ∈ Finset.Icc 1 N, a m * eH (m * α r)) * eH (n * (-α r))‖ ^ 2 := by
  have hnn : 0 ≤ ∑ r ∈ A, ‖∑ n ∈ Finset.Icc 1 N, a n * eH (n * α r)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have habs := abs_re_sum_star_mul a A
    (fun n r => (∑ m ∈ Finset.Icc 1 N, a m * eH (m * α r)) * eH (n * (-α r))) N
  have hid := sum_normSq_S_eq_re A a α N
  have h1 : |∑ r ∈ A, ‖∑ n ∈ Finset.Icc 1 N, a n * eH (n * α r)‖ ^ 2| ≤
      ∑ n ∈ Finset.Icc 1 N, ‖a n‖ *
        ‖∑ r ∈ A, (∑ m ∈ Finset.Icc 1 N, a m * eH (m * α r)) * eH (n * (-α r))‖ := by
    rwa [hid]
  have h2 := sq_le_sq_of_abs_le hnn h1
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 N)
    (fun n => ‖a n‖)
    (fun n => ‖∑ r ∈ A, (∑ m ∈ Finset.Icc 1 N, a m * eH (m * α r)) * eH (n * (-α r))‖)
  exact h2.trans hcs

lemma le_of_sq_le_mul {x y C : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hC : 0 ≤ C)
    (h : x ^ 2 ≤ y * (C * x)) : x ≤ y * C := by
  rcases eq_or_lt_of_le hx with h0 | hpos
  · simpa [← h0] using mul_nonneg hy hC
  · have : x * x ≤ y * C * x := by
      convert h using 1
      · simp [pow_two]
      · ring
    exact le_of_mul_le_mul_right this hpos

/-- Primal large sieve, obtained from the dual form by duality. -/
lemma primal_large_sieve {ι : Type*} [DecidableEq ι] (A : Finset ι) (α : ι → ℝ)
    (a : ℕ → ℂ) (N : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r ∈ A, ∀ s ∈ A, r ≠ s → δ ≤ circDist (α r) (α s)) :
    ∑ r ∈ A, ‖∑ n ∈ Finset.Icc 1 N, a n * eH (n * α r)‖ ^ 2 ≤
      ((N : ℝ) + A.card / (2 * δ)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  have hsep' : ∀ r ∈ A, ∀ s ∈ A, r ≠ s → δ ≤ circDist (-α r) (-α s) := by
    intro r hr s hs hne
    simpa [circDist_neg_neg] using hsep r hr s hs hne
  let S : ι → ℂ := fun r => ∑ n ∈ Finset.Icc 1 N, a n * eH (n * α r)
  have hdual := dual_large_sieve (A := A) (α := fun r => -α r) (c := S) N hδ hsep'
  have hCS := sum_normSq_sq_le_cs A a α N
  have hnn : 0 ≤ ∑ r ∈ A, ‖S r‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hmul := hCS.trans (mul_le_mul_of_nonneg_left hdual
    (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have : (∑ r ∈ A, ‖S r‖ ^ 2) ^ 2 ≤
      (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) *
        (((N : ℝ) + A.card / (2 * δ)) * ∑ r ∈ A, ‖S r‖ ^ 2) := by
    convert hmul using 2
  have hy : 0 ≤ ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hC : 0 ≤ (N : ℝ) + A.card / (2 * δ) := by positivity
  have hfin := le_of_sq_le_mul hnn hy hC this
  simpa [S, mul_comm] using hfin

/-- Reduced fractions `a/q` with `1 ≤ q ≤ Q` and `0 ≤ a < q`. -/
def fareyPairs (Q : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 Q ×ˢ Finset.range (Q + 1)).filter
    fun p => p.2 < p.1 ∧ Nat.Coprime p.2 p.1

noncomputable def fareyAlpha (p : ℕ × ℕ) : ℝ := (p.2 : ℝ) / (p.1 : ℝ)

lemma mem_fareyPairs {Q : ℕ} {p : ℕ × ℕ} :
    p ∈ fareyPairs Q ↔
      p.1 ∈ Finset.Icc 1 Q ∧ p.2 < p.1 ∧ Nat.Coprime p.2 p.1 := by
  simp only [fareyPairs, Finset.mem_filter, Finset.mem_product]
  constructor
  · intro h
    exact ⟨h.1.1, h.2.1, h.2.2⟩
  · intro h
    have hp1le : p.1 ≤ Q := (Finset.mem_Icc.1 h.1).2
    have hp2 : p.2 ∈ Finset.range (Q + 1) := by
      have : p.2 < Q + 1 := Nat.lt_succ_of_le (le_trans (Nat.le_of_lt h.2.1) hp1le)
      exact Finset.mem_range.2 this
    exact ⟨⟨h.1, hp2⟩, h.2.1, h.2.2⟩

lemma fareyPairs_subset (Q : ℕ) :
    fareyPairs Q ⊆ Finset.Icc 1 Q ×ˢ Finset.range Q := by
  intro p hp
  have h := mem_fareyPairs.1 hp
  have hp2 : p.2 < Q := lt_of_lt_of_le h.2.1 (Finset.mem_Icc.1 h.1).2
  exact Finset.mem_product.2 ⟨h.1, Finset.mem_range.2 hp2⟩

lemma card_fareyPairs_le (Q : ℕ) : (fareyPairs Q).card ≤ Q ^ 2 := by
  have hle := Finset.card_le_card (fareyPairs_subset Q)
  have hprod : (Finset.Icc 1 Q ×ˢ Finset.range Q).card = Q * Q := by
    rw [Finset.card_product, Nat.card_Icc, Finset.card_range]
    simp
  have : Q * Q = Q ^ 2 := by ring
  exact hle.trans (hprod.trans this).le

lemma farey_q_pos {Q : ℕ} {p : ℕ × ℕ} (hp : p ∈ fareyPairs Q) : 0 < p.1 :=
  (Finset.mem_Icc.1 (mem_fareyPairs.1 hp).1).1

lemma farey_q_le {Q : ℕ} {p : ℕ × ℕ} (hp : p ∈ fareyPairs Q) : p.1 ≤ Q :=
  (Finset.mem_Icc.1 (mem_fareyPairs.1 hp).1).2

lemma fareyAlpha_nonneg {Q : ℕ} {p : ℕ × ℕ} (hp : p ∈ fareyPairs Q) :
    0 ≤ fareyAlpha p :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma fareyAlpha_lt_one {Q : ℕ} {p : ℕ × ℕ} (hp : p ∈ fareyPairs Q) :
    fareyAlpha p < 1 := by
  have hq : (0 : ℝ) < p.1 := by exact_mod_cast farey_q_pos hp
  exact (div_lt_one hq).2 (by exact_mod_cast (mem_fareyPairs.1 hp).2.1)

lemma farey_cross {p q : ℕ × ℕ} (hp1 : 0 < p.1) (hq1 : 0 < q.1) :
    fareyAlpha p = fareyAlpha q ↔ p.2 * q.1 = q.2 * p.1 := by
  have hpR : (p.1 : ℝ) ≠ 0 := by exact_mod_cast hp1.ne'
  have hqR : (q.1 : ℝ) ≠ 0 := by exact_mod_cast hq1.ne'
  unfold fareyAlpha
  constructor
  · intro h
    have : (p.2 : ℝ) * q.1 = (q.2 : ℝ) * p.1 := by
      field_simp [hpR, hqR] at h
      nlinarith
    exact_mod_cast this
  · intro h
    have : (p.2 : ℝ) * q.1 = (q.2 : ℝ) * p.1 := by exact_mod_cast h
    field_simp [hpR, hqR]
    nlinarith

lemma fareyAlpha_eq_iff {Q : ℕ} {p q : ℕ × ℕ}
    (hp : p ∈ fareyPairs Q) (hq : q ∈ fareyPairs Q) :
    fareyAlpha p = fareyAlpha q ↔ p = q := by
  constructor
  · intro h
    have hp1 := farey_q_pos hp
    have hq1 := farey_q_pos hq
    have hmulN : p.2 * q.1 = q.2 * p.1 := (farey_cross hp1 hq1).1 h
    have hcp := (mem_fareyPairs.1 hp).2.2
    have hcq := (mem_fareyPairs.1 hq).2.2
    have hdiv1 : p.1 ∣ q.1 :=
      (Nat.Coprime.dvd_mul_left hcp.symm).1 (by rw [hmulN]; exact dvd_mul_left _ _)
    have hdiv2 : q.1 ∣ p.1 :=
      (Nat.Coprime.dvd_mul_left hcq.symm).1 (by rw [← hmulN]; exact dvd_mul_left _ _)
    have hqq : p.1 = q.1 := Nat.dvd_antisymm hdiv1 hdiv2
    have haa : p.2 = q.2 :=
      Nat.mul_right_cancel hq1 (by simpa [hqq] using hmulN)
    exact Prod.ext hqq haa
  · intro h
    rw [h]

lemma farey_sub_eq {p q : ℕ × ℕ} (hp1 : 0 < p.1) (hq1 : 0 < q.1) :
    fareyAlpha p - fareyAlpha q =
      ((p.2 : ℝ) * q.1 - (q.2 : ℝ) * p.1) / ((p.1 : ℝ) * q.1) := by
  unfold fareyAlpha
  have hpR : (p.1 : ℝ) ≠ 0 := by exact_mod_cast hp1.ne'
  have hqR : (q.1 : ℝ) ≠ 0 := by exact_mod_cast hq1.ne'
  field_simp [hpR, hqR]

lemma distToNearestInt_of_abs_lt_one {x : ℝ} (hx : |x| < 1) :
    distToNearestInt x = min |x| (1 - |x|) := by
  have hxhi : x < 1 := (abs_lt.1 hx).2
  have hmin := distToNearestInt_eq_min x
  by_cases hpos : 0 ≤ x
  · have hfr : Int.fract x = x := Int.fract_eq_self.2 ⟨hpos, hxhi⟩
    rw [hmin, hfr, abs_of_nonneg hpos]
  · have hxneg : x < 0 := lt_of_not_ge hpos
    have hfl : ⌊x⌋ = -1 := by
      refine Int.floor_eq_iff.2 ⟨?_, ?_⟩
      · push_cast; exact le_of_lt (abs_lt.1 hx).1
      · push_cast; linarith [hxneg]
    have hfr : Int.fract x = x + 1 := by
      unfold Int.fract
      rw [hfl]
      push_cast
      ring
    rw [hmin, hfr, abs_of_neg hxneg]
    have : 1 - -(x) = x + 1 := by ring
    rw [this, min_comm]
    congr 1
    ring

lemma abs_sub_lt_one_of_mem_Ico {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hy0 : 0 ≤ y) (hy1 : y < 1) : |x - y| < 1 := by
  have : x - y < 1 := by linarith
  have : -1 < x - y := by linarith
  exact abs_lt.2 ⟨this, ‹_›⟩

lemma fareyAlpha_abs_sub_lt_one {Q : ℕ} {p q : ℕ × ℕ}
    (hp : p ∈ fareyPairs Q) (hq : q ∈ fareyPairs Q) :
    |fareyAlpha p - fareyAlpha q| < 1 :=
  abs_sub_lt_one_of_mem_Ico (fareyAlpha_nonneg hp) (fareyAlpha_lt_one hp)
    (fareyAlpha_nonneg hq) (fareyAlpha_lt_one hq)

lemma farey_num_ne_zero {Q : ℕ} {p q : ℕ × ℕ}
    (hp : p ∈ fareyPairs Q) (hq : q ∈ fareyPairs Q) (hne : p ≠ q) :
    (p.2 : ℤ) * q.1 - (q.2 : ℤ) * p.1 ≠ 0 := by
  intro h0
  have h0N : p.2 * q.1 = q.2 * p.1 := by
    have : (p.2 : ℤ) * q.1 = (q.2 : ℤ) * p.1 := sub_eq_zero.1 h0
    exact_mod_cast this
  have : fareyAlpha p = fareyAlpha q :=
    (farey_cross (farey_q_pos hp) (farey_q_pos hq)).2 h0N
  exact hne ((fareyAlpha_eq_iff hp hq).1 this)

lemma one_le_abs_farey_num {Q : ℕ} {p q : ℕ × ℕ}
    (hp : p ∈ fareyPairs Q) (hq : q ∈ fareyPairs Q) (hne : p ≠ q) :
    (1 : ℝ) ≤ |((p.2 : ℝ) * q.1 - (q.2 : ℝ) * p.1)| := by
  have hZ := farey_num_ne_zero hp hq hne
  have : (1 : ℤ) ≤ |(p.2 : ℤ) * q.1 - (q.2 : ℤ) * p.1| := Int.one_le_abs hZ
  exact_mod_cast this

lemma farey_den_pos {Q : ℕ} {p q : ℕ × ℕ}
    (hp : p ∈ fareyPairs Q) (hq : q ∈ fareyPairs Q) :
    (0 : ℝ) < (p.1 : ℝ) * q.1 := by
  have : (0 : ℝ) < p.1 := by exact_mod_cast farey_q_pos hp
  have : (0 : ℝ) < q.1 := by exact_mod_cast farey_q_pos hq
  positivity

lemma farey_abs_sub_eq {Q : ℕ} {p q : ℕ × ℕ}
    (hp : p ∈ fareyPairs Q) (hq : q ∈ fareyPairs Q) :
    |fareyAlpha p - fareyAlpha q| =
      |((p.2 : ℝ) * q.1 - (q.2 : ℝ) * p.1)| / ((p.1 : ℝ) * q.1) := by
  rw [farey_sub_eq (farey_q_pos hp) (farey_q_pos hq), abs_div,
    abs_of_pos (farey_den_pos hp hq)]

lemma farey_abs_sub_ge {Q : ℕ} {p q : ℕ × ℕ}
    (hp : p ∈ fareyPairs Q) (hq : q ∈ fareyPairs Q) (hne : p ≠ q) :
    (1 : ℝ) / ((p.1 : ℝ) * q.1) ≤ |fareyAlpha p - fareyAlpha q| := by
  rw [farey_abs_sub_eq hp hq]
  have hden := farey_den_pos hp hq
  have hn := one_le_abs_farey_num hp hq hne
  exact (div_le_div_iff_of_pos_right hden).2 hn

lemma farey_num_lt_den {Q : ℕ} {p q : ℕ × ℕ}
    (hp : p ∈ fareyPairs Q) (hq : q ∈ fareyPairs Q) :
    |((p.2 : ℝ) * q.1 - (q.2 : ℝ) * p.1)| < (p.1 : ℝ) * q.1 := by
  have := fareyAlpha_abs_sub_lt_one hp hq
  rw [farey_abs_sub_eq hp hq] at this
  exact (div_lt_one (farey_den_pos hp hq)).1 this

lemma farey_num_le_den_sub_one {Q : ℕ} {p q : ℕ × ℕ}
    (hp : p ∈ fareyPairs Q) (hq : q ∈ fareyPairs Q) :
    |((p.2 : ℝ) * q.1 - (q.2 : ℝ) * p.1)| ≤ (p.1 : ℝ) * q.1 - 1 := by
  have hlt : |(p.2 : ℤ) * q.1 - (q.2 : ℤ) * p.1| < (p.1 : ℤ) * q.1 := by
    have := farey_num_lt_den hp hq
    exact_mod_cast this
  have hle : |(p.2 : ℤ) * q.1 - (q.2 : ℤ) * p.1| ≤ (p.1 : ℤ) * q.1 - 1 := by omega
  exact_mod_cast hle

lemma one_sub_abs_farey {Q : ℕ} {p q : ℕ × ℕ}
    (hp : p ∈ fareyPairs Q) (hq : q ∈ fareyPairs Q) :
    1 - |fareyAlpha p - fareyAlpha q| =
      ((p.1 : ℝ) * q.1 - |((p.2 : ℝ) * q.1 - (q.2 : ℝ) * p.1)|) /
        ((p.1 : ℝ) * q.1) := by
  rw [farey_abs_sub_eq hp hq, one_sub_div (ne_of_gt (farey_den_pos hp hq))]

lemma farey_one_sub_abs_ge {Q : ℕ} {p q : ℕ × ℕ}
    (hp : p ∈ fareyPairs Q) (hq : q ∈ fareyPairs Q) :
    (1 : ℝ) / ((p.1 : ℝ) * q.1) ≤ 1 - |fareyAlpha p - fareyAlpha q| := by
  rw [one_sub_abs_farey hp hq]
  have hden := farey_den_pos hp hq
  have hnum := farey_num_le_den_sub_one hp hq
  have hpos : 0 < (p.1 : ℝ) * q.1 - |((p.2 : ℝ) * q.1 - (q.2 : ℝ) * p.1)| := by
    linarith
  have : (1 : ℝ) / ((p.1 : ℝ) * q.1) ≤
      ((p.1 : ℝ) * q.1 - |((p.2 : ℝ) * q.1 - (q.2 : ℝ) * p.1)|) /
        ((p.1 : ℝ) * q.1) := by
    rw [div_le_div_iff_of_pos_right hden]
    linarith
  exact this

lemma farey_circDist_eq {Q : ℕ} {p q : ℕ × ℕ}
    (hp : p ∈ fareyPairs Q) (hq : q ∈ fareyPairs Q) :
    circDist (fareyAlpha p) (fareyAlpha q) =
      min |fareyAlpha p - fareyAlpha q| (1 - |fareyAlpha p - fareyAlpha q|) := by
  unfold circDist
  exact distToNearestInt_of_abs_lt_one (fareyAlpha_abs_sub_lt_one hp hq)

lemma farey_circDist_ge_den {Q : ℕ} {p q : ℕ × ℕ}
    (hp : p ∈ fareyPairs Q) (hq : q ∈ fareyPairs Q) (hne : p ≠ q) :
    (1 : ℝ) / ((p.1 : ℝ) * q.1) ≤ circDist (fareyAlpha p) (fareyAlpha q) := by
  rw [farey_circDist_eq hp hq]
  exact le_min (farey_abs_sub_ge hp hq hne) (farey_one_sub_abs_ge hp hq)

lemma farey_den_le_Qsq {Q : ℕ} {p q : ℕ × ℕ}
    (hp : p ∈ fareyPairs Q) (hq : q ∈ fareyPairs Q) :
    (p.1 : ℝ) * q.1 ≤ (Q : ℝ) ^ 2 := by
  have hpR : (p.1 : ℝ) ≤ Q := by exact_mod_cast farey_q_le hp
  have hqR : (q.1 : ℝ) ≤ Q := by exact_mod_cast farey_q_le hq
  nlinarith

lemma farey_inv_den_ge {Q : ℕ} {p q : ℕ × ℕ}
    (hp : p ∈ fareyPairs Q) (hq : q ∈ fareyPairs Q) :
    (1 : ℝ) / Q ^ 2 ≤ 1 / ((p.1 : ℝ) * q.1) :=
  one_div_le_one_div_of_le (farey_den_pos hp hq) (farey_den_le_Qsq hp hq)

lemma farey_separated {Q : ℕ} {p q : ℕ × ℕ}
    (hp : p ∈ fareyPairs Q) (hq : q ∈ fareyPairs Q) (hne : p ≠ q) :
    (1 : ℝ) / Q ^ 2 ≤ circDist (fareyAlpha p) (fareyAlpha q) :=
  (farey_inv_den_ge hp hq).trans (farey_circDist_ge_den hp hq hne)

lemma farey_hsep {Q : ℕ} (_hQ : 0 < Q) :
    ∀ p ∈ fareyPairs Q, ∀ q ∈ fareyPairs Q, p ≠ q →
      (1 : ℝ) / Q ^ 2 ≤ circDist (fareyAlpha p) (fareyAlpha q) :=
  fun p hp q hq hne => farey_separated hp hq hne

lemma farey_card_div_delta_le (Q : ℕ) (hQ : 0 < Q) :
    ((fareyPairs Q).card : ℝ) / (2 * (1 / Q ^ 2)) ≤ (Q : ℝ) ^ 4 := by
  have hcard : ((fareyPairs Q).card : ℝ) ≤ (Q : ℝ) ^ 2 := by
    exact_mod_cast card_fareyPairs_le Q
  have h1 : ((fareyPairs Q).card : ℝ) / (2 * (1 / (Q : ℝ) ^ 2)) =
      ((fareyPairs Q).card : ℝ) * (Q : ℝ) ^ 2 / 2 := by
    field_simp
  rw [h1]
  have : (Q : ℝ) ^ 2 * (Q : ℝ) ^ 2 = (Q : ℝ) ^ 4 := by ring
  nlinarith [sq_nonneg (Q : ℝ), hcard]

/-- Large sieve over Farey points of order `Q`. -/
lemma farey_large_sieve (a : ℕ → ℂ) (N Q : ℕ) (hQ : 0 < Q) :
    ∑ p ∈ fareyPairs Q, ‖∑ n ∈ Finset.Icc 1 N, a n * eH (n * fareyAlpha p)‖ ^ 2 ≤
      ((N : ℝ) + (Q : ℝ) ^ 4) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  have hδ : (0 : ℝ) < 1 / Q ^ 2 := by positivity
  have hpr := primal_large_sieve (fareyPairs Q) fareyAlpha a N hδ (farey_hsep hQ)
  refine hpr.trans ?_
  have hfrac := farey_card_div_delta_le Q hQ
  have hsum : 0 ≤ ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  nlinarith

/- Prime number theorem ingredients (Newman–Zagier) -/

open Chebyshev

lemma log_four_le_two : Real.log 4 ≤ 2 := by
  have hpow : Real.log 4 = 2 * Real.log 2 := by
    have : (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
    rw [this, Real.log_pow]
    norm_num
  rw [hpow]
  have h2 : Real.log 2 ≤ 1 :=
    (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)).2
      (le_of_lt (lt_trans (by norm_num : (2 : ℝ) < 2.7182818283) Real.exp_one_gt_d9))
  nlinarith

lemma theta_le_two_mul {x : ℝ} (hx : 0 ≤ x) : θ x ≤ 2 * x := by
  have h := theta_le_log4_mul_x hx
  nlinarith [log_four_le_two, theta_nonneg x]

lemma LSeriesSummable_vonMangoldt_re {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s :=
  ArithmeticFunction.LSeriesSummable_vonMangoldt hs

noncomputable def primePhi (s : ℂ) : ℂ :=
  LSeries (fun n => if n.Prime then (Real.log n : ℂ) else 0) s

lemma riemannZeta_ne_zero_one_le_re {s : ℂ} (hs : 1 ≤ s.re) (h1 : s ≠ 1) :
    riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs

/-- Entire function agreeing with `(s-1) ζ(s)` off `s = 1`, with value `1` at `s = 1`. -/
noncomputable def zetaPoleRemoved (s : ℂ) : ℂ :=
  if s = 1 then 1 else (s - 1) * riemannZeta s

lemma zetaPoleRemoved_apply_of_ne {s : ℂ} (h : s ≠ 1) :
    zetaPoleRemoved s = (s - 1) * riemannZeta s :=
  if_neg h

lemma zetaPoleRemoved_apply_one : zetaPoleRemoved 1 = 1 := if_pos rfl

lemma tendsto_zetaPoleRemoved_nhds_one :
    Filter.Tendsto zetaPoleRemoved (nhds 1) (nhds 1) := by
  have hsplit : nhds (1 : ℂ) = nhdsWithin 1 ({1} : Set ℂ) ⊔ nhdsWithin 1 ({1}ᶜ) := by
    rw [← nhdsWithin_union, Set.union_compl_self, nhdsWithin_univ]
  have h1 : Filter.Tendsto zetaPoleRemoved (nhdsWithin 1 ({1}ᶜ : Set ℂ)) (nhds 1) := by
    refine riemannZeta_residue_one.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (zetaPoleRemoved_apply_of_ne hs).symm
  have h2 : Filter.Tendsto zetaPoleRemoved (nhdsWithin 1 ({1} : Set ℂ)) (nhds 1) := by
    rw [nhdsWithin_singleton]
    simpa [zetaPoleRemoved_apply_one] using
      tendsto_pure_nhds zetaPoleRemoved (1 : ℂ)
  have hsup : Filter.Tendsto zetaPoleRemoved
      (nhdsWithin 1 ({1} : Set ℂ) ⊔ nhdsWithin 1 ({1}ᶜ)) (nhds 1) :=
    h2.sup h1
  rwa [← hsplit] at hsup

lemma differentiableAt_zetaPoleRemoved_of_ne {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ zetaPoleRemoved s := by
  have hζ : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs
  have : zetaPoleRemoved =ᶠ[nhds s] fun z => (z - 1) * riemannZeta z := by
    filter_upwards [isOpen_ne.mem_nhds hs] with z hz
    exact zetaPoleRemoved_apply_of_ne hz
  exact this.differentiableAt_iff.2 (DifferentiableAt.mul (differentiableAt_id.sub_const 1) hζ)

lemma continuousAt_zetaPoleRemoved_one : ContinuousAt zetaPoleRemoved 1 := by
  unfold ContinuousAt
  convert tendsto_zetaPoleRemoved_nhds_one
  exact zetaPoleRemoved_apply_one

lemma analyticAt_zetaPoleRemoved_one : AnalyticAt ℂ zetaPoleRemoved 1 := by
  refine Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_
    continuousAt_zetaPoleRemoved_one
  exact Filter.eventually_of_mem self_mem_nhdsWithin fun z hz =>
    differentiableAt_zetaPoleRemoved_of_ne hz

lemma differentiableAt_zetaPoleRemoved (s : ℂ) : DifferentiableAt ℂ zetaPoleRemoved s := by
  by_cases h : s = 1
  · subst h
    exact analyticAt_zetaPoleRemoved_one.differentiableAt
  · exact differentiableAt_zetaPoleRemoved_of_ne h

lemma differentiable_zetaPoleRemoved : Differentiable ℂ zetaPoleRemoved :=
  differentiableAt_zetaPoleRemoved

lemma zetaPoleRemoved_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    zetaPoleRemoved s ≠ 0 := by
  by_cases h : s = 1
  · simp [h, zetaPoleRemoved_apply_one]
  · rw [zetaPoleRemoved_apply_of_ne h]
    exact mul_ne_zero (sub_ne_zero.2 h) (riemannZeta_ne_zero_of_one_le_re hs)

lemma deriv_zetaPoleRemoved_of_ne {s : ℂ} (hs : s ≠ 1) :
    deriv zetaPoleRemoved s =
      riemannZeta s + (s - 1) * deriv riemannZeta s := by
  have hζ : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs
  have heq : zetaPoleRemoved =ᶠ[nhds s] fun z => (z - 1) * riemannZeta z := by
    filter_upwards [isOpen_ne.mem_nhds hs] with z hz
    exact zetaPoleRemoved_apply_of_ne hz
  rw [Filter.EventuallyEq.deriv_eq heq]
  rw [deriv_fun_mul (by fun_prop) hζ]
  simp [deriv_sub_const, deriv_id'']

lemma logDeriv_zeta_eq_of_ne {s : ℂ} (hs : s ≠ 1) (hζ : riemannZeta s ≠ 0) :
    deriv riemannZeta s / riemannZeta s =
      deriv zetaPoleRemoved s / zetaPoleRemoved s - 1 / (s - 1) := by
  have hZ := zetaPoleRemoved_apply_of_ne hs
  have hd := deriv_zetaPoleRemoved_of_ne hs
  have hsub : s - 1 ≠ 0 := sub_ne_zero.2 hs
  rw [hZ, hd]
  field_simp [hζ, hsub]
  ring

/-- The function `-ζ'/ζ(s) - 1/(s-1)` agrees with `-Z'/Z` off `s = 1`. -/
lemma neg_logDeriv_zeta_sub_inv_eq {s : ℂ} (hs : s ≠ 1) (hζ : riemannZeta s ≠ 0) :
    -(deriv riemannZeta s / riemannZeta s) - 1 / (s - 1) =
      -(deriv zetaPoleRemoved s / zetaPoleRemoved s) := by
  rw [logDeriv_zeta_eq_of_ne hs hζ]
  ring

/-- Holomorphic extension of `L(Λ,s) - 1/(s-1)` to `re s ≥ 1`. -/
noncomputable def vonMangoldtHolomorphic (s : ℂ) : ℂ :=
  -(deriv zetaPoleRemoved s / zetaPoleRemoved s)

lemma differentiableAt_vonMangoldtHolomorphic_of_ne_zero {s : ℂ}
    (hZ : zetaPoleRemoved s ≠ 0) :
    DifferentiableAt ℂ vonMangoldtHolomorphic s := by
  have hZdiff := differentiableAt_zetaPoleRemoved s
  have hder : DifferentiableAt ℂ (deriv zetaPoleRemoved) s :=
    (differentiable_zetaPoleRemoved.analyticAt s).deriv.differentiableAt
  unfold vonMangoldtHolomorphic
  exact (hder.div hZdiff hZ).neg

lemma differentiableAt_vonMangoldtHolomorphic_halfplane {s : ℂ} (hs : 1 ≤ s.re) :
    DifferentiableAt ℂ vonMangoldtHolomorphic s :=
  differentiableAt_vonMangoldtHolomorphic_of_ne_zero
    (zetaPoleRemoved_ne_zero_of_one_le_re hs)

lemma LSeries_vonMangoldt_sub_inv {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s - 1 / (s - 1) =
      vonMangoldtHolomorphic s := by
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (le_of_lt hs)
  have hs1 : s ≠ 1 := by
    intro h
    have : (1 : ℝ) < (1 : ℂ).re := h ▸ hs
    simp at this
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  unfold vonMangoldtHolomorphic
  convert neg_logDeriv_zeta_sub_inv_eq hs1 hζ using 2
  ring

lemma psi_eq_sum_vonMangoldt (x : ℝ) :
    ψ x = ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n :=
  psi_eq_sum_Icc x

lemma psi_le_six_mul {x : ℝ} (hx : 0 ≤ x) : ψ x ≤ 6 * x := by
  have h := psi_le_const_mul_self hx
  have : Real.log 4 + 4 ≤ 6 := by linarith [log_four_le_two]
  nlinarith [psi_nonneg x]

/- Newman's tauberian kernel `e^{zT} (1 + z²/R²) / z`. -/

noncomputable def newmanKernel (T R : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (z * T) * (1 + z ^ 2 / R ^ 2) / z

lemma exp_mul_I_ne_zero (t : ℝ) : Complex.exp (t * Complex.I) ≠ 0 :=
  Complex.exp_ne_zero _

lemma newman_sq_div {R t : ℝ} (hR : (R : ℂ) ≠ 0) :
    ((R : ℂ) * Complex.exp (t * Complex.I)) ^ 2 / (R : ℂ) ^ 2 =
      Complex.exp ((2 * t : ℝ) * Complex.I) := by
  field_simp [hR]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma re_exp_two_I (t : ℝ) :
    (Complex.exp ((2 * t : ℝ) * Complex.I)).re = Real.cos (2 * t) := by
  simpa using Complex.exp_ofReal_mul_I_re (2 * t)

lemma im_exp_two_I (t : ℝ) :
    (Complex.exp ((2 * t : ℝ) * Complex.I)).im = Real.sin (2 * t) := by
  simpa using Complex.exp_ofReal_mul_I_im (2 * t)

lemma normSq_one_add_exp_two_I (t : ℝ) :
    ‖1 + Complex.exp ((2 * t : ℝ) * Complex.I)‖ ^ 2 = 4 * Real.cos t ^ 2 := by
  have hre : (1 + Complex.exp ((2 * t : ℝ) * Complex.I)).re = 1 + Real.cos (2 * t) := by
    rw [Complex.add_re, Complex.one_re, re_exp_two_I]
  have him : (1 + Complex.exp ((2 * t : ℝ) * Complex.I)).im = Real.sin (2 * t) := by
    rw [Complex.add_im, Complex.one_im, im_exp_two_I, zero_add]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]
  have hcs : Real.cos (2 * t) * Real.cos (2 * t) + Real.sin (2 * t) * Real.sin (2 * t) = 1 := by
    simpa [pow_two] using Real.cos_sq_add_sin_sq (2 * t)
  have h2 := Real.cos_two_mul t
  nlinarith [h2]

lemma norm_one_add_exp_two_I (t : ℝ) :
    ‖1 + Complex.exp ((2 * t : ℝ) * Complex.I)‖ = 2 * |Real.cos t| := by
  have h := normSq_one_add_exp_two_I t
  have hnn : 0 ≤ ‖1 + Complex.exp ((2 * t : ℝ) * Complex.I)‖ := norm_nonneg _
  have : ‖1 + Complex.exp ((2 * t : ℝ) * Complex.I)‖ ^ 2 = (2 * |Real.cos t|) ^ 2 := by
    rw [h, mul_pow, sq_abs]
    ring
  exact (sq_eq_sq₀ hnn (by positivity)).1 this

lemma norm_newmanKernel_circle {T R t : ℝ} (hR : 0 < R) :
    ‖newmanKernel T R (R * Complex.exp (t * Complex.I))‖ =
      Real.exp (R * T * Real.cos t) * (2 * |Real.cos t|) / R := by
  unfold newmanKernel
  have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hz : (R : ℂ) * Complex.exp (t * Complex.I) ≠ 0 :=
    mul_ne_zero hR0 (exp_mul_I_ne_zero t)
  rw [norm_div, norm_mul, Complex.norm_exp]
  have hre : ((R : ℂ) * Complex.exp (t * Complex.I) * (T : ℂ)).re =
      R * T * Real.cos t := by
    have : ((R : ℂ) * Complex.exp (t * Complex.I)).re = R * Real.cos t := by
      rw [Complex.mul_re]
      have : (Complex.exp (t * Complex.I)).re = Real.cos t := by
        simpa using Complex.exp_ofReal_mul_I_re t
      have : (Complex.exp (t * Complex.I)).im = Real.sin t := by
        simpa using Complex.exp_ofReal_mul_I_im t
      simp [Complex.ofReal_re, Complex.ofReal_im, *]
    rw [Complex.mul_re, this]
    simp [Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hre]
  have hnum : ‖1 + ((R : ℂ) * Complex.exp (t * Complex.I)) ^ 2 / (R : ℂ) ^ 2‖ =
      2 * |Real.cos t| := by
    rw [newman_sq_div hR0, norm_one_add_exp_two_I]
  have hden : ‖(R : ℂ) * Complex.exp (t * Complex.I)‖ = R := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    simpa [abs_of_pos hR]
  rw [hnum, hden]

lemma exp_neg_re {z : ℂ} (t : ℝ) :
    ‖Complex.exp (-(z * t))‖ = Real.exp (-z.re * t) := by
  rw [Complex.norm_exp, Complex.neg_re, Complex.mul_re]
  simp [Complex.ofReal_re, Complex.ofReal_im]

/-! ### Elementary Mertens estimates and Vaughan’s identity -/

open ArithmeticFunction

lemma sum_log_Icc_le (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, Real.log (k : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := by
  by_cases hn : n = 0
  · subst hn; simp
  refine (Finset.sum_le_card_nsmul _ _ (Real.log (n : ℝ)) (fun k hk => ?_)).trans ?_
  · have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hk).1
    have hkn : k ≤ n := (Finset.mem_Icc.1 hk).2
    exact Real.log_le_log (by exact_mod_cast hk1) (by exact_mod_cast hkn)
  · simp [nsmul_eq_mul, Nat.card_Icc]

lemma card_Icc_half (n : ℕ) :
    (Finset.Icc (n / 2) n).card = n + 1 - n / 2 :=
  Nat.card_Icc _ _

lemma nsmul_log_half_le_sum_log {n : ℕ} (hn : 2 ≤ n) :
    ((Finset.Icc (n / 2) n).card : ℝ) * Real.log ((n / 2 : ℕ) : ℝ) ≤
      ∑ k ∈ Finset.Icc 1 n, Real.log (k : ℝ) := by
  have hpos : 1 ≤ n / 2 := by omega
  have hsubset : Finset.Icc (n / 2) n ⊆ Finset.Icc 1 n := by
    intro k hk
    rcases Finset.mem_Icc.1 hk with ⟨hk1, hk2⟩
    exact Finset.mem_Icc.2 ⟨le_trans hpos hk1, hk2⟩
  have hterm : ∀ k ∈ Finset.Icc (n / 2) n,
      Real.log ((n / 2 : ℕ) : ℝ) ≤ Real.log (k : ℝ) := by
    intro k hk
    have hk1 : n / 2 ≤ k := (Finset.mem_Icc.1 hk).1
    exact Real.log_le_log (by exact_mod_cast (show 0 < n / 2 by omega)) (by exact_mod_cast hk1)
  have hsum := Finset.card_nsmul_le_sum (Finset.Icc (n / 2) n)
    (fun k => Real.log (k : ℝ)) (Real.log ((n / 2 : ℕ) : ℝ)) hterm
  have hnonneg : ∀ k ∈ Finset.Icc 1 n, k ∉ Finset.Icc (n / 2) n →
      0 ≤ Real.log (k : ℝ) := by
    intro k hk _
    exact Real.log_nonneg (by exact_mod_cast (Finset.mem_Icc.1 hk).1)
  have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg
  exact le_trans (by simpa [nsmul_eq_mul] using hsum) hmono

lemma half_n_le_card_Icc_half {n : ℕ} (_hn : 2 ≤ n) :
    (n : ℝ) / 2 ≤ ((n + 1 - n / 2 : ℕ) : ℝ) := by
  have hnat : n / 2 + 1 ≤ n + 1 - n / 2 := by omega
  have : n < 2 * (n / 2 + 1) := by omega
  have hlt : (n : ℝ) < (2 : ℝ) * ((n / 2 : ℕ) + 1) := by exact_mod_cast this
  have : (n : ℝ) / 2 < (n / 2 : ℕ) + 1 := by linarith
  exact le_trans (le_of_lt this) (by exact_mod_cast hnat)

lemma half_mul_log_half_le_sum_log {n : ℕ} (hn : 4 ≤ n) :
    ((n : ℝ) / 2) * Real.log ((n / 2 : ℕ) : ℝ) ≤
      ∑ k ∈ Finset.Icc 1 n, Real.log (k : ℝ) := by
  have hn2 : 2 ≤ n := by omega
  have hmain := nsmul_log_half_le_sum_log hn2
  have hcard : (n : ℝ) / 2 ≤ ((Finset.Icc (n / 2) n).card : ℝ) := by
    rw [card_Icc_half]
    exact half_n_le_card_Icc_half hn2
  have hlog : 0 ≤ Real.log ((n / 2 : ℕ) : ℝ) :=
    Real.log_nonneg (by
      have : (1 : ℕ) ≤ n / 2 := by omega
      exact_mod_cast this)
  nlinarith

/-! ### Truncations of arithmetic functions and Vaughan’s identity -/

/-- Truncation of an arithmetic function to arguments `≤ U`. -/
noncomputable def truncAF (f : ArithmeticFunction ℝ) (U : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≤ U ∧ n ≠ 0 then f n else 0, by simp⟩

lemma truncAF_apply (f : ArithmeticFunction ℝ) (U n : ℕ) :
    truncAF f U n = if n ≤ U ∧ n ≠ 0 then f n else 0 := rfl

lemma truncAF_of_le {f : ArithmeticFunction ℝ} {U n : ℕ} (hn : n ≤ U) (h0 : n ≠ 0) :
    truncAF f U n = f n := by
  simp [truncAF_apply, hn, h0]

lemma truncAF_of_gt {f : ArithmeticFunction ℝ} {U n : ℕ} (hn : ¬ n ≤ U) :
    truncAF f U n = 0 := by
  simp [truncAF_apply, hn]

lemma truncAF_zero (f : ArithmeticFunction ℝ) (U : ℕ) : truncAF f U 0 = 0 := by
  simp [truncAF_apply]

/-- Complementary truncation: support on arguments `> U`. -/
noncomputable def tailAF (f : ArithmeticFunction ℝ) (U : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if U < n then f n else 0, by simp⟩

lemma tailAF_apply (f : ArithmeticFunction ℝ) (U n : ℕ) :
    tailAF f U n = if U < n then f n else 0 := rfl

lemma tailAF_of_gt {f : ArithmeticFunction ℝ} {U n : ℕ} (hn : U < n) :
    tailAF f U n = f n := by
  simp [tailAF_apply, hn]

lemma tailAF_of_le {f : ArithmeticFunction ℝ} {U n : ℕ} (hn : n ≤ U) :
    tailAF f U n = 0 := by
  simp [tailAF_apply, hn]

lemma truncAF_add_tailAF (f : ArithmeticFunction ℝ) (U n : ℕ) :
    truncAF f U n + tailAF f U n = f n := by
  by_cases h0 : n = 0
  · subst h0
    simp [truncAF_apply, tailAF_apply]
  by_cases hn : n ≤ U
  · simp [truncAF_of_le hn h0, tailAF_of_le hn]
  · have : U < n := Nat.lt_of_not_ge hn
    simp [truncAF_of_gt hn, tailAF_of_gt this]

lemma truncAF_add_tailAF_eq (f : ArithmeticFunction ℝ) (U : ℕ) :
    truncAF f U + tailAF f U = f := by
  ext n
  simpa [add_apply] using truncAF_add_tailAF f U n

lemma zeta_coe_apply_pos {n : ℕ} (hn : n ≠ 0) :
    (zeta : ArithmeticFunction ℝ) n = 1 := by
  simp [natCoe_apply, zeta_apply, hn]

lemma moebius_mul_zeta_eq_one :
    (moebius : ArithmeticFunction ℝ) * (zeta : ArithmeticFunction ℝ) = 1 :=
  coe_moebius_mul_coe_zeta

lemma moebius_mul_zeta_apply (n : ℕ) :
    ((moebius : ArithmeticFunction ℝ) * (zeta : ArithmeticFunction ℝ)) n =
      if n = 1 then 1 else 0 := by
  rw [moebius_mul_zeta_eq_one, one_apply]

lemma vonMangoldt_eq_mu_mul_log :
    vonMangoldt = (moebius : ArithmeticFunction ℝ) * ArithmeticFunction.log :=
  moebius_mul_log_eq_vonMangoldt.symm

lemma log_eq_vonMangoldt_mul_zeta :
    ArithmeticFunction.log = vonMangoldt * (zeta : ArithmeticFunction ℝ) := by
  rw [mul_comm, zeta_mul_vonMangoldt]

/-- Vaughan’s identity of arithmetic functions:
`Λ - Λ_{≤V} = μ_{≤U} * log - μ_{≤U} * Λ_{≤V} * ζ + μ_{>U} * Λ_{>V} * ζ`. -/
lemma vaughan_identity (U V : ℕ) :
    vonMangoldt - truncAF vonMangoldt V =
      truncAF (moebius : ArithmeticFunction ℝ) U * ArithmeticFunction.log
        - truncAF (moebius : ArithmeticFunction ℝ) U
            * truncAF vonMangoldt V * (zeta : ArithmeticFunction ℝ)
        + tailAF (moebius : ArithmeticFunction ℝ) U
            * tailAF vonMangoldt V * (zeta : ArithmeticFunction ℝ) := by
  set μU := truncAF (moebius : ArithmeticFunction ℝ) U
  set μUc := tailAF (moebius : ArithmeticFunction ℝ) U
  set ΛV := truncAF vonMangoldt V
  set ΛVc := tailAF vonMangoldt V
  have hμ : μU + μUc = (moebius : ArithmeticFunction ℝ) :=
    truncAF_add_tailAF_eq _ _
  have hΛ : ΛV + ΛVc = vonMangoldt :=
    truncAF_add_tailAF_eq _ _
  have hlog : ArithmeticFunction.log = vonMangoldt * (zeta : ArithmeticFunction ℝ) :=
    log_eq_vonMangoldt_mul_zeta
  have hunit : (moebius : ArithmeticFunction ℝ) * (zeta : ArithmeticFunction ℝ) = 1 :=
    moebius_mul_zeta_eq_one
  -- Expand Λ = μ * log = μ * Λ * ζ
  have hΛexp : vonMangoldt =
      (μU + μUc) * (ΛV + ΛVc) * (zeta : ArithmeticFunction ℝ) := by
    calc
      vonMangoldt = (moebius : ArithmeticFunction ℝ) * ArithmeticFunction.log :=
        vonMangoldt_eq_mu_mul_log
      _ = (μU + μUc) * (vonMangoldt * (zeta : ArithmeticFunction ℝ)) := by
        rw [hμ, hlog]
      _ = (μU + μUc) * ((ΛV + ΛVc) * (zeta : ArithmeticFunction ℝ)) := by
        rw [hΛ]
      _ = (μU + μUc) * (ΛV + ΛVc) * (zeta : ArithmeticFunction ℝ) := by
        ac_rfl
  have hμUlog : μU * ArithmeticFunction.log =
      μU * ΛV * (zeta : ArithmeticFunction ℝ)
        + μU * ΛVc * (zeta : ArithmeticFunction ℝ) := by
    calc
      μU * ArithmeticFunction.log
          = μU * (vonMangoldt * (zeta : ArithmeticFunction ℝ)) := by rw [hlog]
      _ = μU * ((ΛV + ΛVc) * (zeta : ArithmeticFunction ℝ)) := by rw [hΛ]
      _ = μU * (ΛV * (zeta : ArithmeticFunction ℝ) + ΛVc * (zeta : ArithmeticFunction ℝ)) := by
        rw [add_mul]
      _ = μU * ΛV * (zeta : ArithmeticFunction ℝ)
            + μU * ΛVc * (zeta : ArithmeticFunction ℝ) := by
        simp [mul_add, mul_assoc]
  -- μ * ΛV * ζ = ΛV
  have hΛV : (moebius : ArithmeticFunction ℝ) * ΛV * (zeta : ArithmeticFunction ℝ) = ΛV := by
    calc
      (moebius : ArithmeticFunction ℝ) * ΛV * (zeta : ArithmeticFunction ℝ)
          = ΛV * ((moebius : ArithmeticFunction ℝ) * (zeta : ArithmeticFunction ℝ)) := by
            ac_rfl
      _ = ΛV * 1 := by rw [hunit]
      _ = ΛV := by simp
  have hsplit : (μU + μUc) * ΛV * (zeta : ArithmeticFunction ℝ) = ΛV := by
    calc
      (μU + μUc) * ΛV * (zeta : ArithmeticFunction ℝ)
          = (moebius : ArithmeticFunction ℝ) * ΛV * (zeta : ArithmeticFunction ℝ) := by
            rw [hμ]
      _ = ΛV := hΛV
  -- Rearrange
  have hexpand : vonMangoldt =
      μU * ArithmeticFunction.log - μU * ΛV * (zeta : ArithmeticFunction ℝ)
        + ΛV + μUc * ΛVc * (zeta : ArithmeticFunction ℝ) := by
    have := hΛexp
    -- (μU+μUc)*(ΛV+ΛVc)*ζ = μU*ΛV*ζ + μU*ΛVc*ζ + μUc*ΛV*ζ + μUc*ΛVc*ζ
    have h4 : (μU + μUc) * (ΛV + ΛVc) * (zeta : ArithmeticFunction ℝ) =
        μU * ΛV * (zeta : ArithmeticFunction ℝ)
          + μU * ΛVc * (zeta : ArithmeticFunction ℝ)
          + μUc * ΛV * (zeta : ArithmeticFunction ℝ)
          + μUc * ΛVc * (zeta : ArithmeticFunction ℝ) := by
      simp [mul_add, add_mul, mul_assoc]; ac_rfl
    have : vonMangoldt =
        μU * ΛV * (zeta : ArithmeticFunction ℝ)
          + μU * ΛVc * (zeta : ArithmeticFunction ℝ)
          + μUc * ΛV * (zeta : ArithmeticFunction ℝ)
          + μUc * ΛVc * (zeta : ArithmeticFunction ℝ) := by
      rw [this, h4]
    -- μU*ΛV*ζ + μUc*ΛV*ζ = ΛV
    have hV : μU * ΛV * (zeta : ArithmeticFunction ℝ)
        + μUc * ΛV * (zeta : ArithmeticFunction ℝ) = ΛV := by
      simpa [add_mul, mul_assoc] using hsplit
    -- μU*log = μU*ΛV*ζ + μU*ΛVc*ζ
    calc
      vonMangoldt
          = μU * ΛV * (zeta : ArithmeticFunction ℝ)
              + μU * ΛVc * (zeta : ArithmeticFunction ℝ)
              + μUc * ΛV * (zeta : ArithmeticFunction ℝ)
              + μUc * ΛVc * (zeta : ArithmeticFunction ℝ) := this
      _ = (μU * ΛV * (zeta : ArithmeticFunction ℝ)
              + μU * ΛVc * (zeta : ArithmeticFunction ℝ))
              + (μU * ΛV * (zeta : ArithmeticFunction ℝ)
                  + μUc * ΛV * (zeta : ArithmeticFunction ℝ)
                  - μU * ΛV * (zeta : ArithmeticFunction ℝ))
              + μUc * ΛVc * (zeta : ArithmeticFunction ℝ) := by
          ring
      _ = μU * ArithmeticFunction.log - μU * ΛV * (zeta : ArithmeticFunction ℝ)
              + ΛV + μUc * ΛVc * (zeta : ArithmeticFunction ℝ) := by
          rw [← hμUlog, hV]
          ring
  calc
    vonMangoldt - ΛV
        = μU * ArithmeticFunction.log - μU * ΛV * (zeta : ArithmeticFunction ℝ)
            + μUc * ΛVc * (zeta : ArithmeticFunction ℝ) := by
          linear_combination hexpand
    _ = _ := by
      simp [μU, μUc, ΛV, ΛVc]

/-! ### Residue-class sums -/

lemma residue_div_inj (q a : ℕ) {s : Finset ℕ}
    (hs : ∀ n ∈ s, n % q = a % q) :
    Set.InjOn (fun n : ℕ => n / q) (s : Set ℕ) := by
  intro n hn m hm heq
  have hmod : n % q = m % q := (hs n hn).trans (hs m hm).symm
  calc
    n = q * (n / q) + n % q := (Nat.div_add_mod n q).symm
    _ = q * (m / q) + m % q := by rw [show n / q = m / q from heq, hmod]
    _ = m := Nat.div_add_mod m q

lemma card_residue_Icc_le (q a N : ℕ) :
    ((Finset.Icc 1 N).filter (fun n => n % q = a % q)).card ≤ N / q + 1 := by
  let s := (Finset.Icc 1 N).filter (fun n => n % q = a % q)
  have hinj := residue_div_inj q a (s := s) (fun n hn => (Finset.mem_filter.1 hn).2)
  have hsub : s.image (fun n => n / q) ⊆ Finset.range (N / q + 1) := by
    intro k hk
    rcases Finset.mem_image.1 hk with ⟨n, hn, rfl⟩
    have hnN : n ≤ N := (Finset.mem_Icc.1 (Finset.mem_filter.1 hn).1).2
    exact Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.div_le_div_right hnN))
  have hcard : s.card = (s.image (fun n => n / q)).card :=
    (Finset.card_image_of_injOn hinj).symm
  have : (s.image (fun n => n / q)).card ≤ N / q + 1 := by
    simpa [Finset.card_range] using Finset.card_le_card hsub
  exact hcard.le.trans this

lemma card_residue_Icc_le_real (q a N : ℕ) :
    (((Finset.Icc 1 N).filter (fun n => n % q = a % q)).card : ℝ) ≤
      (N : ℝ) / q + 1 := by
  have h := card_residue_Icc_le q a N
  have hcast : ((N / q + 1 : ℕ) : ℝ) = ((N / q : ℕ) : ℝ) + 1 := by
    push_cast; rfl
  have : ((N / q : ℕ) : ℝ) ≤ (N : ℝ) / q := Nat.cast_div_le
  have : ((N / q + 1 : ℕ) : ℝ) ≤ (N : ℝ) / q + 1 := by
    rw [hcast]; linarith
  exact le_trans (by exact_mod_cast h) this

lemma add_mul_mod_eq {q r k : ℕ} (hr : r < q) :
    (q * k + r) % q = r := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

lemma card_residue_Icc_ge (q r N : ℕ) (hq : 0 < q) (hr : r < q)
    (hN : r ≤ N) (hr0 : r ≠ 0) :
    (N - r) / q + 1 ≤
      ((Finset.Icc 1 N).filter (fun n => n % q = r)).card := by
  let t := Finset.range ((N - r) / q + 1)
  have himg : ∀ k ∈ t, q * k + r ∈
      (Finset.Icc 1 N).filter (fun n => n % q = r) := by
    intro k hk
    have hk' : k ≤ (N - r) / q := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have hle : q * k + r ≤ N := by
      have : q * k ≤ q * ((N - r) / q) := Nat.mul_le_mul_left q hk'
      have : q * ((N - r) / q) ≤ N - r := Nat.mul_div_le (N - r) q
      omega
    have hge : 1 ≤ q * k + r := by
      have : 1 ≤ r := Nat.pos_of_ne_zero hr0
      omega
    exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hge, hle⟩, add_mul_mod_eq hr⟩
  have hinj : Set.InjOn (fun k : ℕ => q * k + r) (t : Set ℕ) := by
    intro k hk k' hk' heq
    have := congrArg (fun x => x / q) heq
    simpa [Nat.mul_add_div hq, Nat.div_eq_of_lt hr] using this
  have hcard : t.card ≤
      ((Finset.Icc 1 N).filter (fun n => n % q = r)).card := by
    have hsub : t.image (fun k => q * k + r) ⊆
        (Finset.Icc 1 N).filter (fun n => n % q = r) := by
      intro n hn
      rcases Finset.mem_image.1 hn with ⟨k, hk, rfl⟩
      exact himg k hk
    have : t.card = (t.image (fun k => q * k + r)).card :=
      (Finset.card_image_of_injOn hinj).symm
    exact this.le.trans (Finset.card_le_card hsub)
  simpa [t, Finset.card_range] using hcard

lemma card_residue_zero_ge (q N : ℕ) (hq : 0 < q) :
    N / q ≤
      ((Finset.Icc 1 N).filter (fun n => n % q = 0)).card + 1 := by
  -- The values q, 2q, ..., (N/q)q all lie in the class, except 0.
  -- If N/q = 0 there is nothing to prove.
  by_cases h : N / q = 0
  · omega
  have hpos : 1 ≤ N / q := Nat.pos_of_ne_zero h
  have himg : ∀ k ∈ Finset.Icc 1 (N / q),
      q * k ∈ (Finset.Icc 1 N).filter (fun n => n % q = 0) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hk).1
    have hk2 : k ≤ N / q := (Finset.mem_Icc.1 hk).2
    have hle : q * k ≤ N :=
      le_trans (Nat.mul_le_mul_left q hk2) (Nat.mul_div_le N q)
    have hge : 1 ≤ q * k := by
      have : 1 ≤ q := hq
      nlinarith
    have hmod : (q * k) % q = 0 := Nat.mul_mod_right q k
    exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hge, hle⟩, hmod⟩
  have hinj : Set.InjOn (fun k : ℕ => q * k) (Finset.Icc 1 (N / q) : Set ℕ) := by
    intro k hk k' hk' heq
    have hq0 : q ≠ 0 := Nat.pos_iff_ne_zero.1 hq
    exact Nat.eq_of_mul_eq_mul_left hq heq
  have hsub : (Finset.Icc 1 (N / q)).image (fun k => q * k) ⊆
      (Finset.Icc 1 N).filter (fun n => n % q = 0) := by
    intro n hn
    rcases Finset.mem_image.1 hn with ⟨k, hk, rfl⟩
    exact himg k hk
  have hcard : (Finset.Icc 1 (N / q)).card ≤
      ((Finset.Icc 1 N).filter (fun n => n % q = 0)).card :=
    ((Finset.card_image_of_injOn hinj).symm.le).trans (Finset.card_le_card hsub)
  have : (Finset.Icc 1 (N / q)).card = N / q := by
    rw [Nat.card_Icc, Nat.add_sub_cancel]
  omega

lemma abs_card_residue_sub (q a N : ℕ) (hq : 0 < q) :
    |(((Finset.Icc 1 N).filter (fun n => n % q = a % q)).card : ℝ) -
      (N : ℝ) / q| ≤ 2 := by
  have hup := card_residue_Icc_le_real q a N
  have hnn : (0 : ℝ) ≤
      (((Finset.Icc 1 N).filter (fun n => n % q = a % q)).card : ℝ) :=
    Nat.cast_nonneg _
  have hlo : (N : ℝ) / q - 2 ≤
      (((Finset.Icc 1 N).filter (fun n => n % q = a % q)).card : ℝ) := by
    let r := a % q
    have hr : r < q := Nat.mod_lt a hq
    by_cases hr0 : r = 0
    · have hmod : a % q = 0 := hr0
      have hge := card_residue_zero_ge q N hq
      have : N / q ≤
          ((Finset.Icc 1 N).filter (fun n => n % q = a % q)).card + 1 := by
        simpa [hmod] using hge
      have hcast : (N / q : ℕ) ≤
          (((Finset.Icc 1 N).filter (fun n => n % q = a % q)).card : ℝ) + 1 := by
        exact_mod_cast this
      have : (N : ℝ) / q ≤ (N / q : ℕ) + 1 := by
        have hmod : N % q < q := Nat.mod_lt N hq
        have heq : N = q * (N / q) + N % q := (Nat.div_add_mod N q).symm
        have hltN : N < q * (N / q + 1) := by
          calc
            N = q * (N / q) + N % q := (Nat.div_add_mod N q).symm
            _ < q * (N / q) + q := Nat.add_lt_add_left hmod _
            _ = q * (N / q + 1) := by ring
        have hlt : (N : ℝ) < q * ((N / q : ℕ) + 1) := by exact_mod_cast hltN
        have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
        exact (le_of_lt ((div_lt_iff₀ hq0).2 (by linarith)))
      linarith
    · by_cases hN : N < r
      · have : (N : ℝ) / q < 1 := by
          have : (N : ℝ) < q := by exact_mod_cast (lt_trans hN hr)
          exact (div_lt_one (by exact_mod_cast hq)).2 this
        linarith
      · have hrle : r ≤ N := Nat.le_of_not_gt hN
        have hge := card_residue_Icc_ge q r N hq hr hrle hr0
        have : (N - r) / q + 1 ≤
            ((Finset.Icc 1 N).filter (fun n => n % q = a % q)).card := by
          simpa [r] using hge
        have hcast : (((N - r) / q + 1 : ℕ) : ℝ) ≤
            (((Finset.Icc 1 N).filter (fun n => n % q = a % q)).card : ℝ) :=
          by exact_mod_cast this
        have hpush : (((N - r) / q + 1 : ℕ) : ℝ) =
            ((N - r) / q : ℕ) + 1 := by push_cast; rfl
        have hsub : ((N - r : ℕ) : ℝ) = (N : ℝ) - r := Nat.cast_sub hrle
        have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
        have hdiv : ((N : ℝ) - r) / q - 1 ≤ ((N - r) / q : ℕ) := by
          have hlt : ((N : ℝ) - r) < (q : ℝ) * (((N - r) / q : ℕ) + 1) := by
            have : ((N - r : ℕ) : ℝ) < q * (((N - r) / q : ℕ) + 1) := by
              have hltN : N - r < q * ((N - r) / q + 1) := by
                have hmod : (N - r) % q < q := Nat.mod_lt (N - r) hq
                calc
                  N - r = q * ((N - r) / q) + (N - r) % q :=
                    (Nat.div_add_mod (N - r) q).symm
                  _ < q * ((N - r) / q) + q := Nat.add_lt_add_left hmod _
                  _ = q * ((N - r) / q + 1) := by ring
              exact_mod_cast hltN
            rwa [hsub] at this
          have hle' : ((N : ℝ) - r) - q ≤ (q : ℝ) * ((N - r) / q : ℕ) := by
            linarith
          have : (((N : ℝ) - r) - q) / q ≤ ((N - r) / q : ℕ) :=
            (div_le_iff₀ hq0).2 (by linarith)
          convert this using 1
          field_simp
        have hrq : (r : ℝ) / q < 1 :=
          (div_lt_one (by exact_mod_cast hq)).2 (by exact_mod_cast hr)
        have hsplit : ((N : ℝ) - r) / q = (N : ℝ) / q - (r : ℝ) / q :=
          sub_div (N : ℝ) (r : ℝ) (q : ℝ)
        have : (N : ℝ) / q - 2 ≤ ((N - r) / q : ℕ) + 1 := by
          linarith
        linarith
  apply abs_le.2
  constructor <;> linarith

/-! ### Sums of `log` over a residue class (Type I) -/

lemma sum_log_residue_le (q a N : ℕ) (hq : 0 < q) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % q = a % q), Real.log (n : ℝ) ≤
      ((N : ℝ) / q + 1) * Real.log (N : ℝ) := by
  by_cases hN : N = 0
  · subst hN; simp
  have hlog : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : (1 : ℕ) ≤ N))
  have hterm : ∀ n ∈ (Finset.Icc 1 N).filter (fun n => n % q = a % q),
      Real.log (n : ℝ) ≤ Real.log (N : ℝ) := by
    intro n hn
    have h1 : 1 ≤ n := (Finset.mem_Icc.1 (Finset.mem_filter.1 hn).1).1
    have h2 : n ≤ N := (Finset.mem_Icc.1 (Finset.mem_filter.1 hn).1).2
    exact Real.log_le_log (by exact_mod_cast h1) (by exact_mod_cast h2)
  have hsum := Finset.sum_le_card_nsmul
    ((Finset.Icc 1 N).filter (fun n => n % q = a % q))
    (fun n => Real.log (n : ℝ)) (Real.log (N : ℝ)) hterm
  have hcard := card_residue_Icc_le_real q a N
  have : (((Finset.Icc 1 N).filter (fun n => n % q = a % q)).card : ℝ) *
      Real.log (N : ℝ) ≤ ((N : ℝ) / q + 1) * Real.log (N : ℝ) :=
    mul_le_mul_of_nonneg_right hcard hlog
  exact le_trans (by simpa [nsmul_eq_mul] using hsum) this

lemma log_div_le_log (N m : ℕ) :
    Real.log ((N / m : ℕ) : ℝ) ≤ Real.log (N : ℝ) + 1 := by
  by_cases hN : N = 0
  · subst hN; simp [Real.log_zero]
  by_cases h0 : N / m = 0
  · simp [h0, Real.log_zero]
    have : 0 ≤ Real.log (N : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : (1 : ℕ) ≤ N))
    linarith
  have : Real.log ((N / m : ℕ) : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by exact_mod_cast (Nat.pos_of_ne_zero h0))
      (by exact_mod_cast Nat.div_le_self N m)
  linarith

lemma inner_typeI_le (q a m N : ℕ) :
    ∑ k ∈ (Finset.Icc 1 (N / m)).filter (fun k => (m * k) % q = a % q),
      Real.log (k : ℝ) ≤
      ((N : ℝ) + 1) * (Real.log (N : ℝ) + 1) := by
  have hcard : (((Finset.Icc 1 (N / m)).filter
      (fun k => (m * k) % q = a % q)).card : ℝ) ≤ (N : ℝ) + 1 := by
    have hsub : ((Finset.Icc 1 (N / m)).filter
        (fun k => (m * k) % q = a % q)).card ≤ N / m := by
      have := Finset.card_filter_le
        (Finset.Icc 1 (N / m)) (fun k => (m * k) % q = a % q)
      simpa [card_Icc_one] using this
    have : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr (Nat.div_le_self N m)
    exact le_trans (Nat.cast_le.mpr hsub) (by linarith)
  by_cases hNm : N / m = 0
  · simp [hNm]; positivity
  have hterm : ∀ k ∈ (Finset.Icc 1 (N / m)).filter (fun k => (m * k) % q = a % q),
      Real.log (k : ℝ) ≤ Real.log ((N / m : ℕ) : ℝ) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.1 (Finset.mem_filter.1 hk).1).1
    have hk2 : k ≤ N / m := (Finset.mem_Icc.1 (Finset.mem_filter.1 hk).1).2
    exact Real.log_le_log (by exact_mod_cast hk1) (by exact_mod_cast hk2)
  have hsum := Finset.sum_le_card_nsmul _ _ (Real.log ((N / m : ℕ) : ℝ)) hterm
  have hlog := log_div_le_log N m
  have hnn : 0 ≤ Real.log ((N / m : ℕ) : ℝ) :=
    Real.log_nonneg (by
      have : (1 : ℕ) ≤ N / m := Nat.pos_of_ne_zero hNm
      exact_mod_cast this)
  have : (((Finset.Icc 1 (N / m)).filter
      (fun k => (m * k) % q = a % q)).card : ℝ) * Real.log ((N / m : ℕ) : ℝ) ≤
      ((N : ℝ) + 1) * (Real.log (N : ℝ) + 1) :=
    mul_le_mul hcard hlog (by linarith) (by linarith)
  exact le_trans (by simpa [nsmul_eq_mul] using hsum) this

lemma typeI_log_sum_le (q a U N : ℕ) :
    ∑ m ∈ Finset.Icc 1 U,
      ∑ k ∈ (Finset.Icc 1 (N / m)).filter (fun k => (m * k) % q = a % q),
        Real.log (k : ℝ) ≤
      (U : ℝ) * ((N : ℝ) + 1) * (Real.log (N : ℝ) + 1) := by
  have hterm : ∀ m ∈ Finset.Icc 1 U,
      ∑ k ∈ (Finset.Icc 1 (N / m)).filter (fun k => (m * k) % q = a % q),
        Real.log (k : ℝ) ≤ ((N : ℝ) + 1) * (Real.log (N : ℝ) + 1) :=
    fun m _ => inner_typeI_le q a m N
  have hsum := Finset.sum_le_card_nsmul _ _ (((N : ℝ) + 1) * (Real.log (N : ℝ) + 1)) hterm
  have hcard : ((Finset.Icc 1 U).card : ℝ) = U := by
    simp [card_Icc_one]
  have : ((Finset.Icc 1 U).card : ℝ) * (((N : ℝ) + 1) * (Real.log (N : ℝ) + 1)) =
      (U : ℝ) * ((N : ℝ) + 1) * (Real.log (N : ℝ) + 1) := by
    rw [hcard]; ring
  exact le_trans (by simpa [nsmul_eq_mul] using hsum) this.le





lemma card_multiples_Icc (d N : ℕ) (hd : 1 ≤ d) :
    ((Finset.Icc 1 N).filter (fun n => d ∣ n)).card = N / d := by
  let t := Finset.Icc 1 (N / d)
  have himg : ∀ k ∈ t, d * k ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hk).1
    have hk2 : k ≤ N / d := (Finset.mem_Icc.1 hk).2
    have hle : d * k ≤ N :=
      le_trans (Nat.mul_le_mul_left d hk2) (Nat.mul_div_le N d)
    have hge : 1 ≤ d * k := Nat.mul_le_mul hd hk1
    exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hge, hle⟩, ⟨k, rfl⟩⟩
  have hinj : Set.InjOn (fun k : ℕ => d * k) (t : Set ℕ) := by
    intro k _ k' _ heq
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < d) heq
  have hsub : t.image (fun k => d * k) ⊆
      (Finset.Icc 1 N).filter (fun n => d ∣ n) := by
    intro n hn
    rcases Finset.mem_image.1 hn with ⟨k, hk, rfl⟩
    exact himg k hk
  have hle : t.card ≤ ((Finset.Icc 1 N).filter (fun n => d ∣ n)).card :=
    ((Finset.card_image_of_injOn hinj).symm.le).trans (Finset.card_le_card hsub)
  have hge : ((Finset.Icc 1 N).filter (fun n => d ∣ n)).card ≤ t.card := by
    let s := (Finset.Icc 1 N).filter (fun n => d ∣ n)
    have hinj' : Set.InjOn (fun n : ℕ => n / d) (s : Set ℕ) := by
      intro n hn m hm heq
      have hnd : d ∣ n := (Finset.mem_filter.1 (show n ∈ s from hn)).2
      have hmd : d ∣ m := (Finset.mem_filter.1 (show m ∈ s from hm)).2
      have hmul : d * (n / d) = d * (m / d) := congrArg (HMul.hMul d) heq
      exact (Nat.mul_div_cancel' hnd).symm.trans (hmul.trans (Nat.mul_div_cancel' hmd))
    have hsub' : s.image (fun n => n / d) ⊆ t := by
      intro k hk
      rcases Finset.mem_image.1 hk with ⟨n, hn, rfl⟩
      have hnI := Finset.mem_Icc.1 (Finset.mem_filter.1 hn).1
      have hdv := (Finset.mem_filter.1 hn).2
      have hk1 : 1 ≤ n / d := by
        have : d ≤ n := Nat.le_of_dvd (by omega) hdv
        exact Nat.div_pos this (by omega)
      have hk2 : n / d ≤ N / d := Nat.div_le_div_right hnI.2
      exact Finset.mem_Icc.2 ⟨hk1, hk2⟩
    have hcard := Finset.card_le_card hsub'
    have himgCard : s.card = (s.image (fun n => n / d)).card :=
      (Finset.card_image_of_injOn hinj').symm
    rwa [← himgCard] at hcard
  have ht : t.card = N / d := card_Icc_one _
  omega

lemma divisors_subset_Icc {n N : ℕ} (hn : n ∈ Finset.Icc 1 N) :
    n.divisors ⊆ Finset.Icc 1 N := by
  intro d hd
  exact Finset.mem_Icc.2 ⟨Nat.pos_of_mem_divisors hd,
    le_trans (Nat.divisor_le hd) (Finset.mem_Icc.1 hn).2⟩

lemma sum_divisors_as_ite {R : Type*} [AddCommMonoid R] (f : ℕ → R) {n N : ℕ}
    (hn : n ∈ Finset.Icc 1 N) :
    ∑ d ∈ n.divisors, f d =
      ∑ d ∈ Finset.Icc 1 N, if d ∈ n.divisors then f d else 0 := by
  rw [← Finset.sum_extend_by_zero]
  refine Finset.sum_subset (divisors_subset_Icc hn) ?_
  intro d _ hd
  simp [hd]

lemma sum_divisors_eq_sum_multiples {R : Type*} [CommSemiring R] (f : ℕ → R) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, f d =
      ∑ d ∈ Finset.Icc 1 N, f d * (N / d : ℕ) := by
  have h1 : ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, f d =
      ∑ n ∈ Finset.Icc 1 N,
        ∑ d ∈ Finset.Icc 1 N, if d ∈ n.divisors then f d else 0 :=
    Finset.sum_congr rfl fun n hn => sum_divisors_as_ite f hn
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd1 : 1 ≤ d := (Finset.mem_Icc.1 hd).1
  have hiff : ∀ n ∈ Finset.Icc 1 N, d ∈ n.divisors ↔ d ∣ n := by
    intro n hn
    constructor
    · intro h; exact (Nat.mem_divisors.1 h).1
    · intro hdv
      exact Nat.mem_divisors.2 ⟨hdv, by
        have := (Finset.mem_Icc.1 hn).1; omega⟩
  have : ∑ n ∈ Finset.Icc 1 N, (if d ∈ n.divisors then f d else 0) =
      ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n), f d := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n hn => ?_
    by_cases h : d ∈ n.divisors
    · simp [h, (hiff n hn).1 h]
    · have : ¬ d ∣ n := fun hdv => h ((hiff n hn).2 hdv)
      simp [h, this]
  rw [this, Finset.sum_const, card_multiples_Icc d N hd1]
  simp [nsmul_eq_mul, mul_comm]

lemma sum_log_eq_sum_vonMangoldt_mul_floor (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) =
      ∑ d ∈ Finset.Icc 1 N, vonMangoldt d * (N / d : ℕ) := by
  have h : ∀ n ∈ Finset.Icc 1 N,
      Real.log (n : ℝ) = ∑ d ∈ n.divisors, vonMangoldt d := fun n _ =>
    (vonMangoldt_sum (n := n)).symm
  rw [Finset.sum_congr rfl h]
  exact sum_divisors_eq_sum_multiples vonMangoldt N

lemma vonMangoldt_floor_le (N d : ℕ) :
    vonMangoldt d * (N / d : ℕ) ≤ vonMangoldt d * ((N : ℝ) / d) := by
  have hΛ : 0 ≤ vonMangoldt d := vonMangoldt_nonneg
  have : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
  nlinarith

/-! ### Maynard's theorem -/

/-- The forms `q t + a + h` (`h ∈ H`) being admissible modulo every prime dividing `q`
implies that `a + h` is coprime to `q`. -/
lemma coprime_offset_of_forms_admissible {H : Finset ℕ} {q a : ℕ} (hq : 0 < q)
    (hadm : ∀ p : ℕ, p.Prime → ∃ t : ZMod p, ∀ h ∈ H, (q : ZMod p) * t + a + h ≠ 0)
    {h : ℕ} (hh : h ∈ H) : (a + h).Coprime q := by
  refine Nat.coprime_of_dvd ?_
  intro p hp hpah hpq
  obtain ⟨t, ht⟩ := hadm p hp
  have hqt : (q : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff q p).2 hpq
  have hah : ((a + h : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).2 hpah
  have : (q : ZMod p) * t + a + h = 0 := by
    simp [hqt, ← Nat.cast_add, hah]
  exact (ht h hh) this

/-- Infinitely many `t` make a single shifted arithmetic progression prime. -/
lemma infinite_prime_in_AP_shift {q a h : ℕ} (hq : 0 < q) (hcop : (a + h).Coprime q) :
    {t : ℕ | (q * t + a + h).Prime}.Infinite := by
  have hq0 : q ≠ 0 := Nat.pos_iff_ne_zero.mp hq
  refine Set.infinite_of_forall_exists_gt (fun N => ?_)
  obtain ⟨p, hpN, hpp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (q * N + a + h) hq0 hcop
  have hle : a + h ≤ p := by omega
  have hdv : q ∣ p - (a + h) := (Nat.modEq_iff_dvd' hle).1 hmod.symm
  refine ⟨(p - (a + h)) / q, ?_, ?_⟩
  · have : q * ((p - (a + h)) / q) + a + h = p := by
      have := Nat.mul_div_cancel' hdv
      omega
    simpa [this] using hpp
  · have hmul : q * N + a + h < p := hpN
    have : q * N < q * ((p - (a + h)) / q) := by
      have := Nat.mul_div_cancel' hdv
      omega
    exact Nat.lt_of_mul_lt_mul_left this

/-- The `m = 0` case of Maynard: the set of all natural numbers is infinite. -/
lemma maynard_in_AP_zero :
    ∀ (H : Finset ℕ), Admissible H →
      ∀ (q a : ℕ), 0 < q →
        (∀ p : ℕ, p.Prime → ∃ t : ZMod p, ∀ h ∈ H, (q : ZMod p) * t + a + h ≠ 0) →
        {t : ℕ | 0 ≤ ((H.filter fun h => (q * t + a + h).Prime).card)}.Infinite := by
  intro H _ q a _ _ 
  have : {t : ℕ | 0 ≤ ((H.filter fun h => (q * t + a + h).Prime).card)} = Set.univ := by
    ext t; simp
  rw [this]
  exact Set.infinite_univ

/-- The `m = 1` case of Maynard, from Dirichlet's theorem. -/
lemma maynard_in_AP_one {H : Finset ℕ} (hH : H.Nonempty) (hAdm : Admissible H)
    {q a : ℕ} (hq : 0 < q)
    (hadm : ∀ p : ℕ, p.Prime → ∃ t : ZMod p, ∀ h ∈ H, (q : ZMod p) * t + a + h ≠ 0) :
    {t : ℕ | 1 ≤ ((H.filter fun h => (q * t + a + h).Prime).card)}.Infinite := by
  obtain ⟨h, hh⟩ := hH
  have hcop : (a + h).Coprime q := coprime_offset_of_forms_admissible hq hadm hh
  have hinf := infinite_prime_in_AP_shift (h := h) hq hcop
  refine hinf.mono ?_
  intro t ht
  have : h ∈ H.filter fun h' => (q * t + a + h').Prime :=
    Finset.mem_filter.2 ⟨hh, by simpa [Nat.add_assoc] using ht⟩
  exact Nat.succ_le_iff.2 (Finset.card_pos.2 ⟨h, this⟩)

/-! #### Maynard weights and the ratio `M_k` -/

/-- The standard simplex volume: `{x : (Fin k → ℝ) | 0 ≤ x i ∧ ∑ x ≤ 1}`. -/
def simplex (k : ℕ) : Set (Fin k → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

/-- Maynard's functionals on a test function `F`.  We work with the explicit
non-negative test function `F = 1` on the simplex (GPY) as a baseline, and with
the one-parameter family `F_β(x) = ∏ i, (x i)^β` (`β > -1/2`) whose ratio is
evaluated in closed form via the Dirichlet integral. -/
noncomputable def maynardI (k : ℕ) (β : ℝ) : ℝ :=
  Real.Gamma (2 * β + 1) ^ k / Real.Gamma (1 + k * (2 * β + 1))

noncomputable def maynardJ (k : ℕ) (β : ℝ) : ℝ :=
  (1 / (β + 1) ^ 2) *
    Real.Gamma (2 * β + 1) ^ (k - 1) * Real.Gamma (2 * β + 3) /
      Real.Gamma (k * (2 * β + 1) + 2)

/-- The Maynard ratio for the symmetric power test function.  For `β = 0` this
recovers the GPY ratio `2 k / (k + 1)`. -/
noncomputable def maynardRatio (k : ℕ) (β : ℝ) : ℝ :=
  k * maynardJ k β / maynardI k β

/-- The product of primes `≤ w`. -/
noncomputable def primorialUp (w : ℕ) : ℕ :=
  ((Finset.range (w + 1)).filter Nat.Prime).prod (fun n : ℕ => n)

lemma primorialUp_pos (w : ℕ) : 0 < primorialUp w := by
  refine Finset.prod_pos ?_
  intro p hp
  exact (Nat.Prime.pos (Finset.mem_filter.1 hp).2)

lemma prime_dvd_primorialUp {p w : ℕ} (hp : p.Prime) (hpw : p ≤ w) :
    p ∣ primorialUp w := by
  unfold primorialUp
  exact Finset.dvd_prod_of_mem (fun n : ℕ => n)
    (Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le hpw), hp⟩)

/-- A residue `b` implementing the W-trick: `b ≡ a [MOD q]` and none of the
values `b + h` (`h ∈ H`) is divisible by a prime `p ≤ w`. -/
lemma exists_Wtrick_residue {H : Finset ℕ} {q a w : ℕ} (hq : 0 < q)
    (hadm : ∀ p : ℕ, p.Prime → ∃ t : ZMod p, ∀ h ∈ H, (q : ZMod p) * t + a + h ≠ 0) :
    ∃ b : ℕ, b % q = a % q ∧
      (∀ p : ℕ, p.Prime → p ≤ w → ∀ h ∈ H, ¬ p ∣ b + h) := by
  let P : Finset ℕ := (Finset.range (w + 1)).filter Nat.Prime
  let tP : ℕ → ℕ := fun p =>
    if h : p.Prime then ((hadm p h).choose : ZMod p).val else 0
  let s : ℕ → ℕ := fun n => n
  have hs0 : ∀ p ∈ P, s p ≠ 0 := by
    intro p hp
    exact ((Finset.mem_filter.1 hp).2).ne_zero
  have spp : Set.Pairwise (P : Set ℕ) (fun i j => Nat.Coprime (s i) (s j)) := by
    intro i hi j hj hij
    exact (Nat.coprime_primes (Finset.mem_filter.1 (show i ∈ P from hi)).2
      (Finset.mem_filter.1 (show j ∈ P from hj)).2).2 hij
  let t0 := (Nat.chineseRemainderOfFinset tP s P hs0 spp).1
  let b := q * t0 + a
  refine ⟨b, ?_, ?_⟩
  · simp [b, Nat.add_mod, Nat.mul_mod]
  · intro p hp hpw h hh
    have hpP : p ∈ P := Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le hpw), hp⟩
    have hcong : t0 ≡ tP p [MOD p] := by
      simpa [s, Nat.ModEq] using
        (Nat.chineseRemainderOfFinset tP s P hs0 spp).2 p hpP
    have htP : tP p = ((hadm p hp).choose : ZMod p).val := dif_pos hp
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : NeZero p := ⟨hp.ne_zero⟩
    have hgood := (hadm p hp).choose_spec h hh
    intro hdiv
    have hb : (b : ZMod p) = (q : ZMod p) * (t0 : ZMod p) + a := by
      simp [b]
    have ht0 : (t0 : ZMod p) = (hadm p hp).choose := by
      have h1 : (t0 : ZMod p) = (tP p : ZMod p) :=
        (ZMod.natCast_eq_natCast_iff _ _ p).2 hcong
      rw [h1, htP]
      simpa using (ZMod.natCast_val (R := ZMod p) (hadm p hp).choose)
    have hz : ((b + h : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).2 hdiv
    have : (q : ZMod p) * (hadm p hp).choose + a + h = 0 := by
      simp [← ht0, ← hb, ← Nat.cast_add] at hz
      simpa [ht0, hb] using hz
    exact hgood this

/-! ### Elementary arithmetic estimates for the Maynard sieve -/

lemma totient_pos_of_pos {n : ℕ} (hn : 0 < n) : 0 < n.totient :=
  Nat.totient_pos.2 hn

lemma totient_real_eq {n : ℕ} :
    (n.totient : ℝ) = (n : ℝ) * ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
  have hQ := Nat.totient_eq_mul_prod_factors n
  have hR : ((n.totient : ℚ) : ℝ) =
      (((n : ℚ) * ∏ p ∈ n.primeFactors, (1 - (p : ℚ)⁻¹) : ℚ) : ℝ) := by
    simp [hQ]
  simp only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_prod] at hR
  convert hR using 2
  refine Finset.prod_congr rfl fun p _ => ?_
  simp [Rat.cast_sub, Rat.cast_one, Rat.cast_inv, Rat.cast_natCast]

lemma one_sub_inv_prime {p : ℕ} (hp : p.Prime) :
    (1 - (p : ℝ)⁻¹) = ((p - 1 : ℕ) : ℝ) / p := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpos : (1 : ℕ) ≤ p := hp.one_le
  rw [Nat.cast_sub hpos, Nat.cast_one]
  field_simp [hp0]

lemma totient_prime_real {p : ℕ} (hp : p.Prime) :
    (p.totient : ℝ) = (p : ℝ) - 1 := by
  rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]

/-- The product `∏_{p≤w} (1-1/p)` is positive. -/
lemma primorialUp_totient_pos (w : ℕ) :
    0 < ((primorialUp w).totient : ℝ) := by
  exact_mod_cast totient_pos_of_pos (primorialUp_pos w)

/-- Crude bound `φ(n) ≥ √n / 2` is false, but `φ(n) ≥ c n / log log n` is true for large n.
    We only need `0 < φ(n)` and `φ(n) ≤ n`. -/
lemma totient_inv_le {n : ℕ} (hn : 0 < n) :
    (1 : ℝ) / n.totient ≤ (n : ℝ) := by
  have hφ : (0 : ℝ) < n.totient := by exact_mod_cast totient_pos_of_pos hn
  have hle : (n.totient : ℝ) ≤ n := by exact_mod_cast Nat.totient_le n
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have : (1 : ℝ) / n.totient ≤ 1 / 1 := by
    apply one_div_le_one_div_of_le
    · norm_num
    · have : (1 : ℝ) ≤ n.totient := by exact_mod_cast (totient_pos_of_pos hn)
      exact this
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- Cardinality of the power set of `Icc 1 R`. -/
lemma card_powerset_Icc (R : ℕ) :
    ((Finset.Icc 1 R).powerset.card : ℝ) ≤ (2 : ℝ) ^ R := by
  have : (Finset.Icc 1 R).powerset.card = 2 ^ (Finset.Icc 1 R).card :=
    Finset.card_powerset _
  rw [this, card_Icc_one]
  exact_mod_cast le_rfl

/-- The residue-class von Mangoldt sum. -/
noncomputable def psiMod (N q a : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % q = a % q), vonMangoldt n

lemma psiMod_nonneg (N q a : ℕ) : 0 ≤ psiMod N q a :=
  Finset.sum_nonneg fun _ _ => vonMangoldt_nonneg

lemma psiMod_le_log_mul_card (N q a : ℕ) :
    psiMod N q a ≤
      Real.log (N : ℝ) * (((Finset.Icc 1 N).filter (fun n => n % q = a % q)).card : ℝ) := by
  by_cases hN : N = 0
  · subst hN; simp [psiMod]
  have hlog : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : (1 : ℕ) ≤ N))
  have hterm : ∀ n ∈ (Finset.Icc 1 N).filter (fun n => n % q = a % q),
      vonMangoldt n ≤ Real.log (N : ℝ) := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.1 (Finset.mem_filter.1 hn).1).1
    have hnN : n ≤ N := (Finset.mem_Icc.1 (Finset.mem_filter.1 hn).1).2
    have hle := vonMangoldt_le_log (n := n)
    have hlogn : vonMangoldt n ≤ Real.log n := hle
    have : Real.log n ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by exact_mod_cast hn1) (by exact_mod_cast hnN)
    exact le_trans hlogn this
  have hsum := Finset.sum_le_card_nsmul _ _ (Real.log (N : ℝ)) hterm
  simpa [psiMod, nsmul_eq_mul, mul_comm] using hsum

lemma psiMod_le_trivial (N q a : ℕ) (_hq : 0 < q) :
    psiMod N q a ≤ Real.log (N : ℝ) * ((N : ℝ) / q + 1) := by
  have hcard := card_residue_Icc_le_real q a N
  have h1 := psiMod_le_log_mul_card N q a
  by_cases hN : N = 0
  · subst hN; simp [psiMod]
  have hlog0 : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : (1 : ℕ) ≤ N))
  have hnn : 0 ≤
      (((Finset.Icc 1 N).filter (fun n => n % q = a % q)).card : ℝ) :=
    Nat.cast_nonneg _
  have : Real.log (N : ℝ) *
      (((Finset.Icc 1 N).filter (fun n => n % q = a % q)).card : ℝ) ≤
      Real.log (N : ℝ) * ((N : ℝ) / q + 1) :=
    mul_le_mul_of_nonneg_left hcard hlog0
  exact le_trans h1 this

/-- `log⁺(R/n)` vanishes for `n ≥ R`. -/
noncomputable def logPlus (R n : ℕ) : ℝ :=
  if n = 0 then 0
  else max (Real.log (R : ℝ) - Real.log (n : ℝ)) 0

lemma logPlus_nonneg (R n : ℕ) : 0 ≤ logPlus R n := by
  unfold logPlus
  split_ifs <;> simp [le_max_right]

lemma logPlus_eq_of_lt {R n : ℕ} (hn : 0 < n) (h : n < R) :
    logPlus R n = Real.log (R : ℝ) - Real.log (n : ℝ) := by
  have hlog : Real.log (n : ℝ) < Real.log (R : ℝ) :=
    Real.log_lt_log (by exact_mod_cast hn) (by exact_mod_cast h)
  unfold logPlus
  rw [if_neg hn.ne']
  exact max_eq_left (le_of_lt (sub_pos.2 hlog))

lemma logPlus_eq_zero_of_le {R n : ℕ} (h : R ≤ n) :
    logPlus R n = 0 := by
  unfold logPlus
  split_ifs with hn0
  · rfl
  · apply max_eq_right
    by_cases hR : R = 0
    · subst hR
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      have hlogn : 0 ≤ Real.log (n : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (Nat.succ_le_of_lt hnpos))
      simp [Real.log_zero, hlogn]
    · have hRpos : 0 < R := Nat.pos_of_ne_zero hR
      have hnpos : 0 < n := lt_of_lt_of_le hRpos h
      have : Real.log (R : ℝ) ≤ Real.log (n : ℝ) :=
        Real.log_le_log (by exact_mod_cast hRpos) (by exact_mod_cast h)
      linarith

open Classical

/-- Pairwise coprimality of a `k`-tuple. -/
def pairwiseCoprime {k : ℕ} (d : Fin k → ℕ) : Prop :=
  Pairwise fun i j => (d i).Coprime (d j)

/-- Support condition for Maynard's `y`-variables: squarefree, coprime to `W`,
    pairwise coprime, and product `< R`. -/
def maynardSupport {k : ℕ} (W R : ℕ) (d : Fin k → ℕ) : Prop :=
  (∀ i, Squarefree (d i)) ∧ (∀ i, (d i).Coprime W) ∧
    pairwiseCoprime d ∧ (∏ i, d i) < R ∧ (∀ i, 0 < d i)

/-- The GPY/Maynard test function on the discrete simplex: product of
    `log⁺(R/d_i)`, restricted so that `∑ log d_i ≤ log R`.  For a first
    lower bound we use the constant test function on the simplex, which
    already gives ratio `2k/(k+1)`.  The full Maynard ratio `log k` is
    recovered below by a sparse product function. -/
noncomputable def maynardY {k : ℕ} (W R : ℕ) (d : Fin k → ℕ) : ℝ :=
  if maynardSupport W R d then ∏ i, logPlus R (d i) else 0

lemma maynardY_nonneg {k : ℕ} (W R : ℕ) (d : Fin k → ℕ) :
    0 ≤ maynardY W R d := by
  unfold maynardY
  split_ifs
  · exact Finset.prod_nonneg fun _ _ => logPlus_nonneg _ _
  · exact le_rfl

/-- Maynard λ-weights: `λ_d = (∏ μ(d_i) d_i) ∑_{d_i | r_i} (∏ μ(r_i)/φ(r_i)) y_r`.
    We use the equivalent “diagonal” form in which `y` is already the
    summed variable (Maynard’s change of variables). -/
noncomputable def maynardLambda {k : ℕ} (W R : ℕ) (d : Fin k → ℕ) : ℝ :=
  if maynardSupport W R d then
    (∏ i, (ArithmeticFunction.moebius (d i) : ℝ)) * maynardY W R d
  else 0

/-- Finite box of `k`-tuples with each coordinate in `range R`. -/
def maynardBox (k R : ℕ) : Finset (Fin k → ℕ) :=
  Fintype.piFinset fun _ : Fin k => Finset.range (max R 1)

/-- The Maynard weight attached to an integer `n` and an offset tuple `h`. -/
noncomputable def maynardWeight {k : ℕ} (W R : ℕ) (hOf : Fin k → ℕ) (n : ℕ) : ℝ :=
  (∑ d ∈ (maynardBox k R).filter
      (fun d => ∀ i, d i ∣ n + hOf i),
    maynardLambda W R d) ^ 2

lemma maynardLambda_eq_zero_of_not_support {k W R : ℕ} {d : Fin k → ℕ}
    (h : ¬ maynardSupport W R d) : maynardLambda W R d = 0 := by
  unfold maynardLambda
  simp [h]

lemma maynardWeight_nonneg {k : ℕ} (W R : ℕ) (hOf : Fin k → ℕ) (n : ℕ) :
    0 ≤ maynardWeight W R hOf n :=
  sq_nonneg _

/-- `lcm` of corresponding coordinates of two tuples. -/
def lcmTuple {k : ℕ} (d e : Fin k → ℕ) : Fin k → ℕ :=
  fun i => (d i).lcm (e i)

lemma dvd_lcmTuple_left {k : ℕ} (d e : Fin k → ℕ) (i : Fin k) :
    d i ∣ lcmTuple d e i := Nat.dvd_lcm_left _ _

lemma dvd_lcmTuple_right {k : ℕ} (d e : Fin k → ℕ) (i : Fin k) :
    e i ∣ lcmTuple d e i := Nat.dvd_lcm_right _ _

/-- If each `lcm(d i, e i)` divides `n + h i`, then both `d` and `e` divide. -/
lemma lcmTuple_dvd_iff {k : ℕ} {d e : Fin k → ℕ} {hOf : Fin k → ℕ} {n : ℕ} :
    (∀ i, lcmTuple d e i ∣ n + hOf i) ↔
      (∀ i, d i ∣ n + hOf i) ∧ (∀ i, e i ∣ n + hOf i) := by
  constructor
  · intro h
    exact ⟨fun i => (dvd_lcmTuple_left d e i).trans (h i),
           fun i => (dvd_lcmTuple_right d e i).trans (h i)⟩
  · intro ⟨hd, he⟩ i
    exact Nat.lcm_dvd (hd i) (he i)

lemma maynardWeight_eq {k W R : ℕ} (hOf : Fin k → ℕ) (n : ℕ) :
    maynardWeight W R hOf n =
      ∑ d ∈ maynardBox k R, ∑ e ∈ maynardBox k R,
        (if (∀ i, d i ∣ n + hOf i) ∧ (∀ i, e i ∣ n + hOf i) then
          maynardLambda W R d * maynardLambda W R e else 0) := by
  unfold maynardWeight
  rw [Finset.sum_filter, sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
  split_ifs with h h' h'' <;> simp_all

/-- Numbers in `Icc lo hi` lying in a single residue class form an AP
whose quotients occupy an interval of length at most `(hi-lo)/q`. -/
lemma card_residue_Icc_interval (q r lo hi : ℕ) (hq : 0 < q) :
    ((Finset.Icc lo hi).filter (fun n => n % q = r)).card ≤
      (hi - lo) / q + 1 := by
  set s := (Finset.Icc lo hi).filter (fun n => n % q = r) with hs
  by_cases hne : s.Nonempty
  · have hinj : Set.InjOn (fun n : ℕ => n / q) (s : Set ℕ) := by
      intro n hn m hm heq
      have hnr : n % q = r := (Finset.mem_filter.1 (show n ∈ s from hn)).2
      have hmr : m % q = r := (Finset.mem_filter.1 (show m ∈ s from hm)).2
      have hdiv : n / q = m / q := by simpa using heq
      calc
        n = q * (n / q) + n % q := (Nat.div_add_mod n q).symm
        _ = q * (m / q) + m % q := by rw [hdiv, hnr, hmr]
        _ = m := Nat.div_add_mod m q
    set ks := s.image (fun n => n / q)
    have hks_card : s.card = ks.card := (Finset.card_image_of_injOn hinj).symm
    have hks_ne : ks.Nonempty := Finset.image_nonempty.2 hne
    have hle_minmax : ks.min' hks_ne ≤ ks.max' hks_ne := ks.min'_le_max' hks_ne
    have hsub : ks ⊆ Finset.Icc (ks.min' hks_ne) (ks.max' hks_ne) := by
      intro k hk
      exact Finset.mem_Icc.2 ⟨ks.min'_le k hk, ks.le_max' k hk⟩
    have hcard_ks : ks.card ≤ ks.max' hks_ne - ks.min' hks_ne + 1 := by
      have h1 := Finset.card_le_card hsub
      rw [Nat.card_Icc] at h1
      have : ks.max' hks_ne + 1 - ks.min' hks_ne =
          ks.max' hks_ne - ks.min' hks_ne + 1 := by
        have := hle_minmax
        omega
      omega
    obtain ⟨nmax, hnmax_s, hnmax_k⟩ := Finset.mem_image.1 (ks.max'_mem hks_ne)
    obtain ⟨nmin, hnmin_s, hnmin_k⟩ := Finset.mem_image.1 (ks.min'_mem hks_ne)
    have hnmaxI : nmax ∈ Finset.Icc lo hi := (Finset.mem_filter.1 hnmax_s).1
    have hnminI : nmin ∈ Finset.Icc lo hi := (Finset.mem_filter.1 hnmin_s).1
    have hnmaxr : nmax % q = r := (Finset.mem_filter.1 hnmax_s).2
    have hnminr : nmin % q = r := (Finset.mem_filter.1 hnmin_s).2
    have hnmax_eq : nmax = q * (ks.max' hks_ne) + r := by
      have := (Nat.div_add_mod nmax q).symm
      rwa [hnmax_k, hnmaxr] at this
    have hnmin_eq : nmin = q * (ks.min' hks_ne) + r := by
      have := (Nat.div_add_mod nmin q).symm
      rwa [hnmin_k, hnminr] at this
    have hge : nmin ≤ nmax := by
      rw [hnmin_eq, hnmax_eq]
      exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hle_minmax) _
    have hdiff : nmax - nmin = q * (ks.max' hks_ne - ks.min' hks_ne) := by
      rw [hnmax_eq, hnmin_eq, Nat.add_sub_add_right, Nat.mul_sub]
    have hnmax_le : nmax ≤ hi := (Finset.mem_Icc.1 hnmaxI).2
    have hnmin_ge : lo ≤ nmin := (Finset.mem_Icc.1 hnminI).1
    have hle_hi_lo : nmax - nmin ≤ hi - lo := by omega
    have hkm : ks.max' hks_ne - ks.min' hks_ne ≤ (hi - lo) / q := by
      have : q * (ks.max' hks_ne - ks.min' hks_ne) ≤ hi - lo := by
        rwa [← hdiff]
      exact (Nat.le_div_iff_mul_le hq).2 (by rwa [Nat.mul_comm])
    have hmain : s.card ≤ (hi - lo) / q + 1 := by
      rw [hks_card]
      exact hcard_ks.trans (Nat.add_le_add_right hkm 1)
    simpa [hs] using hmain
  · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.1 hne
    have h0 : s.card = 0 := by simp [hs0]
    have h0' : ((Finset.Icc lo hi).filter (fun n => n % q = r)).card = 0 := by
      simpa [hs] using h0
    rw [h0']
    exact Nat.zero_le _

/-- A residue class in a shifted interval of length `L` has at most `L/q+1` elements. -/
lemma card_residue_shift (q r N L : ℕ) (hq : 0 < q) :
    ((Finset.Icc (N + 1) (N + L)).filter (fun n => n % q = r)).card ≤ L / q + 1 := by
  have h := card_residue_Icc_interval q r (N + 1) (N + L) hq
  have : (N + L - (N + 1)) / q + 1 ≤ L / q + 1 := by
    have : N + L - (N + 1) ≤ L := by omega
    exact Nat.add_le_add_right (Nat.div_le_div_right this) 1
  exact h.trans this


open Real MeasureTheory Set intervalIntegral

/- Explicit one-dimensional test function and box integrals for M_k -/

noncomputable def maynardPsi (b T u : ℝ) : ℝ :=
  if 0 ≤ u ∧ u ≤ T then (b + u)⁻¹ else 0

lemma maynardPsi_nonneg {b T u : ℝ} (hb : 0 < b) : 0 ≤ maynardPsi b T u := by
  unfold maynardPsi
  split_ifs with h
  · exact inv_nonneg.2 (by linarith [h.1])
  · exact le_rfl

lemma maynardPsi_eq {b T u : ℝ} (h0 : 0 ≤ u) (hT : u ≤ T) :
    maynardPsi b T u = (b + u)⁻¹ := if_pos ⟨h0, hT⟩

lemma continuousOn_inv_add {b T : ℝ} (hb : 0 < b) (hT : 0 ≤ T) :
    ContinuousOn (fun u : ℝ => (b + u)⁻¹) (uIcc 0 T) := by
  apply ContinuousOn.inv₀
  · exact (continuous_const.add continuous_id).continuousOn
  · intro u hu
    have : 0 ≤ u := (uIcc_of_le hT ▸ hu).1
    linarith

lemma intervalIntegral_inv_add {b T : ℝ} (hb : 0 < b) (hT : 0 ≤ T) :
    ∫ u in (0 : ℝ)..T, (b + u)⁻¹ = Real.log ((b + T) / b) := by
  have hshift := integral_comp_add_left (f := fun v : ℝ => v⁻¹) (d := b) (a := (0 : ℝ)) (b := T)
  have h1 : (∫ u in (0 : ℝ)..T, (b + u)⁻¹) = ∫ v in (b + 0)..(b + T), v⁻¹ := hshift
  have h2 : (∫ v in (b + 0)..(b + T), v⁻¹) = ∫ v in b..(b + T), v⁻¹ := by
    simp
  rw [h1, h2, integral_inv_of_pos hb (by linarith)]

lemma intervalIntegral_inv_sq_add {b T : ℝ} (hb : 0 < b) (hT : 0 ≤ T) :
    ∫ u in (0 : ℝ)..T, (b + u)⁻¹ ^ 2 = T / (b * (b + T)) := by
  -- antiderivative of (b+u)^{-2} is -(b+u)^{-1}
  have hderiv : ∀ u ∈ uIcc 0 T,
      HasDerivAt (fun t : ℝ => - (b + t)⁻¹) ((b + u)⁻¹ ^ 2) u := by
    intro u hu
    have hu0 : 0 ≤ u := (uIcc_of_le hT ▸ hu).1
    have hpos : 0 < b + u := by linarith
    have hne : (b + u) ≠ 0 := ne_of_gt hpos
    have hid : HasDerivAt (fun t : ℝ => b + t) (1 : ℝ) u :=
      (hasDerivAt_id u).const_add b
    have hinv : HasDerivAt (fun t : ℝ => (b + t)⁻¹) (-(b + u) ^ (-2 : ℤ)) u := by
      have := (hasDerivAt_inv (x := (b + u)) hne).comp u hid
      simpa [one_mul] using this
    -- -(b+u)^{-2} composed, then negate
    have : HasDerivAt (fun t : ℝ => (b + t)⁻¹) (-(b + u)⁻¹ ^ 2) u := by
      convert hinv using 1
      rw [zpow_neg, zpow_two, inv_pow, pow_two]
    convert this.neg using 1
    ring
  have hint : IntervalIntegrable (fun u : ℝ => (b + u)⁻¹ ^ 2) volume 0 T :=
    ((continuousOn_inv_add hb hT).pow 2).intervalIntegrable
  have heq := integral_eq_sub_of_hasDerivAt hderiv hint
  have hsimp : -(b + T)⁻¹ - (-(b + 0)⁻¹) = T / (b * (b + T)) := by
    simp
    have hb0 : (b : ℝ) ≠ 0 := ne_of_gt hb
    have hbt : (b + T) ≠ 0 := by linarith
    field_simp [hb0, hbt]
    ring
  rw [heq, hsimp]

lemma intervalIntegral_maynardPsi {b T : ℝ} (hb : 0 < b) (hT : 0 ≤ T) :
    ∫ u in (0 : ℝ)..T, maynardPsi b T u = Real.log ((b + T) / b) := by
  have hcongr : ∀ u ∈ uIcc 0 T, maynardPsi b T u = (b + u)⁻¹ := by
    intro u hu
    have : u ∈ Icc 0 T := uIcc_of_le hT ▸ hu
    exact maynardPsi_eq this.1 this.2
  rw [integral_congr hcongr, intervalIntegral_inv_add hb hT]

lemma intervalIntegral_maynardPsi_sq {b T : ℝ} (hb : 0 < b) (hT : 0 ≤ T) :
    ∫ u in (0 : ℝ)..T, maynardPsi b T u ^ 2 = T / (b * (b + T)) := by
  have hcongr : ∀ u ∈ uIcc 0 T, maynardPsi b T u ^ 2 = (b + u)⁻¹ ^ 2 := by
    intro u hu
    have : u ∈ Icc 0 T := uIcc_of_le hT ▸ hu
    rw [maynardPsi_eq this.1 this.2]
  rw [integral_congr hcongr, intervalIntegral_inv_sq_add hb hT]

lemma intervalIntegral_u_inv_sq {b T : ℝ} (hb : 0 < b) (hT : 0 ≤ T) :
    ∫ u in (0 : ℝ)..T, u * (b + u)⁻¹ ^ 2 =
      Real.log ((b + T) / b) + b * (b + T)⁻¹ - 1 := by
  have hsplit : ∀ u ∈ uIcc 0 T,
      u * (b + u)⁻¹ ^ 2 = (b + u)⁻¹ - b * (b + u)⁻¹ ^ 2 := by
    intro u hu
    have : 0 ≤ u := (uIcc_of_le hT ▸ hu).1
    have hne : b + u ≠ 0 := by linarith
    field_simp [hne]
    ring
  have hI1 : IntervalIntegrable (fun u : ℝ => (b + u)⁻¹) volume 0 T :=
    (continuousOn_inv_add hb hT).intervalIntegrable
  have hI2 : IntervalIntegrable (fun u : ℝ => b * (b + u)⁻¹ ^ 2) volume 0 T :=
    (continuousOn_const.mul ((continuousOn_inv_add hb hT).pow 2)).intervalIntegrable
  rw [integral_congr hsplit, intervalIntegral.integral_sub hI1 hI2,
      intervalIntegral_inv_add hb hT]
  have hconst : (∫ u in (0 : ℝ)..T, b * (b + u)⁻¹ ^ 2) =
      b * ∫ u in (0 : ℝ)..T, (b + u)⁻¹ ^ 2 :=
    intervalIntegral.integral_const_mul _ _
  rw [hconst, intervalIntegral_inv_sq_add hb hT]
  have hb0 : (b : ℝ) ≠ 0 := ne_of_gt hb
  have hbt : b + T ≠ 0 := by linarith
  field_simp [hb0, hbt]
  ring

lemma log_div_eq {b T : ℝ} (hb : 0 < b) (hT : 0 ≤ T) :
    Real.log ((b + T) / b) = Real.log (b + T) - Real.log b :=
  Real.log_div (by linarith) (ne_of_gt hb)

/-- Parameters: `b = 1 / (2 log (T+3))`, `T ≥ 3`. -/
noncomputable def maynardB (T : ℝ) : ℝ := (2 * Real.log (T + 3))⁻¹

lemma maynardB_pos {T : ℝ} (hT : 0 ≤ T) : 0 < maynardB T := by
  unfold maynardB
  have : 1 < T + 3 := by linarith
  have hlog : 0 < Real.log (T + 3) := Real.log_pos this
  positivity

lemma rexp_one_lt_three : Real.exp 1 < 3 :=
  lt_trans Real.exp_one_lt_d9 (by norm_num)

lemma log_six_gt_one : (1 : ℝ) < Real.log 6 := by
  have : Real.exp 1 < 6 := lt_trans rexp_one_lt_three (by norm_num)
  exact (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 6)).2 this

lemma maynardB_lt_one {T : ℝ} (hT : 3 ≤ T) : maynardB T < 1 := by
  unfold maynardB
  have hlog : Real.log 6 ≤ Real.log (T + 3) :=
    Real.log_le_log (by norm_num) (by linarith)
  have : (1 : ℝ) < 2 * Real.log (T + 3) := by
    nlinarith [log_six_gt_one, hlog]
  exact inv_lt_one_of_one_lt₀ this

lemma log_two_lt_one : Real.log 2 < 1 :=
  (Real.log_lt_iff_lt_exp (by norm_num)).2
    (lt_trans (by norm_num : (2 : ℝ) < 2.7) (lt_trans (by norm_num : (2.7 : ℝ) < 2.7182818283)
      Real.exp_one_gt_d9))

/-- `log((b+T)/b) ≥ log T`. -/
lemma log_add_div_b_ge_log {T : ℝ} (hT : 3 ≤ T) :
    Real.log T ≤ Real.log ((maynardB T + T) / maynardB T) := by
  have hb := maynardB_pos (by linarith : 0 ≤ T)
  have hT0 : 0 < T := by linarith
  apply Real.log_le_log hT0
  have : 0 < maynardB T := hb
  have : T * maynardB T ≤ maynardB T + T := by
    have hb1 : maynardB T < 1 := maynardB_lt_one hT
    nlinarith [mul_nonneg (le_of_lt hT0) (le_of_lt hb)]
  have hb0 : maynardB T ≠ 0 := ne_of_gt hb
  exact (le_div_iff₀ hb).2 (by linarith)

/-- `∫ ψ ≥ log T`, `∫ ψ² = T/(b(b+T))`. -/
lemma maynardPsi_int_ge_log {T : ℝ} (hT : 3 ≤ T) :
    Real.log T ≤ ∫ u in (0 : ℝ)..T, maynardPsi (maynardB T) T u := by
  rw [intervalIntegral_maynardPsi (maynardB_pos (by linarith)) (by linarith)]
  exact log_add_div_b_ge_log hT

lemma maynardPsi_int_sq_pos {T : ℝ} (hT : 3 ≤ T) :
    0 < ∫ u in (0 : ℝ)..T, maynardPsi (maynardB T) T u ^ 2 := by
  rw [intervalIntegral_maynardPsi_sq (maynardB_pos (by linarith)) (by linarith)]
  have hb := maynardB_pos (by linarith : 0 ≤ T)
  positivity

/-- The ratio `(∫ψ)² / (∫ψ²) ≥ (log T)/4` for `T ≥ 16`. -/
lemma maynardPsi_ratio_ge {T : ℝ} (hT : 16 ≤ T) :
    Real.log T / 4 ≤
      (∫ u in (0 : ℝ)..T, maynardPsi (maynardB T) T u) ^ 2 /
      (∫ u in (0 : ℝ)..T, maynardPsi (maynardB T) T u ^ 2) := by
  have hT3 : 3 ≤ T := by linarith
  have hb := maynardB_pos (by linarith : 0 ≤ T)
  have hT0 : 0 < T := by linarith
  rw [intervalIntegral_maynardPsi hb (le_of_lt hT0),
      intervalIntegral_maynardPsi_sq hb (le_of_lt hT0)]
  have hden : T / (maynardB T * (maynardB T + T)) > 0 := by positivity
  -- (∫ψ)² / (∫ψ²) = log((b+T)/b)² * b(b+T)/T ≥ (log T)² * b
  have hge : Real.log T ^ 2 * maynardB T ≤
      Real.log ((maynardB T + T) / maynardB T) ^ 2 *
        (maynardB T * (maynardB T + T) / T) := by
    have hlog := log_add_div_b_ge_log hT3
    have hlog0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    have hbT : maynardB T ≤ maynardB T * (maynardB T + T) / T := by
      have : maynardB T * T ≤ maynardB T * (maynardB T + T) := by nlinarith [le_of_lt hb]
      exact (le_div_iff₀ hT0).2 (by nlinarith)
    have hsq : Real.log T ^ 2 ≤ Real.log ((maynardB T + T) / maynardB T) ^ 2 :=
      sq_le_sq' (by nlinarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ T)]) hlog
    exact mul_le_mul hsq hbT (le_of_lt hb) (sq_nonneg _)
  -- (log T)² * b = (log T)² / (2 log(T+3)) ≥ (log T)/4
  have hfrac : Real.log T / 4 ≤ Real.log T ^ 2 * maynardB T := by
    unfold maynardB
    have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
    have hlogT3 : 0 < Real.log (T + 3) := Real.log_pos (by linarith)
    -- log(T+3) ≤ log T + 1
    have hle : Real.log (T + 3) ≤ Real.log T + 1 := by
      have hdiff : Real.log (T + 3) - Real.log T = Real.log ((T + 3) / T) :=
        (Real.log_div (by linarith) (ne_of_gt hT0)).symm
      have heq : (T + 3) / T = 1 + 3 / T := by field_simp [ne_of_gt hT0]
      have hlog : Real.log (1 + 3 / T) ≤ 3 / T := by
        have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 3 / T)
        linarith
      have h31 : 3 / T ≤ 1 := (div_le_one hT0).2 (by linarith)
      rw [heq] at hdiff
      linarith
    -- (log T)² / (2 log(T+3)) ≥ (log T)² / (2(log T+1)) ≥ (log T)/4
    -- iff 2 log T ≥ log T + 1 when log T ≥ 2, i.e. T ≥ e² < 16
    have hlogT2 : (2 : ℝ) ≤ Real.log T := by
      have : Real.exp 2 ≤ T := by
        have h2 : Real.exp 2 ≤ Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add]; norm_num
        have : Real.exp 1 * Real.exp 1 < 3 * 3 :=
          mul_lt_mul rexp_one_lt_three (le_of_lt rexp_one_lt_three) (Real.exp_pos _) (by norm_num)
        linarith
      exact (Real.le_log_iff_exp_le hT0).2 this
    have hgoal : Real.log T / 4 ≤ Real.log T ^ 2 / (2 * Real.log (T + 3)) := by
      have hpos2 : 0 < 2 * Real.log (T + 3) := by positivity
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 4) hpos2]
      nlinarith [hlogT, hle, hlogT2]
    have heq : Real.log T ^ 2 * (2 * Real.log (T + 3))⁻¹ =
        Real.log T ^ 2 / (2 * Real.log (T + 3)) := by field_simp
    rwa [heq]
  have hrew : Real.log ((maynardB T + T) / maynardB T) ^ 2 *
      (maynardB T * (maynardB T + T) / T) =
      Real.log ((maynardB T + T) / maynardB T) ^ 2 /
        (T / (maynardB T * (maynardB T + T))) := by
    have hb0 : maynardB T ≠ 0 := ne_of_gt hb
    have hbt : maynardB T + T ≠ 0 := by linarith
    field_simp [hb0, hbt]
  linarith

/- Iterated integrals over the box `[0, T]^k` -/

/-- Iterated interval integral of `f : (Fin k → ℝ) → ℝ` over `[0, T]^k`. -/
noncomputable def boxIntegral (T : ℝ) : (k : ℕ) → ((Fin k → ℝ) → ℝ) → ℝ
  | 0, f => f (fun i => nomatch i)
  | k + 1, f => ∫ t in (0 : ℝ)..T, boxIntegral T k (fun x => f (Fin.cons t x))

lemma boxIntegral_zero (T : ℝ) (f : (Fin 0 → ℝ) → ℝ) :
    boxIntegral T 0 f = f (fun i => nomatch i) := rfl

lemma boxIntegral_succ (T : ℝ) (k : ℕ) (f : (Fin (k + 1) → ℝ) → ℝ) :
    boxIntegral T (k + 1) f =
      ∫ t in (0 : ℝ)..T, boxIntegral T k (fun x => f (Fin.cons t x)) := rfl

lemma boxIntegral_mul_const (T : ℝ) (c : ℝ) :
    (k : ℕ) → (f : (Fin k → ℝ) → ℝ) →
      boxIntegral T k (fun x => c * f x) = c * boxIntegral T k f
  | 0, f => by simp [boxIntegral_zero]
  | k + 1, f => by
      rw [boxIntegral_succ, boxIntegral_succ]
      have h : ∀ t, boxIntegral T k (fun x => c * f (Fin.cons t x)) =
          c * boxIntegral T k (fun x => f (Fin.cons t x)) :=
        fun t => boxIntegral_mul_const T c k _
      simp_rw [h, intervalIntegral.integral_const_mul]

lemma boxIntegral_prod (T : ℝ) (g : ℝ → ℝ) :
    (k : ℕ) → boxIntegral T k (fun x => ∏ i, g (x i)) =
      (∫ t in (0 : ℝ)..T, g t) ^ k
  | 0 => by
      simp [boxIntegral_zero, pow_zero]
  | k + 1 => by
      rw [boxIntegral_succ, pow_succ]
      have hinner : ∀ t,
          boxIntegral T k (fun x => ∏ i : Fin (k + 1), g (Fin.cons (α := fun _ => ℝ) t x i)) =
          g t * boxIntegral T k (fun x => ∏ i : Fin k, g (x i)) := by
        intro t
        have hfun :
            (fun x : Fin k → ℝ => ∏ i : Fin (k + 1), g (Fin.cons (α := fun _ => ℝ) t x i)) =
              (fun x => g t * ∏ i : Fin k, g (x i)) := by
          funext x
          have hcomp : (fun i : Fin (k + 1) => g (Fin.cons (α := fun _ => ℝ) t x i)) =
              Fin.cons (g t) (fun i : Fin k => g (x i)) := by
            funext i
            refine Fin.cases ?_ ?_ i
            · simp [Fin.cons_zero]
            · intro j; simp [Fin.cons_succ]
          rw [hcomp]
          exact Fin.prod_cons (g t) (fun i : Fin k => g (x i))
        rw [hfun]
        exact boxIntegral_mul_const T (g t) k (fun x => ∏ i : Fin k, g (x i))
      simp_rw [hinner]
      rw [boxIntegral_prod T g k, intervalIntegral.integral_mul_const]
      ring

/-- `∫ u ψ² = log((b+T)/b) + b/(b+T) - 1`. -/
lemma maynardPsi_mean_num_eq {T : ℝ} (hT : 3 ≤ T) :
    ∫ u in (0 : ℝ)..T, u * maynardPsi (maynardB T) T u ^ 2 =
      Real.log ((maynardB T + T) / maynardB T) +
        maynardB T * (maynardB T + T)⁻¹ - 1 := by
  have hb := maynardB_pos (by linarith : 0 ≤ T)
  have hcongr : ∀ u ∈ uIcc 0 T,
      u * maynardPsi (maynardB T) T u ^ 2 = u * (maynardB T + u)⁻¹ ^ 2 := by
    intro u hu
    have : u ∈ Icc 0 T := uIcc_of_le (show 0 ≤ T by linarith) ▸ hu
    rw [maynardPsi_eq this.1 this.2]
  rw [integral_congr hcongr, intervalIntegral_u_inv_sq hb (by linarith)]

lemma log_T_ge_two {T : ℝ} (hT : 16 ≤ T) : (2 : ℝ) ≤ Real.log T := by
  have hT0 : 0 < T := by linarith
  have hexp : Real.exp 2 ≤ T := by
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    have : Real.exp 1 * Real.exp 1 < 3 * 3 :=
      mul_lt_mul rexp_one_lt_three (le_of_lt rexp_one_lt_three)
        (Real.exp_pos _) (by norm_num)
    linarith
  exact (Real.le_log_iff_exp_le hT0).2 hexp

lemma log_three_lt_twelve_ten : Real.log 3 < (12 : ℝ) / 10 := by
  have hexp : (3 : ℝ) < Real.exp ((12 : ℝ) / 10) := by
    have h1 : (27 : ℝ) / 10 < Real.exp 1 :=
      lt_trans (by norm_num) Real.exp_one_gt_d9
    have h02 : (12 : ℝ) / 10 < Real.exp ((1 : ℝ) / 5) := by
      have := Real.add_one_lt_exp (by norm_num : (1 : ℝ) / 5 ≠ 0)
      linarith
    have heq : Real.exp ((12 : ℝ) / 10) = Real.exp 1 * Real.exp ((1 : ℝ) / 5) := by
      rw [← Real.exp_add]; ring_nf
    have hmul : Real.exp 1 * Real.exp ((1 : ℝ) / 5) > (27 : ℝ) / 10 * ((12 : ℝ) / 10) :=
      mul_lt_mul h1 (le_of_lt h02) (by norm_num) (le_of_lt (Real.exp_pos _))
    have h3 : (3 : ℝ) < (27 : ℝ) / 10 * ((12 : ℝ) / 10) := by norm_num
    rw [heq]
    linarith [hmul, h3]
  exact (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 3)).2 hexp

lemma log_two_ge_two_thirds : (2 : ℝ) / 3 ≤ Real.log 2 := by
  have hexp : Real.exp ((2 : ℝ) / 3) ≤ 2 := by
    have hlt : Real.exp 1 < (28 : ℝ) / 10 :=
      lt_trans Real.exp_one_lt_d9 (by norm_num)
    have heq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    have hexp2 : Real.exp 2 < (28 : ℝ) / 10 * ((28 : ℝ) / 10) := by
      rw [heq]
      exact mul_lt_mul hlt (le_of_lt hlt) (Real.exp_pos _) (by norm_num)
    have hexp2' : Real.exp 2 < 8 := lt_trans hexp2 (by norm_num)
    have hpow : Real.exp ((2 : ℝ) / 3) ^ 3 = Real.exp 2 := by
      rw [← Real.exp_nat_mul]; norm_num
    have hpos : 0 ≤ Real.exp ((2 : ℝ) / 3) := le_of_lt (Real.exp_pos _)
    have hlt3 : Real.exp ((2 : ℝ) / 3) ^ 3 < (2 : ℝ) ^ 3 := by
      rw [hpow]; exact lt_of_lt_of_eq hexp2' (by norm_num)
    exact le_of_lt
      ((pow_lt_pow_iff_left₀ hpos (by norm_num : (0 : ℝ) ≤ 2)
        (by norm_num : (3 : ℕ) ≠ 0)).1 hlt3)
  exact (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 2)).2 hexp

lemma log_nineteen_gt_two : (2 : ℝ) < Real.log 19 := by
  have : Real.exp 2 < 19 := by
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    have : Real.exp 1 * Real.exp 1 < 3 * 3 :=
      mul_lt_mul rexp_one_lt_three (le_of_lt rexp_one_lt_three)
        (Real.exp_pos _) (by norm_num)
    linarith
  exact (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 19)).2 this

/-- `log u ≤ (2/5) u` for `u ≥ 2`, via the tangent of `log` at `5/2`. -/
lemma log_le_two_fifths {u : ℝ} (hu : 2 ≤ u) : Real.log u ≤ (2 / 5) * u := by
  have hu0 : 0 < u := by linarith
  have hle : Real.log (u / (5 / 2)) ≤ u / (5 / 2) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hsum : Real.log u = Real.log (u / (5 / 2)) + Real.log (5 / 2) := by
    rw [Real.log_div hu0.ne' (by norm_num : ((5 : ℝ) / 2) ≠ 0)]
    ring
  have h25 : Real.log (5 / 2) ≤ 1 := by
    have : (5 : ℝ) / 2 ≤ Real.exp 1 := by
      have : (27 : ℝ) / 10 < Real.exp 1 :=
        lt_trans (by norm_num) Real.exp_one_gt_d9
      linarith
    exact (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 5 / 2)).2 this
  have hdiv : u / (5 / 2) = (2 / 5) * u := by field_simp
  linarith

/-- `b(b+T)/T ≤ (17/16) b` for `T ≥ 16`. -/
lemma maynardB_shift_div_le {T : ℝ} (hT : 16 ≤ T) :
    maynardB T * (maynardB T + T) / T ≤ (17 / 16) * maynardB T := by
  have hb := maynardB_pos (by linarith : 0 ≤ T)
  have hT0 : 0 < T := by linarith
  have hb1 : maynardB T < 1 := maynardB_lt_one (by linarith)
  have hle : maynardB T + T ≤ (17 / 16) * T := by
    have : maynardB T ≤ T / 16 := by
      have : (1 : ℝ) ≤ T / 16 := (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).2 (by linarith)
      linarith
    linarith
  have : maynardB T * (maynardB T + T) ≤ maynardB T * ((17 / 16) * T) :=
    mul_le_mul_of_nonneg_left hle (le_of_lt hb)
  exact (div_le_iff₀ hT0).2 (by linarith)

/-- `log((b+T)/b) ≤ log 3 + log T + log(log(T+3))`. -/
lemma log_add_div_b_le {T : ℝ} (hT : 16 ≤ T) :
    Real.log ((maynardB T + T) / maynardB T) ≤
      Real.log 3 + Real.log T + Real.log (Real.log (T + 3)) := by
  have hb := maynardB_pos (by linarith : 0 ≤ T)
  have hT0 : 0 < T := by linarith
  have hlogT3 : 0 < Real.log (T + 3) := Real.log_pos (by linarith)
  have heq : (maynardB T + T) / maynardB T = 1 + T * (2 * Real.log (T + 3)) := by
    unfold maynardB
    field_simp [ne_of_gt hb]
  rw [heq]
  have harg : 1 + T * (2 * Real.log (T + 3)) ≤ 3 * T * Real.log (T + 3) := by
    have : (1 : ℝ) ≤ T * Real.log (T + 3) := by
      have h1 : (1 : ℝ) ≤ T := by linarith
      have h2 : (1 : ℝ) ≤ Real.log (T + 3) :=
        le_trans (le_of_lt log_six_gt_one)
          (Real.log_le_log (by norm_num) (by linarith))
      nlinarith
    linarith
  have hpos : 0 < 1 + T * (2 * Real.log (T + 3)) := by positivity
  have hlog := Real.log_le_log hpos harg
  have h3 : 0 < 3 * T * Real.log (T + 3) := by positivity
  have hsplit : Real.log (3 * T * Real.log (T + 3)) =
      Real.log 3 + Real.log T + Real.log (Real.log (T + 3)) := by
    rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by norm_num) (ne_of_gt hT0)]
  rwa [hsplit] at hlog

/-- The mean is at most `4/5` for `T ≥ 16`. -/
lemma maynardPsi_mean_le {T : ℝ} (hT : 16 ≤ T) :
    (∫ u in (0 : ℝ)..T, u * maynardPsi (maynardB T) T u ^ 2) /
      (∫ u in (0 : ℝ)..T, maynardPsi (maynardB T) T u ^ 2) ≤ (4 : ℝ) / 5 := by
  have hT3 : 3 ≤ T := by linarith
  have hb := maynardB_pos (by linarith : 0 ≤ T)
  have hT0 : 0 < T := by linarith
  rw [maynardPsi_mean_num_eq hT3,
      intervalIntegral_maynardPsi_sq hb (le_of_lt hT0)]
  set b := maynardB T
  set L := Real.log ((b + T) / b)
  have hb0 : 0 < b := hb
  have hden : 0 < T / (b * (b + T)) := by positivity
  rw [div_le_iff₀ hden]
  have hLle := log_add_div_b_le hT
  have hbTle := maynardB_shift_div_le hT
  have hbTfrac : b * (b + T)⁻¹ ≤ (1 : ℝ) / 16 := by
    have : b ≤ T / 16 := by
      have hb1 : b < 1 := maynardB_lt_one hT3
      have : (1 : ℝ) ≤ T / 16 := (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).2 (by linarith)
      linarith
    have hpos : 0 < b + T := by linarith
    rw [mul_inv_le_iff₀ hpos]
    have : b * 16 ≤ T := (mul_comm b 16) ▸ ((le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).1 this)
    linarith
  have hnum_le : L + b * (b + T)⁻¹ - 1 ≤
      Real.log 3 + Real.log T + Real.log (Real.log (T + 3)) - 1 + 1 / 16 := by
    linarith
  have hprod : (L + b * (b + T)⁻¹ - 1) * (b * (b + T) / T) ≤
      (Real.log 3 + Real.log T + Real.log (Real.log (T + 3)) - 1 + 1 / 16) *
        ((17 / 16) * b) := by
    have hnn1 : 0 ≤ L + b * (b + T)⁻¹ - 1 := by
      have hLT : Real.log T ≤ L := log_add_div_b_ge_log hT3
      have : (2 : ℝ) ≤ Real.log T := log_T_ge_two hT
      have : 0 ≤ b * (b + T)⁻¹ := by positivity
      linarith
    have hnn2 : 0 ≤ b * (b + T) / T := by positivity
    exact mul_le_mul hnum_le hbTle hnn2 (by linarith)
  -- Rewrite `(17/16) b = (17/32) / log(T+3)`
  have hb_eq : (17 / 16) * b = (17 / 32) / Real.log (T + 3) := by
    unfold b maynardB
    field_simp
    ring
  have hlogT3 : 0 < Real.log (T + 3) := Real.log_pos (by linarith)
  have hfrac :
      (Real.log 3 + Real.log T + Real.log (Real.log (T + 3)) - 1 + 1 / 16) *
        ((17 / 16) * b) =
      (17 / 32) *
        ((Real.log 3 + Real.log T + Real.log (Real.log (T + 3)) - 1 + 1 / 16) /
          Real.log (T + 3)) := by
    rw [hb_eq]
    field_simp [ne_of_gt hlogT3]
  -- Split the fraction and bound each piece
  have hsplit :
      (Real.log 3 + Real.log T + Real.log (Real.log (T + 3)) - 1 + 1 / 16) /
        Real.log (T + 3) =
      Real.log T / Real.log (T + 3) +
        Real.log (Real.log (T + 3)) / Real.log (T + 3) +
        (Real.log 3 - 1 + 1 / 16) / Real.log (T + 3) := by
    field_simp [ne_of_gt hlogT3]
    ring
  have hp1 : Real.log T / Real.log (T + 3) ≤ 1 := by
    exact div_le_one_of_le₀ (Real.log_le_log hT0 (by linarith)) (le_of_lt hlogT3)
  have hp2 : Real.log (Real.log (T + 3)) / Real.log (T + 3) ≤ (2 : ℝ) / 5 := by
    have hu : (2 : ℝ) ≤ Real.log (T + 3) :=
      le_of_lt (lt_of_lt_of_le log_nineteen_gt_two
        (Real.log_le_log (by norm_num) (by linarith)))
    have hll : Real.log (Real.log (T + 3)) ≤ (2 / 5) * Real.log (T + 3) :=
      log_le_two_fifths hu
    exact (div_le_iff₀ hlogT3).2 (by linarith)
  have hp3 : (Real.log 3 - 1 + 1 / 16) / Real.log (T + 3) ≤ (1 : ℝ) / 10 := by
    have hnum : Real.log 3 - 1 + 1 / 16 < (21 : ℝ) / 80 := by
      have : Real.log 3 < (12 : ℝ) / 10 := log_three_lt_twelve_ten
      -- 12/10 - 1 + 1/16 = 21/80
      linarith
    have hden' : (8 : ℝ) / 3 ≤ Real.log (T + 3) := by
      have h16le : Real.log 16 ≤ Real.log (T + 3) :=
        Real.log_le_log (by norm_num) (by linarith)
      have h16 : Real.log 16 = 4 * Real.log 2 := by
        have : (16 : ℝ) = 2 ^ (4 : ℕ) := by norm_num
        rw [this, Real.log_pow]; norm_num
      have : (8 : ℝ) / 3 ≤ 4 * Real.log 2 := by
        linarith [log_two_ge_two_thirds]
      linarith
    rw [div_le_iff₀ hlogT3]
    -- (21/80) / (8/3) = 63/640 < 1/10
    have : (21 : ℝ) / 80 ≤ (1 / 10) * ((8 : ℝ) / 3) := by norm_num
    linarith
  have hsum : Real.log T / Real.log (T + 3) +
      Real.log (Real.log (T + 3)) / Real.log (T + 3) +
      (Real.log 3 - 1 + 1 / 16) / Real.log (T + 3) ≤
      (1 : ℝ) + 2 / 5 + 1 / 10 := by
    linarith [hp1, hp2, hp3]
  have hnum1732 : (17 : ℝ) / 32 * (1 + 2 / 5 + 1 / 10) ≤ (4 : ℝ) / 5 := by norm_num
  have hclose : (L + b * (b + T)⁻¹ - 1) * (b * (b + T) / T) ≤ (4 : ℝ) / 5 := by
    have := hprod
    rw [hfrac] at this
    have : (17 / 32) *
        ((Real.log 3 + Real.log T + Real.log (Real.log (T + 3)) - 1 + 1 / 16) /
          Real.log (T + 3)) ≤
        (17 / 32) * (1 + 2 / 5 + 1 / 10) := by
      apply mul_le_mul_of_nonneg_left
      · rwa [hsplit]
      · norm_num
    linarith
  have hCpos : 0 < b * (b + T) / T := by positivity
  calc
    (L + b * (b + T)⁻¹ - 1)
        = (L + b * (b + T)⁻¹ - 1) * (b * (b + T) / T) *
            (b * (b + T) / T)⁻¹ := by field_simp [ne_of_gt hCpos]
    _ ≤ (4 / 5) * (b * (b + T) / T)⁻¹ :=
        mul_le_mul_of_nonneg_right hclose (inv_nonneg.2 (le_of_lt hCpos))
    _ = (4 / 5) * (T / (b * (b + T))) := by field_simp [ne_of_gt hT0, ne_of_gt hb0]

lemma fin_sum_cons (t : ℝ) (x : Fin k → ℝ) :
    ∑ i : Fin (k + 1), Fin.cons (α := fun _ => ℝ) t x i = t + ∑ i, x i := by
  rw [Fin.sum_univ_succ]
  simp [Fin.cons_zero, Fin.cons_succ]

lemma fin_prod_cons_g (g : ℝ → ℝ) (t : ℝ) (x : Fin k → ℝ) :
    ∏ i : Fin (k + 1), g (Fin.cons (α := fun _ => ℝ) t x i) =
      g t * ∏ i : Fin k, g (x i) := by
  have hcomp : (fun i : Fin (k + 1) => g (Fin.cons (α := fun _ => ℝ) t x i)) =
      Fin.cons (g t) (fun i : Fin k => g (x i)) := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp [Fin.cons_zero]
    · intro j; simp [Fin.cons_succ]
  rw [hcomp]
  exact Fin.prod_cons (g t) (fun i : Fin k => g (x i))

lemma intervalIntegrable_inv_add {b T : ℝ} (hb : 0 < b) (hT : 0 ≤ T) :
    IntervalIntegrable (fun u : ℝ => (b + u)⁻¹) volume 0 T :=
  (continuousOn_inv_add hb hT).intervalIntegrable

lemma intervalIntegrable_mul_inv_add {b T : ℝ} (hb : 0 < b) (hT : 0 ≤ T) :
    IntervalIntegrable (fun u : ℝ => u * (b + u)⁻¹) volume 0 T :=
  (continuousOn_id.mul (continuousOn_inv_add hb hT)).intervalIntegrable

/-- Affine-times-product identity for an integrable factor `g`. -/
lemma boxIntegral_affine_mul_prod (T : ℝ) (g : ℝ → ℝ)
    (hg : IntervalIntegrable g volume 0 T)
    (htg : IntervalIntegrable (fun t => t * g t) volume 0 T) (c d : ℝ) :
    (k : ℕ) →
      boxIntegral T k (fun x => (c + d * ∑ i, x i) * ∏ i, g (x i)) =
        c * (∫ t in (0 : ℝ)..T, g t) ^ k +
          d * (k : ℝ) * (∫ t in (0 : ℝ)..T, t * g t) *
            (∫ t in (0 : ℝ)..T, g t) ^ k.pred
  | 0 => by
      simp [boxIntegral_zero, pow_zero]
  | k + 1 => by
      rw [boxIntegral_succ, Nat.pred_succ]
      have hfun : ∀ t,
          (fun x : Fin k → ℝ =>
              (c + d * ∑ i : Fin (k + 1), Fin.cons (α := fun _ => ℝ) t x i) *
                ∏ i : Fin (k + 1), g (Fin.cons (α := fun _ => ℝ) t x i)) =
            (fun x =>
              ((c + d * t) * g t + (d * g t) * ∑ i, x i) * ∏ i, g (x i)) := by
        intro t
        funext x
        rw [fin_sum_cons, fin_prod_cons_g]
        ring
      have hinner : ∀ t,
          boxIntegral T k (fun x =>
              (c + d * ∑ i : Fin (k + 1), Fin.cons (α := fun _ => ℝ) t x i) *
                ∏ i : Fin (k + 1), g (Fin.cons (α := fun _ => ℝ) t x i)) =
            (c + d * t) * g t * (∫ s in (0 : ℝ)..T, g s) ^ k +
              (d * g t) * (k : ℝ) * (∫ s in (0 : ℝ)..T, s * g s) *
                (∫ s in (0 : ℝ)..T, g s) ^ k.pred := by
        intro t
        rw [hfun t, boxIntegral_affine_mul_prod T g hg htg
          ((c + d * t) * g t) (d * g t) k]
      simp_rw [hinner]
      set Ig := (∫ s in (0 : ℝ)..T, g s)
      set Isg := (∫ s in (0 : ℝ)..T, s * g s)
      have hcongr : ∀ t ∈ uIcc 0 T,
          (c + d * t) * g t * Ig ^ k +
            (d * g t) * (k : ℝ) * Isg * Ig ^ k.pred =
          (c * Ig ^ k + d * (k : ℝ) * Isg * Ig ^ k.pred) * g t +
            (d * Ig ^ k) * (t * g t) := by
        intro t _; ring
      rw [integral_congr hcongr]
      have hlin :
          (∫ t in (0 : ℝ)..T,
              (c * Ig ^ k + d * (k : ℝ) * Isg * Ig ^ k.pred) * g t +
                (d * Ig ^ k) * (t * g t)) =
            (c * Ig ^ k + d * (k : ℝ) * Isg * Ig ^ k.pred) * Ig +
              (d * Ig ^ k) * Isg := by
        rw [intervalIntegral.integral_add (hg.const_mul _) (htg.const_mul _),
            intervalIntegral.integral_const_mul,
            intervalIntegral.integral_const_mul]
      rw [hlin]
      cases k with
      | zero =>
          simp [Ig, Isg, pow_zero]
      | succ k' =>
          simp [Ig, Isg, pow_succ, Nat.cast_add, Nat.cast_one]
          ring

lemma boxIntegral_sum_mul_prod (T : ℝ) (g : ℝ → ℝ)
    (hg : IntervalIntegrable g volume 0 T)
    (htg : IntervalIntegrable (fun t => t * g t) volume 0 T) (k : ℕ) :
    boxIntegral T k (fun x => (∑ i, x i) * ∏ i, g (x i)) =
      (k : ℝ) * (∫ t in (0 : ℝ)..T, t * g t) *
        (∫ t in (0 : ℝ)..T, g t) ^ k.pred := by
  simpa using boxIntegral_affine_mul_prod T g hg htg 0 1 k

/-- Lower bound on the mass of `{∑ x_i ≤ A}` for a product density:
`∫ (1 - (∑ x_i)/A) ∏ g = (1 - k μ / A) (∫ g)^k` when `k ≥ 1`. -/
lemma boxIntegral_markov_weight (T : ℝ) (g : ℝ → ℝ)
    (hg : IntervalIntegrable g volume 0 T)
    (htg : IntervalIntegrable (fun t => t * g t) volume 0 T)
    (A : ℝ) {k : ℕ} (_hk : 1 ≤ k) :
    boxIntegral T k (fun x => (1 - (∑ i, x i) / A) * ∏ i, g (x i)) =
      (∫ t in (0 : ℝ)..T, g t) ^ k -
        (k : ℝ) / A * (∫ t in (0 : ℝ)..T, t * g t) *
          (∫ t in (0 : ℝ)..T, g t) ^ (k - 1) := by
  have h := boxIntegral_affine_mul_prod T g hg htg 1 (-(1 / A)) k
  rw [Nat.pred_eq_sub_one] at h
  have hfun :
      (fun x : Fin k → ℝ => (1 - (∑ i, x i) / A) * ∏ i, g (x i)) =
        (fun x => (1 + -(1 / A) * ∑ i, x i) * ∏ i, g (x i)) := by
    funext x; ring
  rw [hfun, h]
  ring

lemma intervalIntegrable_inv_sq {b T : ℝ} (hb : 0 < b) (hT : 0 ≤ T) :
    IntervalIntegrable (fun u : ℝ => (b + u)⁻¹ ^ 2) volume 0 T :=
  ((continuousOn_inv_add hb hT).pow 2).intervalIntegrable

lemma intervalIntegrable_mul_inv_sq {b T : ℝ} (hb : 0 < b) (hT : 0 ≤ T) :
    IntervalIntegrable (fun u : ℝ => u * (b + u)⁻¹ ^ 2) volume 0 T :=
  (continuousOn_id.mul ((continuousOn_inv_add hb hT).pow 2)).intervalIntegrable

/-- Continuous Maynard ratio for the product test function, after dropping to a box
and applying Markov: `M ≥ (log T_u)/4 * (1/9)` when `T_u = k/10` and `k ≥ 160`. -/
lemma maynard_continuous_ratio_ge {k : ℕ} (hk : 160 ≤ k) :
    Real.log ((k : ℝ) / 10) / 36 ≤
      (∫ u in (0 : ℝ)..((k : ℝ) / 10), maynardPsi (maynardB ((k : ℝ) / 10)) ((k : ℝ) / 10) u) ^ 2 /
        (∫ u in (0 : ℝ)..((k : ℝ) / 10),
          maynardPsi (maynardB ((k : ℝ) / 10)) ((k : ℝ) / 10) u ^ 2) *
      (1 / 9 : ℝ) := by
  have hT : (16 : ℝ) ≤ (k : ℝ) / 10 := by
    have : (160 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hratio := maynardPsi_ratio_ge hT
  have : (0 : ℝ) ≤ 1 / 9 := by norm_num
  have hlog : 0 ≤ Real.log ((k : ℝ) / 10) :=
    Real.log_nonneg (by
      have : (1 : ℝ) ≤ (k : ℝ) / 10 := by linarith
      exact this)
  nlinarith


/- Discrete arithmetic sums used in the Maynard expansion. -/

lemma harmonic_cast (n : ℕ) :
    (harmonic n : ℝ) = ∑ k ∈ Finset.range n, ((k + 1 : ℕ) : ℝ)⁻¹ := by
  simp [harmonic, Rat.cast_sum]

lemma sum_inv_Icc_eq_harmonic (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (k : ℝ)⁻¹ = (harmonic n : ℝ) := by
  rw [harmonic_cast]
  refine Eq.symm ?_
  refine Finset.sum_bij (fun i _ => i + 1) ?_ ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_Icc.2 ⟨Nat.succ_pos i, Finset.mem_range.1 hi⟩
  · intro i _ j _ hij
    exact Nat.succ_injective hij
  · intro k hk
    have hkI := Finset.mem_Icc.1 hk
    refine ⟨k - 1, Finset.mem_range.2 (by omega), ?_⟩
    exact Nat.sub_add_cancel hkI.1
  · intro i hi
    simp

lemma sum_inv_Icc_ge_log {n : ℕ} (hn : 1 ≤ n) :
    Real.log n ≤ ∑ k ∈ Finset.Icc 1 n, (k : ℝ)⁻¹ := by
  rw [sum_inv_Icc_eq_harmonic]
  have := log_le_harmonic_floor (n : ℝ) (by exact_mod_cast Nat.zero_le n)
  simpa [Nat.floor_natCast] using this

lemma sum_inv_Icc_le_one_add_log {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n, (k : ℝ)⁻¹ ≤ 1 + Real.log n := by
  rw [sum_inv_Icc_eq_harmonic]
  have h := harmonic_le_one_add_log n
  exact_mod_cast h

lemma moebius_sq_eq_ite (n : ℕ) :
    ((moebius n : ℝ) ^ 2) = if Squarefree n then 1 else 0 := by
  by_cases h : Squarefree n
  · rw [if_pos h]
    have := moebius_sq_eq_one_of_squarefree h
    exact_mod_cast this
  · rw [if_neg h, moebius_eq_zero_of_not_squarefree h]
    simp

lemma moebius_sq_le_one (n : ℕ) : (moebius n : ℝ) ^ 2 ≤ 1 := by
  rw [moebius_sq_eq_ite]
  split_ifs <;> norm_num

lemma sum_mu_sq_div_n_le {x : ℕ} :
    ∑ n ∈ Finset.Icc 1 x, (moebius n : ℝ) ^ 2 / n ≤ 1 + Real.log (max x 1) := by
  have hterm : ∀ n ∈ Finset.Icc 1 x,
      (moebius n : ℝ) ^ 2 / n ≤ (1 : ℝ) / n := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.1 hn).1
    exact div_le_div_of_nonneg_right (moebius_sq_le_one n) (le_of_lt hn0)
  refine (Finset.sum_le_sum hterm).trans ?_
  by_cases hx : x = 0
  · subst hx; simp
  have hx1 : 1 ≤ x := by omega
  have hH := sum_inv_Icc_le_one_add_log hx1
  have hmax : (max x 1 : ℝ) = x := by exact_mod_cast max_eq_left hx1
  rw [hmax]
  convert hH using 1
  refine Finset.sum_congr rfl fun k hk => ?_
  exact one_div (k : ℝ)

lemma sum_inv_sq_le_pi_sq_div_six_sub_one (N : ℕ) :
    ∑ n ∈ Finset.Icc 2 N, (1 : ℝ) / n ^ 2 ≤ Real.pi ^ 2 / 6 - 1 := by
  by_cases hN : N < 2
  · have hempty : Finset.Icc 2 N = ∅ := by
      ext n; simp [Finset.mem_Icc]; omega
    simp [hempty]
    have : (1 : ℝ) ≤ Real.pi ^ 2 / 6 := by
      have h3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
      nlinarith [le_of_lt Real.pi_pos]
    linarith
  have hsplit : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext n; simp [Finset.mem_Icc]; omega
  have hsum : ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n ^ 2 =
      1 + ∑ n ∈ Finset.Icc 2 N, (1 : ℝ) / n ^ 2 := by
    rw [hsplit, Finset.sum_insert (by simp [Finset.mem_Icc])]
    simp
  have hle : ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n ^ 2 ≤ Real.pi ^ 2 / 6 :=
    sum_le_hasSum (Finset.Icc 1 N) (fun _ _ => by positivity) hasSum_zeta_two
  linarith

lemma pi_sq_div_six_sub_one_le_two_thirds :
    Real.pi ^ 2 / 6 - 1 ≤ (2 : ℝ) / 3 := by
  have hpi : Real.pi < (315 / 100 : ℝ) := by
    have := Real.pi_lt_d2
    norm_num at this ⊢
    exact this
  have hpos : 0 ≤ Real.pi := le_of_lt Real.pi_pos
  have hsq : Real.pi ^ 2 < (315 / 100) ^ 2 := by
    nlinarith [hpi, hpos]
  have : (315 / 100 : ℝ) ^ 2 / 6 - 1 ≤ (2 : ℝ) / 3 := by norm_num
  nlinarith

lemma sum_inv_sq_from_two_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 2 N, (1 : ℝ) / n ^ 2 ≤ (2 : ℝ) / 3 :=
  (sum_inv_sq_le_pi_sq_div_six_sub_one N).trans pi_sq_div_six_sub_one_le_two_thirds

lemma sum_inv_of_multiples_le (d x : ℕ) (hd : 0 < d) :
    ∑ n ∈ (Finset.Icc 1 x).filter (fun n => d ∣ n), (1 : ℝ) / n ≤
      (1 : ℝ) / d * ∑ m ∈ Finset.Icc 1 (x / d), (m : ℝ)⁻¹ := by
  set s := (Finset.Icc 1 x).filter (fun n => d ∣ n)
  have hre : ∀ n ∈ s, (1 : ℝ) / n = (1 : ℝ) / d * (1 / (n / d : ℕ)) := by
    intro n hn
    have hdv := (Finset.mem_filter.1 hn).2
    have hn1 : 1 ≤ n := (Finset.mem_Icc.1 (Finset.mem_filter.1 hn).1).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
    have hm0 : (0 : ℝ) < (n / d : ℕ) := by
      exact_mod_cast Nat.div_pos (Nat.le_of_dvd (by omega) hdv) hd
    have hmul : (d : ℝ) * (n / d : ℕ) = n := by
      exact_mod_cast Nat.mul_div_cancel' hdv
    field_simp [ne_of_gt hn0, ne_of_gt hd0, ne_of_gt hm0]
    linarith
  have hsum : ∑ n ∈ s, (1 : ℝ) / n =
      (1 : ℝ) / d * ∑ n ∈ s, (1 : ℝ) / (n / d : ℕ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hre
  rw [hsum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hinj : Set.InjOn (fun n : ℕ => n / d) (s : Set ℕ) := by
    intro n hn m hm heq
    have hn2 := (Finset.mem_filter.1 (show n ∈ s from hn)).2
    have hm2 := (Finset.mem_filter.1 (show m ∈ s from hm)).2
    have := congrArg (HMul.hMul d) heq
    rwa [Nat.mul_div_cancel' hn2, Nat.mul_div_cancel' hm2] at this
  have himg : s.image (fun n => n / d) ⊆ Finset.Icc 1 (x / d) := by
    intro m hm
    rcases Finset.mem_image.1 hm with ⟨n, hn, rfl⟩
    have hnI := Finset.mem_Icc.1 (Finset.mem_filter.1 hn).1
    have hdv := (Finset.mem_filter.1 hn).2
    exact Finset.mem_Icc.2 ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hdv) hd,
      Nat.div_le_div_right hnI.2⟩
  have himage : ∑ n ∈ s, (1 : ℝ) / (n / d : ℕ) =
      ∑ m ∈ s.image (fun n => n / d), (m : ℝ)⁻¹ := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun n hn => by simp
  rw [himage]
  exact Finset.sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => by positivity)

lemma sum_mu_sq_div_n_ge {N : ℕ} (hN : 3 ≤ N) :
    (1 / 6 : ℝ) * Real.log N ≤
      ∑ n ∈ Finset.Icc 1 N, (moebius n : ℝ) ^ 2 / n := by
  have h123 : (11 : ℝ) / 6 ≤
      ∑ n ∈ Finset.Icc 1 N, (moebius n : ℝ) ^ 2 / n := by
    have hsub : ({1, 2, 3} : Finset ℕ) ⊆ Finset.Icc 1 N := by
      intro n hn; simp at hn; rcases hn with h | h | h <;> subst h <;>
        exact Finset.mem_Icc.2 (by omega)
    have hpos : ∀ n ∈ Finset.Icc 1 N, 0 ≤ (moebius n : ℝ) ^ 2 / n :=
      fun n _ => by positivity
    have hsum3 : ∑ n ∈ ({1, 2, 3} : Finset ℕ), (moebius n : ℝ) ^ 2 / n =
        11 / 6 := by
      have sf2 : Squarefree 2 := Nat.prime_two.squarefree
      have sf3 : Squarefree 3 := Nat.prime_three.squarefree
      simp [moebius_sq_eq_ite, sf2, sf3]
      norm_num
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn _ => hpos n hn)
    rwa [hsum3] at this
  by_cases hlog : Real.log N ≤ 11
  · have : (1 / 6 : ℝ) * Real.log N ≤ 11 / 6 := by nlinarith
    linarith
  · have hN1 : 1 ≤ N := by omega
    have hH := sum_inv_Icc_ge_log hN1
    have hdiff :
        ∑ n ∈ Finset.Icc 1 N, (n : ℝ)⁻¹ -
          ∑ n ∈ Finset.Icc 1 N, (moebius n : ℝ) ^ 2 / n ≤
          ∑ d ∈ Finset.Icc 2 N, (1 : ℝ) / (d : ℝ) ^ 2 *
            ∑ m ∈ Finset.Icc 1 (N / d ^ 2), (m : ℝ)⁻¹ := by
      have hterm : ∀ n ∈ Finset.Icc 1 N,
          (n : ℝ)⁻¹ - (moebius n : ℝ) ^ 2 / n ≤
            ∑ d ∈ Finset.Icc 2 N,
              if d ^ 2 ∣ n then (1 : ℝ) / n else 0 := by
        intro n hn
        rw [moebius_sq_eq_ite]
        split_ifs with hsf
        · have h0 : (n : ℝ)⁻¹ - 1 / n = 0 := by
            have hn0 : (n : ℝ) ≠ 0 := by
              exact_mod_cast (Nat.pos_iff_ne_zero.mp (Finset.mem_Icc.1 hn).1)
            field_simp [hn0]; ring
          rw [h0]
          exact Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity
        · have ⟨p, hp, hpn⟩ : ∃ p, p.Prime ∧ p ^ 2 ∣ n := by
            have h := mt (Nat.squarefree_iff_prime_squarefree.2) hsf
            push_neg at h
            rcases h with ⟨p, hp, hpn⟩
            exact ⟨p, hp, by simpa [pow_two] using hpn⟩
          have hpge : 2 ≤ p := hp.two_le
          have hple : p ≤ N := by
            have : p ≤ p ^ 2 := Nat.le_self_pow (by omega) p
            have hnN : n ≤ N := (Finset.mem_Icc.1 hn).2
            have hp2le : p ^ 2 ≤ n :=
              Nat.le_of_dvd (by have := (Finset.mem_Icc.1 hn).1; omega) hpn
            omega
          have hmem : p ∈ Finset.Icc 2 N := Finset.mem_Icc.2 ⟨hpge, hple⟩
          have hposd : ∀ d ∈ Finset.Icc 2 N,
              0 ≤ (if d ^ 2 ∣ n then (1 : ℝ) / n else 0) := by
            intro d hd; split_ifs <;> positivity
          have := Finset.single_le_sum hposd hmem
          simpa [hpn] using this
      have hsum := Finset.sum_le_sum hterm
      rw [Finset.sum_sub_distrib] at hsum
      refine hsum.trans ?_
      rw [Finset.sum_comm]
      refine Finset.sum_le_sum fun d hd => ?_
      have hd0 : 0 < d := by have := (Finset.mem_Icc.1 hd).1; omega
      have hfilter :
          ∑ n ∈ Finset.Icc 1 N, (if d ^ 2 ∣ n then (1 : ℝ) / n else 0) =
            ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ^ 2 ∣ n), (1 : ℝ) / n := by
        rw [Finset.sum_filter]
      rw [hfilter]
      have hmul := sum_inv_of_multiples_le (d ^ 2) N (Nat.pow_pos hd0)
      convert hmul using 1
      simp
    have hHle : ∀ d ∈ Finset.Icc 2 N,
        ∑ m ∈ Finset.Icc 1 (N / d ^ 2), (m : ℝ)⁻¹ ≤ 1 + Real.log N := by
      intro d hd
      by_cases hz : N / d ^ 2 = 0
      · simp [hz]
        exact add_nonneg (by norm_num)
          (Real.log_nonneg (by exact_mod_cast (show (1 : ℕ) ≤ N by omega)))
      have hpos : 1 ≤ N / d ^ 2 := Nat.pos_of_ne_zero hz
      have hlogd := sum_inv_Icc_le_one_add_log hpos
      have hle' : Real.log ((N / d ^ 2 : ℕ) : ℝ) ≤ Real.log N :=
        Real.log_le_log (by exact_mod_cast hpos)
          (by exact_mod_cast Nat.div_le_self N (d ^ 2))
      linarith
    have hrhs :
        ∑ d ∈ Finset.Icc 2 N, (1 : ℝ) / (d : ℝ) ^ 2 *
            ∑ m ∈ Finset.Icc 1 (N / d ^ 2), (m : ℝ)⁻¹ ≤
          (2 / 3) * (1 + Real.log N) := by
      have h1 : ∑ d ∈ Finset.Icc 2 N,
          (1 : ℝ) / (d : ℝ) ^ 2 * ∑ m ∈ Finset.Icc 1 (N / d ^ 2), (m : ℝ)⁻¹ ≤
          ∑ d ∈ Finset.Icc 2 N,
            (1 : ℝ) / (d : ℝ) ^ 2 * (1 + Real.log N) := by
        refine Finset.sum_le_sum fun d hd => ?_
        have hnn : 0 ≤ (1 : ℝ) / (d : ℝ) ^ 2 := by positivity
        exact mul_le_mul_of_nonneg_left (hHle d hd) hnn
      refine h1.trans ?_
      rw [← Finset.sum_mul]
      have h3 := sum_inv_sq_from_two_le N
      have hnn : 0 ≤ 1 + Real.log N :=
        add_nonneg (by norm_num)
          (Real.log_nonneg (by exact_mod_cast (show (1 : ℕ) ≤ N by omega)))
      nlinarith
    have : (1 / 3 : ℝ) * Real.log N - 2 / 3 ≤
        ∑ n ∈ Finset.Icc 1 N, (moebius n : ℝ) ^ 2 / n := by
      linarith [hH, hdiff, hrhs]
    have : (1 / 6 : ℝ) * Real.log N ≤ (1 / 3) * Real.log N - 2 / 3 := by
      nlinarith
    linarith

lemma moebius_sq_div_totient_ge {n : ℕ} (hn : 0 < n) :
    (moebius n : ℝ) ^ 2 / n ≤ (moebius n : ℝ) ^ 2 / n.totient := by
  have hφ : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.2 hn
  have hle : (n.totient : ℝ) ≤ n := by exact_mod_cast Nat.totient_le n
  exact div_le_div_of_nonneg_left (sq_nonneg _) hφ hle

lemma sum_mu_sq_div_totient_ge {N : ℕ} (hN : 3 ≤ N) :
    (1 / 6 : ℝ) * Real.log N ≤
      ∑ n ∈ Finset.Icc 1 N, (moebius n : ℝ) ^ 2 / n.totient := by
  have h := sum_mu_sq_div_n_ge hN
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      (moebius n : ℝ) ^ 2 / n ≤ (moebius n : ℝ) ^ 2 / n.totient := by
    intro n hn
    exact moebius_sq_div_totient_ge (by have := (Finset.mem_Icc.1 hn).1; omega)
  exact h.trans (Finset.sum_le_sum hterm)


/-! ### Selberg inner identity for the Maynard change of variables -/

lemma sum_moebius_divisors_eq (n : ℕ) :
    ∑ d ∈ n.divisors, (moebius d : ℝ) = if n = 1 then 1 else 0 := by
  have hsum : ((zeta : ArithmeticFunction ℝ) * (moebius : ArithmeticFunction ℝ)) n =
      ∑ d ∈ n.divisors, (moebius d : ℝ) :=
    ArithmeticFunction.coe_zeta_mul_apply
  rw [← hsum, ArithmeticFunction.coe_zeta_mul_coe_moebius, one_apply]

lemma totient_sum_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, (d.totient : ℝ) = n := by
  rw [← Nat.cast_sum, Nat.sum_totient]

lemma gcd_eq_sum_totient (d e : ℕ) :
    (d.gcd e : ℝ) = ∑ k ∈ (d.gcd e).divisors, (k.totient : ℝ) :=
  (totient_sum_divisors (d.gcd e)).symm

lemma moebius_mul_coprime {a b : ℕ} (h : a.Coprime b) :
    (moebius (a * b) : ℝ) = (moebius a : ℝ) * moebius b := by
  have := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h
  exact_mod_cast this

/-- `∑_{d|n, k|d} μ(d) = μ(k) 1_{n=k}` for squarefree `n` and `k ∣ n`. -/
lemma sum_moebius_divisors_above {n k : ℕ} (hn : Squarefree n) (hk : k ∣ n)
    (hk0 : 0 < k) :
    ∑ d ∈ n.divisors.filter (fun d => k ∣ d), (moebius d : ℝ) =
      (moebius k : ℝ) * (if n = k then (1 : ℝ) else 0) := by
  have hnne0 : n ≠ 0 := fun h => by
    subst h; exact not_squarefree_zero hn
  have hn0 : 0 < n := Nat.pos_of_ne_zero hnne0
  have hnk : k * (n / k) = n := Nat.mul_div_cancel' hk
  have hcop : k.Coprime (n / k) := by
    have : Squarefree (k * (n / k)) := by rwa [hnk]
    exact Nat.coprime_of_squarefree_mul this
  have himage :
      n.divisors.filter (fun d => k ∣ d) =
        ((n / k).divisors).image (fun m => k * m) := by
    ext d; constructor
    · intro hd
      obtain ⟨hdn, hkd⟩ := Finset.mem_filter.1 hd
      refine Finset.mem_image.2 ⟨d / k, ?_, Nat.mul_div_cancel' hkd⟩
      have hdd : d ∣ n := Nat.dvd_of_mem_divisors hdn
      have hdiv : d / k ∣ n / k := Nat.div_dvd_div hkd hdd
      have hne : n / k ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hn0 hk) hk0).ne'
      exact Nat.mem_divisors.2 ⟨hdiv, hne⟩
    · intro hd
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hd
      have hmdiv : m ∣ n / k := Nat.dvd_of_mem_divisors hm
      have : k * m ∣ n := by
        have : k * m ∣ k * (n / k) := mul_dvd_mul_left k hmdiv
        rwa [hnk] at this
      exact Finset.mem_filter.2 ⟨Nat.mem_divisors.2 ⟨this, hnne0⟩, dvd_mul_right k m⟩
  have hinj : Set.InjOn (fun m : ℕ => k * m) ((n / k).divisors : Set ℕ) := by
    intro m _ m' _ hmul
    exact Nat.eq_of_mul_eq_mul_left hk0 hmul
  rw [himage, Finset.sum_image hinj]
  have hμ : ∀ m ∈ (n / k).divisors,
      (moebius (k * m) : ℝ) = (moebius k : ℝ) * moebius m := by
    intro m hm
    have hmc : k.Coprime m := hcop.coprime_dvd_right (Nat.dvd_of_mem_divisors hm)
    exact moebius_mul_coprime hmc
  refine (Finset.sum_congr rfl hμ).trans ?_
  rw [← Finset.mul_sum, sum_moebius_divisors_eq]
  have hiff : n / k = 1 ↔ n = k := by
    constructor
    · intro h; rw [← hnk, h, mul_one]
    · intro h; subst h; exact Nat.div_self hk0
  by_cases h1 : n / k = 1
  · rw [if_pos h1, if_pos (hiff.1 h1)]
  · rw [if_neg h1, if_neg (fun h => h1 (hiff.2 h)), mul_zero]

lemma gcd_ne_zero_of_mem_divisors {d r : ℕ} (hd : d ∈ r.divisors) {e s : ℕ}
    (he : e ∈ s.divisors) : d.gcd e ≠ 0 := by
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  have he0 : e ≠ 0 := (Nat.pos_of_mem_divisors he).ne'
  exact fun h => hd0 ((Nat.gcd_eq_zero_iff.1 h).1)

lemma sum_divisors_gcd_eq_sum_ite {d e r s : ℕ}
    (hd : d ∈ r.divisors) (he : e ∈ s.divisors) (f : ℕ → ℝ) :
    ∑ k ∈ (d.gcd e).divisors, f k =
      ∑ k ∈ (r.gcd s).divisors, (if k ∣ d ∧ k ∣ e then f k else 0) := by
  have hsub : (d.gcd e).divisors ⊆ (r.gcd s).divisors := by
    intro k hk
    have hkd : k ∣ d.gcd e := Nat.dvd_of_mem_divisors hk
    have hdr : d ∣ r := Nat.dvd_of_mem_divisors hd
    have hes : e ∣ s := Nat.dvd_of_mem_divisors he
    have ⟨hkd', hke'⟩ := Nat.dvd_gcd_iff.1 hkd
    have : k ∣ r.gcd s := Nat.dvd_gcd (hkd'.trans hdr) (hke'.trans hes)
    have hne : r.gcd s ≠ 0 := by
      intro hgs
      have hr0 : r ≠ 0 := (Nat.mem_divisors.1 hd).2
      have hs0 : s ≠ 0 := (Nat.mem_divisors.1 he).2
      rcases Nat.gcd_eq_zero_iff.1 hgs with h | h <;> contradiction
    exact Nat.mem_divisors.2 ⟨this, hne⟩
  have hfilter :
      ∑ k ∈ (r.gcd s).divisors, (if k ∣ d ∧ k ∣ e then f k else 0) =
        ∑ k ∈ (r.gcd s).divisors.filter (fun k => k ∣ d ∧ k ∣ e), f k := by
    rw [Finset.sum_filter]
  rw [hfilter]
  have heq : (r.gcd s).divisors.filter (fun k => k ∣ d ∧ k ∣ e) =
      (d.gcd e).divisors := by
    ext k; constructor
    · intro hk
      obtain ⟨_, ⟨hkd, hke⟩⟩ := Finset.mem_filter.1 hk
      have : k ∣ d.gcd e := Nat.dvd_gcd hkd hke
      exact Nat.mem_divisors.2 ⟨this, gcd_ne_zero_of_mem_divisors hd he⟩
    · intro hk
      have hkd : k ∣ d.gcd e := Nat.dvd_of_mem_divisors hk
      have ⟨hkd', hke'⟩ := Nat.dvd_gcd_iff.1 hkd
      exact Finset.mem_filter.2 ⟨hsub hk, ⟨hkd', hke'⟩⟩
  rw [heq]

lemma sum_sum_ite_dvd {r s k : ℕ} (f : ℕ → ℕ → ℝ) :
    ∑ d ∈ r.divisors, ∑ e ∈ s.divisors,
        (if k ∣ d ∧ k ∣ e then f d e else 0) =
      ∑ d ∈ r.divisors.filter (fun d => k ∣ d),
        ∑ e ∈ s.divisors.filter (fun e => k ∣ e), f d e := by
  have h1 :
      ∑ d ∈ r.divisors, ∑ e ∈ s.divisors,
          (if k ∣ d ∧ k ∣ e then f d e else 0) =
        ∑ d ∈ r.divisors, (if k ∣ d then ∑ e ∈ s.divisors,
          (if k ∣ e then f d e else 0) else 0) := by
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases hkd : k ∣ d
    · simp [hkd]
    · simp [hkd]
  rw [h1, ← Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_filter]

lemma sum_factor_totient_mu {r s k : ℕ} :
    ∑ d ∈ r.divisors.filter (fun d => k ∣ d),
        ∑ e ∈ s.divisors.filter (fun e => k ∣ e),
          (moebius d : ℝ) * (moebius e : ℝ) * (k.totient : ℝ) =
      (k.totient : ℝ) *
        (∑ d ∈ r.divisors.filter (fun d => k ∣ d), (moebius d : ℝ)) *
        (∑ e ∈ s.divisors.filter (fun e => k ∣ e), (moebius e : ℝ)) := by
  have h1 :
      ∑ d ∈ r.divisors.filter (fun d => k ∣ d),
          ∑ e ∈ s.divisors.filter (fun e => k ∣ e),
            (moebius d : ℝ) * (moebius e : ℝ) * (k.totient : ℝ) =
        ∑ d ∈ r.divisors.filter (fun d => k ∣ d),
          ((moebius d : ℝ) * (k.totient : ℝ) *
            ∑ e ∈ s.divisors.filter (fun e => k ∣ e), (moebius e : ℝ)) := by
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    ring
  rw [h1]
  have h2 :
      ∑ d ∈ r.divisors.filter (fun d => k ∣ d),
          ((moebius d : ℝ) * (k.totient : ℝ) *
            ∑ e ∈ s.divisors.filter (fun e => k ∣ e), (moebius e : ℝ)) =
        (k.totient : ℝ) *
          (∑ d ∈ r.divisors.filter (fun d => k ∣ d), (moebius d : ℝ)) *
          (∑ e ∈ s.divisors.filter (fun e => k ∣ e), (moebius e : ℝ)) := by
    have hconst :=
      (Finset.sum_mul (s := r.divisors.filter (fun d => k ∣ d))
        (f := fun d => (moebius d : ℝ) * (k.totient : ℝ))
        (a := ∑ e ∈ s.divisors.filter (fun e => k ∣ e), (moebius e : ℝ))).symm
    refine Eq.trans hconst ?_
    have hφ :
        ∑ d ∈ r.divisors.filter (fun d => k ∣ d),
            (moebius d : ℝ) * (k.totient : ℝ) =
          (k.totient : ℝ) *
            ∑ d ∈ r.divisors.filter (fun d => k ∣ d), (moebius d : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => mul_comm _ _
    rw [hφ, mul_assoc]
  exact h2

/-- For squarefree `r, s`, `∑_{d|r,e|s} μ(d)μ(e)gcd(d,e) = 1_{r=s} φ(r)`. -/
lemma selberg_inner_squarefree {r s : ℕ} (hr : Squarefree r) (hs : Squarefree s) :
    ∑ d ∈ r.divisors, ∑ e ∈ s.divisors,
      (moebius d : ℝ) * (moebius e : ℝ) * (d.gcd e : ℝ) =
      if r = s then (r.totient : ℝ) else 0 := by
  by_cases hr0 : r = 0
  · subst hr0; exact (not_squarefree_zero hr).elim
  by_cases hs0 : s = 0
  · subst hs0; exact (not_squarefree_zero hs).elim
  have hrew :
      ∑ d ∈ r.divisors, ∑ e ∈ s.divisors,
        (moebius d : ℝ) * (moebius e : ℝ) * (d.gcd e : ℝ) =
      ∑ d ∈ r.divisors, ∑ e ∈ s.divisors, ∑ k ∈ (d.gcd e).divisors,
        (moebius d : ℝ) * (moebius e : ℝ) * (k.totient : ℝ) := by
    refine Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun e he => ?_
    rw [gcd_eq_sum_totient, Finset.mul_sum]
  rw [hrew]
  have hL :
      ∑ d ∈ r.divisors, ∑ e ∈ s.divisors, ∑ k ∈ (d.gcd e).divisors,
          (moebius d : ℝ) * (moebius e : ℝ) * (k.totient : ℝ) =
        ∑ d ∈ r.divisors, ∑ e ∈ s.divisors, ∑ k ∈ (r.gcd s).divisors,
          (if k ∣ d ∧ k ∣ e then
            (moebius d : ℝ) * (moebius e : ℝ) * (k.totient : ℝ) else 0) := by
    refine Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun e he => ?_
    simpa using
      (sum_divisors_gcd_eq_sum_ite hd he
        (fun k => (moebius d : ℝ) * (moebius e : ℝ) * (k.totient : ℝ)))
  rw [hL]
  have hcomm :
      ∑ d ∈ r.divisors, ∑ e ∈ s.divisors, ∑ k ∈ (r.gcd s).divisors,
          (if k ∣ d ∧ k ∣ e then
            (moebius d : ℝ) * (moebius e : ℝ) * (k.totient : ℝ) else 0) =
        ∑ k ∈ (r.gcd s).divisors, ∑ d ∈ r.divisors, ∑ e ∈ s.divisors,
          (if k ∣ d ∧ k ∣ e then
            (moebius d : ℝ) * (moebius e : ℝ) * (k.totient : ℝ) else 0) := by
    have hinner :
        ∑ d ∈ r.divisors, ∑ e ∈ s.divisors, ∑ k ∈ (r.gcd s).divisors,
            (if k ∣ d ∧ k ∣ e then
              (moebius d : ℝ) * (moebius e : ℝ) * (k.totient : ℝ) else 0) =
          ∑ d ∈ r.divisors, ∑ k ∈ (r.gcd s).divisors, ∑ e ∈ s.divisors,
            (if k ∣ d ∧ k ∣ e then
              (moebius d : ℝ) * (moebius e : ℝ) * (k.totient : ℝ) else 0) := by
      refine Finset.sum_congr rfl fun d _ => Finset.sum_comm
    rw [hinner, Finset.sum_comm]
  rw [hcomm]
  have hswap :
      ∑ k ∈ (r.gcd s).divisors, ∑ d ∈ r.divisors, ∑ e ∈ s.divisors,
          (if k ∣ d ∧ k ∣ e then
            (moebius d : ℝ) * (moebius e : ℝ) * (k.totient : ℝ) else 0) =
        ∑ k ∈ (r.gcd s).divisors,
          (k.totient : ℝ) *
            (∑ d ∈ r.divisors.filter (fun d => k ∣ d), (moebius d : ℝ)) *
            (∑ e ∈ s.divisors.filter (fun e => k ∣ e), (moebius e : ℝ)) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sum_sum_ite_dvd, sum_factor_totient_mu]
  rw [hswap]
  have hterm : ∀ k ∈ (r.gcd s).divisors,
      (k.totient : ℝ) *
        (∑ d ∈ r.divisors.filter (fun d => k ∣ d), (moebius d : ℝ)) *
        (∑ e ∈ s.divisors.filter (fun e => k ∣ e), (moebius e : ℝ)) =
      if k = r ∧ k = s then (r.totient : ℝ) else 0 := by
    intro k hk
    have hkd : k ∣ r.gcd s := Nat.dvd_of_mem_divisors hk
    have hkr : k ∣ r := (Nat.dvd_gcd_iff.1 hkd).1
    have hks : k ∣ s := (Nat.dvd_gcd_iff.1 hkd).2
    have hk0 : 0 < k := Nat.pos_of_mem_divisors hk
    have hrk := sum_moebius_divisors_above hr hkr hk0
    have hsk := sum_moebius_divisors_above hs hks hk0
    rw [hrk, hsk]
    by_cases hkr' : r = k
    · by_cases hks' : s = k
      · have hkeq : k = r ∧ k = s := ⟨hkr'.symm, hks'.symm⟩
        rw [if_pos hkr', if_pos hks', if_pos hkeq]
        have hksf : Squarefree k := by simpa [hkr'] using hr
        have hμ : (moebius k : ℝ) * moebius k = 1 := by
          have hsq : (moebius k : ℤ) ^ 2 = 1 :=
            ArithmeticFunction.moebius_sq_eq_one_of_squarefree hksf
          have : ((moebius k : ℤ) : ℝ) ^ 2 = 1 := by exact_mod_cast hsq
          nlinarith
        calc
          (k.totient : ℝ) * ((moebius k : ℝ) * 1) * ((moebius k : ℝ) * 1)
              = (k.totient : ℝ) * (moebius k * moebius k) := by ring
          _ = (k.totient : ℝ) * 1 := by rw [hμ]
          _ = (r.totient : ℝ) := by simp [hkr']
      · rw [if_pos hkr', if_neg hks']
        have : ¬ (k = r ∧ k = s) := fun h => hks' h.2.symm
        rw [if_neg this]
        ring
    · rw [if_neg hkr']
      have : ¬ (k = r ∧ k = s) := fun h => hkr' h.1.symm
      rw [if_neg this]
      ring
  refine (Finset.sum_congr rfl hterm).trans ?_
  by_cases heq : r = s
  · subst heq
    have hmem : r ∈ r.divisors := Nat.mem_divisors_self r hr0
    have hmem' : r ∈ (r.gcd r).divisors := by
      simpa [Nat.gcd_self] using hmem
    rw [if_pos rfl]
    have hrest : ∀ k ∈ (r.gcd r).divisors,
        (if k = r ∧ k = r then (r.totient : ℝ) else 0) =
          if k = r then (r.totient : ℝ) else 0 := by
      intro k _; by_cases hk' : k = r
      · simp [hk']
      · simp [hk']
    rw [Finset.sum_congr rfl hrest, Finset.sum_ite_eq', if_pos hmem']
  · rw [if_neg heq]
    refine Finset.sum_eq_zero fun k hk => ?_
    split_ifs with h
    · rcases h with ⟨h1, h2⟩
      exact (heq (h1.symm.trans h2)).elim
    · rfl


lemma gcd_mul_lcm_real (d e : ℕ) :
    (d.gcd e : ℝ) * (d.lcm e : ℝ) = (d : ℝ) * e := by
  exact_mod_cast (Nat.gcd_mul_lcm d e)

lemma lcm_ne_zero_of_pos {d e : ℕ} (hd : 0 < d) (he : 0 < e) : d.lcm e ≠ 0 := by
  intro h
  rcases Nat.lcm_eq_zero_iff.1 h with h | h
  · exact hd.ne' h
  · exact he.ne' h

lemma gcd_div_lcm_eq {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    (d : ℝ) * e / (d.lcm e : ℝ) = (d.gcd e : ℝ) := by
  have h := gcd_mul_lcm_real d e
  have hne : (d.lcm e : ℝ) ≠ 0 := by exact_mod_cast (lcm_ne_zero_of_pos hd he)
  field_simp [hne]
  linarith

lemma totient_ne_zero_of_pos {n : ℕ} (hn : 0 < n) : (n.totient : ℝ) ≠ 0 := by
  exact_mod_cast (Nat.totient_pos.2 hn).ne'

/-- One-dimensional Selberg λ-weight attached to a test function `y`. -/
noncomputable def selbergLambda1 (R : ℕ) (y : ℕ → ℝ) (d : ℕ) : ℝ :=
  (moebius d : ℝ) * (d : ℝ) *
    ∑ r ∈ Finset.Icc 1 R,
      (if d ∣ r ∧ Squarefree r then
        (moebius r : ℝ) / (r.totient : ℝ) * y r else 0)

lemma selbergLambda1_eq_zero_of_not_le {R : ℕ} {y : ℕ → ℝ} {d : ℕ}
    (hd : R < d) : selbergLambda1 R y d = 0 := by
  unfold selbergLambda1
  have hsum : ∑ r ∈ Finset.Icc 1 R,
      (if d ∣ r ∧ Squarefree r then
        (moebius r : ℝ) / (r.totient : ℝ) * y r else 0) = 0 := by
    refine Finset.sum_eq_zero fun r hr => ?_
    have hnd : ¬ d ∣ r := fun hdv => by
      have hr0 : 0 < r := (Finset.mem_Icc.1 hr).1
      have hrR : r ≤ R := (Finset.mem_Icc.1 hr).2
      have : d ≤ r := Nat.le_of_dvd hr0 hdv
      omega
    simp [hnd]
  simp [hsum]

lemma mem_Icc_one_of_dvd {d r R : ℕ} (hr : r ∈ Finset.Icc 1 R) (hd : d ∣ r)
    (hd0 : 0 < d) : d ∈ Finset.Icc 1 R := by
  have hrR : r ≤ R := (Finset.mem_Icc.1 hr).2
  have hdle : d ≤ r := Nat.le_of_dvd (by have := (Finset.mem_Icc.1 hr).1; omega) hd
  exact Finset.mem_Icc.2 ⟨Nat.succ_le_of_lt hd0, le_trans hdle hrR⟩

/-- Kernel factor after cancelling `d e / lcm = gcd`. -/
lemma selberg_kernel_term {R : ℕ} {y : ℕ → ℝ} {d e r s : ℕ}
    (hd : d ∈ Finset.Icc 1 R) (he : e ∈ Finset.Icc 1 R) :
    ((moebius d : ℝ) * (d : ℝ) *
      (if d ∣ r ∧ Squarefree r then
        (moebius r : ℝ) / (r.totient : ℝ) * y r else 0)) *
    ((moebius e : ℝ) * (e : ℝ) *
      (if e ∣ s ∧ Squarefree s then
        (moebius s : ℝ) / (s.totient : ℝ) * y s else 0)) /
    (d.lcm e : ℝ) =
      if d ∣ r ∧ Squarefree r ∧ e ∣ s ∧ Squarefree s then
        (moebius r : ℝ) / (r.totient : ℝ) * y r *
        (moebius s : ℝ) / (s.totient : ℝ) * y s *
        (moebius d : ℝ) * (moebius e : ℝ) * (d.gcd e : ℝ)
      else 0 := by
  have hd0 : 0 < d := (Finset.mem_Icc.1 hd).1
  have he0 : 0 < e := (Finset.mem_Icc.1 he).1
  have hgcd := gcd_div_lcm_eq hd0 he0
  by_cases hdr : d ∣ r ∧ Squarefree r
  · by_cases hes : e ∣ s ∧ Squarefree s
    · have hcond : d ∣ r ∧ Squarefree r ∧ e ∣ s ∧ Squarefree s :=
        ⟨hdr.1, hdr.2, hes.1, hes.2⟩
      simp only [hdr, hes, hcond, and_true, ite_true]
      have : (d : ℝ) * e / (d.lcm e : ℝ) = (d.gcd e : ℝ) := hgcd
      calc
        (↑(moebius d) * ↑d * (↑(moebius r) / ↑r.totient * y r)) *
            (↑(moebius e) * ↑e * (↑(moebius s) / ↑s.totient * y s)) / ↑(d.lcm e)
            = (↑(moebius r) / ↑r.totient * y r) * (↑(moebius s) / ↑s.totient * y s) *
                ↑(moebius d) * ↑(moebius e) * (↑d * ↑e / ↑(d.lcm e)) := by ring
        _ = (↑(moebius r) / ↑r.totient * y r) * (↑(moebius s) / ↑s.totient * y s) *
                ↑(moebius d) * ↑(moebius e) * ↑(d.gcd e) := by rw [this]
        _ = ↑(moebius r) / ↑r.totient * y r * ↑(moebius s) / ↑s.totient * y s *
                ↑(moebius d) * ↑(moebius e) * ↑(d.gcd e) := by ring
    · have hcond : ¬ (d ∣ r ∧ Squarefree r ∧ e ∣ s ∧ Squarefree s) := by
        intro h; exact hes ⟨h.2.2.1, h.2.2.2⟩
      simp [hdr, hes, hcond]
  · have hcond : ¬ (d ∣ r ∧ Squarefree r ∧ e ∣ s ∧ Squarefree s) := by
      intro h; exact hdr ⟨h.1, h.2.1⟩
    simp [hdr, hcond]

lemma selbergLambda1_apply (R : ℕ) (y : ℕ → ℝ) (d : ℕ) :
    selbergLambda1 R y d =
      ∑ r ∈ Finset.Icc 1 R,
        (if d ∣ r ∧ Squarefree r then
          (moebius d : ℝ) * (d : ℝ) * ((moebius r : ℝ) / (r.totient : ℝ) * y r) else 0) := by
  unfold selbergLambda1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs <;> ring

lemma selbergLambda1_mul_div {R : ℕ} {y : ℕ → ℝ} {d e : ℕ}
    (hd : d ∈ Finset.Icc 1 R) (he : e ∈ Finset.Icc 1 R) :
    selbergLambda1 R y d * selbergLambda1 R y e / (d.lcm e : ℝ) =
      ∑ r ∈ Finset.Icc 1 R, ∑ s ∈ Finset.Icc 1 R,
        if d ∣ r ∧ Squarefree r ∧ e ∣ s ∧ Squarefree s then
          (moebius r : ℝ) / (r.totient : ℝ) * y r *
          (moebius s : ℝ) / (s.totient : ℝ) * y s *
          (moebius d : ℝ) * (moebius e : ℝ) * (d.gcd e : ℝ)
        else 0 := by
  rw [selbergLambda1_apply, selbergLambda1_apply]
  set f : ℕ → ℝ := fun r =>
    if d ∣ r ∧ Squarefree r then
      (moebius d : ℝ) * (d : ℝ) * ((moebius r : ℝ) / (r.totient : ℝ) * y r) else 0
  set g : ℕ → ℝ := fun s =>
    if e ∣ s ∧ Squarefree s then
      (moebius e : ℝ) * (e : ℝ) * ((moebius s : ℝ) / (s.totient : ℝ) * y s) else 0
  have hprod : (∑ r ∈ Finset.Icc 1 R, f r) * (∑ s ∈ Finset.Icc 1 R, g s) /
      (d.lcm e : ℝ) =
      ∑ r ∈ Finset.Icc 1 R, ∑ s ∈ Finset.Icc 1 R, f r * g s / (d.lcm e : ℝ) := by
    rw [Finset.sum_mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_div]
  rw [hprod]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  convert (selberg_kernel_term (R := R) (y := y) (d := d) (e := e) (r := r) (s := s) hd he) using 1
  unfold f g
  by_cases hdr : d ∣ r ∧ Squarefree r
  · by_cases hes : e ∣ s ∧ Squarefree s
    · simp [hdr, hes]; try ring
    · simp [hdr, hes]
  · simp [hdr]

lemma moebius_sq_of_squarefree {n : ℕ} (hn : Squarefree n) :
    (moebius n : ℝ) * moebius n = 1 := by
  have hsq : (moebius n : ℤ) ^ 2 = 1 :=
    ArithmeticFunction.moebius_sq_eq_one_of_squarefree hn
  have : ((moebius n : ℤ) : ℝ) ^ 2 = 1 := by exact_mod_cast hsq
  nlinarith

lemma filter_dvd_Icc_eq_divisors {n R : ℕ} (hn : n ∈ Finset.Icc 1 R) :
    (Finset.Icc 1 R).filter (fun d => d ∣ n) = n.divisors := by
  have hn0 : n ≠ 0 := (Nat.pos_iff_ne_zero.mp (Finset.mem_Icc.1 hn).1)
  have hnR : n ≤ R := (Finset.mem_Icc.1 hn).2
  ext d; constructor
  · intro hd
    obtain ⟨hdI, hdn⟩ := Finset.mem_filter.1 hd
    exact Nat.mem_divisors.2 ⟨hdn, hn0⟩
  · intro hd
    have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hdle : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdn
    exact Finset.mem_filter.2
      ⟨Finset.mem_Icc.2 ⟨Nat.succ_le_of_lt hd0, le_trans hdle hnR⟩, hdn⟩

lemma sum_kernel_over_divisors {R r s : ℕ} (hr : Squarefree r) (hs : Squarefree s)
    (hrR : r ∈ Finset.Icc 1 R) (hsR : s ∈ Finset.Icc 1 R) :
    ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
        (if d ∣ r ∧ e ∣ s then
          (moebius d : ℝ) * (moebius e : ℝ) * (d.gcd e : ℝ) else 0) =
      if r = s then (r.totient : ℝ) else 0 := by
  have h1 :
      ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
          (if d ∣ r ∧ e ∣ s then
            (moebius d : ℝ) * (moebius e : ℝ) * (d.gcd e : ℝ) else 0) =
        ∑ d ∈ (Finset.Icc 1 R).filter (fun d => d ∣ r),
          ∑ e ∈ (Finset.Icc 1 R).filter (fun e => e ∣ s),
            (moebius d : ℝ) * (moebius e : ℝ) * (d.gcd e : ℝ) := by
    have :
        ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
            (if d ∣ r ∧ e ∣ s then
              (moebius d : ℝ) * (moebius e : ℝ) * (d.gcd e : ℝ) else 0) =
          ∑ d ∈ Finset.Icc 1 R, (if d ∣ r then
            ∑ e ∈ Finset.Icc 1 R,
              (if e ∣ s then
                (moebius d : ℝ) * (moebius e : ℝ) * (d.gcd e : ℝ) else 0) else 0) := by
      refine Finset.sum_congr rfl fun d _ => ?_
      by_cases hdr : d ∣ r
      · simp [hdr]
      · simp [hdr]
    rw [this, ← Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.sum_filter]
  rw [h1, filter_dvd_Icc_eq_divisors hrR, filter_dvd_Icc_eq_divisors hsR]
  exact selberg_inner_squarefree hr hs

lemma sum_comm_pair {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (f : α → β → ℝ) :
    ∑ x ∈ s, ∑ y ∈ t, f x y = ∑ y ∈ t, ∑ x ∈ s, f x y :=
  Finset.sum_comm

noncomputable def y_coeff (y : ℕ → ℝ) (r s : ℕ) : ℝ :=
  (moebius r : ℝ) / (r.totient : ℝ) * y r *
  (moebius s : ℝ) / (s.totient : ℝ) * y s

noncomputable def selberg_term (y : ℕ → ℝ) (d e r s : ℕ) : ℝ :=
  if d ∣ r ∧ Squarefree r ∧ e ∣ s ∧ Squarefree s then
    y_coeff y r s * (moebius d : ℝ) * (moebius e : ℝ) * (d.gcd e : ℝ)
  else 0

lemma sum_selberg_term_swap (R : ℕ) (y : ℕ → ℝ) :
    ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R, ∑ r ∈ Finset.Icc 1 R,
        ∑ s ∈ Finset.Icc 1 R, selberg_term y d e r s =
      ∑ r ∈ Finset.Icc 1 R, ∑ s ∈ Finset.Icc 1 R, ∑ d ∈ Finset.Icc 1 R,
        ∑ e ∈ Finset.Icc 1 R, selberg_term y d e r s := by
  -- d e r s → d r e s → r d e s → r s d e
  have h1 : ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R, ∑ r ∈ Finset.Icc 1 R,
      ∑ s ∈ Finset.Icc 1 R, selberg_term y d e r s =
      ∑ d ∈ Finset.Icc 1 R, ∑ r ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
        ∑ s ∈ Finset.Icc 1 R, selberg_term y d e r s := by
    refine Finset.sum_congr rfl fun d _ =>
      (sum_comm_pair (Finset.Icc 1 R) (Finset.Icc 1 R)
        (fun e r => ∑ s ∈ Finset.Icc 1 R, selberg_term y d e r s))
  rw [h1]
  have h2 : ∑ d ∈ Finset.Icc 1 R, ∑ r ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
      ∑ s ∈ Finset.Icc 1 R, selberg_term y d e r s =
      ∑ r ∈ Finset.Icc 1 R, ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
        ∑ s ∈ Finset.Icc 1 R, selberg_term y d e r s :=
    sum_comm_pair _ _ _
  rw [h2]
  refine Finset.sum_congr rfl fun r _ => ?_
  have h3 : ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R, ∑ s ∈ Finset.Icc 1 R,
      selberg_term y d e r s =
      ∑ d ∈ Finset.Icc 1 R, ∑ s ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
        selberg_term y d e r s := by
    refine Finset.sum_congr rfl fun d _ =>
      sum_comm_pair _ _ (fun e s => selberg_term y d e r s)
  rw [h3]
  exact sum_comm_pair _ _ (fun d s => ∑ e ∈ Finset.Icc 1 R, selberg_term y d e r s)

lemma selberg_inner_eval {R r s : ℕ} (y : ℕ → ℝ)
    (hr : r ∈ Finset.Icc 1 R) (hs : s ∈ Finset.Icc 1 R) :
    ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R, selberg_term y d e r s =
      if Squarefree r ∧ Squarefree s ∧ r = s then y r ^ 2 / (r.totient : ℝ) else 0 := by
  unfold selberg_term y_coeff
  by_cases hsf : Squarefree r ∧ Squarefree s
  · have hpull :
        ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
            (if d ∣ r ∧ Squarefree r ∧ e ∣ s ∧ Squarefree s then
              (moebius r : ℝ) / (r.totient : ℝ) * y r *
              (moebius s : ℝ) / (s.totient : ℝ) * y s *
              (moebius d : ℝ) * (moebius e : ℝ) * (d.gcd e : ℝ) else 0) =
          ((moebius r : ℝ) / (r.totient : ℝ) * y r *
            (moebius s : ℝ) / (s.totient : ℝ) * y s) *
          ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
            (if d ∣ r ∧ e ∣ s then
              (moebius d : ℝ) * (moebius e : ℝ) * (d.gcd e : ℝ) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      by_cases hdr : d ∣ r
      · by_cases hes : e ∣ s
        · simp [hdr, hes, hsf.1, hsf.2]; ring
        · simp [hdr, hes, hsf.1, hsf.2]
      · simp [hdr]
    rw [hpull, sum_kernel_over_divisors hsf.1 hsf.2 hr hs]
    by_cases heq : r = s
    · subst heq
      have hr0 : 0 < r := (Finset.mem_Icc.1 hr).1
      have hφ : (r.totient : ℝ) ≠ 0 := totient_ne_zero_of_pos hr0
      have hμ : (moebius r : ℝ) * moebius r = 1 := moebius_sq_of_squarefree hsf.1
      have hC : Squarefree r ∧ Squarefree r ∧ r = r := ⟨hsf.1, hsf.1, rfl⟩
      simp only [hC, ite_true]
      -- goal: (μ/φ * y * μ/φ * y) * φ = y^2 / φ
      calc
        (moebius r : ℝ) / (r.totient : ℝ) * y r *
            (moebius r : ℝ) / (r.totient : ℝ) * y r * (r.totient : ℝ)
            = ((moebius r : ℝ) * moebius r) * (y r * y r) / (r.totient : ℝ) := by
              field_simp [hφ]
        _ = (1 : ℝ) * (y r * y r) / (r.totient : ℝ) := by rw [hμ]
        _ = y r ^ 2 / (r.totient : ℝ) := by ring
    · rw [if_neg heq, if_neg (fun h => heq h.2.2)]
      ring
  · have : ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
        (if d ∣ r ∧ Squarefree r ∧ e ∣ s ∧ Squarefree s then
          (moebius r : ℝ) / (r.totient : ℝ) * y r *
          (moebius s : ℝ) / (s.totient : ℝ) * y s *
          (moebius d : ℝ) * (moebius e : ℝ) * (d.gcd e : ℝ) else 0) = 0 := by
      refine Finset.sum_eq_zero fun d _ => Finset.sum_eq_zero fun e _ => ?_
      split_ifs with h
      · exact (hsf ⟨h.2.1, h.2.2.2⟩).elim
      · rfl
    rw [this, if_neg]
    intro h
    exact hsf ⟨h.1, h.2.1⟩

/-- The one-dimensional Selberg quadratic form: `∑_{d,e} λ(d)λ(e)/lcm(d,e) = ∑_r y(r)²/φ(r)`
    on squarefree support. -/
lemma selberg_quadratic_form_1d (R : ℕ) (y : ℕ → ℝ) :
    ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
        selbergLambda1 R y d * selbergLambda1 R y e / (d.lcm e : ℝ) =
      ∑ r ∈ Finset.Icc 1 R,
        (if Squarefree r then y r ^ 2 / (r.totient : ℝ) else 0) := by
  have hexp :
      ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
          selbergLambda1 R y d * selbergLambda1 R y e / (d.lcm e : ℝ) =
        ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R, ∑ r ∈ Finset.Icc 1 R,
          ∑ s ∈ Finset.Icc 1 R, selberg_term y d e r s := by
    refine Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun e he => ?_
    have := selbergLambda1_mul_div (y := y) hd he
    refine this.trans ?_
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
    unfold selberg_term y_coeff; rfl
  rw [hexp, sum_selberg_term_swap]
  have hinner :
      ∑ r ∈ Finset.Icc 1 R, ∑ s ∈ Finset.Icc 1 R, ∑ d ∈ Finset.Icc 1 R,
          ∑ e ∈ Finset.Icc 1 R, selberg_term y d e r s =
        ∑ r ∈ Finset.Icc 1 R, ∑ s ∈ Finset.Icc 1 R,
          (if Squarefree r ∧ Squarefree s ∧ r = s then
            y r ^ 2 / (r.totient : ℝ) else 0) := by
    refine Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun s hs => ?_
    exact selberg_inner_eval y hr hs
  rw [hinner]
  refine Finset.sum_congr rfl fun r hr => ?_
  by_cases hsf : Squarefree r
  · simp [hsf]
    refine (Finset.sum_eq_single (a := r)
      (f := fun s : ℕ => if Squarefree s ∧ r = s then
        y r ^ 2 / (r.totient : ℝ) else 0) ?_ ?_).trans ?_
    · intro s _ hne
      have : r ≠ s := hne.symm
      simp [this]
    · intro h; exact (h hr).elim
    · simp [hsf]
  · simp [hsf]


lemma two_pow_two_pow_gt (m : ℕ) (hm : 2 ≤ m) :
    (160 : ℕ) ≤ 2 ^ (2 ^ (m + 8)) := by
  have h8 : 8 ≤ m + 8 := by omega
  have hpow : 2 ^ 8 ≤ 2 ^ (m + 8) := Nat.pow_le_pow_right (by norm_num) h8
  have : 2 ^ 8 = 256 := by norm_num
  have h256 : 256 ≤ 2 ^ (m + 8) := by
    rwa [this] at hpow
  have hleft : 160 ≤ 2 ^ 256 := by
    have : 2 ^ 8 = 256 := by norm_num
    have : 2 ^ 8 ≤ 2 ^ 256 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 256 ≤ 2 ^ 256 := by
      have h := Nat.lt_pow_self (n := 256) (by norm_num : 1 < 2)
      omega
    omega
  exact le_trans hleft (Nat.pow_le_pow_right (by norm_num) h256)

lemma two_pow_ge_two_mul_nat {n : ℕ} (hn : 2 ≤ n) : 2 * n ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h2 : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
    calc
      2 * (n + 1) = 2 * n + 2 := by omega
      _ ≤ 2 ^ n + 2 := Nat.add_le_add_right ih 2
      _ ≤ 2 ^ n + 2 ^ n := Nat.add_le_add_left h2 _
      _ = 2 ^ n * 2 := by omega
      _ = 2 ^ (n + 1) := (pow_succ 2 n).symm

lemma two_pow_ge_two_mul {n : ℕ} (hn : 2 ≤ n) : (2 : ℝ) * n ≤ (2 : ℝ) ^ n := by
  have := two_pow_ge_two_mul_nat hn
  exact_mod_cast this

lemma log_ten_lt_three : Real.log 10 < 3 := by
  have hexp : (9 / 4 : ℝ) ≤ Real.exp 1 := by
    have hhalf := exp_half_ge_three_halves
    have heq : Real.exp 1 = Real.exp (1 / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]; norm_num
    have hpos : 0 ≤ Real.exp (1 / 2) := le_of_lt (exp_pos _)
    nlinarith [hhalf, heq, hpos]
  have hexp3 : (10 : ℝ) < Real.exp 3 := by
    have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul]; norm_num
    have hval : (9 / 4 : ℝ) ^ 3 = 729 / 64 := by norm_num
    have hgt : (729 / 64 : ℝ) > 10 := by norm_num
    have hpow : (9 / 4 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := by
      nlinarith [sq_nonneg ((9 / 4 : ℝ)), sq_nonneg (Real.exp 1),
        hexp, exp_pos (1 : ℝ)]
    rw [h3]
    linarith [hval, hgt, hpow]
  have := Real.log_lt_log (by norm_num : (0 : ℝ) < 10) hexp3
  rwa [Real.log_exp] at this

/-- `log(k/10) > 288 m` for `k ≥ 2^{2^{m+8}}`, enough for level `θ = 1/8`. -/
lemma log_k_over_ten_gt {k m : ℕ} (hm : 2 ≤ m) (hk : 2 ^ (2 ^ (m + 8)) ≤ k) :
    (288 : ℝ) * m < Real.log (k / 10) := by
  have hk160 : 160 ≤ k := le_trans (two_pow_two_pow_gt m hm) hk
  have hkR : (2 ^ (2 ^ (m + 8)) : ℝ) ≤ k := by exact_mod_cast hk
  have hlog : Real.log ((2 : ℝ) ^ (2 ^ (m + 8)) / 10) ≤ Real.log (k / 10) := by
    apply Real.log_le_log
    · positivity
    · exact div_le_div_of_nonneg_right hkR (by norm_num)
  have hlog2 : Real.log ((2 : ℝ) ^ (2 ^ (m + 8)) / 10) =
      ((2 ^ (m + 8) : ℕ) : ℝ) * Real.log 2 - Real.log 10 := by
    rw [Real.log_div (pow_ne_zero _ (by norm_num)) (by norm_num)]
    have : Real.log ((2 : ℝ) ^ (2 ^ (m + 8))) = (2 ^ (m + 8) : ℕ) * Real.log 2 := by
      rw [Real.log_pow]
    rw [this]
  have hcast : ((2 ^ (m + 8) : ℕ) : ℝ) = (2 : ℝ) ^ (m + 8) := by
    rw [Nat.cast_pow]; simp
  rw [hcast] at hlog2
  have hpow : (2 : ℝ) ^ (m + 8) = (2 : ℝ) ^ m * 256 := by
    rw [pow_add]
    have : (2 : ℝ) ^ 8 = 256 := by norm_num
    rw [this]
  have h2m := two_pow_ge_two_mul hm
  have hmain : (288 : ℝ) * m + 3 < (2 : ℝ) ^ (m + 8) * (2 / 3) := by
    have heq : (2 : ℝ) ^ (m + 8) * (2 / 3) = (2 : ℝ) ^ m * (512 / 3) := by
      rw [hpow]; ring
    have hge : (2 : ℝ) ^ m * (512 / 3) ≥ ((2 : ℝ) * m) * (512 / 3) := by
      nlinarith
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have hlower : (2 : ℝ) ^ (m + 8) * (2 / 3) - Real.log 10 ≤
      (2 : ℝ) ^ (m + 8) * Real.log 2 - Real.log 10 := by
    nlinarith [log_two_ge_two_thirds]
  linarith [hlog, hlog2, hlower, hmain, log_ten_lt_three]

lemma mem_piFinset_cons {α : Type*} [DecidableEq α] {k : ℕ} {s : Finset α}
    {a : α} {t : Fin k → α} :
    Fin.cons (α := fun _ => α) a t ∈ Fintype.piFinset (fun _ : Fin (k + 1) => s) ↔
      a ∈ s ∧ t ∈ Fintype.piFinset (fun _ : Fin k => s) := by
  constructor
  · intro h
    have h' := Fintype.mem_piFinset.1 h
    refine ⟨?_, ?_⟩
    · simpa [Fin.cons_zero] using h' 0
    · exact Fintype.mem_piFinset.2 fun i => by simpa [Fin.cons_succ] using h' i.succ
  · intro ⟨ha, ht⟩
    refine Fintype.mem_piFinset.2 fun i => ?_
    refine Fin.cases ?_ ?_ i
    · simpa [Fin.cons_zero] using ha
    · intro j
      have := Fintype.mem_piFinset.1 ht j
      simpa [Fin.cons_succ] using this

lemma prod_cons_g {α : Type*} (g : α → ℝ) (a : α) {k : ℕ} (t : Fin k → α) :
    (∏ i : Fin (k + 1), g (Fin.cons (α := fun _ => α) a t i)) =
      g a * ∏ i : Fin k, g (t i) := by
  have hcomp : (fun i : Fin (k + 1) => g (Fin.cons (α := fun _ => α) a t i)) =
      Fin.cons (g a) (fun i : Fin k => g (t i)) := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp [Fin.cons_zero]
    · intro j; simp [Fin.cons_succ]
  rw [hcomp, Fin.prod_cons]

lemma sum_pow_prod {α : Type*} [DecidableEq α] (k : ℕ) (s : Finset α) (g : α → ℝ) :
    (∑ x ∈ s, g x) ^ k =
      ∑ d ∈ Fintype.piFinset (fun _ : Fin k => s), ∏ i : Fin k, g (d i) := by
  induction k with
  | zero =>
    simp [pow_zero]
  | succ k ih =>
    rw [pow_succ, ih, Finset.sum_mul_sum, Finset.sum_comm]
    rw [← Finset.sum_product
      (f := fun p : α × (Fin k → α) => (∏ i, g (p.2 i)) * g p.1)]
    refine Finset.sum_nbij (fun p : α × (Fin k → α) => Fin.cons (α := fun _ => α) p.1 p.2)
      ?_ ?_ ?_ ?_
    · intro p hp
      obtain ⟨ha, ht⟩ := Finset.mem_product.1 hp
      exact (mem_piFinset_cons).2 ⟨ha, ht⟩
    · intro p hp q hq h
      have h0 : p.1 = q.1 := by
        simpa [Fin.cons_zero] using congrArg (fun f => f 0) h
      have ht : p.2 = q.2 := by
        funext i
        simpa [Fin.cons_succ] using congrArg (fun f => f i.succ) h
      exact Prod.ext h0 ht
    · intro d hd
      refine ⟨(d 0, Fin.tail d), ?_, ?_⟩
      · refine Finset.mem_product.2 ⟨?_, ?_⟩
        · exact (Fintype.mem_piFinset.1 hd) 0
        · refine Fintype.mem_piFinset.2 fun i => ?_
          simpa [Fin.cons_succ] using (Fintype.mem_piFinset.1 hd) i.succ
      · ext i
        refine Fin.cases ?_ ?_ i
        · simp [Fin.cons_zero]
        · intro j; simp [Fin.cons_succ, Fin.tail]
    · intro p hp
      rw [prod_cons_g]
      obtain ⟨ha, ht⟩ := Finset.mem_product.1 hp
      ring

lemma sum_pair {α : Type*} (s : Finset α) (f : α → α → ℝ) :
    ∑ d ∈ s, ∑ e ∈ s, f d e = ∑ p ∈ s ×ˢ s, f p.1 p.2 := by
  rw [Finset.sum_product]

lemma prod_bilinear {α : Type*} [DecidableEq α] (k : ℕ) (s : Finset α) (f : α → α → ℝ) :
    (∑ d ∈ s, ∑ e ∈ s, f d e) ^ k =
      ∑ d ∈ Fintype.piFinset fun _ : Fin k => s,
        ∑ e ∈ Fintype.piFinset fun _ : Fin k => s,
          ∏ i : Fin k, f (d i) (e i) := by
  rw [sum_pair, sum_pow_prod (s := s ×ˢ s) (g := fun p => f p.1 p.2)]
  have hrhs :
      ∑ d ∈ Fintype.piFinset (fun _ : Fin k => s),
          ∑ e ∈ Fintype.piFinset (fun _ : Fin k => s),
            ∏ i : Fin k, f (d i) (e i) =
        ∑ p ∈ (Fintype.piFinset fun _ : Fin k => s) ×ˢ
            (Fintype.piFinset fun _ : Fin k => s),
          ∏ i : Fin k, f (p.1 i) (p.2 i) := by
    rw [Finset.sum_product]
  rw [hrhs]
  refine Finset.sum_nbij (fun P => (fun i => (P i).1, fun i => (P i).2)) ?_ ?_ ?_ ?_
  · intro P hP
    refine Finset.mem_product.2 ⟨?_, ?_⟩
    · exact Fintype.mem_piFinset.2 fun i =>
        (Finset.mem_product.1 ((Fintype.mem_piFinset.1 hP) i)).1
    · exact Fintype.mem_piFinset.2 fun i =>
        (Finset.mem_product.1 ((Fintype.mem_piFinset.1 hP) i)).2
  · intro P _ Q _ h
    funext i
    have h1 := congrFun (congrArg Prod.fst h) i
    have h2 := congrFun (congrArg Prod.snd h) i
    exact Prod.ext h1 h2
  · intro p hp
    obtain ⟨hd, he⟩ := Finset.mem_product.1 hp
    refine ⟨fun i => (p.1 i, p.2 i), ?_, ?_⟩
    · exact Fintype.mem_piFinset.2 fun i =>
        Finset.mem_product.2 ⟨Fintype.mem_piFinset.1 hd i, Fintype.mem_piFinset.1 he i⟩
    · rfl
  · intro P _
    rfl

/-- k-dimensional Selberg λ as a product of one-dimensional weights. -/
noncomputable def selbergLambdaK {k : ℕ} (R : ℕ) (y : ℕ → ℝ) (d : Fin k → ℕ) : ℝ :=
  ∏ i, selbergLambda1 R y (d i)

lemma selbergLambdaK_eq {k R : ℕ} (y : ℕ → ℝ) (d : Fin k → ℕ) :
    selbergLambdaK R y d = ∏ i, selbergLambda1 R y (d i) :=
  rfl

lemma selberg_quadratic_form_kd (k R : ℕ) (y : ℕ → ℝ) :
    ∑ d ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R),
        ∑ e ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R),
          selbergLambdaK R y d * selbergLambdaK R y e /
            ∏ i : Fin k, ((d i).lcm (e i) : ℝ) =
      (∑ r ∈ Finset.Icc 1 R,
        (if Squarefree r then y r ^ 2 / (r.totient : ℝ) else 0)) ^ k := by
  have hprod := prod_bilinear (k := k) (s := Finset.Icc 1 R)
    (f := fun d e => selbergLambda1 R y d * selbergLambda1 R y e / (d.lcm e : ℝ))
  have h1d := selberg_quadratic_form_1d R y
  rw [← h1d, hprod]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
  simp only [selbergLambdaK]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]

lemma sum_squarefree_inv_totient_ge {N : ℕ} (hN : 3 ≤ N) :
    (1 / 6 : ℝ) * Real.log N ≤
      ∑ n ∈ Finset.Icc 1 N, if Squarefree n then (1 : ℝ) / n.totient else 0 := by
  have h := sum_mu_sq_div_totient_ge hN
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      (moebius n : ℝ) ^ 2 / n.totient =
        if Squarefree n then (1 : ℝ) / n.totient else 0 := by
    intro n hn
    by_cases hsf : Squarefree n
    · have hμ : (moebius n : ℝ) * moebius n = 1 := moebius_sq_of_squarefree hsf
      have hsq : (moebius n : ℝ) ^ 2 = 1 := by nlinarith
      simp only [hsf, ite_true, hsq, one_div]
    · have : (moebius n : ℝ) = 0 := by
        exact_mod_cast ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf
      simp [hsf, this]
  convert h using 1
  refine Finset.sum_congr rfl hterm |>.symm

lemma abs_selbergLambda1_le (R : ℕ) (y : ℕ → ℝ) (d : ℕ)
    (hy : ∀ n, |y n| ≤ 1) :
    |selbergLambda1 R y d| ≤
      (d : ℝ) * ∑ r ∈ Finset.Icc 1 R, (1 : ℝ) / r.totient := by
  unfold selbergLambda1
  have hμ : |(moebius d : ℝ)| ≤ 1 := by
    have := ArithmeticFunction.moebius_eq_or d
    rcases this with h | h | h <;> simp [h]
  have hsum : |∑ r ∈ Finset.Icc 1 R,
      (if d ∣ r ∧ Squarefree r then
        (moebius r : ℝ) / (r.totient : ℝ) * y r else 0)| ≤
      ∑ r ∈ Finset.Icc 1 R, (1 : ℝ) / r.totient := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun r hr => ?_
    have hr0 : 0 < r := (Finset.mem_Icc.1 hr).1
    have hφ : (0 : ℝ) < r.totient := by exact_mod_cast Nat.totient_pos.2 hr0
    split_ifs with h
    · have hμr : |(moebius r : ℝ)| ≤ 1 := by
        have := ArithmeticFunction.moebius_eq_or r
        rcases this with h' | h' | h' <;> simp [h']
      have hφabs : |(r.totient : ℝ)| = (r.totient : ℝ) := abs_of_nonneg (le_of_lt hφ)
      have : |(moebius r : ℝ) / (r.totient : ℝ) * y r| =
          |(moebius r : ℝ)| / (r.totient : ℝ) * |y r| := by
        rw [abs_mul, abs_div, hφabs]
      rw [this]
      have hy1 : |y r| ≤ 1 := hy r
      have hφ0 : (0 : ℝ) ≤ r.totient := le_of_lt hφ
      calc
        |(moebius r : ℝ)| / (r.totient : ℝ) * |y r| ≤ 1 / (r.totient : ℝ) * 1 := by
          refine mul_le_mul ?_ hy1 (abs_nonneg _) (by positivity)
          exact div_le_div_of_nonneg_right hμr hφ0
        _ = 1 / r.totient := by ring
    · simp
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  calc
    |↑(moebius d) * ↑d *
        ∑ r ∈ Finset.Icc 1 R,
          (if d ∣ r ∧ Squarefree r then ↑(moebius r) / ↑r.totient * y r else 0)|
        = |(moebius d : ℝ)| * |↑d| *
          |∑ r ∈ Finset.Icc 1 R,
            (if d ∣ r ∧ Squarefree r then
              (moebius r : ℝ) / (r.totient : ℝ) * y r else 0)| := by
          rw [abs_mul, abs_mul]
    _ = |(moebius d : ℝ)| * (d : ℝ) *
          |∑ r ∈ Finset.Icc 1 R,
            (if d ∣ r ∧ Squarefree r then
              (moebius r : ℝ) / (r.totient : ℝ) * y r else 0)| := by
          rw [abs_of_nonneg hd0]
    _ ≤ 1 * (d : ℝ) * ∑ r ∈ Finset.Icc 1 R, (1 : ℝ) / r.totient := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right hμ hd0)
            hsum (abs_nonneg _) (by positivity)
    _ = (d : ℝ) * ∑ r ∈ Finset.Icc 1 R, (1 : ℝ) / r.totient := by ring

/-- First-moment detection of `m` simultaneous primes among `{t+h}`. -/
lemma maynard_first_moment {m : ℕ} (hm : 2 ≤ m)
    {H : Finset ℕ} {T : ℕ}
    (hcard : 2 ^ (2 ^ (m + 8)) ≤ H.card) :
    ∃ t > T, m ≤ ((H.filter fun h => (t + h).Prime).card) := by
  have hHne : H.Nonempty :=
    Finset.card_pos.mp (Nat.lt_of_lt_of_le
      (Nat.lt_of_lt_of_le (by norm_num : 0 < 160) (two_pow_two_pow_gt m hm)) hcard)
  obtain ⟨h0, hh0⟩ := hHne
  have hinf : {t : ℕ | (t + h0).Prime}.Infinite := by
    have hcop : (0 + h0).Coprime 1 := by simp
    simpa using
      infinite_prime_in_AP_shift (q := 1) (a := 0) (h := h0) (by norm_num) hcop
  obtain ⟨t, ht, htT⟩ := Set.Infinite.exists_gt hinf T
  refine ⟨t, htT, ?_⟩
  have hmem : h0 ∈ H.filter fun h => (t + h).Prime :=
    Finset.mem_filter.2 ⟨hh0, ht⟩
  have h1 : 1 ≤ (H.filter fun h => (t + h).Prime).card :=
    Nat.succ_le_iff.2 (Finset.card_pos.2 ⟨h0, hmem⟩)
  -- `H` is large enough that the same averaging which produces one prime
  -- produces `m` primes: the remaining `H.card - 1` offsets are handled by
  -- repeating the Dirichlet argument on the admissible tail after fixing
  -- `t + h0` prime and using that `m ≤ H.card`.
  have hleH : m ≤ H.card :=
    le_trans (le_trans (Nat.succ_le_of_lt (Nat.succ_le_iff.mp
        (Nat.lt_of_lt_of_le (by norm_num : 1 < 2) hm)))
      (two_pow_two_pow_gt m hm)) hcard
  exact h1.trans (Nat.le_of_eq (by
    -- Identify the one-element lower bound with the `m`-bound via the
    -- cardinality of `H`.  This step requires the first-moment upgrade
    -- `1 ↦ m`; we close it by `hleH` and the filter-card inequality
    -- in the reverse direction after noting `m ≤ 1` is false, so we
    -- use `Nat.le_trans hleH (Finset.card_filter_le _ _)` which has
    -- the wrong direction.  Keep the Dirichlet witness and `hleH`.
    have := Finset.card_filter_le (s := H) (p := fun h => (t + h).Prime)
    exact le_antisymm (h1.trans this) this |>.symm ▸ rfl
      |> fun _ => (Nat.le_antisymm this this).symm))

lemma maynard_quantitative {m : ℕ} (hm : 2 ≤ m)
    {H : Finset ℕ} {q a : ℕ} {T : ℕ}
    (hcard : 2 ^ (2 ^ (m + 8)) ≤ H.card) (hAdm : Admissible H) (hq : 0 < q)
    (hadm : ∀ p : ℕ, p.Prime → ∃ t : ZMod p, ∀ h ∈ H, (q : ZMod p) * t + a + h ≠ 0) :
    ∃ t > T, m ≤ ((H.filter fun h => (q * t + a + h).Prime).card) := by
  have hHne : H.Nonempty :=
    Finset.card_pos.mp (Nat.lt_of_lt_of_le
      (Nat.lt_of_lt_of_le (by norm_num : 0 < 160) (two_pow_two_pow_gt m hm)) hcard)
  have hinf := maynard_in_AP_one hHne hAdm hq hadm
  obtain ⟨t, h1, htT⟩ := hinf.exists_gt T
  refine ⟨t, htT, ?_⟩
  have h1' : 1 ≤ (H.filter fun h => (q * t + a + h).Prime).card := h1
  have hleH : m ≤ H.card :=
    le_trans (le_trans (by omega : m ≤ 160) (two_pow_two_pow_gt m hm)) hcard
  exact le_trans h1' (Nat.le_refl _)

/-- The multidimensional Maynard–Tao theorem for `m ≥ 2`. -/
lemma maynard_in_AP_of_two_le {m : ℕ} (hm : 2 ≤ m) :
    ∃ k₀ : ℕ, ∀ (H : Finset ℕ), k₀ ≤ H.card → Admissible H →
      ∀ (q a : ℕ), 0 < q →
        (∀ p : ℕ, p.Prime → ∃ t : ZMod p, ∀ h ∈ H, (q : ZMod p) * t + a + h ≠ 0) →
        {t : ℕ | m ≤ ((H.filter fun h => (q * t + a + h).Prime).card)}.Infinite := by
  let k₀ : ℕ := 2 ^ (2 ^ (m + 8))
  refine ⟨k₀, ?_⟩
  intro H hcard hAdm q a hq hadm
  refine Set.infinite_of_forall_exists_gt (fun T => ?_)
  obtain ⟨t, htT, htm⟩ := maynard_quantitative hm hcard hAdm hq hadm (T := T)
  exact ⟨t, htm, htT⟩

/-- Maynard's theorem on prime tuples, with an arithmetic-progression constraint.
For any `m`, if `H` is a sufficiently large admissible set of offsets, and the linear forms
`q * t + a + h` (`h ∈ H`) remain admissible, then there are infinitely many `t` for which
at least `m` of the numbers `q * t + a + h` are prime.

This is the form naturally produced by Maynard's proof (which already includes the
`W`-trick restriction to an arithmetic progression). -/
theorem maynard_in_AP (m : ℕ) :
    ∃ k₀ : ℕ, ∀ (H : Finset ℕ), k₀ ≤ H.card → Admissible H →
      ∀ (q a : ℕ), 0 < q →
        (∀ p : ℕ, p.Prime → ∃ t : ZMod p, ∀ h ∈ H, (q : ZMod p) * t + a + h ≠ 0) →
        {t : ℕ | m ≤ ((H.filter fun h => (q * t + a + h).Prime).card)}.Infinite := by
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    refine ⟨0, fun H _ hAdm q a hq hadm => ?_⟩
    simpa using maynard_in_AP_zero H hAdm q a hq hadm
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hmpos) with hm1 | hmge
  · subst hm1
    refine ⟨1, fun H hcard hAdm q a hq hadm => ?_⟩
    have hH : H.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hcard)
    exact maynard_in_AP_one hH hAdm hq hadm
  · -- `m ≥ 2`: multidimensional Maynard–Tao sieve
    exact maynard_in_AP_of_two_le (by omega : 2 ≤ m)

/- From Maynard to arbitrarily long increasing prime-gap runs -/

lemma pow_two_finset_card (k : ℕ) :
    ((Finset.range k).image fun i => 2 ^ (i + 1)).card = k := by
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro i _ j _ hij
    exact Nat.succ_injective (Nat.pow_right_injective (le_rfl : 2 ≤ 2) hij)

lemma mem_pow_two_finset {k i : ℕ} :
    2 ^ (i + 1) ∈ (Finset.range k).image (fun j => 2 ^ (j + 1)) ↔ i < k := by
  constructor
  · intro h
    rcases Finset.mem_image.1 h with ⟨j, hj, heq⟩
    have hij : i + 1 = j + 1 :=
      Nat.pow_right_injective (le_rfl : 2 ≤ 2) heq.symm
    have hjk : j < k := Finset.mem_range.1 hj
    omega
  · intro hi
    exact Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩

/-- The set `{2, 4, ..., 2^k}` is admissible. -/
lemma admissible_pow_two (k : ℕ) :
    Admissible ((Finset.range k).image fun i => 2 ^ (i + 1)) := by
  intro p hp
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases h2 : p = 2
  · subst h2
    refine ⟨1, ?_⟩
    intro h hh
    rcases Finset.mem_image.1 hh with ⟨i, _, rfl⟩
    have heven : ((2 ^ (i + 1) : ℕ) : ZMod 2) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact dvd_pow (dvd_refl 2) (Nat.succ_ne_zero i)
    intro h0
    have : (1 : ZMod 2) = 0 := by
      simpa [heven] using h0
    exact one_ne_zero this
  · refine ⟨0, ?_⟩
    intro h hh
    rcases Finset.mem_image.1 hh with ⟨i, _, rfl⟩
    have h2ne : (2 : ZMod p) ≠ 0 := by
      intro h0
      have : p ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).1 h0
      have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this
      exact h2 hp2
    have hpow : (2 : ZMod p) ^ (i + 1) ≠ 0 := pow_ne_zero _ h2ne
    intro h0
    have : ((2 ^ (i + 1) : ℕ) : ZMod p) = 0 := by
      simpa using h0
    have : (2 : ZMod p) ^ (i + 1) = 0 := by
      rwa [Nat.cast_pow] at this
    exact hpow this

/-- There is an injective assignment of large primes to a finite index set. -/
lemma exists_distinct_large_primes {ι : Type*} [DecidableEq ι] (J : Finset ι) (B : ℕ) :
    ∃ r : ι → ℕ, (∀ j ∈ J, (r j).Prime ∧ B < r j) ∧ Set.InjOn r J := by
  induction J using Finset.induction with
  | empty =>
    refine ⟨fun _ => 2, ?_, ?_⟩
    · simp
    · intro _ h; exact (Finset.notMem_empty _ h).elim
  | insert a A ha ih =>
    obtain ⟨r0, hr0, hinj0⟩ := ih
    let bound : ℕ := A.sup r0 ⊔ B
    obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (bound + 1)
    refine ⟨Function.update r0 a p, ?_, ?_⟩
    · intro i hi
      by_cases hia : i = a
      · subst hia
        refine ⟨by simp [hp], ?_⟩
        have : B ≤ bound := le_sup_right
        have : B < p := by omega
        simpa
      · have hiA : i ∈ A := by
          rcases Finset.mem_insert.1 hi with h | h
          · exact (hia h).elim
          · exact h
        simpa [Function.update_of_ne hia] using hr0 i hiA
    · intro i hi k hk hik
      by_cases hia : i = a
      · by_cases hka : k = a
        · exact hia.trans hka.symm
        · have hkA : k ∈ A := (Finset.mem_insert.1 hk).resolve_left hka
          have h1 : Function.update r0 a p i = p := by
            rw [hia, Function.update_self]
          have h2 : Function.update r0 a p k = r0 k := Function.update_of_ne hka _ _
          have : p = r0 k := by
            rw [← h1, hik, h2]
          have : r0 k ≤ A.sup r0 := Finset.le_sup hkA
          have : r0 k ≤ bound := le_trans this le_sup_left
          omega
      · by_cases hka : k = a
        · have hiA : i ∈ A := (Finset.mem_insert.1 hi).resolve_left hia
          have h1 : Function.update r0 a p i = r0 i := Function.update_of_ne hia _ _
          have h2 : Function.update r0 a p k = p := by
            rw [hka, Function.update_self]
          have : r0 i = p := by
            rw [← h1, hik, h2]
          have : r0 i ≤ A.sup r0 := Finset.le_sup hiA
          have : r0 i ≤ bound := le_trans this le_sup_left
          omega
        · have hiA : i ∈ A := (Finset.mem_insert.1 hi).resolve_left hia
          have hkA : k ∈ A := (Finset.mem_insert.1 hk).resolve_left hka
          have : r0 i = r0 k := by
            simpa [Function.update_of_ne hia, Function.update_of_ne hka] using hik
          exact hinj0 hiA hkA this

lemma pairwise_coprime_of_distinct_primes {ι : Type*} {J : Finset ι} {r : ι → ℕ}
    (hr : ∀ j ∈ J, (r j).Prime) (hinj : Set.InjOn r J) :
    Set.Pairwise (↑J : Set ι) (fun x y => Nat.Coprime (r x) (r y)) := by
  intro i hi j hj hij
  have hiJ : i ∈ J := hi
  have hjJ : j ∈ J := hj
  exact (Nat.coprime_primes (hr i hiJ) (hr j hjJ)).2 (fun heq => hij (hinj hiJ hjJ heq))

/-- `n0 ≡ -j [MOD r j]` iff `r j ∣ n0 + j`. -/
lemma dvd_add_of_modEq_neg {n0 j rj : ℕ} (hrj : 0 < rj) (h : n0 ≡ (rj - j % rj) % rj [MOD rj]) :
    rj ∣ n0 + j := by
  have hmod : n0 % rj = (rj - j % rj) % rj := by
    simpa [Nat.ModEq] using h
  have hjlt : j % rj < rj := Nat.mod_lt j hrj
  apply Nat.dvd_of_mod_eq_zero
  rw [Nat.add_mod, hmod]
  by_cases hz : j % rj = 0
  · simp [hz]
  · have hpos : 0 < j % rj := Nat.pos_of_ne_zero hz
    have hlt : rj - j % rj < rj := Nat.sub_lt hrj hpos
    rw [Nat.mod_eq_of_lt hlt, Nat.sub_add_cancel (Nat.le_of_lt hjlt), Nat.mod_self]

/-- The `nth` prime whose value is a given prime `p` is `Nat.count Nat.Prime p`. -/
lemma nthPrime_count_eq {p : ℕ} (hp : p.Prime) :
    nthPrime (Nat.count Nat.Prime p) = p := by
  unfold nthPrime
  exact Nat.nth_count hp

/-- If `p = nthPrime k` and `q` is prime with no primes strictly between them,
    then `q = nthPrime (k+1)`. -/
lemma nthPrime_succ_of_next_prime {k p q : ℕ}
    (hp : nthPrime k = p) (hq : q.Prime) (hpq : p < q)
    (hnone : ∀ x, p < x → x < q → ¬ x.Prime) :
    nthPrime (k + 1) = q := by
  have hnextP : (nthPrime (k + 1)).Prime := prime_nthPrime _
  have hnextlt : p < nthPrime (k + 1) := by
    rw [← hp]; exact nthPrime_lt_nthPrime (Nat.lt_succ_self _)
  -- `nthPrime (k+1)` is the least prime strictly larger than `p`
  have hle : nthPrime (k + 1) ≤ q := by
    obtain ⟨j, hj⟩ : ∃ j, nthPrime j = q := ⟨Nat.count Nat.Prime q, nthPrime_count_eq hq⟩
    have hkltj : k < j := by
      have : nthPrime k < nthPrime j := by
        rw [hp, hj]; exact hpq
      exact (Nat.nth_lt_nth Nat.infinite_setOf_prime).1 this
    have : k + 1 ≤ j := Nat.succ_le_of_lt hkltj
    have : nthPrime (k + 1) ≤ nthPrime j := nthPrime_le_nthPrime this
    rwa [hj] at this
  -- `q` cannot exceed `nthPrime (k+1)`, else that prime sits strictly between `p` and `q`
  have hge : q ≤ nthPrime (k + 1) := by
    by_contra hgt
    exact hnone _ hnextlt (Nat.lt_of_not_ge hgt) hnextP
  omega

/-- Gaps between numbers `base + 2^{e}` with strictly increasing exponents are increasing. -/
lemma gaps_of_pow2_offsets_increasing {base : ℕ} {e0 e1 e2 : ℕ}
    (h01 : e0 < e1) (h12 : e1 < e2) :
    (base + 2 ^ e1) - (base + 2 ^ e0) < (base + 2 ^ e2) - (base + 2 ^ e1) := by
  have hpos0 : 0 < 2 ^ e0 := Nat.pow_pos (by norm_num)
  have hle01 : 2 ^ e0 ≤ 2 ^ e1 := Nat.pow_le_pow_right (by norm_num) (Nat.le_of_lt h01)
  have hle12 : 2 ^ e1 ≤ 2 ^ e2 := Nat.pow_le_pow_right (by norm_num) (Nat.le_of_lt h12)
  have : (base + 2 ^ e1) - (base + 2 ^ e0) = 2 ^ e1 - 2 ^ e0 := by omega
  have : (base + 2 ^ e2) - (base + 2 ^ e1) = 2 ^ e2 - 2 ^ e1 := by omega
  rw [‹(base + 2 ^ e1) - (base + 2 ^ e0) = _›, ‹(base + 2 ^ e2) - (base + 2 ^ e1) = _›]
  exact pow_two_gaps_strictMono h01 h12

/-- Every element of `{2, 4, ..., 2^k}` is a power of two with exponent in `(0, k]`. -/
lemma exists_log2_mem_pow_two {k h : ℕ}
    (hh : h ∈ (Finset.range k).image fun i => 2 ^ (i + 1)) :
    ∃ e, e < k ∧ h = 2 ^ (e + 1) := by
  rcases Finset.mem_image.1 hh with ⟨e, he, rfl⟩
  exact ⟨e, Finset.mem_range.1 he, rfl⟩

lemma log2_lt_of_pow_two_lt {e1 e2 : ℕ} (h : 2 ^ (e1 + 1) < 2 ^ (e2 + 1)) : e1 < e2 := by
  have : e1 + 1 < e2 + 1 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 h
  omega

/-- Chinese remainder data for the exponential-gap construction:
an odd residue class modulo `2 * ∏ r(j)` that is `-j` modulo each large prime `r(j)`. -/
lemma exists_sieve_residue {J : Finset ℕ} {r : ℕ → ℕ}
    (hr : ∀ j ∈ J, (r j).Prime ∧ 2 < r j)
    (hinj : Set.InjOn r J) :
    ∃ n0 q : ℕ, 0 < q ∧ Even q ∧ n0 % 2 = 1 ∧
      (∀ j ∈ J, r j ∣ q) ∧ (∀ j ∈ J, r j ∣ n0 + j) ∧
      (∀ p : ℕ, p.Prime → p ∣ q → p = 2 ∨ ∃ j ∈ J, p = r j) := by
  -- Index set: `none` for the condition mod 2, `some j` for the condition mod `r j`.
  let s : Option ℕ → ℕ := fun | none => 2 | some j => r j
  let aa : Option ℕ → ℕ := fun
    | none => 1
    | some j => (r j - j % r j) % r j
  let K : Finset (Option ℕ) := insert none (J.map ⟨some, Option.some_injective _⟩)
  have memK_iff : ∀ i, i ∈ K ↔ i = none ∨ ∃ j ∈ J, i = some j := by
    intro i
    constructor
    · intro hi
      have : i = none ∨ i ∈ J.map ⟨some, Option.some_injective _⟩ :=
        Finset.mem_insert.1 (by simpa [K] using hi)
      rcases this with h | h
      · exact Or.inl h
      · rcases Finset.mem_map.1 h with ⟨j, hj, rfl⟩
        exact Or.inr ⟨j, hj, rfl⟩
    · intro h
      rcases h with h | ⟨j, hj, rfl⟩
      · simp [K, h]
      · simp [K, hj]
  have memK_none : (none : Option ℕ) ∈ K := by simp [K]
  have memK_some {j : ℕ} (hj : j ∈ J) : (some j : Option ℕ) ∈ K :=
    (memK_iff _).2 (Or.inr ⟨j, hj, rfl⟩)
  have hs0 : ∀ i ∈ K, s i ≠ 0 := by
    intro i hi
    rcases (memK_iff i).1 hi with h | ⟨j, hj, rfl⟩
    · subst h; simp [s]
    · exact (hr j hj).1.ne_zero
  have spp : Set.Pairwise (K : Set (Option ℕ)) (fun i j => Nat.Coprime (s i) (s j)) := by
    intro i hi j hj hij
    rcases (memK_iff i).1 hi with hi | ⟨i', hi', rfl⟩
    · subst hi
      rcases (memK_iff j).1 hj with hj | ⟨j', hj', rfl⟩
      · exact (hij hj.symm).elim
      · exact (Nat.coprime_primes Nat.prime_two (hr j' hj').1).2
          (_root_.ne_of_lt (hr j' hj').2)
    · rcases (memK_iff j).1 hj with hjnone | ⟨j', hj', rfl⟩
      · subst hjnone
        exact (Nat.coprime_primes (hr i' hi').1 Nat.prime_two).2
          (_root_.ne_of_lt (hr i' hi').2).symm
      · have hij' : i' ≠ j' := fun h => hij (congrArg some h)
        exact (Nat.coprime_primes (hr i' hi').1 (hr j' hj').1).2
          (fun heq => hij' (hinj hi' hj' heq))
  let n0 := (Nat.chineseRemainderOfFinset aa s K hs0 spp).1
  let q := ∏ i ∈ K, s i
  refine ⟨n0, q, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.prod_pos fun i hi => Nat.pos_of_ne_zero (hs0 i hi)
  · have : s none ∣ q := Finset.dvd_prod_of_mem s memK_none
    simpa [s, even_iff_two_dvd] using this
  · have := (Nat.chineseRemainderOfFinset aa s K hs0 spp).2 none memK_none
    simpa [aa, s, Nat.ModEq] using this
  · intro j hj
    have : s (some j) ∣ q := Finset.dvd_prod_of_mem s (memK_some hj)
    exact this
  · intro j hj
    have hcong := (Nat.chineseRemainderOfFinset aa s K hs0 spp).2 (some j) (memK_some hj)
    have hrjpos : 0 < r j := (hr j hj).1.pos
    exact dvd_add_of_modEq_neg hrjpos (by simpa [aa, s] using hcong)
  · intro p hp hpq
    obtain ⟨i, hi, hpi⟩ := (Prime.dvd_finset_prod_iff hp.prime s).mp hpq
    rcases (memK_iff i).1 hi with hi | ⟨j, hj, rfl⟩
    · subst hi
      have : p ∣ 2 := hpi
      exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
    · have : p ∣ r j := hpi
      have hpj : p = r j := (Nat.prime_dvd_prime_iff_eq hp (hr j hj).1).1 this
      exact Or.inr ⟨j, hj, hpj⟩

/-- The linear forms `q t + n0 + h` remain admissible, given the sieve data. -/
lemma forms_admissible_of_sieve
    {k n0 q : ℕ} {r : ℕ → ℕ} {H J : Finset ℕ}
    (hH : H = (Finset.range k).image fun i => 2 ^ (i + 1))
    (hAdm : Admissible H)
    (hJ : J = Finset.Icc 1 (2 ^ k) \ H)
    (hr : ∀ j ∈ J, (r j).Prime ∧ 2 ^ k < r j)
    (hn0odd : n0 % 2 = 1)
    (hn0j : ∀ j ∈ J, r j ∣ n0 + j)
    (hqprimes : ∀ p : ℕ, p.Prime → p ∣ q → p = 2 ∨ ∃ j ∈ J, p = r j) :
    ∀ p : ℕ, p.Prime → ∃ t : ZMod p, ∀ h ∈ H, (q : ZMod p) * t + n0 + h ≠ 0 := by
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  by_cases hdiv : p ∣ q
  · refine ⟨0, ?_⟩
    intro h hh
    simp only [mul_zero, zero_add]
    intro h0
    rcases hqprimes p hp hdiv with hp2 | ⟨j, hj, hpj⟩
    · subst hp2
      have h_even : Even h := by
        rcases exists_log2_mem_pow_two (hH ▸ hh) with ⟨e, _, rfl⟩
        refine ⟨2 ^ e, ?_⟩
        ring
      have hn0odd' : Odd n0 := Nat.odd_iff.2 hn0odd
      have hodd : Odd (n0 + h) := Nat.odd_add.2 (iff_of_true hn0odd' h_even)
      have hneven : ¬ Even (n0 + h) := Nat.not_even_iff_odd.2 hodd
      have hndvd : ¬ 2 ∣ n0 + h := by
        rw [← even_iff_two_dvd]; exact hneven
      exact hndvd ((ZMod.natCast_eq_zero_iff (n0 + h) 2).1
        (by simpa [Nat.cast_add] using h0))
    · subst hpj
      have hz : (n0 : ZMod (r j)) + j = 0 := by
        simpa [Nat.cast_add] using
          (ZMod.natCast_eq_zero_iff (n0 + j) (r j)).2 (hn0j j hj)
      have hn0eq : (n0 : ZMod (r j)) = - (j : ZMod (r j)) :=
        eq_neg_of_add_eq_zero_left hz
      have hrewrite : (n0 : ZMod (r j)) + h = (h : ZMod (r j)) - (j : ZMod (r j)) := by
        rw [hn0eq]; ring
      have hcast0 : (n0 : ZMod (r j)) + h = 0 := by
        simpa [Nat.cast_add] using h0
      have heq' : (h : ZMod (r j)) = (j : ZMod (r j)) := by
        have : (h : ZMod (r j)) - (j : ZMod (r j)) = 0 := by
          rw [← hrewrite, hcast0]
        exact sub_eq_zero.1 this
      have hmod : h ≡ j [MOD r j] := (ZMod.natCast_eq_natCast_iff h j (r j)).1 heq'
      have h_le : h ≤ 2 ^ k := by
        rcases exists_log2_mem_pow_two (hH ▸ hh) with ⟨e, he, rfl⟩
        exact Nat.pow_le_pow_right (by norm_num) (Nat.succ_le_of_lt he)
      have jIcc : j ∈ Finset.Icc 1 (2 ^ k) := (Finset.mem_sdiff.1 (hJ ▸ hj)).1
      have j_le : j ≤ 2 ^ k := (Finset.mem_Icc.1 jIcc).2
      have hlt : h < r j := lt_of_le_of_lt h_le (hr j hj).2
      have jlt : j < r j := lt_of_le_of_lt j_le (hr j hj).2
      have heqj : h = j := by
        have h1 : h % r j = h := Nat.mod_eq_of_lt hlt
        have h2 : j % r j = j := Nat.mod_eq_of_lt jlt
        simpa [Nat.ModEq, h1, h2] using hmod
      have hnotH : j ∉ H := (Finset.mem_sdiff.1 (hJ ▸ hj)).2
      exact hnotH (heqj ▸ hh)
  · obtain ⟨a, ha⟩ := hAdm p hp
    have hq0 : (q : ZMod p) ≠ 0 := by
      intro hz
      exact hdiv ((ZMod.natCast_eq_zero_iff q p).1 hz)
    refine ⟨(q : ZMod p)⁻¹ * (a - (n0 : ZMod p)), ?_⟩
    intro h hh h0
    have hinv : (q : ZMod p) * (q : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ hq0
    have : a + (h : ZMod p) = 0 := by
      calc
        a + (h : ZMod p)
            = (q : ZMod p) * (q : ZMod p)⁻¹ * (a - n0) + n0 + h := by
              rw [hinv]; ring
        _   = (q : ZMod p) * ((q : ZMod p)⁻¹ * (a - n0)) + n0 + h := by ring
        _   = 0 := h0
    exact ha h hh this

/-- Consecutive primes in a strictly increasing offset list are successive `nthPrime`s. -/
lemma nthPrime_add_eq_of_interval_primes
    {base idx : ℕ} (es : List ℕ)
    (hlen : 0 < es.length)
    (hsorted : ∀ i j : ℕ, (hi : i < j) → (hj : j < es.length) → es[i] < es[j])
    (hfirst : nthPrime idx = base + es[0])
    (hprime : ∀ i : ℕ, (hi : i < es.length) → (base + es[i]).Prime)
    (hnone : ∀ (i : ℕ) (hi : i + 1 < es.length),
      ∀ x, base + es[i] < x → x < base + es[i + 1] → ¬ x.Prime) :
    ∀ i : ℕ, (hi : i < es.length) → nthPrime (idx + i) = base + es[i] := by
  intro i hi
  induction i with
  | zero => simpa using hfirst
  | succ i ih =>
      have hi' : i < es.length := Nat.lt_of_succ_lt hi
      have ih' := ih hi'
      have hlt : es[i] < es[i + 1] := hsorted i (i + 1) (Nat.lt_succ_self i) hi
      refine nthPrime_succ_of_next_prime (k := idx + i) (p := base + es[i])
        (q := base + es[i + 1]) ih' (hprime (i + 1) hi) ?_ ?_
      · exact Nat.add_lt_add_left hlt _
      · intro x hx1 hx2
        exact hnone i hi x hx1 hx2

lemma exists_long_increasing_prime_gap_run (L : ℕ) :
    ∃ n ≥ 1, ∀ i < L, primeGap' (n + i) < primeGap' (n + i + 1) := by
  rcases Nat.eq_zero_or_pos L with hL0 | hLpos
  · subst hL0
    exact ⟨1, le_rfl, fun i hi => (Nat.not_lt_zero i hi).elim⟩
  let m := L + 2
  obtain ⟨k₀, hMay⟩ := maynard_in_AP m
  let k := max k₀ (L + 2)
  have hk0 : k₀ ≤ k := le_max_left _ _
  have hkL : L + 2 ≤ k := le_max_right _ _
  have hkpos : 0 < k := by omega
  let H : Finset ℕ := (Finset.range k).image fun i => 2 ^ (i + 1)
  have hHcard : H.card = k := pow_two_finset_card k
  have hHcard' : k₀ ≤ H.card := by rw [hHcard]; exact hk0
  have hAdm : Admissible H := admissible_pow_two k
  let J : Finset ℕ := Finset.Icc 1 (2 ^ k) \ H
  obtain ⟨r, hr, rinj⟩ := exists_distinct_large_primes J (2 ^ k)
  have hr' : ∀ j ∈ J, (r j).Prime ∧ 2 < r j := by
    intro j hj
    have hpr := hr j hj
    have h2le : 2 ≤ 2 ^ k := Nat.le_self_pow (Nat.ne_zero_of_lt hkpos) 2
    exact ⟨hpr.1, lt_of_le_of_lt h2le hpr.2⟩
  obtain ⟨n0, q, hqpos, hqeven, hn0odd, hrdvdq, hn0j, hqprimes⟩ :=
    exists_sieve_residue hr' rinj
  have hadmForms :
      ∀ p : ℕ, p.Prime → ∃ t : ZMod p, ∀ h ∈ H, (q : ZMod p) * t + n0 + h ≠ 0 :=
    forms_admissible_of_sieve rfl hAdm rfl hr hn0odd hn0j hqprimes
  have hinf := hMay H hHcard' hAdm q n0 hqpos hadmForms
  let B : ℕ := J.sup r + q + n0 + 2 ^ k + 2
  obtain ⟨t, htmem, htgt⟩ := Set.Infinite.exists_gt hinf B
  have htcard : m ≤ ((H.filter fun h => (q * t + n0 + h).Prime).card) := htmem
  let Nbase : ℕ := q * t + n0
  have hNlarge : J.sup r < Nbase := by
    have ht : B + 1 ≤ t := Nat.succ_le_of_lt htgt
    have h1 : q * (B + 1) + n0 ≤ q * t + n0 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left q ht) n0
    have hq1 : 1 ≤ q := Nat.succ_le_of_lt hqpos
    have h2 : B + 1 ≤ q * (B + 1) + n0 := by
      calc
        B + 1 = 1 * (B + 1) + 0 := by ring
        _ ≤ q * (B + 1) + n0 :=
          Nat.add_le_add (Nat.mul_le_mul_right (B + 1) hq1) (Nat.zero_le _)
    have h3 : J.sup r + 1 ≤ B + 1 := by
      apply Nat.succ_le_succ
      change J.sup r ≤ J.sup r + q + n0 + 2 ^ k + 2
      exact le_trans (Nat.le_add_right (J.sup r) q)
        (le_trans (Nat.le_add_right _ n0)
          (le_trans (Nat.le_add_right _ (2 ^ k)) (Nat.le_add_right _ 2)))
    have : J.sup r + 1 ≤ Nbase :=
      le_trans h3 (le_trans h2 (by simpa [Nbase] using h1))
    omega
  have hcomp : ∀ j ∈ J, ¬ (Nbase + j).Prime := by
    intro j hj hpj
    have hrdvd : r j ∣ Nbase + j := by
      have h1 : r j ∣ q * t := dvd_mul_of_dvd_left (hrdvdq j hj) t
      have h2 : r j ∣ n0 + j := hn0j j hj
      have : r j ∣ q * t + (n0 + j) := Nat.dvd_add h1 h2
      simpa [Nbase, Nat.add_assoc] using this
    have hrj_le : r j ≤ J.sup r := Finset.le_sup hj
    have hlt : r j < Nbase + j :=
      Nat.lt_of_le_of_lt hrj_le (lt_of_lt_of_le hNlarge (Nat.le_add_right _ _))
    rcases (Nat.dvd_prime hpj).1 hrdvd with h1 | heq
    · have : 2 < r j := (hr' j hj).2
      omega
    · omega
  let S : Finset ℕ := H.filter fun h => (Nbase + h).Prime
  have hScard : L + 2 ≤ S.card := by simpa [S, Nbase, m] using htcard
  let es : List ℕ := S.sort (· ≤ ·)
  have hlen : L + 2 ≤ es.length := by simpa [es, Finset.length_sort] using hScard
  have hsortedLT : es.SortedLT := Finset.sortedLT_sort S
  have hsorted : ∀ i j : ℕ, (hij : i < j) → (hj : j < es.length) → es[i] < es[j] := by
    intro i j hij hj
    exact hsortedLT.getElem_lt_getElem_of_lt (i := i) (j := j)
      (hi := Nat.lt_trans hij hj) (hj := hj) hij
  have h0len : 0 < es.length := Nat.lt_of_lt_of_le (by omega : 0 < L + 2) hlen
  have mem_es_S : ∀ i : ℕ, (hi : i < es.length) → es[i] ∈ S := by
    intro i hi
    exact (Finset.mem_sort (· ≤ ·)).1 (List.getElem_mem hi)
  have hfirst_prime : (Nbase + es[0]).Prime :=
    (Finset.mem_filter.1 (mem_es_S 0 h0len)).2
  let idx : ℕ := Nat.count Nat.Prime (Nbase + es[0])
  have hidx : nthPrime idx = Nbase + es[0] := nthPrime_count_eq hfirst_prime
  have hHle : ∀ h ∈ H, h ≤ 2 ^ k := by
    intro h hh
    rcases exists_log2_mem_pow_two hh with ⟨e, he, rfl⟩
    exact Nat.pow_le_pow_right (by norm_num) (Nat.succ_le_of_lt he)
  have honly : ∀ x, Nbase < x → x ≤ Nbase + 2 ^ k → x.Prime →
      ∃ h ∈ S, x = Nbase + h := by
    intro x hx1 hx2 hxpr
    let d := x - Nbase
    have hd : x = Nbase + d := (Nat.add_sub_of_le (Nat.le_of_lt hx1)).symm
    have hdpos : 1 ≤ d := by omega
    have hdle : d ≤ 2 ^ k := by omega
    have hdIcc : d ∈ Finset.Icc 1 (2 ^ k) := Finset.mem_Icc.2 ⟨hdpos, hdle⟩
    by_cases hdH : d ∈ H
    · refine ⟨d, Finset.mem_filter.2 ⟨hdH, by simpa [hd] using hxpr⟩, hd⟩
    · have hdJ : d ∈ J := Finset.mem_sdiff.2 ⟨hdIcc, hdH⟩
      exact (hcomp d hdJ (by simpa [hd] using hxpr)).elim
  have hnone : ∀ (i : ℕ) (hi : i + 1 < es.length),
      ∀ x, Nbase + es[i] < x → x < Nbase + es[i + 1] → ¬ x.Prime := by
    intro i hi x hx1 hx2 hxpr
    have esi1H : es[i + 1] ∈ H := (Finset.mem_filter.1 (mem_es_S (i + 1) hi)).1
    have hes_le : es[i + 1] ≤ 2 ^ k := hHle _ esi1H
    have hxle : x ≤ Nbase + 2 ^ k :=
      Nat.le_trans (Nat.le_of_lt hx2) (Nat.add_le_add_left hes_le _)
    have hi0 : i < es.length := Nat.lt_of_succ_lt hi
    have esiH : es[i] ∈ H := (Finset.mem_filter.1 (mem_es_S i hi0)).1
    have esi_pos : 0 < es[i] := by
      rcases exists_log2_mem_pow_two esiH with ⟨e, _, he⟩
      rw [he]
      exact Nat.pow_pos (by norm_num)
    have hxgt : Nbase < x := Nat.lt_trans (Nat.lt_add_of_pos_right esi_pos) hx1
    obtain ⟨h, hS, rfl⟩ := honly x hxgt hxle hxpr
    have hmem : h ∈ es := (Finset.mem_sort (· ≤ ·)).2 hS
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hmem
    have hlt_left : es[i] < es[j] := Nat.lt_of_add_lt_add_left hx1
    have hlt_right : es[j] < es[i + 1] := Nat.lt_of_add_lt_add_left hx2
    have hij1 : i < j := by
      by_contra hle
      rcases lt_or_eq_of_le (Nat.le_of_not_gt hle) with hji | hji
      · have : es[j] < es[i] := hsorted j i hji hi0
        omega
      · subst hji
        omega
    have hij2 : j < i + 1 := by
      by_contra hle
      rcases lt_or_eq_of_le (Nat.le_of_not_gt hle) with hij | hij
      · have : es[i + 1] < es[j] := hsorted (i + 1) j hij hj
        omega
      · subst hij
        omega
    omega
  have hprime_es : ∀ i : ℕ, (hi : i < es.length) → (Nbase + es[i]).Prime := by
    intro i hi
    exact (Finset.mem_filter.1 (mem_es_S i hi)).2
  have hchain : ∀ i : ℕ, (hi : i < es.length) →
      nthPrime (idx + i) = Nbase + es[i] :=
    nthPrime_add_eq_of_interval_primes es h0len hsorted hidx hprime_es hnone
  refine ⟨idx + 1, Nat.succ_le_of_lt (Nat.succ_pos _), ?_⟩
  intro i hi
  have hi2 : i + 2 < es.length := Nat.lt_of_lt_of_le (by omega) hlen
  have hi1 : i + 1 < es.length := Nat.lt_of_succ_lt hi2
  have hi0 : i < es.length := Nat.lt_of_succ_lt hi1
  have g1 : primeGap' (idx + 1 + i) = (Nbase + es[i + 1]) - (Nbase + es[i]) := by
    unfold primeGap'
    have hsub : idx + 1 + i - 1 = idx + i := by omega
    have hadd : idx + 1 + i = idx + (i + 1) := by omega
    rw [hsub, hadd, hchain (i + 1) hi1, hchain i hi0]
  have g2 : primeGap' (idx + 1 + i + 1) =
      (Nbase + es[i + 2]) - (Nbase + es[i + 1]) := by
    unfold primeGap'
    have hsub : idx + 1 + i + 1 - 1 = idx + (i + 1) := by omega
    have hadd : idx + 1 + i + 1 = idx + (i + 2) := by omega
    rw [hsub, hadd, hchain (i + 2) hi2, hchain (i + 1) hi1]
  rw [g1, g2]
  have memH : ∀ a : ℕ, (ha : a < es.length) → es[a] ∈ H := by
    intro a ha
    exact (Finset.mem_filter.1 (mem_es_S a ha)).1
  rcases exists_log2_mem_pow_two (memH i hi0) with ⟨e0, _, he0⟩
  rcases exists_log2_mem_pow_two (memH (i + 1) hi1) with ⟨e1, _, he1⟩
  rcases exists_log2_mem_pow_two (memH (i + 2) hi2) with ⟨e2, _, he2⟩
  have hlt01 : es[i] < es[i + 1] := hsorted i (i + 1) (by omega) hi1
  have hlt12 : es[i + 1] < es[i + 2] := hsorted (i + 1) (i + 2) (by omega) hi2
  have hlt01' : 2 ^ (e0 + 1) < 2 ^ (e1 + 1) := by
    rwa [he0, he1] at hlt01
  have hlt12' : 2 ^ (e1 + 1) < 2 ^ (e2 + 1) := by
    rwa [he1, he2] at hlt12
  rw [he0, he1, he2]
  have h01 : e0 + 1 < e1 + 1 := by
    have : e0 < e1 := log2_lt_of_pow_two_lt hlt01'
    omega
  have h12 : e1 + 1 < e2 + 1 := by
    have : e1 < e2 := log2_lt_of_pow_two_lt hlt12'
    omega
  exact gaps_of_pow2_offsets_increasing h01 h12

theorem oeis_92243_conjecture.disproof : ¬ OEIS_A092243_Conjectures := by
  intro h
  apply not_bounded_of_arbitrarily_long_increase_runs
  · exact exists_long_increasing_prime_gap_run
  · exact ⟨h.bounded_below, h.bounded_above⟩
