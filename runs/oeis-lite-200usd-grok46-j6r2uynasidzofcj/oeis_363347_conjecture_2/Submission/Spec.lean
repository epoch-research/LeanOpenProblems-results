import FormalConjectures.Util.ProblemImports

open Rat Nat

/--
Helper function for A363347, which computes the denominator $R_k(n)$ of the continued fraction expression.
For $2 \le k \le n-1$, $R_k(n)$ is defined recursively:
$$R_k(n) = k - \frac{k+1}{R_{k+1}(n)}$$
The base case is $R_{n-1}(n) = (n-1) - \frac{n}{-4}$.
-/
def continued_fraction_denominator (n k : ℕ) : ℚ :=
  if n ≤ 2 then 0
  else
    -- The recursive descent involves terms from $k=n-1$ down to $k=2$.
    if 2 ≤ k ∧ k ≤ n - 1 then
      -- Base Case: k = n - 1.
      if k = n - 1 then
        -- R_{n-1} = (n-1) + n/4
        (k : ℚ) + (n : ℚ) / 4
      -- Recursive Step: 2 <= k < n - 1.
      else
        let R_next := continued_fraction_denominator n (k + 1)
        -- R_k = k - (k+1) / R_{k+1}
        (k : ℚ) - (k + 1 : ℚ) / R_next
    else 0
termination_by n - k

/--
A363347: Denominator of the continued fraction
$$\frac{1}{2 - \frac{3}{3 - \frac{4}{4 - \frac{5}{\dots - \frac{n-1}{(n-1) - \frac{n}{-4}}}}}} $$
The value of the continued fraction is $C_n = 1/R_2(n)$. If $R_2(n) = N/D$ in reduced form, $C_n = D/N$.
The sequence $a(n)$ is the denominator of the final fraction, which is $\vert N \vert$.
-/
noncomputable def A363347 (n : ℕ) : ℕ :=
  if n ≤ 2 then 0 -- The sequence is indexed starting from $n=3$.
  else
    let R2 := continued_fraction_denominator n 2
    R2.num.natAbs

/-! Integer companion sequence. -/

/-- Integer sequence implementing the same recurrence as the continued fraction numerators:
`pseq n (n+1) = -1`, `pseq n n = 4`, and
`pseq n k = k * pseq n (k+1) - (k+1) * pseq n (k+2)` for `k < n`. -/
def pseq (n k : ℕ) : ℤ :=
  if n + 1 ≤ k then
    if k = n + 1 then (-1 : ℤ) else 0
  else if k = n then
    (4 : ℤ)
  else
    (k : ℤ) * pseq n (k + 1) - (k + 1 : ℤ) * pseq n (k + 2)
termination_by n + 1 - k

lemma pseq_succ (n : ℕ) : pseq n (n + 1) = -1 := by
  rw [pseq, if_pos le_rfl, if_pos rfl]

lemma pseq_n (n : ℕ) : pseq n n = 4 := by
  rw [pseq, if_neg (by omega : ¬ n + 1 ≤ n), if_pos rfl]

lemma pseq_rec (n k : ℕ) (hk : k < n) :
    pseq n k = (k : ℤ) * pseq n (k + 1) - (k + 1 : ℤ) * pseq n (k + 2) := by
  rw [pseq, if_neg (by omega : ¬ n + 1 ≤ k), if_neg (by omega : ¬ k = n)]

lemma pseq_pred (n : ℕ) (hn : 1 ≤ n) : pseq n (n - 1) = 5 * (n : ℤ) - 4 := by
  rw [pseq_rec n (n - 1) (by omega)]
  have h1 : n - 1 + 1 = n := by omega
  have h2 : n - 1 + 2 = n + 1 := by omega
  rw [h1, h2, pseq_n, pseq_succ]
  have : (n - 1 : ℕ) = (n : ℤ) - 1 := by omega
  rw [this]
  ring

/-- Auxiliary integer sequence `hseq n k = (k-1) * (k-3)! * pseq n k`. -/
def hseq (n k : ℕ) : ℤ :=
  (k - 1 : ℤ) * ((k - 3).factorial : ℤ) * pseq n k

/-- Closed-form right-hand side for `hseq`. -/
def hRHS (n k : ℕ) : ℤ :=
  4 * (n - 1 : ℤ) * ((n - 3).factorial : ℤ) +
    ((n : ℤ) ^ 2 + 2 * n - 4) *
      ((∑ i ∈ Finset.range (n - 3), (i.factorial : ℤ)) -
        ∑ i ∈ Finset.range (k - 3), (i.factorial : ℤ))

lemma factorial_succ_cast (t : ℕ) :
    ((t + 1).factorial : ℤ) = (t + 1 : ℤ) * (t.factorial : ℤ) := by
  rw [factorial_succ]
  push_cast
  ring

lemma hseq_rec (n k : ℕ) (hk3 : 3 ≤ k) (hkn : k < n) :
    (k - 2 : ℤ) * hseq n k = (k - 1 : ℤ) * hseq n (k + 1) - hseq n (k + 2) := by
  have fac_k2 : ((k - 2).factorial : ℤ) = (k - 2 : ℤ) * ((k - 3).factorial : ℤ) := by
    have : k - 2 = (k - 3) + 1 := by omega
    rw [this, factorial_succ_cast]
    have : ((k - 3 : ℕ) + 1 : ℤ) = (k : ℤ) - 2 := by omega
    rw [this]
  have fac_k1 : ((k - 1).factorial : ℤ) = (k - 1 : ℤ) * (k - 2 : ℤ) * ((k - 3).factorial : ℤ) := by
    have : k - 1 = (k - 2) + 1 := by omega
    rw [this, factorial_succ_cast, fac_k2]
    have : ((k - 2 : ℕ) + 1 : ℤ) = (k : ℤ) - 1 := by omega
    rw [this]
    ring
  -- Expand both sides with the definitions, keeping `pseq n (k+1)` and `pseq n (k+2)` as atoms.
  have hleft :
      (k - 2 : ℤ) * hseq n k =
        (k - 2 : ℤ) * (k - 1 : ℤ) * ((k - 3).factorial : ℤ) *
          ((k : ℤ) * pseq n (k + 1) - (k + 1 : ℤ) * pseq n (k + 2)) := by
    unfold hseq
    rw [pseq_rec n k hkn]
    ring
  have hright :
      (k - 1 : ℤ) * hseq n (k + 1) - hseq n (k + 2) =
        (k - 1 : ℤ) * (k : ℤ) * ((k - 2).factorial : ℤ) * pseq n (k + 1) -
          (k + 1 : ℤ) * ((k - 1).factorial : ℤ) * pseq n (k + 2) := by
    unfold hseq
    have h13 : (k + 1 - 3 : ℕ) = k - 2 := by omega
    have h23 : (k + 2 - 3 : ℕ) = k - 1 := by omega
    have hsub1 : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by omega
    have hsub2 : ((k + 2 : ℕ) : ℤ) - 1 = (k : ℤ) + 1 := by omega
    rw [h13, h23, hsub1, hsub2]
    ring
  rw [hleft, hright, fac_k2, fac_k1]
  ring

lemma hRHS_rec (n k : ℕ) (hk3 : 3 ≤ k) :
    (k - 2 : ℤ) * hRHS n k = (k - 1 : ℤ) * hRHS n (k + 1) - hRHS n (k + 2) := by
  have split1 : ∑ i ∈ Finset.range (k + 1 - 3), (i.factorial : ℤ) =
      ∑ i ∈ Finset.range (k - 3), (i.factorial : ℤ) + ((k - 3).factorial : ℤ) := by
    have : k + 1 - 3 = (k - 3) + 1 := by omega
    rw [this, Finset.sum_range_succ]
  have split2 : ∑ i ∈ Finset.range (k + 2 - 3), (i.factorial : ℤ) =
      ∑ i ∈ Finset.range (k - 3), (i.factorial : ℤ) + ((k - 3).factorial : ℤ) +
        ((k - 2).factorial : ℤ) := by
    have : k + 2 - 3 = (k - 2) + 1 := by omega
    rw [this, Finset.sum_range_succ]
    have : k - 2 = (k - 3) + 1 := by omega
    rw [this, Finset.sum_range_succ]
  have fac_k2 : ((k - 2).factorial : ℤ) = (k - 2 : ℤ) * ((k - 3).factorial : ℤ) := by
    have : k - 2 = (k - 3) + 1 := by omega
    rw [this, factorial_succ_cast]
    have : ((k - 3 : ℕ) + 1 : ℤ) = (k : ℤ) - 2 := by omega
    rw [this]
  unfold hRHS
  rw [split1, split2, fac_k2]
  ring

lemma hseq_at_n (n : ℕ) (hn : 3 ≤ n) :
    hseq n n = 4 * (n - 1 : ℤ) * ((n - 3).factorial : ℤ) := by
  unfold hseq
  rw [pseq_n]
  have : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  -- hseq uses (n - 1 : ℤ) which is already Int sub
  ring

lemma hseq_at_succ (n : ℕ) :
    hseq n (n + 1) = - (n : ℤ) * ((n - 2).factorial : ℤ) := by
  unfold hseq
  rw [pseq_succ]
  have h2 : n + 1 - 3 = n - 2 := by omega
  rw [h2]
  have : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by omega
  rw [this]
  ring

lemma hRHS_at_n (n : ℕ) :
    hRHS n n = 4 * (n - 1 : ℤ) * ((n - 3).factorial : ℤ) := by
  unfold hRHS
  simp

lemma hRHS_at_succ (n : ℕ) (hn : 3 ≤ n) :
    hRHS n (n + 1) = - (n : ℤ) * ((n - 2).factorial : ℤ) := by
  unfold hRHS
  have hsum : ∑ i ∈ Finset.range (n + 1 - 3), (i.factorial : ℤ) =
      ∑ i ∈ Finset.range (n - 3), (i.factorial : ℤ) + ((n - 3).factorial : ℤ) := by
    have : n + 1 - 3 = (n - 3) + 1 := by omega
    rw [this, Finset.sum_range_succ]
  rw [hsum]
  have fac : ((n - 2).factorial : ℤ) = (n - 2 : ℤ) * ((n - 3).factorial : ℤ) := by
    have : n - 2 = (n - 3) + 1 := by omega
    rw [this, factorial_succ_cast]
    have : ((n - 3 : ℕ) + 1 : ℤ) = (n : ℤ) - 2 := by omega
    rw [this]
  rw [fac]
  ring

lemma hseq_eq_hRHS (n k : ℕ) (hn : 5 ≤ n) (hk3 : 3 ≤ k) (hkn : k ≤ n + 1) :
    hseq n k = hRHS n k := by
  suffices ∀ d k, n + 1 - k = d → 3 ≤ k → k ≤ n + 1 → hseq n k = hRHS n k by
    exact this (n + 1 - k) k rfl hk3 hkn
  intro d
  refine Nat.strongRecOn d fun d ih k heq hk3 hkn => ?_
  have hn3 : 3 ≤ n := by omega
  by_cases h1 : k = n + 1
  · rw [h1, hseq_at_succ, hRHS_at_succ n hn3]
  · by_cases h2 : k = n
    · rw [h2, hseq_at_n n hn3, hRHS_at_n]
    · have hklt : k < n := by omega
      have ih1 : hseq n (k + 1) = hRHS n (k + 1) :=
        ih (n + 1 - (k + 1)) (by omega) (k + 1) rfl (by omega) (by omega)
      have ih2 : hseq n (k + 2) = hRHS n (k + 2) :=
        ih (n + 1 - (k + 2)) (by omega) (k + 2) rfl (by omega) (by omega)
      have lhs := hseq_rec n k hk3 hklt
      have rhs := hRHS_rec n k hk3
      have hk2z : (k - 2 : ℤ) ≠ 0 := by omega
      apply Int.eq_of_mul_eq_mul_left hk2z
      rw [lhs, rhs, ih1, ih2]

lemma P_pos (n : ℕ) (hn : 2 ≤ n) : (0 : ℤ) < (n : ℤ) ^ 2 + 2 * n - 4 := by
  nlinarith

lemma pseq_two (n : ℕ) (hn : 5 ≤ n) :
    pseq n 2 = (n : ℤ) ^ 2 + 2 * n - 4 := by
  have hrec : pseq n 2 = 2 * pseq n 3 - 3 * pseq n 4 := by
    rw [pseq_rec n 2 (by omega)]
    ring
  have h3 : hseq n 3 = hRHS n 3 := hseq_eq_hRHS n 3 hn (by omega) (by omega)
  have h4 : hseq n 4 = hRHS n 4 := hseq_eq_hRHS n 4 hn (by omega) (by omega)
  have hs3 : hseq n 3 = 2 * pseq n 3 := by
    unfold hseq; ring
  have hs4 : hseq n 4 = 3 * pseq n 4 := by
    unfold hseq; ring
  have hdiff : pseq n 2 = hseq n 3 - hseq n 4 := by
    rw [hrec, hs3, hs4]
  rw [hdiff, h3, h4]
  unfold hRHS
  have : (3 - 3 : ℕ) = 0 := rfl
  have : (4 - 3 : ℕ) = 1 := rfl
  simp [this]
  ring

lemma sum_factorial_even (n : ℕ) (hn : 5 ≤ n) :
    2 ∣ ∑ i ∈ Finset.range (n - 3), i.factorial := by
  have heq : n - 3 = (n - 5) + 2 := by omega
  rw [heq]
  have split :
      ∑ i ∈ Finset.range ((n - 5) + 2), i.factorial =
        Nat.factorial 0 + Nat.factorial 1 + ∑ i ∈ Finset.range (n - 5), (i + 2).factorial := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    ring
  rw [split]
  change 2 ∣ 1 + 1 + ∑ i ∈ Finset.range (n - 5), (i + 2).factorial
  apply dvd_add
  · exact ⟨1, rfl⟩
  · apply Finset.dvd_sum
    intro i hi
    exact Nat.dvd_factorial (by omega : 0 < 2) (by omega : 2 ≤ i + 2)

lemma pseq_three (n : ℕ) (hn : 5 ≤ n) :
    pseq n 3 =
      2 * (n - 1 : ℤ) * ((n - 3).factorial : ℤ) +
        ((n : ℤ) ^ 2 + 2 * n - 4) *
          ↑((∑ i ∈ Finset.range (n - 3), i.factorial) / 2) := by
  have h : hseq n 3 = hRHS n 3 := hseq_eq_hRHS n 3 hn (by omega) (by omega)
  have hs : hseq n 3 = 2 * pseq n 3 := by
    unfold hseq; ring
  have hr : hRHS n 3 =
      4 * (n - 1 : ℤ) * ((n - 3).factorial : ℤ) +
        ((n : ℤ) ^ 2 + 2 * n - 4) * ∑ i ∈ Finset.range (n - 3), (i.factorial : ℤ) := by
    unfold hRHS
    simp
  have heven := sum_factorial_even n hn
  have hcast :
      (∑ i ∈ Finset.range (n - 3), (i.factorial : ℤ)) =
        (2 : ℤ) * ↑((∑ i ∈ Finset.range (n - 3), i.factorial) / 2) := by
    have hsum : (∑ i ∈ Finset.range (n - 3), (i.factorial : ℤ)) =
        ↑(∑ i ∈ Finset.range (n - 3), i.factorial) := by
      simp
    rw [hsum, ← Nat.cast_two, ← Nat.cast_mul, Nat.mul_div_cancel' heven]
  have heq : 2 * pseq n 3 =
      4 * (n - 1 : ℤ) * ((n - 3).factorial : ℤ) +
        ((n : ℤ) ^ 2 + 2 * n - 4) * ∑ i ∈ Finset.range (n - 3), (i.factorial : ℤ) := by
    rw [← hs, h, hr]
  rw [hcast] at heq
  apply Int.eq_of_mul_eq_mul_left (by norm_num : (2 : ℤ) ≠ 0)
  convert heq using 1
  ring

lemma pseq_ne_zero (n k : ℕ) (hn : 5 ≤ n) (hk3 : 3 ≤ k) (hkn : k ≤ n + 1) :
    pseq n k ≠ 0 := by
  have hh := hseq_eq_hRHS n k hn hk3 hkn
  intro hz
  have hseq0 : hseq n k = 0 := by
    unfold hseq; simp [hz]
  rw [hh] at hseq0
  by_cases hkle : k ≤ n
  · have hP : (0 : ℤ) < (n : ℤ) ^ 2 + 2 * n - 4 := P_pos n (by omega)
    have hlead : (0 : ℤ) < 4 * (n - 1 : ℤ) * ((n - 3).factorial : ℤ) := by
      have a : (0 : ℤ) < n - 1 := by omega
      have b : (0 : ℤ) < (n - 3).factorial := by exact_mod_cast factorial_pos (n - 3)
      nlinarith
    have hdiff :
        0 ≤ (∑ i ∈ Finset.range (n - 3), (i.factorial : ℤ)) -
          ∑ i ∈ Finset.range (k - 3), (i.factorial : ℤ) := by
      have : k - 3 ≤ n - 3 := by omega
      refine sub_nonneg.mpr ?_
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono this) ?_
      intro i _ _
      exact Int.natCast_nonneg _
    have : (0 : ℤ) < hRHS n k := by
      unfold hRHS
      nlinarith
    linarith
  · have hk' : k = n + 1 := by omega
    subst hk'
    rw [hRHS_at_succ n (by omega)] at hseq0
    have : (n : ℤ) * ((n - 2).factorial : ℤ) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · have hn0 : (n : ℤ) ≠ 0 := by omega
      exact hn0 h
    · exact (factorial_ne_zero (n - 2)) (Int.natCast_eq_zero.mp h)

lemma cfd_base (n : ℕ) (hn : 3 ≤ n) :
    continued_fraction_denominator n (n - 1) = ((n - 1 : ℕ) : ℚ) + (n : ℚ) / 4 := by
  unfold continued_fraction_denominator
  have h1 : ¬ n ≤ 2 := by omega
  have h2 : 2 ≤ n - 1 ∧ n - 1 ≤ n - 1 := by omega
  simp [h1, h2]

lemma cfd_rec (n k : ℕ) (hn : 3 ≤ n) (hk2 : 2 ≤ k) (hk : k < n - 1) :
    continued_fraction_denominator n k =
      (k : ℚ) - (k + 1 : ℚ) / continued_fraction_denominator n (k + 1) := by
  conv_lhs => unfold continued_fraction_denominator
  have h1 : ¬ n ≤ 2 := by omega
  have h2 : 2 ≤ k ∧ k ≤ n - 1 := by omega
  have h3 : ¬ k = n - 1 := by omega
  simp [h1, h2, h3]

lemma cfd_eq_pseq (n k : ℕ) (hn : 5 ≤ n) (hk2 : 2 ≤ k) (hk : k ≤ n - 1) :
    continued_fraction_denominator n k = (pseq n k : ℚ) / (pseq n (k + 1) : ℚ) := by
  suffices ∀ d k, n - 1 - k = d → 2 ≤ k → k ≤ n - 1 →
      continued_fraction_denominator n k = (pseq n k : ℚ) / (pseq n (k + 1) : ℚ) by
    exact this (n - 1 - k) k rfl hk2 hk
  intro d
  refine Nat.strongRecOn d fun d ih k heq hk2 hk => ?_
  have hn3 : 3 ≤ n := by omega
  by_cases hbase : k = n - 1
  · rw [hbase, cfd_base n hn3]
    have hnp : n - 1 + 1 = n := by omega
    rw [pseq_pred n (by omega), hnp, pseq_n]
    have hn1 : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
      have : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
      exact_mod_cast this
    have hcast : ((5 * (n : ℤ) - 4 : ℤ) : ℚ) = 5 * (n : ℚ) - 4 := by
      push_cast
      ring
    rw [hcast, hn1]
    field
    try ring
  · have hklt : k < n - 1 := by omega
    have ih' : continued_fraction_denominator n (k + 1) =
        (pseq n (k + 1) : ℚ) / (pseq n (k + 2) : ℚ) :=
      ih (n - 1 - (k + 1)) (by omega) (k + 1) rfl (by omega) (by omega)
    rw [cfd_rec n k hn3 hk2 hklt, ih']
    have hne : (pseq n (k + 1) : ℚ) ≠ 0 := by
      exact_mod_cast pseq_ne_zero n (k + 1) hn (by omega) (by omega)
    have hp := pseq_rec n k (by omega : k < n)
    have hpq : (pseq n k : ℚ) =
        (k : ℚ) * (pseq n (k + 1) : ℚ) - (k + 1 : ℚ) * (pseq n (k + 2) : ℚ) := by
      exact_mod_cast hp
    field [hne]
    rw [hpq]
    try ring

lemma A363347_of_ge_three (n : ℕ) (hn : 3 ≤ n) :
    A363347 n = (continued_fraction_denominator n 2).num.natAbs := by
  unfold A363347
  have : ¬ n ≤ 2 := by omega
  simp [this]

lemma num_rat_div_of_pos_ne {a b : ℤ} (ha : 0 < a) (hb : b ≠ 0) :
    ((a : ℚ) / (b : ℚ)).num.natAbs = a.natAbs / Int.gcd a b := by
  rw [← Rat.divInt_eq_div, Rat.num_divInt]
  rw [show Int.gcd a b = Int.gcd b a from Int.gcd_comm a b]
  cases lt_or_gt_of_ne hb with
  | inl hneg =>
    have hs : b.sign = -1 := Int.sign_eq_neg_one_of_neg hneg
    rw [hs]
    simp
    have hdvd : ((b.gcd a : ℤ) ∣ a) := Int.gcd_dvd_right b a
    rw [Int.natAbs_ediv_of_dvd (Int.dvd_neg.mpr hdvd), Int.natAbs_neg]
    simp [Int.natAbs_ediv_of_dvd hdvd]
  | inr hpos =>
    have hs : b.sign = 1 := Int.sign_eq_one_of_pos hpos
    rw [hs]
    simp
    rw [Int.natAbs_ediv_of_dvd (Int.gcd_dvd_right b a)]
    simp

lemma P_natAbs (n : ℕ) (hn : 2 ≤ n) :
    ((n : ℤ) ^ 2 + 2 * n - 4).natAbs = n ^ 2 + 2 * n - 4 := by
  have hle : 4 ≤ n ^ 2 + 2 * n := by
    have : 2 ≤ n := hn
    have : 4 ≤ n * n + 2 * n := by nlinarith
    simpa [pow_two] using this
  have : (n : ℤ) ^ 2 + 2 * (n : ℤ) - 4 = ((n ^ 2 + 2 * n - 4 : ℕ) : ℤ) := by
    rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_mul]
    simp [pow_two]
    try ring
  rw [this, Int.natAbs_natCast]

lemma A363347_formula (n : ℕ) (hn : 5 ≤ n) :
    A363347 n =
      (n ^ 2 + 2 * n - 4) /
        Nat.gcd (n ^ 2 + 2 * n - 4) (2 * (n - 1) * (n - 3).factorial) := by
  have hn3 : 3 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  rw [A363347_of_ge_three n hn3, cfd_eq_pseq n 2 hn (by omega) (by omega)]
  have h2 := pseq_two n hn
  have h3 := pseq_three n hn
  have h2pos : (0 : ℤ) < pseq n 2 := by
    rw [h2]; exact P_pos n hn2
  have h3ne : pseq n 3 ≠ 0 := pseq_ne_zero n 3 hn (by omega) (by omega)
  rw [num_rat_div_of_pos_ne h2pos h3ne, h2, P_natAbs n hn2]
  have hg : Int.gcd ((n : ℤ) ^ 2 + 2 * n - 4) (pseq n 3) =
      Int.gcd ((n : ℤ) ^ 2 + 2 * n - 4) (2 * (n - 1 : ℤ) * ((n - 3).factorial : ℤ)) := by
    rw [h3, Int.gcd_add_mul_left_right]
  rw [hg]
  have hcast : Int.gcd ((n : ℤ) ^ 2 + 2 * n - 4)
      (2 * (n - 1 : ℤ) * ((n - 3).factorial : ℤ)) =
      Nat.gcd (n ^ 2 + 2 * n - 4) (2 * (n - 1) * (n - 3).factorial) := by
    rw [Int.gcd]
    have hP := P_natAbs n hn2
    have hQ : (2 * (n - 1 : ℤ) * ((n - 3).factorial : ℤ)).natAbs =
        2 * (n - 1) * (n - 3).factorial := by
      have : 0 ≤ (2 : ℤ) * (n - 1 : ℤ) * ((n - 3).factorial : ℤ) := by
        have : (0 : ℤ) ≤ n - 1 := by omega
        have : (0 : ℤ) ≤ (n - 3).factorial := Int.natCast_nonneg _
        nlinarith
      have hn1 : (n - 1 : ℤ) = ↑(n - 1) := by omega
      have heq : 2 * (n - 1 : ℤ) * ((n - 3).factorial : ℤ) =
          ↑(2 * (n - 1) * (n - 3).factorial) := by
        rw [hn1]
        simp
      rw [heq, Int.natAbs_natCast]
    rw [hP, hQ]
  rw [hcast]

lemma prime_ge_eleven {p : ℕ} (hp : p.Prime)
    (hmod : p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10]) : 11 ≤ p := by
  have hpmod : p % 10 = 1 ∨ p % 10 = 9 := hmod
  rcases hpmod with h | h
  · have : p = 10 * (p / 10) + 1 := by
      have := Nat.div_add_mod p 10
      omega
    have : p / 10 ≠ 0 := by
      intro hz
      have : p = 1 := by omega
      exact hp.ne_one this
    omega
  · have : p = 10 * (p / 10) + 9 := by
      have := Nat.div_add_mod p 10
      omega
    have : p / 10 ≠ 0 := by
      intro hz
      have hp9 : p = 9 := by omega
      have : ¬ Nat.Prime 9 := by decide
      exact this (hp9 ▸ hp)
    omega

lemma isSquare_five {p : ℕ} [hp : Fact p.Prime]
    (hmod : p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10]) : IsSquare (5 : ZMod p) := by
  have hprime : p.Prime := hp.out
  have hp2 : p ≠ 2 := by
    intro h
    subst h
    have : ¬ (2 ≡ 1 [MOD 10] ∨ 2 ≡ 9 [MOD 10]) := by decide
    exact this hmod
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h54 : (5 : ℕ) % 4 = 1 := by norm_num
  -- `IsSquare (p : ZMod 5) ↔ IsSquare (5 : ZMod p)`
  refine (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := p) h54 hp2).mp ?_
  have hmod5 : p ≡ 1 [MOD 5] ∨ p ≡ 4 [MOD 5] := by
    rcases hmod with h | h
    · left
      have : p % 10 = 1 := h
      have : p % 5 = 1 := by
        have := Nat.mod_mod_of_dvd p (show 5 ∣ 10 by norm_num)
        omega
      exact this
    · right
      have : p % 10 = 9 := h
      have : p % 5 = 4 := by
        have := Nat.mod_mod_of_dvd p (show 5 ∣ 10 by norm_num)
        omega
      exact this
  rcases hmod5 with h | h
  · refine ⟨(1 : ZMod 5), ?_⟩
    have : (p : ZMod 5) = 1 := (ZMod.natCast_eq_natCast_iff p 1 5).mpr h
    rw [this]
    rfl
  · refine ⟨(2 : ZMod 5), ?_⟩
    have : (p : ZMod 5) = 4 := (ZMod.natCast_eq_natCast_iff p 4 5).mpr h
    rw [this]
    rfl

lemma A363347_three : A363347 3 = 11 := by
  unfold A363347
  simp
  have h : continued_fraction_denominator 3 2 = (2 : ℚ) + (3 : ℚ) / 4 := by
    unfold continued_fraction_denominator
    simp
  rw [h]
  have heq : (2 : ℚ) + 3 / 4 = (11 : ℚ) / 4 := by
    field
    try ring
  rw [heq]
  have := num_rat_div_of_pos_ne (a := 11) (b := 4) (by norm_num) (by norm_num)
  simpa using this

lemma P_int_cast (n : ℕ) (hn : 2 ≤ n) :
    (n : ℤ) ^ 2 + 2 * n - 4 = ((n ^ 2 + 2 * n - 4 : ℕ) : ℤ) := by
  have hle : 4 ≤ n ^ 2 + 2 * n := by
    have : 4 ≤ n * n + 2 * n := by nlinarith
    simpa [pow_two] using this
  rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_mul]
  simp [pow_two]
  try ring

lemma dvd_P_of_sq (p n : ℕ)
    (h : ((n : ZMod p) + 1) ^ 2 = 5) :
    (p : ℤ) ∣ (n : ℤ) ^ 2 + 2 * n - 4 := by
  have : (((n : ℤ) + 1) ^ 2 - 5 : ℤ) ≡ 0 [ZMOD p] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    rw [sub_eq_zero]
    simpa using h
  have : (p : ℤ) ∣ ((n : ℤ) + 1) ^ 2 - 5 := Int.modEq_zero_iff_dvd.1 this
  convert this using 1
  ring

lemma n_of_root_ge_three {p n : ℕ} (hp11 : 11 ≤ p)
    (hdiv : (p : ℤ) ∣ (n : ℤ) ^ 2 + 2 * n - 4) : 3 ≤ n := by
  by_contra h
  have hnle : n ≤ 2 := by omega
  have habs : ((n : ℤ) ^ 2 + 2 * n - 4).natAbs ≤ 4 := by
    interval_cases n <;> norm_num
  have hne : (n : ℤ) ^ 2 + 2 * n - 4 ≠ 0 := by
    interval_cases n <;> norm_num
  have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv
    (lt_of_le_of_lt habs (by omega : (4 : ℕ) < p))
  exact hne this

lemma n_ne_four {p n : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (hdiv : (p : ℤ) ∣ (n : ℤ) ^ 2 + 2 * n - 4) : n ≠ 4 := by
  intro hn4
  subst hn4
  have h20 : (p : ℤ) ∣ (20 : ℤ) := by simpa using hdiv
  have : p ∣ 20 := Int.natCast_dvd_natCast.mp h20
  have : p ∣ 4 * 5 := this
  rw [hp.dvd_mul] at this
  rcases this with h4 | h5
  · rw [show (4 = 2 * 2) from rfl, hp.dvd_mul] at h4
    have hp2 : p ∣ 2 := by tauto
    have : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp2
    omega
  · have hp5 : p = 5 :=
      (Nat.dvd_prime Nat.prime_five).1 h5 |>.resolve_left (by omega)
    omega

lemma p_dvd_eval {p n k : ℕ} (hnp : n = p - k) (hk : k ≤ p)
    (hdiv : (p : ℤ) ∣ (n : ℤ) ^ 2 + 2 * n - 4) :
    (p : ℤ) ∣ ((k : ℤ) ^ 2 - 2 * k - 4) := by
  have hn : (n : ℤ) = (p : ℤ) - k := by
    rw [hnp]
    omega
  rw [hn] at hdiv
  have h' : (p : ℤ) ∣ ((p : ℤ) - k) ^ 2 + 2 * ((p : ℤ) - k) - 4 := hdiv
  have hexp : ((p : ℤ) - k) ^ 2 + 2 * ((p : ℤ) - k) - 4 =
      (p : ℤ) * (p - 2 * k + 2) + (k ^ 2 - 2 * k - 4) := by ring
  rw [hexp] at h'
  exact (Int.dvd_add_right (dvd_mul_right _ _)).mp h'

lemma int_dvd_to_nat {p k : ℕ} {a : ℤ}
    (h : (p : ℤ) ∣ a) (ha : a = (k : ℤ) ∨ a = - (k : ℤ)) : p ∣ k := by
  rcases ha with hpos | hneg
  · rw [hpos] at h
    exact Int.natCast_dvd_natCast.mp h
  · rw [hneg] at h
    exact Int.natCast_dvd_natCast.mp (Int.dvd_neg.mp h)

lemma p_ge_n_add_six {p n : ℕ} (_hp : p.Prime) (hp11 : 11 ≤ p)
    (_hn5 : 5 ≤ n) (hnlt : n < p)
    (hdiv : (p : ℤ) ∣ (n : ℤ) ^ 2 + 2 * n - 4)
    (hsp : ¬ (n = 6 ∧ p = 11)) : n + 6 ≤ p := by
  by_contra hlt
  have : p ≤ n + 5 := by omega
  have : n + 1 ≤ p := by omega
  have hcases : p = n + 1 ∨ p = n + 2 ∨ p = n + 3 ∨ p = n + 4 ∨ p = n + 5 := by
    omega
  rcases hcases with hp1 | hp2 | hp3 | hp4 | hp5
  · have h := p_dvd_eval (n := n) (p := p) (k := 1) (by omega) (by omega) hdiv
    have hneg : (p : ℤ) ∣ (-5 : ℤ) := by simpa using h
    have : p ∣ 5 :=
      int_dvd_to_nat hneg (Or.inr (by norm_num))
    have : p = 5 :=
      (Nat.dvd_prime Nat.prime_five).1 this |>.resolve_left (by omega)
    omega
  · have h := p_dvd_eval (n := n) (p := p) (k := 2) (by omega) (by omega) hdiv
    have hneg : (p : ℤ) ∣ (-4 : ℤ) := by simpa using h
    have : p ∣ 4 :=
      int_dvd_to_nat hneg (Or.inr (by norm_num))
    have : p ≤ 4 := Nat.le_of_dvd (by norm_num) this
    omega
  · have h := p_dvd_eval (n := n) (p := p) (k := 3) (by omega) (by omega) hdiv
    have hneg : (p : ℤ) ∣ (-1 : ℤ) := by simpa using h
    have : p ∣ 1 :=
      int_dvd_to_nat hneg (Or.inr (by norm_num))
    have : p ≤ 1 := Nat.le_of_dvd (by norm_num) this
    omega
  · have h := p_dvd_eval (n := n) (p := p) (k := 4) (by omega) (by omega) hdiv
    have hpos : (p : ℤ) ∣ (4 : ℤ) := by simpa using h
    have : p ∣ 4 :=
      int_dvd_to_nat hpos (Or.inl rfl)
    have : p ≤ 4 := Nat.le_of_dvd (by norm_num) this
    omega
  · have h := p_dvd_eval (n := n) (p := p) (k := 5) (by omega) (by omega) hdiv
    have hpos : (p : ℤ) ∣ (11 : ℤ) := by simpa using h
    have : p ∣ 11 :=
      int_dvd_to_nat hpos (Or.inl rfl)
    have : p = 11 :=
      (Nat.dvd_prime (by decide : Nat.Prime 11)).1 this |>.resolve_left (by omega)
    have : n = 6 := by omega
    exact hsp ⟨‹n = 6›, ‹p = 11›⟩

lemma P_lt_of_ge_five (n : ℕ) (hn : 5 ≤ n) :
    n ^ 2 + 2 * n - 4 < (n + 6) * (n - 2) := by
  have lhs : ((n ^ 2 + 2 * n - 4 : ℕ) : ℤ) = (n : ℤ) ^ 2 + 2 * n - 4 :=
    (P_int_cast n (by omega)).symm
  have rhs : (((n + 6) * (n - 2) : ℕ) : ℤ) =
      (n + 6 : ℤ) * ((n : ℤ) - 2) := by
    rw [Nat.cast_mul, Nat.cast_add]
    have : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
    rw [this]
    simp
  have : ((n ^ 2 + 2 * n - 4 : ℕ) : ℤ) < ((n + 6) * (n - 2) : ℕ) := by
    rw [lhs, rhs]
    nlinarith
  exact Nat.cast_lt.mp this

lemma p_dvd_P_nat {p n : ℕ} (hn : 2 ≤ n)
    (hdiv : (p : ℤ) ∣ (n : ℤ) ^ 2 + 2 * n - 4) :
    p ∣ n ^ 2 + 2 * n - 4 := by
  rwa [← Int.natCast_dvd_natCast, ← P_int_cast n hn]

/-- A363347 Conjecture 2: The sequence contains all prime numbers which end with a 1 or 9. -/
theorem oeis_363347_conjecture_2 :
  ∀ p : ℕ,
    (p.Prime ∧ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) →
    ∃ n : ℕ, A363347 n = p := by
  intro p ⟨hp, hmod⟩
  have hp11 : 11 ≤ p := prime_ge_eleven hp hmod
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, hr⟩ := isSquare_five (p := p) hmod
  set n := (r - 1).val with hnval
  have hnlt : n < p := ZMod.val_lt (r - 1)
  have hcong : ((n : ZMod p) + 1) ^ 2 = 5 := by
    rw [hnval, ZMod.natCast_zmod_val, sub_add_cancel, pow_two]
    exact hr.symm
  have hdiv : (p : ℤ) ∣ (n : ℤ) ^ 2 + 2 * n - 4 := dvd_P_of_sq p n hcong
  have hn3 : 3 ≤ n := n_of_root_ge_three hp11 hdiv
  by_cases hn_eq3 : n = 3
  · have h11 : (p : ℤ) ∣ (11 : ℤ) := by
      rw [hn_eq3] at hdiv
      simpa using hdiv
    have : p ∣ 11 := Int.natCast_dvd_natCast.mp h11
    have hp11eq : p = 11 :=
      (Nat.dvd_prime (by decide : Nat.Prime 11)).1 this |>.resolve_left (by omega)
    refine ⟨3, ?_⟩
    rw [hp11eq]
    exact A363347_three
  · have hn4 : n ≠ 4 := n_ne_four hp hp11 hdiv
    have hn5 : 5 ≤ n := by omega
    have hform := A363347_formula n hn5
    have hpdvd : p ∣ n ^ 2 + 2 * n - 4 := p_dvd_P_nat (by omega) hdiv
    set P := n ^ 2 + 2 * n - 4 with hPdef
    set m := P / p with hmdef
    have hPpos : 0 < P := by
      have : 4 < n * n + 2 * n := by nlinarith
      have : 4 < n ^ 2 + 2 * n := by simpa [pow_two] using this
      omega
    have hmpos : 0 < m := Nat.div_pos (Nat.le_of_dvd hPpos hpdvd) hp.pos
    have hPm : P = p * m := (Nat.mul_div_cancel' hpdvd).symm
    have hcop : Nat.Coprime p (2 * (n - 1) * (n - 3).factorial) := by
      rw [hp.coprime_iff_not_dvd]
      intro hd
      have hsplit := (hp.dvd_mul).1 hd
      rcases hsplit with h2n1 | hfac
      · have hsplit2 := (hp.dvd_mul).1 h2n1
        rcases hsplit2 with h2 | hn1
        · have : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
          omega
        · have : p ≤ n - 1 := Nat.le_of_dvd (by omega) hn1
          omega
      · have : p ≤ n - 3 := (hp.dvd_factorial).1 hfac
        omega
    have hmdvd : m ∣ 2 * (n - 1) * (n - 3).factorial := by
      by_cases hsp : n = 6 ∧ p = 11
      · rcases hsp with ⟨hn6, hp11eq⟩
        have hm4 : m = 4 := by
          rw [hmdef, hPdef, hn6, hp11eq]
          norm_num
        rw [hm4, hn6]
        decide
      · have hge : n + 6 ≤ p := p_ge_n_add_six hp hp11 hn5 hnlt hdiv hsp
        have hltP : P < (n + 6) * (n - 2) := by
          simpa [hPdef] using P_lt_of_ge_five n hn5
        have hlt2 : P < p * (n - 2) :=
          lt_of_lt_of_le hltP (Nat.mul_le_mul_right (n - 2) hge)
        have hm_lt : m < n - 2 := by
          rw [hmdef]
          exact Nat.div_lt_of_lt_mul hlt2
        have hm_le : m ≤ n - 3 := by omega
        have : m ∣ (n - 3).factorial := Nat.dvd_factorial hmpos hm_le
        exact Dvd.dvd.mul_left this _
    have hgcd : Nat.gcd P (2 * (n - 1) * (n - 3).factorial) = m := by
      rw [hPm]
      exact Nat.gcd_mul_of_coprime_of_dvd hcop hmdvd
    refine ⟨n, ?_⟩
    rw [hform, hgcd, hPm]
    exact Nat.mul_div_cancel p hmpos
