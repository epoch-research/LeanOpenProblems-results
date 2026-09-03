import Submission.FloorArithmetic

/-!
# Sublinearity of the fractional floor remainder

This independent extension does not import `Submission.Spec`.  The exceptional
intervals have fixed integer parameters; a coarse binomial estimate replaces
Stirling's formula.  No arithmetic infinitude claim is made here.
-/

namespace FloorSublinear

open FloorArithmetic

/-- A deliberately coarse multinomial bound, proved using only the binomial
bound `choose n k ≤ 2^n`. -/
lemma factorial_mul_le_exp (r k : ℕ) :
    (r * k).factorial ≤ k.factorial ^ r * 2 ^ (r * r * k) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hc := Nat.choose_le_two_pow (r * k + k) k
    calc
      ((r + 1) * k).factorial =
          (r * k + k).choose k * (r * k).factorial * k.factorial := by
        rw [Nat.add_choose_mul_factorial_mul_factorial, Nat.add_mul, one_mul]
      _ ≤ 2 ^ (r * k + k) * (k.factorial ^ r * 2 ^ (r * r * k)) * k.factorial :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul hc ih)
      _ = k.factorial ^ (r + 1) * 2 ^ (r * r * k + (r * k + k)) := by
        rw [pow_succ, pow_add]
        ring
      _ ≤ k.factorial ^ (r + 1) * 2 ^ ((r + 1) * (r + 1) * k) := by
        apply Nat.mul_le_mul_left
        apply Nat.pow_le_pow_right (by omega)
        nlinarith

/-- If a block extends a fixed proportion past `N`, its factorial denominator
beats `N!` by a factor `2^N`, uniformly in bounded `r`. -/
lemma factorial_ratio_exp_bound (N k r M L : ℕ)
    (hr : r ≤ M) (hk : k ≤ N) (hNk : N ≤ r * k)
    (hgap : N ≤ L * (r * k - N))
    (hlarge : 2 ^ ((M * M + 1) * L) ≤ N + 1) :
    N.factorial * 2 ^ N ≤ k.factorial ^ r := by
  have hexp : r * r * k ≤ M * M * N :=
    Nat.mul_le_mul (Nat.mul_le_mul hr hr) hk
  have hp : 2 ^ ((M * M + 1) * N) ≤ (N + 1) ^ (r * k - N) := by
    calc
      2 ^ ((M * M + 1) * N) ≤ 2 ^ (((M * M + 1) * L) * (r * k - N)) := by
        apply Nat.pow_le_pow_right (by omega)
        simpa [Nat.mul_assoc] using Nat.mul_le_mul_left (M * M + 1) hgap
      _ = (2 ^ ((M * M + 1) * L)) ^ (r * k - N) := by rw [pow_mul]
      _ ≤ (N + 1) ^ (r * k - N) := Nat.pow_le_pow_left hlarge _
  have hfac : N.factorial * (N + 1) ^ (r * k - N) ≤ (r * k).factorial := by
    simpa [Nat.add_sub_of_le hNk] using
      (Nat.factorial_mul_pow_le_factorial (m := N) (n := r * k - N))
  have hb : N.factorial * 2 ^ ((M * M + 1) * N) ≤
      k.factorial ^ r * 2 ^ (M * M * N) :=
    (Nat.mul_le_mul_left _ hp).trans
      (hfac.trans ((factorial_mul_le_exp r k).trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hexp))))
  have he : (M * M + 1) * N = N + M * M * N := by ring
  rw [he, pow_add, ← Nat.mul_assoc] at hb
  exact Nat.le_of_mul_le_mul_right hb (by positivity)

/-- Exceptional indices: a short initial interval and `M` short intervals
immediately to the right of `N/r`.  The intervals need not be disjoint. -/
def exceptional (N M L : ℕ) : Finset ℕ :=
  Finset.Icc 1 (N / M) ∪
    (Finset.Icc 1 M).biUnion
      (fun r => Finset.Icc (N / r + 1) (N / r + N / L + 1))

lemma exceptional_card_le (N M L : ℕ) :
    (exceptional N M L).card ≤ N / M + M * (N / L + 1) := by
  have hb : ((Finset.Icc 1 M).biUnion
      (fun r => Finset.Icc (N / r + 1) (N / r + N / L + 1))).card ≤
      M * (N / L + 1) := by
    apply (Finset.card_biUnion_le_card_mul _ _ (N / L + 1) ?_).trans_eq
    · simp [Nat.card_Icc]
    · intro r _
      simp [Nat.card_Icc]
      omega
  exact (Finset.card_union_le _ _).trans (by
    simpa [Nat.card_Icc] using Nat.add_le_add_left hb (N / M))

lemma outside_exceptional (N M L k : ℕ) (hM : 0 < M) (hL : 0 < L)
    (hk : 1 ≤ k) (hout : k ∉ exceptional N M L) :
    N / k + 1 ≤ M ∧ N ≤ L * ((N / k + 1) * k - N) := by
  have hsmall : N / M < k := by
    by_contra h
    apply hout
    exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨hk, by omega⟩)
  have hNM : N < M * k := by
    have := (Nat.div_lt_iff_lt_mul hM).mp hsmall
    simpa [Nat.mul_comm] using this
  have hrM : N / k + 1 ≤ M := by
    have := (Nat.div_lt_iff_lt_mul (by omega : 0 < k)).mpr hNM
    omega
  let r := N / k + 1
  have hr : 0 < r := Nat.succ_pos _
  have hNr : N < r * k := by
    simpa [r, Nat.mul_comm] using Nat.lt_mul_div_succ N (by omega : 0 < k)
  have hlow : N / r + 1 ≤ k := by
    have := (Nat.div_lt_iff_lt_mul hr).mpr (by simpa [Nat.mul_comm] using hNr)
    omega
  have hhigh : N / r + N / L + 1 < k := by
    by_contra h
    apply hout
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    exact ⟨r, Finset.mem_Icc.mpr ⟨hr, hrM⟩,
      Finset.mem_Icc.mpr ⟨hlow, by omega⟩⟩
  have hdivr := Nat.lt_mul_div_succ N hr
  have hdivL := Nat.lt_mul_div_succ N hL
  have hmul := Nat.mul_le_mul_left r (show N / r + N / L + 2 ≤ k by omega)
  have hbase : N / L + 1 ≤ r * k - N := by
    have : r * (N / L + 1) ≥ N / L + 1 := Nat.le_mul_of_pos_left _ hr
    have hsum : N + (N / L + 1) ≤ r * k := by nlinarith
    omega
  refine ⟨hrM, ?_⟩
  change N ≤ L * (r * k - N)
  exact hdivL.le.trans (Nat.mul_le_mul_left L hbase)


/-- The existing fractional-remainder estimate is exponentially small off the
fixed-parameter exceptional set. -/
lemma remainder_le_exp (N M L k : ℕ) (hM : 0 < M) (hL : 0 < L)
    (hk : 2 ≤ k) (hkN : k ≤ N) (hout : k ∉ exceptional N M L)
    (hlarge : 2 ^ ((M * M + 1) * L) ≤ N + 1) :
    (rho N k : ℝ) / (d k : ℝ) ≤ 2 * (1 / 2 : ℝ) ^ N := by
  obtain ⟨hr, hgap⟩ := outside_exceptional N M L k hM hL (by omega) hout
  have hNk : N ≤ (N / k + 1) * k := by
    have hh : N < (N / k + 1) * k := by
      simpa [Nat.mul_comm] using Nat.lt_mul_div_succ N (by omega : 0 < k)
    exact hh.le
  have hf : (N.factorial : ℝ) * 2 ^ N ≤ (k.factorial : ℝ) ^ (N / k + 1) := by
    exact_mod_cast factorial_ratio_exp_bound N k (N / k + 1) M L hr hkN hNk hgap hlarge
  have hden : (0 : ℝ) < (k.factorial : ℝ) ^ (N / k + 1) := by positivity
  calc
    (rho N k : ℝ) / (d k : ℝ) ≤
        2 * (N.factorial : ℝ) / (k.factorial : ℝ) ^ (N / k + 1) :=
      remainder_le_geometric N k hk
    _ = 2 * ((N.factorial : ℝ) / (k.factorial : ℝ) ^ (N / k + 1)) := by ring
    _ ≤ 2 * (1 / (2 : ℝ) ^ N) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply (div_le_div_iff₀ hden (by positivity)).mpr
      simpa using hf
    _ = 2 * (1 / 2 : ℝ) ^ N := by rw [one_div_pow]

lemma R_le_exceptional_card (N M L : ℕ) (hM : 0 < M) (hL : 0 < L)
    (hlarge : 2 ^ ((M * M + 1) * L) ≤ N + 1) :
    R N ≤ ((exceptional N M L).card : ℝ) + (N : ℝ) * (2 * (1 / 2 : ℝ) ^ N) := by
  have hind : (∑ k ∈ Finset.Icc 2 N,
      if k ∈ exceptional N M L then (1 : ℝ) else 0) ≤
      ((exceptional N M L).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast Finset.card_le_card (show
      (Finset.Icc 2 N).filter (fun k => k ∈ exceptional N M L) ⊆ exceptional N M L from
        fun _ hk => (Finset.mem_filter.mp hk).2)
  have hcard : ((Finset.Icc 2 N).card : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (show (Finset.Icc 2 N).card ≤ N by simp [Nat.card_Icc])
  calc
    R N ≤ ∑ k ∈ Finset.Icc 2 N,
        ((if k ∈ exceptional N M L then (1 : ℝ) else 0) + 2 * (1 / 2 : ℝ) ^ N) := by
      apply Finset.sum_le_sum
      intro k hk
      obtain ⟨hk2, hkN⟩ := Finset.mem_Icc.mp hk
      by_cases he : k ∈ exceptional N M L
      · simp only [if_pos he]
        exact (remainder_lt_one N k hk2).le.trans (le_add_of_nonneg_right (by positivity))
      · simp only [if_neg he, zero_add]
        exact remainder_le_exp N M L k hM hL hk2 hkN he hlarge
    _ = (∑ k ∈ Finset.Icc 2 N, if k ∈ exceptional N M L then (1 : ℝ) else 0) +
        ((Finset.Icc 2 N).card : ℝ) * (2 * (1 / 2 : ℝ) ^ N) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((exceptional N M L).card : ℝ) + (N : ℝ) * (2 * (1 / 2 : ℝ) ^ N) :=
      add_le_add hind (mul_le_mul_of_nonneg_right hcard (by positivity))

/-- An explicit fixed-parameter estimate.  The enormous threshold is harmless:
`M,L` are chosen first, and only then is `N` sent to infinity. -/
theorem normalized_R_le (N M L : ℕ) (hN : 0 < N) (hM : 0 < M) (hL : 0 < L)
    (hlarge : 2 ^ ((M * M + 1) * L) ≤ N + 1) :
    R N / (N : ℝ) ≤ 1 / (M : ℝ) + (M : ℝ) / (L : ℝ) + (M : ℝ) / (N : ℝ) +
      2 * (1 / 2 : ℝ) ^ N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hc : ((exceptional N M L).card : ℝ) ≤
      (N : ℝ) / (M : ℝ) + (M : ℝ) * ((N : ℝ) / (L : ℝ) + 1) := by
    calc
      ((exceptional N M L).card : ℝ) ≤ (N / M : ℕ) + (M : ℝ) * ((N / L : ℕ) + 1) := by
        exact_mod_cast exceptional_card_le N M L
      _ ≤ (N : ℝ) / (M : ℝ) + (M : ℝ) * ((N : ℝ) / (L : ℝ) + 1) := by
        gcongr <;> exact Nat.cast_div_le
  have hb := (R_le_exceptional_card N M L hM hL hlarge).trans
    (add_le_add hc (le_refl ((N : ℝ) * (2 * (1 / 2 : ℝ) ^ N))))
  calc
    R N / (N : ℝ) ≤
        ((N : ℝ) / (M : ℝ) + (M : ℝ) * ((N : ℝ) / (L : ℝ) + 1) +
          (N : ℝ) * (2 * (1 / 2 : ℝ) ^ N)) / (N : ℝ) :=
      div_le_div_of_nonneg_right hb hNr.le
    _ = 1 / (M : ℝ) + (M : ℝ) / (L : ℝ) + (M : ℝ) / (N : ℝ) +
        2 * (1 / 2 : ℝ) ^ N := by
      field_simp
      ring

/-- Unconditional sublinearity of the sum of fractional remainders. -/
theorem normalized_R_tendsto_zero :
    Filter.Tendsto (fun N : ℕ => R N / (N : ℝ)) Filter.atTop (nhds 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [] with N
    exact ha.trans_le (div_nonneg (R_nonneg N) (Nat.cast_nonneg N))
  · intro ε hε
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show 0 < ε / 3 by positivity)
    let M := m + 1
    have hM : 0 < M := Nat.succ_pos _
    have hMr : (0 : ℝ) < M := by exact_mod_cast hM
    have hm' : 1 / (M : ℝ) < ε / 3 := by simpa [M] using hm
    obtain ⟨l, hl⟩ := exists_nat_one_div_lt (show 0 < (ε / 3) / (M : ℝ) by positivity)
    let L := l + 1
    have hL : 0 < L := Nat.succ_pos _
    have hl' : (M : ℝ) / (L : ℝ) < ε / 3 := by
      have hh : 1 / (L : ℝ) < (ε / 3) / (M : ℝ) := by simpa [L] using hl
      have := (lt_div_iff₀ hMr).mp hh
      simpa [div_eq_mul_inv, mul_comm] using this
    have hlim : Filter.Tendsto (fun N : ℕ =>
        1 / (M : ℝ) + (M : ℝ) / (L : ℝ) + (M : ℝ) / (N : ℝ) +
          2 * (1 / 2 : ℝ) ^ N) Filter.atTop
        (nhds (1 / (M : ℝ) + (M : ℝ) / (L : ℝ))) := by
      have ht1 : Filter.Tendsto (fun N : ℕ => (M : ℝ) / (N : ℝ))
          Filter.atTop (nhds 0) := by
        simpa using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (M : ℝ)
      have ht2 : Filter.Tendsto (fun N : ℕ => 2 * (1 / 2 : ℝ) ^ N)
          Filter.atTop (nhds 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
          (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (2 : ℝ)
      simpa using ((tendsto_const_nhds (x := 1 / (M : ℝ) + (M : ℝ) / (L : ℝ))).add ht1).add ht2
    have hsmall : 1 / (M : ℝ) + (M : ℝ) / (L : ℝ) < ε := by linarith
    filter_upwards [Filter.eventually_ge_atTop (max 1 (2 ^ ((M * M + 1) * L))),
      hlim.eventually_lt_const hsmall] with N hN hb
    exact (normalized_R_le N M L (by omega) hM hL (by omega)).trans_lt hb

/-- The shifted normalization used by the exact terminal-residue theorem. -/
lemma normalized_R_succ_tendsto_zero :
    Filter.Tendsto (fun n : ℕ => R (n + 1) / (n + 1 : ℝ))
      Filter.atTop (nhds 0) := by
  simpa [Function.comp_def] using normalized_R_tendsto_zero.comp (Filter.tendsto_add_atTop_nat 1)

/-- The rationality consequence with the previously supplied sublinearity
hypothesis discharged.  The older conditional theorem remains in
`FloorArithmetic` for backwards compatibility. -/
theorem rational_implies_terminal_limit
    (hr : ¬ Irrational FreshFactorialAttack.series) :
    Filter.Tendsto (fun n : ℕ => ((I (n + 1) % (n + 1) : ℕ) : ℝ) / (n + 1 : ℝ))
      Filter.atTop (nhds 1) :=
  FloorArithmetic.rational_implies_terminal_limit normalized_R_succ_tendsto_zero hr

/-- Only the genuine arithmetic nonterminal-subsequence hypothesis remains.
No such subsequence is asserted in this development. -/
theorem irrational_of_uniformly_nonterminal_subsequence
    (ε : ℝ) (hε : 0 < ε)
    (hbad : ∀ M : ℕ, ∃ n ≥ M,
      ((I (n + 1) % (n + 1) : ℕ) : ℝ) / (n + 1 : ℝ) ≤ 1 - ε) :
    Irrational FreshFactorialAttack.series :=
  FloorArithmetic.irrational_of_uniformly_nonterminal_subsequence
    normalized_R_succ_tendsto_zero ε hε hbad

/-! ## Exact factorial absorption and the rational gcd identity -/

lemma prod_Icc_eq_factorial (N : ℕ) :
    (∏ i ∈ Finset.Icc 1 N, i) = N.factorial := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ N + 1), ih, Nat.factorial_succ]
    exact Nat.mul_comm _ _

/-- Three distinct positive entries in `1,...,N` can be absorbed together. -/
lemma three_mul_dvd_factorial (a b c N : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (haN : a ≤ N) (hbN : b ≤ N) (hcN : c ≤ N)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    a * b * c ∣ N.factorial := by
  have hs : ({a, b, c} : Finset ℕ) ⊆ Finset.Icc 1 N := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact Finset.mem_Icc.mpr ⟨ha, haN⟩
    · exact Finset.mem_Icc.mpr ⟨hb, hbN⟩
    · exact Finset.mem_Icc.mpr ⟨hc, hcN⟩
  have hd := Finset.prod_dvd_prod_of_subset {a, b, c} (Finset.Icc 1 N) id hs
  simpa [prod_Icc_eq_factorial, hab, hac, hbc, Nat.mul_assoc] using hd

/-- Uniform absorption, including the collision cases `K=q` and `K=2q`.
No coprimality assumption on `q,K` is required. -/
theorem factorial_absorption (q K N : ℕ) (hq : 0 < q) (hK : 0 < K)
    (hKN : K ≤ N) (hqN : 3 * q ≤ N) :
    q ^ 2 * K ∣ N.factorial := by
  have hthree : q * (2 * q) * (3 * q) ∣ N.factorial :=
    three_mul_dvd_factorial q (2 * q) (3 * q) N
      hq (by omega) (by omega) (by omega) (by omega) hqN
      (by omega) (by omega) (by omega)
  by_cases heq : K = q
  · subst K
    exact (show q ^ 2 * q ∣ q * (2 * q) * (3 * q) from ⟨6, by ring⟩).trans hthree
  by_cases heq2 : K = 2 * q
  · subst K
    exact (show q ^ 2 * (2 * q) ∣ q * (2 * q) * (3 * q) from ⟨3, by ring⟩).trans hthree
  have hd : q * (2 * q) * K ∣ N.factorial :=
    three_mul_dvd_factorial q (2 * q) K N
      hq (by omega) hK (by omega) (by omega) hKN
      (by omega) (Ne.symm heq) (Ne.symm heq2)
  exact (show q ^ 2 * K ∣ q * (2 * q) * K from ⟨2, by ring⟩).trans hd

/-- The denominator is natural; the numerator may have either sign. -/
lemma coprime_mul_of_dvd (a : ℤ) (q t : ℕ) (hqt : q ∣ t) :
    IsCoprime ((q : ℤ) * (t : ℤ)) (a * (t : ℤ) - 1) := by
  obtain ⟨u, hu⟩ := hqt
  have ht : IsCoprime (t : ℤ) (a * (t : ℤ) - 1) := ⟨a, -1, by ring⟩
  have hq : IsCoprime (q : ℤ) (a * (t : ℤ) - 1) := by
    refine ⟨a * (u : ℤ), -1, ?_⟩
    rw [hu]
    push_cast
    ring
  exact hq.mul_left ht

/-- Pure integer algebra for the gcd step, separated from the series. -/
lemma gcd_eq_of_scaled_relation (A B q K : ℕ) (a : ℤ) (hq : 0 < q)
    (hd : q ^ 2 * K ∣ A)
    (heq : (A : ℤ) * a = (q : ℤ) * ((B : ℤ) + (K : ℤ))) :
    Nat.gcd A B = K := by
  obtain ⟨u, hu⟩ := hd
  let t := q * u
  have hqt : q ∣ t := ⟨u, rfl⟩
  have hA : (A : ℤ) = (K : ℤ) * ((q : ℤ) * (t : ℤ)) := by
    rw [hu]
    dsimp [t]
    ring
  have hB : (B : ℤ) = (K : ℤ) * (a * (t : ℤ) - 1) := by
    apply mul_left_cancel₀ (show (q : ℤ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hq))
    rw [hA] at heq
    nlinarith [heq]
  rw [← Int.gcd_natCast_natCast, hA, hB, Int.gcd_mul_left,
    Int.isCoprime_iff_gcd_eq_one.mp (coprime_mul_of_dvd a q t hqt)]
  simp

/-- The common divisor of the two integer coefficients. -/
def G (N : ℕ) : ℕ := Nat.gcd N.factorial (I N)

/-- The unnormalized linear form in the actual series. -/
noncomputable def F (N : ℕ) : ℝ :=
  (N.factorial : ℝ) * FreshFactorialAttack.series - (I N : ℝ)

lemma F_eq_remainder_add_tail (N : ℕ) (hN : 1 ≤ N) :
    F N = R N + scaledTail N := by
  have hh := scaled_series_decomposition (N - 1)
  rw [Nat.sub_add_cancel hN] at hh
  unfold F
  linarith

lemma F_pos (N : ℕ) (hN : 1 ≤ N) : 0 < F N := by
  rw [F_eq_remainder_add_tail N hN]
  exact add_pos_of_nonneg_of_pos (R_nonneg N) (scaledTail_pos N)

lemma F_lt_index (N : ℕ) (hN : 3 ≤ N) : F N < (N : ℝ) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hR := R_lt_card N (by omega)
  have hT := (scaledTail_bounds (N - 1) (by omega)).2
  have hpred : N - 1 + 1 = N := Nat.sub_add_cancel (by omega)
  rw [hpred] at hT
  have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    norm_num
  rw [hcast] at hR
  simp only [hcast, sub_add_cancel] at hT
  have hT1 : scaledTail N < 1 :=
    hT.trans_le ((div_le_one (by linarith : (0 : ℝ) < N)).mpr hNr)
  rw [F_eq_remainder_add_tail N (by omega)]
  linarith

/-- Integrality and the strict finite window need no asymptotic estimate. -/
lemma rational_F_integer (q : ℚ) (hq : FreshFactorialAttack.series = (q : ℝ))
    (N : ℕ) (hN : 3 ≤ N) (hden : q.den ≤ N) :
    ∃ K : ℕ, 0 < K ∧ K < N ∧ F N = (K : ℝ) := by
  have hpred : N - 1 + 1 = N := Nat.sub_add_cancel (by omega)
  obtain ⟨z, hz⟩ := FreshFactorialAttack.rational_scaled_is_integer q (N - 1) (by omega)
  rw [hpred] at hz
  have hF : F N = ((z - (I N : ℤ) : ℤ) : ℝ) := by
    simp only [F, hq, hz, Int.cast_sub, Int.cast_natCast]
  have hzpos : 0 < z - (I N : ℤ) := by
    exact_mod_cast (show (0 : ℝ) < ((z - (I N : ℤ) : ℤ) : ℝ) by
      rw [← hF]; exact F_pos N (by omega))
  obtain ⟨K, hK⟩ := Int.eq_ofNat_of_zero_le hzpos.le
  have hFK : F N = (K : ℝ) := by simpa [hK] using hF
  refine ⟨K, ?_, ?_, hFK⟩
  · exact_mod_cast (show (0 : ℝ) < (K : ℝ) by rw [← hFK]; exact F_pos N (by omega))
  · exact_mod_cast (show (K : ℝ) < (N : ℝ) by rw [← hFK]; exact F_lt_index N hN)

/-- Under rationality, the exact positive integer `F_N` is the gcd, once
`N ≥ max(3,3*q.den)`.  In particular, the reduced denominator is handled
explicitly rather than confusing it with a rational numerator. -/
theorem rational_G_eq_F (q : ℚ) (hq : FreshFactorialAttack.series = (q : ℝ))
    (N : ℕ) (hN : max 3 (3 * q.den) ≤ N) :
    (G N : ℝ) = F N := by
  obtain ⟨K, hK, hKN, hFK⟩ := rational_F_integer q hq N (by omega) (by omega)
  have hd := factorial_absorption q.den K N q.den_pos hK hKN.le (by omega)
  have hden0 : (q.den : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt q.den_pos)
  have heq : (N.factorial : ℝ) * (q.num : ℝ) =
      (q.den : ℝ) * ((I N : ℝ) + (K : ℝ)) := by
    have hh := hFK
    simp only [F, hq, Rat.cast_def] at hh
    field_simp at hh
    nlinarith [hh]
  have hg : G N = K := gcd_eq_of_scaled_relation N.factorial (I N) q.den K q.num
    q.den_pos hd (by exact_mod_cast heq)
  rw [hg, hFK]

lemma G_pos (N : ℕ) : 0 < G N :=
  Nat.gcd_pos_of_pos_left (I N) (Nat.factorial_pos N)

/-- The coefficients after gcd division really are primitive integers. -/
lemma primitive_coefficients_coprime (N : ℕ) :
    Nat.Coprime (N.factorial / G N) (I N / G N) :=
  Nat.coprime_div_gcd_div_gcd (G_pos N)

/-- The value of the primitive integer linear form, not a real-coefficient
normalization declared by convention. -/
noncomputable def primitiveValue (N : ℕ) : ℝ :=
  ((N.factorial / G N : ℕ) : ℝ) * FreshFactorialAttack.series - ((I N / G N : ℕ) : ℝ)

lemma primitiveValue_eq_F_div_G (N : ℕ) : primitiveValue N = F N / (G N : ℝ) := by
  have hg0 : (G N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (G_pos N))
  have hd1 : G N ∣ N.factorial := Nat.gcd_dvd_left _ _
  have hd2 : G N ∣ I N := Nat.gcd_dvd_right _ _
  rw [primitiveValue, Nat.cast_div hd1 hg0, Nat.cast_div hd2 hg0, F]
  ring

/-- The primitive form has exactly value one under rationality. -/
theorem rational_primitiveValue_eq_one (q : ℚ)
    (hq : FreshFactorialAttack.series = (q : ℝ))
    (N : ℕ) (hN : max 3 (3 * q.den) ≤ N) :
    primitiveValue N = 1 := by
  rw [primitiveValue_eq_F_div_G, ← rational_G_eq_F q hq N hN]
  exact div_self (by exact_mod_cast (Nat.ne_of_gt (G_pos N)))

lemma rational_G_lt_index (q : ℚ) (hq : FreshFactorialAttack.series = (q : ℝ))
    (N : ℕ) (hN : max 3 (3 * q.den) ≤ N) : G N < N := by
  have hh := F_lt_index N (by omega)
  rw [← rational_G_eq_F q hq N hN] at hh
  exact_mod_cast hh

/-- The unshifted version of the terminal-residue limit. -/
theorem rational_implies_terminal_limit_at_index
    (hr : ¬ Irrational FreshFactorialAttack.series) :
    Filter.Tendsto (fun N : ℕ => ((I N % N : ℕ) : ℝ) / (N : ℝ))
      Filter.atTop (nhds 1) := by
  apply (Filter.tendsto_add_atTop_iff_nat 1).mp
  simpa using rational_implies_terminal_limit hr

end FloorSublinear
