import FormalConjectures.Util.ProblemImports

open Nat Real Finset
open scoped Real Chebyshev

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-!
Elementary Chebyshev gap: `θ(2n) - θ(n) ≥ (log 4 / 3) * n - error`.
-/

lemma log_centralBinom_ge (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * Real.log 4 - Real.log (2 * n) ≤ Real.log (n.centralBinom) := by
  have hpos : 0 < n.centralBinom := centralBinom_pos n
  have hn0 : 0 < n := hn
  have h4 : (4 : ℝ) ^ n ≤ (2 * n : ℝ) * n.centralBinom := by
    have := four_pow_le_two_mul_self_mul_centralBinom n hn0
    exact_mod_cast this
  have hlog := log_le_log (by positivity : (0 : ℝ) < 4 ^ n) h4
  rw [Real.log_pow, Real.log_mul (by positivity) (by exact_mod_cast hpos.ne')] at hlog
  linarith

lemma p_sq_gt_two_mul {n p : ℕ} (hp : p.Prime) (h1 : n < p) : p ^ 2 > 2 * n := by
  have : n + 1 ≤ p := by omega
  have : (n + 1) ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left this 2
  nlinarith

/-- Primes in `(n, 2n]` appear exactly once in `centralBinom n`. -/
lemma factorization_centralBinom_dyadic {n p : ℕ}
    (hp : p.Prime) (h1 : n < p) (h2 : p ≤ 2 * n) :
    (n.centralBinom).factorization p = 1 := by
  have hn0 : 0 < n := by
    have := hp.two_le
    omega
  have hsub : 2 * n - n = n := by omega
  have hC : n.centralBinom * (n.factorial * n.factorial) = (2 * n).factorial := by
    simpa [centralBinom, hsub, mul_assoc] using
      (choose_mul_factorial_mul_factorial (n := 2 * n) (k := n) (by omega))
  have hnf : (n.factorial).factorization p = 0 :=
    factorization_factorial_eq_zero_of_lt h1
  have hp2 : p ^ 2 > 2 * n := p_sq_gt_two_mul hp h1
  have hlog : Nat.log p (2 * n) < 2 :=
    (Nat.log_lt_iff_lt_pow hp.one_lt (by omega)).2 hp2
  have h2f : ((2 * n).factorial).factorization p = (2 * n) / p := by
    rw [factorization_factorial hp hlog]
    simp [Ico_succ_singleton]
  have hdiv : (2 * n) / p = 1 := by
    have hge : 1 ≤ (2 * n) / p := Nat.div_pos (by omega) hp.pos
    have hlt : (2 * n) / p < 2 := by
      rw [Nat.div_lt_iff_lt_mul hp.pos]
      nlinarith
    omega
  have hc0 : n.centralBinom ≠ 0 := (centralBinom_pos n).ne'
  have hf0 : n.factorial ≠ 0 := factorial_ne_zero n
  have hfact :
      (n.centralBinom * (n.factorial * n.factorial)).factorization p =
        (n.centralBinom).factorization p +
          ((n.factorial).factorization p + (n.factorial).factorization p) := by
    rw [Nat.factorization_mul hc0 (mul_ne_zero hf0 hf0),
        Nat.factorization_mul hf0 hf0]
    simp [Pi.add_apply]
  have : (n.centralBinom).factorization p + 2 * (n.factorial).factorization p =
      ((2 * n).factorial).factorization p := by
    rw [hC] at hfact
    simpa [two_mul] using hfact.symm
  simpa [hnf, h2f, hdiv] using this

lemma theta_eq_sum_primes (n : ℕ) :
    Chebyshev.theta (n : ℝ) =
      ∑ p ∈ (Finset.Icc 1 n).filter Nat.Prime, Real.log (p : ℝ) := by
  have h := Chebyshev.theta_eq_sum_Icc (n : ℝ)
  have hfl : ⌊(n : ℝ)⌋₊ = n := Nat.floor_natCast n
  rw [hfl] at h
  have h01 :
      (Finset.Icc 0 n).filter Nat.Prime = (Finset.Icc 1 n).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro ⟨⟨_, hp2⟩, hp⟩
      exact ⟨⟨hp.one_lt.le, hp2⟩, hp⟩
    · intro ⟨⟨h1, h2⟩, hp⟩
      exact ⟨⟨Nat.zero_le _, h2⟩, hp⟩
  simpa [h01] using h

/-- Contribution of primes in `(n, 2n]` to `θ` is `θ(2n) - θ(n)`. -/
lemma dyadic_contribution (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ (Finset.Icc (n + 1) (2 * n)).filter Nat.Prime, Real.log (p : ℝ) =
      Chebyshev.theta (2 * n) - Chebyshev.theta n := by
  have hθ2 := theta_eq_sum_primes (2 * n)
  have hθ1 := theta_eq_sum_primes n
  have hsplit :
      (Finset.Icc 1 (2 * n)).filter Nat.Prime =
        (Finset.Icc 1 n).filter Nat.Prime ∪
          (Finset.Icc (n + 1) (2 * n)).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro ⟨⟨h1, h2⟩, hp⟩
      have : p ≤ n ∨ n + 1 ≤ p := by omega
      rcases this with h | h
      · exact Or.inl ⟨⟨h1, h⟩, hp⟩
      · exact Or.inr ⟨⟨h, h2⟩, hp⟩
    · intro h
      rcases h with ⟨⟨h1, h2⟩, hp⟩ | ⟨⟨h1, h2⟩, hp⟩
      · exact ⟨⟨h1, by omega⟩, hp⟩
      · exact ⟨⟨by omega, h2⟩, hp⟩
  have hdisj :
      Disjoint ((Finset.Icc 1 n).filter Nat.Prime)
        ((Finset.Icc (n + 1) (2 * n)).filter Nat.Prime) := by
    refine Finset.disjoint_left.mpr ?_
    intro p hp hq
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp hq
    omega
  have hcast : Chebyshev.theta ((2 * n : ℕ) : ℝ) = Chebyshev.theta (2 * (n : ℝ)) := by
    simp
  rw [← hcast, hθ2, hθ1, hsplit, Finset.sum_union hdisj, add_sub_cancel_left]


lemma factorization_centralBinom_le_one_of_large {n p : ℕ}
    (hp2 : 2 * n < p ^ 2) :
    (n.centralBinom).factorization p ≤ 1 :=
  factorization_choose_le_one (p_large := hp2)

lemma log_centralBinom_eq_sum_factorization (n : ℕ) :
    Real.log (n.centralBinom : ℝ) =
      (n.centralBinom).factorization.sum fun p t => (t : ℝ) * Real.log p :=
  log_nat_eq_sum_factorization _

/-- Primes dividing `centralBinom n` are at most `2n`. -/
lemma support_factorization_centralBinom {n p : ℕ}
    (h : (n.centralBinom).factorization p ≠ 0) : p ≤ 2 * n :=
  le_two_mul_of_factorization_centralBinom_pos (Nat.pos_of_ne_zero h)

/-- The Chebyshev gap lower bound. -/
lemma theta_two_n_sub_theta_n_ge (n : ℕ) (hn : 3 ≤ n) :
    (Real.log 4 / 3) * n - 2 * Real.sqrt (2 * n) * Real.log (2 * n) - Real.log (2 * n) ≤
      Chebyshev.theta (2 * n) - Chebyshev.theta n := by
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 < n := by omega
  have hlogC := log_centralBinom_ge n hn1
  -- log C = sum_p v_p log p
  have hsum := log_centralBinom_eq_sum_factorization n
  -- Split support into p ≤ sqrt(2n) and sqrt(2n) < p ≤ 2n
  let s2 : ℕ := Nat.sqrt (2 * n)
  have hs2 : s2 * s2 ≤ 2 * n := by
    simpa [pow_two] using Nat.sqrt_le' (2 * n)
  have hs2' : 2 * n < (s2 + 1) * (s2 + 1) := by
    simpa [pow_two] using Nat.lt_succ_sqrt' (2 * n)
  -- dyadic primes contribute exactly θ(2n)-θ(n)
  have hdy := dyadic_contribution n hn1
  -- log C ≥ dyadic contribution  (other terms nonnegative)
  have hvpos : ∀ p, 0 ≤ ((n.centralBinom).factorization p : ℝ) * Real.log p := by
    intro p
    have : 0 ≤ Real.log (p : ℝ) := log_natCast_nonneg p
    positivity
  -- Write log C as sum over primes p ≤ 2n
  have hsupport :
      (n.centralBinom).factorization.support ⊆
        (Finset.range (2 * n + 1)).filter Nat.Prime := by
    intro p hp
    have hne : (n.centralBinom).factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
    have hpP : p.Prime := by
      have h' : ¬((n.centralBinom).factorization p = 0) := hne
      rw [Nat.factorization_eq_zero_iff] at h'
      push_neg at h'
      exact h'.1
    have hple : p ≤ 2 * n := support_factorization_centralBinom hne
    simp [hpP, hple]
  have hlogC' :
      Real.log (n.centralBinom : ℝ) =
        ∑ p ∈ (Finset.range (2 * n + 1)).filter Nat.Prime,
          ((n.centralBinom).factorization p : ℝ) * Real.log p := by
    rw [hsum]
    simp only [Finsupp.sum]
    refine Finset.sum_subset ?_ ?_
    · intro p hp
      exact hsupport hp
    · intro p hp hnp
      have : (n.centralBinom).factorization p = 0 := by
        contrapose! hnp
        exact Finsupp.mem_support_iff.mpr hnp
      simp [this]
  -- Split the sum at n and at 2n/3
  -- First: dyadic part equals θ(2n)-θ(n)
  have hdy' :
      ∑ p ∈ (Finset.Icc (n + 1) (2 * n)).filter Nat.Prime,
          ((n.centralBinom).factorization p : ℝ) * Real.log p =
        Chebyshev.theta (2 * n) - Chebyshev.theta n := by
    refine Eq.trans ?_ hdy
    refine Finset.sum_congr rfl ?_
    intro p hp
    have hpP : p.Prime := (Finset.mem_filter.mp hp).2
    have hmem := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
    have : (n.centralBinom).factorization p = 1 :=
      factorization_centralBinom_dyadic hpP hmem.1 hmem.2
    simp [this]
  -- Remaining primes p ≤ n contribute at most θ(2n/3) + small-prime error
  -- Bound: p ≤ s2 contribute ≤ (log(2n)) * (#primes ≤ s2) ≤ s2 * log(2n)
  --        s2 < p ≤ 2n/3 contribute ≤ θ(2n/3) ≤ log 4 * (2n/3)
  --        2n/3 < p ≤ n contribute 0
  have hzero : ∀ p, 2 * n < 3 * p → p ≤ n → 2 < n →
      (n.centralBinom).factorization p = 0 :=
    fun p h1 h2 h3 => factorization_centralBinom_of_two_mul_self_lt_three_mul h3 h2 h1
  have hunion :
      (Finset.range (2 * n + 1)).filter Nat.Prime =
        (Finset.range (n + 1)).filter Nat.Prime ∪
          (Finset.Icc (n + 1) (2 * n)).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    constructor
    · intro ⟨hp2n, hpP⟩
      have : p ≤ n ∨ n + 1 ≤ p := by omega
      rcases this with h | h
      · exact Or.inl ⟨by omega, hpP⟩
      · exact Or.inr ⟨⟨h, by omega⟩, hpP⟩
    · intro h
      rcases h with ⟨hp, hpP⟩ | ⟨⟨h1, h2⟩, hpP⟩
      · exact ⟨by omega, hpP⟩
      · exact ⟨by omega, hpP⟩
  have hdisj :
      Disjoint ((Finset.range (n + 1)).filter Nat.Prime)
        ((Finset.Icc (n + 1) (2 * n)).filter Nat.Prime) := by
    refine Finset.disjoint_left.mpr ?_
    intro p hp hq
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hp hq
    omega
  have hsplit_sum :
      Real.log (n.centralBinom : ℝ) =
        ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime,
            ((n.centralBinom).factorization p : ℝ) * Real.log p +
          ∑ p ∈ (Finset.Icc (n + 1) (2 * n)).filter Nat.Prime,
            ((n.centralBinom).factorization p : ℝ) * Real.log p := by
    rw [hlogC', hunion, Finset.sum_union hdisj]
  -- Upper bound the non-dyadic contribution
  have hrest :
      ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime,
          ((n.centralBinom).factorization p : ℝ) * Real.log p ≤
        Real.log 4 * ((2 * n / 3 : ℕ) : ℝ) + (s2 : ℝ) * Real.log (2 * n) := by
    -- split at s2 and at 2n/3
    let S := (Finset.range (n + 1)).filter Nat.Prime
    let Ssmall := S.filter (fun p => p ≤ s2)
    let Smid := S.filter (fun p => s2 < p ∧ 3 * p ≤ 2 * n)
    let Slarge := S.filter (fun p => 2 * n < 3 * p)
    have hS : S = Ssmall ∪ Smid ∪ Slarge := by
      ext p
      simp only [S, Ssmall, Smid, Slarge, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
      constructor
      · intro ⟨hp, hpP⟩
        by_cases h1 : p ≤ s2
        · exact Or.inl (Or.inl ⟨⟨hp, hpP⟩, h1⟩)
        · by_cases h2 : 3 * p ≤ 2 * n
          · exact Or.inl (Or.inr ⟨⟨hp, hpP⟩, ⟨by omega, h2⟩⟩)
          · exact Or.inr ⟨⟨hp, hpP⟩, by omega⟩
      · intro h
        rcases h with (⟨⟨hp, hpP⟩, _⟩ | ⟨⟨hp, hpP⟩, _⟩) | ⟨⟨hp, hpP⟩, _⟩
        · exact ⟨hp, hpP⟩
        · exact ⟨hp, hpP⟩
        · exact ⟨hp, hpP⟩
    have d1 : Disjoint Ssmall Smid := by
      refine Finset.disjoint_left.mpr ?_
      intro p hp hq
      simp [Ssmall, Smid, S] at hp hq
      omega
    have d2 : Disjoint (Ssmall ∪ Smid) Slarge := by
      refine Finset.disjoint_left.mpr ?_
      intro p hp hq
      have hp' : p ∈ Ssmall ∨ p ∈ Smid := Finset.mem_union.mp hp
      have hL : 2 * n < 3 * p := by
        simp only [Slarge, S, Finset.mem_filter] at hq; exact hq.2
      rcases hp' with hS | hM
      · simp only [Ssmall, S, Finset.mem_filter] at hS
        have hple : p ≤ s2 := hS.2
        have hp2 : 2 ≤ p := hS.1.2.two_le
        have hpp : p * p ≤ 2 * n := (Nat.mul_le_mul hple hple).trans hs2
        have : p < 3 := by nlinarith
        omega
      · simp only [Smid, S, Finset.mem_filter] at hM
        have : 3 * p ≤ 2 * n := hM.2.2
        omega
    change ∑ p ∈ S, _ ≤ _
    rw [hS, Finset.sum_union d2, Finset.sum_union d1]
    have hsmall :
        ∑ p ∈ Ssmall, ((n.centralBinom).factorization p : ℝ) * Real.log p ≤
          (s2 : ℝ) * Real.log (2 * n) := by
      have hterm : ∀ p ∈ Ssmall,
          ((n.centralBinom).factorization p : ℝ) * Real.log p ≤ Real.log (2 * n) := by
        intro p hp
        have hpP : p.Prime := by simp [Ssmall, S] at hp; exact hp.1.2
        have hp2 : 2 ≤ p := hpP.two_le
        have hv : (n.centralBinom).factorization p ≤ Nat.log p (2 * n) := by
          unfold centralBinom
          exact Nat.factorization_choose_le_log
        have hpow : (p : ℝ) ^ (Nat.log p (2 * n)) ≤ (2 * n : ℝ) := by
          exact_mod_cast Nat.pow_log_le_self p (by omega : 2 * n ≠ 0)
        have hlogp : 0 < Real.log (p : ℝ) :=
          log_pos (by exact_mod_cast (hpP.one_lt : 1 < p))
        have hmul : ((n.centralBinom).factorization p : ℝ) * Real.log p ≤
            (Nat.log p (2 * n) : ℝ) * Real.log p :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hv) (log_natCast_nonneg p)
        have hlogb : (Nat.log p (2 * n) : ℝ) * Real.log p ≤ Real.log (2 * n) := by
          have := Real.log_le_log (by positivity) hpow
          rw [Real.log_pow] at this
          exact this
        linarith [hmul, hlogb]
      have hcard : (Ssmall.card : ℝ) ≤ s2 := by
        have : Ssmall ⊆ Finset.Icc 1 s2 := by
          intro p hp
          simp [Ssmall, S] at hp
          exact Finset.mem_Icc.mpr ⟨hp.1.2.one_lt.le, hp.2⟩
        exact_mod_cast (Finset.card_le_card this).trans (by
          simpa [Nat.add_sub_cancel] using (Finset.card_Icc 1 s2).le)
      calc
        _ ≤ ∑ p ∈ Ssmall, Real.log (2 * n) := Finset.sum_le_sum hterm
        _ = Ssmall.card * Real.log (2 * n) := by simp [sum_const, nsmul_eq_mul]
        _ ≤ (s2 : ℝ) * Real.log (2 * n) := by
          have hlognn : 0 ≤ Real.log (2 * (n : ℝ)) := by
            simpa using log_natCast_nonneg (2 * n)
          nlinarith [hcard]
    have hmid :
        ∑ p ∈ Smid, ((n.centralBinom).factorization p : ℝ) * Real.log p ≤
          Real.log 4 * ((2 * n / 3 : ℕ) : ℝ) := by
      have hterm : ∀ p ∈ Smid,
          ((n.centralBinom).factorization p : ℝ) * Real.log p ≤ Real.log p := by
        intro p hp
        have hpP : p.Prime := by simp [Smid, S] at hp; exact hp.1.2
        have hps : s2 < p := by simp [Smid, S] at hp; exact hp.2.1
        have hp2 : 2 * n < p ^ 2 := by
          have : s2 + 1 ≤ p := by omega
          have : (s2 + 1) ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left this 2
          nlinarith
        have hv : (n.centralBinom).factorization p ≤ 1 :=
          factorization_centralBinom_le_one_of_large hp2
        have : ((n.centralBinom).factorization p : ℝ) ≤ 1 := by exact_mod_cast hv
        have hlog : 0 ≤ Real.log (p : ℝ) := log_natCast_nonneg p
        nlinarith
      have : ∑ p ∈ Smid, ((n.centralBinom).factorization p : ℝ) * Real.log p ≤
          ∑ p ∈ Smid, Real.log p := Finset.sum_le_sum hterm
      have hsub : Smid ⊆ (Finset.Icc 1 (2 * n / 3)).filter Nat.Prime := by
        intro p hp
        simp [Smid, S] at hp
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.1.2.one_lt.le, ?_⟩, hp.1.2⟩
        have hmul : p * 3 ≤ 2 * n := by simpa [mul_comm] using hp.2.2
        exact (Nat.le_div_iff_mul_le (by decide : 0 < 3)).2 hmul
      have : ∑ p ∈ Smid, Real.log (p : ℝ) ≤
          ∑ p ∈ (Finset.Icc 1 (2 * n / 3)).filter Nat.Prime, Real.log p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => log_natCast_nonneg _)
      have : ∑ p ∈ (Finset.Icc 1 (2 * n / 3)).filter Nat.Prime, Real.log (p : ℝ) =
          Chebyshev.theta ((2 * n / 3 : ℕ) : ℝ) := (theta_eq_sum_primes _).symm
      have hθle : Chebyshev.theta ((2 * n / 3 : ℕ) : ℝ) ≤
          Real.log 4 * ((2 * n / 3 : ℕ) : ℝ) :=
        Chebyshev.theta_le_log4_mul_x (by exact_mod_cast (Nat.zero_le _))
      linarith
    have hlarge :
        ∑ p ∈ Slarge, ((n.centralBinom).factorization p : ℝ) * Real.log p = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      have : (n.centralBinom).factorization p = 0 := by
        simp [Slarge, S] at hp
        exact hzero p hp.2 (by omega) hn2
      simp [this]
    linarith
  have hmain :
      Chebyshev.theta (2 * n) - Chebyshev.theta n =
        Real.log (n.centralBinom : ℝ) -
          ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime,
            ((n.centralBinom).factorization p : ℝ) * Real.log p := by
    linarith [hsplit_sum, hdy']
  have : Chebyshev.theta (2 * n) - Chebyshev.theta n ≥
      ((n : ℝ) * Real.log 4 - Real.log (2 * n)) -
        (Real.log 4 * ((2 * n / 3 : ℕ) : ℝ) + (s2 : ℝ) * Real.log (2 * n)) := by
    rw [hmain]
    linarith [hlogC, hrest]
  have hdiv3 : ((2 * n / 3 : ℕ) : ℝ) ≤ (2 : ℝ) * n / 3 := by
    simpa using (Nat.cast_div_le (α := ℝ) (m := 2 * n) (n := 3))
  have hs2r : (s2 : ℝ) ≤ Real.sqrt (2 * (n : ℝ)) := by
    have : (s2 : ℝ) ≤ Real.sqrt (2 * n : ℕ) := Real.nat_sqrt_le_real_sqrt
    simpa using this
  have hnn : (0 : ℝ) ≤ Real.log (2 * (n : ℝ)) := by
    simpa using log_natCast_nonneg (2 * n)
  have hnn' : (0 : ℝ) ≤ Real.sqrt (2 * (n : ℝ)) := Real.sqrt_nonneg _
  have h4pos : 0 < Real.log 4 := log_pos (by norm_num)
  nlinarith


