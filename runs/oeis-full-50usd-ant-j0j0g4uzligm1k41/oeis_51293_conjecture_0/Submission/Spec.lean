import FormalConjectures.Util.ProblemImports

open Finset Nat Real Filter Asymptotics Polynomial

/-- A051293: Number of nonempty subsets of {1,...,n} with integer average. -/
def A051293 (n : ℕ) : ℕ :=
  Finset.card (
    (Finset.Icc 1 n).powerset.filter fun S : Finset ℕ =>
      S.Nonempty ∧ S.card ∣ S.sum id
  )

noncomputable def a_real (n : ℕ) : ℝ := A051293 n

namespace TestQ

noncomputable def Q (t : ℕ) : ℝ := ∑' i : ℕ, (i:ℝ)^t * (1/2)^i

theorem hsummable (t : ℕ) : Summable (fun i : ℕ => (i:ℝ)^t * (1/2:ℝ)^i) := by
  have h : ‖(1/2:ℝ)‖ < 1 := by rw [Real.norm_eq_abs]; norm_num
  exact summable_pow_mul_geometric_of_norm_lt_one t h

theorem Q0 : Q 0 = 2 := by
  simp only [Q, pow_zero, one_mul]
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

theorem Qrec (t : ℕ) (ht : 1 ≤ t) :
    2 * Q t = ∑ r ∈ range (t+1), (t.choose r : ℝ) * Q r := by
  -- Step A: Q t = ∑' i, (i+1)^t * (1/2)^(i+1)
  have hstep : Q t = ∑' i : ℕ, ((i:ℝ)+1)^t * (1/2)^(i+1) := by
    have := (hsummable t).tsum_eq_zero_add
    rw [Q]
    rw [this]
    have h0 : ((0:ℕ):ℝ)^t * (1/2:ℝ)^0 = 0 := by
      simp [zero_pow (by omega : t ≠ 0)]
    rw [h0, zero_add]
    apply tsum_congr
    intro i
    push_cast
    ring
  -- Step B: expand binomial and interchange
  have hbin : ∀ i : ℕ, ((i:ℝ)+1)^t * (1/2)^(i+1)
      = ∑ r ∈ range (t+1), ((t.choose r : ℝ) * (i:ℝ)^r * (1/2)^i) * (1/2) := by
    intro i
    rw [add_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [one_pow, mul_one, pow_succ]
    ring
  rw [hstep]
  simp_rw [hbin]
  have e1 : ∀ i : ℕ, ∑ r ∈ range (t+1), ((t.choose r:ℝ)*(i:ℝ)^r*(1/2)^i)*(1/2)
      = (1/2) * ∑ r ∈ range (t+1), (t.choose r:ℝ)*(i:ℝ)^r*(1/2)^i := by
    intro i; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro r hr; ring
  simp_rw [e1]
  rw [tsum_mul_left]
  rw [Summable.tsum_finsetSum (fun r _ => by
    have := (hsummable r).mul_left (t.choose r : ℝ)
    apply this.congr; intro i; ring)]
  have e2 : ∀ r ∈ range (t+1), (∑' i : ℕ, (t.choose r:ℝ)*(i:ℝ)^r*(1/2)^i) = (t.choose r:ℝ) * Q r := by
    intro r hr
    rw [Q, ← tsum_mul_left]
    apply tsum_congr; intro i; ring
  rw [Finset.sum_congr rfl e2]
  ring

theorem Q1 : Q 1 = 2 := by
  have h := Qrec 1 le_rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h; norm_num [Nat.choose, Q0] at h
  linarith

theorem Q2 : Q 2 = 6 := by
  have h := Qrec 2 (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [Nat.choose, Q0, Q1] at h
  linarith

theorem Q3 : Q 3 = 26 := by
  have h := Qrec 3 (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [Nat.choose, Q0, Q1, Q2] at h
  linarith

theorem Q4 : Q 4 = 150 := by
  have h := Qrec 4 (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [Nat.choose, Q0, Q1, Q2, Q3] at h
  linarith

theorem Q5 : Q 5 = 1082 := by
  have h := Qrec 5 (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [Nat.choose, Q0, Q1, Q2, Q3, Q4] at h
  linarith

noncomputable def Sfun (t n : ℕ) : ℝ := ∑ i ∈ range n, (i:ℝ)^t * (1/2)^i

theorem Sfun_le_Q (t n : ℕ) : Sfun t n ≤ Q t := by
  rw [Sfun, Q]
  exact (hsummable t).sum_le_tsum (Finset.range n) (fun i _ => by positivity)

/-- poly times geometric tends to 0. -/
theorem tendsto_poly_geom (k : ℕ) :
    Tendsto (fun n : ℕ => (n:ℝ)^k * (1/2)^n) atTop (nhds 0) := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt k (r := 2) (by norm_num)
  apply h.congr
  intro n
  rw [div_eq_mul_inv, ← inv_pow]
  norm_num

theorem summable_shift5 : Summable (fun i : ℕ => ((i:ℝ)+1)^5 * (1/2)^i) := by
  have h1 : Summable (fun i : ℕ => ((i:ℝ)+1)^5 * (1/2)^(i+1)) := by
    have := (summable_nat_add_iff 1).2 (hsummable 5)
    apply this.congr
    intro i
    push_cast
    ring
  have h2 := h1.mul_left 2
  apply h2.congr
  intro i
  rw [pow_succ]
  ring

noncomputable def Kconst : ℝ := ∑' i : ℕ, ((i:ℝ)+1)^5 * (1/2)^i

theorem Kconst_nonneg : 0 ≤ Kconst := by
  apply tsum_nonneg
  intro i
  positivity

/-- Tail bound: for `t ≤ 5` and `n ≥ 1`. -/
theorem tail_bound (t : ℕ) (ht : t ≤ 5) (n : ℕ) (hn : 1 ≤ n) :
    Q t - Sfun t n ≤ (n+1)^5 * (1/2)^n * Kconst := by
  have hf : Summable (fun i : ℕ => (i:ℝ)^t * (1/2)^i) := hsummable t
  -- Q t - Sfun t n = ∑' i, f (i+n)
  have hsplit : (∑ i ∈ range n, (i:ℝ)^t * (1/2)^i) + ∑' i, ((i+n:ℕ):ℝ)^t * (1/2)^(i+n) = Q t := by
    have := hf.sum_add_tsum_nat_add n
    rw [Q]
    convert this using 3
  have hQeq : Q t - Sfun t n = ∑' i, ((i+n:ℕ):ℝ)^t * (1/2)^(i+n) := by
    rw [Sfun]; linarith [hsplit]
  rw [hQeq]
  -- termwise bound
  have hRHS_sum : Summable (fun i : ℕ => ((i:ℝ)+1)^5 * (n+1)^5 * (1/2)^n * (1/2)^i) := by
    have := summable_shift5.mul_right ((n+1:ℝ)^5 * (1/2)^n)
    apply this.congr; intro i; ring
  have hLHS_sum : Summable (fun i : ℕ => ((i+n:ℕ):ℝ)^t * (1/2)^(i+n)) := by
    have := (summable_nat_add_iff n).2 hf
    apply this.congr; intro i; push_cast; ring
  calc ∑' i : ℕ, ((i+n:ℕ):ℝ)^t * (1/2)^(i+n)
      ≤ ∑' i : ℕ, ((i:ℝ)+1)^5 * (n+1)^5 * (1/2)^n * (1/2)^i := by
        apply Summable.tsum_mono hLHS_sum hRHS_sum
        intro i
        show ((i+n:ℕ):ℝ)^t * (1/2)^(i+n) ≤ ((i:ℝ)+1)^5 * ((n:ℝ)+1)^5 * (1/2)^n * (1/2)^i
        have hik : ((i+n:ℕ):ℝ) ≤ ((i:ℝ)+1) * ((n:ℝ)+1) := by
          push_cast; nlinarith [Nat.cast_nonneg i (α := ℝ), Nat.cast_nonneg n (α := ℝ)]
        have hik0 : (0:ℝ) ≤ ((i+n:ℕ):ℝ) := by positivity
        have hpow : ((i+n:ℕ):ℝ)^t ≤ ((i+n:ℕ):ℝ)^5 := by
          have hpos : 0 < i + n := by omega
          apply pow_le_pow_right₀ (by exact_mod_cast hpos) ht
        have hpow2 : ((i+n:ℕ):ℝ)^5 ≤ (((i:ℝ)+1)*((n:ℝ)+1))^5 := by
          apply pow_le_pow_left₀ hik0 hik
        have hpe : (1/2:ℝ)^(i+n) = (1/2)^n * (1/2)^i := by
          rw [pow_add]; ring
        rw [hpe]
        calc ((i+n:ℕ):ℝ)^t * ((1/2)^n * (1/2)^i)
            ≤ (((i:ℝ)+1)*((n:ℝ)+1))^5 * ((1/2)^n * (1/2)^i) := by
              apply mul_le_mul_of_nonneg_right (le_trans hpow hpow2) (by positivity)
          _ = ((i:ℝ)+1)^5 * (n+1)^5 * (1/2)^n * (1/2)^i := by ring
    _ = (n+1)^5 * (1/2)^n * Kconst := by
        rw [Kconst, ← tsum_mul_left]
        apply tsum_congr; intro i; ring

theorem haux : Tendsto (fun n : ℕ => (n:ℝ)^5 * ((n:ℝ)+1)^5 * (1/2)^n) atTop (nhds 0) := by
  have hg : Tendsto (fun n : ℕ => 32 * ((n:ℝ)^10 * (1/2)^n)) atTop (nhds 0) := by
    have := (tendsto_poly_geom 10).const_mul (32:ℝ)
    simpa using this
  apply squeeze_zero_norm (a := fun n : ℕ => 32 * ((n:ℝ)^10 * (1/2)^n)) _ hg
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; norm_num
  · have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hpos
    have h1 : ((n:ℝ)+1)^5 ≤ 32 * (n:ℝ)^5 := by
      have : ((n:ℝ)+1) ≤ 2 * (n:ℝ) := by linarith
      calc ((n:ℝ)+1)^5 ≤ (2*(n:ℝ))^5 := by
            apply pow_le_pow_left₀ (by positivity) this
        _ = 32 * (n:ℝ)^5 := by ring
    calc (n:ℝ)^5 * ((n:ℝ)+1)^5 * (1/2)^n
        ≤ (n:ℝ)^5 * (32 * (n:ℝ)^5) * (1/2)^n := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 32 * ((n:ℝ)^10 * (1/2)^n) := by ring

theorem tail_limit (t : ℕ) (ht : t ≤ 5) :
    Tendsto (fun n : ℕ => (n:ℝ)^5 * (Q t - Sfun t n)) atTop (nhds 0) := by
  have hlim : Tendsto (fun n : ℕ => Kconst * ((n:ℝ)^5 * ((n:ℝ)+1)^5 * (1/2)^n)) atTop (nhds 0) := by
    have := haux.const_mul Kconst
    simpa using this
  apply squeeze_zero_norm (a := fun n : ℕ => Kconst * ((n:ℝ)^5 * ((n:ℝ)+1)^5 * (1/2)^n)) _ hlim
  intro n
  have hnonneg : 0 ≤ Q t - Sfun t n := by
    rw [show Q t - Sfun t n = ∑' i, ((i+n:ℕ):ℝ)^t * (1/2)^(i+n) from ?_]
    · apply tsum_nonneg; intro i; positivity
    · have := (hsummable t).sum_add_tsum_nat_add n
      rw [Q, Sfun]; linarith [this]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp
  · have hb := tail_bound t ht n hpos
    calc (n:ℝ)^5 * (Q t - Sfun t n)
        ≤ (n:ℝ)^5 * ((n+1)^5 * (1/2)^n * Kconst) := by
          apply mul_le_mul_of_nonneg_left hb (by positivity)
      _ = Kconst * ((n:ℝ)^5 * ((n:ℝ)+1)^5 * (1/2)^n) := by ring

-- (TestQ content above)

/-- The "main term" `M(n) = ∑_{k=1}^n C(n,k)/k`. -/
noncomputable def Mn (n : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 n, (n.choose k : ℝ) / k

theorem reindex_Icc (m : ℕ) (g : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 m, g k = ∑ i ∈ Finset.range m, g (i+1) := by
  induction m with
  | zero => simp
  | succ p ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ p+1), Finset.sum_range_succ, ih]

theorem Mn_rec (m : ℕ) : Mn (m+1) = Mn m + ((2:ℝ)^(m+1) - 1)/((m:ℝ)+1) := by
  rw [Mn, Finset.sum_Icc_succ_top (by omega : 1 ≤ m+1)]
  have hchoose_top : ((m+1).choose (m+1) : ℝ) = 1 := by rw [Nat.choose_self]; simp
  -- Pascal split
  have hpascal_sum : ∑ k ∈ Finset.Icc 1 m, ((m+1).choose k:ℝ)/k
      = (∑ k ∈ Finset.Icc 1 m, (m.choose (k-1):ℝ)/k) + Mn m := by
    rw [Mn, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk1 : k - 1 + 1 = k := by omega
    have hpas : (m+1).choose k = m.choose (k-1) + m.choose k := by
      conv_lhs => rw [← hk1]
      rw [Nat.choose_succ_succ' m (k-1), hk1]
    rw [hpas]; push_cast; ring
  -- absorption
  have habs : ∀ k ∈ Finset.Icc 1 m, (m.choose (k-1):ℝ)/k = ((m+1).choose k:ℝ)/((m:ℝ)+1) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk1 : k - 1 + 1 = k := by omega
    have hmul : (m+1) * m.choose (k-1) = (m+1).choose k * k := by
      have h := Nat.add_one_mul_choose_eq m (k-1)
      simp only [hk1] at h
      exact h
    have hkne : (k:ℝ) ≠ 0 := by
      have : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
      exact ne_of_gt this
    have hmne : (m:ℝ)+1 ≠ 0 := by positivity
    have hmulR : ((m:ℝ)+1) * (m.choose (k-1):ℝ) = ((m+1).choose k:ℝ) * (k:ℝ) := by
      exact_mod_cast hmul
    field_simp
    linear_combination hmulR
  rw [Finset.sum_congr rfl habs] at hpascal_sum
  -- factor out 1/(m+1)
  have hfactor : ∑ k ∈ Finset.Icc 1 m, ((m+1).choose k:ℝ)/((m:ℝ)+1)
      = (∑ k ∈ Finset.Icc 1 m, ((m+1).choose k:ℝ))/((m:ℝ)+1) := by
    rw [Finset.sum_div]
  rw [hfactor] at hpascal_sum
  -- sum of choose over Icc 1 m = 2^{m+1} - 2
  have hrange : ∑ k ∈ Finset.range (m+2), ((m+1).choose k:ℝ) = (2:ℝ)^(m+1) := by
    rw [← Nat.cast_sum, Nat.sum_range_choose (m+1)]; push_cast; ring
  have hdecomp : ∑ k ∈ Finset.range (m+2), ((m+1).choose k:ℝ)
      = ((m+1).choose 0:ℝ) + ((∑ k ∈ Finset.Icc 1 m, ((m+1).choose k:ℝ)) + ((m+1).choose (m+1):ℝ)) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ' (fun k => ((m+1).choose k:ℝ)) m]
    rw [reindex_Icc m (fun k => ((m+1).choose k:ℝ))]
    ring
  simp only [Nat.choose_zero_right, Nat.choose_self, Nat.cast_one] at hdecomp
  have hsum_choose : (∑ k ∈ Finset.Icc 1 m, ((m+1).choose k:ℝ)) = (2:ℝ)^(m+1) - 2 := by
    rw [hrange] at hdecomp; linarith
  rw [hsum_choose] at hpascal_sum
  -- combine
  rw [hpascal_sum, hchoose_top]
  have hm1 : (m:ℝ)+1 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem Mn_eq (n : ℕ) : Mn n = ∑ j ∈ Finset.Icc 1 n, ((2:ℝ)^j - 1)/j := by
  induction n with
  | zero => simp [Mn]
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m+1), ← ih, Mn_rec]
    push_cast
    ring

/- Analytic asymptotics for the main term -/

noncomputable def poly5 (n : ℕ) : ℝ :=
  (n:ℝ)^5 + (n:ℝ)^4 + 3*(n:ℝ)^3 + 13*(n:ℝ)^2 + 75*(n:ℝ) + 541

noncomputable def Tfun (n : ℕ) : ℝ := ∑ j ∈ Finset.Icc 1 n, (2:ℝ)^j / j
noncomputable def Hfun (n : ℕ) : ℝ := ∑ j ∈ Finset.Icc 1 n, (1:ℝ) / j

noncomputable def RSfun (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (n:ℝ)^6 / (((n:ℝ)-(i:ℝ)) * 2^(i+1))
noncomputable def Rfun (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (1/2:ℝ)^(i+1) * (i:ℝ)^6 / ((n:ℝ)-(i:ℝ))

theorem sqrt2_pow_le (n : ℕ) : (Real.sqrt 2)^n ≤ 2^((n+1)/2) := by
  have h2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have h1 : (1:ℝ) ≤ Real.sqrt 2 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have : (2:ℝ)^((n+1)/2) = (Real.sqrt 2)^(2*((n+1)/2)) := by rw [pow_mul, h2]
  rw [this]; apply pow_le_pow_right₀ h1; omega

theorem tendsto_aux' : Tendsto (fun n : ℕ => (n:ℝ)^7 / 2^((n+1)/2)) atTop (nhds 0) := by
  have hr : (1:ℝ) < Real.sqrt 2 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt 7 hr
  apply squeeze_zero_norm _ hlim
  intro n
  rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs]
  have hp : (0:ℝ) < 2^((n+1)/2) := by positivity
  rw [abs_of_pos hp, abs_of_nonneg (show (0:ℝ) ≤ (n:ℝ)^7 by positivity)]
  gcongr
  exact sqrt2_pow_le n

theorem poly5_eq (n : ℕ) : poly5 n = (1/2) * ∑ t ∈ Finset.range 6, (Q t) * (n:ℝ)^(5-t) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      Q0, Q1, Q2, Q3, Q4, Q5]
  norm_num [poly5]
  ring

theorem Mn_split (n : ℕ) : Mn n = Tfun n - Hfun n := by
  rw [Mn_eq, Tfun, Hfun, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [sub_div]

theorem Hfun_nonneg (n : ℕ) : 0 ≤ Hfun n := by
  rw [Hfun]; apply Finset.sum_nonneg; intro j _; positivity

theorem Hfun_le (n : ℕ) : Hfun n ≤ n := by
  rw [Hfun]
  calc ∑ j ∈ Finset.Icc 1 n, (1:ℝ)/j ≤ ∑ j ∈ Finset.Icc 1 n, (1:ℝ) := by
        apply Finset.sum_le_sum; intro j hj; rw [Finset.mem_Icc] at hj
        rw [div_le_one (by exact_mod_cast (by omega : (0:ℕ) < j))]
        exact_mod_cast (by omega : 1 ≤ j)
    _ = n := by rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]

theorem hH : Tendsto (fun n:ℕ => (n:ℝ)^6 * Hfun n / 2^(n+1)) atTop (nhds 0) := by
  apply squeeze_zero (g := fun n:ℕ => (n:ℝ)^7 * (1/2)^n)
  · intro n
    exact div_nonneg (mul_nonneg (by positivity) (Hfun_nonneg n)) (by positivity)
  · intro n
    calc (n:ℝ)^6 * Hfun n / 2^(n+1)
        ≤ (n:ℝ)^6 * (n:ℝ) / 2^(n+1) := by
          gcongr
          exact Hfun_le n
      _ = (n:ℝ)^7 / 2^(n+1) := by ring
      _ ≤ (n:ℝ)^7 / 2^n := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          exact pow_le_pow_right₀ (by norm_num) (by omega)
      _ = (n:ℝ)^7 * (1/2)^n := by rw [div_pow, one_pow]; ring
  · exact tendsto_poly_geom 7

theorem Tfun_reflect (n : ℕ) :
    (n:ℝ)^6 * Tfun n / 2^(n+1) = RSfun n := by
  rw [Tfun, Finset.mul_sum, Finset.sum_div, RSfun]
  apply Finset.sum_bij' (i := fun j _ => n - j) (j := fun i _ => n - i)
  · intro j hj; rw [Finset.mem_Icc] at hj; rw [Finset.mem_range]; omega
  · intro i hi; rw [Finset.mem_range] at hi; rw [Finset.mem_Icc]; omega
  · intro j hj; rw [Finset.mem_Icc] at hj; omega
  · intro i hi; rw [Finset.mem_range] at hi; omega
  · intro j hj
    rw [Finset.mem_Icc] at hj
    have hjn : j ≤ n := hj.2
    have hcast : (n:ℝ) - ((n-j:ℕ):ℝ) = (j:ℝ) := by rw [Nat.cast_sub hjn]; ring
    have hjne : (j:ℝ) ≠ 0 := by
      have : (0:ℝ) < (j:ℝ) := by exact_mod_cast (by omega : 0 < j)
      exact ne_of_gt this
    rw [hcast]
    rw [show (2:ℝ)^(n+1) = 2^((n-j)+1) * 2^j from by rw [← pow_add]; congr 1; omega]
    field_simp

theorem RSfun_decomp (n : ℕ) :
    RSfun n = (1/2)*(∑ t ∈ Finset.range 6, (n:ℝ)^(5-t)*Sfun t n) + Rfun n := by
  have hterm : ∀ i ∈ Finset.range n,
      (n:ℝ)^6 / (((n:ℝ)-(i:ℝ)) * 2^(i+1))
      = (1/2)^(i+1) * (∑ t ∈ Finset.range 6, (n:ℝ)^(5-t)*(i:ℝ)^t)
        + (1/2)^(i+1) * (i:ℝ)^6/((n:ℝ)-(i:ℝ)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hlt : (i:ℝ) < (n:ℝ) := by exact_mod_cast hi
    have hne : (n:ℝ)-(i:ℝ) ≠ 0 := by
      have : (0:ℝ) < (n:ℝ)-(i:ℝ) := by linarith
      exact ne_of_gt this
    have hs : (∑ t ∈ Finset.range 6, (n:ℝ)^(5-t)*(i:ℝ)^t)
        = (n:ℝ)^5 + (n:ℝ)^4*(i:ℝ) + (n:ℝ)^3*(i:ℝ)^2 + (n:ℝ)^2*(i:ℝ)^3 + (n:ℝ)*(i:ℝ)^4 + (i:ℝ)^5 := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
          Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
      norm_num
    have htel : ((n:ℝ)-(i:ℝ)) * (∑ t ∈ Finset.range 6, (n:ℝ)^(5-t)*(i:ℝ)^t) + (i:ℝ)^6 = (n:ℝ)^6 := by
      rw [hs]; ring
    have hdiv : (n:ℝ)^6/((n:ℝ)-(i:ℝ))
        = (∑ t ∈ Finset.range 6, (n:ℝ)^(5-t)*(i:ℝ)^t) + (i:ℝ)^6/((n:ℝ)-(i:ℝ)) := by
      rw [← htel, add_div, mul_div_cancel_left₀ _ hne]
    rw [← div_div, hdiv, add_div]
    rw [show (1/2:ℝ)^(i+1) = 1/2^(i+1) from by rw [div_pow, one_pow]]
    ring
  rw [RSfun, Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
      show (∑ i ∈ Finset.range n, (1/2:ℝ)^(i+1)*(i:ℝ)^6/((n:ℝ)-(i:ℝ))) = Rfun n from rfl]
  congr 1
  -- first part
  rw [Finset.mul_sum]
  have e1 : ∀ i : ℕ, (1/2:ℝ)^(i+1)*(∑ t ∈ Finset.range 6, (n:ℝ)^(5-t)*(i:ℝ)^t)
      = ∑ t ∈ Finset.range 6, (n:ℝ)^(5-t)*((i:ℝ)^t*(1/2)^(i+1)) := by
    intro i; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro t _; ring
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.range n) => e1 i)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [Sfun, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_succ]
  ring

theorem hTeq (n : ℕ) :
    (n:ℝ)^6 * Tfun n / 2^(n+1) - poly5 n
    = (1/2)*(∑ t ∈ Finset.range 6, (n:ℝ)^(5-t)*(Sfun t n - Q t)) + Rfun n := by
  have hsplit : ∑ t ∈ Finset.range 6, (n:ℝ)^(5-t)*(Sfun t n - Q t)
      = (∑ t ∈ Finset.range 6, (n:ℝ)^(5-t)*Sfun t n) - ∑ t ∈ Finset.range 6, Q t *(n:ℝ)^(5-t) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro t _; ring
  rw [Tfun_reflect, RSfun_decomp, poly5_eq, hsplit]
  ring

theorem tendsto_term (t : ℕ) (ht : t ≤ 5) :
    Tendsto (fun n:ℕ => (n:ℝ)^(5-t)*(Sfun t n - Q t)) atTop (nhds 0) := by
  have hup : Tendsto (fun n:ℕ => (n:ℝ)^5*(Q t - Sfun t n)) atTop (nhds 0) := tail_limit t ht
  have hlow : Tendsto (fun n:ℕ => -((n:ℝ)^5*(Q t - Sfun t n))) atTop (nhds 0) := by
    simpa using hup.neg
  have key : ∀ n:ℕ, (n:ℝ)^(5-t)*(Sfun t n - Q t) = -((n:ℝ)^(5-t)*(Q t - Sfun t n)) := by
    intro n; ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup
  · filter_upwards [eventually_ge_atTop 1] with n hn
    rw [key n]
    have hQS : 0 ≤ Q t - Sfun t n := by linarith [Sfun_le_Q t n]
    have hle : (n:ℝ)^(5-t) ≤ (n:ℝ)^5 := pow_le_pow_right₀ (by exact_mod_cast hn) (by omega)
    have := mul_le_mul_of_nonneg_right hle hQS
    linarith
  · filter_upwards [eventually_ge_atTop 1] with n hn
    rw [key n]
    have hQS : 0 ≤ Q t - Sfun t n := by linarith [Sfun_le_Q t n]
    have h1 : (0:ℝ) ≤ (n:ℝ)^(5-t)*(Q t - Sfun t n) := mul_nonneg (by positivity) hQS
    have h2 : (0:ℝ) ≤ (n:ℝ)^5*(Q t - Sfun t n) := mul_nonneg (by positivity) hQS
    linarith

theorem tendsto_sumpart :
    Tendsto (fun n:ℕ => (1/2)*(∑ t ∈ Finset.range 6, (n:ℝ)^(5-t)*(Sfun t n - Q t))) atTop (nhds 0) := by
  have h0 : Tendsto (fun n:ℕ => ∑ t ∈ Finset.range 6, (n:ℝ)^(5-t)*(Sfun t n - Q t)) atTop (nhds 0) := by
    have := tendsto_finset_sum (Finset.range 6)
      (fun t (ht : t ∈ Finset.range 6) => tendsto_term t (by rw [Finset.mem_range] at ht; omega))
    simpa using this
  have h1 := h0.const_mul ((1:ℝ)/2)
  rw [mul_zero] at h1
  exact h1

theorem Rfun_nonneg (n : ℕ) : 0 ≤ Rfun n := by
  rw [Rfun]
  apply Finset.sum_nonneg
  intro i hi
  rw [Finset.mem_range] at hi
  have hlt : (i:ℝ) < n := by exact_mod_cast hi
  apply div_nonneg (by positivity)
  linarith

theorem Rfun_le (n : ℕ) (hn : 1 ≤ n) :
    Rfun n ≤ Q 6 / n + (n:ℝ)^7/2^((n+1)/2) := by
  have hnn : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  rw [Rfun, ← Finset.sum_filter_add_sum_filter_not (Finset.range n) (fun i => 2*i ≤ n)]
  apply _root_.add_le_add
  · -- low part
    calc ∑ i ∈ (Finset.range n).filter (fun i => 2*i ≤ n), (1/2:ℝ)^(i+1)*(i:ℝ)^6/((n:ℝ)-(i:ℝ))
        ≤ ∑ i ∈ (Finset.range n).filter (fun i => 2*i ≤ n), (2/n)*((1/2)^(i+1)*(i:ℝ)^6) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Finset.mem_filter, Finset.mem_range] at hi
          obtain ⟨hilt, hile⟩ := hi
          have hiltR : (i:ℝ) < n := by exact_mod_cast hilt
          have hile2 : 2*(i:ℝ) ≤ n := by exact_mod_cast hile
          have hpos : (0:ℝ) < (n:ℝ)-(i:ℝ) := by linarith
          have hfrac : 1/((n:ℝ)-(i:ℝ)) ≤ 2/n := by
            rw [div_le_div_iff₀ hpos hnn]; nlinarith
          calc (1/2:ℝ)^(i+1)*(i:ℝ)^6/((n:ℝ)-(i:ℝ))
              = ((1/2)^(i+1)*(i:ℝ)^6)*(1/((n:ℝ)-(i:ℝ))) := by rw [mul_one_div]
            _ ≤ ((1/2)^(i+1)*(i:ℝ)^6)*(2/n) := by
                apply mul_le_mul_of_nonneg_left hfrac (by positivity)
            _ = (2/n)*((1/2)^(i+1)*(i:ℝ)^6) := by ring
      _ = (2/n)*∑ i ∈ (Finset.range n).filter (fun i => 2*i ≤ n), (1/2)^(i+1)*(i:ℝ)^6 := by
          rw [← Finset.mul_sum]
      _ ≤ (2/n)*∑ i ∈ Finset.range n, (1/2)^(i+1)*(i:ℝ)^6 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro i _ _; positivity
      _ = (2/n)*((1/2)*Sfun 6 n) := by
          congr 1
          rw [Sfun, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro i _; rw [pow_succ]; ring
      _ ≤ (2/n)*((1/2)*Q 6) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_left (Sfun_le_Q 6 n) (by norm_num)
      _ = Q 6/n := by ring
  · -- high part
    calc ∑ i ∈ (Finset.range n).filter (fun i => ¬ 2*i ≤ n), (1/2:ℝ)^(i+1)*(i:ℝ)^6/((n:ℝ)-(i:ℝ))
        ≤ ∑ i ∈ (Finset.range n).filter (fun i => ¬ 2*i ≤ n), (n:ℝ)^6*(1/2)^((n+1)/2) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Finset.mem_filter, Finset.mem_range] at hi
          obtain ⟨hilt, hile⟩ := hi
          have hilt2 : n < 2*i := by omega
          have hiltR : (i:ℝ) < n := by exact_mod_cast hilt
          have hpos : (0:ℝ) < (n:ℝ)-(i:ℝ) := by linarith
          have hden1 : (1:ℝ) ≤ (n:ℝ)-(i:ℝ) := by
            have h : (i:ℝ)+1 ≤ (n:ℝ) := by exact_mod_cast (by omega : i+1 ≤ n)
            linarith
          have hi6 : (i:ℝ)^6 ≤ (n:ℝ)^6 := pow_le_pow_left₀ (by positivity) (le_of_lt hiltR) 6
          have hexp : (n+1)/2 ≤ i+1 := by omega
          have hpow : (1/2:ℝ)^(i+1) ≤ (1/2)^((n+1)/2) :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) hexp
          rw [div_le_iff₀ hpos]
          calc (1/2:ℝ)^(i+1)*(i:ℝ)^6 ≤ (1/2)^((n+1)/2)*(n:ℝ)^6 := by
                apply mul_le_mul hpow hi6 (by positivity) (by positivity)
            _ ≤ (n:ℝ)^6*(1/2)^((n+1)/2)*((n:ℝ)-(i:ℝ)) := by
                rw [mul_comm ((1/2:ℝ)^((n+1)/2)) _]
                apply le_mul_of_one_le_right (by positivity) hden1
      _ = (((Finset.range n).filter (fun i => ¬ 2*i ≤ n)).card : ℝ)*((n:ℝ)^6*(1/2)^((n+1)/2)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (n:ℝ)*((n:ℝ)^6*(1/2)^((n+1)/2)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have hcard : ((Finset.range n).filter (fun i => ¬ 2*i ≤ n)).card ≤ n := by
            calc _ ≤ (Finset.range n).card := Finset.card_filter_le _ _
              _ = n := Finset.card_range n
          exact_mod_cast hcard
      _ = (n:ℝ)^7/2^((n+1)/2) := by rw [div_pow, one_pow]; ring

theorem tendsto_R : Tendsto (fun n:ℕ => Rfun n) atTop (nhds 0) := by
  have hbnd : Tendsto (fun n:ℕ => Q 6/(n:ℝ) + (n:ℝ)^7/2^((n+1)/2)) atTop (nhds 0) := by
    have h1 : Tendsto (fun n:ℕ => Q 6/(n:ℝ)) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (Q 6)
    have h2 : Tendsto (fun n:ℕ => (n:ℝ)^7/2^((n+1)/2)) atTop (nhds 0) := tendsto_aux'
    simpa using h1.add h2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbnd
  · filter_upwards with n; exact Rfun_nonneg n
  · filter_upwards [eventually_ge_atTop 1] with n hn; exact Rfun_le n hn

theorem analytic :
    Tendsto (fun n:ℕ => (n:ℝ)^6 * Mn n / 2^(n+1) - poly5 n) atTop (nhds 0) := by
  have hmain : Tendsto (fun n:ℕ => ((n:ℝ)^6*Tfun n/2^(n+1) - poly5 n)) atTop (nhds 0) := by
    have hadd := tendsto_sumpart.add tendsto_R
    rw [add_zero] at hadd
    apply hadd.congr'
    filter_upwards with n
    exact (hTeq n).symm
  have hsub := hmain.sub hH
  rw [sub_zero] at hsub
  apply hsub.congr'
  filter_upwards with n
  rw [Mn_split]
  ring

end TestQ

namespace TestL1

noncomputable def l1norm (p : Polynomial ℂ) : ℝ := ∑ i ∈ range (p.natDegree + 1), ‖p.coeff i‖

theorem l1norm_nonneg (p : Polynomial ℂ) : 0 ≤ l1norm p := by
  apply Finset.sum_nonneg; intro i _; positivity

/-- Sum over a larger range equals l1norm. -/
theorem l1norm_eq_sum_range (p : Polynomial ℂ) (N : ℕ) (hN : p.natDegree < N) :
    l1norm p = ∑ i ∈ range N, ‖p.coeff i‖ := by
  rw [l1norm]
  rw [← Finset.sum_range_add_sum_Ico _ (Nat.succ_le_of_lt hN)]
  have : ∑ i ∈ Finset.Ico (p.natDegree + 1) N, ‖p.coeff i‖ = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_Ico] at hi
    rw [coeff_eq_zero_of_natDegree_lt (by omega), norm_zero]
  linarith [this]

theorem norm_coeff_le_l1norm (p : Polynomial ℂ) (k : ℕ) : ‖p.coeff k‖ ≤ l1norm p := by
  rcases lt_or_ge p.natDegree k with hk | hk
  · rw [coeff_eq_zero_of_natDegree_lt hk, norm_zero]
    exact l1norm_nonneg p
  · apply Finset.single_le_sum (f := fun i => ‖p.coeff i‖) (fun i _ => by positivity)
    rw [Finset.mem_range]; omega

theorem l1norm_mul_le (p q : Polynomial ℂ) : l1norm (p * q) ≤ l1norm p * l1norm q := by
  set N := p.natDegree + q.natDegree + 1 with hN
  have hpq : (p*q).natDegree < N := lt_of_le_of_lt natDegree_mul_le (by omega)
  have hp : p.natDegree < N := by omega
  have hq : q.natDegree < N := by omega
  rw [l1norm_eq_sum_range (p*q) N hpq, l1norm_eq_sum_range p N hp, l1norm_eq_sum_range q N hq]
  -- ∑ n ‖(pq).coeff n‖ ≤ ∑ n ∑ antidiag ‖..‖‖..‖ ≤ product
  have step1 : ∀ n, ‖(p*q).coeff n‖ ≤ ∑ x ∈ antidiagonal n, ‖p.coeff x.1‖ * ‖q.coeff x.2‖ := by
    intro n
    rw [coeff_mul]
    calc ‖∑ x ∈ antidiagonal n, p.coeff x.1 * q.coeff x.2‖
        ≤ ∑ x ∈ antidiagonal n, ‖p.coeff x.1 * q.coeff x.2‖ := norm_sum_le _ _
      _ = ∑ x ∈ antidiagonal n, ‖p.coeff x.1‖ * ‖q.coeff x.2‖ := by
          apply Finset.sum_congr rfl; intro x _; rw [norm_mul]
  calc ∑ n ∈ range N, ‖(p*q).coeff n‖
      ≤ ∑ n ∈ range N, ∑ x ∈ antidiagonal n, ‖p.coeff x.1‖ * ‖q.coeff x.2‖ :=
        Finset.sum_le_sum (fun n _ => step1 n)
    _ = ∑ x ∈ (range N).biUnion (fun n => antidiagonal n), ‖p.coeff x.1‖ * ‖q.coeff x.2‖ := by
        rw [Finset.sum_biUnion]
        intro a _ b _ hab
        simp only [Finset.disjoint_left, Finset.mem_antidiagonal]
        intro x hxa hxb
        exact hab (by omega)
    _ ≤ ∑ x ∈ (range N) ×ˢ (range N), ‖p.coeff x.1‖ * ‖q.coeff x.2‖ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_antidiagonal] at hx
          obtain ⟨n, hn, hxn⟩ := hx
          simp only [Finset.mem_product, Finset.mem_range]
          omega
        · intro x _ _; positivity
    _ = (∑ a ∈ range N, ‖p.coeff a‖) * (∑ b ∈ range N, ‖q.coeff b‖) := by
        rw [Finset.sum_product, Finset.sum_mul_sum]

theorem l1norm_add_le (p q : Polynomial ℂ) : l1norm (p + q) ≤ l1norm p + l1norm q := by
  set N := max (p.natDegree) (q.natDegree) + 1 with hN
  have hpq : (p+q).natDegree < N := lt_of_le_of_lt (natDegree_add_le p q) (by omega)
  have hp : p.natDegree < N := by omega
  have hq : q.natDegree < N := by omega
  rw [l1norm_eq_sum_range (p+q) N hpq, l1norm_eq_sum_range p N hp, l1norm_eq_sum_range q N hq,
      ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [coeff_add]
  exact norm_add_le _ _

theorem l1norm_neg (p : Polynomial ℂ) : l1norm (-p) = l1norm p := by
  simp only [l1norm, natDegree_neg, coeff_neg, norm_neg]

theorem l1norm_one : l1norm (1 : Polynomial ℂ) = 1 := by
  simp [l1norm]

theorem l1norm_monomial (m : ℕ) (a : ℂ) : l1norm (monomial m a) = ‖a‖ := by
  have hnd : (monomial m a).natDegree < m + 1 := lt_of_le_of_lt (natDegree_monomial_le a) (by omega)
  rw [l1norm_eq_sum_range (monomial m a) (m+1) hnd]
  rw [Finset.sum_eq_single m]
  · rw [coeff_monomial]; simp
  · intro b _ hb; rw [coeff_monomial, if_neg (by omega), norm_zero]
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

theorem l1norm_Xpow (m : ℕ) : l1norm ((X : Polynomial ℂ)^m) = 1 := by
  rw [X_pow_eq_monomial, l1norm_monomial]; simp

theorem l1norm_block_le (m : ℕ) : l1norm (1 - (-X : Polynomial ℂ)^m) ≤ 2 := by
  have hb : l1norm ((-X : Polynomial ℂ)^m) = 1 := by
    rcases Nat.even_or_odd m with he | ho
    · rw [he.neg_pow, l1norm_Xpow]
    · rw [ho.neg_pow, l1norm_neg, l1norm_Xpow]
  calc l1norm (1 - (-X : Polynomial ℂ)^m)
      ≤ l1norm (1 : Polynomial ℂ) + l1norm (-(-X:Polynomial ℂ)^m) := by
        rw [sub_eq_add_neg]; exact l1norm_add_le _ _
    _ = 1 + l1norm ((-X:Polynomial ℂ)^m) := by rw [l1norm_one, l1norm_neg]
    _ = 1 + 1 := by rw [hb]
    _ = 2 := by norm_num

theorem l1norm_pow_le (p : Polynomial ℂ) (q : ℕ) : l1norm (p^q) ≤ (l1norm p)^q := by
  induction q with
  | zero => simp [l1norm_one]
  | succ k ih =>
      rw [pow_succ, pow_succ]
      calc l1norm (p^k * p) ≤ l1norm (p^k) * l1norm p := l1norm_mul_le _ _
        _ ≤ (l1norm p)^k * l1norm p := by
            apply mul_le_mul_of_nonneg_right ih (l1norm_nonneg p)

theorem l1norm_prod_le (s : Finset ℕ) (f : ℕ → Polynomial ℂ) :
    l1norm (∏ i ∈ s, f i) ≤ ∏ i ∈ s, l1norm (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [l1norm_one]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      calc l1norm (f a * ∏ i ∈ s, f i) ≤ l1norm (f a) * l1norm (∏ i ∈ s, f i) := l1norm_mul_le _ _
        _ ≤ l1norm (f a) * ∏ i ∈ s, l1norm (f i) := by
            apply mul_le_mul_of_nonneg_left ih (l1norm_nonneg _)

theorem l1norm_C_mul_X (c : ℂ) : l1norm (C c * X) = ‖c‖ := by
  rw [show C c * X = monomial 1 c by rw [← C_mul_X_pow_eq_monomial, pow_one]]
  exact l1norm_monomial 1 c

theorem l1norm_factor_le (c : ℂ) : l1norm (1 + C c * X) ≤ 1 + ‖c‖ := by
  calc l1norm (1 + C c * X) ≤ l1norm (1:Polynomial ℂ) + l1norm (C c * X) := l1norm_add_le _ _
    _ = 1 + ‖c‖ := by rw [l1norm_one, l1norm_C_mul_X]

/- Roots of unity block identities -/

theorem evallemma (m : ℕ) (hm : 0 < m) (w : ℂ) (h : IsPrimitiveRoot w m) :
    ∀ t : ℂ, ∏ i ∈ Finset.range m, (1 - w^i * t) = 1 - t^m := by
  have key : ∀ u : ℂ, u^m - 1 = ∏ i ∈ Finset.range m, (u - w^i) := by
    intro u
    have := X_pow_sub_C_eq_prod h hm (show (1:ℂ)^m = 1 by simp)
    have h2 := congrArg (fun p => Polynomial.eval u p) this
    simp only [eval_sub, eval_pow, eval_X, eval_C, eval_prod, mul_one, map_one,
      eval_one] at h2
    convert h2 using 2
  intro t
  rcases eq_or_ne t 0 with rfl | ht
  · simp [zero_pow hm.ne']
  · have e1 : ∀ i, (1 - w^i * t) = t * (t⁻¹ - w^i) := by
      intro i; rw [mul_sub, mul_inv_cancel₀ ht]; ring
    calc ∏ i ∈ Finset.range m, (1 - w^i * t)
        = ∏ i ∈ Finset.range m, (t * (t⁻¹ - w^i)) := by
          apply Finset.prod_congr rfl; intro i _; rw [e1]
      _ = t^m * ∏ i ∈ Finset.range m, (t⁻¹ - w^i) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
      _ = t^m * ((t⁻¹)^m - 1) := by rw [← key]
      _ = 1 - t^m := by rw [inv_pow, mul_sub, mul_inv_cancel₀ (pow_ne_zero m ht)]; ring

theorem blockid_offset (m : ℕ) (hm : 0 < m) (w : ℂ) (h : IsPrimitiveRoot w m) (a : ℕ) :
    ∏ i ∈ Finset.range m, (1 + C (w^(a+i)) * X) = 1 - (- X)^m := by
  have hwm : w^m = 1 := h.pow_eq_one
  apply Polynomial.funext
  intro t
  rw [eval_prod]
  simp only [eval_add, eval_one, eval_mul, eval_C, eval_X, eval_sub, eval_pow, eval_neg]
  -- reduce ∏ (1 + w^(a+i) t) = 1 - (-t)^m
  have key := evallemma m hm w h (w^a * (-t))
  have hwam : (w^a * (-t))^m = (-t)^m := by
    rw [mul_pow, ← pow_mul, mul_comm a m, pow_mul, hwm, one_pow, one_mul]
  rw [hwam] at key
  rw [← key]
  apply Finset.prod_congr rfl
  intro i _
  rw [pow_add]
  ring

theorem factorization (m : ℕ) (hm : 0 < m) (w : ℂ) (h : IsPrimitiveRoot w m) (q : ℕ) :
    ∏ i ∈ Finset.range (m*q), (1 + C (w^(i+1)) * X) = (1 - (-X)^m)^q := by
  induction q with
  | zero => simp
  | succ k ih =>
      rw [Nat.mul_succ, Finset.prod_range_add, ih, pow_succ]
      congr 1
      rw [← blockid_offset m hm w h (m*k+1)]
      apply Finset.prod_congr rfl
      intro i _
      rw [show m*k+i+1 = m*k+1+i from by ring]

theorem norm_wpow (m : ℕ) (hm : 0 < m) (w : ℂ) (h : IsPrimitiveRoot w m) (j : ℕ) :
    ‖w^j‖ = 1 := by
  have hw1 : ‖w‖ = 1 := by
    have := Complex.norm_eq_one_of_pow_eq_one h.pow_eq_one (by omega)
    exact this
  rw [norm_pow, hw1, one_pow]

theorem l1norm_P_le (m : ℕ) (hm : 0 < m) (w : ℂ) (h : IsPrimitiveRoot w m) (n : ℕ) :
    l1norm (∏ i ∈ Finset.range n, (1 + C (w^(i+1)) * X)) ≤ 2^(n/m + n%m) := by
  have hn : n = m*(n/m) + n%m := (Nat.div_add_mod n m).symm
  set q := n/m
  set s := n%m
  rw [hn, Finset.prod_range_add, factorization m hm w h]
  calc l1norm ((1-(-X:ℂ[X])^m)^q * ∏ i ∈ Finset.range s, (1 + C (w^(m*q+i+1)) * X))
      ≤ l1norm ((1-(-X:ℂ[X])^m)^q) * l1norm (∏ i ∈ Finset.range s, (1 + C (w^(m*q+i+1)) * X)) :=
        l1norm_mul_le _ _
    _ ≤ 2^q * 2^s := by
        apply mul_le_mul
        · calc l1norm ((1-(-X:ℂ[X])^m)^q) ≤ (l1norm (1-(-X:ℂ[X])^m))^q := l1norm_pow_le _ _
            _ ≤ 2^q := by
                apply pow_le_pow_left₀ (l1norm_nonneg _) (l1norm_block_le m)
        · calc l1norm (∏ i ∈ Finset.range s, (1 + C (w^(m*q+i+1)) * X))
              ≤ ∏ i ∈ Finset.range s, l1norm (1 + C (w^(m*q+i+1)) * X) := l1norm_prod_le _ _
            _ ≤ ∏ i ∈ Finset.range s, (2:ℝ) := by
                apply Finset.prod_le_prod
                · intro i _; exact l1norm_nonneg _
                · intro i _
                  calc l1norm (1 + C (w^(m*q+i+1)) * X) ≤ 1 + ‖w^(m*q+i+1)‖ := l1norm_factor_le _
                    _ = 2 := by rw [norm_wpow m hm w h]; norm_num
            _ = 2^s := by rw [Finset.prod_const, Finset.card_range]
        · exact l1norm_nonneg _
        · positivity
    _ = 2^(q+s) := by rw [pow_add]

/-- The key exponent bound: for m ≥ 2, m ≤ n, `n/m + n%m ≤ (n+1)/2`. -/
theorem exp_bound (m n : ℕ) (hm : 2 ≤ m) (hmn : m ≤ n) : n/m + n%m ≤ (n+1)/2 := by
  set q := n/m with hq
  set s := n%m with hs
  have hqs : m * q + s = n := Nat.div_add_mod n m
  have hq1 : 1 ≤ q := (Nat.one_le_div_iff (by omega)).2 hmn
  have hslt : s < m := Nat.mod_lt n (by omega)
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  have hmq : m * q = 2*q + (m-2)*q := by
    rw [← Nat.add_mul, Nat.add_sub_cancel' hm]
  have hmm : (m-2) ≤ (m-2)*q := Nat.le_mul_of_pos_right (m-2) hq1
  omega

theorem coeff_prod_formula (s : Finset ℕ) (a : ℕ → ℂ) (k : ℕ) :
    (∏ i ∈ s, (C (a i) * X + 1)).coeff k = ∑ t ∈ s.powersetCard k, ∏ i ∈ t, a i := by
  rw [Finset.prod_add]
  have hstep : ∀ t ∈ s.powerset, (∏ i ∈ t, C (a i) * X) * (∏ _i ∈ s \ t, 1)
      = C (∏ i ∈ t, a i) * X ^ t.card := by
    intro t ht
    rw [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib, Finset.prod_const, map_prod]
  rw [Finset.sum_congr rfl hstep, Polynomial.finset_sum_coeff, Finset.powersetCard_eq_filter,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t ht
  rw [coeff_C_mul, coeff_X_pow]
  by_cases hc : t.card = k
  · simp [hc]
  · rw [if_neg (fun h => hc h.symm), if_neg hc, mul_zero]

theorem prod_bridge (n : ℕ) (w : ℂ) :
    (∏ i ∈ Finset.Icc 1 n, (C (w^i) * X + 1)) = ∏ i ∈ Finset.range n, (1 + C (w^(i+1)) * X) := by
  induction n with
  | zero => simp
  | succ p ih =>
      rw [Finset.prod_Icc_succ_top (by omega), ih, Finset.prod_range_succ]
      ring

theorem Cj_l1_bound (n k : ℕ) (w : ℂ) (m : ℕ) (hm2 : 2 ≤ m) (hmn : m ≤ n) (h : IsPrimitiveRoot w m) :
    ‖(∏ i ∈ Finset.Icc 1 n, (C (w^i) * X + 1)).coeff k‖ ≤ 2^((n+1)/2) := by
  rw [prod_bridge]
  calc ‖(∏ i ∈ Finset.range n, (1 + C (w^(i+1)) * X)).coeff k‖
      ≤ l1norm (∏ i ∈ Finset.range n, (1 + C (w^(i+1)) * X)) := norm_coeff_le_l1norm _ _
    _ ≤ 2^(n/m + n%m) := l1norm_P_le m (by omega) w h n
    _ ≤ 2^((n+1)/2) := by
        apply pow_le_pow_right₀ (by norm_num)
        exact exp_bound m n hm2 hmn

theorem geomfilter (k : ℕ) (hk : 0 < k) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ k) (s : ℕ) :
    ∑ j ∈ Finset.range k, (ζ^s)^j = if k ∣ s then (k:ℂ) else 0 := by
  by_cases hd : k ∣ s
  · rw [if_pos hd]
    have hz : ζ^s = 1 := (hζ.pow_eq_one_iff_dvd s).2 hd
    rw [hz]
    simp
  · rw [if_neg hd]
    have hne : ζ^s ≠ 1 := fun h => hd ((hζ.pow_eq_one_iff_dvd s).1 h)
    rw [geom_sum_eq hne]
    have hk1 : (ζ^s)^k = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    rw [hk1]
    simp

open Complex in
/-- Number of `k`-subsets of `{1..n}` whose sum is divisible by `k`. -/
noncomputable def Ncount (n k : ℕ) : ℕ :=
  (((Finset.Icc 1 n).powersetCard k).filter (fun S => k ∣ S.sum id)).card

open Complex in
theorem Ndiff_bound (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    |(Ncount n k : ℝ) - (n.choose k : ℝ) / k| ≤ 2^((n+1)/2) := by
  classical
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / k) with hζdef
  have hζ : IsPrimitiveRoot ζ k := Complex.isPrimitiveRoot_exp k (by omega)
  set f : ℕ → ℂ := fun j => (∏ i ∈ Finset.Icc 1 n, (C ((ζ^j)^i) * X + 1)).coeff k with hf
  -- (A) closed form for f j
  have hA : ∀ j, f j = ∑ t ∈ (Finset.Icc 1 n).powersetCard k, (ζ^j)^(t.sum id) := by
    intro j
    rw [hf]
    simp only
    rw [coeff_prod_formula]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.prod_pow_eq_pow_sum]
    rfl
  -- (B) sum over j
  have hsum : ∑ j ∈ Finset.range k, f j = (k : ℂ) * (Ncount n k : ℂ) := by
    simp_rw [hA]
    rw [Finset.sum_comm]
    have hterm : ∀ t ∈ (Finset.Icc 1 n).powersetCard k,
        ∑ j ∈ Finset.range k, (ζ^j)^(t.sum id)
          = if k ∣ t.sum id then (k:ℂ) else 0 := by
      intro t _
      rw [← geomfilter k (by omega) ζ hζ (t.sum id)]
      apply Finset.sum_congr rfl
      intro j _
      rw [← pow_mul, mul_comm j, pow_mul]
    rw [Finset.sum_congr rfl hterm]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
    rw [Ncount, nsmul_eq_mul, mul_comm]
  -- (C) f 0 = choose
  have hC0 : f 0 = (n.choose k : ℂ) := by
    rw [hA]
    simp only [pow_zero, one_pow]
    rw [Finset.sum_const, Finset.card_powersetCard, Nat.card_Icc]
    simp
  -- split range k
  have hsplit : ∑ j ∈ Finset.range k, f j = f 0 + ∑ j ∈ Finset.Ico 1 k, f j := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive f (Nat.zero_le 1) hk]
    congr 1
    rw [Nat.Ico_zero_eq_range, Finset.sum_range_one]
  -- the difference
  set D : ℝ := (Ncount n k : ℝ) - (n.choose k : ℝ) / k with hD
  have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hk
  have hDc : (D : ℂ) = (∑ j ∈ Finset.Ico 1 k, f j) / (k : ℂ) := by
    have h1 : (k:ℂ) * (Ncount n k : ℂ) = (n.choose k : ℂ) + ∑ j ∈ Finset.Ico 1 k, f j := by
      rw [← hsum, hsplit, hC0]
    have hDeq : (D : ℂ) = (Ncount n k : ℂ) - (n.choose k : ℂ) / (k:ℂ) := by
      rw [hD]; push_cast; ring
    rw [hDeq, eq_div_iff hkc, sub_mul, div_mul_cancel₀ _ hkc]
    linear_combination h1
  -- bound each term
  have hbound : ∀ j ∈ Finset.Ico 1 k, ‖f j‖ ≤ 2^((n+1)/2) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    have hfj : f j = (∏ i ∈ Finset.Icc 1 n, (C ((ζ^j)^i) * X + 1)).coeff k := by rw [hf]
    rw [hfj]
    have hwk : (ζ^j)^k = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have hwne : (ζ^j) ≠ 1 := by
      intro h
      have hdvd := (hζ.pow_eq_one_iff_dvd j).1 h
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    have hfin : IsOfFinOrder (ζ^j) := isOfFinOrder_iff_pow_eq_one.2 ⟨k, by omega, hwk⟩
    have hmpos : 0 < orderOf (ζ^j) := hfin.orderOf_pos
    have hmdvd : orderOf (ζ^j) ∣ k := orderOf_dvd_of_pow_eq_one hwk
    have hprim : IsPrimitiveRoot (ζ^j) (orderOf (ζ^j)) := IsPrimitiveRoot.orderOf (ζ^j)
    have hm1 : orderOf (ζ^j) ≠ 1 := by
      intro h
      apply hwne
      have hpo := pow_orderOf_eq_one (ζ^j)
      rw [h, pow_one] at hpo
      exact hpo
    have hm2 : 2 ≤ orderOf (ζ^j) := by omega
    have hmn : orderOf (ζ^j) ≤ n := le_trans (Nat.le_of_dvd (by omega) hmdvd) hkn
    exact Cj_l1_bound n k (ζ^j) (orderOf (ζ^j)) hm2 hmn hprim
  -- combine
  have hnormD : |D| = ‖(D:ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hnormD, hDc, norm_div]
  rw [Complex.norm_natCast]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < (k:ℝ))]
  calc ‖∑ j ∈ Finset.Ico 1 k, f j‖
      ≤ ∑ j ∈ Finset.Ico 1 k, ‖f j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.Ico 1 k, (2:ℝ)^((n+1)/2) := Finset.sum_le_sum hbound
    _ = (k-1) * 2^((n+1)/2) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        congr 1
        push_cast [Nat.cast_sub hk]
        ring
    _ ≤ 2^((n+1)/2) * (k:ℝ) := by
        have hkr : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
        nlinarith [pow_pos (show (0:ℝ)<2 by norm_num) ((n+1)/2), hkr]

end TestL1

/- Combinatorial error term and final assembly -/

noncomputable def En (n : ℕ) : ℝ := a_real n - TestQ.Mn n

theorem A051293_eq_sum (n : ℕ) : A051293 n = ∑ k ∈ Finset.Icc 1 n, TestL1.Ncount n k := by
  rw [A051293]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun S => S.card) (t := Finset.Icc 1 n)]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [TestL1.Ncount]
    congr 1
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hsub, hne, hdvd⟩, hcard⟩
      exact ⟨⟨hsub, hcard⟩, hcard ▸ hdvd⟩
    · rintro ⟨⟨hsub, hcard⟩, hdvd⟩
      refine ⟨⟨hsub, ?_, ?_⟩, hcard⟩
      · rw [← Finset.card_pos]; omega
      · rw [hcard]; exact hdvd
  · intro S hS
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨hsub, hne, _⟩ := hS
    simp only [Finset.mem_coe, Finset.mem_Icc]
    refine ⟨Finset.card_pos.2 hne, ?_⟩
    calc S.card ≤ (Finset.Icc 1 n).card := Finset.card_le_card hsub
      _ = n := by rw [Nat.card_Icc]; omega

theorem a_real_eq (n : ℕ) : a_real n = ∑ k ∈ Finset.Icc 1 n, (TestL1.Ncount n k : ℝ) := by
  rw [a_real, A051293_eq_sum, Nat.cast_sum]

theorem combi (n : ℕ) : |En n| ≤ (n:ℝ) * 2^((n+1)/2) := by
  have hEn : En n = ∑ k ∈ Finset.Icc 1 n, ((TestL1.Ncount n k : ℝ) - (n.choose k:ℝ)/k) := by
    rw [En, a_real_eq, TestQ.Mn, ← Finset.sum_sub_distrib]
  rw [hEn]
  calc |∑ k ∈ Finset.Icc 1 n, ((TestL1.Ncount n k:ℝ) - (n.choose k:ℝ)/k)|
      ≤ ∑ k ∈ Finset.Icc 1 n, |(TestL1.Ncount n k:ℝ) - (n.choose k:ℝ)/k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Icc 1 n, (2:ℝ)^((n+1)/2) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [Finset.mem_Icc] at hk
        exact TestL1.Ndiff_bound n k hk.1 hk.2
    _ = (n:ℝ) * 2^((n+1)/2) := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]

theorem Epart : Tendsto (fun n : ℕ => (n:ℝ)^6 * En n / 2^(n+1)) atTop (nhds 0) := by
  apply squeeze_zero_norm _ TestQ.tendsto_aux'
  intro n
  set A : ℝ := 2^((n+1)/2) with hA
  set B : ℝ := 2^(n+1) with hB
  have hApos : (0:ℝ) < A := by rw [hA]; positivity
  have hBpos : (0:ℝ) < B := by rw [hB]; positivity
  have hAA : A * A ≤ B := by
    rw [hA, hB, ← pow_add]; apply pow_le_pow_right₀ (by norm_num); omega
  have hEn' : |En n| ≤ (n:ℝ) * A := combi n
  have hn6 : (0:ℝ) ≤ (n:ℝ)^6 := by positivity
  rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_pow,
      abs_of_nonneg (le_of_lt hBpos)]
  have habsn : |(n:ℝ)| = (n:ℝ) := abs_of_nonneg (by positivity)
  rw [habsn, div_le_div_iff₀ hBpos hApos]
  calc (n:ℝ)^6 * |En n| * A ≤ (n:ℝ)^6 * ((n:ℝ) * A) * A := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hApos)
        apply mul_le_mul_of_nonneg_left hEn' hn6
    _ = (n:ℝ)^7 * (A * A) := by ring
    _ ≤ (n:ℝ)^7 * B := by apply mul_le_mul_of_nonneg_left hAA (by positivity)

theorem oeis_51293_conjecture_0 :
    Tendsto
      (fun n : ℕ =>
        -- The numerator f(n)
        (a_real n - ((2 : ℝ) ^ (n + 1) / (n : ℝ)) * (
          (1 : ℝ)
          + 1 / (n : ℝ)
          + 3 / ((n : ℝ) ^ 2)
          + 13 / ((n : ℝ) ^ 3)
          + 75 / ((n : ℝ) ^ 4)
          + 541 / ((n : ℝ) ^ 5)
        ))
        /
        -- The denominator g(n)
        (((2 : ℝ) ^ (n + 1)) / ((n : ℝ) ^ 6))
      )
      atTop
      (nhds 0) := by
  have hsum := TestQ.analytic.add Epart
  simp only [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  have h2 : (2:ℝ)^(n+1) ≠ 0 := by positivity
  have hP : (n:ℝ)^5 * ((1:ℝ) + 1/(n:ℝ) + 3/((n:ℝ)^2) + 13/((n:ℝ)^3) + 75/((n:ℝ)^4) + 541/((n:ℝ)^5))
      = TestQ.poly5 n := by
    rw [TestQ.poly5]; field_simp
  have hEna : a_real n = TestQ.Mn n + En n := by rw [En]; ring
  have key : (a_real n - ((2 : ℝ) ^ (n + 1) / (n : ℝ)) * ((1 : ℝ) + 1 / (n : ℝ) + 3 / ((n : ℝ) ^ 2)
        + 13 / ((n : ℝ) ^ 3) + 75 / ((n : ℝ) ^ 4) + 541 / ((n : ℝ) ^ 5)))
        / (((2 : ℝ) ^ (n + 1)) / ((n : ℝ) ^ 6))
      = (n:ℝ)^6 * TestQ.Mn n / 2^(n+1) - TestQ.poly5 n + (n:ℝ)^6 * En n / 2^(n+1) := by
    rw [hEna, ← hP]
    field_simp
    ring
  simpa using key.symm
