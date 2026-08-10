import FormalConjectures.Util.ProblemImports

open Finset Nat Real
open scoped Nat.Prime
open ArithmeticFunction hiding log
open scoped ArithmeticFunction

namespace ChebLB

noncomputable section

/-- The Stirling-type upper bound: `log N! ≤ N log N - N + (log N)/2 + 1` for `N ≥ 1`. -/
theorem log_factorial_le_stirling {n : ℕ} (hn : n ≠ 0) :
    Real.log (n !) ≤ n * Real.log n - n + Real.log n / 2 + 1 := by
  -- stirlingSeq n ≤ stirlingSeq 1 = e/√2, so log (stirlingSeq n) ≤ 1 - (log 2)/2.
  have hpos : 0 < Stirling.stirlingSeq n := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    exact Stirling.stirlingSeq'_pos m
  have hanti : Stirling.stirlingSeq n ≤ Stirling.stirlingSeq 1 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have := Stirling.stirlingSeq'_antitone (Nat.zero_le m)
    simpa [Function.comp] using this
  have h1 : Stirling.stirlingSeq 1 = Real.exp 1 / Real.sqrt 2 := Stirling.stirlingSeq_one
  -- log (stirlingSeq n) = log n! - (1/2) log (2 n) - n * log (n / e)
  have hform := Stirling.log_stirlingSeq_formula n
  -- bound: log (stirlingSeq n) ≤ log (stirlingSeq 1) = 1 - (log 2)/2
  have hlog1 : Real.log (Stirling.stirlingSeq 1) = 1 - Real.log 2 / 2 := by
    rw [h1, Real.log_div (by positivity) (by positivity), Real.log_exp,
        Real.log_sqrt (by norm_num)]
  have hle : Real.log (Stirling.stirlingSeq n) ≤ 1 - Real.log 2 / 2 := by
    rw [← hlog1]
    exact Real.log_le_log hpos hanti
  rw [hform] at hle
  -- expand: log (2 n) = log 2 + log n, log (n / e) = log n - 1
  have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have e1 : Real.log (2 * (n:ℝ)) = Real.log 2 + Real.log n := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hnpos)]
  have e2 : Real.log ((n:ℝ) / Real.exp 1) = Real.log n - 1 := by
    rw [Real.log_div (ne_of_gt hnpos) (by positivity), Real.log_exp]
  rw [e1, e2] at hle
  nlinarith [hle]

/-- `ω u = u log u - u` has derivative `log u` for `u > 0`. -/
theorem hasDerivAt_omega {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (fun x => x * Real.log x - x) (Real.log u) u := by
  have h1 : HasDerivAt (fun x => x * Real.log x) (Real.log u + 1) u :=
    Real.hasDerivAt_mul_log hu
  have h2 : HasDerivAt (fun x : ℝ => x) 1 u := hasDerivAt_id u
  have := h1.sub h2
  simpa using this

/-- Lower bound of `ω` at the floor: `ω ⌊y⌋ ≥ ω y - log y` for `y ≥ 1`. -/
theorem omega_floor_lower {y : ℝ} (hy : 1 ≤ y) :
    (⌊y⌋₊ : ℝ) * Real.log ⌊y⌋₊ - ⌊y⌋₊ ≥ y * Real.log y - y - Real.log y := by
  set N := (⌊y⌋₊ : ℕ) with hN
  have hNle : (N : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hN1 : 1 ≤ N := Nat.one_le_floor_iff y |>.mpr hy
  have hN1' : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
  rcases eq_or_lt_of_le hNle with heq | hlt
  · -- y = N : equality up to - log y, and log y ≥ 0
    rw [heq]; have : 0 ≤ Real.log y := Real.log_nonneg hy; linarith
  · -- N < y : MVT on [N, y]
    have hcont : ContinuousOn (fun x => x * Real.log x - x) (Set.Icc (N:ℝ) y) := by
      apply ContinuousOn.sub
      · exact (continuousOn_id.mul (Real.continuousOn_log.mono (by
          intro x hx; simp only [Set.mem_Icc] at hx; simp only [Set.mem_compl_iff,
            Set.mem_singleton_iff]; linarith [hx.1, hN1'])))
      · exact continuousOn_id
    have hderiv : ∀ x ∈ Set.Ioo (N:ℝ) y, HasDerivAt (fun x => x * Real.log x - x) (Real.log x) x := by
      intro x hx; simp only [Set.mem_Ioo] at hx
      exact hasDerivAt_omega (by linarith [hx.1, hN1'])
    obtain ⟨c, hc, hcslope⟩ := exists_hasDerivAt_eq_slope _ _ hlt hcont hderiv
    simp only [Set.mem_Ioo] at hc
    have hyN : (0:ℝ) < y - N := by linarith
    have hlogc : Real.log c ≤ Real.log y := Real.log_le_log (by linarith [hN1', hc.1]) (le_of_lt hc.2)
    have hlogc0 : 0 ≤ Real.log c := Real.log_nonneg (by linarith [hN1', hc.1])
    have hlogy0 : 0 ≤ Real.log y := Real.log_nonneg hy
    -- f y - f N = log c * (y - N)
    have hfdiff : (y * Real.log y - y) - ((N:ℝ) * Real.log N - N) = Real.log c * (y - N) := by
      field_simp at hcslope ⊢
      linarith [hcslope]
    have hyN1 : y - (N:ℝ) ≤ 1 := by
      have := Nat.lt_floor_add_one y; rw [← hN] at this; push_cast at this ⊢; linarith
    -- log c * (y - N) ≤ log y * 1 = log y
    have : Real.log c * (y - N) ≤ Real.log y := by
      calc Real.log c * (y - N) ≤ Real.log y * (y - N) := by
            apply mul_le_mul_of_nonneg_right hlogc (le_of_lt hyN)
        _ ≤ Real.log y * 1 := by apply mul_le_mul_of_nonneg_left hyN1 hlogy0
        _ = Real.log y := mul_one _
    linarith [hfdiff, this]

/-- Upper bound of `ω` at the floor: `ω ⌊y⌋ ≤ ω y` for `y ≥ 1`. -/
theorem omega_floor_upper {y : ℝ} (hy : 1 ≤ y) :
    (⌊y⌋₊ : ℝ) * Real.log ⌊y⌋₊ - ⌊y⌋₊ ≤ y * Real.log y - y := by
  set N := (⌊y⌋₊ : ℕ) with hN
  have hNle : (N : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hN1 : 1 ≤ N := Nat.one_le_floor_iff y |>.mpr hy
  have hN1' : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
  rcases eq_or_lt_of_le hNle with heq | hlt
  · rw [heq]
  · have hcont : ContinuousOn (fun x => x * Real.log x - x) (Set.Icc (N:ℝ) y) := by
      apply ContinuousOn.sub
      · exact (continuousOn_id.mul (Real.continuousOn_log.mono (by
          intro x hx; simp only [Set.mem_Icc] at hx; simp only [Set.mem_compl_iff,
            Set.mem_singleton_iff]; linarith [hx.1, hN1'])))
      · exact continuousOn_id
    have hderiv : ∀ x ∈ Set.Ioo (N:ℝ) y, HasDerivAt (fun x => x * Real.log x - x) (Real.log x) x := by
      intro x hx; simp only [Set.mem_Ioo] at hx
      exact hasDerivAt_omega (by linarith [hx.1, hN1'])
    obtain ⟨c, hc, hcslope⟩ := exists_hasDerivAt_eq_slope _ _ hlt hcont hderiv
    simp only [Set.mem_Ioo] at hc
    have hyN : (0:ℝ) < y - N := by linarith
    have hlogc0 : 0 ≤ Real.log c := Real.log_nonneg (by linarith [hN1', hc.1])
    have hfdiff : (y * Real.log y - y) - ((N:ℝ) * Real.log N - N) = Real.log c * (y - N) := by
      field_simp at hcslope ⊢
      linarith [hcslope]
    nlinarith [hfdiff, mul_nonneg hlogc0 (le_of_lt hyN)]

/-- Per-term lower bound (used for positive coefficients):
`log ⌊y⌋! ≥ y log y - y - log y + (log 2π)/2` for `y ≥ 1`. -/
theorem term_lower {y : ℝ} (hy : 1 ≤ y) :
    Real.log ((⌊y⌋₊)!) ≥ y * Real.log y - y - Real.log y + Real.log (2 * Real.pi) / 2 := by
  have hN1 : 1 ≤ ⌊y⌋₊ := Nat.one_le_floor_iff y |>.mpr hy
  have hNne : (⌊y⌋₊ : ℕ) ≠ 0 := by omega
  have hstir := Stirling.le_log_factorial_stirling hNne
  have hlogN : (0:ℝ) ≤ Real.log ⌊y⌋₊ := by
    apply Real.log_nonneg; exact_mod_cast hN1
  have homega := omega_floor_lower hy
  -- log ⌊y⌋! ≥ ⌊y⌋ log⌊y⌋ - ⌊y⌋ + log⌊y⌋/2 + log2π/2
  -- and ⌊y⌋log⌊y⌋ - ⌊y⌋ ≥ y log y - y - log y
  linarith [hstir, hlogN, homega]

/-- Per-term upper bound (used for negative coefficients):
`log ⌊y⌋! ≤ y log y - y + (log y)/2 + 1` for `y ≥ 1`. -/
theorem term_upper {y : ℝ} (hy : 1 ≤ y) :
    Real.log ((⌊y⌋₊)!) ≤ y * Real.log y - y + Real.log y / 2 + 1 := by
  have hN1 : 1 ≤ ⌊y⌋₊ := Nat.one_le_floor_iff y |>.mpr hy
  have hNne : (⌊y⌋₊ : ℕ) ≠ 0 := by omega
  have hstir := log_factorial_le_stirling hNne
  have hNle : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hlogNle : Real.log ⌊y⌋₊ ≤ Real.log y :=
    Real.log_le_log (by exact_mod_cast hN1) hNle
  have homega := omega_floor_upper hy
  linarith [hstir, hlogNle, homega]

/-- The per-term "remainder" function. -/
def rterm (a : ℕ → ℤ) (Q k : ℕ) (x : ℝ) : ℝ :=
  if 0 < a k then ((a k : ℝ)/Q) * (- Real.log (x/k) + Real.log (2 * Real.pi)/2)
  else ((a k : ℝ)/Q) * (Real.log (x/k)/2 + 1)

/-- Per-term lower bound combining Stirling with the `ω` floor bounds. -/
theorem term_bound (a : ℕ → ℤ) (Q k : ℕ) (hQ : 0 < Q) (hk : 0 < k) (x : ℝ)
    (hxk : (1:ℝ) ≤ x/k) :
    ((a k : ℝ)/Q) * Real.log ((⌊x/k⌋₊)!) ≥
      ((a k : ℝ)/Q) * ((x/k) * (Real.log (x/k) - 1)) + rterm a Q k x := by
  set y := x/k with hy
  set c := (a k : ℝ)/Q with hc
  rcases lt_or_ge 0 (a k) with hpos | hnpos
  · -- a k > 0
    have hcpos : 0 ≤ c := by
      rw [hc]; positivity
    have hlow := term_lower hxk
    rw [rterm, if_pos hpos]
    -- log⌊y⌋! ≥ y(log y -1) - log y + log2π/2
    have : Real.log ((⌊y⌋₊)!) ≥ y * (Real.log y - 1) + (- Real.log y + Real.log (2*Real.pi)/2) := by
      nlinarith [hlow]
    nlinarith [mul_le_mul_of_nonneg_left this hcpos]
  · -- a k ≤ 0
    have hcneg : c ≤ 0 := by
      rw [hc]; apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      exact_mod_cast hnpos
    have hup := term_upper hxk
    rw [rterm, if_neg (by omega)]
    have : Real.log ((⌊y⌋₊)!) ≤ y * (Real.log y - 1) + (Real.log y/2 + 1) := by
      nlinarith [hup]
    nlinarith [mul_le_mul_of_nonpos_left this hcneg]

/-- The leading constant `C` of the combination. -/
def Cval (kset : Finset ℕ) (a : ℕ → ℤ) (Q : ℕ) : ℝ :=
  - ∑ k ∈ kset, (a k : ℝ) * Real.log k / (Q * k)

/-- The key identity: `∑ (a_k/Q)·(x/k)(log(x/k)-1) = C·x`. -/
theorem sum_M_eq (kset : Finset ℕ) (a : ℕ → ℤ) (Q : ℕ) (hQ : 0 < Q)
    (hk0 : ∀ k ∈ kset, 0 < k) (hsum0 : ∑ k ∈ kset, (a k : ℝ)/k = 0)
    (x : ℝ) (hx0 : 0 < x) :
    ∑ k ∈ kset, ((a k : ℝ)/Q) * ((x/k) * (Real.log (x/k) - 1)) = Cval kset a Q * x := by
  have hQ' : (Q:ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  -- rewrite each term
  have hMk : ∀ k ∈ kset, ((a k : ℝ)/Q) * ((x/k) * (Real.log (x/k) - 1))
      = x * ((a k : ℝ)/(Q*k) * (Real.log x - Real.log k - 1)) := by
    intro k hk
    have hkpos := hk0 k hk
    have hkne : (k:ℝ) ≠ 0 := by exact_mod_cast hkpos.ne'
    rw [Real.log_div hx0.ne' hkne]
    field_simp
  rw [Finset.sum_congr rfl hMk, ← Finset.mul_sum]
  -- inner sum
  have hS0 : ∑ k ∈ kset, (a k : ℝ)/(Q*k) = 0 := by
    have : ∑ k ∈ kset, (a k : ℝ)/(Q*k) = (1/Q) * ∑ k ∈ kset, (a k : ℝ)/k := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k hk
      rw [mul_comm (Q:ℝ) (k:ℝ)]; field_simp
    rw [this, hsum0, mul_zero]
  have hinner : ∑ k ∈ kset, (a k : ℝ)/(Q*k) * (Real.log x - Real.log k - 1)
      = Cval kset a Q := by
    have expand : ∀ k ∈ kset, (a k : ℝ)/(Q*k) * (Real.log x - Real.log k - 1)
        = (a k : ℝ)/(Q*k) * Real.log x - (a k : ℝ) * Real.log k/(Q*k) - (a k : ℝ)/(Q*k) := by
      intro k hk; field_simp
    have h1 : ∑ k ∈ kset, (a k : ℝ)/(Q*k) * Real.log x = 0 := by
      rw [← Finset.sum_mul, hS0, zero_mul]
    rw [Finset.sum_congr rfl expand, Finset.sum_sub_distrib, Finset.sum_sub_distrib, h1, hS0]
    simp [Cval]
  rw [hinner, mul_comm]

/-- Main combined lower bound:
`∑ (a_k/Q)·log⌊x/k⌋! ≥ C·x + ∑ rterm`. -/
theorem A_lb_bound (kset : Finset ℕ) (a : ℕ → ℤ) (Q : ℕ) (hQ : 0 < Q)
    (hk0 : ∀ k ∈ kset, 0 < k) (hsum0 : ∑ k ∈ kset, (a k : ℝ)/k = 0)
    (x : ℝ) (hx0 : 0 < x) (hxk : ∀ k ∈ kset, (1:ℝ) ≤ x/k) :
    ∑ k ∈ kset, ((a k : ℝ)/Q) * Real.log ((⌊x/k⌋₊)!)
      ≥ Cval kset a Q * x + ∑ k ∈ kset, rterm a Q k x := by
  have hstep : ∑ k ∈ kset, ((a k : ℝ)/Q) * Real.log ((⌊x/k⌋₊)!)
      ≥ ∑ k ∈ kset, (((a k : ℝ)/Q) * ((x/k) * (Real.log (x/k) - 1)) + rterm a Q k x) := by
    apply Finset.sum_le_sum
    intro k hk
    exact term_bound a Q k hQ (hk0 k hk) x (hxk k hk)
  rw [Finset.sum_add_distrib, sum_M_eq kset a Q hQ hk0 hsum0 x hx0] at hstep
  exact hstep

/-- The coefficient of `-log x` in the remainder sum. -/
def Kval (kset : Finset ℕ) (a : ℕ → ℤ) (Q : ℕ) : ℝ :=
  ∑ k ∈ kset, (if 0 < a k then (a k : ℝ)/Q else -(a k : ℝ)/(2*Q))

/-- The constant term in the remainder sum. -/
def Lcval (kset : Finset ℕ) (a : ℕ → ℤ) (Q : ℕ) : ℝ :=
  ∑ k ∈ kset, (if 0 < a k then (a k : ℝ)/Q * (Real.log k + Real.log (2*Real.pi)/2)
               else (a k : ℝ)/Q * (1 - Real.log k/2))

/-- `∑ rterm = -K·log x + Lc`. -/
theorem sum_rterm_eq (kset : Finset ℕ) (a : ℕ → ℤ) (Q : ℕ) (hQ : 0 < Q)
    (hk0 : ∀ k ∈ kset, 0 < k) (x : ℝ) (hx0 : 0 < x) :
    ∑ k ∈ kset, rterm a Q k x = - Kval kset a Q * Real.log x + Lcval kset a Q := by
  have hQ' : (Q:ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hper : ∀ k ∈ kset, rterm a Q k x
      = (if 0 < a k then (a k : ℝ)/Q else -(a k : ℝ)/(2*Q)) * (-Real.log x)
        + (if 0 < a k then (a k : ℝ)/Q * (Real.log k + Real.log (2*Real.pi)/2)
           else (a k : ℝ)/Q * (1 - Real.log k/2)) := by
    intro k hk
    have hkne : (k:ℝ) ≠ 0 := by exact_mod_cast (hk0 k hk).ne'
    rw [rterm]
    rcases lt_or_ge 0 (a k) with hpos | hnpos
    · rw [if_pos hpos, if_pos hpos, if_pos hpos, Real.log_div hx0.ne' hkne]; ring
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), Real.log_div hx0.ne' hkne]; ring
  rw [Finset.sum_congr rfl hper, Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [Kval, Lcval]
  ring

theorem log_factorial_eq (N : ℕ) :
    Real.log (N !) = ∑ d ∈ Finset.Ioc 0 N, vonMangoldt d * ((N / d : ℕ) : ℝ) := by
  have hIoc : Finset.Ioc 0 N = Finset.Ico 1 (N + 1) := by
    ext x; simp [Nat.succ_le_iff]
  have hfac : (N ! : ℝ) = ∏ m ∈ Finset.Ioc 0 N, (m : ℝ) := by
    rw [hIoc, ← Nat.cast_prod, Finset.prod_Ico_id_eq_factorial]
  rw [hfac, Real.log_prod]
  swap
  · intro m hm
    simp only [Finset.mem_Ioc] at hm
    exact_mod_cast hm.1.ne'
  have h1 : ∀ m ∈ Finset.Ioc 0 N, Real.log (m : ℝ) = ∑ d ∈ m.divisors, vonMangoldt d := by
    intro m hm; rw [vonMangoldt_sum]
  rw [Finset.sum_congr rfl h1]
  -- rewrite each inner sum over the common index set Ioc 0 N
  have h2 : ∀ m ∈ Finset.Ioc 0 N, (∑ d ∈ m.divisors, vonMangoldt d)
      = ∑ d ∈ Finset.Ioc 0 N, (if d ∣ m then vonMangoldt d else 0) := by
    intro m hm
    simp only [Finset.mem_Ioc] at hm
    have hset : m.divisors = (Finset.Ioc 0 N).filter (· ∣ m) := by
      ext d
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Ioc]
      constructor
      · rintro ⟨hdvd, hm0⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd hm.1, le_trans (Nat.le_of_dvd hm.1 hdvd) hm.2⟩, hdvd⟩
      · rintro ⟨⟨_, _⟩, hdvd⟩
        exact ⟨hdvd, hm.1.ne'⟩
    rw [hset, Finset.sum_filter]
  rw [Finset.sum_congr rfl h2, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [Finset.mem_Ioc] at hd
  rw [← Finset.sum_filter, Finset.sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul, mul_comm]

theorem floor_div_mul (x : ℝ) (hx : 0 ≤ x) (k d : ℕ) :
    ⌊x / (k * d : ℕ)⌋₊ = ⌊x / d⌋₊ / k := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp
  rw [← Nat.floor_div_natCast (x / d) k]
  congr 1
  push_cast
  rw [div_div, mul_comm]

theorem psi_ge_A (kset : Finset ℕ) (a : ℕ → ℤ) (Q : ℕ) (hQ : 0 < Q)
    (hk0 : ∀ k ∈ kset, 0 < k)
    (hg : ∀ M : ℕ, (∑ k ∈ kset, a k * ((M / k : ℕ) : ℤ)) ≤ (Q : ℤ))
    (x : ℝ) (hx : 0 ≤ x) :
    (∑ k ∈ kset, ((a k : ℝ) / Q) * Real.log ((⌊x / k⌋₊)!)) ≤ Chebyshev.psi x := by
  set N := ⌊x⌋₊ with hN
  -- rewrite each term and extend the inner sum range to Ioc 0 N
  have key : ∀ k ∈ kset, ((a k : ℝ) / Q) * Real.log ((⌊x / k⌋₊)!)
      = ∑ d ∈ Finset.Ioc 0 N, ((a k : ℝ) / Q) * (vonMangoldt d * ((⌊x / k⌋₊ / d : ℕ) : ℝ)) := by
    intro k hk
    have hkpos := hk0 k hk
    rw [log_factorial_eq, Finset.mul_sum]
    apply Finset.sum_subset
    · intro d hd
      simp only [Finset.mem_Ioc] at hd ⊢
      refine ⟨hd.1, le_trans hd.2 ?_⟩
      rw [hN]
      exact Nat.floor_le_floor (div_le_self hx (by exact_mod_cast hkpos))
    · intro d hd hd'
      simp only [Finset.mem_Ioc] at hd hd'
      have : ⌊x / k⌋₊ / d = 0 := Nat.div_eq_of_lt (by omega)
      rw [this]; simp
  rw [Finset.sum_congr rfl key, Finset.sum_comm]
  -- now ∑ d ∈ Ioc 0 N, ∑ k ∈ kset, (a k/Q)*(Λ d * (⌊x/k⌋₊/d))
  have hpsi : Chebyshev.psi x = ∑ d ∈ Finset.Ioc 0 N, vonMangoldt d := rfl
  rw [hpsi]
  apply Finset.sum_le_sum
  intro d hd
  simp only [Finset.mem_Ioc] at hd
  -- inner: ∑ k, (a k/Q)*(Λ d * (⌊x/k⌋₊/d)) = Λ d * (1/Q) * g(⌊x/d⌋₊)
  have hfloor : ∀ k ∈ kset, (⌊x / k⌋₊ / d : ℕ) = (⌊x / d⌋₊ / k : ℕ) := by
    intro k hk
    have h1 := floor_div_mul x hx k d
    have h2 := floor_div_mul x hx d k
    rw [Nat.mul_comm] at h2
    omega
  rw [Finset.sum_congr rfl (fun k hk => by rw [hfloor k hk])]
  have hinner : (∑ k ∈ kset, ((a k : ℝ) / Q) * (vonMangoldt d * ((⌊x / d⌋₊ / k : ℕ) : ℝ)))
      = vonMangoldt d / Q * ((∑ k ∈ kset, a k * ((⌊x / d⌋₊ / k : ℕ) : ℤ) : ℤ) : ℝ) := by
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k hk; ring
  rw [hinner]
  have hgle := hg (⌊x / d⌋₊)
  have hLd : (0 : ℝ) ≤ vonMangoldt d := vonMangoldt_nonneg
  calc vonMangoldt d / Q * ((∑ k ∈ kset, a k * ((⌊x / d⌋₊ / k : ℕ) : ℤ) : ℤ) : ℝ)
      ≤ vonMangoldt d / Q * (Q : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact_mod_cast hgle
    _ = vonMangoldt d := by field_simp

open Chebyshev in
/-- Bound on `ψ - θ`: `ψ t - θ t ≤ log 4 · √t + 2·(log t)·t^(1/3)` for `t ≥ 2`. -/
theorem psi_sub_theta_le (t : ℝ) (ht : 2 ≤ t) :
    Chebyshev.psi t - Chebyshev.theta t
      ≤ Real.log 4 * t ^ ((1:ℝ)/2) + 2 * Real.log t * t ^ ((1:ℝ)/3) := by
  have ht1 : (1:ℝ) ≤ t := by linarith
  have ht0 : (0:ℝ) ≤ t := by linarith
  rw [psi_eq_theta_add_sum_theta ht]
  set M := ⌊Real.log t / Real.log 2⌋₊ with hM
  -- ψ - θ = ∑_{n ∈ Icc 2 M} θ (t^(1/n))
  have hrw : θ t + ∑ n ∈ Finset.Icc 2 M, θ (t ^ ((1:ℝ)/n)) - θ t
      = ∑ n ∈ Finset.Icc 2 M, θ (t ^ ((1:ℝ)/n)) := by ring
  rw [hrw]
  -- each term ≤ log4 * t^(1/n)
  have hterm : ∀ n ∈ Finset.Icc 2 M, θ (t ^ ((1:ℝ)/n)) ≤ Real.log 4 * t ^ ((1:ℝ)/n) := by
    intro n hn
    exact theta_le_log4_mul_x (by positivity)
  have hsum1 : ∑ n ∈ Finset.Icc 2 M, θ (t ^ ((1:ℝ)/n))
      ≤ ∑ n ∈ Finset.Icc 2 M, Real.log 4 * t ^ ((1:ℝ)/n) :=
    Finset.sum_le_sum hterm
  refine le_trans hsum1 ?_
  -- split off n = 2
  rcases Nat.lt_or_ge M 2 with hM2 | hM2
  · -- M < 2 : sum is empty or just... Icc 2 M empty
    have : Finset.Icc 2 M = ∅ := by
      rw [Finset.Icc_eq_empty]; omega
    rw [this, Finset.sum_empty]
    have h4 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hlt : (0:ℝ) ≤ Real.log t := Real.log_nonneg ht1
    apply add_nonneg (mul_nonneg h4 (by positivity))
      (mul_nonneg (mul_nonneg (by norm_num) hlt) (by positivity))
  · -- M ≥ 2
    rw [show Finset.Icc 2 M = insert 2 (Finset.Icc 3 M) from ?_]
    · rw [Finset.sum_insert (by simp)]
      have hn2 : Real.log 4 * t ^ ((1:ℝ)/(2:ℕ)) = Real.log 4 * t ^ ((1:ℝ)/2) := by norm_num
      rw [hn2]
      -- remaining sum ≤ (card) • log4 * t^(1/3) ≤ 2 log t * t^(1/3)
      have hrest : ∑ n ∈ Finset.Icc 3 M, Real.log 4 * t ^ ((1:ℝ)/n)
          ≤ 2 * Real.log t * t ^ ((1:ℝ)/3) := by
        have hb : ∀ n ∈ Finset.Icc 3 M, Real.log 4 * t ^ ((1:ℝ)/n)
            ≤ Real.log 4 * t ^ ((1:ℝ)/3) := by
          intro n hn
          simp only [Finset.mem_Icc] at hn
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Real.rpow_le_rpow_of_exponent_le ht1
          apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
          exact_mod_cast hn.1
        refine le_trans (Finset.sum_le_sum hb) ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        -- card (Icc 3 M) ≤ M ≤ log t / log 2
        have hcard : (Finset.Icc 3 M).card ≤ M := by
          rw [Nat.card_Icc]; omega
        have hMle : (M : ℝ) ≤ Real.log t / Real.log 2 := by
          rw [hM]; exact Nat.floor_le (div_nonneg (Real.log_nonneg ht1) (Real.log_nonneg (by norm_num)))
        have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
        have hcard' : ((Finset.Icc 3 M).card : ℝ) ≤ Real.log t / Real.log 2 :=
          le_trans (by exact_mod_cast hcard) hMle
        have hlog4 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; ring
        calc ((Finset.Icc 3 M).card : ℝ) * (Real.log 4 * t ^ ((1:ℝ)/3))
            ≤ (Real.log t / Real.log 2) * (Real.log 4 * t ^ ((1:ℝ)/3)) := by
              apply mul_le_mul_of_nonneg_right hcard' (by positivity)
          _ = 2 * Real.log t * t ^ ((1:ℝ)/3) := by rw [hlog4]; field_simp
      linarith [hrest]
    · ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega

/-- The smooth lower bound function for `θ`. -/
def thetaLB (kset : Finset ℕ) (a : ℕ → ℤ) (Q : ℕ) (x : ℝ) : ℝ :=
  Cval kset a Q * x - Kval kset a Q * Real.log x + Lcval kset a Q
    - (Real.log 4 * x ^ ((1:ℝ)/2) + 2 * Real.log x * x ^ ((1:ℝ)/3))

/-- Main effective Chebyshev lower bound: `θ x ≥ thetaLB x`. -/
theorem theta_lower (kset : Finset ℕ) (a : ℕ → ℤ) (Q : ℕ) (hQ : 0 < Q)
    (hk0 : ∀ k ∈ kset, 0 < k) (hsum0 : ∑ k ∈ kset, (a k : ℝ)/k = 0)
    (hg : ∀ M : ℕ, (∑ k ∈ kset, a k * ((M / k : ℕ) : ℤ)) ≤ (Q : ℤ))
    (x : ℝ) (hx2 : 2 ≤ x) (hxk : ∀ k ∈ kset, (1:ℝ) ≤ x/k) :
    Chebyshev.theta x ≥ thetaLB kset a Q x := by
  have hx0 : 0 < x := by linarith
  have h1 : Cval kset a Q * x - Kval kset a Q * Real.log x + Lcval kset a Q
      ≤ Chebyshev.psi x := by
    have hA := A_lb_bound kset a Q hQ hk0 hsum0 x hx0 hxk
    have hpsi := psi_ge_A kset a Q hQ hk0 hg x (le_of_lt hx0)
    have hr := sum_rterm_eq kset a Q hQ hk0 x hx0
    rw [hr] at hA
    linarith [hA, hpsi]
  have h2 := psi_sub_theta_le x hx2
  rw [thetaLB]
  linarith [h1, h2]

/-- Antiderivative for the integral lower bound. -/
theorem hasDerivAt_Hgen (A B E F t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => A*s - B*Real.log s - E*s^((1:ℝ)/2) - F*s^((1:ℝ)/3))
      (A - B/t - E*((1:ℝ)/2)*t^((1:ℝ)/2-1) - F*((1:ℝ)/3)*t^((1:ℝ)/3-1)) t := by
  have h1 : HasDerivAt (fun s : ℝ => A*s) A t := by
    simpa using (hasDerivAt_id t).const_mul A
  have h2 : HasDerivAt (fun s : ℝ => B*Real.log s) (B/t) t := by
    have := (Real.hasDerivAt_log (ne_of_gt ht)).const_mul B
    simpa [mul_one_div] using this
  have h3 : HasDerivAt (fun s : ℝ => E*s^((1:ℝ)/2)) (E*((1:ℝ)/2)*t^((1:ℝ)/2-1)) t := by
    have := (Real.hasDerivAt_rpow_const (p := (1:ℝ)/2) (Or.inl (ne_of_gt ht))).const_mul E
    simpa [mul_assoc] using this
  have h4 : HasDerivAt (fun s : ℝ => F*s^((1:ℝ)/3)) (F*((1:ℝ)/3)*t^((1:ℝ)/3-1)) t := by
    have := (Real.hasDerivAt_rpow_const (p := (1:ℝ)/3) (Or.inl (ne_of_gt ht))).const_mul F
    simpa [mul_assoc] using this
  exact ((h1.sub h2).sub h3).sub h4

open Chebyshev in
/-- Integral lower bound via FTC and monotonicity. -/
theorem integral_theta_lower (t0 X : ℝ) (ht0 : 2 ≤ t0) (htX : t0 ≤ X)
    (g : ℝ → ℝ) (hg_le_theta : ∀ t ∈ Set.Icc t0 X, g t ≤ Chebyshev.theta t)
    (A B E F : ℝ)
    (hbound : ∀ t ∈ Set.Icc t0 X,
      A - B/t - E*((1:ℝ)/2)*t^((1:ℝ)/2-1) - F*((1:ℝ)/3)*t^((1:ℝ)/3-1)
        ≤ g t / (t * Real.log t ^ 2)) :
    (A*X - B*Real.log X - E*X^((1:ℝ)/2) - F*X^((1:ℝ)/3))
      - (A*t0 - B*Real.log t0 - E*t0^((1:ℝ)/2) - F*t0^((1:ℝ)/3))
      ≤ ∫ t in t0..X, Chebyshev.theta t / (t * Real.log t ^ 2) := by
  set Hf : ℝ → ℝ := fun s => A*s - B*Real.log s - E*s^((1:ℝ)/2) - F*s^((1:ℝ)/3) with hHf
  set Hd : ℝ → ℝ := fun t => A - B/t - E*((1:ℝ)/2)*t^((1:ℝ)/2-1) - F*((1:ℝ)/3)*t^((1:ℝ)/3-1) with hHd
  -- H' is continuous on [t0, X]
  have hcontHd : ContinuousOn Hd (Set.Icc t0 X) := by
    apply ContinuousOn.sub; apply ContinuousOn.sub; apply ContinuousOn.sub
    · exact continuousOn_const
    · exact (continuousOn_const.div continuousOn_id (fun x hx => by
        simp only [Set.mem_Icc] at hx; exact ne_of_gt (by linarith [hx.1])))
    · exact (continuousOn_const.mul ((continuousOn_id.rpow_const (fun x hx => by
        simp only [Set.mem_Icc, id_eq] at hx ⊢; left; exact ne_of_gt (by linarith [hx.1])))))
    · exact (continuousOn_const.mul ((continuousOn_id.rpow_const (fun x hx => by
        simp only [Set.mem_Icc, id_eq] at hx ⊢; left; exact ne_of_gt (by linarith [hx.1])))))
  have hintHd : IntervalIntegrable Hd MeasureTheory.volume t0 X :=
    hcontHd.intervalIntegrable_of_Icc htX
  -- FTC: ∫ Hd = Hf X - Hf t0
  have hFTC : ∫ t in t0..X, Hd t = Hf X - Hf t0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [Set.uIcc_of_le htX] at ht
      simp only [Set.mem_Icc] at ht
      exact hasDerivAt_Hgen A B E F t (by linarith [ht.1])
    · exact hintHd
  -- the integrand θ/(t log²t) is integrable on [t0,X]
  have hintTheta : IntervalIntegrable (fun t => Chebyshev.theta t / (t * Real.log t ^ 2))
      MeasureTheory.volume t0 X := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le htX]
    exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq X).mono_set
      (Set.Icc_subset_Icc ht0 le_rfl)
  -- monotonicity: ∫ Hd ≤ ∫ θ/(t log²t)
  have hmono : ∫ t in t0..X, Hd t ≤ ∫ t in t0..X, Chebyshev.theta t / (t * Real.log t ^ 2) := by
    apply intervalIntegral.integral_mono_on htX hintHd hintTheta
    intro t ht
    have hht := hbound t ht
    have hgt := hg_le_theta t ht
    simp only [Set.mem_Icc] at ht
    have htpos : (0:ℝ) < t := by linarith [ht.1]
    have hlogpos : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    have hden : 0 < t * Real.log t ^ 2 := by positivity
    calc Hd t ≤ g t / (t * Real.log t ^ 2) := hht
      _ ≤ Chebyshev.theta t / (t * Real.log t ^ 2) := by
          gcongr
  rw [hFTC] at hmono
  simpa [hHf] using hmono

end

end ChebLB
