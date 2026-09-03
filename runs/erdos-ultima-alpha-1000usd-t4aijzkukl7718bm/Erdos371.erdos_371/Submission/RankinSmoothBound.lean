import Submission.PrimeHarmonicBounds
import Submission.PrimeWinnerBulkUpper

/-! Elementary Rankin upper bounds for smooth numbers. These are unsigned
sparsity estimates, not shifted smooth-number correlation estimates. -/

namespace Erdos371
open Finset Filter
open scoped Topology

noncomputable def natNegRpowHom (s : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ)^(-s)
  map_one' := by simp
  map_mul' a b := by simp only [Nat.cast_mul]; exact Real.mul_rpow (by positivity) (by positivity)

lemma smooth_rankin_bound (B N : ℕ) (s : ℝ) (hs : 0 < s) :
    (Nat.smoothNumbersUpTo N B).card ≤
      (N : ℝ)^s * ∏ p ∈ B.primesBelow, (1-(p : ℝ)^(-s))⁻¹ := by
  classical
  have hp : ∀ {p : ℕ}, p.Prime → ‖natNegRpowHom s p‖ < 1 := by
    intro p hp
    change ‖(p : ℝ)^(-s)‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  have hE := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric hp B
  let S := Nat.smoothNumbersUpTo N B
  let f : {n // n ∈ S} → B.smoothNumbers := fun n => ⟨n.val, (Nat.mem_smoothNumbersUpTo.mp n.property).2⟩
  have hinj : Function.Injective f := fun n m h =>
    Subtype.ext (congrArg (fun u : B.smoothNumbers => u.val) h)
  have hsum := hE.2.summable.sum_le_tsum (S.attach.image f) (fun n _ => by
    change 0 ≤ (n.val : ℝ)^(-s)
    positivity)
  rw [hE.2.tsum_eq, sum_image (fun _ _ _ _ he => hinj he)] at hsum
  change (∑ n ∈ S.attach, (n.val : ℝ)^(-s)) ≤
    ∏ p ∈ B.primesBelow, (1-(p : ℝ)^(-s))⁻¹ at hsum
  rw [sum_attach S (fun n : ℕ => (n : ℝ)^(-s))] at hsum
  calc
    _ = ∑ _n ∈ S, (1 : ℝ) := by simp [S]
    _ ≤ ∑ n ∈ S, (N : ℝ)^s * (n : ℝ)^(-s) := by
      apply sum_le_sum
      intro n hn
      obtain ⟨hnN, hnB⟩ := Nat.mem_smoothNumbersUpTo.mp hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hnB.1
      have hpow : (n : ℝ)^s ≤ (N : ℝ)^s :=
        Real.rpow_le_rpow hn0.le (by exact_mod_cast hnN) hs.le
      calc
        _ = (n : ℝ)^s * (n : ℝ)^(-s) := by rw [← Real.rpow_add hn0]; simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = (N : ℝ)^s * ∑ n ∈ S, (n : ℝ)^(-s) := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)

lemma prime_neg_rpow_le_three_quarters (p : ℕ) (hp : p.Prime) (s : ℝ) (hs : 1/2 ≤ s) :
    (p : ℝ)^(-s) ≤ 3/4 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  calc
    _ ≤ (2 : ℝ)^(-s) := Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
    _ ≤ (2 : ℝ)^(-(1/2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ ≤ _ := by
      rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
      have hroot : (4/3 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
      exact (inv_le_comm₀ (by positivity) (by norm_num : (0 : ℝ) < 3/4)).mpr (by norm_num; exact hroot)

lemma geometric_inv_le_exp_four (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 3/4) :
    (1-x)⁻¹ ≤ Real.exp (4*x) := by
  have hpos : 0 < 1-x := by linarith
  have he : (1-x)⁻¹ = 1+x/(1-x) := by field_simp; ring
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [he] at hlog
  have hdiv : x/(1-x) ≤ 4*x := (div_le_iff₀ hpos).mpr (by nlinarith)
  have h := Real.exp_le_exp.mpr (show Real.log (1-x)⁻¹ ≤ 4*x by rw [he]; linarith)
  simpa only [Real.exp_log (inv_pos.mpr hpos)] using h

lemma prime_neg_rpow_sum_le (B : ℕ) (hB : 1 ≤ B) (s : ℝ) (hs : s ≤ 1) :
    (∑ p ∈ B.primesBelow, (p : ℝ)^(-s)) ≤ (B : ℝ)^(1-s)*(1+Real.log B) := by
  have hsum : (∑ p ∈ B.primesBelow, (1 : ℝ)/p) ≤ 1+Real.log B := by
    calc
      _ ≤ ∑ n ∈ Icc 1 B, (1 : ℝ)/n := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          obtain ⟨hpB, hp⟩ := Nat.mem_primesBelow.mp hp
          exact mem_Icc.mpr ⟨hp.one_le, hpB.le⟩
        · intros; positivity
      _ = harmonic B := by simp [harmonic_eq_sum_Icc, one_div]
      _ ≤ _ := harmonic_le_one_add_log B
  calc
    _ ≤ ∑ p ∈ B.primesBelow, (B : ℝ)^(1-s) * (1/p) := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpB, hp⟩ := Nat.mem_primesBelow.mp hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have he : (p : ℝ)^(-s) = (p : ℝ)^(1-s) / p := by
        have h := Real.rpow_sub hp0 (1-s) 1
        rw [Real.rpow_one, show 1-s-1 = -s by ring] at h
        exact h
      rw [he, mul_one_div]
      exact div_le_div_of_nonneg_right (Real.rpow_le_rpow hp0.le (by exact_mod_cast hpB.le) (by linarith)) hp0.le
    _ = (B : ℝ)^(1-s) * (∑ p ∈ B.primesBelow, (1 : ℝ)/p) := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)

/-- A finite Rankin bound that needs no prime number theorem. The Euler
product is bounded by a full harmonic sum, so the constants are coarse. -/
theorem smooth_rankin_exp_bound (B N : ℕ) (hB : 1 ≤ B) (s : ℝ)
    (hs : 1/2 ≤ s) (hs' : s ≤ 1) :
    (Nat.smoothNumbersUpTo N B).card ≤
      (N : ℝ)^s * Real.exp (4*(B : ℝ)^(1-s)*(1+Real.log B)) := by
  apply (smooth_rankin_bound B N s (by linarith)).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∏ p ∈ B.primesBelow, Real.exp (4*(p : ℝ)^(-s)) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact inv_nonneg.mpr (by have := prime_neg_rpow_le_three_quarters p (Nat.mem_primesBelow.mp hp).2 s hs; linarith)
      · intro p hp
        exact geometric_inv_le_exp_four _ (by positivity)
          (prime_neg_rpow_le_three_quarters p (Nat.mem_primesBelow.mp hp).2 s hs)
    _ = Real.exp (4 * ∑ p ∈ B.primesBelow, (p : ℝ)^(-s)) := by rw [mul_sum, Real.exp_sum]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [prime_neg_rpow_sum_le B hB s hs'])


lemma smooth_count_rankin_exp_bound (B N : ℕ) (s : ℝ)
    (hs : 1/2 ≤ s) (hs' : s ≤ 1) :
    (((range N).filter (fun n => Nat.maxPrimeFac n ≤ B)).card : ℝ) ≤
      1 + (N : ℝ)^s * Real.exp (4*(B+1 : ℝ)^(1-s)*(1+Real.log (B+1 : ℝ))) := by
  have hsub : (range N).filter (fun n => Nat.maxPrimeFac n ≤ B) ⊆
      insert 0 (Nat.smoothNumbersUpTo N (B+1)) := by
    intro n hn
    obtain ⟨hnN, hnB⟩ := mem_filter.mp hn
    by_cases hn0 : n = 0
    · simp [hn0]
    · apply mem_insert_of_mem
      apply Nat.mem_smoothNumbersUpTo.mpr
      refine ⟨(mem_range.mp hnN).le, Nat.mem_smoothNumbers'.mpr ?_⟩
      intro p hp hpn
      exact Nat.lt_succ_of_le ((Nat.le_maxPrimeFac hn0 hp hpn).trans hnB)
  have hc := (card_le_card hsub).trans (card_insert_le _ _)
  have hc' : (((range N).filter (fun n => Nat.maxPrimeFac n ≤ B)).card : ℝ) ≤
      (Nat.smoothNumbersUpTo N (B+1)).card + 1 := by exact_mod_cast hc
  have hr := smooth_rankin_exp_bound (B+1) N (by omega) s hs hs'
  push_cast at hr
  linarith

lemma rankin_exponent_polylog_upper (x : ℝ) (hx : 1 ≤ x) (B k : ℕ)
    (hB : 1 ≤ B) (hBx : (B : ℝ) ≤ 2*x^k) (s : ℝ)
    (hs : 0 ≤ 1-s) (hs' : 1-s ≤ 1) (hks : (k : ℝ)*(1-s) ≤ 1/2) :
    4*(B : ℝ)^(1-s)*(1+Real.log B) ≤
      8*Real.sqrt x*(1+Real.log 2+(k : ℝ)*Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hpow : (B : ℝ)^(1-s) ≤ 2*Real.sqrt x := by
    calc
      _ ≤ (2*x^k)^(1-s) := Real.rpow_le_rpow hB0.le hBx hs
      _ = (2 : ℝ)^(1-s) * x^((k : ℝ)*(1-s)) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      _ ≤ 2 * x^(1/2 : ℝ) := by
        apply mul_le_mul
        · simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hs'
        · exact Real.rpow_le_rpow_of_exponent_le hx hks
        · positivity
        · norm_num
      _ = _ := by rw [← Real.sqrt_eq_rpow]
  have hlog : Real.log B ≤ Real.log 2 + (k : ℝ)*Real.log x := by
    calc
      _ ≤ Real.log (2*x^k) := Real.log_le_log hB0 hBx
      _ = _ := by rw [Real.log_mul (by norm_num) (pow_pos hx0 k).ne', Real.log_pow]
  have hlog0 : 0 ≤ 1+Real.log B := by have := Real.log_natCast_nonneg B; linarith
  have hlog1 : 1+Real.log B ≤ 1+Real.log 2+(k : ℝ)*Real.log x := by linarith
  have hh := mul_le_mul hpow hlog1 hlog0 (by positivity : (0 : ℝ) ≤ 2*Real.sqrt x)
  nlinarith

lemma rankin_polylog_exponent_tendsto (k : ℕ) :
    Tendsto (fun N : ℕ =>
      8*Real.sqrt (Real.log N)*(1+Real.log 2+(k : ℝ)*Real.log (Real.log N))/Real.log N)
      atTop (nhds 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h1 := tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hlog)
      (a := (1+Real.log 2 : ℝ))
  have h2 : Tendsto (fun N : ℕ => Real.log (Real.log N)/Real.sqrt (Real.log N))
      atTop (nhds 0) := by
    simpa only [← Real.sqrt_eq_rpow, Function.comp_apply] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).tendsto_div_nhds_zero.comp hlog
  have ht := (h1.add (h2.const_mul (k : ℝ))).const_mul 8
  simp only [mul_zero, add_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
  have hln : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hsqrt : Real.sqrt (Real.log (N : ℝ)) ≠ 0 := (Real.sqrt_pos.mpr hln).ne'
  have he := Real.sq_sqrt hln.le
  dsimp
  field_simp
  rw [he]
  ring

noncomputable def polylogSmoothCutoff (k N : ℕ) : ℕ := ⌊(Real.log N)^k⌋₊

/-- A fixed power of log N is a sufficiently small smoothness cutoff that
the smooth integers satisfy a power saving in N. The saving may depend on k. -/
theorem smooth_polylog_power_bound (k : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ᶠ N : ℕ in atTop,
      (((range N).filter (fun n => Nat.maxPrimeFac n ≤ polylogSmoothCutoff k N)).card : ℝ) ≤
        1 + (N : ℝ)^(1-δ) := by
  let δ : ℝ := 1/(8*((k : ℝ)+1))
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hd : 0 < δ := by dsimp [δ]; positivity
  have hdle : δ ≤ 1/8 := by
    dsimp [δ]
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  refine ⟨δ, hd, by linarith, ?_⟩
  have hsmall := (rankin_polylog_exponent_tendsto k).eventually_le_const hd
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hsmall, hlog.eventually_ge_atTop 1, eventually_gt_atTop (1 : ℕ)] with N hsmall hln hN
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hln0 : 0 < Real.log (N : ℝ) := by linarith
  let B := polylogSmoothCutoff k N
  have hBx : (B+1 : ℝ) ≤ 2*(Real.log N)^k := by
    have hfloor : (B : ℝ) ≤ (Real.log N)^k := Nat.floor_le (by positivity)
    have hone : (1 : ℝ) ≤ (Real.log N)^k := one_le_pow₀ hln
    linarith
  have hks : (k : ℝ)*(1-(1-2*δ)) ≤ 1/2 := by
    dsimp [δ]
    field_simp
    nlinarith
  have he := rankin_exponent_polylog_upper (Real.log N) hln (B+1) k (by omega)
    (by simpa only [Nat.cast_add, Nat.cast_one] using hBx) (1-2*δ)
    (by linarith) (by linarith) hks
  push_cast at he
  have hexp : 4*(B+1 : ℝ)^(1-(1-2*δ))*(1+Real.log (B+1 : ℝ)) ≤ δ*Real.log N := by
    have hmul := (div_le_iff₀ hln0).mp hsmall
    exact he.trans hmul
  have hr := smooth_count_rankin_exp_bound B N (1-2*δ) (by linarith) (by linarith)
  calc
    _ ≤ 1 + (N : ℝ)^(1-2*δ) * Real.exp (4*(B+1 : ℝ)^(1-(1-2*δ))*(1+Real.log (B+1 : ℝ))) := hr
    _ ≤ 1 + (N : ℝ)^(1-2*δ) * Real.exp (δ*Real.log N) := by gcongr
    _ = 1 + (N : ℝ)^(1-δ) := by
      rw [mul_comm δ, ← Real.rpow_def_of_pos hn0, ← Real.rpow_add hn0]
      congr 2
      ring

#print axioms smooth_rankin_bound
#print axioms smooth_rankin_exp_bound
#print axioms smooth_polylog_power_bound
end Erdos371
