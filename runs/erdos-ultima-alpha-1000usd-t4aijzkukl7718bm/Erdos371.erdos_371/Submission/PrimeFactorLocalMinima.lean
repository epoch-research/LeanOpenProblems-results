import Submission.LogarithmicSignedReduction
import Submission.PrimeWinnerPrimeWeightedEnergy

/-! Logarithmic near-tie rarity forces a positive lower proportion of strict
local minima. This does not prove balance of the adjacent comparisons. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

def riseRunStartCount (q : ℕ → Prop) [DecidablePred q] (N : ℕ) : ℕ :=
  ((range N).filter fun n => 0<n ∧ ¬q (n-1) ∧ q n).card

lemma riseRunStartCount_succ (q : ℕ → Prop) [DecidablePred q] (N : ℕ) :
    riseRunStartCount q (N+1) = riseRunStartCount q N+
      if 0<N ∧ ¬q (N-1) ∧ q N then 1 else 0 := by
  simp only [riseRunStartCount,range_add_one,filter_insert]
  split_ifs
  · rw [card_insert_of_notMem (fun h => (mem_range.mp (mem_filter.mp h).1).false)]
  · simp

lemma variation_run_potential (a : ℕ → ℝ) (q : ℕ → Prop) [DecidablePred q] (N : ℕ)
    (ha : ∀ n≤N+1, 0≤a n ∧ a n≤1)
    (hs : ∀ n≤N, |a (n+1)-a n| = if q n then a (n+1)-a n else a n-a (n+1)) :
    (∑ n ∈ range (N+1), |a (n+1)-a n|) ≤
      2*(riseRunStartCount q (N+1) : ℝ)+(if q N then a (N+1) else 2-a (N+1)) := by
  induction N with
  | zero =>
    have h0 := ha 0 (by omega)
    simp only [sum_range_one,zero_add] at *
    rw [hs 0 le_rfl]
    have hz : riseRunStartCount q 1=0 := by simp [riseRunStartCount]
    rw [hz,Nat.cast_zero,mul_zero,zero_add]
    split_ifs <;> linarith
  | succ N ih =>
    have hi := ih (fun n hn => ha n (by omega)) (fun n hn => hs n (by omega))
    have h0 := ha (N+1) (by omega)
    rw [sum_range_succ,hs (N+1) le_rfl,riseRunStartCount_succ]
    simp only [Nat.add_sub_cancel,Nat.zero_lt_succ,true_and,Nat.cast_add]
    by_cases hq : q N <;> by_cases hq' : q (N+1) <;>
      simp only [hq,hq',not_true_eq_false,not_false_eq_true,false_and,true_and,
        if_true,if_false,Nat.cast_one,Nat.cast_zero] at hi ⊢ <;> linarith

/-- Each increasing run contributes at most one unit of increase, and each
fall-to-rise transition starts a new run. -/
lemma variation_le_twice_run_starts_add_two (a : ℕ → ℝ) (q : ℕ → Prop) [DecidablePred q]
    (N : ℕ) (ha : ∀ n≤N, 0≤a n ∧ a n≤1)
    (hs : ∀ n<N, |a (n+1)-a n| = if q n then a (n+1)-a n else a n-a (n+1)) :
    (∑ n ∈ range N, |a (n+1)-a n|) ≤ 2*(riseRunStartCount q N : ℝ)+2 := by
  cases N with
  | zero => simp [riseRunStartCount]
  | succ N =>
    have h := variation_run_potential a q N ha (fun n hn => hs n (by omega))
    have hlast := ha (N+1) le_rfl
    split_ifs at h <;> linarith

def primeLocalMinima (N : ℕ) : Finset ℕ :=
  (range N).filter fun n => 0<n ∧ Nat.maxPrimeFac n < Nat.maxPrimeFac (n-1) ∧
    Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)

lemma primeLocalMinima_card_eq_run_starts (N : ℕ) :
    (primeLocalMinima N).card = riseRunStartCount
      (fun n => Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)) N := by
  congr 1
  ext n
  simp only [primeLocalMinima,mem_filter]
  constructor
  · rintro ⟨hn,hpos,hprev,hnext⟩
    refine ⟨hn,hpos,?_,hnext⟩
    simpa only [Nat.sub_add_cancel hpos] using hprev.not_gt
  · rintro ⟨hn,hpos,hprev,hnext⟩
    have he := consecutive_maxPrimeFac_ne (n-1)
    rw [Nat.sub_add_cancel hpos] at he hprev
    exact ⟨hn,hpos,lt_of_le_of_ne (not_lt.mp hprev) he,hnext⟩

lemma logDifference_abs_eq_oriented (N n : ℕ) (hN : 1<N) :
    |normalizedPrimeLog N (n+1)-normalizedPrimeLog N n| =
      if Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1) then
        normalizedPrimeLog N (n+1)-normalizedPrimeLog N n
      else normalizedPrimeLog N n-normalizedPrimeLog N (n+1) := by
  by_cases hn : n=0
  · subst n
    simp [normalizedPrimeLog,primeLog]
  · rw [← logDifference_eq_sub]
    by_cases h : Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)
    · rw [if_pos h,abs_of_nonneg ((logDifference_pos_iff N n hN (by omega)).mpr h).le]
    · rw [if_neg h,abs_of_nonpos (not_lt.mp (fun hh => h
        ((logDifference_pos_iff N n hN (by omega)).mp hh))),logDifference_eq_sub]
      ring

lemma normalizedPrimeLog_variation_bound (N : ℕ) (hN : 1<N) :
    (∑ n ∈ range N, |logDifference N n|) ≤ 2*((primeLocalMinima N).card : ℝ)+2 := by
  rw [primeLocalMinima_card_eq_run_starts]
  simpa only [logDifference_eq_sub] using variation_le_twice_run_starts_add_two
    (normalizedPrimeLog N) (fun n => Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)) N
    (fun n hn => normalizedPrimeLog_mem_unit N n hN hn)
    (fun n _ => logDifference_abs_eq_oriented N n hN)

lemma logDifference_variation_lower (δ : ℝ) (hδ : 0<δ) (N : ℕ) (hN : 1<N) :
    δ*((N : ℝ)-(logRatioSet N δ).card-1) ≤ ∑ n ∈ range N, |logDifference N n| := by
  let G := (range N).filter fun n => 0<n ∧ ¬logRatioEvent N δ n
  have hcover : range N ⊆ G ∪ logRatioSet N δ ∪ {0} := by
    intro n hn
    by_cases hn0 : n=0
    · exact mem_union_right _ (by simp [hn0])
    · apply mem_union_left
      by_cases h : logRatioEvent N δ n
      · exact mem_union_right _ (mem_filter.mpr ⟨hn,h⟩)
      · exact mem_union_left _ (mem_filter.mpr ⟨hn,by omega,h⟩)
  have hc := (card_le_card hcover).trans (card_union_le _ _)
  have hc' := card_union_le G (logRatioSet N δ)
  simp only [card_range,card_singleton] at hc
  have hnum : (N : ℝ)-(logRatioSet N δ).card-1 ≤ G.card := by
    have hh : N≤G.card+(logRatioSet N δ).card+1 := by omega
    exact_mod_cast (show (N : ℤ)-(logRatioSet N δ).card-1≤G.card by omega)
  calc
    _ ≤ δ*(G.card : ℝ) := mul_le_mul_of_nonneg_left hnum hδ.le
    _ = ∑ _n ∈ G, δ := by simp [mul_comm]
    _ ≤ ∑ n ∈ G, |logDifference N n| := by
      apply sum_le_sum
      intro n hn
      obtain ⟨_,hnpos,hnot⟩ := mem_filter.mp hn
      exact (lt_of_not_ge (fun h => hnot ((logRatioEvent_iff_logDifference N n δ hN hnpos).mpr h))).le
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)

/-- The ACTUAL largest-prime-factor sequence has a positive lower natural
proportion of strict local minima. No density value is asserted. -/
theorem primeLocalMinima_positive_lower_proportion :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop, c≤((primeLocalMinima N).card : ℝ)/N := by
  obtain ⟨δ,hδ,hnear⟩ := logRatioSet_uniform_rarity (1/4) (by norm_num)
  have hone := tendsto_one_div_atTop_nhds_zero_nat.eventually_lt_const
    (show 0<δ/(8*(δ+2)) by positivity)
  refine ⟨δ/8,by positivity,?_⟩
  filter_upwards [hnear,hone,eventually_gt_atTop (1 : ℕ)] with N hn ho hN
  have hN0 : (0 : ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hlow := logDifference_variation_lower δ hδ N hN
  have hupp := normalizedPrimeLog_variation_bound N hN
  have hnear' := (div_le_iff₀ hN0).mp hn
  apply (le_div_iff₀ hN0).mpr
  have hone' : (δ+2)<δ*N/8 := by
    have hh := (div_lt_div_iff₀ hN0 (show 0<8*(δ+2) by positivity)).mp ho
    nlinarith
  nlinarith

noncomputable def primeLocalMinimaAbove (B N : ℕ) : Finset ℕ :=
  (primeLocalMinima N).filter fun n => B < Nat.maxPrimeFac n

lemma smooth_ceil_power_count_eventually_le (u : ℝ) (hu : 0≤u) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,
      (((range N).filter fun n => Nat.maxPrimeFac n≤ceilPowerCutoff u N).card : ℝ)/N ≤ 8*u+ε := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he := nat_sqrt_add_one_div_tendsto_zero.add
    ((tendsto_const_nhds (x := (8*Real.log 3 : ℝ))).div_atTop hlog)
  simp only [add_zero] at he
  filter_upwards [he.eventually_lt_const hε,eventually_gt_atTop (1 : ℕ)] with N heN hN
  have hlogN : 0<Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hs := smooth_count_ratio_log_bound (ceilPowerCutoff u N) N hN
  have hl := div_le_div_of_nonneg_right (ceilPowerCutoff_succ_log_bound u hu N (by omega)) hlogN.le
  have hid : (Real.log 3+u*Real.log N)/Real.log N=Real.log 3/Real.log N+u := by field_simp
  rw [hid] at hl
  simp only [mul_div_assoc] at heN
  linarith

/-- Positive local-minimum mass persists with a fixed positive-power lower
bound on the center's prime label. -/
theorem primeLocalMinimaAbove_power_positive_mass :
    ∃ u c : ℝ, 0<u ∧ 0<c ∧ ∀ᶠ N : ℕ in atTop,
      c≤((primeLocalMinimaAbove (ceilPowerCutoff u N) N).card : ℝ)/N := by
  obtain ⟨c,hc,hm⟩ := primeLocalMinima_positive_lower_proportion
  let u : ℝ := c/64
  have hu : 0<u := by dsimp [u]; positivity
  refine ⟨u,c/2,hu,by positivity,?_⟩
  filter_upwards [hm,smooth_ceil_power_count_eventually_le u hu.le (c/8) (by positivity),
    eventually_gt_atTop (0 : ℕ)] with N hmN hsN hN
  have he := card_filter_add_card_filter_not (s := primeLocalMinima N)
    (fun n => ceilPowerCutoff u N<Nat.maxPrimeFac n)
  have hsub : (primeLocalMinima N).filter (fun n => ¬ceilPowerCutoff u N<Nat.maxPrimeFac n) ⊆
      (range N).filter (fun n => Nat.maxPrimeFac n≤ceilPowerCutoff u N) := by
    intro n hn
    obtain ⟨hn,hp⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨(mem_filter.mp hn).1,not_lt.mp hp⟩
  have hcard : ((primeLocalMinima N).card : ℝ) ≤
      (primeLocalMinimaAbove (ceilPowerCutoff u N) N).card+
        ((range N).filter fun n => Nat.maxPrimeFac n≤ceilPowerCutoff u N).card := by
    exact_mod_cast (show (primeLocalMinima N).card≤
      (primeLocalMinimaAbove (ceilPowerCutoff u N) N).card+
      ((range N).filter fun n => Nat.maxPrimeFac n≤ceilPowerCutoff u N).card from by
        have hh := card_le_card hsub
        change _+_=_ at he
        dsimp only [primeLocalMinimaAbove]
        omega)
  have hdiv := div_le_div_of_nonneg_right hcard (Nat.cast_nonneg (α := ℝ) N)
  rw [add_div] at hdiv
  dsimp [u] at hsN
  linarith

#print axioms normalizedPrimeLog_variation_bound
#print axioms primeLocalMinima_positive_lower_proportion
#print axioms primeLocalMinimaAbove_power_positive_mass
end Erdos371
