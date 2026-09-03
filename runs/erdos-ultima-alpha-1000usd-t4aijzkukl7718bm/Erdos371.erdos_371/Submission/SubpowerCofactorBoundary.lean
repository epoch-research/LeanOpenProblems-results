import Submission.PrimeLogBoundaryRarity
import Submission.PositivePrimeFractionSmoothRuns

/-! Subpower-cofactor centers, and their incident adjacent comparisons, have
natural density zero. In particular the prime smooth-neighbor runs proved
recently do not by themselves control a positive-density part of Erdos 371. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

lemma prime_log_level_exception_hasDensity_zero (E : ℕ → Prop) (a : ℝ) (ha : 0 < a)
    (hE : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      E n → 1 < n ∧ |normalizedPrimeLog n n-a| ≤ δ) :
    {n | E n}.HasDensity 0 := by
  classical
  rw [density_iff_count]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,hrare⟩ := prime_log_level_nonatomic a ha (ε/2) (by positivity)
  obtain ⟨K,hK⟩ := eventually_atTop.mp (hE δ hδ)
  have hsmall := tendsto_const_div_atTop_nhds_zero_nat (K : ℝ)
  filter_upwards [hrare,hsmall.eventually_lt_const (by positivity : (0 : ℝ) < ε/2)]
    with N hN hsmall
  have hsub : (range N).filter E ⊆ range K ∪
      (range N).filter (fun n => 1 < n ∧ |normalizedPrimeLog n n-a| ≤ δ) := by
    intro n hn
    obtain ⟨hnN,hEn⟩ := mem_filter.mp hn
    by_cases hnK : n < K
    · exact mem_union_left _ (mem_range.mpr hnK)
    · exact mem_union_right _ (mem_filter.mpr ⟨hnN,hK n (by omega) hEn⟩)
  have hc := (Nat.cast_le (α := ℝ)).mpr ((card_le_card hsub).trans (card_union_le _ _))
  simp only [card_range,Nat.cast_add] at hc
  have hd := div_le_div_of_nonneg_right hc (Nat.cast_nonneg (α := ℝ) N)
  rw [add_div] at hd
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (by positivity)]
  linarith

lemma normalizedPrimeLog_near_one_of_small_cofactor (n : ℕ) (hn : 1 < n)
    (δ : ℝ) (hcof : (primeCofactor n : ℝ) ≤ (n : ℝ)^δ) :
    |normalizedPrimeLog n n-1| ≤ δ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hL0 : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hp := Nat.prime_maxPrimeFac_of_one_lt n hn
  have hp0 : (0 : ℝ) < Nat.maxPrimeFac n := by exact_mod_cast hp.pos
  obtain ⟨hcf,_,_⟩ := primeCofactor_data n hn
  have hcf0 : (0 : ℝ) < primeCofactor n := by exact_mod_cast hcf
  have hlogcf : Real.log (primeCofactor n) ≤ δ*Real.log n := by
    have h := Real.log_le_log hcf0 hcof
    rwa [Real.log_rpow hn0] at h
  have he : primeLog n+Real.log (primeCofactor n) = Real.log n := by
    rw [primeLog,← Real.log_mul hp0.ne' hcf0.ne']
    congr 1
    exact_mod_cast maxPrimeFac_mul_primeCofactor n
  have hu := (normalizedPrimeLog_mem_unit n n hn le_rfl).2
  have hlo : 1-δ ≤ normalizedPrimeLog n n := by
    unfold normalizedPrimeLog
    apply (le_div_iff₀ hL0).mpr
    nlinarith
  rw [abs_of_nonpos (sub_nonpos.mpr hu)]
  linarith

/-- Every pointwise subpower bound on the cofactor defines a density-zero
set of centers. No smoothness restriction on the bounding function is needed. -/
theorem subpower_cofactor_centers_hasDensity_zero (K : ℕ → ℝ)
    (hK : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, K n ≤ (n : ℝ)^δ) :
    {n : ℕ | 1 < n ∧ (primeCofactor n : ℝ) ≤ K n}.HasDensity 0 := by
  apply prime_log_level_exception_hasDensity_zero _ 1 (by norm_num)
  intro δ hδ
  filter_upwards [hK δ hδ] with n hn
  intro he
  exact ⟨he.1,normalizedPrimeLog_near_one_of_small_cofactor n he.1 δ (he.2.trans hn)⟩

theorem polylog_cofactor_centers_hasDensity_zero (c a : ℝ) :
    {n : ℕ | 1 < n ∧ (primeCofactor n : ℝ) ≤ c*(Real.log n)^a}.HasDensity 0 := by
  apply subpower_cofactor_centers_hasDensity_zero
  intro δ hδ
  have ht := (log_nat_rpow_div_rpow_tendsto_zero a δ hδ).const_mul c
  simp only [mul_zero] at ht
  filter_upwards [ht.eventually_le_const (by norm_num : (0 : ℝ) < 1),
    eventually_gt_atTop (0 : ℕ)] with n hn hn0
  have hnpow : 0 < (n : ℝ)^δ := Real.rpow_pos_of_pos (by exact_mod_cast hn0) δ
  have hh : (c*(Real.log n)^a)/(n : ℝ)^δ ≤ 1 := by
    simpa only [mul_div_assoc] using hn
  simpa only [one_mul] using (div_le_iff₀ hnpow).mp hh

def shortPrimeMultiples (c a : ℝ) : Set ℕ :=
  {n | ∃ p k : ℕ, p.Prime ∧ 0 < k ∧ (k : ℝ) ≤ c*(Real.log p)^a ∧ n = k*p}

lemma shortPrimeMultiples_subset_cofactor_centers (c a : ℝ) (hc : 0 ≤ c) (ha : 0 ≤ a) :
    shortPrimeMultiples c a ⊆ {n : ℕ | 1 < n ∧ (primeCofactor n : ℝ) ≤ c*(Real.log n)^a} := by
  intro n hn
  obtain ⟨p,k,hp,hk,hkbound,rfl⟩ := hn
  have hpn : p ≤ k*p := by nlinarith [hp.pos]
  have hn2 : 1 < k*p := hp.one_lt.trans_le hpn
  have hmax : p ≤ Nat.maxPrimeFac (k*p) := by
    rw [Nat.maxPrimeFac_mul hk.ne' hp.ne_zero,hp.maxPrimeFac_eq_self]
    exact le_max_right _ _
  have hcof : primeCofactor (k*p) ≤ k := by
    unfold primeCofactor
    have h := Nat.div_le_div_left hmax hp.pos (a := k*p)
    simpa only [Nat.mul_div_left k hp.pos] using h
  have hlog := Real.log_le_log (by exact_mod_cast hp.pos : (0 : ℝ) < p)
    (by exact_mod_cast hpn : (p : ℝ) ≤ k*p)
  have hpow := Real.rpow_le_rpow (Real.log_natCast_nonneg p) hlog ha
  have hmul := mul_le_mul_of_nonneg_left hpow hc
  refine ⟨hn2,?_⟩
  have hcof' : (primeCofactor (k*p) : ℝ) ≤ k := by exact_mod_cast hcof
  exact hcof'.trans (hkbound.trans (by simpa only [Nat.cast_mul] using hmul))

/-- All the recent prime-multiple run centers lie in this zero-density
family, for suitable c and a. The good-prime restriction is not needed. -/
theorem shortPrimeMultiples_hasDensity_zero (c a : ℝ) (hc : 0 ≤ c) (ha : 0 ≤ a) :
    (shortPrimeMultiples c a).HasDensity 0 := by
  exact density_zero_of_eventually_imp _ _
    (Eventually.of_forall (shortPrimeMultiples_subset_cofactor_centers c a hc ha))
    (polylog_cofactor_centers_hasDensity_zero c a)

lemma density_zero_shift_one (E : ℕ → Prop) (hE : {n | E n}.HasDensity 0) :
    {n | E (n+1)}.HasDensity 0 := by
  classical
  rw [density_iff_count] at hE ⊢
  have ht := hE.add tendsto_one_div_atTop_nhds_zero_nat
  simp only [add_zero] at ht
  apply squeeze_zero (fun _ => by positivity) _ ht
  intro N
  have hcard : ((range N).filter (fun n => E (n+1))).card ≤ ((range N).filter E).card+1 := by
    have hshift : ((range N).filter (fun n => E (n+1))).card ≤
        ((range (N+1)).filter E).card := by
      apply card_le_card_of_injOn (fun n => n+1)
      · intro n hn
        simp only [mem_coe] at hn ⊢
        obtain ⟨hnN,hnE⟩ := mem_filter.mp hn
        exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hnN; omega),hnE⟩
      · intro n _ m _ h
        exact Nat.add_right_cancel h
    apply hshift.trans
    rw [range_add_one,filter_insert]
    split_ifs
    · exact card_insert_le _ _
    · omega
  have h := div_le_div_of_nonneg_right ((Nat.cast_le (α := ℝ)).mpr hcard) (Nat.cast_nonneg N)
  simpa only [Nat.cast_add,Nat.cast_one,add_div] using h

lemma density_zero_incident_edges (E : ℕ → Prop) (hE : {n | E n}.HasDensity 0) :
    {n | E n ∨ E (n+1)}.HasDensity 0 := by
  classical
  have hshift := density_zero_shift_one E hE
  rw [density_iff_count] at hE hshift ⊢
  have ht := hE.add hshift
  simp only [add_zero] at ht
  apply squeeze_zero (fun _ => by positivity) _ ht
  intro N
  have he : (range N).filter (fun n => E n ∨ E (n+1)) =
      (range N).filter E ∪ (range N).filter (fun n => E (n+1)) := by
    ext n
    simp only [mem_filter,mem_union]
    tauto
  rw [he]
  have h := div_le_div_of_nonneg_right
    ((Nat.cast_le (α := ℝ)).mpr (card_union_le ((range N).filter E)
      ((range N).filter (fun n => E (n+1))))) (Nat.cast_nonneg N)
  simpa only [Nat.cast_add,add_div] using h

/-- Even all adjacent edges incident to such run centers form a natural
zero-density set. This quantifies why the run theorems do not settle 371. -/
theorem shortPrimeMultiple_edges_hasDensity_zero (c a : ℝ) (hc : 0 ≤ c) (ha : 0 ≤ a) :
    {n | n ∈ shortPrimeMultiples c a ∨ n+1 ∈ shortPrimeMultiples c a}.HasDensity 0 :=
  density_zero_incident_edges _ (shortPrimeMultiples_hasDensity_zero c a hc ha)

def primeRunCenters (K : ℕ → ℕ) : Set ℕ :=
  {n | ∃ p k : ℕ, p.Prime ∧ 0 < k ∧ k ≤ K p ∧ n = k*p}

lemma primeRunCenters_hasDensity_zero_of_polylog_bound (K : ℕ → ℕ)
    (c a : ℝ) (hc : 0 ≤ c) (ha : 0 ≤ a)
    (hK : ∀ᶠ p : ℕ in atTop, (K p : ℝ) ≤ c*(Real.log p)^a) :
    (primeRunCenters K).HasDensity 0 := by
  obtain ⟨B,hB⟩ := eventually_atTop.mp hK
  let M := (range B).sup (fun p => K p*p)
  apply density_zero_of_eventually_imp _ _ ?_ (shortPrimeMultiples_hasDensity_zero c a hc ha)
  filter_upwards [eventually_gt_atTop M] with n hn
  intro hcenter
  obtain ⟨p,k,hp,hk,hkK,hkn⟩ := hcenter
  have hpB : B ≤ p := by
    by_contra h
    have hpBr : p ∈ range B := mem_range.mpr (by omega)
    have hbound : K p*p ≤ M := by
      exact Finset.le_sup (f := fun q => K q*q) hpBr
    have hh := Nat.mul_le_mul_right p hkK
    omega
  refine ⟨p,k,hp,hk,?_,hkn⟩
  exact (by exact_mod_cast hkK : (k : ℝ) ≤ K p).trans (hB p hpB)

/-- The precise centers used in the constant-times-log/log-log theorem
are sparse, even without imposing the smooth-neighbor property. -/
theorem scaledPrimeRun_centers_hasDensity_zero (c : ℝ) (hc : 0 ≤ c) :
    (primeRunCenters (scaledPrimeRunCutoff c)).HasDensity 0 := by
  apply primeRunCenters_hasDensity_zero_of_polylog_bound _ c 1 hc (by norm_num)
  filter_upwards [criticalPrimeRun_data 1 (by norm_num)] with p hd
  have hW : 0 ≤ criticalPrimeRunWeight 1 p := by linarith [hd.2.1]
  have hf : (scaledPrimeRunCutoff c p : ℝ) ≤ c*criticalPrimeRunWeight 1 p :=
    Nat.floor_le (mul_nonneg hc hW)
  simpa only [Real.rpow_one] using hf.trans (mul_le_mul_of_nonneg_left hd.2.2.1 hc)

/-- This includes both incident edges of every prime-multiple run from
the latest positive-prime-fraction theorem. Their natural density is zero. -/
theorem scaledPrimeRun_edges_hasDensity_zero (c : ℝ) (hc : 0 ≤ c) :
    {n | n ∈ primeRunCenters (scaledPrimeRunCutoff c) ∨
      n+1 ∈ primeRunCenters (scaledPrimeRunCutoff c)}.HasDensity 0 :=
  density_zero_incident_edges _ (scaledPrimeRun_centers_hasDensity_zero c hc)

#print axioms subpower_cofactor_centers_hasDensity_zero
#print axioms polylog_cofactor_centers_hasDensity_zero
#print axioms shortPrimeMultiples_hasDensity_zero
#print axioms shortPrimeMultiple_edges_hasDensity_zero
#print axioms scaledPrimeRun_edges_hasDensity_zero
end Erdos371
