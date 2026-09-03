import Submission.NearTieSieveCutoff

/-! Negligibility of fixed-ratio near ties in the small-cofactor regime. -/

namespace Erdos371
namespace FiniteSieve
open Finset Filter

lemma log_nat_mono_of_right_pos (X N : ℕ) (hXN : X ≤ N) (_hN : 0 < N) :
    Real.log X ≤ Real.log N := by
  by_cases hX : X = 0
  · simpa [hX] using Real.log_natCast_nonneg N
  · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hX) (by exact_mod_cast hXN)

lemma boundedCofactorNearTieSet_ratio_bound (N C X z : ℕ)
    (hN : 0 < N) (hz : 1 ≤ z) (hXN : X^2 ≤ N) :
    ((boundedCofactorNearTieSet N C X z).card : ℝ)/N ≤
      (4*Real.exp 2*(C : ℝ)^2*Real.exp 16) * ((1+Real.log N)/(Real.log (z+1 : ℝ))^2) +
      (X : ℝ)^2*brunRoundingError z/N := by
  have hXle : X ≤ N := (show X ≤ X^2 by nlinarith).trans hXN
  have hlog := log_nat_mono_of_right_pos X N hXle hN
  have h := div_le_div_of_nonneg_right (boundedCofactorNearTieSet_bound N C X z hz hXN)
    (Nat.cast_nonneg N)
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have he : ((4*Real.exp 2*N/(Real.log (z+1 : ℝ))^2) *
      ((C : ℝ)^2 * Real.exp 16 * (1+Real.log X)) +
      (X : ℝ)^2 * ((2*brunDegree z+1 : ℕ) * (z : ℝ)^(4*brunDegree z))) / N =
      (4*Real.exp 2*(C : ℝ)^2*Real.exp 16) * ((1+Real.log X)/(Real.log (z+1 : ℝ))^2) +
      (X : ℝ)^2*brunRoundingError z/N := by
    unfold brunRoundingError
    field_simp
  rw [he] at h
  refine h.trans (add_le_add ?_ le_rfl)
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)) (by positivity)

/-- Uniform negligibility when the square of the cofactor cutoff has a
fixed power saving below the averaging endpoint. -/
theorem boundedCofactorNearTieSet_tendsto_zero (C : ℕ) (X : ℕ → ℕ)
    (δ : ℝ) (hδ : 0 < δ)
    (hX : ∀ᶠ N : ℕ in atTop, (X N : ℝ)^2 ≤ (N : ℝ)^(1-δ)) :
    Tendsto (fun N : ℕ =>
      ((boundedCofactorNearTieSet N C (X N) (nearTieSieveCutoff N)).card : ℝ)/N)
      atTop (nhds 0) := by
  have hmain := nearTieSieveCutoff_main_ratio_tendsto_zero.const_mul
    (4*Real.exp 2*(C : ℝ)^2*Real.exp 16)
  have herr := (tendsto_rpow_neg_atTop (show 0 < δ/2 by linarith)).comp tendsto_natCast_atTop_atTop
  have ht := hmain.add herr
  simp only [mul_zero, add_zero, Function.comp_def] at ht
  apply squeeze_zero' (Eventually.of_forall fun N => by positivity) _ ht
  filter_upwards [hX, brunRoundingError_eventually_le_rpow (δ/2) (by linarith),
    eventually_gt_atTop (0 : ℕ)] with N hXN hEN hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hXNsq : (X N)^2 ≤ N := by
    have hpow : (N : ℝ)^(1-δ) ≤ N := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1 (by linarith : 1-δ ≤ 1)
    exact_mod_cast hXN.trans hpow
  have hE0 := (brunRoundingError_pos _ (nearTieSieveCutoff_one_le N)).le
  have he : (X N : ℝ)^2*brunRoundingError (nearTieSieveCutoff N)/N ≤ (N : ℝ)^(-(δ/2)) := by
    calc
      _ ≤ ((N : ℝ)^(1-δ) * (N : ℝ)^(δ/2))/N :=
        div_le_div_of_nonneg_right (mul_le_mul hXN hEN hE0 (Real.rpow_nonneg hN0.le _)) hN0.le
      _ = _ := by
        rw [← Real.rpow_add hN0]
        have hexp : -(δ/2) = (1-δ+δ/2)-1 := by ring
        rw [hexp, Real.rpow_sub hN0, Real.rpow_one]
  exact (boundedCofactorNearTieSet_ratio_bound N C (X N) (nearTieSieveCutoff N)
    hN (nearTieSieveCutoff_one_le N) hXNsq).trans (add_le_add le_rfl he)

lemma card_filter_range_add_le (P : ℕ → Prop) [DecidablePred P] (N k : ℕ) :
    ((range (N+k)).filter P).card ≤ ((range N).filter P).card + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Nat.add_assoc, range_add_one, filter_insert]
    split_ifs
    · exact (card_insert_le _ _).trans (by omega)
    · omega

lemma smooth_shifted_Icc_count_le (N z j : ℕ) (hj : j ≤ 1) :
    ((Icc 2 N).filter fun n => Nat.maxPrimeFac (n+j) ≤ z).card ≤
      ((range N).filter fun n => Nat.maxPrimeFac n ≤ z).card + 2 := by
  have hcount : ((Icc 2 N).filter fun n => Nat.maxPrimeFac (n+j) ≤ z).card ≤
      ((range (N+2)).filter fun n => Nat.maxPrimeFac n ≤ z).card := by
    apply card_le_card_of_injOn (fun n => n+j)
    · intro n hn
      simp only [mem_coe, mem_filter, mem_Icc, mem_range] at hn ⊢
      exact ⟨by omega, hn.2⟩
    · intro n hn m hm h
      dsimp at h
      omega
  exact hcount.trans (card_filter_range_add_le _ N 2)

lemma boundedCofactorNearTieSet_remove_cutoff (N C X z : ℕ) :
    (boundedCofactorNearTieSet N C X 0).card ≤
      (boundedCofactorNearTieSet N C X z).card +
      2 * ((range N).filter fun n => Nat.maxPrimeFac n ≤ z).card + 4 := by
  let A := (Icc 2 N).filter fun n => Nat.maxPrimeFac n ≤ z
  let B := (Icc 2 N).filter fun n => Nat.maxPrimeFac (n+1) ≤ z
  have hs : boundedCofactorNearTieSet N C X 0 ⊆ boundedCofactorNearTieSet N C X z ∪ A ∪ B := by
    intro n hn
    obtain ⟨hn,ha,hb,hpq,hqp,_,_⟩ := mem_filter.mp hn
    by_cases hp : z < Nat.maxPrimeFac n
    · by_cases hq : z < Nat.maxPrimeFac (n+1)
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hn,ha,hb,hpq,hqp,hp,hq⟩))
      · exact mem_union_right _ (mem_filter.mpr ⟨hn,by omega⟩)
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hn,by omega⟩))
  have h := (card_le_card hs).trans (card_union_le _ _)
  have h' := card_union_le (s := boundedCofactorNearTieSet N C X z) (t := A)
  have hA := smooth_shifted_Icc_count_le N z 0 (by omega)
  have hB := smooth_shifted_Icc_count_le N z 1 le_rfl
  simp only [Nat.add_zero] at hA
  change A.card ≤ _ at hA
  change B.card ≤ _ at hB
  omega

/-- The lower bound on both prime factors can be removed, because the chosen
sieve cutoff is subpower and hence smooth integers are negligible. -/
theorem cofactorNearTieSet_tendsto_zero (C : ℕ) (X : ℕ → ℕ)
    (δ : ℝ) (hδ : 0 < δ)
    (hX : ∀ᶠ N : ℕ in atTop, (X N : ℝ)^2 ≤ (N : ℝ)^(1-δ)) :
    Tendsto (fun N : ℕ => ((boundedCofactorNearTieSet N C (X N) 0).card : ℝ)/N)
      atTop (nhds 0) := by
  have hgood := boundedCofactorNearTieSet_tendsto_zero C X δ hδ hX
  have hsmooth := subpower_smooth_count_tendsto_zero nearTieSieveCutoff nearTieSieveCutoff_subpower
  have ht := (hgood.add (hsmooth.const_mul (2 : ℝ))).add
    (tendsto_const_div_atTop_nhds_zero_nat (4 : ℝ))
  simp only [mul_zero, add_zero] at ht
  apply squeeze_zero (fun N => by positivity) _ ht
  intro N
  have h := (Nat.cast_le (α := ℝ)).mpr (boundedCofactorNearTieSet_remove_cutoff N C (X N) (nearTieSieveCutoff N))
  have hdiv := div_le_div_of_nonneg_right h (Nat.cast_nonneg N)
  convert hdiv using 1; push_cast; ring

def smallCofactorRatioEvent (C : ℕ) (α : ℝ) (n : ℕ) : Prop :=
  1 < n ∧ (primeCofactor n : ℝ) ≤ (n : ℝ)^α ∧
    (primeCofactor (n+1) : ℝ) ≤ (n : ℝ)^α ∧
    Nat.maxPrimeFac n ≤ C*Nat.maxPrimeFac (n+1) ∧
    Nat.maxPrimeFac (n+1) ≤ C*Nat.maxPrimeFac n

/-- A natural-density-zero theorem in the small-cofactor regime. -/
theorem smallCofactorRatioEvent_hasDensity_zero (C : ℕ) (α : ℝ)
    (hα0 : 0 ≤ α) (hα : α < 1/2) :
    {n | smallCofactorRatioEvent C α n}.HasDensity 0 := by
  classical
  let X : ℕ → ℕ := fun N => ⌊(N : ℝ)^α⌋₊
  have hX : ∀ᶠ N : ℕ in atTop, (X N : ℝ)^2 ≤ (N : ℝ)^(1-(1-2*α)) := by
    apply Eventually.of_forall
    intro N
    have hf : (X N : ℝ) ≤ (N : ℝ)^α := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    have h := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) (X N)) hf 2
    have he : ((N : ℝ)^α)^2 = (N : ℝ)^(1-(1-2*α)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
      congr 1
      ring
    rwa [he] at h
  have ht := cofactorNearTieSet_tendsto_zero C X (1-2*α) (by linarith) hX
  rw [density_iff_count]
  apply squeeze_zero (fun N => by positivity) _ ht
  intro N
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  apply Nat.cast_le.mpr
  apply card_le_card
  intro n hn
  obtain ⟨hnN, hn, ha, hb, hpq, hqp⟩ := mem_filter.mp hn
  have hnN' := (mem_range.mp hnN).le
  have hrpow := Real.rpow_le_rpow (Nat.cast_nonneg n)
    (show (n : ℝ) ≤ N by exact_mod_cast hnN') hα0
  apply mem_filter.mpr
  exact ⟨mem_Icc.mpr ⟨hn,hnN'⟩, Nat.le_floor (ha.trans hrpow), Nat.le_floor (hb.trans hrpow),
    hpq,hqp,(Nat.prime_maxPrimeFac_of_one_lt n hn).pos,
    (Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega)).pos⟩

lemma density_zero_of_eventually_imp (P Q : ℕ → Prop)
    (hPQ : ∀ᶠ n : ℕ in atTop, P n → Q n) (hQ : {n | Q n}.HasDensity 0) :
    {n | P n}.HasDensity 0 := by
  classical
  obtain ⟨K,hK⟩ := eventually_atTop.mp hPQ
  have hcount (N : ℕ) : ((range N).filter P).card ≤ ((range N).filter Q).card + K := by
    have hs : (range N).filter P ⊆ (range N).filter Q ∪ range K := by
      intro n hn
      obtain ⟨hnN,hnP⟩ := mem_filter.mp hn
      by_cases hnK : n < K
      · exact mem_union_right _ (mem_range.mpr hnK)
      · exact mem_union_left _ (mem_filter.mpr ⟨hnN,hK n (by omega) hnP⟩)
    simpa only [card_range] using (card_le_card hs).trans (card_union_le _ _)
  rw [density_iff_count] at hQ ⊢
  have ht := hQ.add (tendsto_const_div_atTop_nhds_zero_nat (K : ℝ))
  simp only [add_zero] at ht
  apply squeeze_zero (fun N => by positivity) _ ht
  intro N
  have h := div_le_div_of_nonneg_right ((Nat.cast_le (α := ℝ)).mpr (hcount N)) (Nat.cast_nonneg N)
  simpa only [Nat.cast_add, add_div] using h

def largePrimeRatioEvent (C : ℕ) (β : ℝ) (n : ℕ) : Prop :=
  1 < n ∧ (n : ℝ)^β ≤ Nat.maxPrimeFac n ∧ (n : ℝ)^β ≤ Nat.maxPrimeFac (n+1) ∧
    Nat.maxPrimeFac n ≤ C*Nat.maxPrimeFac (n+1) ∧
    Nat.maxPrimeFac (n+1) ≤ C*Nat.maxPrimeFac n

lemma largePrimeRatioEvent_eventually_small_cofactor (C : ℕ) (β α : ℝ)
    (hgap : 1-β < α) :
    ∀ᶠ n : ℕ in atTop, largePrimeRatioEvent C β n → smallCofactorRatioEvent C α n := by
  have hγ : 0 < α-(1-β) := by linarith
  filter_upwards [((tendsto_rpow_atTop hγ).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2]
    with n hlarge
  intro hevent
  obtain ⟨hn,hp,hq,hpq,hqp⟩ := hevent
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have ha0 : (0 : ℝ) ≤ primeCofactor n := Nat.cast_nonneg _
  have hb0 : (0 : ℝ) ≤ primeCofactor (n+1) := Nat.cast_nonneg _
  have ha : (primeCofactor n : ℝ)*Nat.maxPrimeFac n = n := by
    exact_mod_cast (show primeCofactor n * Nat.maxPrimeFac n = n by
      simpa only [mul_comm] using maxPrimeFac_mul_primeCofactor n)
  have hb : (primeCofactor (n+1) : ℝ)*Nat.maxPrimeFac (n+1) = n+1 := by
    exact_mod_cast (show primeCofactor (n+1) * Nat.maxPrimeFac (n+1) = n+1 by
      simpa only [mul_comm] using maxPrimeFac_mul_primeCofactor (n+1))
  have hpow0 : 0 < (n : ℝ)^β := Real.rpow_pos_of_pos hn0 _
  have hdiv : (n : ℝ)/(n : ℝ)^β = (n : ℝ)^(1-β) := by
    rw [Real.rpow_sub hn0, Real.rpow_one]
  have hCa : (primeCofactor n : ℝ) ≤ (n : ℝ)^(1-β) := by
    rw [← hdiv]
    apply (le_div_iff₀ hpow0).mpr
    calc
      _ ≤ (primeCofactor n : ℝ)*Nat.maxPrimeFac n := mul_le_mul_of_nonneg_left hp ha0
      _ = _ := ha
  have hCb : (primeCofactor (n+1) : ℝ) ≤ 2*(n : ℝ)^(1-β) := by
    rw [← hdiv, ← mul_div_assoc]
    apply (le_div_iff₀ hpow0).mpr
    have h := mul_le_mul_of_nonneg_left hq hb0
    nlinarith
  have he : 2*(n : ℝ)^(1-β) ≤ (n : ℝ)^α := by
    have h := mul_le_mul_of_nonneg_left hlarge (Real.rpow_nonneg hn0.le (1-β))
    dsimp only [Function.comp_def] at h
    rw [← Real.rpow_add hn0] at h
    have hexp : (1-β)+(α-(1-β)) = α := by ring
    rw [hexp] at h
    simpa only [mul_comm] using h
  refine ⟨hn, ?_, hCb.trans he, hpq,hqp⟩
  exact hCa.trans ((by have := Real.rpow_nonneg hn0.le (1-β); linarith :
    (n : ℝ)^(1-β) ≤ 2*(n : ℝ)^(1-β)).trans he)

/-- Fixed-ratio near ties have density zero when both largest prime factors
are above any fixed power strictly larger than the square root. -/
theorem largePrimeRatioEvent_hasDensity_zero (C : ℕ) (β : ℝ) (hβ : 1/2 < β) :
    {n | largePrimeRatioEvent C β n}.HasDensity 0 := by
  let α : ℝ := max 0 ((1-β+1/2)/2)
  have hα0 : 0 ≤ α := le_max_left _ _
  have hα : α < 1/2 := max_lt (by norm_num) (by linarith)
  have hgap : 1-β < α := by
    have h := le_max_right 0 ((1-β+1/2)/2)
    dsimp [α]
    linarith
  exact density_zero_of_eventually_imp _ _
    (largePrimeRatioEvent_eventually_small_cofactor C β α hgap)
    (smallCofactorRatioEvent_hasDensity_zero C α hα0 hα)

#print axioms smallCofactorRatioEvent_hasDensity_zero
#print axioms largePrimeRatioEvent_hasDensity_zero
#print axioms cofactorNearTieSet_tendsto_zero
end FiniteSieve
end Erdos371
