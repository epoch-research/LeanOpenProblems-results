import Submission.PrimeBandDensity

/-! Fixed multiplicative-ratio near ties between consecutive largest prime
factors have natural density zero. This does not assert symmetry of their order. -/

namespace Erdos371
namespace FiniteSieve
open Finset Filter

lemma factorRatioEvent_eventually_split (C : ℕ) (u a b v : ℝ) (hua : u < a) (hbv : b < v) :
    ∀ᶠ n : ℕ in atTop, factorRatioEvent C n →
      smallPrimeRatioEvent C a n ∨ largePrimeRatioEvent C b n ∨ logPrimeBandEvent u v n := by
  have ha := ((tendsto_rpow_atTop (sub_pos.mpr hua)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (C : ℝ)
  have hb := ((tendsto_rpow_atTop (sub_pos.mpr hbv)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (C : ℝ)
  filter_upwards [ha,hb,eventually_gt_atTop (1 : ℕ)] with n hCa hCb hn
  intro hcomp
  dsimp only [Function.comp_def] at hCa hCb
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.le
  have hcomp1 : (Nat.maxPrimeFac n : ℝ) ≤ C*(Nat.maxPrimeFac (n+1) : ℝ) := by exact_mod_cast hcomp.1
  have hcomp2 : (Nat.maxPrimeFac (n+1) : ℝ) ≤ C*(Nat.maxPrimeFac n : ℝ) := by exact_mod_cast hcomp.2
  by_cases hp : (Nat.maxPrimeFac n : ℝ) ≤ (n : ℝ)^u
  · apply Or.inl
    refine ⟨hn,hp.trans (Real.rpow_le_rpow_of_exponent_le hn1 hua.le),?_,hcomp⟩
    calc
      (Nat.maxPrimeFac (n+1) : ℝ) ≤ C*(Nat.maxPrimeFac n : ℝ) := hcomp2
      _ ≤ (n : ℝ)^(a-u)*(n : ℝ)^u := mul_le_mul hCa hp (Nat.cast_nonneg _) (Real.rpow_nonneg hn0.le _)
      _ = _ := by rw [← Real.rpow_add hn0,sub_add_cancel]
  · by_cases hq : (n : ℝ)^v ≤ (Nat.maxPrimeFac n : ℝ)
    · apply Or.inr ∘ Or.inl
      refine ⟨hn,(Real.rpow_le_rpow_of_exponent_le hn1 hbv.le).trans hq,?_,hcomp.1,hcomp.2⟩
      have hgap : 0 < (n : ℝ)^(v-b) := Real.rpow_pos_of_pos hn0 _
      have hprod : (n : ℝ)^v ≤ (Nat.maxPrimeFac (n+1) : ℝ)*(n : ℝ)^(v-b) := by
        have h := mul_le_mul_of_nonneg_right hCb (Nat.cast_nonneg (α := ℝ) (Nat.maxPrimeFac (n+1)))
        exact hq.trans (hcomp1.trans (by simpa only [mul_comm] using h))
      have he : (n : ℝ)^b = (n : ℝ)^v/(n : ℝ)^(v-b) := by
        rw [← Real.rpow_sub hn0,sub_sub_cancel]
      rw [he]
      exact (div_le_iff₀ hgap).mpr hprod
    · exact Or.inr (Or.inr ⟨hn,le_of_lt (lt_of_not_ge hp),(lt_of_not_ge hq).le⟩)

lemma count_le_of_eventually_three_cover (P Q R W : ℕ → Prop)
    [DecidablePred P] [DecidablePred Q] [DecidablePred R] [DecidablePred W]
    (hcover : ∀ᶠ n : ℕ in atTop, P n → Q n ∨ R n ∨ W n) :
    ∃ K : ℕ, ∀ N : ℕ, ((range N).filter P).card ≤
      ((range N).filter Q).card + ((range N).filter R).card + ((range N).filter W).card + K := by
  obtain ⟨K,hK⟩ := eventually_atTop.mp hcover
  refine ⟨K,fun N => ?_⟩
  have hs : (range N).filter P ⊆
      ((range N).filter Q ∪ (range N).filter R) ∪ (range N).filter W ∪ range K := by
    intro n hn
    obtain ⟨hnN,hnP⟩ := mem_filter.mp hn
    by_cases hnK : n < K
    · exact mem_union_right _ (mem_range.mpr hnK)
    · rcases hK n (by omega) hnP with hQ | hR | hW
      · exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hnN,hQ⟩)))
      · exact mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hnN,hR⟩)))
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hnN,hW⟩))
  have hc := card_le_card hs
  have h1 := card_union_le ((range N).filter Q) ((range N).filter R)
  have h2 := card_union_le ((range N).filter Q ∪ (range N).filter R) ((range N).filter W)
  have h3 := card_union_le (((range N).filter Q ∪ (range N).filter R) ∪ (range N).filter W) (range K)
  rw [card_range] at h3
  omega

/-- Consecutive largest prime factors escape every fixed multiplicative
neighborhood of one another outside a set of natural density zero. -/
theorem factorRatioEvent_hasDensity_zero (C : ℕ) :
    {n | factorRatioEvent C n}.HasDensity 0 := by
  classical
  rw [density_iff_count]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ : ℝ := min (ε/1000) (1/100)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδsmall : δ ≤ 1/100 := min_le_right _ _
  have hδε : δ ≤ ε/1000 := min_le_left _ _
  let u : ℝ := 1/2-δ
  let a : ℝ := 1/2-δ/2
  let b : ℝ := 1/2+δ/2
  let v : ℝ := 1/2+δ
  let t : ℝ := 1-δ
  have hu : 0 < u := by dsimp [u]; linarith
  have huv : u ≤ v := by dsimp [u,v]; linarith
  have ht : 0 < t := by dsimp [t]; linarith
  have ht1 : t < 1 := by dsimp [t]; linarith
  have hua : u < a := by dsimp [u,a]; linarith
  have hbv : b < v := by dsimp [b,v]; linarith
  have ha0 : 0 ≤ a := by dsimp [a]; linarith
  have ha : a < 1/2 := by dsimp [a]; linarith
  have hb : 1/2 < b := by dsimp [b]; linarith
  have hmu : 1/4 ≤ t*u := by dsimp [t,u]; nlinarith [sq_nonneg δ]
  have hmupos : 0 < t*u := mul_pos ht hu
  have hwidth : v-t*u ≤ (5/2)*δ := by dsimp [t,u,v]; nlinarith [sq_nonneg δ]
  have hbandconst : 8*(v-t*u)/(t*u) < ε/4 := by
    have hle : 8*(v-t*u)/(t*u) ≤ 80*δ := by
      apply (div_le_iff₀ hmupos).mpr
      have h := mul_le_mul_of_nonneg_left hmu hδ.le
      nlinarith
    linarith
  obtain ⟨K,hK⟩ := count_le_of_eventually_three_cover (factorRatioEvent C)
    (smallPrimeRatioEvent C a) (largePrimeRatioEvent C b) (logPrimeBandEvent u v)
    (factorRatioEvent_eventually_split C u a b v hua hbv)
  have hsmall := (density_iff_count _ 0).mp (smallPrimeRatioEvent_hasDensity_zero C a ha0 ha)
  have hlarge := (density_iff_count _ 0).mp (largePrimeRatioEvent_hasDensity_zero C b hb)
  have he := (hsmall.add hlarge).add (tendsto_const_div_atTop_nhds_zero_nat (K : ℝ))
  simp only [add_zero] at he
  filter_upwards [he.eventually (gt_mem_nhds (show 0 < ε/2 by linarith)),
    logPrimeBandEvent_eventually_ratio_le u v t hu huv ht ht1 (ε/4) (by linarith)] with N heN hbandN
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (by positivity)]
  have hc := div_le_div_of_nonneg_right ((Nat.cast_le (α := ℝ)).mpr (hK N)) (Nat.cast_nonneg N)
  simp only [Nat.cast_add,add_div] at hc
  linarith

#print axioms factorRatioEvent_hasDensity_zero
end FiniteSieve
end Erdos371
