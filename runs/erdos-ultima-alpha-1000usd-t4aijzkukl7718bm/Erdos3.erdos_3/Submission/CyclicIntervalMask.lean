import Submission.MaskedUniformityCounting

/-! Interval masks in a cyclic group: exact centering and a uniform lower
bound for the number of four-term patterns in the reference interval. -/
namespace Erdos3CyclicIntervalMask
open Finset Erdos3MaskedUniformityCounting Erdos3UniformityCounting
  Erdos3LinearFormsUniformity Erdos3CorrelationSifting
open scoped BigOperators Classical
set_option maxHeartbeats 4000000

noncomputable def castSet (p : ℕ) (S : Finset ℕ) : Finset (ZMod p) := S.image (fun k : ℕ ↦ (k : ZMod p))
noncomputable def intervalMask (p N : ℕ) : Finset (ZMod p) := castSet p (range N)
noncomputable def intervalDensity (S : Finset ℕ) (N : ℕ) : ℝ := (S.card : ℝ)/(N : ℝ)
noncomputable def relativeBalance (p N : ℕ) (S : Finset ℕ) (x : ZMod p) : ℝ :=
  indicator (castSet p S) x-intervalDensity S N*indicator (intervalMask p N) x

lemma castSet_card (p N : ℕ) [NeZero p] (hNp : N ≤ p) (S : Finset ℕ) (hS : S ⊆ range N) :
    (castSet p S).card = S.card := by
  unfold castSet
  apply card_image_of_injOn
  intro a ha b hb hab
  have ha' : a < p := (mem_range.mp (hS ha)).trans_le hNp
  have hb' : b < p := (mem_range.mp (hS hb)).trans_le hNp
  have he := congrArg ZMod.val hab
  rwa [ZMod.val_natCast_of_lt ha',ZMod.val_natCast_of_lt hb'] at he

lemma intervalMask_card (p N : ℕ) [NeZero p] (hNp : N ≤ p) : (intervalMask p N).card = N := by
  rw [intervalMask,castSet_card p N hNp (range N) (by rfl),card_range]

lemma mem_intervalMask (p N : ℕ) [NeZero p] (hNp : N ≤ p) (x : ZMod p) :
    x ∈ intervalMask p N ↔ x.val < N := by
  constructor
  · intro hx
    simp only [intervalMask,castSet] at hx
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hx
    have hkN := mem_range.mp hk
    simpa only [ZMod.val_natCast_of_lt (hkN.trans_le hNp)] using hkN
  · intro hx
    simp only [intervalMask,castSet]
    exact mem_image.mpr ⟨x.val,mem_range.mpr hx,ZMod.natCast_zmod_val x⟩

lemma castSet_subset_interval (p N : ℕ) (S : Finset ℕ) (hS : S ⊆ range N) :
    castSet p S ⊆ intervalMask p N := by
  unfold castSet intervalMask
  exact image_subset_image hS

lemma intervalDensity_bounds (N : ℕ) (hN : 0 < N) (S : Finset ℕ) (hS : S ⊆ range N) :
    0 ≤ intervalDensity S N ∧ intervalDensity S N ≤ 1 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨by unfold intervalDensity; positivity,(div_le_one hN').mpr ?_⟩
  exact_mod_cast (card_le_card hS).trans_eq (card_range N)

lemma relativeBalance_bound (p N : ℕ) [Fact p.Prime] (hN : 0 < N)
    (S : Finset ℕ) (hS : S ⊆ range N) (x : ZMod p) : |relativeBalance p N S x| ≤ 1 :=
  masked_indicator_bound (castSet p S) (intervalMask p N)
    (intervalDensity_bounds N hN S hS).1 (intervalDensity_bounds N hN S hS).2 x

lemma relativeBalance_mean_zero (p N : ℕ) [NeZero p] (hN : 0 < N) (hNp : N ≤ p)
    (S : Finset ℕ) (hS : S ⊆ range N) : (𝔼 x, relativeBalance p N S x) = 0 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  simp only [relativeBalance,expect_sub_distrib,← mul_expect,expect_indicator,
    density,castSet_card p N hNp S hS,intervalMask_card p N hNp,ZMod.card,intervalDensity]
  field_simp
  ring

lemma relativeBalance_outside (p N : ℕ) [NeZero p] (S : Finset ℕ) (hS : S ⊆ range N)
    {x : ZMod p} (hx : x ∉ intervalMask p N) : relativeBalance p N S x = 0 := by
  have hx' : x ∉ castSet p S := fun h ↦ hx (castSet_subset_interval p N S hS h)
  simp only [relativeBalance,indicator,if_neg hx,if_neg hx',mul_zero,sub_self]

lemma rectangle_pattern_membership (p N m k : ℕ) (hkm : k*m ≤ N)
    {x d : ZMod p} (hx : x ∈ intervalMask p m) (hd : d ∈ intervalMask p m) :
    ∀ i : Fin k, x+(i.val : ZMod p)*d ∈ intervalMask p N := by
  simp only [intervalMask,castSet] at hx hd
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
  obtain ⟨b,hb,rfl⟩ := mem_image.mp hd
  intro i
  have ha' := mem_range.mp ha
  have hb' := mem_range.mp hb
  have hi : i.val+1 ≤ k := i.isLt
  have hmul : i.val*b ≤ i.val*m := Nat.mul_le_mul_left _ hb'.le
  have hbound : a+i.val*b < N := by
    have hk := Nat.mul_le_mul_right m hi
    nlinarith
  simp only [intervalMask,castSet]
  apply mem_image.mpr
  refine ⟨a+i.val*b,mem_range.mpr hbound,?_⟩
  simp only [Nat.cast_add,Nat.cast_mul]

lemma interval_pattern_lower (p N m k : ℕ) [Fact p.Prime] (hmp : m ≤ p) (hkm : k*m ≤ N) :
    ((m : ℝ)/(p : ℝ))^2 ≤
      (linearAverage (fun i : Fin k ↦ (i.val : ZMod p))
        (fun _ x ↦ (indicator (intervalMask p N) x : ℂ))).re := by
  let J := intervalMask p m
  let I := intervalMask p N
  have hp (x d : ZMod p) : indicator J x*indicator J d ≤
      ∏ i : Fin k, indicator I (x+(i.val : ZMod p)*d) := by
    by_cases hx : x ∈ J
    · by_cases hd : d ∈ J
      · have hpat := rectangle_pattern_membership p N m k hkm hx hd
        have he : (∏ i : Fin k, indicator I (x+(i.val : ZMod p)*d)) = 1 := by
          apply prod_eq_one
          intro i _
          exact if_pos (hpat i)
        rw [he]
        simp only [indicator,if_pos hx,if_pos hd,mul_one,le_refl]
      · have hn : 0 ≤ ∏ i : Fin k, indicator I (x+(i.val : ZMod p)*d) :=
          prod_nonneg (fun i _ ↦ (indicator_norm_bounds I _).1)
        simpa only [indicator,if_neg hd,mul_zero] using hn
    · have hn : 0 ≤ ∏ i : Fin k, indicator I (x+(i.val : ZMod p)*d) :=
        prod_nonneg (fun i _ ↦ (indicator_norm_bounds I _).1)
      simpa only [indicator,if_neg hx,zero_mul] using hn
  calc
    _ = (density J)^2 := by rw [density,intervalMask_card p m hmp,ZMod.card]
    _ = 𝔼 x, 𝔼 d, indicator J x*indicator J d := by
      simp only [← mul_expect,← expect_mul,expect_indicator,pow_two]
    _ ≤ 𝔼 x, 𝔼 d, ∏ i : Fin k, indicator I (x+(i.val : ZMod p)*d) :=
      expect_le_expect (fun x _ ↦ expect_le_expect (fun d _ ↦ hp x d))
    _ = _ := by
      simp only [linearAverage,← Complex.ofReal_prod,← Complex.ofReal_expect,Complex.ofReal_re]
      rfl

lemma four_interval_patterns (p N : ℕ) [Fact p.Prime] (hN : 8 ≤ N) (hNp : N ≤ p) (hpN : p ≤ 4*N) :
    (1/1024 : ℝ) ≤ (linearAverage (fun i : Fin 4 ↦ (i.val : ZMod p))
      (fun _ x ↦ (indicator (intervalMask p N) x : ℂ))).re := by
  have hm : N ≤ 8*(N/4) := by omega
  have hmp : N/4 ≤ p := (Nat.div_le_self _ _).trans hNp
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hratio : (1/32 : ℝ) ≤ ((N/4 : ℕ) : ℝ)/(p : ℝ) := by
    apply (le_div_iff₀ hp).mpr
    have hh : p ≤ 32*(N/4) := by omega
    have hh' : (p : ℝ) ≤ 32*((N/4 : ℕ) : ℝ) := by exact_mod_cast hh
    linarith
  have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1/32) hratio 2
  apply le_trans (by norm_num at hs ⊢; exact hs)
  exact interval_pattern_lower p N (N/4) 4 hmp (by omega)

#print axioms relativeBalance_mean_zero
#print axioms four_interval_patterns
end Erdos3CyclicIntervalMask
