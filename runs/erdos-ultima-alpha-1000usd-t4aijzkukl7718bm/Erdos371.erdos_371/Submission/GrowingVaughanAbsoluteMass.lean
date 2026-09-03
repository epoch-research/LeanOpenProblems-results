import Submission.VaughanLongCoefficients
import Submission.PowerSeparatedVaughan
import Submission.RichPowerPrimeBands
import Submission.LargePrimeSquares

/-! Growing Vaughan cutoffs do not make the absolute reciprocal long tail
negligible. Distinct prime products in a square band give a uniform positive
mass. This rules out an absolute-value shortcut, not the Erdős conjecture. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology
set_option autoImplicit false

noncomputable def increasingPrimePairs (S : Finset ℕ) : Finset (ℕ × ℕ) :=
  (S ×ˢ S).filter (fun z => z.1 < z.2)

lemma reciprocal_pair_square_identity (S : Finset ℕ) :
    (∑ p ∈ S, (1 : ℝ)/p)^2 =
      (∑ p ∈ S, (1 : ℝ)/(p : ℝ)^2)+
        2*∑ z ∈ increasingPrimePairs S, (1 : ℝ)/(z.1*z.2 : ℕ) := by
  have hpoint (p q : ℕ) : (1 : ℝ)/p*(1/q) =
      (if p=q then 1/(p : ℝ)^2 else 0)+
      (if p<q then (1 : ℝ)/(p*q : ℕ) else 0)+
      (if q<p then (1 : ℝ)/(p*q : ℕ) else 0) := by
    rcases lt_trichotomy p q with h | rfl | h
    · simp only [h,h.ne,h.not_gt,if_true,if_false,zero_add,add_zero,Nat.cast_mul]
      ring
    · simp only [lt_self_iff_false,if_true,if_false,add_zero]
      ring
    · simp only [h,h.ne',h.not_gt,if_true,if_false,zero_add,Nat.cast_mul]
      ring
  have hswap : (∑ p ∈ S, ∑ q ∈ S, if q<p then (1 : ℝ)/(p*q : ℕ) else 0) =
      ∑ p ∈ S, ∑ q ∈ S, if p<q then (1 : ℝ)/(p*q : ℕ) else 0 := by
    rw [sum_comm]
    simp only [Nat.mul_comm]
  rw [pow_two,sum_mul_sum]
  simp_rw [hpoint,sum_add_distrib]
  rw [hswap]
  have hdiag : (∑ p ∈ S, ∑ q ∈ S, if p=q then (1 : ℝ)/(p : ℝ)^2 else 0) =
      ∑ p ∈ S, (1 : ℝ)/(p : ℝ)^2 := by
    apply sum_congr rfl
    intro p hp
    simp [hp]
  rw [hdiag]
  simp only [increasingPrimePairs,sum_filter,sum_product]
  ring

lemma increasingPrimePairs_product_injective (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) :
    Set.InjOn (fun z : ℕ × ℕ => z.1*z.2) (increasingPrimePairs S) := by
  rintro ⟨p,q⟩ hpq ⟨r,s⟩ hrs he
  obtain ⟨hpq,hpq'⟩ := mem_filter.mp hpq
  obtain ⟨hrs,hrs'⟩ := mem_filter.mp hrs
  obtain ⟨hp,hq⟩ := mem_product.mp hpq
  obtain ⟨hr,hs⟩ := mem_product.mp hrs
  have hpp := hS p hp
  have hqq := hS q hq
  have hrr := hS r hr
  have hss := hS s hs
  change p*q=r*s at he
  change p<q at hpq'
  change r<s at hrs'
  have hd : p ∣ r*s := by rw [← he]; exact dvd_mul_right _ _
  rcases hpp.dvd_mul.mp hd with hrp | hsp
  · have hpr := (Nat.prime_dvd_prime_iff_eq hpp hrr).mp hrp
    subst r
    have hqs := Nat.eq_of_mul_eq_mul_left hpp.pos he
    subst s
    rfl
  · have hps := (Nat.prime_dvd_prime_iff_eq hpp hss).mp hsp
    subst s
    have hqr : q=r := Nat.eq_of_mul_eq_mul_left hpp.pos (by simpa only [Nat.mul_comm] using he)
    omega

noncomputable def vaughanAbsoluteReciprocalWindow (U V C N : ℕ) : ℝ :=
  ∑ q ∈ Ioc C N, |vaughanLongFunction U V q/Real.log q|/(q : ℝ)

lemma square_band_semiprime_mass_le_long_mass (B U V : ℕ)
    (hB : 1 ≤ B) (hU : 1 ≤ U) (hV : 1 ≤ V) (hUB : U ≤ B) (hVB : V ≤ B) :
    (∑ z ∈ increasingPrimePairs (largePrimeSet B (B^2)), (1 : ℝ)/(z.1*z.2 : ℕ)) ≤
      vaughanAbsoluteReciprocalWindow U V (B^2) (B^4) := by
  let S := largePrimeSet B (B^2)
  let T := (increasingPrimePairs S).image (fun z => z.1*z.2)
  have hS (p : ℕ) (hp : p ∈ S) : p.Prime ∧ B<p ∧ p≤B^2 := by
    obtain ⟨hp,hBp⟩ := mem_filter.mp hp
    obtain ⟨hpB,hpp⟩ := Nat.mem_primesBelow.mp hp
    exact ⟨hpp,hBp,by omega⟩
  have hsub : T ⊆ Ioc (B^2) (B^4) := by
    intro q hq
    obtain ⟨⟨r,s⟩,hrs,rfl⟩ := mem_image.mp hq
    obtain ⟨hrs,_⟩ := mem_filter.mp hrs
    obtain ⟨hr,hs⟩ := mem_product.mp hrs
    have hr := hS r hr
    have hs := hS s hs
    apply mem_Ioc.mpr
    constructor
    · dsimp only
      nlinarith
    · have hh := Nat.mul_le_mul hr.2.2 hs.2.2
      exact hh.trans_eq (by ring)
  have he (q : ℕ) (hq : q ∈ T) :
      |vaughanLongFunction U V q/Real.log q|/(q : ℝ) = 1/(q : ℝ) := by
    obtain ⟨⟨r,s⟩,hrs,rfl⟩ := mem_image.mp hq
    obtain ⟨hrs,hrs'⟩ := mem_filter.mp hrs
    obtain ⟨hr,hs⟩ := mem_product.mp hrs
    have hr := hS r hr
    have hs := hS s hs
    rw [vaughanLongFunction_semiprime U V r s hU hV hr.1 hs.1 (by omega)
      (by omega) (by omega)]
    norm_num
  have hi := increasingPrimePairs_product_injective S (fun p hp => (hS p hp).1)
  calc
    _ = ∑ q ∈ T, (1 : ℝ)/q := (sum_image hi).symm
    _ = ∑ q ∈ T, |vaughanLongFunction U V q/Real.log q|/(q : ℝ) :=
      sum_congr rfl (fun q hq => (he q hq).symm)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)

lemma square_band_reciprocal_square_tendsto :
    Tendsto (fun B => ∑ p ∈ largePrimeSet B (B^2), (1 : ℝ)/(p : ℝ)^2) atTop (𝓝 0) := by
  have hs : Summable (fun p : ℕ => (1 : ℝ)/(p : ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have ht := (hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).const_sub
    (∑' p : ℕ, (1 : ℝ)/(p : ℝ)^2)
  simp only [sub_self] at ht
  apply squeeze_zero (fun _ => by positivity) _ ht
  intro B
  apply le_trans _ (reciprocal_square_tail_bound B (B^2))
  apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
  intro p hp
  obtain ⟨hp,hBp⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨mem_range.mpr (Nat.mem_primesBelow.mp hp).1,hBp⟩

/-- The absolute reciprocal tail stays bounded below even with arbitrary
moving cutoffs as large as B. The lower bound is uniform in U and V. -/
theorem growing_vaughan_absolute_mass_positive :
    ∀ᶠ B : ℕ in atTop, ∀ U V : ℕ, 1 ≤ U → 1 ≤ V → U ≤ B → V ≤ B →
      (1/64 : ℝ) ≤ vaughanAbsoluteReciprocalWindow U V (B^2) (B^4) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_gt_atTop (1 : ℕ),
    hlog.eventually_ge_atTop (2*(1+primePowerErrorConstant+Real.log 4)),
    square_band_reciprocal_square_tendsto.eventually_lt_const (by norm_num : (0 : ℝ)<1/32)]
    with B hB hBl hd
  intro U V hU hV hUB hVB
  have hmass := square_prime_band_mass_lower B hB hBl
  have hs := reciprocal_pair_square_identity (largePrimeSet B (B^2))
  change (1/4 : ℝ) ≤ ∑ p ∈ largePrimeSet B (B^2), (1 : ℝ)/p at hmass
  have hp : (1/64 : ℝ) ≤ ∑ z ∈ increasingPrimePairs (largePrimeSet B (B^2)),
      (1 : ℝ)/(z.1*z.2 : ℕ) := by nlinarith
  exact hp.trans (square_band_semiprime_mass_le_long_mass B U V hB.le hU hV hUB hVB)

lemma vaughanPowerCutoff_fourth_le (γ : ℝ) (hγ : γ ≤ 1/4) (B : ℕ) (hB : 1 ≤ B) :
    vaughanPowerCutoff γ (B^4) ≤ B := by
  have hBr : (0 : ℝ)<B := by exact_mod_cast hB
  have hb := vaughanPowerCutoff_le γ (B^4)
  have hp : ((B^4 : ℕ) : ℝ)^γ ≤ B := by
    rw [Nat.cast_pow,← Real.rpow_natCast,← Real.rpow_mul hBr.le]
    have hh := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hB : (1 : ℝ)≤B)
      (show (4 : ℕ)*γ ≤ 1 by norm_num; linarith)
    simpa only [Real.rpow_one] using hh
  exact_mod_cast hb.trans hp

/-- This disproves only absolute-tail decay for the growing Vaughan
coefficients, NOT the original comparison-density conjecture. -/
theorem polynomial_vaughan_absolute_mass_not_zero (γ : ℝ) (hγ : 0 < γ) (hγq : γ ≤ 1/4) :
    ¬Tendsto (fun B : ℕ => vaughanAbsoluteReciprocalWindow
      (vaughanPowerCutoff γ (B^4)) (vaughanPowerCutoff γ (B^4)) (B^2) (B^4)) atTop (𝓝 0) := by
  intro hz
  obtain ⟨B,hB,hpos,hsmall⟩ := (eventually_ge_atTop (1 : ℕ) |>.and
    (growing_vaughan_absolute_mass_positive.and
      (hz.eventually_lt_const (by norm_num : (0 : ℝ)<1/128)))).exists
  have hT := vaughanPowerCutoff_pos γ hγ.le (B^4) (by exact pow_pos (by omega : 0<B) _)
  have hTB := vaughanPowerCutoff_fourth_le γ hγq B hB
  have hh := hpos _ _ hT hT hTB hTB
  linarith

#print axioms growing_vaughan_absolute_mass_positive
#print axioms polynomial_vaughan_absolute_mass_not_zero
end Erdos371
