import Submission.PolynomialThreeAPThreshold

/-! Transfer of the quantitative three-term bound from odd cyclic groups to integer intervals. -/
namespace Erdos3IntegerThreeAPBound
open Finset Erdos3PolynomialThreeAPThreshold Erdos3DyadicThreeAPBound Erdos3CorrelationSifting
open scoped BigOperators Classical
set_option maxHeartbeats 3000000

lemma odd_zmod_doubling (N : ℕ) : Function.Bijective (fun x : ZMod (2*N+1) ↦ x+x) := by
  have hu : IsUnit (2 : ZMod (2*N+1)) :=
    (ZMod.isUnit_iff_coprime 2 (2*N+1)).mpr (Nat.coprime_two_left.mpr (odd_two_mul_add_one N))
  have hi : Function.Injective (fun x : ZMod (2*N+1) ↦ x+x) := by
    intro x y hxy
    apply hu.mul_left_cancel
    simpa only [two_mul] using hxy
  exact ⟨hi,Finite.surjective_of_injective hi⟩

lemma cast_interval_injective (N : ℕ) (S : Finset ℕ) (hS : S ⊆ range N) :
    Set.InjOn (fun n : ℕ ↦ (n : ZMod (2*N+1))) (S : Set ℕ) := by
  intro a ha b hb hab
  have ha' : a < 2*N+1 := by have := mem_range.mp (hS ha); omega
  have hb' : b < 2*N+1 := by have := mem_range.mp (hS hb); omega
  have hh := congrArg ZMod.val hab
  simpa only [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] using hh

lemma cast_threeAPFree (N : ℕ) (S : Finset ℕ) (hS : S ⊆ range N)
    (hfree : ThreeAPFree (S : Set ℕ)) :
    ThreeAPFree (S.image (fun n : ℕ ↦ (n : ZMod (2*N+1))) : Set (ZMod (2*N+1))) := by
  intro x hx y hy z hz hxyz
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
  obtain ⟨b,hb,rfl⟩ := mem_image.mp hy
  obtain ⟨c,hc,rfl⟩ := mem_image.mp hz
  have haN := mem_range.mp (hS ha)
  have hbN := mem_range.mp (hS hb)
  have hcN := mem_range.mp (hS hc)
  have he : a+c = b+b := by
    have hh := congrArg ZMod.val hxyz
    simp only [← Nat.cast_add, ZMod.val_natCast_of_lt (by omega : a+c < 2*N+1),
      ZMod.val_natCast_of_lt (by omega : b+b < 2*N+1)] at hh
    exact hh
  exact congrArg (fun n : ℕ ↦ (n : ZMod (2*N+1))) (hfree ha hb hc he)

lemma dyadic_shift_two (l : ℕ) : dyadicDensity (l+2) = dyadicDensity l/4 := by
  unfold dyadicDensity
  rw [pow_add, div_div]
  norm_num

/-- A three-term-free subset of [0,N) with density at least 2^-l forces a
polynomial-exponent upper bound on N. -/
theorem integer_threeAP_density_bound (N l : ℕ) (hN : 0 < N)
    (S : Finset ℕ) (hS : S ⊆ range N) (hfree : ThreeAPFree (S : Set ℕ))
    (hdensity : dyadicDensity l ≤ (S.card : ℝ)/N) : N < 2^(thresholdExponent (l+2)) := by
  letI : NeZero (2*N+1) := ⟨by omega⟩
  let T := S.image (fun n : ℕ ↦ (n : ZMod (2*N+1)))
  have hcard : T.card = S.card := card_image_of_injOn (cast_interval_injective N S hS)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hSpos : 0 < S.card := by
    have hh := (dyadicDensity_pos l).trans_le hdensity
    have hc : (0 : ℝ) < S.card := by simpa using (lt_div_iff₀ hNpos).mp hh
    exact_mod_cast hc
  have hT : T.Nonempty := (card_pos.mp hSpos).image _
  have hden : dyadicDensity (l+2) ≤ density T := by
    unfold density
    rw [hcard, ZMod.card, dyadic_shift_two]
    have hM : (0 : ℝ) < (2*N+1 : ℕ) := by positivity
    apply (le_div_iff₀ hM).mpr
    have hh := (le_div_iff₀ hNpos).mp hdensity
    push_cast
    have hp := dyadicDensity_pos l
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hh := threeAPFree_card_lt_pow_threshold (odd_zmod_doubling N) T hT
    (cast_threeAPFree N S hS hfree) (l+2) hden
  rw [ZMod.card] at hh
  omega

/-- Above the threshold, every three-term-free subset of the interval has small density. -/
theorem integer_threeAP_density_lt (N l : ℕ) (hN : 0 < N)
    (hbig : 2^(thresholdExponent (l+2)) ≤ N)
    (S : Finset ℕ) (hS : S ⊆ range N) (hfree : ThreeAPFree (S : Set ℕ)) :
    (S.card : ℝ)/N < dyadicDensity l := by
  by_contra! h
  exact (not_lt_of_ge hbig) (integer_threeAP_density_bound N l hN S hS hfree h)

#print axioms integer_threeAP_density_bound
#print axioms integer_threeAP_density_lt
end Erdos3IntegerThreeAPBound
