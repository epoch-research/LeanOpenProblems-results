import Submission.LocalMinimaOppositeCollisions

/-! Both orientations of local-minimum collision pairs contribute to the
weighted opposite mass. This sharpens the previous finite bound by a factor
of two; it does not establish the asymptotic opposite fraction one half. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

lemma primeLoserOppositeCollisions_swap_iff (B N : ℕ) (nm : ℕ × ℕ) :
    nm.swap ∈ primeLoserOppositeCollisions B N ↔
      nm ∈ primeLoserOppositeCollisions B N := by
  simp only [primeLoserOppositeCollisions, primeLoserCollisions,
    mem_filter, mem_offDiag, Prod.fst_swap, Prod.snd_swap]
  tauto

lemma primeLoserOppositeCollisions_label_eq (B N : ℕ) (nm : ℕ × ℕ)
    (hnm : nm ∈ primeLoserOppositeCollisions B N) :
    primeLoser nm.1 = primeLoser nm.2 :=
  (mem_filter.mp (mem_filter.mp hnm).1).2

lemma opposite_factorSign_neg_one_iff (n m : ℕ) (h : factorSign n ≠ factorSign m) :
    factorSign n = -1 ↔ factorSign m ≠ -1 := by
  unfold factorSign predicateSign at *
  split_ifs at * <;> norm_num at *

noncomputable def primeLoserFallRiseCollisions (B N : ℕ) : Finset (ℕ × ℕ) :=
  (primeLoserOppositeCollisions B N).filter fun nm => factorSign nm.1 = -1

noncomputable def primeLoserWeightedFallRiseMass (N : ℕ) : ℝ :=
  ∑ nm ∈ primeLoserFallRiseCollisions 0 N, (primeLoser nm.1 : ℝ)

/-- Swapping the two entries preserves their common prime weight and
exchanges the two orientations. No arithmetic cancellation is involved. -/
theorem primeLoserWeightedOppositeMass_eq_twice_fallRise (N : ℕ) :
    primeLoserWeightedOppositeMass N = 2 * primeLoserWeightedFallRiseMass N := by
  classical
  have he : (∑ nm ∈ primeLoserFallRiseCollisions 0 N, (primeLoser nm.1 : ℝ)) =
      ∑ nm ∈ (primeLoserOppositeCollisions 0 N).filter
        (fun nm => factorSign nm.1 ≠ -1), (primeLoser nm.1 : ℝ) := by
    apply sum_bij (fun nm _ => nm.swap)
    · intro nm hnm
      obtain ⟨hm, hs⟩ := mem_filter.mp hnm
      exact mem_filter.mpr ⟨(primeLoserOppositeCollisions_swap_iff 0 N nm).mpr hm,
        (opposite_factorSign_neg_one_iff nm.1 nm.2 (mem_filter.mp hm).2).mp hs⟩
    · intro a _ b _ hab
      exact Prod.swap_injective hab
    · intro nm hnm
      obtain ⟨hm, hs⟩ := mem_filter.mp hnm
      refine ⟨nm.swap, ?_, Prod.swap_swap nm⟩
      exact mem_filter.mpr ⟨(primeLoserOppositeCollisions_swap_iff 0 N nm).mpr hm,
        (opposite_factorSign_neg_one_iff nm.2 nm.1 (mem_filter.mp hm).2.symm).mpr hs⟩
    · intro nm hnm
      exact_mod_cast primeLoserOppositeCollisions_label_eq 0 N nm (mem_filter.mp hnm).1
  have hpart := sum_filter_add_sum_filter_not (primeLoserOppositeCollisions 0 N)
    (fun nm => factorSign nm.1 = -1) (fun nm => (primeLoser nm.1 : ℝ))
  change primeLoserWeightedFallRiseMass N + _ = primeLoserWeightedOppositeMass N at hpart
  change primeLoserWeightedFallRiseMass N = _ at he
  linarith

lemma localMinima_weighted_same_pair_sum_le_fallRise (B N : ℕ) :
    (∑ nm ∈ ((primeLocalMinimaAbove B N) ×ˢ (primeLocalMinimaAbove B N)).filter
      (fun nm => Nat.maxPrimeFac nm.1 = Nat.maxPrimeFac nm.2),
      (Nat.maxPrimeFac nm.1 : ℝ)) ≤ primeLoserWeightedFallRiseMass N := by
  classical
  let U := ((primeLocalMinimaAbove B N) ×ˢ (primeLocalMinimaAbove B N)).filter
    (fun nm => Nat.maxPrimeFac nm.1 = Nat.maxPrimeFac nm.2)
  let f := fun nm : ℕ × ℕ => (nm.1-1,nm.2)
  have hi : Set.InjOn f U := localMinima_pair_map_injective B N
  have hsub : U.image f ⊆ primeLoserFallRiseCollisions 0 N := by
    intro nm hnm
    obtain ⟨uv, huv, rfl⟩ := mem_image.mp hnm
    have hn := (mem_filter.mp (mem_product.mp (mem_filter.mp huv).1).1).1
    exact mem_filter.mpr ⟨localMinima_pair_maps_to_opposite B N uv huv,
      (primeLocalMinima_incidence_data N uv.1 hn).2.2.2.1⟩
  have he : (∑ nm ∈ U, (Nat.maxPrimeFac nm.1 : ℝ)) =
      ∑ nm ∈ U.image f, (primeLoser nm.1 : ℝ) := by
    rw [sum_image hi]
    apply sum_congr rfl
    intro nm hnm
    have hn := (mem_filter.mp (mem_product.mp (mem_filter.mp hnm).1).1).1
    have hd := primeLocalMinima_incidence_data N nm.1 hn
    simp only [f, hd.2.1]
  rw [he]
  exact sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)

/-- Count both the fall-to-rise pair and its reversed partner. -/
theorem twice_localMinima_weighted_same_pair_sum_le_opposite (B N : ℕ) :
    2 * (∑ nm ∈ ((primeLocalMinimaAbove B N) ×ˢ (primeLocalMinimaAbove B N)).filter
      (fun nm => Nat.maxPrimeFac nm.1 = Nat.maxPrimeFac nm.2),
      (Nat.maxPrimeFac nm.1 : ℝ)) ≤ primeLoserWeightedOppositeMass N := by
  rw [primeLoserWeightedOppositeMass_eq_twice_fallRise]
  exact mul_le_mul_of_nonneg_left (localMinima_weighted_same_pair_sum_le_fallRise B N)
    (by norm_num)

/-- The sharper weighted Cauchy--Schwarz bound retains both orientations. -/
theorem twice_primeLocalMinimaAbove_sq_le_weightedOpposite (B N : ℕ) :
    2 * ((primeLocalMinimaAbove B N).card : ℝ)^2 ≤
      (∑ p ∈ (primeWinnerLabels N).filter (B < ·), (1 : ℝ)/p) *
        primeLoserWeightedOppositeMass N := by
  classical
  let S := primeLocalMinimaAbove B N
  let T := (primeWinnerLabels N).filter (B < ·)
  let d (p : ℕ) := (S.filter fun n => Nat.maxPrimeFac n = p).card
  have hf : (S : Set ℕ).MapsTo Nat.maxPrimeFac T := by
    intro n hn
    change n ∈ (primeLocalMinima N).filter (fun n => B < Nat.maxPrimeFac n) at hn
    obtain ⟨hnmin, hpn⟩ := mem_filter.mp hn
    obtain ⟨hnN, hnpos, _, _⟩ := mem_filter.mp hnmin
    exact mem_filter.mpr ⟨primeWinnerLabels_mono (mem_range.mp hnN).le
      (maxPrimeFac_mem_labels_of_pos n (maxPrimeFac_pos_of_pos n hnpos)), hpn⟩
  have hsum : (∑ p ∈ T, (d p : ℝ)) = S.card := by
    exact_mod_cast (card_eq_sum_card_fiberwise hf).symm
  have hsq : 2 * (∑ p ∈ T, (p : ℝ) * (d p : ℝ)^2) ≤
      primeLoserWeightedOppositeMass N := by
    have he := label_weighted_fiber_square_sum S T Nat.maxPrimeFac
      (fun _ => (1 : ℝ)) (fun p => (p : ℝ)) (fun n hn => hf hn)
    simp only [sum_const, nsmul_eq_mul, mul_one] at he
    rw [he]
    exact twice_localMinima_weighted_same_pair_sum_le_opposite B N
  have hcs := sum_sq_le_sum_mul_sum_of_sq_eq_mul T
    (r := fun p => (d p : ℝ)) (f := fun p => (1 : ℝ)/p)
    (g := fun p => (p : ℝ)*(d p : ℝ)^2)
    (by intros; positivity) (by intros; positivity) (fun p hp => by
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast
        (primeWinnerLabel_pos N p (mem_filter.mp hp).1).ne'
      dsimp only
      field_simp)
  rw [hsum] at hcs
  have hh := mul_le_mul_of_nonneg_left hsq (show 0 ≤ ∑ p ∈ T, (1 : ℝ)/p by positivity)
  change 2 * (S.card : ℝ)^2 ≤ _
  nlinarith

/-- In a positive-power prime range, the improved finite estimate has this
particularly simple form. -/
theorem primeLocalMinimaAbove_power_sq_le_opposite (u : ℝ) (hu : 0 < u)
    (N : ℕ) (hN : 4 ≤ N) :
    u * ((primeLocalMinimaAbove (ceilPowerCutoff u N) N).card : ℝ)^2 ≤
      primeLoserWeightedOppositeMass N := by
  have hO : 0 ≤ primeLoserWeightedOppositeMass N := by
    unfold primeLoserWeightedOppositeMass
    positivity
  have hb := (twice_primeLocalMinimaAbove_sq_le_weightedOpposite
    (ceilPowerCutoff u N) N).trans
      (mul_le_mul_of_nonneg_right (high_primeWinnerLabels_reciprocal_bound u hu N hN) hO)
  have hh := mul_le_mul_of_nonneg_left hb hu.le
  have he : u * ((2/u) * primeLoserWeightedOppositeMass N) =
      2 * primeLoserWeightedOppositeMass N := by field_simp
  rw [he] at hh
  nlinarith

/-- Quantitative conversion of any known local-minimum lower proportion.
The same u,c in the earlier estimate now give twice its lower bound. -/
theorem weightedOpposite_lower_of_power_localMinima (u c : ℝ)
    (hu : 0 < u) (hc : 0 ≤ c)
    (hmin : ∀ᶠ N : ℕ in atTop,
      c ≤ ((primeLocalMinimaAbove (ceilPowerCutoff u N) N).card : ℝ)/N) :
    ∀ᶠ N : ℕ in atTop,
      u*c^2*(N : ℝ)^2 ≤ primeLoserWeightedOppositeMass N ∧
        u*c^2/2 ≤ primeLoserWeightedOppositeRatio N := by
  filter_upwards [hmin, primeLoserWeightedCollisionMass_eventually_lower,
    eventually_ge_atTop (4 : ℕ)] with N hm hQ hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hm' := (le_div_iff₀ hN0).mp hm
  have hs : c^2*(N : ℝ)^2 ≤
      ((primeLocalMinimaAbove (ceilPowerCutoff u N) N).card : ℝ)^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) hm' 2
  have hmass : u*c^2*(N : ℝ)^2 ≤ primeLoserWeightedOppositeMass N := by
    have hh := mul_le_mul_of_nonneg_left hs hu.le
    simpa only [mul_assoc] using hh.trans
      (primeLocalMinimaAbove_power_sq_le_opposite u hu N hN)
  refine ⟨hmass, ?_⟩
  have hQ0 : 0 < primeLoserWeightedCollisionMass N :=
    lt_of_lt_of_le (by positivity) hQ
  unfold primeLoserWeightedOppositeRatio
  apply (le_div_iff₀ hQ0).mpr
  have hh := mul_le_mul_of_nonneg_left (primeLoserWeightedCollisionMass_bound N)
    (show 0 ≤ u*c^2 by positivity)
  nlinarith

/-- Apply the sharper estimate to the previously proved positive mass of
actual prime-factor local minima. The lower fraction is positive, not one half. -/
theorem weightedOpposite_improved_positive_lower :
    ∃ u c : ℝ, 0 < u ∧ 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c ≤ ((primeLocalMinimaAbove (ceilPowerCutoff u N) N).card : ℝ)/N ∧
        u*c^2*(N : ℝ)^2 ≤ primeLoserWeightedOppositeMass N ∧
        u*c^2/2 ≤ primeLoserWeightedOppositeRatio N := by
  obtain ⟨u,c,hu,hc,hmin⟩ := primeLocalMinimaAbove_power_positive_mass
  refine ⟨u,c,hu,hc,?_⟩
  filter_upwards [hmin, weightedOpposite_lower_of_power_localMinima u c hu hc.le hmin]
    with N hm hbound
  exact ⟨hm,hbound⟩

#print axioms weightedOpposite_improved_positive_lower
#print axioms primeLocalMinimaAbove_power_sq_le_opposite
#print axioms weightedOpposite_lower_of_power_localMinima
#print axioms primeLoserWeightedOppositeMass_eq_twice_fallRise
#print axioms twice_localMinima_weighted_same_pair_sum_le_opposite
#print axioms twice_primeLocalMinimaAbove_sq_le_weightedOpposite
end Erdos371
