import Submission.BothLargePrimeLower
import Submission.PrimeLoserCollisionPatterns

/-! A genuine obstruction to extending an unsigned collision bound into a
fixed interior prime range. The actual collision count is superlinear there;
this is not a disproof of comparison balance or of a signed energy bound. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

lemma primeLoser_mem_labels_of_one_lt (N n : ℕ) (hn : n<N) (hp : 1<primeLoser n) :
    primeLoser n ∈ primeWinnerLabels N := by
  have hprime := primeLoser_prime_of_one_lt n hp
  have hpn : primeLoser n ≤ n := (min_le_left _ _).trans (Nat.maxPrimeFac_le (n := n))
  exact mem_insert_of_mem (Nat.mem_primesBelow.mpr ⟨by omega,hprime⟩)

/-- Cauchy--Schwarz in the opposite direction: positive incidence mass on
few prime labels forces many unsigned collisions. -/
lemma bothAbove_card_sq_le_labels_mul_collisions (B N : ℕ) (hB : 1 ≤ B) :
    ((bothAboveSet B N).card : ℝ)^2 ≤
      ((primeWinnerLabels N).card : ℝ)*((bothAboveSet B N).card+(primeLoserCollisions B N).card) := by
  let S := bothAboveSet B N
  let T := primeWinnerLabels N
  let d (p : ℕ) := (S.filter fun n => primeLoser n=p).card
  have hmap : (S : Set ℕ).MapsTo primeLoser T := by
    intro n hn
    change n ∈ bothAboveSet B N at hn
    obtain ⟨hnN,hnB,hnB'⟩ := mem_filter.mp hn
    exact primeLoser_mem_labels_of_one_lt N n (mem_range.mp hnN)
      (lt_of_le_of_lt hB (lt_min hnB hnB'))
  have hsum : (∑ p ∈ T, (d p : ℝ))=S.card := by
    have hh := card_eq_sum_card_fiberwise hmap
    exact_mod_cast hh.symm
  have hsq : (∑ p ∈ T, (d p : ℝ)^2) ≤ S.card+(primeLoserCollisions B N).card := by
    have hh := (sum_card_sq_fibers_le_same_pairs S T primeLoser).trans_eq
      (card_same_pairs_eq_diagonal_add_offDiag S primeLoser)
    exact_mod_cast hh
  have hcs := sum_mul_sq_le_sq_mul_sq T (fun _ => (1 : ℝ)) (fun p => (d p : ℝ))
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one,hsum] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg (α := ℝ) T.card))

lemma bothAbove_ratio_sq_le_labels_ratio (B N : ℕ) (hB : 1 ≤ B) (hN : 0<N) :
    (((bothAboveSet B N).card : ℝ)/N)^2 ≤
      (((primeWinnerLabels N).card : ℝ)/N)*(1+((primeLoserCollisions B N).card : ℝ)/N) := by
  have hN0 : (0 : ℝ)<N := by exact_mod_cast hN
  have hmass : ((bothAboveSet B N).card : ℝ)/N ≤ 1 := by
    apply (div_le_one hN0).mpr
    exact_mod_cast (card_filter_le (range N) (fun n => B<Nat.maxPrimeFac n ∧ B<Nat.maxPrimeFac (n+1))).trans_eq (card_range N)
  have hraw := div_le_div_of_nonneg_right (bothAbove_card_sq_le_labels_mul_collisions B N hB)
    (sq_nonneg (N : ℝ))
  have hprod : (((bothAboveSet B N).card : ℝ)/N)^2 ≤
      (((primeWinnerLabels N).card : ℝ)/N)*
        (((bothAboveSet B N).card : ℝ)/N+((primeLoserCollisions B N).card : ℝ)/N) := by
    convert hraw using 1 <;> field_simp
  exact hprod.trans (mul_le_mul_of_nonneg_left (add_le_add hmass (le_refl _))
    (by positivity))

/-- Any fixed positive proportion of incidences forces a superlinear
unsigned collision count because the available prime labels are sparse. -/
theorem primeLoserCollisions_ratio_tendsto_atTop_of_positive_mass (B : ℕ → ℕ)
    (c : ℝ) (hc : 0<c) (hB : ∀ᶠ N : ℕ in atTop, 1 ≤ B N)
    (hmass : ∀ᶠ N : ℕ in atTop, c ≤ ((bothAboveSet (B N) N).card : ℝ)/N) :
    Tendsto (fun N : ℕ => ((primeLoserCollisions (B N) N).card : ℝ)/N) atTop atTop := by
  apply tendsto_atTop.mpr
  intro R
  have hden : 0 < max R 0+2 := by have := le_max_right R 0; linarith
  have hε : 0 < c^2/(max R 0+2) := div_pos (sq_pos_of_pos hc) hden
  have hsmall := primeWinnerLabels_card_tendsto_zero.eventually_lt_const hε
  filter_upwards [hB,hmass,hsmall,eventually_gt_atTop (0 : ℕ)] with N hBN hm hs hN
  have hprod := bothAbove_ratio_sq_le_labels_ratio (B N) N hBN hN
  have hsmall' : (((primeWinnerLabels N).card : ℝ)/N)*(max R 0+2) < c^2 :=
    (lt_div_iff₀ hden).mp hs
  have hmasssq : c^2 ≤ (((bothAboveSet (B N) N).card : ℝ)/N)^2 :=
    pow_le_pow_left₀ hc.le hm 2
  by_contra hnot
  have hQ : ((primeLoserCollisions (B N) N).card : ℝ)/N < R := lt_of_not_ge hnot
  have hQL : 1+((primeLoserCollisions (B N) N).card : ℝ)/N ≤ max R 0+2 := by
    have := le_max_left R 0
    linarith
  have hle := mul_le_mul_of_nonneg_left hQL
    (show (0 : ℝ) ≤ ((primeWinnerLabels N).card : ℝ)/N by positivity)
  linarith

/-- This divergence concerns the actual largest-prime-factor sequence, in
a range strictly above the square root—not an abstract countermodel. -/
theorem primeLoserCollisions_upperHalf_ratio_tendsto_atTop :
    Tendsto (fun N : ℕ =>
      ((primeLoserCollisions (ceilPowerCutoff (21/40) N) N).card : ℝ)/N) atTop atTop := by
  apply primeLoserCollisions_ratio_tendsto_atTop_of_positive_mass _ (1/20) (by norm_num) _
    bothAbove_upperHalf_positive_proportion
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
  exact (ceilPowerCutoff_data (21/40) (3/4) (by norm_num) (by norm_num) (by norm_num) N hN).1.le

/-- No constant multiple of N bounds these unsigned collisions eventually.
This does not negate any signed energy estimate. -/
theorem no_linear_upperHalf_unsigned_collision_bound :
    ¬∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
      ((primeLoserCollisions (ceilPowerCutoff (21/40) N) N).card : ℝ) ≤ C*N := by
  rintro ⟨C,hC⟩
  have hlarge := primeLoserCollisions_upperHalf_ratio_tendsto_atTop.eventually_gt_atTop C
  obtain ⟨N,hN,hbig,hsmall⟩ := ((eventually_gt_atTop (0 : ℕ)).and (hlarge.and hC)).exists
  have hN0 : (0 : ℝ)<N := by exact_mod_cast hN
  have hh := (div_le_iff₀ hN0).mpr hsmall
  linarith

/-- In this same range, each collision still involves two distinct winners.
Its superlinear growth is not due to repetitions of one prime pair. -/
theorem upperHalf_collisions_distinct_winners_eventually :
    ∀ᶠ N : ℕ in atTop, ∀ n m,
      (n,m) ∈ primeLoserCollisions (ceilPowerCutoff (21/40) N) N → primeWinner n ≠ primeWinner m := by
  filter_upwards [ceilPowerCutoff_upperHalf_product_eventually,eventually_gt_atTop (1 : ℕ)] with N hs hN
  have hB := (ceilPowerCutoff_data (21/40) (3/4) (by norm_num) (by norm_num) (by norm_num) N hN).1.le
  intro n m hnm
  exact primeLoserCollisions_distinct_winners _ _ _ _ hB hs hnm

#print axioms primeLoserCollisions_upperHalf_ratio_tendsto_atTop
#print axioms no_linear_upperHalf_unsigned_collision_bound
#print axioms upperHalf_collisions_distinct_winners_eventually
end Erdos371
