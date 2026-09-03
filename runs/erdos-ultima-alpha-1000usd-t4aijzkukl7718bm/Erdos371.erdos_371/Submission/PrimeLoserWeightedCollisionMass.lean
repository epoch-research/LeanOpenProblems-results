import Submission.PrimeLoserPrimeWeightedCollisions

/-! The prime-weighted unsigned collision mass is of quadratic order. This
makes a relative signed-cancellation hypothesis sufficient, without the
polynomial precision required by the earlier unweighted energy criterion. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

noncomputable def primeLoserWeightedCollisionMass (N : ℕ) : ℝ :=
  ∑ nm ∈ primeLoserCollisions 0 N, (primeLoser nm.1 : ℝ)

noncomputable def primeLoserWeightedOppositeMass (N : ℕ) : ℝ :=
  ∑ nm ∈ primeLoserOppositeCollisions 0 N, (primeLoser nm.1 : ℝ)

lemma primeLoserPrimeWeightedCollisions_eq_mass_sub_twice_opposite (N : ℕ) :
    primeLoserPrimeWeightedCollisions N = primeLoserWeightedCollisionMass N-
      2*primeLoserWeightedOppositeMass N := by
  unfold primeLoserPrimeWeightedCollisions primeLoserWeightedCollisionMass
    primeLoserWeightedOppositeMass primeLoserOppositeCollisions
  rw [sum_filter]
  rw [mul_sum,← sum_sub_distrib]
  apply sum_congr rfl
  intro nm hnm
  rw [mul_assoc,factorSign_product_eq]
  by_cases h : factorSign nm.1=factorSign nm.2 <;> simp [h]
  ring

lemma primeLoserIncidences_card_le_twice_div (p N : ℕ) (hp : 0<p) :
    (primeLoserIncidences p N).card ≤ 2*(N/p) := by
  let L := (range (N+1)).filter fun n => n≠0 ∧ p ∣ n
  let R := (range N).filter fun n => p ∣ n+1
  have hs : primeLoserIncidences p N ⊆ L ∪ R := by
    intro n hn
    obtain ⟨hnN,he⟩ := mem_filter.mp hn
    have hn0 : n≠0 := by
      rintro rfl
      simp only [primeLoser,Nat.maxPrimeFac_zero,Nat.zero_add,Nat.maxPrimeFac_one,
        min_eq_left (by omega : 0≤1)] at he
      omega
    rcases primeLabel_pair_cases n with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_range.mpr
        (by have := mem_range.mp hnN; omega),hn0,by
          rw [← he,← ha]
          exact Nat.maxPrimeFac_dvd⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hnN,by
        rw [← he,← hb]
        exact Nat.maxPrimeFac_dvd⟩)
  have hh := (card_le_card hs).trans (card_union_le L R)
  simpa only [L,R,Nat.card_multiples',Nat.card_multiples,two_mul] using hh

lemma primeLoser_weighted_degree_le (p N : ℕ) (hp : 0<p) :
    (p : ℝ)*(primeLoserIncidences p N).card ≤ 2*N := by
  have h := primeLoserIncidences_card_le_twice_div p N hp
  have hd := Nat.mul_div_le N p
  have hh : p*(primeLoserIncidences p N).card ≤ 2*N := by nlinarith
  exact_mod_cast hh

lemma primeLoser_unsigned_weighted_second_moment (N : ℕ) :
    (∑ p ∈ primeWinnerLabels N, (p : ℝ)*((primeLoserIncidences p N).card : ℝ)^2) =
      primeLoserPrimeWeightedDiagonal N+primeLoserWeightedCollisionMass N := by
  let S := bothAboveSet 0 N
  let T := primeWinnerLabels N
  have hf : ∀ n ∈ S, primeLoser n ∈ T := by
    intro n hn
    obtain ⟨hnN,hp,hp'⟩ := mem_filter.mp hn
    exact primeLoser_mem_labels_of_pos N n (mem_range.mp hnN) (lt_min hp hp')
  have he : (∑ p ∈ T, (p : ℝ)*((primeLoserIncidences p N).card : ℝ)^2) =
      ∑ p ∈ T, (p : ℝ)*(∑ n ∈ S.filter (fun n => primeLoser n=p), (1 : ℝ))^2 := by
    apply sum_congr rfl
    intro p hp
    rw [primeLoserIncidences_eq_high_filter 0 N p (primeWinnerLabel_pos N p hp)]
    simp only [sum_const,nsmul_eq_mul,mul_one]
    rfl
  rw [he,label_weighted_fiber_square_sum S T primeLoser (fun _ => 1) (fun p => (p : ℝ)) hf,
    ← diag_union_offDiag,filter_union,
    sum_union (disjoint_filter_filter (disjoint_diag_offDiag S))]
  simp only [mul_one]
  congr 1
  rw [filter_true_of_mem (fun nm hnm => congrArg primeLoser (mem_diag.mp hnm).2),sum_diag]
  rfl

/-- Unlike the unweighted collision count, the prime-weighted mass is at most
2*N^2. No cancellation is used in this bound. -/
theorem primeLoserWeightedCollisionMass_bound (N : ℕ) :
    primeLoserWeightedCollisionMass N ≤ 2*(N : ℝ)^2 := by
  have hsum : (∑ p ∈ primeWinnerLabels N, ((primeLoserIncidences p N).card : ℝ)) ≤ N := by
    have hh := sum_card_fiberwise_eq_card_filter (range N) (primeWinnerLabels N) primeLoser
    have hc := (card_filter_le (range N) (fun n => primeLoser n ∈ primeWinnerLabels N)).trans_eq (card_range N)
    rw [← hh] at hc
    exact_mod_cast hc
  have hrow (p : ℕ) (hp : p ∈ primeWinnerLabels N) :
      (p : ℝ)*((primeLoserIncidences p N).card : ℝ)^2 ≤
        2*N*(primeLoserIncidences p N).card := by
    have hh := mul_le_mul_of_nonneg_right (primeLoser_weighted_degree_le p N (primeWinnerLabel_pos N p hp))
      (Nat.cast_nonneg (α := ℝ) (primeLoserIncidences p N).card)
    simpa only [mul_assoc,← pow_two] using hh
  have hs := sum_le_sum hrow
  rw [primeLoser_unsigned_weighted_second_moment,← mul_sum] at hs
  have hm := mul_le_mul_of_nonneg_left hsum (show (0 : ℝ)≤2*N by positivity)
  have hdiag : 0≤primeLoserPrimeWeightedDiagonal N := by unfold primeLoserPrimeWeightedDiagonal; positivity
  nlinarith

lemma bothAbove_card_sq_le_weighted_second_moment (B N : ℕ) :
    ((bothAboveSet B N).card : ℝ)^2 ≤
      (∑ p ∈ (primeWinnerLabels N).filter (B < ·), (1 : ℝ)/p)*
        (primeLoserPrimeWeightedDiagonal N+primeLoserWeightedCollisionMass N) := by
  let S := bothAboveSet B N
  let T := (primeWinnerLabels N).filter (B < ·)
  let d (p : ℕ) := (primeLoserIncidences p N).card
  have hf : (S : Set ℕ).MapsTo primeLoser T := by
    intro n hn
    change n ∈ bothAboveSet B N at hn
    obtain ⟨hnN,hp,hp'⟩ := mem_filter.mp hn
    have hpl : B<primeLoser n := lt_min hp hp'
    exact mem_filter.mpr ⟨primeLoser_mem_labels_of_pos N n (mem_range.mp hnN) (by omega),hpl⟩
  have hsum : (∑ p ∈ T, (d p : ℝ))=S.card := by
    have he : (∑ p ∈ T, (d p : ℝ)) =
        ∑ p ∈ T, (((S.filter fun n => primeLoser n=p).card : ℝ)) := by
      apply sum_congr rfl
      intro p hp
      dsimp only [d]
      rw [primeLoserIncidences_eq_high_filter B N p (mem_filter.mp hp).2]
    rw [he]
    exact_mod_cast (card_eq_sum_card_fiberwise hf).symm
  have hcs := sum_sq_le_sum_mul_sum_of_sq_eq_mul T
    (r := fun p => (d p : ℝ)) (f := fun p => (1 : ℝ)/p)
    (g := fun p => (p : ℝ)*(d p : ℝ)^2)
    (by intros; positivity) (by intros; positivity) (fun p hp => by
      have hp0 : (p : ℝ)≠0 := by exact_mod_cast
        (primeWinnerLabel_pos N p (mem_filter.mp hp).1).ne'
      dsimp only
      field_simp)
  rw [hsum] at hcs
  have he : (∑ p ∈ T, (p : ℝ)*(d p : ℝ)^2) ≤
      primeLoserPrimeWeightedDiagonal N+primeLoserWeightedCollisionMass N := by
    rw [← primeLoser_unsigned_weighted_second_moment]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)
  exact hcs.trans (mul_le_mul_of_nonneg_left he (by positivity))

/-- Positive incidence mass in the upper-half range already forces a fixed
positive quadratic lower bound for the full weighted collision mass. -/
theorem primeLoserWeightedCollisionMass_eventually_lower :
    ∀ᶠ N : ℕ in atTop, (1/3200 : ℝ)*(N : ℝ)^2 ≤ primeLoserWeightedCollisionMass N := by
  have hdiag := primeLoserPrimeWeightedDiagonal_tendsto_zero.eventually_lt_const
    (by norm_num : (0 : ℝ)<1/3200)
  filter_upwards [bothAbove_upperHalf_positive_proportion,hdiag,eventually_ge_atTop (4 : ℕ)]
    with N hm hd hN
  have hN0 : (0 : ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hm' := (le_div_iff₀ hN0).mp hm
  have hs : (N : ℝ)^2/400 ≤ ((bothAboveSet (ceilPowerCutoff (21/40) N) N).card : ℝ)^2 := by
    nlinarith [sq_nonneg (((bothAboveSet (ceilPowerCutoff (21/40) N) N).card : ℝ)-N/20)]
  have hH := high_primeWinnerLabels_reciprocal_bound (21/40) (by norm_num) N hN
  have hH4 : (∑ p ∈ (primeWinnerLabels N).filter (ceilPowerCutoff (21/40) N < ·), (1 : ℝ)/p) ≤ 4 := by
    linarith
  have hraw := (bothAbove_card_sq_le_weighted_second_moment (ceilPowerCutoff (21/40) N) N).trans
    (mul_le_mul_of_nonneg_right hH4 (by
      unfold primeLoserPrimeWeightedDiagonal primeLoserWeightedCollisionMass
      positivity))
  have hd' := (div_lt_iff₀ (sq_pos_of_pos hN0)).mp hd
  nlinarith

#print axioms primeLoserIncidences_card_le_twice_div
#print axioms primeLoserWeightedCollisionMass_bound
#print axioms primeLoserWeightedCollisionMass_eventually_lower
end Erdos371
