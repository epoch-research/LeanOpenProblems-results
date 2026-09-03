import Submission.PrimeLoserCollisionGrowth
import Submission.PrimeWinnerEnergyIncrement

/-! Exact signed collision identities. These keep the off-diagonal signs;
no estimate for their cancellation is assumed. -/
namespace Erdos371
open Finset Filter
open scoped Topology

noncomputable def primeLoserEnergyAbove (B N : ℕ) : ℝ :=
  ∑ p ∈ (primeWinnerLabels N).filter (B < ·), (primeLoserSum p N)^2

noncomputable def primeLoserSignedCollisions (B N : ℕ) : ℝ :=
  ∑ nm ∈ primeLoserCollisions B N, factorSign nm.1 * factorSign nm.2

noncomputable def primeLoserOppositeCollisions (B N : ℕ) : Finset (ℕ × ℕ) :=
  (primeLoserCollisions B N).filter fun nm => factorSign nm.1 ≠ factorSign nm.2

lemma primeLoser_mem_labels_of_pos (N n : ℕ) (hn : n<N) (hp : 0<primeLoser n) :
    primeLoser n ∈ primeWinnerLabels N := by
  by_cases h : primeLoser n=1
  · simp [h,primeWinnerLabels]
  · exact primeLoser_mem_labels_of_one_lt N n hn (by omega)

lemma maxPrimeFac_mem_labels_of_pos (N : ℕ) (hp : 0<Nat.maxPrimeFac N) :
    Nat.maxPrimeFac N ∈ primeWinnerLabels N := by
  by_cases h : N=0
  · simp [h] at hp
  by_cases h1 : N=1
  · simp [h1,primeWinnerLabels]
  · apply mem_insert_of_mem
    exact Nat.mem_primesBelow.mpr ⟨by have := Nat.maxPrimeFac_le (n := N); omega,
      Nat.prime_maxPrimeFac_of_one_lt N (by omega)⟩

lemma weighted_fiber_square_sum {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (f : ι → κ) (a : ι → ℝ)
    (hf : ∀ n ∈ s, f n ∈ t) :
    (∑ p ∈ t, (∑ n ∈ s.filter (fun n => f n=p), a n)^2) =
      ∑ nm ∈ (s ×ˢ s).filter (fun nm => f nm.1=f nm.2), a nm.1*a nm.2 := by
  let U := (s ×ˢ s).filter fun nm => f nm.1=f nm.2
  have hrow (p : κ) : (∑ n ∈ s.filter (fun n => f n=p), a n)^2 =
      ∑ nm ∈ U.filter (fun nm => f nm.1=p), a nm.1*a nm.2 := by
    rw [pow_two, sum_mul_sum, ← sum_product']
    apply sum_congr _ (by intros; rfl)
    ext nm
    simp only [U,mem_product,mem_filter]
    aesop
  simp_rw [hrow]
  exact sum_fiberwise_of_maps_to (fun nm hnm =>
    hf nm.1 (mem_product.mp (mem_filter.mp hnm).1).1) _

/-- Squaring the signed prime-loser sums gives exactly the diagonal incidence
mass and the signed, ordered off-diagonal collisions. -/
theorem primeLoserEnergyAbove_signed_formula (B N : ℕ) :
    primeLoserEnergyAbove B N =
      (bothAboveSet B N).card + primeLoserSignedCollisions B N := by
  let S := bothAboveSet B N
  let T := (primeWinnerLabels N).filter (B < ·)
  have hf : ∀ n ∈ S, primeLoser n ∈ T := by
    intro n hn
    obtain ⟨hnN,hnB,hnB'⟩ := mem_filter.mp hn
    have hp : B < primeLoser n := lt_min hnB hnB'
    exact mem_filter.mpr ⟨primeLoser_mem_labels_of_pos N n (mem_range.mp hnN)
      (by omega), hp⟩
  have he : primeLoserEnergyAbove B N =
      ∑ p ∈ T, (∑ n ∈ S.filter (fun n => primeLoser n=p), factorSign n)^2 := by
    apply sum_congr rfl
    intro p hp
    congr 1
    change (∑ n ∈ primeLoserIncidences p N, factorSign n)=_
    rw [primeLoserIncidences_eq_high_filter B N p (mem_filter.mp hp).2]
  rw [he, weighted_fiber_square_sum S T primeLoser factorSign hf,
    ← diag_union_offDiag, filter_union,
    sum_union (disjoint_filter_filter (disjoint_diag_offDiag S))]
  congr 1
  rw [filter_true_of_mem (fun nm hnm => congrArg primeLoser (mem_diag.mp hnm).2)]
  simp only [sum_diag, ← pow_two, factorSign_sq, sum_const, nsmul_eq_mul, mul_one]
  rfl

lemma factorSign_product_eq (n m : ℕ) :
    factorSign n*factorSign m = if factorSign n=factorSign m then 1 else -1 := by
  unfold factorSign predicateSign
  split_ifs <;> norm_num at *

/-- Opposite signs count negatively, with their full multiplicity retained. -/
theorem primeLoserSignedCollisions_eq_card_sub_twice_opposite (B N : ℕ) :
    primeLoserSignedCollisions B N = (primeLoserCollisions B N).card -
      2*((primeLoserOppositeCollisions B N).card : ℝ) := by
  unfold primeLoserSignedCollisions primeLoserOppositeCollisions
  simp_rw [factorSign_product_eq]
  have he (nm : ℕ × ℕ) :
      (if factorSign nm.1=factorSign nm.2 then (1 : ℝ) else -1) =
        1-2*(if factorSign nm.1 ≠ factorSign nm.2 then 1 else 0) := by
    by_cases h : factorSign nm.1=factorSign nm.2 <;> norm_num [h]
  simp_rw [he, sum_sub_distrib, ← mul_sum]
  rw [sum_boole]
  simp

noncomputable def primeLoserEndpointCorrection (B N : ℕ) : ℝ :=
  if B < Nat.maxPrimeFac N then 2*primeLoserSum (Nat.maxPrimeFac N) N+1 else 0

/-- The high winner and loser energies differ at only the final prime label. -/
theorem primeWinnerEnergyAbove_eq_loser_add_endpoint (B N : ℕ) :
    primeWinnerEnergyAbove B N =
      primeLoserEnergyAbove B N + primeLoserEndpointCorrection B N := by
  let T := (primeWinnerLabels N).filter (B < ·)
  have hrow (p : ℕ) (hp : p ∈ T) :
      (primeWinnerSum p N)^2 = (primeLoserSum p N)^2 +
        if Nat.maxPrimeFac N=p then 2*primeLoserSum p N+1 else 0 := by
    have hp0 : 0<p := by have := (mem_filter.mp hp).2; omega
    have h := primeWinnerSum_sub_primeLoserSum p N
    simp only [Nat.maxPrimeFac_zero, if_neg (by omega : ¬0=p), sub_zero] at h
    have he : primeWinnerSum p N = primeLoserSum p N +
        (if Nat.maxPrimeFac N=p then 1 else 0) := by linarith
    rw [he]
    split_ifs <;> ring
  have he : primeWinnerEnergyAbove B N = primeLoserEnergyAbove B N +
      ∑ p ∈ T, if Nat.maxPrimeFac N=p then 2*primeLoserSum p N+1 else 0 := by
    change (∑ p ∈ T, (primeWinnerSum p N)^2)=_
    rw [sum_congr rfl hrow,sum_add_distrib]
    rfl
  rw [he, sum_ite_eq]
  unfold primeLoserEndpointCorrection
  congr 1
  by_cases hp : B < Nat.maxPrimeFac N
  · rw [if_pos hp, if_pos (mem_filter.mpr
      ⟨maxPrimeFac_mem_labels_of_pos N (by omega),hp⟩)]
  · rw [if_neg hp, if_neg (by intro h; exact hp (mem_filter.mp h).2)]

/-- The exact energy identity, rather than the unsigned upper bound. -/
theorem primeWinnerEnergyAbove_signed_collision_formula (B N : ℕ) :
    primeWinnerEnergyAbove B N = (bothAboveSet B N).card +
      primeLoserSignedCollisions B N + primeLoserEndpointCorrection B N := by
  rw [primeWinnerEnergyAbove_eq_loser_add_endpoint, primeLoserEnergyAbove_signed_formula]

lemma primeLoserSum_norm_le_multiples (p N : ℕ) (hp : 0<p) :
    ‖primeLoserSum p N‖ ≤ 2*((N/p : ℕ) : ℝ)+2 := by
  have h := primeWinnerSum_sub_primeLoserSum p N
  simp only [Nat.maxPrimeFac_zero, if_neg (by omega : ¬0=p), sub_zero] at h
  have he : primeLoserSum p N = primeWinnerSum p N-
      (if Nat.maxPrimeFac N=p then 1 else 0) := by linarith
  rw [he]
  have he1 : ‖(if Nat.maxPrimeFac N=p then (1 : ℝ) else 0)‖ ≤ 1 := by
    split_ifs <;> norm_num
  have hn := norm_sub_le (primeWinnerSum p N)
    (if Nat.maxPrimeFac N=p then (1 : ℝ) else 0)
  have hw := primeWinnerSum_norm_le_multiples p N
  linarith

lemma primeLoserEndpointCorrection_bound (B N : ℕ) :
    ‖primeLoserEndpointCorrection B N‖ ≤ 4*(N : ℝ)/(B+1)+5 := by
  unfold primeLoserEndpointCorrection
  by_cases hp : B<Nat.maxPrimeFac N
  · rw [if_pos hp]
    have hnorm := norm_add_le (2*primeLoserSum (Nat.maxPrimeFac N) N) 1
    rw [norm_mul] at hnorm
    norm_num only [Real.norm_ofNat, norm_one] at hnorm
    have hb := primeLoserSum_norm_le_multiples (Nat.maxPrimeFac N) N (by omega)
    have hdiv : ((N/Nat.maxPrimeFac N : ℕ) : ℝ) ≤ (N : ℝ)/(B+1) := by
      apply (Nat.cast_div_le (α := ℝ)).trans
      apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
      exact_mod_cast (show B+1 ≤ Nat.maxPrimeFac N by omega)
    rw [mul_div_assoc]
    linarith
  · rw [if_neg hp, norm_zero]
    positivity

/-- At any diverging cutoff, the single endpoint correction is negligible
on the scale N, independently of the unknown signed collision estimate. -/
theorem primeLoserEndpointCorrection_ratio_tendsto (B : ℕ → ℕ)
    (hB : Tendsto B atTop atTop) :
    Tendsto (fun N : ℕ => primeLoserEndpointCorrection (B N) N/N) atTop (nhds 0) := by
  have ht : Tendsto (fun N : ℕ => (4 : ℝ)/((B N : ℝ)+1)+5/(N : ℝ))
      atTop (nhds 0) := by
    have hb : Tendsto (fun N : ℕ => (B N : ℝ)+1) atTop atTop :=
      tendsto_atTop_mono (fun _ => le_add_of_nonneg_right (by norm_num))
        (tendsto_natCast_atTop_atTop.comp hB)
    simpa only [add_zero] using
      ((tendsto_const_nhds (x := (4 : ℝ))).div_atTop hb).add
      ((tendsto_const_nhds (x := (5 : ℝ))).div_atTop tendsto_natCast_atTop_atTop)
  apply squeeze_zero_norm' _ ht
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hN0 : (0 : ℝ)<N := by exact_mod_cast hN
  have h := div_le_div_of_nonneg_right (primeLoserEndpointCorrection_bound (B N) N) hN0.le
  rw [norm_div,Real.norm_natCast]
  convert h using 1
  field_simp

/-- A finite, exact criterion for a given high-label energy bound. -/
theorem primeWinnerEnergyAbove_le_iff_signed_collisions (B N : ℕ) (R : ℝ) :
    primeWinnerEnergyAbove B N ≤ R ↔
      primeLoserSignedCollisions B N ≤ R-(bothAboveSet B N).card-
        primeLoserEndpointCorrection B N := by
  rw [primeWinnerEnergyAbove_signed_collision_formula]
  constructor <;> intro h <;> linarith

/-- Positivity of a square bounds the negative part of the signed collisions.
It gives no upper bound for the positive part that would prove balance. -/
lemma primeLoserSignedCollisions_lower (B N : ℕ) :
    -((bothAboveSet B N).card : ℝ) ≤ primeLoserSignedCollisions B N := by
  have h : 0 ≤ primeLoserEnergyAbove B N := by
    unfold primeLoserEnergyAbove
    exact sum_nonneg fun _ _ => sq_nonneg _
  rw [primeLoserEnergyAbove_signed_formula] at h
  linarith

lemma twice_opposite_collisions_le_total_add_mass (B N : ℕ) :
    2*((primeLoserOppositeCollisions B N).card : ℝ) ≤
      (primeLoserCollisions B N).card+(bothAboveSet B N).card := by
  have h := primeLoserSignedCollisions_lower B N
  rw [primeLoserSignedCollisions_eq_card_sub_twice_opposite] at h
  linarith

#print axioms primeLoserEnergyAbove_signed_formula
#print axioms primeLoserSignedCollisions_eq_card_sub_twice_opposite
#print axioms primeWinnerEnergyAbove_signed_collision_formula
#print axioms primeLoserEndpointCorrection_ratio_tendsto
#print axioms primeWinnerEnergyAbove_le_iff_signed_collisions
#print axioms twice_opposite_collisions_le_total_add_mass
end Erdos371
