import Submission.PrimeWinnerPrimeWeightedEnergy
import Submission.SmallPrimeReflectionDensity

/-! The prime-weighted collision criterion. Its diagonal and endpoint terms
are negligible, so only the weighted signed off-diagonal term remains. -/
namespace Erdos371
open Finset Filter
open scoped Topology

noncomputable def primeLoserPrimeWeightedEnergy (N : ℕ) : ℝ :=
  ∑ p ∈ primeWinnerLabels N, (p : ℝ)*(primeLoserSum p N)^2

noncomputable def primeLoserPrimeWeightedCollisions (N : ℕ) : ℝ :=
  ∑ nm ∈ primeLoserCollisions 0 N, (primeLoser nm.1 : ℝ)*factorSign nm.1*factorSign nm.2

noncomputable def primeLoserPrimeWeightedDiagonal (N : ℕ) : ℝ :=
  ∑ n ∈ bothAboveSet 0 N, (primeLoser n : ℝ)

noncomputable def primeLoserPrimeWeightedEndpoint (N : ℕ) : ℝ :=
  (Nat.maxPrimeFac N : ℝ)*primeLoserEndpointCorrection 0 N

lemma label_weighted_fiber_square_sum {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (f : ι → κ) (a : ι → ℝ) (w : κ → ℝ)
    (hf : ∀ n ∈ s, f n ∈ t) :
    (∑ p ∈ t, w p*(∑ n ∈ s.filter (fun n => f n=p), a n)^2) =
      ∑ nm ∈ (s ×ˢ s).filter (fun nm => f nm.1=f nm.2), w (f nm.1)*a nm.1*a nm.2 := by
  let U := (s ×ˢ s).filter fun nm => f nm.1=f nm.2
  have hrow (p : κ) : w p*(∑ n ∈ s.filter (fun n => f n=p), a n)^2 =
      ∑ nm ∈ U.filter (fun nm => f nm.1=p), w (f nm.1)*a nm.1*a nm.2 := by
    rw [pow_two,sum_mul_sum,← sum_product',mul_sum]
    have he : (s.filter (fun n => f n=p)) ×ˢ (s.filter (fun n => f n=p)) =
        U.filter (fun nm => f nm.1=p) := by
      ext nm
      simp only [U,mem_product,mem_filter]
      aesop
    apply sum_congr he
    intro nm hnm
    have hh := (mem_filter.mp hnm).2
    rw [hh,mul_assoc]
  simp_rw [hrow]
  exact sum_fiberwise_of_maps_to (fun nm hnm =>
    hf nm.1 (mem_product.mp (mem_filter.mp hnm).1).1) _

lemma primeLoserPrimeWeightedEnergy_formula (N : ℕ) :
    primeLoserPrimeWeightedEnergy N = primeLoserPrimeWeightedDiagonal N+
      primeLoserPrimeWeightedCollisions N := by
  let S := bothAboveSet 0 N
  let T := primeWinnerLabels N
  have hf : ∀ n ∈ S, primeLoser n ∈ T := by
    intro n hn
    obtain ⟨hnN,hnB,hnB'⟩ := mem_filter.mp hn
    exact primeLoser_mem_labels_of_pos N n (mem_range.mp hnN) (lt_min hnB hnB')
  have he : primeLoserPrimeWeightedEnergy N =
      ∑ p ∈ T, (p : ℝ)*(∑ n ∈ S.filter (fun n => primeLoser n=p), factorSign n)^2 := by
    apply sum_congr rfl
    intro p hp
    congr 2
    change (∑ n ∈ primeLoserIncidences p N, factorSign n)=_
    rw [primeLoserIncidences_eq_high_filter 0 N p (primeWinnerLabel_pos N p hp)]
  rw [he,label_weighted_fiber_square_sum S T primeLoser factorSign (fun p => (p : ℝ)) hf,
    ← diag_union_offDiag,filter_union,
    sum_union (disjoint_filter_filter (disjoint_diag_offDiag S))]
  congr 1
  rw [filter_true_of_mem (fun nm hnm => congrArg primeLoser (mem_diag.mp hnm).2)]
  simp only [sum_diag,mul_assoc,← pow_two,factorSign_sq,mul_one]
  rfl

lemma primeWinnerPrimeWeightedEnergy_eq_loser_add_endpoint (N : ℕ) :
    primeWinnerPrimeWeightedEnergy N = primeLoserPrimeWeightedEnergy N+
      primeLoserPrimeWeightedEndpoint N := by
  have hrow (p : ℕ) (hp : p ∈ primeWinnerLabels N) :
      (p : ℝ)*(primeWinnerSum p N)^2 = (p : ℝ)*(primeLoserSum p N)^2+
        if Nat.maxPrimeFac N=p then p*(2*primeLoserSum p N+1) else 0 := by
    have hp0 := primeWinnerLabel_pos N p hp
    have h := primeWinnerSum_sub_primeLoserSum p N
    simp only [Nat.maxPrimeFac_zero,if_neg (by omega : ¬0=p),sub_zero] at h
    have he : primeWinnerSum p N = primeLoserSum p N+
        (if Nat.maxPrimeFac N=p then 1 else 0) := by linarith
    rw [he]
    split_ifs <;> ring
  rw [primeWinnerPrimeWeightedEnergy,sum_congr rfl hrow,sum_add_distrib,sum_ite_eq]
  unfold primeLoserPrimeWeightedEnergy primeLoserPrimeWeightedEndpoint primeLoserEndpointCorrection
  congr 1
  by_cases hp : 0<Nat.maxPrimeFac N
  · rw [if_pos hp,if_pos (maxPrimeFac_mem_labels_of_pos N hp)]
  · have hp0 : Nat.maxPrimeFac N=0 := by omega
    have hnmem : Nat.maxPrimeFac N ∉ primeWinnerLabels N := by
      intro h
      exact hp (primeWinnerLabel_pos N _ h)
    simp only [if_neg hnmem,if_neg hp,mul_zero]

/-- Full prime-weighted energy: exact signed collision formula. -/
theorem primeWinnerPrimeWeightedEnergy_collision_formula (N : ℕ) :
    primeWinnerPrimeWeightedEnergy N = primeLoserPrimeWeightedDiagonal N+
      primeLoserPrimeWeightedCollisions N+primeLoserPrimeWeightedEndpoint N := by
  rw [primeWinnerPrimeWeightedEnergy_eq_loser_add_endpoint,primeLoserPrimeWeightedEnergy_formula]

lemma primeLoserPrimeWeightedEndpoint_bound (N : ℕ) :
    ‖primeLoserPrimeWeightedEndpoint N‖ ≤ 9*(N : ℝ) := by
  unfold primeLoserPrimeWeightedEndpoint primeLoserEndpointCorrection
  by_cases hp : 0<Nat.maxPrimeFac N
  · rw [if_pos hp,norm_mul,Real.norm_natCast]
    have hnorm := norm_add_le (2*primeLoserSum (Nat.maxPrimeFac N) N) 1
    rw [norm_mul] at hnorm
    norm_num only [Real.norm_ofNat,norm_one] at hnorm
    have hb := primeLoserSum_norm_le_multiples (Nat.maxPrimeFac N) N hp
    have hdiv : (Nat.maxPrimeFac N : ℝ)*((N/Nat.maxPrimeFac N : ℕ) : ℝ) ≤ N := by
      exact_mod_cast Nat.mul_div_le N (Nat.maxPrimeFac N)
    have hpN : (Nat.maxPrimeFac N : ℝ)≤N := by exact_mod_cast Nat.maxPrimeFac_le (n := N)
    have hmul := mul_le_mul_of_nonneg_left hnorm (Nat.cast_nonneg (α := ℝ) (Nat.maxPrimeFac N))
    have hmul' := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (α := ℝ) (Nat.maxPrimeFac N))
    nlinarith
  · rw [if_neg hp,mul_zero,norm_zero]
    positivity

lemma primeLoserPrimeWeightedEndpoint_tendsto :
    Tendsto (fun N : ℕ => primeLoserPrimeWeightedEndpoint N/(N : ℝ)^2) atTop (nhds 0) := by
  have ht := tendsto_const_div_atTop_nhds_zero_nat (9 : ℝ)
  apply squeeze_zero_norm' _ ht
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hN0 : (N : ℝ)≠0 := by exact_mod_cast hN.ne'
  rw [norm_div,Real.norm_of_nonneg (sq_nonneg _)]
  have h := div_le_div_of_nonneg_right (primeLoserPrimeWeightedEndpoint_bound N) (sq_nonneg (N : ℝ))
  convert h using 1
  field_simp

lemma full_large_primeWinner_count_tendsto_zero (K : ℕ) :
    Tendsto (fun N : ℕ => (((range N).filter fun n => N<K*primeWinner n).card : ℝ)/N)
      atTop (nhds 0) := by
  have ht := (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).add
    (large_primeWinner_count_tendsto_zero K)
  simp only [add_zero] at ht
  apply squeeze_zero (fun _ => by positivity) _ ht
  intro N
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  have hs : (range N).filter (fun n => N<K*primeWinner n) ⊆
      range 2 ∪ (range N).filter (fun n => 1<n ∧ N<K*primeWinner n) := by
    intro n hn
    obtain ⟨hnN,hw⟩ := mem_filter.mp hn
    by_cases hn1 : 1<n
    · exact mem_union_right _ (mem_filter.mpr ⟨hnN,hn1,hw⟩)
    · exact mem_union_left _ (mem_range.mpr (by omega))
  have hh := (card_le_card hs).trans (card_union_le (range 2)
    ((range N).filter (fun n => 1<n ∧ N<K*primeWinner n)))
  simp only [card_range] at hh
  exact_mod_cast hh

lemma primeWinner_sum_div_sq_bound (K N : ℕ) (hK : 0<K) (hN : 0<N) :
    (∑ n ∈ range N, (primeWinner n : ℝ))/(N : ℝ)^2 ≤
      1/(K : ℝ)+(((range N).filter fun n => N<K*primeWinner n).card : ℝ)/N := by
  have hK0 : (0 : ℝ)<K := by exact_mod_cast hK
  have hN0 : (0 : ℝ)<N := by exact_mod_cast hN
  have hterm (n : ℕ) (hn : n ∈ range N) :
      (primeWinner n : ℝ) ≤ (N : ℝ)/K+
        (if N<K*primeWinner n then (N : ℝ) else 0) := by
    have hpN : primeWinner n ≤ N := by
      have hh : primeWinner n≤n+1 := max_le (Nat.maxPrimeFac_le.trans (by omega)) Nat.maxPrimeFac_le
      exact hh.trans (by have := mem_range.mp hn; omega)
    split_ifs with h
    · have hh : (primeWinner n : ℝ)≤N := by exact_mod_cast hpN
      have hnz : (0 : ℝ)≤(N : ℝ)/K := by positivity
      linarith
    · rw [add_zero]
      apply (le_div_iff₀ hK0).mpr
      exact_mod_cast (show primeWinner n*K≤N by simpa only [Nat.mul_comm] using not_lt.mp h)
  have hh := sum_le_sum hterm
  rw [sum_add_distrib] at hh
  simp only [sum_const,card_range,nsmul_eq_mul,← sum_filter] at hh
  have hdiv := div_le_div_of_nonneg_right hh (sq_nonneg (N : ℝ))
  convert hdiv using 1
  field_simp

/-- Largest-prime-factor labels are o(N) in mean, after normalization by N.
Only one-dimensional sparsity is used here. -/
theorem primeWinner_sum_div_sq_tendsto_zero :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, (primeWinner n : ℝ))/(N : ℝ)^2)
      atTop (nhds 0) := by
  apply tendsto_order.mpr
  constructor
  · intro ε hε
    exact Eventually.of_forall fun N => hε.trans_le (by positivity)
  · intro ε hε
    obtain ⟨K,hK⟩ := exists_nat_gt (max 0 (2/ε))
    have hK0 : (0 : ℝ)<K := (le_max_left _ _).trans_lt hK
    have hKnat : 0<K := by exact_mod_cast hK0
    have hsmall : 1/(K : ℝ)<ε/2 := by
      have hh := (le_max_right _ _).trans_lt hK
      have hh' := (div_lt_iff₀ hε).mp hh
      apply (div_lt_iff₀ hK0).mpr
      nlinarith
    filter_upwards [(full_large_primeWinner_count_tendsto_zero K).eventually_lt_const
      (half_pos hε),eventually_gt_atTop (0 : ℕ)] with N he hN
    exact (primeWinner_sum_div_sq_bound K N hKnat hN).trans_lt (by linarith)

lemma primeLoserPrimeWeightedDiagonal_tendsto_zero :
    Tendsto (fun N : ℕ => primeLoserPrimeWeightedDiagonal N/(N : ℝ)^2) atTop (nhds 0) := by
  apply squeeze_zero (fun _ => by unfold primeLoserPrimeWeightedDiagonal; positivity) _
    primeWinner_sum_div_sq_tendsto_zero
  intro N
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  calc
    _ ≤ ∑ n ∈ bothAboveSet 0 N, (primeWinner n : ℝ) :=
      sum_le_sum fun n _ => by exact_mod_cast (primeLoser_lt_primeWinner n).le
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)

/-- The weighted energy limit is exactly the weighted signed collision limit:
the diagonal and endpoint have both been proved negligible. -/
theorem primeWeightedEnergy_tendsto_iff_weightedSignedCollisions :
    Tendsto (fun N : ℕ => primeWinnerPrimeWeightedEnergy N/(N : ℝ)^2) atTop (nhds 0) ↔
      Tendsto (fun N : ℕ => primeLoserPrimeWeightedCollisions N/(N : ℝ)^2) atTop (nhds 0) := by
  have hdiag := primeLoserPrimeWeightedDiagonal_tendsto_zero
  have hend := primeLoserPrimeWeightedEndpoint_tendsto
  constructor
  · intro h
    have ht := (h.sub hdiag).sub hend
    simp only [sub_zero] at ht
    convert ht using 1
    ext N
    rw [primeWinnerPrimeWeightedEnergy_collision_formula]
    ring
  · intro h
    have ht := (hdiag.add h).add hend
    simp only [add_zero] at ht
    convert ht using 1
    ext N
    rw [primeWinnerPrimeWeightedEnergy_collision_formula]
    ring

/-- A purely off-diagonal weighted signed criterion for the ORIGINAL target.
Its cancellation hypothesis remains unproved. -/
theorem density_of_primeWeightedSignedCollisions
    (h : Tendsto (fun N : ℕ => primeLoserPrimeWeightedCollisions N/(N : ℝ)^2)
      atTop (nhds 0)) :
    {n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.HasDensity (1/2) :=
  density_of_primeWeightedEnergy (primeWeightedEnergy_tendsto_iff_weightedSignedCollisions.mpr h)

#print axioms primeWinnerPrimeWeightedEnergy_collision_formula
#print axioms primeWinner_sum_div_sq_tendsto_zero
#print axioms primeWeightedEnergy_tendsto_iff_weightedSignedCollisions
#print axioms density_of_primeWeightedSignedCollisions
end Erdos371
