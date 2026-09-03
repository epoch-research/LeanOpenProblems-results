import Submission.RichPowerPrimeBands
import Submission.PrimeAllocationRetention

/-! Small-box suppression for whole-prime-power allocations. All probabilities
are finite normalized sums; no independence between neighboring integers is
asserted. -/
namespace Erdos371.RandomBins
open Finset Filter
open Erdos371.FiniteSieve
open scoped Topology

lemma allocation_avoidance_mass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ℕ) (hK : 0 < K) (T : Finset ι) (c : Fin K) :
    (∑ a ∈ univ.filter (fun a : ι → Fin K => ∀ i ∈ T, a i ≠ c),
      ((K : ℝ)⁻¹)^Fintype.card ι) = (1-1/(K : ℝ))^T.card := by
  classical
  let choices : ι → Finset (Fin K) := fun i => if i ∈ T then univ.erase c else univ
  have he : univ.filter (fun a : ι → Fin K => ∀ i ∈ T, a i ≠ c) = Fintype.piFinset choices := by
    ext a
    simp only [mem_filter,mem_univ,true_and,Fintype.mem_piFinset]
    constructor
    · intro ha i
      dsimp only [choices]
      by_cases hi : i ∈ T
      · simp only [if_pos hi,mem_erase,mem_univ,and_true]
        exact ha i hi
      · simp only [if_neg hi,mem_univ]
    · intro ha i hi
      have hh := ha i
      simpa only [choices,if_pos hi,mem_erase,mem_univ,and_true] using hh
  have hcard (i : ι) : (choices i).card = if i ∈ T then K-1 else K := by
    by_cases hi : i ∈ T <;> simp [choices,hi]
  rw [he,sum_const,nsmul_eq_mul,Fintype.card_piFinset]
  simp_rw [hcard]
  rw [Nat.cast_prod]
  have hi : ((K : ℝ)⁻¹)^Fintype.card ι = ∏ _i : ι, (K : ℝ)⁻¹ := by simp
  rw [hi,← prod_mul_distrib]
  have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  calc
    _ = ∏ i : ι, if i ∈ T then (1-1/(K : ℝ)) else 1 := by
      apply prod_congr rfl
      intro i hi
      by_cases h : i ∈ T
      · simp only [if_pos h,Nat.cast_pred hK]
        field_simp
      · simp only [if_neg h,mul_inv_cancel₀ hK0]
    _ = _ := by rw [prod_ite_mem_eq]; simp

lemma selectedPrimeAtoms_card (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (n : ℕ) (hn : n ≠ 0) :
    ((univ : Finset (PrimeAtomIndex n)).filter fun i => i.val ∈ S).card = primeDivisorCountIn S n := by
  classical
  apply card_bij (fun i _ => i.val)
  · intro i hi
    exact mem_filter.mpr ⟨(mem_filter.mp hi).2,(Nat.mem_primeFactors.mp i.property).2.1⟩
  · intro i hi j hj he
    exact Subtype.ext he
  · intro p hp
    obtain ⟨hp,hpd⟩ := mem_filter.mp hp
    have hpn : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hS p hp,hpd,hn⟩
    exact ⟨⟨p,hpn⟩,mem_filter.mpr ⟨mem_univ _,hp⟩,rfl⟩

lemma primeAllocation_avoidance_weight (K : ℕ) (hK : 0 < K)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (n : ℕ) (hn : n ≠ 0) (c : Fin K) :
    (∑ a ∈ univ.filter (fun a : PrimeAtomIndex n → Fin K =>
        ∀ i : PrimeAtomIndex n, i.val ∈ S → a i ≠ c),
      ∏ d, allocationWeight K (boxProduct (primePowerAtom n) a d)) =
      (1-1/(K : ℝ))^primeDivisorCountIn S n := by
  classical
  have hw (a : PrimeAtomIndex n → Fin K) :
      (∏ d, allocationWeight K (boxProduct (primePowerAtom n) a d)) =
        ((K : ℝ)⁻¹)^Fintype.card (PrimeAtomIndex n) :=
    prod_allocationWeight_boxes K (fun i : PrimeAtomIndex n => i.val)
      (fun i => n.factorization i.val) (primeAtom_prime n) (primeAtom_exponent_pos n)
      Subtype.val_injective a
  simp_rw [hw]
  have hh := allocation_avoidance_mass K hK
    ((univ : Finset (PrimeAtomIndex n)).filter fun i => i.val ∈ S) c
  rw [selectedPrimeAtoms_card S hS n hn] at hh
  simpa only [mem_filter,mem_univ,true_and] using hh

/-- Total normalized weight of allocations having at least one box below Y. -/
noncomputable def smallBoxAllocationMass (K : ℕ) (Y : ℝ) (n : ℕ) : ℝ := by
  classical
  exact ∑ a ∈ univ.filter (fun a : PrimeAtomIndex n → Fin K =>
      ∃ c, (boxProduct (primePowerAtom n) a c : ℝ) < Y),
    ∏ c, allocationWeight K (boxProduct (primePowerAtom n) a c)

lemma smallBoxAllocationMass_nonneg (K : ℕ) (Y : ℝ) (n : ℕ) :
    0 ≤ smallBoxAllocationMass K Y n := by
  apply sum_nonneg
  intro a ha
  apply prod_nonneg
  intro c hc
  unfold allocationWeight
  positivity

/-- A small box contains none of the selected primes if all selected primes
are at least the box lower threshold. -/
lemma small_box_avoids_prime_band (K n : ℕ) (Y : ℝ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, Y ≤ (p : ℝ)) (a : PrimeAtomIndex n → Fin K) (c : Fin K)
    (hc : (boxProduct (primePowerAtom n) a c : ℝ) < Y) :
    ∀ i : PrimeAtomIndex n, i.val ∈ S → a i ≠ c := by
  intro i hi ha
  have hm : i ∈ univ.filter (fun j => a j = c) := mem_filter.mpr ⟨mem_univ _,ha⟩
  have hprod : primePowerAtom n i ≤ boxProduct (primePowerAtom n) a c :=
    single_le_prod' (fun j _ => primePowerAtom_pos n j) hm
  have hp : i.val ≤ primePowerAtom n i := by
    simpa only [primePowerAtom,pow_one] using
      Nat.pow_le_pow_right (primeAtom_prime n i).pos (primeAtom_exponent_pos n i)
  have hr : (i.val : ℝ) ≤ boxProduct (primePowerAtom n) a c := by exact_mod_cast hp.trans hprod
  exact (hS i.val hi).not_gt (hr.trans_lt hc)

/-- A union bound over the K colors, with an exact one-box avoidance mass. -/
theorem smallBoxAllocationMass_prime_count_bound (K : ℕ) (hK : 0 < K)
    (Y : ℝ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ Y ≤ (p : ℝ))
    (n : ℕ) (hn : n ≠ 0) :
    smallBoxAllocationMass K Y n ≤ (K : ℝ)*(1-1/(K : ℝ))^primeDivisorCountIn S n := by
  classical
  let W := fun a : PrimeAtomIndex n → Fin K => ∏ c, allocationWeight K (boxProduct (primePowerAtom n) a c)
  have hW (a : PrimeAtomIndex n → Fin K) : 0 ≤ W a := by
    apply prod_nonneg
    intro c hc
    unfold allocationWeight
    positivity
  have hpoint (a : PrimeAtomIndex n → Fin K) :
      (if ∃ c, (boxProduct (primePowerAtom n) a c : ℝ) < Y then W a else 0) ≤
        ∑ c : Fin K, if ∀ i : PrimeAtomIndex n, i.val ∈ S → a i ≠ c then W a else 0 := by
    split_ifs with h
    · obtain ⟨c,hc⟩ := h
      have hav := small_box_avoids_prime_band K n Y S (fun p hp => (hS p hp).2) a c hc
      have hh := single_le_sum (s := univ)
        (f := fun d : Fin K => if ∀ i : PrimeAtomIndex n, i.val ∈ S → a i ≠ d then W a else 0)
        (fun d hd => by
          dsimp only
          split_ifs
          · exact hW a
          · exact le_rfl) (mem_univ c)
      simpa only [if_pos hav] using hh
    · apply sum_nonneg
      intro c hc
      split_ifs
      · exact hW a
      · exact le_rfl
  have hs := sum_le_sum (s := univ) fun a ha => hpoint a
  rw [sum_comm] at hs
  change (∑ a : PrimeAtomIndex n → Fin K,
    if ∃ c, (boxProduct (primePowerAtom n) a c : ℝ) < Y then W a else 0) ≤ _ at hs
  have he (c : Fin K) : (∑ a : PrimeAtomIndex n → Fin K,
      if ∀ i : PrimeAtomIndex n, i.val ∈ S → a i ≠ c then W a else 0) =
      (1-1/(K : ℝ))^primeDivisorCountIn S n := by
    rw [← sum_filter]
    exact primeAllocation_avoidance_weight K hK S (fun p hp => (hS p hp).1) n hn c
  simp_rw [he] at hs
  simpa only [smallBoxAllocationMass,sum_filter,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,W] using hs

/-- For each fixed K, all box products exceed a sufficiently small positive
power of N outside arbitrarily small mean allocation mass. -/
theorem smallBoxAllocationMass_power_uniform_rarity (K : ℕ) (hK : 0 < K)
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η ≤ α ∧ ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ range N, smallBoxAllocationMass K ((N : ℝ)^η) (n+1))/N < ε := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hr : 0 ≤ 1-1/(K : ℝ) := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hK1
    norm_num at hh
    have hh' : 1/(K : ℝ) ≤ 1 := by simpa only [one_div] using hh
    exact sub_nonneg.mpr hh'
  have hr1 : 1-1/(K : ℝ) < 1 := by
    have hinv : 0 < 1/(K : ℝ) := by positivity
    linarith
  obtain ⟨η,hη,hηα,S,hS⟩ := power_prime_band_suppression α (1-1/(K : ℝ)) hα hα1 hr hr1
    (ε/(K : ℝ)) (by positivity)
  refine ⟨η,hη,hηα,?_⟩
  filter_upwards [hS,eventually_gt_atTop (0 : ℕ)] with N hS hN
  obtain ⟨hpr,hmean⟩ := hS
  have hs := sum_le_sum (s := range N) fun n hn => smallBoxAllocationMass_prime_count_bound K hK
    ((N : ℝ)^η) (S N) (fun p hp => ⟨(hpr p hp).1,(hpr p hp).2.1⟩) (n+1) (by omega)
  rw [← mul_sum] at hs
  have hd := div_le_div_of_nonneg_right hs (Nat.cast_nonneg (α := ℝ) N)
  rw [mul_div_assoc] at hd
  have hm := mul_lt_mul_of_pos_left hmean hKr
  rw [mul_div_cancel₀ _ hKr.ne'] at hm
  exact hd.trans_lt hm

#print axioms allocation_avoidance_mass
#print axioms smallBoxAllocationMass_prime_count_bound
#print axioms smallBoxAllocationMass_power_uniform_rarity
end Erdos371.RandomBins
