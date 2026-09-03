import Submission.LogGrowingPrimeCofactorCurrents

/-! For almost all primes, a growing initial run of their multiples has
neighbors whose largest prime factors are smaller than the prime. This is
stronger than zero current on that run, but still a boundary phenomenon. -/
namespace Erdos371
open Finset Filter FiniteSieve DilationSpectrum
open scoped Topology

lemma dyadicPrimeBand_nat_data {X p : ℕ} (hp : p ∈ narrowPrimeBand 1 2 X) :
    p.Prime ∧ X < p ∧ p ≤ 2*X := by
  have hprime : p.Prime := (mem_filter.mp (mem_sdiff.mp hp).1).2
  obtain ⟨hl,hu⟩ := narrowPrimeBand_member_bounds 1 2 X p hp
  simp only [one_mul] at hl
  have hl' : X < p := by exact_mod_cast hl
  change p ≤ ⌊(2 : ℝ)*(X : ℝ)⌋₊ at hu
  rw [show (2 : ℝ)*X = ((2*X : ℕ) : ℝ) by push_cast; rfl,Nat.floor_natCast] at hu
  exact ⟨hprime,hl',hu⟩

noncomputable def roughNeighborPrimes (K X : ℕ) : Finset ℕ :=
  (narrowPrimeBand 1 2 X).filter fun p => ∃ k ≤ K, 1 ≤ k ∧
    (p < Nat.maxPrimeFac (k*p-1) ∨ p < Nat.maxPrimeFac (k*p+1))

private lemma mul_cofactor_max (p k : ℕ) (hp : p.Prime) (hk : 0 < k) (hkp : k ≤ p) :
    Nat.maxPrimeFac (k*p) = p := by
  rw [Nat.maxPrimeFac_mul hk.ne' hp.ne_zero,hp.maxPrimeFac_eq_self]
  exact max_eq_right (Nat.maxPrimeFac_le.trans hkp)

lemma roughNeighborPrimes_subset_loser_image (K X : ℕ) (hX : 0 < X) (hK : K ≤ X) :
    roughNeighborPrimes K X ⊆ (bothAboveSet X ((2*K+1)*X)).image primeLoser := by
  classical
  intro p hp
  obtain ⟨hpband,k,hkK,hk1,hn⟩ := mem_filter.mp hp
  obtain ⟨hprime,hpX,hpupper⟩ := dyadicPrimeBand_nat_data hpband
  have hkp : Nat.maxPrimeFac (k*p) = p :=
    mul_cofactor_max p k hprime (by omega) (by omega)
  have he : k*p-1+1 = k*p := Nat.sub_add_cancel (by nlinarith [hprime.pos])
  have hprod := Nat.mul_le_mul hkK hpupper
  rcases hn with hn | hn
  · apply mem_image.mpr
    refine ⟨k*p-1,mem_filter.mpr ⟨mem_range.mpr (by nlinarith),?_⟩,?_⟩
    · rw [he,hkp]
      exact ⟨hpX.trans hn,hpX⟩
    · simp only [primeLoser,he,hkp,min_eq_right hn.le]
  · apply mem_image.mpr
    refine ⟨k*p,mem_filter.mpr ⟨mem_range.mpr (by nlinarith),?_⟩,?_⟩
    · rw [hkp]
      exact ⟨hpX,hpX.trans hn⟩
    · simp only [primeLoser,hkp,min_eq_left hn.le]

lemma roughNeighborPrimes_card_le (K X : ℕ) (hX : 0 < X) (hK : K ≤ X) :
    (roughNeighborPrimes K X).card ≤ (bothAboveSet X ((2*K+1)*X)).card :=
  (card_le_card (roughNeighborPrimes_subset_loser_image K X hX hK)).trans card_image_le

lemma smooth_neighbors_of_not_mem_roughNeighborPrimes (K X p : ℕ) (hK : K ≤ X)
    (hp : p ∈ narrowPrimeBand 1 2 X) (hnot : p ∉ roughNeighborPrimes K X) :
    ∀ k ∈ Icc 1 K, Nat.maxPrimeFac (k*p-1) < p ∧ Nat.maxPrimeFac (k*p+1) < p := by
  classical
  intro k hk
  obtain ⟨hprime,hpX,_⟩ := dyadicPrimeBand_nat_data hp
  obtain ⟨hk1,hkK⟩ := mem_Icc.mp hk
  have hn : ¬(p < Nat.maxPrimeFac (k*p-1) ∨ p < Nat.maxPrimeFac (k*p+1)) := by
    intro h
    exact hnot (mem_filter.mpr ⟨hp,k,hkK,hk1,h⟩)
  have hkp : Nat.maxPrimeFac (k*p) = p :=
    mul_cofactor_max p k hprime (by omega) (by omega)
  have he : k*p-1+1 = k*p := Nat.sub_add_cancel (by nlinarith [hprime.pos])
  have hl := consecutive_maxPrimeFac_ne (k*p-1)
  have hr := consecutive_maxPrimeFac_ne (k*p)
  rw [he,hkp] at hl
  rw [hkp] at hr
  exact ⟨lt_of_le_of_ne (not_lt.mp (fun h => hn (Or.inl h))) hl.symm,
    lt_of_le_of_ne (not_lt.mp (fun h => hn (Or.inr h))) hr⟩

lemma logPowerCofactorCutoff_eventually_le_endpoint (a : ℝ) :
    ∀ᶠ X : ℕ in atTop, logPowerCofactorCutoff a X ≤ X := by
  have ht : Tendsto (fun X : ℕ => (Real.log X)^a/(X : ℝ)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using log_nat_rpow_div_rpow_tendsto_zero a 1 (by norm_num)
  filter_upwards [ht.eventually_le_const (by norm_num : (0 : ℝ) < 1),
    eventually_gt_atTop (0 : ℕ)] with X hsmall hX
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hw : (Real.log X)^a ≤ X := by
    simpa only [one_mul] using (div_le_iff₀ hX0).mp hsmall
  have hf : (logPowerCofactorCutoff a X : ℝ) ≤ (Real.log X)^a :=
    Nat.floor_le (Real.rpow_nonneg (Real.log_natCast_nonneg X) a)
  exact_mod_cast hf.trans hw

/-- Larger neighboring factors themselves are absent for almost every
prime in the indicated growing cofactor range. -/
theorem logPower_roughNeighborPrimes_scaled_count_tendsto (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) :
    Tendsto (fun X : ℕ =>
      ((roughNeighborPrimes (logPowerCofactorCutoff a X) X).card : ℝ)*Real.log X/X)
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun X => by
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg X))
      (Nat.cast_nonneg X))) _ (logPower_bothAbove_linear_scaled_count_tendsto a ha ha1)
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    logPowerCofactorCutoff_eventually_le_endpoint a] with X hX hK
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
    ((Nat.cast_le (α := ℝ)).mpr
      (roughNeighborPrimes_card_le (logPowerCofactorCutoff a X) X hX hK))
    (Real.log_natCast_nonneg X)) (Nat.cast_nonneg X)

theorem logPower_roughNeighborPrimes_prime_proportion_tendsto (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) :
    Tendsto (fun X : ℕ =>
      ((roughNeighborPrimes (logPowerCofactorCutoff a X) X).card : ℝ)/
        (narrowPrimeBand 1 2 X).card) atTop (𝓝 0) := by
  have hden := narrowPrimeBand_card_scaled_limit 1 2 (by norm_num) (by norm_num)
  norm_num only at hden
  have ht := (logPower_roughNeighborPrimes_scaled_count_tendsto a ha ha1).div hden one_ne_zero
  simp only [zero_div] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with X hX
  have hx : (X : ℝ) ≠ 0 := by exact_mod_cast (show X ≠ 0 by omega)
  have hl : Real.log X ≠ 0 := (Real.log_pos (by exact_mod_cast hX)).ne'
  simp only [Pi.div_apply]
  field_simp

/-- Every sufficiently large dyadic interval contains such a prime. -/
theorem eventually_exists_prime_smooth_neighbor_run (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    ∀ᶠ X : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ X < p ∧ p ≤ 2*X ∧
      ∀ k ∈ Icc 1 (logPowerCofactorCutoff a X),
        Nat.maxPrimeFac (k*p-1) < p ∧ Nat.maxPrimeFac (k*p+1) < p := by
  have hden := narrowPrimeBand_card_scaled_limit 1 2 (by norm_num) (by norm_num)
  norm_num only at hden
  filter_upwards [logPowerCofactorCutoff_eventually_le_endpoint a,
    (logPower_roughNeighborPrimes_scaled_count_tendsto a ha ha1).eventually_lt_const
      (by norm_num : (0 : ℝ) < 1/4),hden.eventually_const_lt (by norm_num : (1/2 : ℝ) < 1),
    eventually_ge_atTop (2 : ℕ)] with X hK hbad hband hX
  have hlt : (roughNeighborPrimes (logPowerCofactorCutoff a X) X).card <
      (narrowPrimeBand 1 2 X).card := by
    by_contra h
    have hle : ((narrowPrimeBand 1 2 X).card : ℝ) ≤
        (roughNeighborPrimes (logPowerCofactorCutoff a X) X).card := by exact_mod_cast (not_lt.mp h)
    have hle' := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hle (Real.log_natCast_nonneg X)) (Nat.cast_nonneg (α := ℝ) X)
    linarith
  have hnot : ¬narrowPrimeBand 1 2 X ⊆ roughNeighborPrimes (logPowerCofactorCutoff a X) X := by
    intro h
    exact (not_le_of_gt hlt) (card_le_card h)
  obtain ⟨p,hp⟩ := sdiff_nonempty.mpr hnot
  obtain ⟨hpband,hpnot⟩ := mem_sdiff.mp hp
  obtain ⟨hprime,hlo,hhi⟩ := dyadicPrimeBand_nat_data hpband
  exact ⟨p,hprime,hlo,hhi,smooth_neighbors_of_not_mem_roughNeighborPrimes
    (logPowerCofactorCutoff a X) X p hK hpband hpnot⟩

lemma logPowerCofactorCutoff_dyadic_domination (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    ∀ᶠ X : ℕ in atTop, ∀ p : ℕ, X < p → p ≤ 2*X →
      logPowerCofactorCutoff a p ≤ logPowerCofactorCutoff b X := by
  have hlog : Tendsto (fun X : ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ht := (tendsto_rpow_atTop (sub_pos.mpr hab)).comp hlog
  filter_upwards [eventually_ge_atTop (2 : ℕ),ht.eventually_ge_atTop ((2 : ℝ)^a)]
    with X hX hpow
  intro p hpX hp2X
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hL0 : 0 < Real.log X := Real.log_pos (by exact_mod_cast hX)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hlogp : Real.log p ≤ 2*Real.log X := by
    have h := Real.log_le_log hp0 (by exact_mod_cast hp2X : (p : ℝ) ≤ 2*X)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hX0.ne'] at h
    have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hX : (2 : ℝ) ≤ X)
    linarith
  unfold logPowerCofactorCutoff
  apply Nat.floor_mono
  calc
    _ ≤ (2*Real.log X)^a := Real.rpow_le_rpow (Real.log_natCast_nonneg p) hlogp ha
    _ = (2 : ℝ)^a*(Real.log X)^a := Real.mul_rpow (by norm_num) hL0.le
    _ ≤ (Real.log X)^(b-a)*(Real.log X)^a :=
      mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hL0.le a)
    _ = _ := by rw [← Real.rpow_add hL0,sub_add_cancel]

noncomputable def roughNeighborPrimesAtOwnScale (a : ℝ) (X : ℕ) : Finset ℕ :=
  (narrowPrimeBand 1 2 X).filter fun p => ∃ k ≤ logPowerCofactorCutoff a p, 1 ≤ k ∧
    (p < Nat.maxPrimeFac (k*p-1) ∨ p < Nat.maxPrimeFac (k*p+1))

/-- The cofactor range may be measured at the prime itself, not just at
the lower endpoint of the dyadic band. -/
theorem roughNeighborPrimesAtOwnScale_proportion_tendsto (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) :
    Tendsto (fun X : ℕ => ((roughNeighborPrimesAtOwnScale a X).card : ℝ)/
      (narrowPrimeBand 1 2 X).card) atTop (𝓝 0) := by
  let b : ℝ := (a+1)/2
  have hab : a < b := by dsimp [b]; linarith
  have hb1 : b < 1 := by dsimp [b]; linarith
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _
    (logPower_roughNeighborPrimes_prime_proportion_tendsto b (ha.trans hab.le) hb1)
  filter_upwards [logPowerCofactorCutoff_dyadic_domination a b ha hab] with X hdom
  have hs : roughNeighborPrimesAtOwnScale a X ⊆
      roughNeighborPrimes (logPowerCofactorCutoff b X) X := by
    intro p hp
    obtain ⟨hpband,k,hk,hk1,hrough⟩ := mem_filter.mp hp
    obtain ⟨_,hpX,hp2X⟩ := dyadicPrimeBand_nat_data hpband
    exact mem_filter.mpr ⟨hpband,k,hk.trans (hdom p hpX hp2X),hk1,hrough⟩
  exact div_le_div_of_nonneg_right ((Nat.cast_le (α := ℝ)).mpr (card_le_card hs))
    (Nat.cast_nonneg _)

/-- Infinitely many primes have smooth neighbors at every one of the first
floor((log p)^a) positive multiples, for every fixed 0<=a<1. -/
theorem infinitely_many_prime_smooth_neighbor_runs (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    {p : ℕ | p.Prime ∧ ∀ k ∈ Icc 1 (logPowerCofactorCutoff a p),
      Nat.maxPrimeFac (k*p-1) < p ∧ Nat.maxPrimeFac (k*p+1) < p}.Infinite := by
  let b : ℝ := (a+1)/2
  have hab : a < b := by dsimp [b]; linarith
  have hb1 : b < 1 := by dsimp [b]; linarith
  have hb0 : 0 ≤ b := (ha.trans hab.le)
  apply Set.infinite_of_forall_exists_gt
  intro M
  obtain ⟨X,hgood,hdom,hM⟩ := ((eventually_exists_prime_smooth_neighbor_run b hb0 hb1).and
    ((logPowerCofactorCutoff_dyadic_domination a b ha hab).and (eventually_ge_atTop M))).exists
  obtain ⟨p,hp,hpX,hp2X,hrun⟩ := hgood
  refine ⟨p,⟨hp,?_⟩,by omega⟩
  intro k hk
  obtain ⟨hk1,hkK⟩ := mem_Icc.mp hk
  exact hrun k (mem_Icc.mpr ⟨hk1,hkK.trans (hdom p hpX hp2X)⟩)

#print axioms roughNeighborPrimes_subset_loser_image
#print axioms logPower_roughNeighborPrimes_prime_proportion_tendsto
#print axioms eventually_exists_prime_smooth_neighbor_run
#print axioms roughNeighborPrimesAtOwnScale_proportion_tendsto
#print axioms infinitely_many_prime_smooth_neighbor_runs
end Erdos371
