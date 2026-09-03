import Submission.WideConductorScales
import Submission.ChebyshevCompositeGain

/-!
# Fixed reciprocal mass in wide prime-product modulus pools

Two disjoint logarithmic intervals supply composite moduli with fixed
positive reciprocal mass.  Their conductor errors have a power saving.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 2000000

noncomputable def widePrimePool (a b m : ℕ) : Finset ℕ :=
  (progressionScaleN (b*m)+1).primesBelow.filter (fun p => progressionScaleN (a*m) ≤ p)

lemma mem_widePrimePool {a b m p : ℕ} : p ∈ widePrimePool a b m ↔
    p.Prime ∧ progressionScaleN (a*m) ≤ p ∧ p ≤ progressionScaleN (b*m) := by
  simp only [widePrimePool, mem_filter, Nat.mem_primesBelow, Nat.lt_succ_iff]
  constructor
  · rintro ⟨⟨hu,hp⟩,hl⟩
    exact ⟨hp,hl,hu⟩
  · rintro ⟨hp,hl,hu⟩
    exact ⟨⟨hu,hp⟩,hl⟩

lemma widePrimePool_disjoint (a b c m : ℕ) :
    Disjoint (widePrimePool a b m) (widePrimePool b c m) := by
  apply disjoint_left.mpr
  intro p hp hq
  obtain ⟨hp,hpa,hpb⟩ := mem_widePrimePool.mp hp
  obtain ⟨_,hqb,_⟩ := mem_widePrimePool.mp hq
  have he : p = progressionScaleN (b*m) := by omega
  rw [he] at hp
  exact Nat.Prime.not_prime_pow' (by omega : 64*(b*m) ≠ 1) hp

lemma widePrimePool_mass_lower (a b m : ℕ) (hab : a < b) (hm : 1 ≤ m) :
    ((b-a : ℕ) : ℝ)/(2048*(b : ℝ)) ≤ poolTotientMass (widePrimePool a b m) := by
  have hbm : a*m < b*m := Nat.mul_lt_mul_of_pos_right hab hm
  have h := prime_moduli_reciprocal_ge_block_count (a*m) (b*m) hbm
  rw [sum_primeModuliBetween_eq_nat _ _ (fun d => (d.totient : ℝ)⁻¹)] at h
  change _ ≤ poolTotientMass (widePrimePool a b m) at h
  apply le_trans (le_of_eq ?_) h
  rw [← Nat.sub_mul]
  push_cast
  have hb : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  field_simp

lemma prime_pool_mass_upper (P : Finset ℕ) (H : ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ H) :
    poolTotientMass P ≤ 2*(1+Real.log H) := by
  have hloc (p : ℕ) (hp : p ∈ P) : (p.totient : ℝ)⁻¹ ≤ 2*(p : ℝ)⁻¹ := by
    have hp2 := (hP p hp).1.two_le
    have hpr : (0 : ℝ) < p := by exact_mod_cast (hP p hp).1.pos
    have hsub : (0 : ℝ) < (p-1 : ℕ) := by exact_mod_cast (show 0 < p-1 by omega)
    rw [Nat.totient_prime (hP p hp).1]
    have he : (p : ℝ) ≤ 2*((p-1 : ℕ) : ℝ) := by exact_mod_cast (show p ≤ 2*(p-1) by omega)
    calc
      _ = 1/((p-1 : ℕ) : ℝ) := (one_div _).symm
      _ ≤ 2/(p : ℝ) := (div_le_div_iff₀ hsub hpr).mpr (by nlinarith only [he])
      _ = _ := div_eq_mul_inv _ _
  have hsub : P ⊆ Icc 1 H := by
    intro p hp
    exact mem_Icc.mpr ⟨(hP p hp).1.pos, (hP p hp).2⟩
  have hH : (∑ p ∈ Icc 1 H, (p : ℝ)⁻¹) = (harmonic H : ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  calc
    _ ≤ ∑ p ∈ P, 2*(p : ℝ)⁻¹ := sum_le_sum hloc
    _ = 2*∑ p ∈ P, (p : ℝ)⁻¹ := (mul_sum _ _ _).symm
    _ ≤ 2*∑ p ∈ Icc 1 H, (p : ℝ)⁻¹ := mul_le_mul_of_nonneg_left
      (sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))) (by norm_num)
    _ ≤ _ := by rw [hH]; exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log H) (by norm_num)

lemma widePrimePool_mass_upper (a b m : ℕ) :
    poolTotientMass (widePrimePool a b m) ≤ 130*((b : ℝ)+1)*((m : ℝ)+1) := by
  apply (prime_pool_mass_upper _ (progressionScaleN (b*m)) (fun p hp =>
    ⟨(mem_widePrimePool.mp hp).1, (mem_widePrimePool.mp hp).2.2⟩)).trans
  have hlog := log_two_pow_le (64*(b*m))
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hlog
  change Real.log (progressionScaleN (b*m)) ≤ 64*((b : ℝ)*m) at hlog
  nlinarith [Nat.cast_nonneg (α := ℝ) b, Nat.cast_nonneg (α := ℝ) m,
    mul_nonneg (Nat.cast_nonneg (α := ℝ) b) (Nat.cast_nonneg (α := ℝ) m)]

noncomputable def wideLeftPool (m : ℕ) := widePrimePool 10000 10001 m
noncomputable def wideRightPool (m : ℕ) := widePrimePool 10001 10002 m
noncomputable def wideProductPool (m : ℕ) := pairPrimeProducts (wideLeftPool m) (wideRightPool m)

def wideMassDenominator : ℕ := (2048*10001)*(2048*10002)

lemma wideLeftPool_prime (m p : ℕ) (hp : p ∈ wideLeftPool m) : p.Prime :=
  (mem_widePrimePool.mp hp).1
lemma wideRightPool_prime (m p : ℕ) (hp : p ∈ wideRightPool m) : p.Prime :=
  (mem_widePrimePool.mp hp).1
lemma widePools_disjoint (m : ℕ) : Disjoint (wideLeftPool m) (wideRightPool m) :=
  widePrimePool_disjoint _ _ _ _

lemma wideProductPool_mass (m : ℕ) : poolTotientMass (wideProductPool m) =
    poolTotientMass (wideLeftPool m)*poolTotientMass (wideRightPool m) :=
  pairPrimeProducts_mass _ _ (wideLeftPool_prime m) (wideRightPool_prime m) (widePools_disjoint m)

lemma wideProductPool_mass_lower (m : ℕ) (hm : 1 ≤ m) :
    1/(wideMassDenominator : ℝ) ≤ poolTotientMass (wideProductPool m) := by
  rw [wideProductPool_mass]
  have hL := widePrimePool_mass_lower 10000 10001 m (by decide) hm
  have hR := widePrimePool_mass_lower 10001 10002 m (by decide) hm
  norm_num at hL hR
  have h := mul_le_mul hL hR (by norm_num) (poolTotientMass_nonneg _)
  norm_num [wideMassDenominator] at h ⊢
  exact h

lemma widePrimePools_bounds (m p : ℕ) (hp : p ∈ wideLeftPool m ∨ p ∈ wideRightPool m) :
    2 ≤ p ∧ progressionScaleN (10000*m) ≤ p ∧ p ≤ progressionScaleN (10002*m) := by
  rcases hp with hp | hp
  · obtain ⟨hp,hl,hu⟩ := mem_widePrimePool.mp hp
    exact ⟨hp.two_le,hl,hu.trans (progressionScaleN_monotone (by omega))⟩
  · obtain ⟨hp,hl,hu⟩ := mem_widePrimePool.mp hp
    exact ⟨hp.two_le,(progressionScaleN_monotone (by omega)).trans hl,hu⟩

lemma wideProductPool_bounds (m d : ℕ) (hd : d ∈ wideProductPool m) :
    2 ≤ d ∧ progressionScaleN (20000*m) ≤ d ∧ d ≤ progressionScaleN (20004*m) := by
  obtain ⟨⟨p,q⟩, hpq, rfl⟩ := mem_image.mp hd
  obtain ⟨hp,hq⟩ := mem_product.mp hpq
  have hpb := widePrimePools_bounds m p (Or.inl hp)
  have hqb := widePrimePools_bounds m q (Or.inr hq)
  have heq (a : ℕ) : progressionScaleN ((2*a)*m) = progressionScaleN (a*m)*progressionScaleN (a*m) := by
    simp only [progressionScaleN, ← pow_add]
    congr 1
    ring
  refine ⟨by dsimp; nlinarith [hpb.1,hqb.1],?_,?_⟩
  · rw [show 20000 = 2*10000 by decide, heq]
    exact Nat.mul_le_mul hpb.2.1 hqb.2.1
  · rw [show 20004 = 2*10002 by decide, heq]
    exact Nat.mul_le_mul hpb.2.2 hqb.2.2

lemma wideProductPool_card_le (m : ℕ) : (wideProductPool m).card ≤ progressionScaleN (20004*m) := by
  have hsub : wideProductPool m ⊆ Icc 1 (progressionScaleN (20004*m)) := by
    intro d hd
    have h := wideProductPool_bounds m d hd
    exact mem_Icc.mpr ⟨by omega,h.2.2⟩
  exact (card_le_card hsub).trans_eq (by simp)

end Erdos821
