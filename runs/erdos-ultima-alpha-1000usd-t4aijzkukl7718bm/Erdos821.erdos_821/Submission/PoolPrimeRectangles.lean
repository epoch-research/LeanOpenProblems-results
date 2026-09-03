import Submission.PoolSuccessorScales
import Submission.CofactorPrimePairCover
import Submission.RestrictedCofactorDiagonal

/-!
# Prime-variable rectangles retaining the multiplier pool

The inner weight is restricted to actual primes above M. This guarantees
unit support at products of primes at most z whenever z<=M. Prime powers
are not silently treated as primes.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
open Sieve
set_option maxHeartbeats 4000000

noncomputable def intervalPrimeWeight (M : ℕ) : ArithmeticFunction ℝ :=
  mangoldtRestriction {n | n.Prime ∧ M<n}

lemma intervalPrimeWeight_nonneg (M n : ℕ) : 0 ≤ intervalPrimeWeight M n :=
  mangoldtRestriction_nonneg _ n

lemma intervalPrimeWeight_le (M n : ℕ) : intervalPrimeWeight M n ≤ vonMangoldt n :=
  mangoldtRestriction_le _ n

lemma intervalPrimeWeight_apply (M n : ℕ) :
    intervalPrimeWeight M n = if n.Prime ∧ M<n then vonMangoldt n else 0 := by
  simp only [intervalPrimeWeight,mangoldtRestriction,ArithmeticFunction.coe_mk,Set.mem_setOf_eq]
  by_cases h : n.Prime ∧ M<n <;> simp [h]

lemma intervalPrimeWeight_prime (M n : ℕ) (hn : n.Prime) (hM : M<n) :
    intervalPrimeWeight M n = Real.log n := by
  rw [intervalPrimeWeight_apply,if_pos ⟨hn,hM⟩,vonMangoldt_apply_prime hn]

lemma intervalPrimeWeight_support (M n : ℕ) (h : intervalPrimeWeight M n ≠ 0) :
    n.Prime ∧ M<n := by
  by_contra hn
  exact h (by rw [intervalPrimeWeight_apply,if_neg hn])

lemma intervalPrimeWeight_unit (M n p : ℕ) (h : intervalPrimeWeight M n ≠ 0)
    (hp : p.Prime) (hpM : p ≤ M) : n.Coprime p := by
  have hn := intervalPrimeWeight_support M n h
  exact (Nat.coprime_primes hn.1 hp).mpr (by omega)

lemma intervalPrimeMass_le (M N : ℕ) (hMN : M ≤ N) :
    restrictedMass (intervalPrimeWeight M) N ≤ mangoldtSum N-mangoldtSum M := by
  change restrictedMass (intervalPrimeWeight M) N ≤ (∑ n ∈ Icc 1 N, vonMangoldt n)-(∑ n ∈ Icc 1 M, vonMangoldt n)
  rw [← sum_natural_interval_sub vonMangoldt M N hMN]
  have he : restrictedMass (intervalPrimeWeight M) N =
      ∑ n ∈ Icc (M+1) N, intervalPrimeWeight M n := by
    symm
    apply sum_subset (Icc_subset_Icc (by omega) le_rfl)
    intro n hn hnot
    have hM : ¬M<n := by
      intro h
      exact hnot (mem_Icc.mpr ⟨h,(mem_Icc.mp hn).2⟩)
    rw [intervalPrimeWeight_apply,if_neg (by tauto)]
  rw [he]
  exact sum_le_sum (fun n _ => intervalPrimeWeight_le M n)

noncomputable def poolPrimePairPool (P : Finset ℕ) (A B M N : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (P ×ˢ (Icc (A+1) B ×ˢ Icc (M+1) N)).filter
    (fun x => x.2.2.Prime ∧ (x.1*x.2.1*x.2.2+1).Prime)

lemma poolPrimePairPool_card (P : Finset ℕ) (A B M N : ℕ) :
    (poolPrimePairPool P A B M N).card = ∑ c ∈ P, (cofactorPrimePairPool c A B M N).card := by
  simp only [poolPrimePairPool,cofactorPrimePairPool,card_eq_sum_ones,sum_filter,sum_product]

lemma pool_prime_pair_log_weight (P : Finset ℕ) (A B M N z : ℕ)
    (hP : ∀ c ∈ P, 0<c) (hM : 1 ≤ M) (hz : z ≤ M) :
    Real.log (M : ℝ)*((poolPrimePairPool P A B M N).card : ℝ) ≤
      poolPrimeSuccessorWeight (intervalPrimeWeight M) P A B N z := by
  let T := poolPrimePairPool P A B M N
  have hsub : T ⊆ (P ×ˢ (Icc (A+1) B ×ˢ Icc 1 N)).filter
      (fun x => (x.1*x.2.1*x.2.2+1).Prime ∧ z<x.1*x.2.1*x.2.2+1) := by
    intro x hx
    obtain ⟨hxI,hn,hs⟩ := mem_filter.mp hx
    obtain ⟨hc,haq⟩ := mem_product.mp hxI
    obtain ⟨ha,hq⟩ := mem_product.mp haq
    have ha0 : 0 < x.2.1 := by have := (mem_Icc.mp ha).1; omega
    have hMq : M<x.2.2 := (mem_Icc.mp hq).1
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hc,mem_product.mpr
      ⟨ha,mem_Icc.mpr ⟨hn.pos,(mem_Icc.mp hq).2⟩⟩⟩,hs,
        (hz.trans_lt hMq).trans (cofactor_successor_gt_inner x.1 x.2.1 x.2.2 (hP _ hc) ha0)⟩
  have hlog (x : ℕ × (ℕ × ℕ)) (hx : x ∈ T) :
      Real.log (M : ℝ) ≤ intervalPrimeWeight M x.2.2 := by
    obtain ⟨hxI,hn,_⟩ := mem_filter.mp hx
    have hMq : M<x.2.2 := (mem_Icc.mp (mem_product.mp (mem_product.mp hxI).2).2).1
    rw [intervalPrimeWeight_prime M x.2.2 hn hMq]
    exact Real.log_le_log (by exact_mod_cast hM) (Nat.cast_le.mpr hMq.le)
  calc
    _ = ∑ _x ∈ T, Real.log (M : ℝ) := by simp only [sum_const,nsmul_eq_mul,mul_comm]; rfl
    _ ≤ ∑ x ∈ T, intervalPrimeWeight M x.2.2 := sum_le_sum hlog
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => intervalPrimeWeight_nonneg M x.2.2)

lemma oneRootDenominator_all_log_lower (z : ℕ) (hz : 1 ≤ z) :
    Real.log ((z : ℝ)+1) ≤ oneRootDenominator (z+1).primesBelow z := by
  simpa using oneRootDenominator_totient_log_lower 1 z (by decide) hz

/-- The main mass can be bounded by the actual Mangoldt interval. The
ambient error is not multiplied by the cardinality of P. -/
theorem exists_pool_prime_rectangle_power_saving (a b s l v t : ℕ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hs : 2*a+1 ≤ s)
    (hl : 1 ≤ l) (ht : 1 ≤ t) (hlevel : 2*b+1 ≤ l+t) :
    ∃ K : ℝ, 0 < K ∧ ∀ m D B M N : ℕ, M ≤ N →
      cofactorScale s (2*m) ≤ B → cofactorScale l (2*m) ≤ D*B →
      D*B ≤ cofactorScale v (2*m) → N ≤ cofactorScale t (2*m) →
      2 ≤ M → cofactorScale b m ≤ M →
      ∀ P : Finset ℕ, P ⊆ Icc 1 D →
      (∀ c ∈ P, ∀ p : ℕ, p.Prime → p ≤ cofactorScale b m → ¬p ∣ c) →
      ((poolPrimePairPool P 0 B M N).card : ℝ) ≤
        (P.card : ℝ)*(B : ℝ)*(mangoldtSum N-mangoldtSum M)/
          (Real.log ((cofactorScale b m : ℝ)+1)*Real.log M)+
        K*((m : ℝ)+1)^7/(2 : ℝ)^m*((D*B : ℕ) : ℝ)*(cofactorScale t (2*m) : ℝ)/Real.log M := by
  obtain ⟨K,hK,HK⟩ := exists_pool_unit_successor_power_saving a b s l v t ha hab hs hl ht hlevel
  refine ⟨K,hK,?_⟩
  intro m D B M N hMN hB hDB hDBup hN hM hzM P hP hrough
  let z := cofactorScale b m
  let J := (z+1).primesBelow
  have hJ : ∀ p ∈ J, p.Prime ∧ p ≤ z := by
    intro p hp
    obtain ⟨hpz,hpr⟩ := Nat.mem_primesBelow.mp hp
    exact ⟨hpr,by omega⟩
  have hunitP : ∀ c ∈ P, ∀ p ∈ J, c.Coprime p := by
    intro c hc p hp
    exact ((hJ p hp).1.coprime_iff_not_dvd.mpr (hrough c hc p (hJ p hp).1 (hJ p hp).2)).symm
  have hunit : ∀ n ∈ Icc 1 N, intervalPrimeWeight M n ≠ 0 → ∀ p ∈ J, n.Coprime p := by
    intro n hn hn0 p hp
    exact intervalPrimeWeight_unit M n p hn0 (hJ p hp).1 ((hJ p hp).2.trans hzM)
  have hsieve := HK (intervalPrimeWeight M) (intervalPrimeWeight_nonneg M) (intervalPrimeWeight_le M)
    m D B N hB hDB hDBup hN P J hP hJ hunitP hunit
  have hlogz : 0 < Real.log ((z : ℝ)+1) := Real.log_pos (by
    have : (0 : ℝ) < z := by exact_mod_cast cofactorScale_pos b m
    linarith)
  have hlogM : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast (show 1<M by omega))
  have hinv := one_div_le_one_div_of_le hlogz (oneRootDenominator_all_log_lower z (cofactorScale_pos b m))
  rw [one_div] at hinv
  have hm := intervalPrimeMass_le M N hMN
  have hmain := mul_le_mul (mul_le_mul_of_nonneg_left hm
    (mul_nonneg (Nat.cast_nonneg P.card) (Nat.cast_nonneg B))) hinv
      (inv_nonneg.mpr (le_trans hlogz.le (oneRootDenominator_all_log_lower z (cofactorScale_pos b m))))
      (by have := sub_nonneg.mpr (show mangoldtSum M ≤ mangoldtSum N from
          sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hMN) (fun _ _ _ => vonMangoldt_nonneg)); positivity)
  have hweight := (pool_prime_pair_log_weight P 0 B M N z
    (fun c hc => (mem_Icc.mp (hP hc)).1) (by omega) hzM).trans hsieve
  have hbnd := hweight.trans (_root_.add_le_add hmain le_rfl)
  rw [mul_comm (Real.log (M : ℝ))] at hbnd
  have hh := (le_div_iff₀ hlogM).mpr hbnd
  apply hh.trans_eq
  dsimp [z]
  ring

end Erdos821.AnalyticSieve
