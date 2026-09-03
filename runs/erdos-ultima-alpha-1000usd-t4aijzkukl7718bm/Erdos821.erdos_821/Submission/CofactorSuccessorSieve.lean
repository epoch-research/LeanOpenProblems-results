import Submission.OneRootDenominator
import Submission.CofactorNaturalMean

/-!
# A weighted upper sieve for prime linear successors

The cofactor and the Mangoldt-weighted variable are averaged together.
The residue family is allowed to depend on the coefficient, with no
roughness assumption on that coefficient in the finite sieve bound.
-/
open Nat Finset Filter ArithmeticFunction
open scoped Classical BigOperators
namespace Erdos821.AnalyticSieve
open Sieve
set_option maxHeartbeats 3000000

noncomputable def successorUnit (c d : ℕ) : (ZMod d)ˣ :=
  if h : c.Coprime d then -(ZMod.unitOfCoprime c h) else 1

lemma successorUnit_coe (c d : ℕ) (h : c.Coprime d) :
    (successorUnit c d : ZMod d) = -(c : ZMod d) := by
  rw [successorUnit,dif_pos h]
  rfl

lemma successorUnit_congruence (c d a n : ℕ) (h : c.Coprime d) :
    (successorUnit c d : ZMod d)*(a : ZMod d)*(n : ZMod d)=1 ↔
      d ∣ c*a*n+1 := by
  rw [successorUnit_coe c d h,← ZMod.natCast_eq_zero_iff]
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one]
  constructor <;> intro hh <;> linear_combination -hh

noncomputable def cofactorSuccessorDiscrepancy (c A B N d : ℕ) : ℝ :=
  |cofactorCongruenceWeight d (successorUnit c d) A B N-
    ((B-A : ℕ) : ℝ)*mangoldtSum N/(d : ℝ)|

noncomputable def cofactorPrimeSuccessorWeight (c A B N z : ℕ) : ℝ :=
  ∑ x ∈ (Icc (A+1) B ×ˢ Icc 1 N) with
    (c*x.1*x.2+1).Prime ∧ z<c*x.1*x.2+1, vonMangoldt x.2

lemma cofactor_successor_support_count (c A B N : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ ¬p ∣ c) :
    (∑ x ∈ Icc (A+1) B ×ˢ Icc 1 N,
      if ∀ p ∈ P, p ∣ c*x.1*x.2+1 then vonMangoldt x.2 else 0) =
        cofactorCongruenceWeight (∏ p ∈ P, p)
          (successorUnit c (∏ p ∈ P, p)) A B N := by
  have hc : c.Coprime (∏ p ∈ P, p) := Nat.coprime_prod_right_iff.mpr (by
    intro p hp
    exact ((hP p hp).1.coprime_iff_not_dvd.mpr (hP p hp).2).symm)
  simp only [cofactorCongruenceWeight,sum_product,
    successorUnit_congruence c _ _ _ hc,
    prod_primes_dvd_iff P (fun p hp => (hP p hp).1)]

lemma cofactor_prime_successor_le_sifted (c A B N z : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ z) :
    cofactorPrimeSuccessorWeight c A B N z ≤
      ∑ x ∈ (Icc (A+1) B ×ˢ Icc 1 N) with
        ∀ p ∈ P, ¬p ∣ c*x.1*x.2+1, vonMangoldt x.2 := by
  apply sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => vonMangoldt_nonneg)
  intro x hx
  obtain ⟨hxI,hprime,hz⟩ := mem_filter.mp hx
  refine mem_filter.mpr ⟨hxI,?_⟩
  intro p hp hpd
  have he : p=c*x.1*x.2+1 := (Nat.prime_dvd_prime_iff_eq (hP p hp).1 hprime).mp hpd
  have hh := (hP p hp).2
  omega

/-- A finite bound retaining the full averaged error over positive moduli.
Mangoldt prime powers remain included in the sequence weight. -/
theorem exists_cofactor_successor_sieve_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ c A B N z : ℕ, 1 ≤ z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ p ≤ z ∧ ¬p ∣ c) →
        cofactorPrimeSuccessorWeight c A B N z ≤
          ((B-A : ℕ) : ℝ)*mangoldtSum N*(oneRootDenominator P z)⁻¹+
            C*((z^2 : ℕ) : ℝ)^ε*
              ∑ d ∈ Icc 1 (z^2), cofactorSuccessorDiscrepancy c A B N d := by
  classical
  obtain ⟨C,hC,HC⟩ := exists_weighted_selberg_mean_bound ε hε
  refine ⟨C,hC,?_⟩
  intro c A B N z hz P hP
  apply (cofactor_prime_successor_le_sifted c A B N z P
    (fun p hp => ⟨(hP p hp).1,(hP p hp).2.1⟩)).trans
  convert HC (ℕ × ℕ) (Icc (A+1) B ×ˢ Icc 1 N) (fun x => vonMangoldt x.2)
    (fun _ _ => vonMangoldt_nonneg) P (fun p hp => (hP p hp).1) z hz
    (fun p x => p ∣ c*x.1*x.2+1) (((B-A : ℕ) : ℝ)*mangoldtSum N)
    (cofactorSuccessorDiscrepancy c A B N)
    (fun d _ => abs_nonneg _) ?_ using 1
  · simp only [sum_filter]
    apply sum_congr rfl
    intro x hx
    by_cases hh : ∀ p ∈ P, ¬p ∣ c*x.1*x.2+1
    · rw [if_pos hh,if_pos hh]
    · rw [if_neg hh,if_neg hh]
  intro U hU _hUz
  have hUP := mem_powerset.mp hU
  rw [cofactor_successor_support_count c A B N U
    (fun p hp => ⟨(hP p (hUP hp)).1,(hP p (hUP hp)).2.2⟩)]
  exact le_rfl

/-- Prime factors of the coefficient are omitted from the sieve pool.
Their exact first-power totient ratio is retained in the main term. -/
theorem exists_cofactor_successor_log_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ c A B N z : ℕ, 0 < c → 1 ≤ z →
      cofactorPrimeSuccessorWeight c A B N z ≤
        ((B-A : ℕ) : ℝ)*mangoldtSum N*((c : ℝ)/(c.totient : ℝ))/Real.log (z+1 : ℝ)+
          C*((z^2 : ℕ) : ℝ)^ε*
            ∑ d ∈ Icc 1 (z^2), cofactorSuccessorDiscrepancy c A B N d := by
  obtain ⟨C,hC,HC⟩ := exists_cofactor_successor_sieve_bound ε hε
  refine ⟨C,hC,?_⟩
  intro c A B N z hc hz
  let P := (z+1).primesBelow \ c.primeFactors
  have hP : ∀ p ∈ P, p.Prime ∧ p ≤ z ∧ ¬p ∣ c := by
    intro p hp
    obtain ⟨hpz,hpc⟩ := mem_sdiff.mp hp
    obtain ⟨hpl,hprime⟩ := Nat.mem_primesBelow.mp hpz
    refine ⟨hprime,by omega,?_⟩
    intro hpd
    exact hpc (hprime.mem_primeFactors hpd hc.ne')
  apply (HC c A B N z hz P hP).trans
  apply _root_.add_le_add _ le_rfl
  have hcR : (0 : ℝ)<c := by exact_mod_cast hc
  have hφ : (0 : ℝ)<c.totient := by exact_mod_cast Nat.totient_pos.mpr hc
  have hlog : 0 < Real.log (z+1 : ℝ) := Real.log_pos (by exact_mod_cast (show 1<z+1 by omega))
  have hb := oneRootDenominator_totient_log_lower c z hc hz
  have hbase : 0 < ((c.totient : ℝ)/(c : ℝ))*Real.log (z+1 : ℝ) := by positivity
  have hinv := one_div_le_one_div_of_le hbase hb
  have he : 1/(((c.totient : ℝ)/(c : ℝ))*Real.log (z+1 : ℝ)) =
      ((c : ℝ)/(c.totient : ℝ))/Real.log (z+1 : ℝ) := by field_simp
  rw [he,one_div] at hinv
  have hh := mul_le_mul_of_nonneg_left hinv
    (show 0 ≤ ((B-A : ℕ) : ℝ)*mangoldtSum N from
      mul_nonneg (Nat.cast_nonneg _) (mangoldtSum_nonneg _))
  simpa only [mul_div_assoc] using hh

end Erdos821.AnalyticSieve
