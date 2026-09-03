import Submission.CofactorSuccessorScales
import Submission.UniformCofactorNaturalMean

/-!
# Sieve bounds on intervals of the Mangoldt-weighted variable

Subtracting the two prefix progression formulas gives the actual interval
mass in the main term. Both prefix errors are retained.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
open Sieve
set_option maxHeartbeats 3000000

lemma sum_natural_interval_sub {G : Type*} [AddCommGroup G]
    (f : ℕ → G) (M N : ℕ) (hMN : M ≤ N) :
    (∑ n ∈ Icc (M+1) N, f n) = (∑ n ∈ Icc 1 N, f n)-(∑ n ∈ Icc 1 M, f n) := by
  have he : Icc 1 N = Icc 1 M ∪ Icc (M+1) N := by
    ext n
    simp only [mem_union,mem_Icc]
    omega
  have hd : Disjoint (Icc 1 M) (Icc (M+1) N) := by
    apply disjoint_left.mpr
    intro n hn hm
    have h1 := mem_Icc.mp hn
    have h2 := mem_Icc.mp hm
    omega
  rw [he,sum_union hd]
  abel

lemma cofactor_successor_interval_count (c A B M N : ℕ) (hMN : M ≤ N)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ ¬p ∣ c) :
    (∑ x ∈ Icc (A+1) B ×ˢ Icc (M+1) N,
      if ∀ p ∈ P, p ∣ c*x.1*x.2+1 then vonMangoldt x.2 else 0) =
        cofactorCongruenceWeight (∏ p ∈ P, p) (successorUnit c (∏ p ∈ P, p)) A B N-
          cofactorCongruenceWeight (∏ p ∈ P, p) (successorUnit c (∏ p ∈ P, p)) A B M := by
  rw [← cofactor_successor_support_count c A B N P hP,
    ← cofactor_successor_support_count c A B M P hP]
  simp only [sum_product,← sum_sub_distrib]
  apply sum_congr rfl
  intro a ha
  exact sum_natural_interval_sub _ M N hMN

lemma cofactor_successor_interval_discrepancy (c A B M N d : ℕ) :
    |cofactorCongruenceWeight d (successorUnit c d) A B N-
      cofactorCongruenceWeight d (successorUnit c d) A B M-
        ((B-A : ℕ) : ℝ)*(mangoldtSum N-mangoldtSum M)/(d : ℝ)| ≤
      cofactorSuccessorDiscrepancy c A B N d+cofactorSuccessorDiscrepancy c A B M d := by
  unfold cofactorSuccessorDiscrepancy
  convert abs_sub
    (cofactorCongruenceWeight d (successorUnit c d) A B N-((B-A : ℕ) : ℝ)*mangoldtSum N/d)
    (cofactorCongruenceWeight d (successorUnit c d) A B M-((B-A : ℕ) : ℝ)*mangoldtSum M/d) using 1
  congr 1
  ring

noncomputable def cofactorIntervalPrimeSuccessorWeight (c A B M N z : ℕ) : ℝ :=
  ∑ x ∈ (Icc (A+1) B ×ˢ Icc (M+1) N) with
    (c*x.1*x.2+1).Prime ∧ z<c*x.1*x.2+1, vonMangoldt x.2

lemma cofactor_interval_prime_successor_le_sifted (c A B M N z : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ z) :
    cofactorIntervalPrimeSuccessorWeight c A B M N z ≤
      ∑ x ∈ (Icc (A+1) B ×ˢ Icc (M+1) N) with
        ∀ p ∈ P, ¬p ∣ c*x.1*x.2+1, vonMangoldt x.2 := by
  apply sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => vonMangoldt_nonneg)
  intro x hx
  obtain ⟨hxI,hprime,hz⟩ := mem_filter.mp hx
  refine mem_filter.mpr ⟨hxI,?_⟩
  intro p hp hpd
  have he : p=c*x.1*x.2+1 := (Nat.prime_dvd_prime_iff_eq (hP p hp).1 hprime).mp hpd
  have hh := (hP p hp).2
  omega

/-- This is an upper bound for prime successors; the inner variable is
still Mangoldt weighted and therefore includes prime powers. -/
theorem exists_cofactor_interval_successor_sieve_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ c A B M N z : ℕ, M ≤ N → 1 ≤ z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ p ≤ z ∧ ¬p ∣ c) →
        cofactorIntervalPrimeSuccessorWeight c A B M N z ≤
          ((B-A : ℕ) : ℝ)*(mangoldtSum N-mangoldtSum M)*(oneRootDenominator P z)⁻¹+
            C*((z^2 : ℕ) : ℝ)^ε*∑ d ∈ Icc 1 (z^2),
              (cofactorSuccessorDiscrepancy c A B N d+cofactorSuccessorDiscrepancy c A B M d) := by
  classical
  obtain ⟨C,hC,HC⟩ := exists_weighted_selberg_mean_bound ε hε
  refine ⟨C,hC,?_⟩
  intro c A B M N z hMN hz P hP
  apply (cofactor_interval_prime_successor_le_sifted c A B M N z P
    (fun p hp => ⟨(hP p hp).1,(hP p hp).2.1⟩)).trans
  convert HC (ℕ × ℕ) (Icc (A+1) B ×ˢ Icc (M+1) N) (fun x => vonMangoldt x.2)
    (fun _ _ => vonMangoldt_nonneg) P (fun p hp => (hP p hp).1) z hz
    (fun p x => p ∣ c*x.1*x.2+1) (((B-A : ℕ) : ℝ)*(mangoldtSum N-mangoldtSum M))
    (fun d => cofactorSuccessorDiscrepancy c A B N d+cofactorSuccessorDiscrepancy c A B M d)
    (fun d _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) ?_ using 1
  · simp only [sum_filter]
    apply sum_congr rfl
    intro x hx
    by_cases hh : ∀ p ∈ P, ¬p ∣ c*x.1*x.2+1
    · rw [if_pos hh,if_pos hh]
    · rw [if_neg hh,if_neg hh]
  intro U hU _hUz
  have hUP := mem_powerset.mp hU
  rw [cofactor_successor_interval_count c A B M N hMN U
    (fun p hp => ⟨(hP p (hUP hp)).1,(hP p (hUP hp)).2.2⟩)]
  exact cofactor_successor_interval_discrepancy c A B M N _

theorem exists_cofactor_interval_successor_log_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ c A B M N z : ℕ, M ≤ N → 0 < c → 1 ≤ z →
      cofactorIntervalPrimeSuccessorWeight c A B M N z ≤
        ((B-A : ℕ) : ℝ)*(mangoldtSum N-mangoldtSum M)*
          ((c : ℝ)/(c.totient : ℝ))/Real.log (z+1 : ℝ)+
          C*((z^2 : ℕ) : ℝ)^ε*∑ d ∈ Icc 1 (z^2),
            (cofactorSuccessorDiscrepancy c A B N d+cofactorSuccessorDiscrepancy c A B M d) := by
  obtain ⟨C,hC,HC⟩ := exists_cofactor_interval_successor_sieve_bound ε hε
  refine ⟨C,hC,?_⟩
  intro c A B M N z hMN hc hz
  let P := (z+1).primesBelow \ c.primeFactors
  have hP : ∀ p ∈ P, p.Prime ∧ p ≤ z ∧ ¬p ∣ c := by
    intro p hp
    obtain ⟨hpz,hpc⟩ := mem_sdiff.mp hp
    obtain ⟨hpl,hprime⟩ := Nat.mem_primesBelow.mp hpz
    refine ⟨hprime,by omega,?_⟩
    intro hpd
    exact hpc (hprime.mem_primeFactors hpd hc.ne')
  apply (HC c A B M N z hMN hz P hP).trans
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
  have hmass : mangoldtSum M ≤ mangoldtSum N :=
    sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hMN) (fun _ _ _ => vonMangoldt_nonneg)
  have hh := mul_le_mul_of_nonneg_left hinv
    (show 0 ≤ ((B-A : ℕ) : ℝ)*(mangoldtSum N-mangoldtSum M) from
      mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hmass))
  simpa only [mul_div_assoc] using hh

end Erdos821.AnalyticSieve
