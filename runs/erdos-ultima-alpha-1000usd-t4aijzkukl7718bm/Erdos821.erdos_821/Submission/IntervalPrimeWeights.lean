import Submission.PrimeMassLogBounds
import Submission.EvenReciprocalTotient

/-!
# Reciprocal prime-product weights on logarithmic intervals

These finite bounds keep the logarithm of the ratio of the endpoints. They
are proved directly, not by subtracting two prefix upper bounds.
-/
open Nat Finset Filter
open scoped Classical BigOperators
namespace Erdos821.Sieve
set_option maxHeartbeats 3000000

lemma sum_inv_interval_le_log_ratio (A B : ℕ) (hA : 0 < A) (hAB : A ≤ B) :
    (∑ n ∈ Icc (A+1) B, (n : ℝ)⁻¹) ≤ Real.log ((B : ℝ)/A) := by
  rw [show Icc (A+1) B = Ico (A+1) (B+1) by ext n; simp]
  rw [← sum_Ico_add' (fun n : ℕ => (n : ℝ)⁻¹) A B 1]
  calc
    _ ≤ ∑ n ∈ Ico A B, (Real.log ((n+1 : ℕ) : ℝ)-Real.log (n : ℝ)) := by
      apply sum_le_sum
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hA.trans_le (mem_Ico.mp hn).1
      have hn1 : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
      have h := Real.one_sub_inv_le_log_of_pos (div_pos hn1 hn0)
      rw [Real.log_div hn1.ne' hn0.ne'] at h
      have he : 1-(((n+1 : ℕ) : ℝ)/(n : ℝ))⁻¹ = (((n+1 : ℕ) : ℝ))⁻¹ := by
        push_cast
        field_simp
        ring
      rwa [he] at h
    _ = Real.log (B : ℝ)-Real.log (A : ℝ) := sum_Ico_sub (fun n : ℕ => Real.log (n : ℝ)) hAB
    _ = _ := (Real.log_div (by exact_mod_cast (hA.trans_le hAB).ne')
      (by exact_mod_cast hA.ne')).symm

lemma sum_inv_multiples_interval_eq (A B d : ℕ) (hd : 0 < d) :
    (∑ n ∈ Icc (A+1) B with d ∣ n, (n : ℝ)⁻¹) =
      (d : ℝ)⁻¹*∑ k ∈ Icc (A/d+1) (B/d), (k : ℝ)⁻¹ := by
  have hset : (Icc (A+1) B).filter (fun n => d ∣ n) =
      (Icc (A/d+1) (B/d)).image (fun k => d*k) := by
    ext n
    constructor
    · intro hn
      obtain ⟨hnI,hdn⟩ := mem_filter.mp hn
      have he : d*(n/d)=n := Nat.mul_div_cancel' hdn
      refine mem_image.mpr ⟨n/d,mem_Icc.mpr ⟨?_,Nat.div_le_div_right (mem_Icc.mp hnI).2⟩,he⟩
      have hnA : A < (n/d)*d := by rw [mul_comm _ d,he]; exact (mem_Icc.mp hnI).1
      exact Nat.succ_le_iff.mpr ((Nat.div_lt_iff_lt_mul hd).mpr hnA)
    · intro hn
      obtain ⟨k,hk,rfl⟩ := mem_image.mp hn
      obtain ⟨hkA,hkB⟩ := mem_Icc.mp hk
      have hA := (Nat.div_lt_iff_lt_mul hd).mp (show A/d < k by omega)
      have hB := (Nat.le_div_iff_mul_le hd).mp hkB
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by simpa only [mul_comm] using hA,
        by simpa only [mul_comm] using hB⟩,Nat.dvd_mul_right _ _⟩
  rw [hset,sum_image (by intro a ha b hb he; exact Nat.eq_of_mul_eq_mul_left hd he),mul_sum]
  exact sum_congr rfl (fun k hk => by rw [Nat.cast_mul,mul_inv])

/-- A direct interval bound for multiples. The endpoint error is independent
of d, which is useful after summing prime-product divisor weights. -/
lemma sum_inv_multiples_interval_le (A B d : ℕ) (hA : 0 < A) (hAB : A ≤ B) (hd : 0 < d) :
    (∑ n ∈ Icc (A+1) B with d ∣ n, (n : ℝ)⁻¹) ≤
      Real.log ((B : ℝ)/A)/(d : ℝ)+1/(A : ℝ) := by
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hBR : (0 : ℝ) < B := by exact_mod_cast hA.trans_le hAB
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog : 0 ≤ Real.log ((B : ℝ)/A) := Real.log_nonneg ((one_le_div hAR).mpr (by exact_mod_cast hAB))
  rw [sum_inv_multiples_interval_eq A B d hd]
  let f := A/d+1
  let q := B/d
  by_cases hfq : f ≤ q
  · have hf : 0 < f := Nat.succ_pos _
    have hfR : (0 : ℝ) < f := by exact_mod_cast hf
    have hqR : (0 : ℝ) < q := by exact_mod_cast hf.trans_le hfq
    have hAdf : (A : ℝ) ≤ (d : ℝ)*f := by
      have hh := (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self (A/d))
      exact_mod_cast (by simpa only [mul_comm] using hh.le : A ≤ d*f)
    have hdqB : (d : ℝ)*q ≤ B := by exact_mod_cast Nat.mul_div_le B d
    have hratio : (q : ℝ)/f ≤ (B : ℝ)/A := by
      apply (div_le_div_iff₀ hfR hAR).mpr
      nlinarith only [mul_le_mul_of_nonneg_right hAdf hqR.le,
        mul_le_mul_of_nonneg_right hdqB hfR.le]
    have hlogs : Real.log ((q : ℝ)/f) ≤ Real.log ((B : ℝ)/A) :=
      Real.log_le_log (div_pos hqR hfR) hratio
    have hfirst : (d : ℝ)⁻¹*(f : ℝ)⁻¹ ≤ 1/(A : ℝ) := by
      rw [← mul_inv,one_div]
      exact (inv_le_inv₀ (mul_pos hdR hfR) hAR).mpr hAdf
    have hset : Icc f q = insert f (Icc (f+1) q) := by
      ext k
      simp only [mem_Icc,mem_insert]
      omega
    change (d : ℝ)⁻¹*(∑ k ∈ Icc f q, (k : ℝ)⁻¹) ≤ _
    rw [hset,sum_insert (by simp)]
    have htail := (sum_inv_interval_le_log_ratio f q hf hfq).trans hlogs
    have hm := mul_le_mul_of_nonneg_left htail (inv_nonneg.mpr hdR.le)
    calc
      _ = (d : ℝ)⁻¹*(f : ℝ)⁻¹+(d : ℝ)⁻¹*∑ k ∈ Icc (f+1) q, (k : ℝ)⁻¹ := by ring
      _ ≤ 1/(A : ℝ)+(d : ℝ)⁻¹*Real.log ((B : ℝ)/A) := add_le_add hfirst hm
      _ = _ := by ring
  · have hset : Icc (A/d+1) (B/d) = ∅ := Icc_eq_empty_of_lt (Nat.lt_of_not_ge hfq)
    rw [hset,sum_empty,mul_zero]
    positivity

lemma prime_product_expansion (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (w : ℕ → ℝ) (n : ℕ) :
    (∏ p ∈ Q with p ∣ n, (1+w p)) =
      ∑ S ∈ Q.powerset, if (∏ p ∈ S, p) ∣ n then ∏ p ∈ S, w p else 0 := by
  have hfilter : Q.powerset.filter (fun S => (∏ p ∈ S, p) ∣ n) =
      (Q.filter (fun p => p ∣ n)).powerset := by
    ext S
    simp only [mem_filter,mem_powerset]
    constructor
    · rintro ⟨hSQ,hdvd⟩ p hp
      exact mem_filter.mpr ⟨hSQ hp,(dvd_prod_of_mem id hp).trans hdvd⟩
    · intro hS
      have hSQ : S ⊆ Q := fun p hp => (mem_filter.mp (hS hp)).1
      exact ⟨hSQ,(prod_primes_dvd_iff S (fun p hp => hQ p (hSQ hp)) n).mpr
        (fun p hp => (mem_filter.mp (hS hp)).2)⟩
  rw [← sum_filter,hfilter,← prod_one_add]

/-- Interval analogue of the harmonic prime-product averaging bound. -/
theorem interval_prime_product_average (A B : ℕ) (hA : 0 < A) (hAB : A ≤ B)
    (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (w : ℕ → ℝ) (hw : ∀ p ∈ Q, 0 ≤ w p) :
    (∑ n ∈ Icc (A+1) B, (∏ p ∈ Q with p ∣ n, (1+w p))/(n : ℝ)) ≤
      Real.log ((B : ℝ)/A)*(∏ p ∈ Q, (1+w p/(p : ℝ)))+
        (1/(A : ℝ))*(∏ p ∈ Q, (1+w p)) := by
  have hweight (S : Finset ℕ) (hS : S ∈ Q.powerset) : 0 ≤ ∏ p ∈ S, w p :=
    prod_nonneg (fun p hp => hw p (mem_powerset.mp hS hp))
  calc
    _ = ∑ n ∈ Icc (A+1) B, ∑ S ∈ Q.powerset,
        (∏ p ∈ S, w p)*(if (∏ p ∈ S, p) ∣ n then (n : ℝ)⁻¹ else 0) := by
      apply sum_congr rfl
      intro n hn
      rw [prime_product_expansion Q hQ w n,sum_div]
      apply sum_congr rfl
      intro S hS
      split_ifs <;> simp [div_eq_mul_inv]
    _ = ∑ S ∈ Q.powerset, (∏ p ∈ S, w p)*
        ∑ n ∈ Icc (A+1) B with (∏ p ∈ S, p) ∣ n, (n : ℝ)⁻¹ := by
      rw [sum_comm]
      simp only [sum_filter,mul_sum]
    _ ≤ ∑ S ∈ Q.powerset, (∏ p ∈ S, w p)*
        (Real.log ((B : ℝ)/A)/((∏ p ∈ S, p : ℕ) : ℝ)+1/(A : ℝ)) := by
      apply sum_le_sum
      intro S hS
      exact mul_le_mul_of_nonneg_left
        (sum_inv_multiples_interval_le A B _ hA hAB
          (prod_pos (fun p hp => (hQ p (mem_powerset.mp hS hp)).pos))) (hweight S hS)
    _ = Real.log ((B : ℝ)/A)*(∑ S ∈ Q.powerset, ∏ p ∈ S, w p/(p : ℝ))+
        (1/(A : ℝ))*(∑ S ∈ Q.powerset, ∏ p ∈ S, w p) := by
      rw [mul_sum,mul_sum,← sum_add_distrib]
      apply sum_congr rfl
      intro S hS
      rw [prod_div_distrib,Nat.cast_prod]
      ring
    _ = _ := by rw [← prod_one_add,← prod_one_add]

end Erdos821.Sieve
