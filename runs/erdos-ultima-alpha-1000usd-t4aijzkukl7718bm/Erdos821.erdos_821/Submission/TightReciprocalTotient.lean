import Submission.IntervalTotientScales

/-!
# A sharper reciprocal-totient Euler-product bound

The finite product through 299 and a telescoping tail give 39/20.
Consequently the even-cofactor harmonic coefficient is 13/10.
These estimates do not settle Erdős 821.
-/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821.Sieve
open AnalyticSieve
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000

lemma reciprocal_totient_euler_product_le_thirty_nine_twentieths (A : ℕ) :
    (∏ p ∈ (A+1).primesBelow, (1+1/((p : ℝ)*((p : ℝ)-1)))) ≤ (39/20 : ℝ) := by
  let P := (A+1).primesBelow
  let f : ℕ → ℝ := fun p => 1+1/((p : ℝ)*((p : ℝ)-1))
  have hf (p : ℕ) (hp : p.Prime) : 1 ≤ f p := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hh : 0 ≤ 1/((p : ℝ)*((p : ℝ)-1)) :=
      div_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
    dsimp [f]
    linarith
  have hsmall : (∏ p ∈ P with p ≤ 299, f p) ≤ (∏ p ∈ (300 : ℕ).primesBelow, f p) := by
    have hsub : P.filter (fun p => p ≤ 299) ⊆ (300 : ℕ).primesBelow := by
      intro p hp
      obtain ⟨hpP,hp299⟩ := mem_filter.mp hp
      exact Nat.mem_primesBelow.mpr ⟨by omega,(Nat.mem_primesBelow.mp hpP).2⟩
    have hrest : 1 ≤ ∏ p ∈ (300 : ℕ).primesBelow \ P.filter (fun p => p ≤ 299), f p := by
      calc
        _ = ∏ _p ∈ (300 : ℕ).primesBelow \ P.filter (fun p => p ≤ 299), (1 : ℝ) := by simp
        _ ≤ _ := Finset.prod_le_prod (fun _ _ => by norm_num)
          (fun p hp => hf p (Nat.mem_primesBelow.mp (mem_sdiff.mp hp).1).2)
    calc
      _ = 1*(∏ p ∈ P with p ≤ 299, f p) := by ring
      _ ≤ (∏ p ∈ (300 : ℕ).primesBelow \ P.filter (fun p => p ≤ 299), f p) *
          (∏ p ∈ P with p ≤ 299, f p) :=
        mul_le_mul_of_nonneg_right hrest (Finset.prod_nonneg (fun p hp =>
          (by norm_num : (0 : ℝ) ≤ 1).trans (hf p (Nat.mem_primesBelow.mp (mem_filter.mp hp).1).2)))
      _ = _ := Finset.prod_sdiff hsub
  have htailSum : (∑ p ∈ P with ¬p ≤ 299, 1/((p : ℝ)*((p : ℝ)-1))) ≤ 1/299 := by
    have hsub : P.filter (fun p => ¬p ≤ 299) ⊆ Icc 300 (A+1) := by
      intro p hp
      obtain ⟨hpP,hp299⟩ := mem_filter.mp hp
      exact mem_Icc.mpr ⟨by omega,by have := (Nat.mem_primesBelow.mp hpP).1; omega⟩
    apply le_trans (sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => ?_))
      (sum_reciprocal_successive_tail 299 (A+1) (by norm_num))
    have hpR : (300 : ℝ) ≤ p := by exact_mod_cast (mem_Icc.mp hp).1
    exact div_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
  have htail : (∏ p ∈ P with ¬p ≤ 299, f p) ≤ (299/298 : ℝ) := by
    calc
      _ ≤ ∏ p ∈ P with ¬p ≤ 299, Real.exp (1/((p : ℝ)*((p : ℝ)-1))) := by
        apply Finset.prod_le_prod
        · intro p hp
          exact (by norm_num : (0 : ℝ) ≤ 1).trans (hf p (Nat.mem_primesBelow.mp (mem_filter.mp hp).1).2)
        · intro p hp
          simpa only [f,add_comm] using Real.add_one_le_exp (1/((p : ℝ)*((p : ℝ)-1)))
      _ = Real.exp (∑ p ∈ P with ¬p ≤ 299, 1/((p : ℝ)*((p : ℝ)-1))) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (1/299) := Real.exp_le_exp.mpr htailSum
      _ ≤ 299/298 := by
        convert Real.exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 1/299) (by norm_num : (1/299 : ℝ) < 1) using 1
        norm_num
  have hsmallExact : (∏ p ∈ (300 : ℕ).primesBelow, f p) * (299/298 : ℝ) ≤ (39/20 : ℝ) := by
    have hr :
        (∏ p ∈ (300 : ℕ).primesBelow, (1+1/((p : ℚ)*((p : ℚ)-1)))) *
          (299/298 : ℚ) ≤ 39/20 := by
      decide +kernel
    have hh := (Rat.cast_le (K := ℝ)).mpr hr
    simpa only [f, Rat.cast_mul, Rat.cast_div, Rat.cast_add, Rat.cast_sub, Rat.cast_one,
      Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_prod] using hh
  calc
    _ = (∏ p ∈ P with p ≤ 299, f p)*(∏ p ∈ P with ¬p ≤ 299, f p) :=
      (Finset.prod_filter_mul_prod_filter_not P (fun p => p ≤ 299) f).symm
    _ ≤ (∏ p ∈ (300 : ℕ).primesBelow, f p)*(299/298 : ℝ) :=
      mul_le_mul hsmall htail (Finset.prod_nonneg (fun p hp =>
        (by norm_num : (0 : ℝ) ≤ 1).trans (hf p (Nat.mem_primesBelow.mp (mem_filter.mp hp).1).2)))
        (Finset.prod_nonneg (fun p hp => (by norm_num : (0 : ℝ) ≤ 1).trans (hf p (Nat.mem_primesBelow.mp hp).2)))
    _ ≤ _ := hsmallExact

theorem sum_reciprocal_totient_le_thirty_nine_twentieths_harmonic (A : ℕ) :
    (∑ n ∈ Icc 1 A, 1/(n.totient : ℝ)) ≤ (39/20 : ℝ)*(harmonic A : ℝ) := by
  let w : ℕ → ℝ := fun p => 1/((p : ℝ)-1)
  let Q := (A+1).primesBelow
  have hw (p : ℕ) (hp : p.Prime) : 0 ≤ w p := by
    have h : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    dsimp [w]
    exact div_nonneg (by norm_num) (by linarith)
  have hprod : (∏ p ∈ Q, (1+w p/(p : ℝ))) ≤ (39/20 : ℝ) := by
    convert reciprocal_totient_euler_product_le_thirty_nine_twentieths A using 1
    apply Finset.prod_congr rfl
    intro p hp
    dsimp [w]
    rw [div_div, mul_comm]
  have havg := harmonic_average_prime_product_le A w (fun p hp => hw p (Nat.mem_primesBelow.mp hp).2)
  have heq (n : ℕ) (hn : n ∈ Icc 1 A) :
      1/(n.totient : ℝ) = (∏ p ∈ n.primeFactors, (1+w p))/(n : ℝ) := by
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show 0 < n from (mem_Icc.mp hn).1).ne'
    have hprod' : ∏ p ∈ n.primeFactors, (1+w p) = (n : ℝ)/n.totient := by
      rw [totient_ratio_eq_prime_product n (mem_Icc.mp hn).1]
      apply prod_congr rfl
      intro p hp
      have hpR : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
      dsimp [w]
      have hp1 : (p : ℝ)-1 ≠ 0 := ne_of_gt (by linarith)
      field_simp [hp1]
      ring
    rw [hprod']
    field_simp
  have hH : 0 ≤ (harmonic A : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    exact sum_nonneg (fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n))
  calc
    _ = ∑ n ∈ Icc 1 A, (∏ p ∈ n.primeFactors, (1+w p))/(n : ℝ) := sum_congr rfl heq
    _ ≤ (harmonic A : ℝ)*(∏ p ∈ Q, (1+w p/(p : ℝ))) := havg
    _ ≤ (harmonic A : ℝ)*(39/20 : ℝ) := mul_le_mul_of_nonneg_left hprod hH
    _ = _ := mul_comm _ _


theorem even_reciprocal_totient_le_thirteen_tenths_harmonic (A : ℕ) :
    evenReciprocalTotient A ≤ (13/10 : ℝ)*(harmonic A : ℝ) := by
  have h := sum_reciprocal_totient_le_thirty_nine_twentieths_harmonic A
  have he := even_reciprocal_totient_le_two_thirds A
  linarith

end Erdos821.Sieve
