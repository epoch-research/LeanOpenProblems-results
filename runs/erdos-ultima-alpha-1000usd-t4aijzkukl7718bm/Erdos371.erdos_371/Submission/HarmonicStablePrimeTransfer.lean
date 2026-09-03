import Submission.HarmonicPrimeGapTransfer
import Submission.HarmonicDilationTransfer

/-! Harmonic transfer with the actual adjacent endpoint. The replacement of
N/p by N is valid here because both sums use the same harmonic denominator. -/
namespace Erdos371.FiniteInformation
open Finset Filter BlockPrimes EntropyScales
open scoped Topology
set_option autoImplicit false

lemma sum_Icc_one_eq_sum_range (N : ℕ) (F : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, F n) = ∑ n ∈ range N, F (n+1) := by
  apply sum_nbij' (fun n => n-1) (fun n => n+1)
  · intro n hn
    have := mem_Icc.mp hn
    simp only [mem_range]
    omega
  · intro n hn
    have := mem_range.mp hn
    simp only [mem_Icc]
    omega
  · intro n hn
    have := mem_Icc.mp hn
    omega
  · intro n hn
    omega
  · intro n hn
    have := mem_Icc.mp hn
    congr 1
    omega

lemma harmonic_range_Icc_sum_error (N : ℕ) (F : ℕ → ℝ) (hF : ∀ n, |F n| ≤ 1) :
    |(∑ n ∈ range (N+1), F n/(n+1 : ℝ))-
      (∑ n ∈ Icc 1 (N+1), F n/(n : ℝ))| ≤ 2 := by
  rw [sum_Icc_one_eq_sum_range]
  have he : (∑ n ∈ range (N+1), F n/(n+1 : ℝ))-
      (∑ n ∈ range (N+1), F (n+1)/((n+1 : ℕ) : ℝ)) =
        F 0-F (N+1)/(N+1 : ℝ)-∑ k ∈ range N, F (k+1)/((k+1)*(k+2) : ℝ) := by
    rw [sum_range_succ' (fun n => F n/(n+1 : ℝ)),sum_range_succ]
    simp only [Nat.cast_add,Nat.cast_one,Nat.cast_zero,zero_add,div_one]
    have hterm (k : ℕ) : F (k+1)/(k+1+1 : ℝ)-F (k+1)/(k+1 : ℝ) =
        -(F (k+1)/((k+1)*(k+2) : ℝ)) := by
      have h₁ : (k+1 : ℝ) ≠ 0 := by positivity
      have h₂ : (k+2 : ℝ) ≠ 0 := by positivity
      field_simp
      <;> ring
    have hs := sum_congr (s₁ := range N) rfl (fun k _ => hterm k)
    rw [sum_sub_distrib,sum_neg_distrib] at hs
    linarith
  rw [he]
  have ht : |∑ k ∈ range N, F (k+1)/((k+1)*(k+2) : ℝ)| ≤ 1-1/(N+1 : ℝ) := by
    rw [← reciprocal_product_sum]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro k hk
    rw [abs_div,abs_of_pos (by positivity : (0 : ℝ)<(k+1)*(k+2))]
    exact div_le_div_of_nonneg_right (hF (k+1)) (by positivity)
  have hend : |F (N+1)/(N+1 : ℝ)| ≤ 1/(N+1 : ℝ) := by
    rw [abs_div,abs_of_pos (by positivity : (0 : ℝ)<N+1)]
    exact div_le_div_of_nonneg_right (hF (N+1)) (by positivity)
  have hb₁ := abs_sub (F 0) (F (N+1)/(N+1 : ℝ))
  have hb₂ := abs_sub (F 0-F (N+1)/(N+1 : ℝ))
    (∑ k ∈ range N, F (k+1)/((k+1)*(k+2) : ℝ))
  linarith [hF 0]

noncomputable def harmonicMean (N : ℕ) (F : ℕ → ℝ) : ℝ :=
  (∑ n ∈ Icc 1 N, F n/(n : ℝ))/(harmonic N : ℝ)

lemma harmonicMean_range_error (N : ℕ) (F : ℕ → ℝ) (hF : ∀ n, |F n| ≤ 1) :
    |harmonicRangeMean (N+1) F-harmonicMean (N+1) F| ≤ 2/(harmonic (N+1) : ℝ) := by
  rw [harmonicRangeMean,harmonicMean,← sub_div,abs_div,abs_of_pos (harmonic_real_pos N)]
  exact div_le_div_of_nonneg_right (harmonic_range_Icc_sum_error N F hF) (harmonic_real_pos N).le

lemma harmonicMean_abs_le (N : ℕ) (F : ℕ → ℝ) (hF : ∀ n, |F n| ≤ 1) :
    |harmonicMean (N+1) F| ≤ 1 := by
  rw [harmonicMean,abs_div,abs_of_pos (harmonic_real_pos N)]
  apply (div_le_one (harmonic_real_pos N)).mpr
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro n hn
  rw [abs_div,abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n),← one_div]
  exact div_le_div_of_nonneg_right (hF n) (Nat.cast_nonneg n)

noncomputable def harmonicGapDiscrepancy {A : Type*}
    (N p : ℕ) (L : ℕ → A) (C : A → A → ℝ) : ℝ :=
  p*harmonicMean N (fun n => if p ∣ n then C (L n) (L (n+p)) else 0)-
    harmonicMean N (fun n => C (L n) (L (n+p)))

lemma harmonicGapDiscrepancy_range_error {A : Type*} (N p : ℕ)
    (L : ℕ → A) (C : A → A → ℝ) (hC : ∀ a b, |C a b| ≤ 1) :
    |harmonicRangeGapDiscrepancy (N+1) p L C-harmonicGapDiscrepancy (N+1) p L C| ≤
      2*(p+1 : ℝ)/(harmonic (N+1) : ℝ) := by
  have hc := harmonicMean_range_error N
    (fun n => if p ∣ n then C (L n) (L (n+p)) else 0)
    (fun n => by dsimp only; split_ifs <;> simp_all)
  have hu := harmonicMean_range_error N (fun n => C (L n) (L (n+p))) (fun n => hC _ _)
  let V (n : ℕ) := C (L n) (L (n+p))
  have he : harmonicRangeGapDiscrepancy (N+1) p L C-harmonicGapDiscrepancy (N+1) p L C =
      p*(harmonicRangeMean (N+1) (fun n => if p ∣ n then V n else 0)-
        harmonicMean (N+1) (fun n => if p ∣ n then V n else 0))-
      (harmonicRangeMean (N+1) V-harmonicMean (N+1) V) := by
    dsimp [harmonicRangeGapDiscrepancy,harmonicGapDiscrepancy,V]
    ring
  rw [he]
  apply (abs_sub _ _).trans
  rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
  exact (add_le_add (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg p)) hu).trans_eq (by ring)

/-- One common finite scale controls the actual Icc harmonic discrepancy. -/
theorem harmonic_prime_gap_transfer {A : Type*} [Fintype A]
    (H₀ : ℕ) (hH₀ : 8 ≤ H₀) (ε : ℝ) (hε : 0 < ε) :
    ∃ K > 0, ∀ᶠ N : ℕ in atTop, ∀ L : ℕ → A, ∃ n < K,
      ∀ C : A → A → ℝ, (∀ a b, |C a b| ≤ 1) →
        |(∑ p ∈ halfBlockPrimes (factorialScale H₀ n), harmonicGapDiscrepancy (N+1) p L C) /
          (halfBlockPrimes (factorialScale H₀ n)).card| < ε := by
  obtain ⟨K,hK,htrans⟩ := harmonic_range_prime_gap_transfer (A := A) H₀ hH₀ (ε/2) (by positivity)
  let B := (range K).sup (factorialScale H₀)
  have ht : Tendsto (fun N : ℕ => 2*(B+1 : ℝ)/(harmonic (N+1) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop harmonic_real_tendsto
  refine ⟨K,hK,?_⟩
  filter_upwards [htrans,ht.eventually_lt_const (by positivity : (0 : ℝ)<ε/2)] with N htrans ht
  intro L
  obtain ⟨n,hn,hscale⟩ := htrans L
  refine ⟨n,hn,?_⟩
  intro C hC
  let S := halfBlockPrimes (factorialScale H₀ n)
  have hH : factorialScale H₀ n ≤ B := le_sup (mem_range.mpr hn)
  have hS : S.Nonempty := halfBlockPrimes_nonempty _
    (le_trans (by omega : 4 ≤ H₀) (factorialScale_ge H₀ n))
  have herr : |(∑ p ∈ S, (harmonicRangeGapDiscrepancy (N+1) p L C-
      harmonicGapDiscrepancy (N+1) p L C))/(S.card : ℝ)| ≤
        2*(B+1 : ℝ)/(harmonic (N+1) : ℝ) := by
    apply abs_finset_average_le S hS
    intro p hp
    have hpH := (mem_halfBlockPrimes.mp hp).2
    have hpB : p ≤ B := by omega
    apply (harmonicGapDiscrepancy_range_error N p L C hC).trans
    exact div_le_div_of_nonneg_right (by exact_mod_cast (show 2*(p+1) ≤ 2*(B+1) by omega))
      (harmonic_real_pos N).le
  have hs := hscale C hC
  change |(∑ p ∈ S, harmonicRangeGapDiscrepancy (N+1) p L C)/(S.card : ℝ)| < ε/2 at hs
  rw [sum_sub_distrib,sub_div,abs_sub_comm] at herr
  have htri := abs_sub_le
    ((∑ p ∈ S, harmonicGapDiscrepancy (N+1) p L C)/(S.card : ℝ))
    ((∑ p ∈ S, harmonicRangeGapDiscrepancy (N+1) p L C)/(S.card : ℝ)) 0
  simp only [sub_zero] at htri
  change |(∑ p ∈ S, harmonicGapDiscrepancy (N+1) p L C)/(S.card : ℝ)| < ε
  linarith

lemma harmonic_stable_gap_error {A : Type*} (N p : ℕ) (hp : 0 < p)
    (L : ℕ → A) (C : A → A → ℝ) (hC : ∀ a b, |C a b| ≤ 1)
    (hL : ∀ m, 0 < m → L (p*m)=L m) :
    |harmonicGapDiscrepancy (N+1) p L C-
      (harmonicMean (N+1) (fun m => C (L m) (L (m+1)))-
        harmonicMean (N+1) (fun m => C (L m) (L (m+p))))| ≤
      p/(harmonic (N+1) : ℝ) := by
  have hd : p*harmonicMean (N+1) (fun m => if p ∣ m then C (L m) (L (m+p)) else 0) =
      (∑ m ∈ Icc 1 ((N+1)/p), C (L m) (L (m+1))/(m : ℝ))/(harmonic (N+1) : ℝ) := by
    unfold harmonicMean
    simp only [ite_div,zero_div]
    rw [← mul_div_assoc,harmonic_dilation_sum p (N+1) hp]
    congr 1
    apply sum_congr rfl
    intro m hm
    have hm0 : 0 < m := (mem_Icc.mp hm).1
    rw [hL m hm0,show p*m+p=p*(m+1) by ring,hL (m+1) (by omega)]
  unfold harmonicGapDiscrepancy
  rw [hd,sub_sub_sub_cancel_right,harmonicMean,← sub_div,abs_div,
    abs_of_pos (harmonic_real_pos N),abs_sub_comm]
  exact div_le_div_of_nonneg_right
    (harmonic_div_endpoint_bound p (N+1) hp (fun m => C (L m) (L (m+1))) (fun m => hC _ _))
    (harmonic_real_pos N).le

/-- For stable finite labels the adjacent harmonic mean really has endpoint
N+1, not (N+1)/p. The prime-gap skew mean itself remains unevaluated. -/
theorem stable_harmonic_prime_transfer {A : Type*} [Fintype A]
    (H₀ : ℕ) (hH₀ : 8 ≤ H₀) (ε : ℝ) (hε : 0 < ε) :
    ∃ K > 0, ∀ᶠ N : ℕ in atTop, ∀ L : ℕ → A,
      (∀ p, 0 < p → p ≤ (range K).sup (factorialScale H₀) →
        ∀ m, 0 < m → L (p*m)=L m) → ∃ n < K,
      ∀ C : A → A → ℝ, (∀ a b, |C a b| ≤ 1) →
        |harmonicMean (N+1) (fun m => C (L m) (L (m+1)))-
          (∑ p ∈ halfBlockPrimes (factorialScale H₀ n),
            harmonicMean (N+1) (fun m => C (L m) (L (m+p)))) /
              (halfBlockPrimes (factorialScale H₀ n)).card| < ε := by
  obtain ⟨K,hK,htrans⟩ := harmonic_prime_gap_transfer (A := A) H₀ hH₀ (ε/2) (by positivity)
  let B := (range K).sup (factorialScale H₀)
  have ht : Tendsto (fun N : ℕ => (B : ℝ)/(harmonic (N+1) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop harmonic_real_tendsto
  refine ⟨K,hK,?_⟩
  filter_upwards [htrans,ht.eventually_lt_const (by positivity : (0 : ℝ)<ε/2)] with N htrans ht
  intro L hL
  obtain ⟨n,hn,hscale⟩ := htrans L
  refine ⟨n,hn,?_⟩
  intro C hC
  let S := halfBlockPrimes (factorialScale H₀ n)
  have hH : factorialScale H₀ n ≤ B := le_sup (mem_range.mpr hn)
  have hS : S.Nonempty := halfBlockPrimes_nonempty _
    (le_trans (by omega : 4 ≤ H₀) (factorialScale_ge H₀ n))
  let V (p : ℕ) := harmonicMean (N+1) (fun m => C (L m) (L (m+p)))
  have he : |(∑ p ∈ S, (harmonicGapDiscrepancy (N+1) p L C-(V 1-V p)))/(S.card : ℝ)| ≤
      (B : ℝ)/(harmonic (N+1) : ℝ) := by
    apply abs_finset_average_le S hS
    intro p hp
    obtain ⟨hpp,hpH⟩ := mem_halfBlockPrimes.mp hp
    have hpB : p ≤ B := by omega
    exact (harmonic_stable_gap_error N p hpp.pos L C hC (hL p hpp.pos hpB)).trans
      (div_le_div_of_nonneg_right (by exact_mod_cast hpB) (harmonic_real_pos N).le)
  have heq : (∑ p ∈ S, (V 1-V p))/(S.card : ℝ) = V 1-(∑ p ∈ S,V p)/(S.card : ℝ) := by
    rw [sum_sub_distrib,sub_div,sum_const,nsmul_eq_mul]
    have hcard : (S.card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hS).ne'
    field_simp
  rw [sum_sub_distrib,sub_div,heq,abs_sub_comm] at he
  have hs := hscale C hC
  change |(∑ p ∈ S,harmonicGapDiscrepancy (N+1) p L C)/(S.card : ℝ)| < ε/2 at hs
  have htri := abs_sub_le (V 1-(∑ p ∈ S,V p)/(S.card : ℝ))
    ((∑ p ∈ S,harmonicGapDiscrepancy (N+1) p L C)/(S.card : ℝ)) 0
  simp only [sub_zero] at htri
  change |V 1-(∑ p ∈ S,V p)/(S.card : ℝ)| < ε
  linarith

#print axioms harmonic_range_Icc_sum_error
#print axioms harmonic_prime_gap_transfer
#print axioms stable_harmonic_prime_transfer
end Erdos371.FiniteInformation
