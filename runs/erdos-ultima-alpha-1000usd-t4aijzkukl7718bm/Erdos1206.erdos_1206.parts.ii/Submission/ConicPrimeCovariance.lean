import Submission.DualPrimeConditionalCounts

/-! The ordered conic contrast has zero main term at two distinct regular
primes. This is the finite-prime covariance step, not an infinite score theorem. -/
namespace Erdos1206.ConicPrimeCovariance
open Finset SquarefreeConicFamily QuadraticEqualDiscriminant DualPrimeConditionalCounts
  QuadraticConditionalCounts BoxDensityLimits PrimeBoxCRT
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def contrast (p : ℕ) (x : ℕ × ℕ) : ℝ :=
  ∑i,sign i*indicator (a i) (b i) (c i) p x

noncomputable def covariance (S : Finset ℕ) (N p q : ℕ) : ℝ :=
  ∑x∈positiveBox N (Head a b c S),contrast p x*contrast q x

lemma covariance_expand (S : Finset ℕ) (N p q : ℕ) :
    covariance S N p q=∑i,∑j,sign i*sign j*(jointCounts a b c S i j N p q).card := by
  dsimp only [covariance,contrast]
  simp_rw [sum_mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  calc
    _ = sign i*sign j*∑x∈positiveBox N (Head a b c S),
        indicator (a i) (b i) (c i) p x*indicator (a j) (b j) (c j) q x := by
      rw [mul_sum]
      apply sum_congr rfl
      intro x _
      ring
    _ = _ := by rw [sum_indicator_product]

lemma covariance_centered (S : Finset ℕ) (N : ℕ) {p q : ℕ}
    (hp : p.Prime) (hpbig : 1000000<p) :
    covariance S N p q=∑i,∑j,sign i*sign j*((jointCounts a b c S i j N p q).card-
      headDensity a b c S*localDensity (zeros (a i) (b i) (c i)) p*
        localDensity (zeros (a j) (b j) (c j)) q*(N:ℝ)^2) := by
  have hz : (∑i,∑j,sign i*sign j*(headDensity a b c S*
      localDensity (zeros (a i) (b i) (c i)) p*
        localDensity (zeros (a j) (b j) (c j)) q*(N:ℝ)^2))=0 := by
    calc
      _ = (headDensity a b c S*(N:ℝ)^2)*
        ((∑i,sign i*localDensity (zeros (a i) (b i) (c i)) p)*
          (∑j,sign j*localDensity (zeros (a j) (b j) (c j)) q)) := by
        rw [sum_mul_sum,mul_sum]
        apply sum_congr rfl
        intro i _
        rw [mul_sum]
        apply sum_congr rfl
        intro j _
        ring
      _ = 0 := by rw [local_cancellation hp hpbig,zero_mul,mul_zero]
  simp only [mul_sub,sum_sub_distrib]
  rw [hz,sub_zero,covariance_expand]

lemma off_diagonal_bound (S : Finset ℕ) (hS : ∀ r∈S, r.Prime) (N : ℕ) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q)
    (hpS : p∉S) (hqS : q∉S) (hpbig : 1000000<p) :
    |covariance S N p q| ≤ 16*error S N p q := by
  rw [covariance_centered S N hp hpbig]
  calc
    _ ≤ ∑i,|∑j,sign i*sign j*((jointCounts a b c S i j N p q).card-
        headDensity a b c S*localDensity (zeros (a i) (b i) (c i)) p*
          localDensity (zeros (a j) (b j) (c j)) q*(N:ℝ)^2)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑i,∑j,|sign i*sign j*((jointCounts a b c S i j N p q).card-
        headDensity a b c S*localDensity (zeros (a i) (b i) (c i)) p*
          localDensity (zeros (a j) (b j) (c j)) q*(N:ℝ)^2)| :=
      sum_le_sum (fun i _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑_i : Fin 4,∑_j : Fin 4,error S N p q := by
      apply sum_le_sum
      intro i _
      apply sum_le_sum
      intro j _
      rw [abs_mul,abs_mul,abs_sign,abs_sign,one_mul,one_mul]
      exact joint_discrepancy a b c S hS i j hp hq hpq hpS hqS N
    _ = _ := by simp; ring

lemma sign_sq (i : Fin 4) : sign i^2=1 := by rw [←sq_abs,abs_sign]; norm_num

lemma contrast_sq_le (p : ℕ) (x : ℕ × ℕ) :
    contrast p x^2 ≤ 4*∑i,indicator (a i) (b i) (c i) p x := by
  have hh := sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin 4)) sign
    (fun i => indicator (a i) (b i) (c i) p x)
  have hs (i : Fin 4) : indicator (a i) (b i) (c i) p x^2=indicator (a i) (b i) (c i) p x := by
    dsimp only [indicator]
    split_ifs <;> norm_num
  simpa only [contrast,sign_sq,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,hs] using hh

lemma sum_indicator (S : Finset ℕ) (i : Fin 4) (N p : ℕ) :
    (∑x∈positiveBox N (Head a b c S),indicator (a i) (b i) (c i) p x)=
      (counts a b c S i N p).card := by
  simp only [indicator,sum_boole]
  congr 1
  congr 1
  ext x
  simp only [positiveBox,counts,mem_filter]
  tauto

lemma diagonal_bound (S : Finset ℕ) (N p : ℕ) :
    covariance S N p p ≤ 4*∑i,((counts a b c S i N p).card:ℝ) := by
  have hh := sum_le_sum (fun x (_ : x∈positiveBox N (Head a b c S)) => contrast_sq_le p x)
  simp only [covariance,←pow_two] at ⊢
  calc
    _ ≤ ∑x∈positiveBox N (Head a b c S),4*∑i,indicator (a i) (b i) (c i) p x := hh
    _ = _ := by rw [←mul_sum,sum_comm]; simp only [sum_indicator]

#print axioms off_diagonal_bound
#print axioms diagonal_bound
end Erdos1206.ConicPrimeCovariance
