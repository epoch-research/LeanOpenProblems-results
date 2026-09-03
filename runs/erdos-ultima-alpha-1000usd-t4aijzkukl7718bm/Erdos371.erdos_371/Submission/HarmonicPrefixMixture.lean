import Submission.FiniteMixtureLaw
import Submission.FiniteEndpointTransfer

/-! Exact positive-mixture representation of harmonic sampling. -/
namespace Erdos371.FiniteInformation
open Finset Filter
open scoped Topology
set_option autoImplicit false

lemma harmonic_real_sum (N : ℕ) :
    (harmonic N : ℝ) = ∑ n ∈ range N, (1 : ℝ)/(n+1) := by
  simp [harmonic, Rat.cast_sum, one_div]

lemma harmonic_real_pos (N : ℕ) : 0 < (harmonic (N+1) : ℝ) := by
  exact_mod_cast harmonic_pos (Nat.succ_ne_zero N)

lemma harmonic_real_tail (N : ℕ) :
    (harmonic (N+1) : ℝ) = 1+∑ k ∈ range N, (1 : ℝ)/(k+2) := by
  rw [harmonic_real_sum,sum_range_succ']
  simp only [Nat.cast_add,Nat.cast_one,zero_add,div_one]
  ring

lemma harmonic_prefix_identity (N : ℕ) (F : ℕ → ℝ) :
    (∑ n ∈ range (N+1), F n/(n+1 : ℝ)) =
      prefixMean (N+1) F + ∑ k ∈ range N, prefixMean (k+1) F/(k+2 : ℝ) := by
  induction N with
  | zero => simp [prefixMean]
  | succ N ih =>
    rw [sum_range_succ,ih,sum_range_succ]
    have hN : (N+1 : ℝ) ≠ 0 := by positivity
    have hN' : (N+2 : ℝ) ≠ 0 := by positivity
    have he : prefixMean (N+1+1) F =
        ((N+1 : ℝ)*prefixMean (N+1) F+F (N+1))/(N+2 : ℝ) := by
      unfold prefixMean
      rw [sum_range_succ]
      simp only [Nat.cast_add,Nat.cast_one]
      field_simp
      <;> ring
    rw [he]
    simp only [Nat.cast_add,Nat.cast_one]
    field_simp
    <;> ring

def harmonicPrefixLength (N : ℕ) (i : Fin (N+1)) : ℕ :=
  if i.val=0 then N+1 else i.val

noncomputable def harmonicPrefixWeight (N : ℕ) (i : Fin (N+1)) : ℝ :=
  if i.val=0 then 1 else 1/(i.val+1 : ℝ)

lemma harmonicPrefixLength_pos (N : ℕ) (i : Fin (N+1)) : 0 < harmonicPrefixLength N i := by
  unfold harmonicPrefixLength
  split_ifs <;> omega

lemma harmonicPrefixWeight_nonneg (N : ℕ) (i : Fin (N+1)) : 0 ≤ harmonicPrefixWeight N i := by
  unfold harmonicPrefixWeight
  split_ifs <;> positivity

lemma harmonicPrefixWeight_sum (N : ℕ) :
    ∑ i, harmonicPrefixWeight N i = (harmonic (N+1) : ℝ) := by
  rw [Fin.sum_univ_succ,harmonic_real_tail]
  simp only [harmonicPrefixWeight,Fin.val_zero,if_true,Fin.val_succ,
    Nat.add_eq_zero_iff,one_ne_zero,and_false,if_false,Nat.cast_add,Nat.cast_one]
  rw [← sum_range (n := N) (fun k => (1 : ℝ)/(k+1+1))]
  congr 1
  apply sum_congr rfl
  intro k hk
  ring

noncomputable def harmonicPrefixLaw (N : ℕ) : Law (Fin (N+1)) where
  mass i := harmonicPrefixWeight N i / (harmonic (N+1) : ℝ)
  nonneg i := div_nonneg (harmonicPrefixWeight_nonneg N i) (harmonic_real_pos N).le
  total := by
    rw [← sum_div,harmonicPrefixWeight_sum,div_self (harmonic_real_pos N).ne']

lemma mean_harmonicPrefixLaw (N : ℕ) (G : ℕ → ℝ) :
    mean (harmonicPrefixLaw N) (fun i => G (harmonicPrefixLength N i)) =
      (G (N+1)+∑ k ∈ range N, G (k+1)/(k+2 : ℝ))/(harmonic (N+1) : ℝ) := by
  unfold mean harmonicPrefixLaw
  simp only [div_mul_eq_mul_div,← sum_div]
  congr 1
  rw [Fin.sum_univ_succ]
  simp only [harmonicPrefixWeight,harmonicPrefixLength,Fin.val_zero,if_true,Fin.val_succ,
    Nat.add_eq_zero_iff,one_ne_zero,and_false,if_false,one_mul,one_div]
  rw [← sum_range (n := N) (fun k => ((k+1 : ℕ)+1 : ℝ)⁻¹*G (k+1))]
  congr 1
  apply sum_congr rfl
  intro k hk
  simp only [Nat.cast_add,Nat.cast_one]
  ring

lemma harmonicPrefixLaw_representation (N : ℕ) (F : ℕ → ℝ) :
    mean (harmonicPrefixLaw N) (fun i => prefixMean (harmonicPrefixLength N i) F) =
      (∑ n ∈ range (N+1), F n/(n+1 : ℝ))/(harmonic (N+1) : ℝ) := by
  rw [mean_harmonicPrefixLaw N (fun k => prefixMean k F),← harmonic_prefix_identity]

lemma reciprocal_product_sum (N : ℕ) :
    (∑ k ∈ range N, (1 : ℝ)/((k+1)*(k+2))) = 1-1/(N+1 : ℝ) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [sum_range_succ,ih]
    simp only [Nat.cast_add,Nat.cast_one]
    have h₁ : (N+1 : ℝ) ≠ 0 := by positivity
    have h₂ : (N+2 : ℝ) ≠ 0 := by positivity
    field_simp
    <;> ring

/-- Exact reciprocal-prefix moment. It gives an O(1/H_N) bound for any
componentwise error of size O(1/k), including fixed cyclic rounding costs. -/
lemma harmonicPrefixLaw_reciprocal_length (N : ℕ) :
    mean (harmonicPrefixLaw N) (fun i => (1 : ℝ)/harmonicPrefixLength N i) =
      1/(harmonic (N+1) : ℝ) := by
  rw [mean_harmonicPrefixLaw N (fun k => (1 : ℝ)/k)]
  have he (k : ℕ) : (1/(k+1 : ℝ))/(k+2 : ℝ) = 1/((k+1)*(k+2) : ℝ) := div_div _ _ _
  simp only [he,reciprocal_product_sum,Nat.cast_add,Nat.cast_one]
  congr 1
  ring

lemma harmonic_real_tendsto : Tendsto (fun N : ℕ => (harmonic (N+1) : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono (fun N => log_add_one_le_harmonic (N+1))
  exact Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp
    (tendsto_add_atTop_nat 2))

lemma harmonicPrefixLaw_reciprocal_length_zero :
    Tendsto (fun N : ℕ => mean (harmonicPrefixLaw N)
      (fun i => (1 : ℝ)/harmonicPrefixLength N i)) atTop (𝓝 0) := by
  simp_rw [harmonicPrefixLaw_reciprocal_length]
  exact tendsto_const_nhds.div_atTop harmonic_real_tendsto

#print axioms harmonicPrefixLaw_representation
#print axioms harmonicPrefixLaw_reciprocal_length
#print axioms harmonicPrefixLaw_reciprocal_length_zero
end Erdos371.FiniteInformation
