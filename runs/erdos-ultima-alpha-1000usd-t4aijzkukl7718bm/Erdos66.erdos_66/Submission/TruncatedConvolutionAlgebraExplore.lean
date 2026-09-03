import Submission.TruncatedProfileComparisonExplore

/-! Exact interval reflection and the boundary/middle split for natural
convolutions. No padded reflection interval is used. -/
namespace Erdos66TruncatedConvolutionAlgebra
open AdditiveCombinatorics Erdos66Fractional Erdos66Generating Erdos66Rounding
  Erdos66TruncatedProfileComparison Erdos66ClampedPrefixContinuation
  Erdos66ShortSupportSwapTail Erdos66ReflectionRoundingPatch
open scoped Classical
set_option maxHeartbeats 2600000

lemma sum_reflect_Ico (f : ℕ → ℝ) (n a b : ℕ) (hab : a ≤ b) (hbn : b ≤ n+1) :
    (∑ i∈Finset.Ico a b, f (n-i))=
      ∑ j∈Finset.Ico (n+1-b) (n+1-a), f j := by
  apply Finset.sum_bij (fun i _ ↦ n-i)
  · intro i hi
    simp only [Finset.mem_Ico] at hi ⊢
    omega
  · intro i hi j hj he
    simp only [Finset.mem_Ico] at hi hj
    omega
  · intro j hj
    refine ⟨n-j,?_,?_⟩
    · simp only [Finset.mem_Ico] at hj ⊢
      omega
    · simp only [Finset.mem_Ico] at hj
      dsimp only
      omega
  · intro _ _
    rfl

lemma sum_reflect_product_Ico (f g : ℕ → ℝ) (n a b : ℕ) (hab : a ≤ b) (hbn : b ≤ n+1) :
    (∑ i∈Finset.Ico a b, f i*g (n-i))=
      ∑ j∈Finset.Ico (n+1-b) (n+1-a), g j*f (n-j) := by
  have hh := sum_reflect_Ico (fun j ↦ g j*f (n-j)) n a b hab hbn
  rw [←hh]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_Ico.mp hi
  dsimp only
  rw [show n-(n-i)=i by omega,mul_comm]

lemma sumConv_three_parts (f g : ℕ → ℝ) (n m : ℕ) (hm : 2*m ≤ n+1) :
    sumConv f g n=
      (∑ i∈Finset.range m, f i*g (n-i))+
      (∑ i∈Finset.Ico m (n+1-m), f i*g (n-i))+
      ∑ i∈Finset.range m, g i*f (n-i) := by
  have h1 : m ≤ n+1-m := by omega
  have h2 : n+1-m ≤ n+1 := by omega
  have hh := Finset.sum_range_add_sum_Ico (fun i ↦ f i*g (n-i)) (show m ≤ n+1 by omega)
  have hs := Finset.sum_Ico_consecutive (f := fun i ↦ f i*g (n-i)) h1 h2
  have hr := sum_reflect_product_Ico f g n (n+1-m) (n+1) h2 le_rfl
  simp only [Nat.sub_self,Nat.Ico_zero_eq_range,
    show n+1-(n+1-m)=m by omega] at hr
  rw [←hs,hr] at hh
  simpa only [sumConv,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,add_assoc] using hh.symm

lemma reflected_interval_occupancy (A : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L)
    (n m a b : ℕ) (hab : a ≤ b) (hbn : b ≤ n+1) (hbm : b+m ≤ n+1) :
    (∑ i∈Finset.Ico a b, indicator A (n-i)) ≤ (b-a : ℕ)*profile m+2 := by
  rw [sum_reflect_Ico _ n a b hab hbn]
  have hs := (abs_le.mp (local_count_error A profile 1
    (brackets_count_discrepancy profile A hbr) (n+1-b) (n+1-a) (by omega))).2
  have hc : ((intervalPart A (n+1-b) (n+1-a)).card : ℝ)=
      ∑ i∈Finset.Ico (n+1-b) (n+1-a), indicator A i := by simp [intervalPart,indicator]
  rw [hc] at hs
  have hb : (∑ i∈Finset.Ico (n+1-b) (n+1-a), profile i) ≤ (b-a : ℕ)*profile m := by
    calc
      _ ≤ ∑ _i∈Finset.Ico (n+1-b) (n+1-a), profile m := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := Finset.mem_Ico.mp hi
        exact profile_antitone (by omega)
      _ = _ := by simp only [Finset.sum_const,Nat.card_Ico,nsmul_eq_mul]; congr 2; omega
  linarith

lemma boundary_indicator_profile (A : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L)
    (n m : ℕ) :
    (∑ i∈Finset.range m, indicator A i*profile (n-i)) ≤
      (∑ i∈Finset.range m, profile i*profile (n-i))+4 := by
  have hh := (abs_le.mp (truncated_mixed_comparison A hbr n 0 m)).2
  simpa only [Nat.Ico_zero_eq_range,add_comm] using (sub_le_iff_le_add.mp hh)

lemma boundary_profile_indicator (A : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L)
    (n m : ℕ) (hm : m ≤ n+1) :
    (∑ i∈Finset.range m, profile i*indicator A (n-i)) ≤
      (∑ i∈Finset.range m, profile i*profile (n-i))+4 := by
  have hh := (abs_le.mp (truncated_mixed_comparison A hbr n (n+1-m) (n+1))).2
  rw [sum_reflect_product_Ico (indicator A) profile n (n+1-m) (n+1) (by omega) le_rfl,
    sum_reflect_product_Ico profile profile n (n+1-m) (n+1) (by omega) le_rfl] at hh
  simp only [Nat.sub_self,show n+1-(n+1-m)=m by omega,Nat.Ico_zero_eq_range] at hh
  linarith

end Erdos66TruncatedConvolutionAlgebra
