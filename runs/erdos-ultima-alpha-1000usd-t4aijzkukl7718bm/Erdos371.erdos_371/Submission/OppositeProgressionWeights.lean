import Submission.PrimePowerKernelReplacement

/-! Uniform bounds for monotone weights on the two opposite progressions.
These bounds apply to the short-divisor terms, not to the prime kernel. -/
namespace Erdos371
open Finset

noncomputable def oppositeProgressionSign (p a v : ℕ) : ℝ :=
  if v=0 then 0 else
    (if p ∣ a*v-1 then 1 else 0) - (if p ∣ a*v+1 then 1 else 0)

lemma oppositeProgressionSign_prefix_count (p a X : ℕ) (ha : 0 < a) :
    (∑ v ∈ Icc 1 X, oppositeProgressionSign p a v) =
      (cofactorResidueCount (a*X) p a true : ℝ) - cofactorResidueCount (a*X) p a false := by
  unfold cofactorResidueCount
  rw [Nat.mul_div_cancel_left X ha]
  rw [← sum_boole,← sum_boole,← sum_sub_distrib]
  apply sum_congr rfl
  intro v hv
  simp only [oppositeProgressionSign,if_neg (show v≠0 by have := (mem_Icc.mp hv).1; omega),
    if_true,Bool.false_eq_true,if_false,Nat.mul_comm]

lemma oppositeProgressionSign_one_prefix (p X : ℕ) :
    (∑ v ∈ Icc 1 X, oppositeProgressionSign p 1 v) =
      (if p ∣ 0 then 1 else 0) + (if p ∣ 1 then 1 else 0) -
        (if p ∣ X then 1 else 0) - (if p ∣ X+1 then 1 else 0) := by
  induction X with
  | zero => simp
  | succ X ih =>
    rw [sum_Icc_succ_top (by omega),ih]
    simp only [oppositeProgressionSign,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,
      if_false,one_mul,Nat.add_sub_cancel]
    ring

/-- A bound independent of the modulus and of the progression coefficient. -/
theorem oppositeProgressionSign_prefix_bound (p a X : ℕ) (hp : 0 < p) (ha : 0 < a) :
    |∑ v ∈ Icc 1 X, oppositeProgressionSign p a v| ≤ 2 := by
  by_cases hX : X=0
  · simp [hX]
  by_cases ha1 : a=1
  · rw [ha1,oppositeProgressionSign_one_prefix]
    split_ifs <;> norm_num
  have ha2 : 2 ≤ a := by omega
  have hT : 0 < a*X := Nat.mul_pos ha (by omega)
  rw [oppositeProgressionSign_prefix_count p a X ha]
  have ht := bilinearCount_cofactor_positive (a*X-1) p a ha2
  rw [Nat.sub_add_cancel hT] at ht
  rw [← ht,← bilinearCount_cofactor_negative (a*X) p a ha]
  have he := bilinearCount_succ (a*X-1) a p
  rw [Nat.sub_add_cancel hT] at he
  rw [he,Nat.cast_add]
  have hb := bilinearCount_discrepancy_le_one (a*X-1) p a hp ha
  rw [Real.norm_eq_abs] at hb
  have hc : |((if a ∣ a*X ∧ p ∣ (a*X-1)+2 then 1 else 0 : ℕ) : ℝ)| ≤ 1 := by
    split_ifs <;> norm_num
  have htri := abs_sub ((bilinearCount (a*X-1) p a : ℝ)-bilinearCount (a*X-1) a p)
    ((if a ∣ a*X ∧ p ∣ (a*X-1)+2 then 1 else 0 : ℕ) : ℝ)
  rw [sub_sub] at htri
  exact htri.trans (by linarith)

lemma oppositeProgressionSign_range_bound (p a X : ℕ) (hp : 0 < p) (ha : 0 < a) :
    |∑ v ∈ range X, oppositeProgressionSign p a v| ≤ 2 := by
  cases X with
  | zero => simp
  | succ X =>
    have he : (∑ v ∈ range (X+1), oppositeProgressionSign p a v) =
        ∑ v ∈ Icc 1 X, oppositeProgressionSign p a v := by
      rw [show Icc 1 X = Ico 1 (X+1) by ext v; simp,
        sum_Ico_eq_sub _ (by omega)]
      simp [oppositeProgressionSign]
    rw [he]
    exact oppositeProgressionSign_prefix_bound p a X hp ha

/-- Abel summation with a monotone weight on a finite interval. -/
theorem monotone_weighted_sum_bound (g w : ℕ → ℝ) (K W : ℝ) (L X : ℕ)
    (hK : 0 ≤ K) (hW : 0 ≤ W)
    (hg : ∀ T, |∑ v ∈ range T, g v| ≤ K)
    (hw : ∀ v ∈ Ioc L X, 0 ≤ w v ∧ w v ≤ W)
    (hmono : MonotoneOn w (Set.Ioc L X) ∨ AntitoneOn w (Set.Ioc L X)) :
    |∑ v ∈ Ioc L X, w v*g v| ≤ 3*K*W := by
  by_cases hLX : L<X
  · have hLX1 : L+1 ≤ X := by omega
    have hLmem : L+1 ∈ Ioc L X := mem_Ioc.mpr ⟨by omega,hLX1⟩
    have hXmem : X ∈ Ioc L X := mem_Ioc.mpr ⟨hLX,le_rfl⟩
    have hends (v : ℕ) (hv : v ∈ Ioc L X) (T : ℕ) :
        |w v*(∑ j ∈ range T, g j)| ≤ K*W := by
      rw [abs_mul,abs_of_nonneg (hw v hv).1]
      exact (mul_le_mul_of_nonneg_left (hg T) (hw v hv).1).trans
        (by nlinarith [(hw v hv).2])
    have hvar : (∑ v ∈ Ioc L (X-1), |w (v+1)-w v|) ≤ W := by
      have hmem (v : ℕ) (hv : v ∈ Ioc L (X-1)) :
          v ∈ Set.Ioc L X ∧ v+1 ∈ Set.Ioc L X := by
        have := mem_Ioc.mp hv
        constructor <;> constructor <;> omega
      have hsum : (∑ v ∈ Ioc L (X-1), (w (v+1)-w v)) = w X-w (L+1) := by
        rw [show Ioc L (X-1) = Ico (L+1) X by ext v; simp; omega]
        exact sum_Ico_sub w hLX1
      rcases hmono with hmono | hmono
      · have he (v : ℕ) (hv : v ∈ Ioc L (X-1)) :
            |w (v+1)-w v| = w (v+1)-w v :=
          abs_of_nonneg (sub_nonneg.mpr (hmono (hmem v hv).1 (hmem v hv).2 (by omega)))
        rw [sum_congr rfl he,hsum]
        linarith [(hw (L+1) hLmem).1,(hw X hXmem).2]
      · have he (v : ℕ) (hv : v ∈ Ioc L (X-1)) :
            |w (v+1)-w v| = -(w (v+1)-w v) :=
          abs_of_nonpos (sub_nonpos.mpr (hmono (hmem v hv).1 (hmem v hv).2 (by omega)))
        rw [sum_congr rfl he,sum_neg_distrib,hsum]
        linarith [(hw X hXmem).1,(hw (L+1) hLmem).2]
    have hmiddle : |∑ v ∈ Ioc L (X-1), (w (v+1)-w v)*(∑ j ∈ range (v+1), g j)| ≤ K*W := by
      calc
        _ ≤ ∑ v ∈ Ioc L (X-1), |(w (v+1)-w v)*(∑ j ∈ range (v+1), g j)| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ v ∈ Ioc L (X-1), |w (v+1)-w v| * K := by
          apply sum_le_sum
          intro v hv
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hg (v+1)) (abs_nonneg _)
        _ ≤ K*W := by rw [← sum_mul]; nlinarith
    have he := sum_Ioc_by_parts w g hLX
    simp only [smul_eq_mul] at he
    rw [he]
    exact ((abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)).trans
      (by linarith [hends X hXmem (X+1),hends (L+1) hLmem (L+1)])
  · have he : Ioc L X = ∅ := Ioc_eq_empty (by omega)
    rw [he,sum_empty,abs_zero]
    positivity

/-- Monotone nonnegative weights cost only their supremum, not the length
of the progression or the modulus. -/
theorem oppositeProgressionSign_weighted_bound (p a L X : ℕ) (hp : 0 < p) (ha : 0 < a)
    (w : ℕ → ℝ) (W : ℝ) (hW : 0 ≤ W)
    (hw : ∀ v ∈ Ioc L X, 0 ≤ w v ∧ w v ≤ W)
    (hmono : MonotoneOn w (Set.Ioc L X) ∨ AntitoneOn w (Set.Ioc L X)) :
    |∑ v ∈ Ioc L X, w v*oppositeProgressionSign p a v| ≤ 6*W := by
  simpa only [show (3 : ℝ)*2=6 by norm_num] using
    monotone_weighted_sum_bound (oppositeProgressionSign p a) w 2 W L X
      (by norm_num) hW (fun T => oppositeProgressionSign_range_bound p a T hp ha) hw hmono

#print axioms oppositeProgressionSign_prefix_bound
#print axioms oppositeProgressionSign_weighted_bound
end Erdos371
