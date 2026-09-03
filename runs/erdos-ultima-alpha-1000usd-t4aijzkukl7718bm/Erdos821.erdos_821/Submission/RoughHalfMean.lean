import Submission.RoughModulusMean

/-!
# Primitive-conductor means on arbitrary power-width intervals

A finite cover by narrow conductor intervals retains the strict
below-square-root range. The endpoints are included in the cover.
-/
open Nat Finset Filter ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 3000000

lemma exists_consecutive_interval_cover (f : ℕ → ℕ) (hf : Monotone f)
    (a b : ℕ) (hab : a ≤ b) (q : ℕ) (hq : q ∈ Icc (f a) (f b)) :
    ∃ j ∈ Icc a b, q ∈ Icc (f j) (f (j+1)) := by
  induction b generalizing a with
  | zero =>
    have ha : a=0 := by omega
    subst a
    refine ⟨0,by simp,mem_Icc.mpr ⟨(mem_Icc.mp hq).1,?_⟩⟩
    exact (mem_Icc.mp hq).2.trans (hf (by omega))
  | succ b ih =>
    by_cases ha : a=b+1
    · subst a
      refine ⟨b+1,by simp,mem_Icc.mpr ⟨(mem_Icc.mp hq).1,?_⟩⟩
      exact (mem_Icc.mp hq).2.trans (hf (by omega))
    have hab' : a ≤ b := by omega
    by_cases hqb : q ≤ f b
    · obtain ⟨j,hj,hjq⟩ := ih a hab' (mem_Icc.mpr ⟨(mem_Icc.mp hq).1,hqb⟩)
      exact ⟨j,mem_Icc.mpr ⟨(mem_Icc.mp hj).1,(mem_Icc.mp hj).2.trans (Nat.le_succ b)⟩,hjq⟩
    · exact ⟨b,mem_Icc.mpr ⟨hab',Nat.le_succ b⟩,
        mem_Icc.mpr ⟨(Nat.lt_of_not_ge hqb).le,(mem_Icc.mp hq).2⟩⟩

lemma sum_le_sum_interval_cover (P J : Finset ℕ) (Q : ℕ → Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ q, 0 ≤ w q) (hcover : ∀ q ∈ P, ∃ j ∈ J, q ∈ Q j) :
    (∑ q ∈ P, w q) ≤ ∑ j ∈ J, ∑ q ∈ Q j, w q := by
  calc
    _ ≤ ∑ q ∈ P, ∑ j ∈ J, if q ∈ Q j then w q else 0 := by
      apply sum_le_sum
      intro q hq
      obtain ⟨j,hj,hjq⟩ := hcover q hq
      have hh := single_le_sum (s := J)
        (f := fun j => if q ∈ Q j then w q else 0)
        (fun j _ => by dsimp only; split_ifs; exact hw q; exact le_rfl) hj
      simpa only [if_pos hjq] using hh
    _ = ∑ j ∈ J, ∑ q ∈ P with q ∈ Q j, w q := by
      rw [sum_comm]
      simp only [sum_filter]
    _ ≤ _ := sum_le_sum (fun j _ => sum_le_sum_of_subset_of_nonneg
      (fun q hq => (mem_filter.mp hq).2) (fun q _ _ => hw q))

/-- The lower exponent may be arbitrarily small but positive. -/
theorem interval_primitive_mean_below_half (a b t m : ℕ)
    (ha : 1 ≤ a) (hab : a ≤ b) (ht : 22 ≤ t) (hb : 2*b+5 ≤ t) (hm : 1 ≤ m) :
    primitivePoolMean (Icc (progressionScaleN (a*m)) (progressionScaleN (b*m)))
      (progressionScaleN (t*m)) ≤
      ((b+1 : ℕ) : ℝ)*(wideMeanConstant t : ℝ)*((m : ℝ)+1)^5*
        (2 : ℝ)^((64*t-1)*m) := by
  let Q (j : ℕ) := Icc (progressionScaleN (j*m)) (progressionScaleN ((j+1)*m))
  have hf : Monotone (fun j => progressionScaleN (j*m)) := by
    intro i j hij
    unfold progressionScaleN
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 64 (Nat.mul_le_mul_right m hij))
  have hcover := exists_consecutive_interval_cover (fun j => progressionScaleN (j*m)) hf a b hab
  have hs := sum_le_sum_interval_cover
    (Icc (progressionScaleN (a*m)) (progressionScaleN (b*m))) (Icc a b) Q
    (fun d => (∑ χ ∈ primitiveCharacters d, ‖twistedArithmeticSum χ vonMangoldt (progressionScaleN (t*m))‖)/(d.totient : ℝ))
    (fun d => by positivity) hcover
  change primitivePoolMean _ _ ≤ ∑ j ∈ Icc a b, primitivePoolMean (Q j) _ at hs
  have hmean (j : ℕ) (hj : j ∈ Icc a b) :
      primitivePoolMean (Q j) (progressionScaleN (t*m)) ≤
        (wideMeanConstant t : ℝ)*((m : ℝ)+1)^5*(2 : ℝ)^((64*t-1)*m) := by
    obtain ⟨haj,hjb⟩ := mem_Icc.mp hj
    apply wide_primitive_mean_bound (Q j) j (j+1) t m (by omega) (by omega)
      (by omega) (by omega) (by omega)
    intro d hd
    have hd' := mem_Icc.mp hd
    refine ⟨?_,hd'⟩
    have he : 0 < 64*(j*m) := Nat.mul_pos (by decide) (Nat.mul_pos (by omega) hm)
    exact (Nat.one_lt_pow he.ne' (by decide)).trans_le hd'.1
  apply hs.trans
  calc
    _ ≤ ∑ _j ∈ Icc a b, (wideMeanConstant t : ℝ)*((m : ℝ)+1)^5*(2 : ℝ)^((64*t-1)*m) :=
      sum_le_sum hmean
    _ = ((Icc a b).card : ℝ)*((wideMeanConstant t : ℝ)*((m : ℝ)+1)^5*(2 : ℝ)^((64*t-1)*m)) := by
      simp only [sum_const,nsmul_eq_mul]
    _ ≤ _ := by
      have hc : (Icc a b).card ≤ b+1 := by simp only [Nat.card_Icc]; omega
      have hcR : ((Icc a b).card : ℝ) ≤ (b+1 : ℕ) := by exact_mod_cast hc
      have hh := mul_le_mul_of_nonneg_right hcR
        (show 0 ≤ (wideMeanConstant t : ℝ)*((m : ℝ)+1)^5*(2 : ℝ)^((64*t-1)*m) by positivity)
      simpa only [mul_assoc] using hh

end Erdos821
