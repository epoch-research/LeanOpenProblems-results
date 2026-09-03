import Submission.DyadicPrimePairRectangles

/-!
# Fine arithmetic partitions of a dyadic interval

Using R equal subintervals between R*s and 2*R*s incurs only the factor
1+1/R when replacing the cofactor prefix H/M by H/q inside a weighted sum.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 3000000

lemma refined_interval_cover (R s q : ℕ) (hs : 0 < s)
    (hq : q ∈ Icc (R*s+1) (2*R*s)) :
    ∃ j ∈ range R, (R+j)*s<q ∧ q ≤ (R+j+1)*s := by
  obtain ⟨hqlo,hqhi⟩ := mem_Icc.mp hq
  let v := (q-1)/s
  have hvlo : R ≤ v := (Nat.le_div_iff_mul_le hs).mpr (by omega)
  have hvhi : v < 2*R := (Nat.div_lt_iff_lt_mul hs).mpr (by omega)
  have he : R+(v-R)=v := Nat.add_sub_of_le hvlo
  refine ⟨v-R,mem_range.mpr (by omega),?_,?_⟩
  · rw [he]
    have hh := Nat.div_mul_le_self (q-1) s
    change v*s ≤ q-1 at hh
    omega
  · rw [he]
    have hh := (Nat.div_lt_iff_lt_mul hs).mp (Nat.lt_succ_self ((q-1)/s))
    change q-1 < (v+1)*s at hh
    omega

lemma sum_step_intervals {G : Type*} [AddCommGroup G] (f : ℕ → G) (T R s : ℕ) :
    (∑ j ∈ range R, ∑ q ∈ Icc ((T+j)*s+1) ((T+j+1)*s), f q) =
      ∑ q ∈ Icc (T*s+1) ((T+R)*s), f q := by
  have hh (j : ℕ) := sum_natural_interval_sub f ((T+j)*s) ((T+j+1)*s)
    (Nat.mul_le_mul_right s (by omega : T+j ≤ T+j+1))
  simp_rw [hh]
  rw [sum_natural_interval_sub f (T*s) ((T+R)*s)
    (Nat.mul_le_mul_right s (by omega : T ≤ T+R))]
  induction R with
  | zero => simp
  | succ R ih =>
    rw [sum_range_succ,ih]
    simp only [Nat.add_assoc]
    abel

lemma refined_interval_ratio (R s j q : ℕ) (hR : 0 < R)
    (hq : q ≤ (R+j+1)*s) :
    (q : ℝ) ≤ (1+1/(R : ℝ))*((R+j)*s : ℕ) := by
  have hR0 : (0 : ℝ)<R := by exact_mod_cast hR
  have hqr : (q : ℝ) ≤ ((R : ℝ)+j+1)*s := by exact_mod_cast hq
  have hh := mul_le_mul_of_nonneg_left hqr hR0.le
  have hj : 0 ≤ (j : ℝ)*s := by positivity
  apply (mul_le_mul_iff_right₀ hR0).mp
  push_cast
  have he : (R : ℝ)*((1+1/(R : ℝ))*(((R : ℝ)+j)*s)) =
      ((R : ℝ)+1)*(((R : ℝ)+j)*s) := by field_simp
  rw [he]
  nlinarith only [hh,hj]

lemma weighted_refined_interval_upper (R s : ℕ) (hR : 0 < R) (hs : 0 < s)
    (w : ℕ → ℝ) (hw : ∀ q, 0 ≤ w q) :
    (∑ j ∈ range R, (∑ q ∈ Icc ((R+j)*s+1) ((R+j+1)*s), w q)/((R+j)*s : ℕ)) ≤
      (1+1/(R : ℝ))*(∑ q ∈ Icc (R*s+1) (2*R*s), w q/(q : ℝ)) := by
  calc
    _ = ∑ j ∈ range R, ∑ q ∈ Icc ((R+j)*s+1) ((R+j+1)*s), w q/((R+j)*s : ℕ) := by
      simp only [sum_div]
    _ ≤ ∑ j ∈ range R, ∑ q ∈ Icc ((R+j)*s+1) ((R+j+1)*s),
        (1+1/(R : ℝ))*(w q/(q : ℝ)) := by
      apply sum_le_sum
      intro j hj
      apply sum_le_sum
      intro q hq
      have hM : 0 < (R+j)*s := Nat.mul_pos (by omega) hs
      have hq0 : 0 < q := by have := (mem_Icc.mp hq).1; omega
      have hr := refined_interval_ratio R s j q hR (mem_Icc.mp hq).2
      have hh := mul_le_mul_of_nonneg_left hr (hw q)
      apply (div_le_iff₀ (by exact_mod_cast hM : (0 : ℝ)<((R+j)*s : ℕ))).mpr
      apply (mul_le_mul_iff_left₀ (by exact_mod_cast hq0 : (0 : ℝ)<q)).mp
      have he : ((1+1/(R : ℝ))*(w q/(q : ℝ))*((R+j)*s : ℕ))*(q : ℝ) =
          (1+1/(R : ℝ))*w q*((R+j)*s : ℕ) := by
        field_simp
      rw [he]
      nlinarith only [hh]
    _ = _ := by
      rw [sum_step_intervals]
      rw [← mul_sum]
      rw [show (R+R)*s=2*R*s by ring]

end Erdos821.AnalyticSieve
