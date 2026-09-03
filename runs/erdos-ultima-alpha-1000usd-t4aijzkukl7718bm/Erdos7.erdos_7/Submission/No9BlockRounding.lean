import Submission.No9LossRounding
import Submission.PositiveIteration

/-! Soundness of cubic truncation and rounded block profiles. -/
namespace Erdos7No9Certificate
open scoped BigOperators
open Erdos7KilledSieve
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

lemma rounded_coefficient_mul (r x : ℚ) (v a : ℕ) (hr : 0 ≤ r)
    (hx : x ≤ (v:ℚ)/scale) (ha : r ≤ (a:ℚ)/coefficientScale) :
    r*x ≤ (ceilDiv (a*v) coefficientScale:ℚ)/scale := by
  apply (mul_le_mul_of_nonneg_left hx hr).trans
  apply (mul_le_mul_of_nonneg_right ha (by positivity : (0:ℚ) ≤ (v:ℚ)/scale)).trans
  exact rounded_mul_bound _ _ _ _ (by norm_num [coefficientScale]) le_rfl

lemma realValues_congr (h v : ℕ → ℕ) (hv : ∀ j,j < nodes → h j=v j) : realValues h=realValues v := by
  ext j
  simp only [realValues,hv j.val j.isLt]

lemma rounded_three_powers (p R A B : ℕ) (hp : 1 < p) (hR0 : 1 ≤ R) (hR1 : R ≤ 18)
    (hB : 0 < B) (h y1 y2 y3 : ℕ → ℕ)
    (hy1 : ∀ j,j < nodes → offdiag p R A B h j=y1 j)
    (hy2 : ∀ j,j < nodes → offdiag p R A B y1 j=y2 j)
    (hy3 : ∀ j,j < nodes → offdiag p R A B y2 j=y3 j) :
    let T := realOperator p R A B
    (T^1) (realValues h) ≤ realValues y1 ∧
    (T^2) (realValues h) ≤ realValues y2 ∧
    (T^3) (realValues h) ≤ realValues y3 := by
  dsimp only
  have hT := realOperator_monotone p R A B hp hR1
  have h1 := rounded_offdiag p R A B hp hR0 hR1 hB h
  have h2 := rounded_offdiag p R A B hp hR0 hR1 hB y1
  have h3 := rounded_offdiag p R A B hp hR0 hR1 hB y2
  rw [realValues_congr _ _ hy1] at h1
  rw [realValues_congr _ _ hy2] at h2
  rw [realValues_congr _ _ hy3] at h3
  have hh2 : (realOperator p R A B^2) (realValues h) ≤ realValues y2 := by
    rw [pow_succ',Module.End.mul_apply,pow_one]
    exact (hT h1).trans h2
  refine ⟨by simpa only [pow_one] using h1,hh2,?_⟩
  rw [pow_succ',Module.End.mul_apply]
  exact (hT hh2).trans h3

def blockAlpha (b : BlockControl) : ℚ := 1-(5/4)/(b.hi:ℚ)
def blockBeta (b : BlockControl) : ℚ := geometricMeanNorm b.lo (5/4)
def blockRemainder (b : BlockControl) : ℚ :=
  ((b.count:ℚ)*blockBeta b)^4/(1-(b.count:ℚ)*blockBeta b)

structure BlockAnalyticBounds (b : BlockControl) : Prop where
  lo_two : 2 ≤ b.lo
  hi_two : 2 ≤ b.hi
  R_pos : 1 ≤ b.R
  R_le : b.R ≤ 18
  small : (b.count:ℚ)*blockBeta b < 1
  a0 : (blockAlpha b)^b.count ≤ (b.a0:ℚ)/coefficientScale
  a1 : (b.count:ℚ)*(blockAlpha b)^(b.count-1) ≤ (b.a1:ℚ)/coefficientScale
  a2 : (b.count.choose 2:ℚ)*(blockAlpha b)^(b.count-2) ≤ (b.a2:ℚ)/coefficientScale
  a3 : (b.count.choose 3:ℚ)*(blockAlpha b)^(b.count-3) ≤ (b.a3:ℚ)/coefficientScale
  remainder : blockRemainder b ≤ (b.remainder:ℚ)/coefficientScale

lemma blockAlpha_nonneg (b : BlockControl) (hb : 2 ≤ b.hi) : 0 ≤ blockAlpha b := by
  have hh : (2:ℚ) ≤ b.hi := by exact_mod_cast hb
  have hp : (0:ℚ) < b.hi := by linarith
  dsimp [blockAlpha]
  apply sub_nonneg.mpr
  exact (div_le_one hp).mpr (by linarith)

lemma blockAlpha_le_one (b : BlockControl) : blockAlpha b ≤ 1 := by
  dsimp [blockAlpha]
  exact sub_le_self _ (by positivity)

lemma blockBeta_nonneg (b : BlockControl) (hb : 2 ≤ b.lo) : 0 ≤ blockBeta b := by
  have hh : (2:ℚ) ≤ b.lo := by exact_mod_cast hb
  have hp : (0:ℚ) < b.lo := by linarith
  have h1 : (0:ℚ) < (b.lo:ℚ)-1 := by linarith
  have h2 : (0:ℚ) < 2*(b.lo:ℚ)-1 := by linarith
  dsimp [blockBeta,geometricMeanNorm]
  positivity

lemma rounded_blockRaw (b : BlockControl) (hb : BlockAnalyticBounds b)
    (h y1 y2 y3 : ℕ → ℕ) (hh0 : ∀ j,j < nodes → h j ≤ h 0)
    (hy1 : ∀ j,j < nodes → offdiag b.lo b.R 5 4 h j=y1 j)
    (hy2 : ∀ j,j < nodes → offdiag b.lo b.R 5 4 y1 j=y2 j)
    (hy3 : ∀ j,j < nodes → offdiag b.lo b.R 5 4 y2 j=y3 j) :
    (((blockAlpha b) • (1:Module.End ℚ (Fin nodes → ℚ))+realOperator b.lo b.R 5 4)^b.count)
      (realValues h) ≤ realValues (blockRaw b h y1 y2 y3) := by
  let T := realOperator b.lo b.R 5 4
  have hp : 1 < b.lo := by have := hb.lo_two; omega
  have hT : Monotone T := realOperator_monotone _ _ _ _ hp hb.R_le
  have hα0 := blockAlpha_nonneg b hb.hi_two
  have hα1 := blockAlpha_le_one b
  have hβ := blockBeta_nonneg b hb.lo_two
  have hnorm : T (fun _ => 1) ≤ fun _ => blockBeta b := by
    rw [show T=realOperator b.lo b.R 5 4 from rfl,realOperator_one _ _ _ _ hp hb.R_le]
    exact le_rfl
  have htop : realValues h ≤ fun _ => (h 0:ℚ)/scale := by
    intro j
    change (h j.val:ℚ)/scale ≤ (h 0:ℚ)/scale
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (hh0 j.val j.isLt)) scale_pos.le
  obtain ⟨h1,h2,h3⟩ := rounded_three_powers b.lo b.R 5 4 hp hb.R_pos hb.R_le (by norm_num)
    h y1 y2 y3 hy1 hy2 hy3
  intro j
  have hr := positive_operator_truncation T hT (blockAlpha b) (blockBeta b) ((h 0:ℚ)/scale)
    hα0 hα1 hβ (by positivity) hnorm (realValues h) htop b.count 4 hb.small j
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.choose_zero_right,
    Nat.cast_one,Nat.sub_zero,pow_zero,Module.End.one_apply,one_mul,Nat.choose_one_right] at hr
  have h0' := rounded_coefficient_mul ((blockAlpha b)^b.count) (realValues h j)
    (h j.val) b.a0 (pow_nonneg hα0 _) le_rfl hb.a0
  have h1' := rounded_coefficient_mul ((b.count:ℚ)*(blockAlpha b)^(b.count-1))
    ((T^1) (realValues h) j) (y1 j.val) b.a1 (by positivity) (h1 j) hb.a1
  have h2' := rounded_coefficient_mul ((b.count.choose 2:ℚ)*(blockAlpha b)^(b.count-2))
    ((T^2) (realValues h) j) (y2 j.val) b.a2 (by positivity) (h2 j) hb.a2
  have h3' := rounded_coefficient_mul ((b.count.choose 3:ℚ)*(blockAlpha b)^(b.count-3))
    ((T^3) (realValues h) j) (y3 j.val) b.a3 (by positivity) (h3 j) hb.a3
  have hrem0 : 0 ≤ blockRemainder b := div_nonneg (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) hβ) 4)
    (sub_nonneg.mpr hb.small.le)
  have hrem := rounded_coefficient_mul (blockRemainder b) ((h 0:ℚ)/scale)
    (h 0) b.remainder hrem0 le_rfl hb.remainder
  apply hr.trans
  exact (add_le_add (add_le_add (add_le_add (add_le_add h0' h1') h2') h3') hrem).trans_eq (by
    simp only [realValues,blockRaw,Nat.cast_add,add_div])

lemma rounded_blockUniform (b : BlockControl) (hb : BlockAnalyticBounds b)
    (h y1 y2 y3 : ℕ → ℕ) (hh0 : ∀ j,j < nodes → h j ≤ h 0)
    (hy1 : ∀ j,j < nodes → offdiag b.lo b.R 5 4 h j=y1 j)
    (hy2 : ∀ j,j < nodes → offdiag b.lo b.R 5 4 y1 j=y2 j)
    (hy3 : ∀ j,j < nodes → offdiag b.lo b.R 5 4 y2 j=y3 j) :
    (((1:Module.End ℚ (Fin nodes → ℚ))+realOperator b.lo b.R 5 4)^b.count)
      (realValues h) ≤ realValues (blockUniform b h y1 y2 y3) := by
  let T := realOperator b.lo b.R 5 4
  have hp : 1 < b.lo := by have := hb.lo_two; omega
  have hT : Monotone T := realOperator_monotone _ _ _ _ hp hb.R_le
  have hβ := blockBeta_nonneg b hb.lo_two
  have hnorm : T (fun _ => 1) ≤ fun _ => blockBeta b := by
    rw [show T=realOperator b.lo b.R 5 4 from rfl,realOperator_one _ _ _ _ hp hb.R_le]
    exact le_rfl
  have htop : realValues h ≤ fun _ => (h 0:ℚ)/scale := by
    intro j
    change (h j.val:ℚ)/scale ≤ (h 0:ℚ)/scale
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (hh0 j.val j.isLt)) scale_pos.le
  obtain ⟨h1,h2,h3⟩ := rounded_three_powers b.lo b.R 5 4 hp hb.R_pos hb.R_le (by norm_num)
    h y1 y2 y3 hy1 hy2 hy3
  intro j
  have hr := positive_operator_truncation T hT 1 (blockBeta b) ((h 0:ℚ)/scale)
    (by norm_num) le_rfl hβ (by positivity) hnorm (realValues h) htop b.count 4 hb.small j
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.choose_zero_right,
    Nat.cast_one,Nat.sub_zero,pow_zero,Module.End.one_apply,one_mul,Nat.choose_one_right,
    one_smul,one_pow,mul_one] at hr
  have h1' := mul_le_mul_of_nonneg_left (h1 j) (Nat.cast_nonneg b.count)
  have h2' := mul_le_mul_of_nonneg_left (h2 j) (Nat.cast_nonneg (b.count.choose 2))
  have h3' := mul_le_mul_of_nonneg_left (h3 j) (Nat.cast_nonneg (b.count.choose 3))
  have hrem0 : 0 ≤ blockRemainder b := div_nonneg (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) hβ) 4)
    (sub_nonneg.mpr hb.small.le)
  have hrem := rounded_coefficient_mul (blockRemainder b) ((h 0:ℚ)/scale)
    (h 0) b.remainder hrem0 le_rfl hb.remainder
  apply hr.trans
  exact (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (realValues h j)) h1') h2') h3') hrem).trans_eq (by
    simp only [realValues,blockUniform,Nat.cast_add,Nat.cast_mul,add_div,mul_div_assoc])

#print axioms rounded_blockRaw
#print axioms rounded_blockUniform
end Erdos7No9Certificate
