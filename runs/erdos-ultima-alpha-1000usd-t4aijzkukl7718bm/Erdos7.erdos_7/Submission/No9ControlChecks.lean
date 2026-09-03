import Submission.No9BlockRounding

/-! Decidable integer checks imply the required rational operator inequalities. -/
namespace Erdos7No9Certificate
open scoped BigOperators
open Erdos7KilledSieve
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

def alphaNumerator (b : BlockControl) : ℕ := 4*b.hi-5
def alphaDenominator (b : BlockControl) : ℕ := 4*b.hi
def betaNumerator (b : BlockControl) : ℕ := 5*b.count*(2*b.lo-1)
def betaDenominator (b : BlockControl) : ℕ := 4*b.lo*(b.lo-1)

structure BlockIntegerBounds (b : BlockControl) : Prop where
  lo_two : 2 ≤ b.lo
  hi_two : 2 ≤ b.hi
  R_pos : 1 ≤ b.R
  R_le : b.R ≤ 18
  small : betaNumerator b < betaDenominator b
  a0 : coefficientScale*alphaNumerator b^b.count ≤ b.a0*alphaDenominator b^b.count
  a1 : coefficientScale*(b.count*alphaNumerator b^(b.count-1)) ≤ b.a1*alphaDenominator b^(b.count-1)
  a2 : coefficientScale*(b.count.choose 2*alphaNumerator b^(b.count-2)) ≤ b.a2*alphaDenominator b^(b.count-2)
  a3 : coefficientScale*(b.count.choose 3*alphaNumerator b^(b.count-3)) ≤ b.a3*alphaDenominator b^(b.count-3)
  remainder : coefficientScale*betaNumerator b^4 ≤
    b.remainder*(betaDenominator b^3*(betaDenominator b-betaNumerator b))

lemma nat_ratio_le_scaled (a b v : ℕ) (hb : 0 < b) (hv : coefficientScale*a ≤ v*b) :
    (a:ℚ)/b ≤ (v:ℚ)/coefficientScale := by
  apply (div_le_div_iff₀ (by exact_mod_cast hb) coefficientScale_pos).mpr
  have hh : (coefficientScale:ℚ)*a ≤ v*b := by exact_mod_cast hv
  nlinarith only [hh]

lemma nat_power_ratio_le_scaled (a n d v r : ℕ) (hd : 0 < d)
    (hv : coefficientScale*(a*n^r) ≤ v*d^r) :
    (a:ℚ)*((n:ℚ)/d)^r ≤ (v:ℚ)/coefficientScale := by
  have hh := nat_ratio_le_scaled (a*n^r) (d^r) v (by positivity) hv
  simpa only [Nat.cast_mul,Nat.cast_pow,div_pow,mul_div_assoc] using hh

lemma blockAlpha_ratio (b : BlockControl) (hb : 2 ≤ b.hi) :
    blockAlpha b=(alphaNumerator b:ℚ)/alphaDenominator b := by
  have hhi : (b.hi:ℚ)≠0 := by exact_mod_cast (by omega : b.hi≠0)
  dsimp [blockAlpha,alphaNumerator,alphaDenominator]
  rw [Nat.cast_sub (by omega : 5 ≤ 4*b.hi)]
  simp only [Nat.cast_mul,Nat.cast_ofNat]
  field_simp

lemma blockBeta_ratio (b : BlockControl) (hb : 2 ≤ b.lo) :
    (b.count:ℚ)*blockBeta b=(betaNumerator b:ℚ)/betaDenominator b := by
  dsimp [blockBeta,geometricMeanNorm,betaNumerator,betaDenominator]
  simp only [Nat.cast_mul,Nat.cast_sub (by omega : 1 ≤ 2*b.lo),
    Nat.cast_sub (by omega : 1 ≤ b.lo),Nat.cast_ofNat,Nat.cast_one]
  have hp : (b.lo:ℚ)≠0 := by exact_mod_cast (by omega : b.lo≠0)
  have hp1 : (b.lo:ℚ)-1≠0 := by
    have hh : (2:ℚ) ≤ b.lo := by exact_mod_cast hb
    linarith
  field_simp

lemma betaDenominator_pos (b : BlockControl) (hb : 2 ≤ b.lo) : 0 < betaDenominator b := by
  dsimp [betaDenominator]
  have hp : 0 < b.lo := by omega
  have h1 : 0 < b.lo-1 := by omega
  positivity

lemma blockRemainder_ratio (b : BlockControl) (hb : 2 ≤ b.lo)
    (hsmall : betaNumerator b < betaDenominator b) :
    blockRemainder b=(betaNumerator b:ℚ)^4/
      ((betaDenominator b:ℚ)^3*((betaDenominator b:ℚ)-betaNumerator b)) := by
  unfold blockRemainder
  rw [blockBeta_ratio b hb]
  have hd : (betaDenominator b:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt (betaDenominator_pos b hb))
  have hs : (betaDenominator b:ℚ)-(betaNumerator b:ℚ)≠0 := by
    have hh : (betaNumerator b:ℚ) < betaDenominator b := by exact_mod_cast hsmall
    linarith
  have hs' : (1:ℚ)-(betaNumerator b:ℚ)/betaDenominator b≠0 := by
    have hlt : (betaNumerator b:ℚ)/betaDenominator b < 1 :=
      (div_lt_one (by exact_mod_cast betaDenominator_pos b hb)).mpr (by exact_mod_cast hsmall)
    linarith
  field_simp

lemma blockIntegerBounds_sound (b : BlockControl) (hb : BlockIntegerBounds b) : BlockAnalyticBounds b := by
  have haDen : 0 < alphaDenominator b := by dsimp [alphaDenominator]; have := hb.hi_two; omega
  refine ⟨hb.lo_two,hb.hi_two,hb.R_pos,hb.R_le,?_,?_,?_,?_,?_,?_⟩
  · rw [blockBeta_ratio b hb.lo_two]
    exact (div_lt_one (by exact_mod_cast betaDenominator_pos b hb.lo_two)).mpr (by exact_mod_cast hb.small)
  · rw [blockAlpha_ratio b hb.hi_two]
    simpa only [Nat.cast_one,one_mul] using nat_power_ratio_le_scaled 1 _ _ b.a0 b.count haDen (by simpa only [one_mul] using hb.a0)
  · rw [blockAlpha_ratio b hb.hi_two]
    exact nat_power_ratio_le_scaled _ _ _ b.a1 _ haDen hb.a1
  · rw [blockAlpha_ratio b hb.hi_two]
    exact nat_power_ratio_le_scaled _ _ _ b.a2 _ haDen hb.a2
  · rw [blockAlpha_ratio b hb.hi_two]
    exact nat_power_ratio_le_scaled _ _ _ b.a3 _ haDen hb.a3
  · rw [blockRemainder_ratio b hb.lo_two hb.small]
    have hd : 0 < betaDenominator b^3*(betaDenominator b-betaNumerator b) :=
      Nat.mul_pos (pow_pos (betaDenominator_pos b hb.lo_two) _) (Nat.sub_pos_of_lt hb.small)
    have hh := nat_ratio_le_scaled _ _ _ hd hb.remainder
    simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_sub hb.small.le] using hh

def lossGeometryCheck (A B q j : ℕ) : Bool :=
  decide (0 < B) && decide (B ≤ A) && decide (0 < q) && decide (j+1 < nodes) &&
  decide (A*grid j ≤ q*(A-B)) && decide (q*(A-B) ≤ A*grid (j+1))

lemma lossGeometryCheck_iff (A B q j : ℕ) :
    lossGeometryCheck A B q j=true ↔ LossGeometry A B q j := by
  simp only [lossGeometryCheck,Bool.and_eq_true,decide_eq_true_eq,and_assoc]
  constructor
  · rintro ⟨h1,h2,h3,h4,h5,h6⟩; exact ⟨h1,h2,h3,h4,h5,h6⟩
  · rintro ⟨h1,h2,h3,h4,h5,h6⟩; exact ⟨h1,h2,h3,h4,h5,h6⟩

def blockIntegerCheck (b : BlockControl) : Bool :=
  decide (2 ≤ b.lo) && decide (2 ≤ b.hi) && decide (1 ≤ b.R) && decide (b.R ≤ 18) &&
  decide (betaNumerator b < betaDenominator b) &&
  decide (coefficientScale*alphaNumerator b^b.count ≤ b.a0*alphaDenominator b^b.count) &&
  decide (coefficientScale*(b.count*alphaNumerator b^(b.count-1)) ≤ b.a1*alphaDenominator b^(b.count-1)) &&
  decide (coefficientScale*(b.count.choose 2*alphaNumerator b^(b.count-2)) ≤ b.a2*alphaDenominator b^(b.count-2)) &&
  decide (coefficientScale*(b.count.choose 3*alphaNumerator b^(b.count-3)) ≤ b.a3*alphaDenominator b^(b.count-3)) &&
  decide (coefficientScale*betaNumerator b^4 ≤ b.remainder*(betaDenominator b^3*(betaDenominator b-betaNumerator b)))

lemma blockIntegerCheck_iff (b : BlockControl) : blockIntegerCheck b=true ↔ BlockIntegerBounds b := by
  simp only [blockIntegerCheck,Bool.and_eq_true,decide_eq_true_eq,and_assoc]
  constructor
  · rintro ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩; exact ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
  · rintro ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩; exact ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩

#print axioms blockIntegerBounds_sound
end Erdos7No9Certificate
