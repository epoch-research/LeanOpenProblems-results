import FormalConjecturesUtil
import Submission.UnsignedRestrictionMass

/-! A finite family of disjoint prime rectangles gives an explicit lower
bound for the unsigned subcritical main term. -/

namespace Erdos371PrimePowerRectangles

open Finset Erdos371PrimeLogMass
open Erdos371SubcriticalPrimePairCancellation (pairs)
open Erdos371WeightedLargeDivisorEnergy (weight weight_nonneg)
open Erdos371UnsignedRestrictionMass (mainMass)

abbrev primes (x : ℕ) := (x+1).primesBelow

def block (X k : ℕ) : Finset ℕ := primes (X^(k+1)) \ primes (X^k)
def j (k : ℕ) : ℕ := min k (19-k)
def rect (X k : ℕ) : Finset (ℕ×ℕ) := (primes (X^(j k))).product (block X k)

lemma mass_nonneg (x : ℕ) : 0 ≤ mass x :=
  sum_nonneg fun p _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)

lemma mem_block {X k p : ℕ} : p ∈ block X k ↔ p.Prime ∧ X^k<p ∧ p ≤ X^(k+1) := by
  simp only [block,mem_sdiff,Nat.mem_primesBelow]
  constructor
  · rintro ⟨⟨hhi,hp⟩,hlo⟩
    have hlo' : ¬p<X^k+1 := fun h => hlo ⟨h,hp⟩
    exact ⟨hp,by omega,by omega⟩
  · rintro ⟨hp,hlo,hhi⟩
    exact ⟨⟨by omega,hp⟩,by omega⟩

lemma block_disjoint {X k l : ℕ} (hX : 0<X) (hkl : k ≠ l) :
    Disjoint (block X k) (block X l) := by
  apply disjoint_left.mpr
  intro p hpk hpl
  obtain ⟨_,hklo,hkhi⟩ := mem_block.mp hpk
  obtain ⟨_,hllo,hlhi⟩ := mem_block.mp hpl
  rcases lt_or_gt_of_ne hkl with h | h
  · have hh := Nat.pow_le_pow_right hX (show k+1 ≤ l by omega)
    omega
  · have hh := Nat.pow_le_pow_right hX (show l+1 ≤ k by omega)
    omega

lemma rect_subset {X k : ℕ} (hX : 0<X) (hk : k ∈ Icc 1 18) :
    rect X k ⊆ pairs (X^20) := by
  rintro ⟨q,p⟩ hz
  obtain ⟨hq,hp⟩ := mem_product.mp hz
  obtain ⟨hqX,hq⟩ := Nat.mem_primesBelow.mp hq
  obtain ⟨hp,hplo,hphi⟩ := mem_block.mp hp
  have hjk : j k ≤ k := min_le_left _ _
  have hjbound : j k+(k+1) ≤ 20 := by
    have hh := min_le_right k (19-k)
    have hk' := mem_Icc.mp hk
    dsimp [j]
    omega
  have hqp : q<p := by
    have hh := Nat.pow_le_pow_right hX hjk
    omega
  have hprod : q*p ≤ X^20 := by
    calc
      _ ≤ X^(j k)*X^(k+1) := Nat.mul_le_mul (by omega) hphi
      _ = X^(j k+(k+1)) := (pow_add _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right hX hjbound
  exact Erdos371SubcriticalPrimePairCancellation.mem_pairs.mpr ⟨hq,hp,hqp,hprod⟩

lemma rect_disjoint {X k l : ℕ} (hX : 0<X) (hkl : k ≠ l) :
    Disjoint (rect X k) (rect X l) := by
  apply disjoint_left.mpr
  intro z hz hw
  exact disjoint_left.mp (block_disjoint hX hkl) (mem_product.mp hz).2 (mem_product.mp hw).2

lemma block_mass {X : ℕ} (hX : 0<X) (k : ℕ) :
    (∑ p ∈ block X k, Real.log (p : ℝ)/p) = mass (X^(k+1))-mass (X^k) := by
  apply (eq_sub_iff_add_eq).mpr
  exact sum_sdiff (by
    intro p hp
    obtain ⟨hpX,hp⟩ := Nat.mem_primesBelow.mp hp
    have hpow : X^k ≤ X^(k+1) := Nat.pow_le_pow_right hX (by omega)
    exact Nat.mem_primesBelow.mpr ⟨by omega,hp⟩)

lemma power_gt_one {X : ℕ} (hX : 1<X) {k : ℕ} (hk : 0<k) : 1<X^k := by
  have hh := Nat.pow_le_pow_right (by omega : 0<X) (show 1 ≤ k by omega)
  exact hX.trans_le (by simpa only [pow_one] using hh)

lemma harmonic_block_lower {X : ℕ} (hX : 1<X) (k : ℕ) :
    (mass (X^(k+1))-mass (X^k))/Real.log (X^(k+1) : ℕ) ≤
      ∑ p ∈ block X k, 1/(p : ℝ) := by
  have hl : 0<Real.log (X^(k+1) : ℕ) := Real.log_pos
    (by exact_mod_cast power_gt_one hX (by omega : 0<k+1))
  rw [← block_mass (by omega : 0<X) k,sum_div]
  apply sum_le_sum
  intro p hp
  obtain ⟨hp,_,hpX⟩ := mem_block.mp hp
  have hp0 : (0 : ℝ)<p := Nat.cast_pos.mpr hp.pos
  have hh := Real.log_le_log hp0 (Nat.cast_le.mpr hpX)
  have ht := div_le_div_of_nonneg_right hh hp0.le
  have ht' := div_le_div_of_nonneg_right ht hl.le
  calc
    _ ≤ (Real.log (X^(k+1) : ℕ)/(p : ℝ))/Real.log (X^(k+1) : ℕ) := ht'
    _ = _ := by field_simp

lemma rect_sum (X k : ℕ) :
    (∑ z ∈ rect X k, weight (X^20) z.1/(z.1*z.2 : ℕ)) =
      (mass (X^(j k))/Real.log (X^20 : ℕ)) * (∑ p ∈ block X k, 1/(p : ℝ)) := by
  unfold rect
  apply (sum_product' (primes (X^(j k))) (block X k)
    (fun q p => weight (X^20) q/(q*p : ℕ))).trans
  unfold mass
  rw [sum_div,sum_mul_sum]
  apply sum_congr rfl
  intro q hq
  apply sum_congr rfl
  intro p hp
  simp only [weight,Nat.cast_mul]
  ring

noncomputable def piece (X k : ℕ) : ℝ :=
  (mass (X^(j k))/Real.log (X^20 : ℕ)) *
    ((mass (X^(k+1))-mass (X^k))/Real.log (X^(k+1) : ℕ))

noncomputable def lower (X : ℕ) : ℝ := ∑ k ∈ Icc 1 18, piece X k

lemma piece_le_rect {X : ℕ} (hX : 1<X) (k : ℕ) :
    piece X k ≤ ∑ z ∈ rect X k, weight (X^20) z.1/(z.1*z.2 : ℕ) := by
  rw [rect_sum]
  exact mul_le_mul_of_nonneg_left (harmonic_block_lower hX k)
    (div_nonneg (mass_nonneg _) (Real.log_natCast_nonneg _))

/-- All eighteen rectangles are disjoint and lie below the product cutoff. -/
theorem lower_le_mainMass {X : ℕ} (hX : 1<X) : lower X ≤ mainMass (X^20) := by
  have hX0 : 0<X := by omega
  have hd : ((Icc 1 18 : Finset ℕ) : Set ℕ).PairwiseDisjoint (rect X) := by
    intro k hk l hl hkl
    exact rect_disjoint hX0 hkl
  calc
    _ ≤ ∑ k ∈ Icc 1 18, ∑ z ∈ rect X k, weight (X^20) z.1/(z.1*z.2 : ℕ) :=
      sum_le_sum fun k _ => piece_le_rect hX k
    _ = ∑ z ∈ (Icc 1 18).biUnion (rect X), weight (X^20) z.1/(z.1*z.2 : ℕ) :=
      (sum_biUnion hd).symm
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro z hz
        obtain ⟨k,hk,hz⟩ := mem_biUnion.mp hz
        exact rect_subset hX0 hk hz
      · intro z _ _
        exact div_nonneg (weight_nonneg _ _) (Nat.cast_nonneg _)

end Erdos371PrimePowerRectangles

#print axioms Erdos371PrimePowerRectangles.lower_le_mainMass
