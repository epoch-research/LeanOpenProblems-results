import FormalConjecturesUtil
import Submission.PrimeDiscrepancy

/-! Multiplying the losing endpoints of same-winner comparisons gives another
signed comparison. The winner can grow and the map need not be injective;
this identity is not a cancellation estimate for Erdős 371. -/

namespace Erdos371ProductSignTransport

open Erdos371PrimeDiscrepancy

/-- The integer on the side with the smaller largest prime factor. -/
def lower (n : ℕ) : ℕ := if P n<P (n+1) then n else n+1

def transport (n m : ℕ) : ℕ :=
  if sign n=sign m then lower n*lower m-1 else lower n*lower m

lemma lower_bounds (n : ℕ) : n≤lower n ∧ lower n≤n+1 := by
  unfold lower
  split_ifs <;> omega

lemma lower_prime_lt (n : ℕ) : P (lower n)<winner n := by
  have hne := consecutive_ne n
  unfold lower winner
  split_ifs with h
  · rw [max_eq_right h.le]
    exact h
  · rw [max_eq_left (le_of_not_gt h)]
    omega

lemma lower_residue (n p : ℕ) (hp : winner n=p) :
    (lower n : ZMod p)= -(sign n : ZMod p) := by
  by_cases h : P n<P (n+1)
  · have hw : p=P (n+1) := by simpa [winner,max_eq_right h.le] using hp.symm
    have hd : p∣n+1 := hw ▸ Nat.maxPrimeFac_dvd
    have hz := (CharP.cast_eq_zero_iff (ZMod p) p (n+1)).mpr hd
    simp only [Nat.cast_add,Nat.cast_one] at hz
    simp only [lower,sign,if_pos h,Int.cast_one]
    linear_combination hz
  · have hw : p=P n := by simpa [winner,max_eq_left (le_of_not_gt h)] using hp.symm
    have hd : p∣n := hw ▸ Nat.maxPrimeFac_dvd
    have hz := (CharP.cast_eq_zero_iff (ZMod p) p n).mpr hd
    simp [lower,sign,h,hz]

lemma sign_product_eq (n m : ℕ) :
    sign n*sign m=if sign n=sign m then 1 else -1 := by
  unfold sign
  split_ifs <;> norm_num at *

lemma product_residue {n m p : ℕ} (hn : winner n=p) (hm : winner m=p) :
    ((lower n*lower m : ℕ) : ZMod p)=
      if sign n=sign m then 1 else -1 := by
  rw [Nat.cast_mul,lower_residue n p hn,lower_residue m p hm,neg_mul_neg,
    ← Int.cast_mul,sign_product_eq]
  split_ifs <;> norm_num

lemma transport_bound {n m N : ℕ} (hn : n<N) (hm : m<N) :
    transport n m≤N^2 := by
  have hx := lower_bounds n
  have hy := lower_bounds m
  have hb := Nat.mul_le_mul (show lower n≤N by omega) (show lower m≤N by omega)
  unfold transport
  rw [pow_two]
  split_ifs <;> omega

/-- A local multiplication law for actual prime-factor comparisons.
The output is at most quadratic in the original range, not in that range. -/
theorem transport_sign_and_winner {n m : ℕ} (hn : 1<n) (hm : 1 < m)
    (hw : winner n=winner m) :
    sign (transport n m)= -(sign n*sign m) ∧
      winner n≤winner (transport n m) := by
  let p := winner n
  have hp : p.Prime := winner_prime (by omega)
  have hx := lower_bounds n
  have hy := lower_bounds m
  have hxy : 1<lower n*lower m := by nlinarith
  have hlt : P (lower n*lower m)<p := by
    rw [P,Nat.maxPrimeFac_mul (by omega) (by omega)]
    exact max_lt (lower_prime_lt n) (by simpa [← hw] using lower_prime_lt m)
  have hr := product_residue (p := p) rfl hw.symm
  by_cases hs : sign n=sign m
  · have hd : p∣lower n*lower m-1 := by
      apply (CharP.cast_eq_zero_iff (ZMod p) p _).mp
      rw [Nat.cast_sub hxy.le,Nat.cast_one,hr,if_pos hs]
      ring
    have hpT : p≤P (lower n*lower m-1) :=
      Nat.le_maxPrimeFac (by omega) hp hd
    have he : lower n*lower m-1+1=lower n*lower m := by omega
    have hcmp : ¬P (lower n*lower m-1)<P (lower n*lower m-1+1) := by
      rw [he]
      omega
    simp only [transport,sign_product_eq,if_pos hs]
    constructor
    · simp only [sign,if_neg hcmp]
    · exact hpT.trans (le_max_left _ _)
  · have hd : p∣lower n*lower m+1 := by
      apply (CharP.cast_eq_zero_iff (ZMod p) p _).mp
      rw [Nat.cast_add,Nat.cast_one,hr,if_neg hs]
      ring
    have hpT : p≤P (lower n*lower m+1) := Nat.le_maxPrimeFac (by omega) hp hd
    have hcmp : P (lower n*lower m)<P (lower n*lower m+1) := hlt.trans_le hpT
    simp only [transport,sign_product_eq,if_neg hs,neg_neg]
    constructor
    · simp only [sign,if_pos hcmp]
    · exact hpT.trans (le_max_right _ _)

/-- Even two distinct ascents with the same winner can produce a larger winner. -/
lemma winner_can_increase :
    winner 4=5 ∧ winner 9=5 ∧ sign 4=1 ∧ sign 9=1 ∧
      transport 4 9=35 ∧ winner (transport 4 9)=7 := by decide +kernel

/-- The collision is not merely the symmetry of an ordered pair. -/
lemma distinct_unordered_pairs_collide :
    5<24 ∧ 9<15 ∧ (5,24)≠(9,15) ∧
    winner 5=5 ∧ winner 24=5 ∧ winner 9=5 ∧ winner 15=5 ∧
    transport 5 24=144 ∧ transport 9 15=144 := by decide +kernel

end Erdos371ProductSignTransport

#print axioms Erdos371ProductSignTransport.transport_sign_and_winner
#print axioms Erdos371ProductSignTransport.winner_can_increase
#print axioms Erdos371ProductSignTransport.distinct_unordered_pairs_collide
