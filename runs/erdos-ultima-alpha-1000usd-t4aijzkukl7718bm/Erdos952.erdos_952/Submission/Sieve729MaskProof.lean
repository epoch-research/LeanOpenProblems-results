import Submission.Sieve729Masks

/-! Correctness of the arithmetic bit masks for all integer columns. -/

namespace Erdos952Investigation.Sieve729

set_option maxHeartbeats 0

lemma normPoly_mod (p u v : ℤ) :
    normPoly (u % p) (v % p) % p = normPoly u v % p := by
  simp [normPoly, pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod]

lemma expanded_correct (k : Fin 6) (r c : ℕ) (hc : c < period) :
    (expandedBits k r).testBit c =
      decide (normPoly (r : ℤ) (c : ℤ) % (prime k : ℤ) ≠ 0) := by
  have hrp := Nat.mod_lt r (prime_pos k)
  have hcp := Nat.mod_lt c (prime_pos k)
  have hpl := prime_le k
  let rr : Fin 29 := ⟨r % prime k, by omega⟩
  let cc : Fin 29 := ⟨c % prime k, by omega⟩
  obtain ⟨hl, hs⟩ := expanded_checks k rr hrp
  have hr : expandedBits k r = expandedBits k rr.val := by
    simp [expandedBits, smallBits, rr]
  rw [hr, BitsetBarrier.periodic_bits (prime_pos k) hl hs c hc]
  have hsmall := small_correct k rr cc hrp hcp
  have hn : normPoly (rr.val : ℤ) (cc.val : ℤ) % (prime k : ℤ) =
      normPoly (r : ℤ) (c : ℤ) % (prime k : ℤ) := by
    simpa only [rr, cc, Int.natCast_emod] using normPoly_mod (prime k) r c
  simpa only [cc, hn] using hsmall

lemma cast_mod_period (k : Fin 6) (c : ℤ) :
    (c % (period : ℤ)) % (prime k : ℤ) = c % (prime k : ℤ) := by
  obtain ⟨t, ht⟩ := prime_dvd_period k
  have htp : (period : ℤ) = (prime k : ℤ) * t := by exact_mod_cast ht
  have he : (prime k : ℤ) ∣ c - c % (period : ℤ) := by
    refine (show (prime k : ℤ) ∣ (period : ℤ) from ⟨t, htp⟩).trans ?_
    exact Int.dvd_self_sub_emod
  exact Int.modEq_iff_dvd.mpr he

lemma allowed_bits (r : ℕ) (c : ℤ) (h : Allowed ((r : ℤ), c)) :
    (bits r).testBit (c % (period : ℤ)).toNat = true := by
  have hp : (0 : ℤ) < period := by norm_num [period]
  have hc0 := Int.emod_nonneg c (ne_of_gt hp)
  have hc1 := Int.emod_lt_of_pos c hp
  have hc : (c % (period : ℤ)).toNat < period := by omega
  have hk (k : Fin 6) : (expandedBits k r).testBit (c % (period : ℤ)).toNat = true := by
    rw [expanded_correct k r _ hc]
    apply decide_eq_true
    have he : normPoly (r : ℤ) ((c % (period : ℤ)).toNat : ℤ) % (prime k : ℤ) =
        normPoly (r : ℤ) c % (prime k : ℤ) := by
      rw [Int.toNat_of_nonneg hc0, ← normPoly_mod (prime k) r (c % (period : ℤ)),
        cast_mod_period, normPoly_mod]
    rw [he]
    exact h k
  simp only [bits, Nat.testBit_land, hk, Bool.and_self]

#print axioms allowed_bits

end Erdos952Investigation.Sieve729
