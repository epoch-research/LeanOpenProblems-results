import Submission.PeriodicBits

/-! Periodic arithmetic masks for the primes 3, 5, 7, 13, 17, 29. -/

namespace Erdos952Investigation.Sieve729

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

def period : ℕ := 672945

def prime : Fin 6 → ℕ := ![3, 5, 7, 13, 17, 29]

def normPoly (u v : ℤ) : ℤ := (1 + u + v)^2 + (u - v)^2

def Allowed (z : ℤ × ℤ) : Prop := ∀ k : Fin 6, normPoly z.1 z.2 % (prime k : ℤ) ≠ 0

def baseTable : Fin 6 → List ℕ
  | 0 => [7, 5, 7]
  | 1 => [21, 14, 27, 14, 21]
  | 2 => [127, 127, 127, 119, 127, 127, 127]
  | 3 => [7163, 8031, 4094, 7919, 7671, 6141, 8127, 6141, 7671, 7919, 4094, 8031, 7163]
  | 4 => [129983, 114683, 98301, 128991, 130431, 122871, 65534, 126959, 130815, 126959, 65534, 122871, 130431, 128991, 98301, 114683, 129983]
  | 5 => [535822079, 503316471, 536829951, 402653181, 536607743, 532676543, 528482271, 536737791, 268435454, 536801279, 520093679, 534773631, 536346111, 469762043, 536854527, 469762043, 536346111, 534773631, 520093679, 536801279, 268435454, 536737791, 528482271, 532676543, 536607743, 402653181, 536829951, 503316471, 535822079]

def smallBits (k : Fin 6) (r : ℕ) : ℕ := (baseTable k).getD (r % prime k) 0

def expandedBits (k : Fin 6) (r : ℕ) : ℕ :=
  smallBits k r * (((1 : ℕ) <<< period) - 1) / (((1 : ℕ) <<< prime k) - 1)

def bits (r : ℕ) : ℕ :=
  expandedBits 0 r &&& expandedBits 1 r &&& expandedBits 2 r &&&
  expandedBits 3 r &&& expandedBits 4 r &&& expandedBits 5 r

lemma prime_pos (k : Fin 6) : 0 < prime k := by fin_cases k <;> decide
lemma prime_le (k : Fin 6) : prime k ≤ 29 := by fin_cases k <;> decide
lemma prime_dvd_period (k : Fin 6) : prime k ∣ period := by fin_cases k <;> decide
lemma prime_is_prime (k : Fin 6) : (prime k).Prime := by fin_cases k <;> decide

private lemma small_correct_0 : ∀ r c : Fin 29,
    r.val < prime 0 → c.val < prime 0 →
    (smallBits 0 r.val).testBit c.val = decide (normPoly r.val c.val % (prime 0 : ℤ) ≠ 0) := by
  decide +kernel

private lemma expanded_checks_0 : ∀ r : Fin 29, r.val < prime 0 →
    expandedBits 0 r.val % (1 <<< prime 0) = smallBits 0 r.val ∧
    expandedBits 0 r.val >>> prime 0 = expandedBits 0 r.val % (1 <<< (period - prime 0)) := by
  decide +kernel

private lemma small_correct_1 : ∀ r c : Fin 29,
    r.val < prime 1 → c.val < prime 1 →
    (smallBits 1 r.val).testBit c.val = decide (normPoly r.val c.val % (prime 1 : ℤ) ≠ 0) := by
  decide +kernel

private lemma expanded_checks_1 : ∀ r : Fin 29, r.val < prime 1 →
    expandedBits 1 r.val % (1 <<< prime 1) = smallBits 1 r.val ∧
    expandedBits 1 r.val >>> prime 1 = expandedBits 1 r.val % (1 <<< (period - prime 1)) := by
  decide +kernel

private lemma small_correct_2 : ∀ r c : Fin 29,
    r.val < prime 2 → c.val < prime 2 →
    (smallBits 2 r.val).testBit c.val = decide (normPoly r.val c.val % (prime 2 : ℤ) ≠ 0) := by
  decide +kernel

private lemma expanded_checks_2 : ∀ r : Fin 29, r.val < prime 2 →
    expandedBits 2 r.val % (1 <<< prime 2) = smallBits 2 r.val ∧
    expandedBits 2 r.val >>> prime 2 = expandedBits 2 r.val % (1 <<< (period - prime 2)) := by
  decide +kernel

private lemma small_correct_3 : ∀ r c : Fin 29,
    r.val < prime 3 → c.val < prime 3 →
    (smallBits 3 r.val).testBit c.val = decide (normPoly r.val c.val % (prime 3 : ℤ) ≠ 0) := by
  decide +kernel

private lemma expanded_checks_3 : ∀ r : Fin 29, r.val < prime 3 →
    expandedBits 3 r.val % (1 <<< prime 3) = smallBits 3 r.val ∧
    expandedBits 3 r.val >>> prime 3 = expandedBits 3 r.val % (1 <<< (period - prime 3)) := by
  decide +kernel

private lemma small_correct_4 : ∀ r c : Fin 29,
    r.val < prime 4 → c.val < prime 4 →
    (smallBits 4 r.val).testBit c.val = decide (normPoly r.val c.val % (prime 4 : ℤ) ≠ 0) := by
  decide +kernel

private lemma expanded_checks_4 : ∀ r : Fin 29, r.val < prime 4 →
    expandedBits 4 r.val % (1 <<< prime 4) = smallBits 4 r.val ∧
    expandedBits 4 r.val >>> prime 4 = expandedBits 4 r.val % (1 <<< (period - prime 4)) := by
  decide +kernel

private lemma small_correct_5 : ∀ r c : Fin 29,
    r.val < prime 5 → c.val < prime 5 →
    (smallBits 5 r.val).testBit c.val = decide (normPoly r.val c.val % (prime 5 : ℤ) ≠ 0) := by
  decide +kernel

private lemma expanded_checks_5 : ∀ r : Fin 29, r.val < prime 5 →
    expandedBits 5 r.val % (1 <<< prime 5) = smallBits 5 r.val ∧
    expandedBits 5 r.val >>> prime 5 = expandedBits 5 r.val % (1 <<< (period - prime 5)) := by
  decide +kernel

lemma small_correct : ∀ (k : Fin 6) (r c : Fin 29),
    r.val < prime k → c.val < prime k →
    (smallBits k r.val).testBit c.val = decide (normPoly r.val c.val % (prime k : ℤ) ≠ 0) := by
  intro k
  fin_cases k
  · exact small_correct_0
  · exact small_correct_1
  · exact small_correct_2
  · exact small_correct_3
  · exact small_correct_4
  · exact small_correct_5

lemma expanded_checks : ∀ (k : Fin 6) (r : Fin 29), r.val < prime k →
    expandedBits k r.val % (1 <<< prime k) = smallBits k r.val ∧
    expandedBits k r.val >>> prime k = expandedBits k r.val % (1 <<< (period - prime k)) := by
  intro k
  fin_cases k
  · exact expanded_checks_0
  · exact expanded_checks_1
  · exact expanded_checks_2
  · exact expanded_checks_3
  · exact expanded_checks_4
  · exact expanded_checks_5

#print axioms small_correct
#print axioms expanded_checks

end Erdos952Investigation.Sieve729
