import Submission.CollisionShape

/-!
# Exact pinned-root and defect counts

Fixing one root and the root-sum defect injects the remaining unordered pair
into divisors of a difference of two cubes. These are unconditional finite
counting bounds, not a proof of the positive-density conjecture. The needed
aggregate over all primitive defects is not bounded here. No admitted
specification theorem is imported.
-/

namespace Erdos1206.PinnedDefect

/-- The two extreme-root roles are covered by one divisor identity. -/
theorem extreme_factor {r s b c q : ℤ}
    (hcube : r ^ 3 + s ^ 3 = b ^ 3 + c ^ 3)
    (hsum : b + c = r + s + q) :
    (r + q) ^ 3 - r ^ 3 = 3 * (b + c) * (b - s) * (c - s) := by
  have h : r + q = b + c - s := by omega
  rw [h]
  nlinarith only [hcube]

/-- The two middle-root roles are covered by one divisor identity. -/
theorem middle_factor {r s a d q : ℤ}
    (hcube : a ^ 3 + d ^ 3 = r ^ 3 + s ^ 3)
    (hsum : r + s = a + d + q) :
    r ^ 3 - (r - q) ^ 3 = 3 * (a + d) * (s - a) * (d - s) := by
  have h : r - q = a + d - s := by omega
  rw [h]
  nlinarith only [hcube]

/-- A natural-number divisibility consequence, valid in either extreme role. -/
theorem extreme_sum_dvd {r s b c q : ℕ}
    (hcube : r ^ 3 + s ^ 3 = b ^ 3 + c ^ 3)
    (hsum : b + c = r + s + q) :
    b + c ∣ (r + q) ^ 3 - r ^ 3 := by
  have hpow : r ^ 3 ≤ (r + q) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hc : (r : ℤ) ^ 3 + s ^ 3 = b ^ 3 + c ^ 3 := by exact_mod_cast hcube
  have hs : (b : ℤ) + c = r + s + q := by exact_mod_cast hsum
  have hf := extreme_factor hc hs
  apply Int.natCast_dvd_natCast.mp
  refine ⟨3 * ((b : ℤ) - s) * ((c : ℤ) - s), ?_⟩
  rw [Nat.cast_sub hpow]
  push_cast
  nlinarith only [hf]

/-- A natural-number divisibility consequence, valid in either middle role. -/
theorem middle_sum_dvd {r s a d q : ℕ} (hqr : q ≤ r)
    (hcube : a ^ 3 + d ^ 3 = r ^ 3 + s ^ 3)
    (hsum : r + s = a + d + q) :
    a + d ∣ r ^ 3 - (r - q) ^ 3 := by
  have hpow : (r - q) ^ 3 ≤ r ^ 3 := Nat.pow_le_pow_left (Nat.sub_le _ _) 3
  have hc : (a : ℤ) ^ 3 + d ^ 3 = r ^ 3 + s ^ 3 := by exact_mod_cast hcube
  have hs : (r : ℤ) + s = a + d + q := by exact_mod_cast hsum
  have hf := middle_factor hc hs
  apply Int.natCast_dvd_natCast.mp
  refine ⟨3 * ((s : ℤ) - a) * ((d : ℤ) - s), ?_⟩
  rw [Nat.cast_sub hpow]
  push_cast [Nat.cast_sub hqr]
  nlinarith only [hf]

/-- Fixed sum and cube sum determine a sorted pair uniquely. -/
theorem sorted_pair_unique {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d)
    (hsum : a + b = c + d) (hcube : a ^ 3 + b ^ 3 = c ^ 3 + d ^ 3) :
    a = c ∧ b = d := by
  rcases unordered_pair_eq_of_sum_eq_of_cube_sum_eq hsum hcube with h | h
  · exact h
  · omega

/-- Count any finite collection with a fixed extreme root and positive defect.
The triple is `(other extreme, smaller middle, larger middle)`. -/
theorem card_extreme_le_divisors (r q : ℕ) (hq : 0 < q)
    (W : Finset (ℕ × ℕ × ℕ))
    (hW : ∀ p ∈ W, p.2.1 ≤ p.2.2 ∧
      r ^ 3 + p.1 ^ 3 = p.2.1 ^ 3 + p.2.2 ^ 3 ∧
      p.2.1 + p.2.2 = r + p.1 + q) :
    W.card ≤ ((r + q) ^ 3 - r ^ 3).divisors.card := by
  have hpos : 0 < (r + q) ^ 3 - r ^ 3 :=
    Nat.sub_pos_of_lt (Nat.pow_lt_pow_left (by omega) (by decide))
  apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ × ℕ => p.2.1 + p.2.2)
  · intro p hp
    rcases hW p hp with ⟨_, hc, hs⟩
    exact Nat.mem_divisors.mpr ⟨extreme_sum_dvd hc hs, by omega⟩
  · rintro ⟨s, b, c⟩ hp ⟨s', b', c'⟩ hp' heq
    rcases hW (s, b, c) hp with ⟨hbc, hc, hs⟩
    rcases hW (s', b', c') hp' with ⟨hbc', hc', hs'⟩
    dsimp only at hbc hc hs hbc' hc' hs' heq
    have hss : s = s' := by omega
    have hcc : b ^ 3 + c ^ 3 = b' ^ 3 + c' ^ 3 := by rw [hss] at hc; omega
    obtain ⟨hb, hc⟩ := sorted_pair_unique hbc hbc' heq hcc
    simp only [hss, hb, hc]

/-- Count any finite collection with a fixed middle root and positive defect.
The triple is `(other middle, smaller extreme, larger extreme)`. -/
theorem card_middle_le_divisors (r q : ℕ) (hq : 0 < q) (hqr : q < r)
    (W : Finset (ℕ × ℕ × ℕ))
    (hW : ∀ p ∈ W, p.2.1 ≤ p.2.2 ∧
      p.2.1 ^ 3 + p.2.2 ^ 3 = r ^ 3 + p.1 ^ 3 ∧
      r + p.1 = p.2.1 + p.2.2 + q) :
    W.card ≤ (r ^ 3 - (r - q) ^ 3).divisors.card := by
  have hpos : 0 < r ^ 3 - (r - q) ^ 3 :=
    Nat.sub_pos_of_lt (Nat.pow_lt_pow_left (by omega) (by decide))
  apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ × ℕ => p.2.1 + p.2.2)
  · intro p hp
    rcases hW p hp with ⟨_, hc, hs⟩
    exact Nat.mem_divisors.mpr ⟨middle_sum_dvd hqr.le hc hs, by omega⟩
  · rintro ⟨s, a, d⟩ hp ⟨s', a', d'⟩ hp' heq
    rcases hW (s, a, d) hp with ⟨had, hc, hs⟩
    rcases hW (s', a', d') hp' with ⟨had', hc', hs'⟩
    dsimp only at had hc hs had' hc' hs' heq
    have hss : s = s' := by omega
    have hcc : a ^ 3 + d ^ 3 = a' ^ 3 + d' ^ 3 := by rw [hss] at hc; omega
    obtain ⟨ha, hd⟩ := sorted_pair_unique had had' heq hcc
    simp only [hss, ha, hd]

end Erdos1206.PinnedDefect
