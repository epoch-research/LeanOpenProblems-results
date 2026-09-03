import FormalConjecturesUtil

/-! Exact valuations for ternary repunits and an exclusion of nontrivial repeated
blocks. These lemmas do not settle the missing-digit conjecture. -/

namespace Erdos406Structure

/-- The ternary repunit with `r` digits. -/
def ternaryRepunit (r : ℕ) : ℕ := Nat.ofDigits 3 (List.replicate r 1)

lemma ternaryRepunit_succ (r : ℕ) :
    ternaryRepunit (r + 1) = 1 + 3 * ternaryRepunit r := by
  simp [ternaryRepunit, List.replicate_succ, Nat.ofDigits_cons]

lemma ternaryRepunit_identity (r : ℕ) : 2 * ternaryRepunit r + 1 = 3 ^ r := by
  induction r with
  | zero => simp [ternaryRepunit]
  | succ r ih => rw [ternaryRepunit_succ, pow_succ]; nlinarith

lemma ternaryRepunit_digits (r : ℕ) :
    Nat.digits 3 (ternaryRepunit r) = List.replicate r 1 := by
  apply Nat.digits_ofDigits 3 (by decide)
  · intro d hd
    simp only [List.mem_replicate] at hd
    omega
  · intro h
    simp

lemma ternaryRepunit_good (r : ℕ) :
    Nat.digits 3 (ternaryRepunit r) ⊆ [0, 1] := by
  rw [ternaryRepunit_digits]
  intro d hd
  simp only [List.mem_replicate] at hd
  simp [hd.2]

lemma ternaryRepunit_ge (r : ℕ) : r ≤ ternaryRepunit r := by
  induction r with
  | zero => omega
  | succ r ih => rw [ternaryRepunit_succ]; omega

lemma ternaryRepunit_mod_two (r : ℕ) : ternaryRepunit r % 2 = r % 2 := by
  induction r with
  | zero => simp [ternaryRepunit]
  | succ r ih =>
    rw [ternaryRepunit_succ]
    omega


lemma ternaryRepunit_valuation {r : ℕ} (hr : 0 < r) :
    padicValNat 2 (ternaryRepunit r) = if Even r then 1 + padicValNat 2 r else 0 := by
  have hR : ternaryRepunit r ≠ 0 := by
    have hh := ternaryRepunit_ge r
    omega
  have he : 3 ^ r - 1 = 2 * ternaryRepunit r := by
    have hh := ternaryRepunit_identity r
    omega
  by_cases hEven : Even r
  · rw [if_pos hEven]
    have h := padicValNat.pow_two_sub_one (by decide : 1 < 3)
      (by decide : ¬ 2 ∣ 3) (ne_of_gt hr) hEven
    rw [he, padicValNat.mul (by decide) hR] at h
    have h4 : padicValNat 2 4 = 2 := by
      change padicValNat 2 (2 ^ 2) = 2
      simp only [padicValNat.prime_pow]
    norm_num [h4] at h
    omega
  · rw [if_neg hEven]
    apply padicValNat.eq_zero_of_not_dvd
    intro hd
    have hmod := Nat.mod_eq_zero_of_dvd hd
    rw [ternaryRepunit_mod_two] at hmod
    exact hEven (Nat.even_iff.mpr hmod)

lemma ternaryRepunit_one : ternaryRepunit 1 = 1 := by
  decide +kernel

lemma ternaryRepunit_two : ternaryRepunit 2 = 4 := by
  decide +kernel

lemma ternaryRepunit_gt_twice {r : ℕ} (hr : 3 ≤ r) : 2 * r < ternaryRepunit r := by
  induction r, hr using Nat.le_induction with
  | base => decide +kernel
  | succ r hr ih => rw [ternaryRepunit_succ]; omega

lemma ternaryRepunit_power_of_two_iff (r : ℕ) :
    (ternaryRepunit r).isPowerOfTwo ↔ r = 1 ∨ r = 2 := by
  constructor
  · rintro ⟨k, hk⟩
    have hpos : 0 < ternaryRepunit r := by rw [hk]; positivity
    have hr : 0 < r := by
      by_contra hh
      have hz : r = 0 := by omega
      subst r
      norm_num [ternaryRepunit] at hpos
    have hval := ternaryRepunit_valuation hr
    rw [hk, padicValNat.prime_pow] at hval
    by_cases hEven : Even r
    · rw [if_pos hEven] at hval
      have hv : 2 ^ padicValNat 2 r ≤ r := by
        apply Nat.le_of_dvd hr
        exact (padicValNat_dvd_iff_le (ne_of_gt hr)).mpr le_rfl
      have hb : ternaryRepunit r ≤ 2 * r := by
        rw [hk, hval, pow_add]
        norm_num
        omega
      have hrle : r ≤ 2 := by
        by_contra hh
        have ht := ternaryRepunit_gt_twice (by omega : 3 ≤ r)
        omega
      omega
    · rw [if_neg hEven] at hval
      have hR : ternaryRepunit r = 1 := by simpa [hval] using hk
      have hg := ternaryRepunit_ge r
      left
      omega
  · rintro (rfl | rfl)
    · exact ⟨0, ternaryRepunit_one⟩
    · exact ⟨2, ternaryRepunit_two⟩

lemma three_pow_mod_eight (a : ℕ) : 3 ^ a % 8 = 1 ∨ 3 ^ a % 8 = 3 := by
  rcases Nat.even_or_odd a with ⟨b, rfl⟩ | ⟨b, rfl⟩
  · left
    rw [← two_mul, pow_mul]
    norm_num [Nat.pow_mod]
  · right
    rw [pow_add, pow_mul]
    norm_num [Nat.mul_mod, Nat.pow_mod]

lemma three_pow_add_one_dvd_two_pow {a k : ℕ} (ha : 0 < a)
    (hd : 3 ^ a + 1 ∣ 2 ^ k) : a = 1 := by
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp hd
  have hp : 1 < 3 ^ a := one_lt_pow₀ (by decide) (ne_of_gt ha)
  have hjlt : j < 3 := by
    by_contra hh
    obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le (by omega : 3 ≤ j)
    have hm := congrArg (fun n : ℕ => n % 8) hj
    have hcases := three_pow_mod_eight a
    norm_num [pow_add, Nat.add_mod, Nat.mul_mod] at hm
    omega
  have hpa : 3 ^ a = 3 ^ 1 := by
    interval_cases j <;> norm_num at hj <;> norm_num <;> omega
  exact (Nat.pow_right_injective (by decide : 2 ≤ 3)) hpa

def blockGeom (L r : ℕ) : ℕ := ∑ i ∈ Finset.range r, (3 ^ L) ^ i

lemma blockGeom_succ (L r : ℕ) : blockGeom L (r + 1) = 3 ^ L * blockGeom L r + 1 := by
  exact geom_sum_succ

lemma blockGeom_ge (L r : ℕ) : r ≤ blockGeom L r := by
  induction r with
  | zero => simp [blockGeom]
  | succ r ih =>
    rw [blockGeom_succ]
    have hpow : 1 ≤ 3 ^ L := Nat.one_le_pow _ _ (by decide)
    nlinarith

lemma blockGeom_mod_two (L r : ℕ) : blockGeom L r % 2 = r % 2 := by
  induction r with
  | zero => simp [blockGeom]
  | succ r ih =>
    rw [blockGeom_succ]
    have hpow : 3 ^ L % 2 = 1 := by norm_num [Nat.pow_mod]
    have hm : (3 ^ L * blockGeom L r) % 2 = r % 2 := by
      rw [Nat.mul_mod, hpow, one_mul, Nat.mod_mod, ih]
    omega

lemma blockGeom_double (L t : ℕ) :
    blockGeom L (t + t) = blockGeom L t * (3 ^ (L * t) + 1) := by
  unfold blockGeom
  rw [Finset.sum_range_add]
  simp only [pow_add]
  rw [← Finset.mul_sum, ← pow_mul]
  ring

lemma blockGeom_dvd_two_pow_iff {L r : ℕ} (hL : 0 < L) (hr : 0 < r) :
    (∃ k : ℕ, blockGeom L r ∣ 2 ^ k) ↔ r = 1 ∨ (L = 1 ∧ r = 2) := by
  constructor
  · rintro ⟨k, hk⟩
    rcases Nat.even_or_odd r with ⟨t, ht⟩ | hodd
    · have htpos : 0 < t := by omega
      have hdiv : 3 ^ (L * t) + 1 ∣ 2 ^ k := by
        apply dvd_trans _ hk
        rw [ht, blockGeom_double]
        exact dvd_mul_left _ _
      have he := three_pow_add_one_dvd_two_pow (Nat.mul_pos hL htpos) hdiv
      have hL1 : L = 1 := Nat.eq_one_of_mul_eq_one_right he
      have ht1 : t = 1 := Nat.eq_one_of_mul_eq_one_left he
      right
      exact ⟨hL1, by omega⟩
    · have hnot : ¬ 2 ∣ blockGeom L r := by
        intro h
        have hm := Nat.mod_eq_zero_of_dvd h
        rw [blockGeom_mod_two, Nat.odd_iff.mp hodd] at hm
        omega
      obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp hk
      have hj0 : j = 0 := by
        by_contra h
        apply hnot
        rw [hj]
        exact dvd_pow_self 2 h
      have he : blockGeom L r = 1 := by simpa [hj0] using hj
      have hh := blockGeom_ge L r
      left
      omega
  · rintro (rfl | ⟨rfl, rfl⟩)
    · exact ⟨0, by simp [blockGeom]⟩
    · exact ⟨2, by norm_num [blockGeom, Finset.sum_range_succ]⟩

lemma ofDigits_repeated_block (w : List ℕ) (r : ℕ) :
    Nat.ofDigits 3 (List.replicate r w).flatten = Nat.ofDigits 3 w * blockGeom w.length r := by
  induction r with
  | zero => simp [blockGeom]
  | succ r ih =>
    rw [List.replicate_succ, List.flatten_cons, Nat.ofDigits_append, ih, blockGeom_succ]
    ring

/-- A nontrivial exact repetition of a `{0,1}` ternary block represents a power
of two only for the word `11`, representing four. This does not bound the length
of arbitrary primitive words. -/
lemma repeated_good_block_power_of_two_iff (w : List ℕ) (r : ℕ)
    (hw : w ⊆ [0, 1]) (hr : 2 ≤ r) :
    (Nat.ofDigits 3 (List.replicate r w).flatten).isPowerOfTwo ↔ w = [1] ∧ r = 2 := by
  constructor
  · rintro ⟨k, hk⟩
    rw [ofDigits_repeated_block] at hk
    have ha : 0 < Nat.ofDigits 3 w := by
      by_contra h
      have hz : Nat.ofDigits 3 w = 0 := by omega
      rw [hz, zero_mul] at hk
      have hp : 0 < 2 ^ k := by positivity
      omega
    have hL : 0 < w.length := by
      by_contra h
      have hz : w = [] := List.eq_nil_of_length_eq_zero (by omega)
      simp [hz] at ha
    have hd : blockGeom w.length r ∣ 2 ^ k := by
      rw [← hk]
      exact dvd_mul_left _ _
    have he := (blockGeom_dvd_two_pow_iff hL (by omega : 0 < r)).mp ⟨k, hd⟩
    obtain ⟨hL1, hr2⟩ : w.length = 1 ∧ r = 2 := by omega
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hL1
    have hmem := hw (by simp : a ∈ [a])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    simp only [Nat.ofDigits_singleton] at ha
    have ha1 : a = 1 := by omega
    exact ⟨by simp [ha1], hr2⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨2, by decide +kernel⟩

#print axioms ternaryRepunit_valuation
#print axioms ternaryRepunit_power_of_two_iff
#print axioms repeated_good_block_power_of_two_iff
end Erdos406Structure
