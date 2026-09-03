import Submission.GeneralResidueObstruction
import Submission.ValuationStructure

/-! Structural rigidity of widely separated two-block cubes. This is a
necessary restriction only, not a proof of the missing-digit conjecture. -/

namespace Erdos406Work

lemma good_mod_three_pow {n : ℕ} (hn : Nat.digits 3 n ⊆ [0, 1]) (L : ℕ) :
    Nat.digits 3 (n % 3 ^ L) ⊆ [0, 1] := by
  rw [Nat.self_mod_pow_eq_ofDigits_take L n (by decide : 2 ≤ 3)]
  exact good_ofDigits fun d hd => hn (List.mem_of_mem_take hd)

lemma good_div_three_pow {n : ℕ} (hn : Nat.digits 3 n ⊆ [0, 1]) (L : ℕ) :
    Nat.digits 3 (n / 3 ^ L) ⊆ [0, 1] := by
  rw [digits_div_three_pow]
  exact fun d hd => hn (List.mem_of_mem_drop hd)

lemma good_split_iff {a b L : ℕ} (ha : a < 3 ^ L) :
    Nat.digits 3 (a + 3 ^ L * b) ⊆ [0, 1] ↔
      Nat.digits 3 a ⊆ [0, 1] ∧ Nat.digits 3 b ⊆ [0, 1] := by
  constructor
  · intro hg
    constructor
    · have hh := good_mod_three_pow hg L
      simpa [Nat.add_mod, Nat.mod_eq_of_lt ha] using hh
    · have hh := good_div_three_pow hg L
      rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt ha, zero_add] at hh
      exact hh
  · exact fun h => good_add_shifted ha h.1 h.2

lemma good_mul_three_iff (n : ℕ) :
    Nat.digits 3 (3 * n) ⊆ [0, 1] ↔ Nat.digits 3 n ⊆ [0, 1] := by
  simpa using (good_split_iff (a := 0) (b := n) (L := 1) (by decide))

/-- Three consecutive unit terms of a scaled cubic binomial expansion form
a geometric progression; if all are ternary-good, the two root coefficients
must coincide. -/
lemma cubic_coefficient_rigidity {a b c : ℕ}
    (ha : a % 3 = 1) (hb : b % 3 = 1) (hc : c % 3 = 1)
    (h0 : Nat.digits 3 (c * a ^ 3) ⊆ [0, 1])
    (h1 : Nat.digits 3 (c * a ^ 2 * b) ⊆ [0, 1])
    (h2 : Nat.digits 3 (c * a * b ^ 2) ⊆ [0, 1]) : a = b := by
  have hm0 : (c * a ^ 3) % 3 = 1 := by
    simp [Nat.mul_mod, Nat.pow_mod, ha, hc]
  have hm1 : (c * a ^ 2 * b) % 3 = 1 := by
    simp [Nat.mul_mod, Nat.pow_mod, ha, hb, hc]
  have hm2 : (c * a * b ^ 2) % 3 = 1 := by
    simp [Nat.mul_mod, Nat.pow_mod, ha, hb, hc]
  have hh := good_units_threeGPFree ⟨hm0, h0⟩ ⟨hm1, h1⟩ ⟨hm2, h2⟩ (by ring)
  have he : (c * a ^ 2) * a = (c * a ^ 2) * b := by
    calc
      _ = c * a ^ 3 := by ring
      _ = _ := hh
  have hap : 0 < a := by omega
  have hcp : 0 < c := by omega
  exact Nat.eq_of_mul_eq_mul_left (by positivity) he

/-- The bounds ensure that the four binomial coefficients occupy disjoint
ternary blocks, so no carries can hide their digits. -/
lemma separated_scaled_cube_good_iff {a b c L : ℕ}
    (h0 : c * a ^ 3 < 3 ^ L)
    (h1 : 3 * (c * a ^ 2 * b) < 3 ^ L)
    (h2 : 3 * (c * a * b ^ 2) < 3 ^ L) :
    Nat.digits 3 (c * (a + 3 ^ L * b) ^ 3) ⊆ [0, 1] ↔
      Nat.digits 3 (c * a ^ 3) ⊆ [0, 1] ∧
      Nat.digits 3 (c * a ^ 2 * b) ⊆ [0, 1] ∧
      Nat.digits 3 (c * a * b ^ 2) ⊆ [0, 1] ∧
      Nat.digits 3 (c * b ^ 3) ⊆ [0, 1] := by
  have he : c * (a + 3 ^ L * b) ^ 3 =
      c * a ^ 3 + 3 ^ L * (3 * (c * a ^ 2 * b) +
        3 ^ L * (3 * (c * a * b ^ 2) + 3 ^ L * (c * b ^ 3))) := by ring
  rw [he, good_split_iff h0, good_split_iff h1, good_split_iff h2,
    good_mul_three_iff, good_mul_three_iff]

lemma separated_scaled_cube_rigid_iff {a b c L : ℕ}
    (ha : a % 3 = 1) (hb : b % 3 = 1) (hc : c % 3 = 1)
    (h0 : c * a ^ 3 < 3 ^ L)
    (h1 : 3 * (c * a ^ 2 * b) < 3 ^ L)
    (h2 : 3 * (c * a * b ^ 2) < 3 ^ L) :
    Nat.digits 3 (c * (a + 3 ^ L * b) ^ 3) ⊆ [0, 1] ↔
      a = b ∧ Nat.digits 3 (c * a ^ 3) ⊆ [0, 1] := by
  rw [separated_scaled_cube_good_iff h0 h1 h2]
  constructor
  · rintro ⟨hg0, hg1, hg2, hg3⟩
    exact ⟨cubic_coefficient_rigidity ha hb hc hg0 hg1 hg2, hg0⟩
  · rintro ⟨rfl, hg⟩
    refine ⟨hg, ?_, ?_, hg⟩
    · convert hg using 1
      congr 1
      ring
    · convert hg using 1
      congr 1
      ring

/-- If a scaled cube is good and its root splits into these two widely
separated unit blocks, the root has a nontrivial odd factor. In particular it
cannot be a power of two. This does not cover roots without such a gap. -/
lemma separated_good_cube_root_not_power_of_two {a b c L : ℕ}
    (ha : a % 3 = 1) (hb : b % 3 = 1) (hc : c % 3 = 1) (hL : 2 ≤ L)
    (h0 : c * a ^ 3 < 3 ^ L)
    (h1 : 3 * (c * a ^ 2 * b) < 3 ^ L)
    (h2 : 3 * (c * a * b ^ 2) < 3 ^ L)
    (hg : Nat.digits 3 (c * (a + 3 ^ L * b) ^ 3) ⊆ [0, 1]) :
    ¬ (a + 3 ^ L * b).isPowerOfTwo := by
  have he := ((separated_scaled_cube_rigid_iff ha hb hc h0 h1 h2).mp hg).1
  subst b
  rintro ⟨k, hk⟩
  have hd : 3 ^ L + 1 ∣ a + 3 ^ L * a := by
    refine ⟨a, ?_⟩
    ring
  rw [hk] at hd
  have hh := Erdos406Structure.three_pow_add_one_dvd_two_pow (by omega : 0 < L) hd
  omega


lemma good_mul_three_pow_iff (n L : ℕ) :
    Nat.digits 3 (3 ^ L * n) ⊆ [0, 1] ↔ Nat.digits 3 n ⊆ [0, 1] := by
  induction L with
  | zero => simp
  | succ L ih => rw [pow_succ', mul_assoc, good_mul_three_iff, ih]

lemma good_not_dvd_three_mod {n : ℕ} (hg : Nat.digits 3 n ⊆ [0, 1])
    (hn : ¬ 3 ∣ n) : n % 3 = 1 := by
  have hh := ternary_digit_bound hg 0
  have hne : n % 3 ≠ 0 := fun h => hn (Nat.dvd_of_mod_eq_zero h)
  norm_num at hh
  omega

lemma cubic_unit_coefficient_rigidity {a b c : ℕ}
    (ha : ¬ 3 ∣ a) (hb : ¬ 3 ∣ b) (hc : ¬ 3 ∣ c)
    (h0 : Nat.digits 3 (c * a ^ 3) ⊆ [0, 1])
    (h1 : Nat.digits 3 (c * a ^ 2 * b) ⊆ [0, 1])
    (h2 : Nat.digits 3 (c * a * b ^ 2) ⊆ [0, 1]) : a = b := by
  have hpa := Nat.prime_three.coprime_iff_not_dvd.mpr ha
  have hpb := Nat.prime_three.coprime_iff_not_dvd.mpr hb
  have hpc := Nat.prime_three.coprime_iff_not_dvd.mpr hc
  have hm0 := good_not_dvd_three_mod h0 (Nat.prime_three.coprime_iff_not_dvd.mp
    (hpc.mul_right (hpa.pow_right 3)))
  have hm1 := good_not_dvd_three_mod h1 (Nat.prime_three.coprime_iff_not_dvd.mp
    ((hpc.mul_right (hpa.pow_right 2)).mul_right hpb))
  have hm2 := good_not_dvd_three_mod h2 (Nat.prime_three.coprime_iff_not_dvd.mp
    ((hpc.mul_right hpa).mul_right (hpb.pow_right 2)))
  have hh := good_units_threeGPFree ⟨hm0, h0⟩ ⟨hm1, h1⟩ ⟨hm2, h2⟩ (by ring)
  have hap : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; exact ha (dvd_zero 3))
  have hcp : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; exact hc (dvd_zero 3))
  apply Nat.eq_of_mul_eq_mul_left (show 0 < c * a ^ 2 by positivity)
  calc
    (c * a ^ 2) * a = c * a ^ 3 := by ring
    _ = (c * a ^ 2) * b := hh

/-- With no coprimality assumptions, the two root coefficients must have the
same three-free part. Thus they can differ only by a power of three. -/
lemma cubic_coefficient_common_three_free_part {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h0 : Nat.digits 3 (c * a ^ 3) ⊆ [0, 1])
    (h1 : Nat.digits 3 (c * a ^ 2 * b) ⊆ [0, 1])
    (h2 : Nat.digits 3 (c * a * b ^ 2) ⊆ [0, 1]) :
    ∃ r s u : ℕ, ¬ 3 ∣ u ∧ a = 3 ^ r * u ∧ b = 3 ^ s * u := by
  obtain ⟨r, A, hA, heA⟩ := Nat.exists_eq_pow_mul_and_not_dvd (ne_of_gt ha) 3 (by decide)
  obtain ⟨s, B, hB, heB⟩ := Nat.exists_eq_pow_mul_and_not_dvd (ne_of_gt hb) 3 (by decide)
  obtain ⟨t, C, hC, heC⟩ := Nat.exists_eq_pow_mul_and_not_dvd (ne_of_gt hc) 3 (by decide)
  have e0 : c * a ^ 3 = 3 ^ (t + r * 3) * (C * A ^ 3) := by
    rw [heA, heC]
    simp only [pow_add, pow_mul]
    ring
  have e1 : c * a ^ 2 * b = 3 ^ (t + r * 2 + s) * (C * A ^ 2 * B) := by
    rw [heA, heB, heC]
    simp only [pow_add, pow_mul]
    ring
  have e2 : c * a * b ^ 2 = 3 ^ (t + r + s * 2) * (C * A * B ^ 2) := by
    rw [heA, heB, heC]
    simp only [pow_add, pow_mul]
    ring
  rw [e0, good_mul_three_pow_iff] at h0
  rw [e1, good_mul_three_pow_iff] at h1
  rw [e2, good_mul_three_pow_iff] at h2
  have he := cubic_unit_coefficient_rigidity hA hB hC h0 h1 h2
  exact ⟨r, s, A, hA, heA, he ▸ heB⟩

/-- The power-of-two exclusion holds for arbitrary positive coefficients,
not just units modulo three. The separation bounds are still essential. -/
lemma separated_positive_good_cube_root_not_power_of_two {a b c L : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hL : 2 ≤ L)
    (h0 : c * a ^ 3 < 3 ^ L)
    (h1 : 3 * (c * a ^ 2 * b) < 3 ^ L)
    (h2 : 3 * (c * a * b ^ 2) < 3 ^ L)
    (hg : Nat.digits 3 (c * (a + 3 ^ L * b) ^ 3) ⊆ [0, 1]) :
    ¬ (a + 3 ^ L * b).isPowerOfTwo := by
  obtain ⟨hg0, hg1, hg2, hg3⟩ := (separated_scaled_cube_good_iff h0 h1 h2).mp hg
  obtain ⟨r, s, u, hu, heA, heB⟩ :=
    cubic_coefficient_common_three_free_part ha hb hc hg0 hg1 hg2
  rintro ⟨k, hk⟩
  have hL3 : 3 ∣ 3 ^ L := dvd_pow_self 3 (by omega : L ≠ 0)
  have hr0 : r = 0 := by
    by_contra hr
    have ha3 : 3 ∣ a := by
      rw [heA]
      exact dvd_mul_of_dvd_left (dvd_pow_self 3 hr) u
    have hd : 3 ∣ 2 ^ k := hk ▸ dvd_add ha3 (dvd_mul_of_dvd_left hL3 b)
    have hh := Nat.prime_three.dvd_of_dvd_pow hd
    norm_num at hh
  have he : a + 3 ^ L * b = (3 ^ (L + s) + 1) * u := by
    rw [heA, heB, hr0, pow_zero, one_mul, pow_add]
    ring
  have hd : 3 ^ (L + s) + 1 ∣ 2 ^ k := by
    rw [← hk, he]
    exact dvd_mul_right _ _
  have hh := Erdos406Structure.three_pow_add_one_dvd_two_pow (by omega : 0 < L + s) hd
  omega

/-- Applied directly to a candidate power of four: its cubic root cannot
have a decomposition satisfying these three carry-free separation bounds. -/
lemma good_four_power_forbids_separated_cubic_root {m a b L : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hL : 2 ≤ L)
    (he : 4 ^ (m / 3) = a + 3 ^ L * b)
    (h0 : 4 ^ (m % 3) * a ^ 3 < 3 ^ L)
    (h1 : 3 * (4 ^ (m % 3) * a ^ 2 * b) < 3 ^ L)
    (h2 : 3 * (4 ^ (m % 3) * a * b ^ 2) < 3 ^ L)
    (hg : Nat.digits 3 (4 ^ m) ⊆ [0, 1]) : False := by
  have hepow : 4 ^ (m % 3) * (a + 3 ^ L * b) ^ 3 = 4 ^ m := by
    rw [← he, ← pow_mul, ← pow_add]
    congr 1
    omega
  have hh := separated_positive_good_cube_root_not_power_of_two ha hb
    (by positivity : 0 < 4 ^ (m % 3)) hL h0 h1 h2 (hepow ▸ hg)
  apply hh
  refine ⟨2 * (m / 3), ?_⟩
  rw [← he, pow_mul]
  rfl

#print axioms separated_scaled_cube_rigid_iff
#print axioms cubic_coefficient_common_three_free_part
#print axioms separated_positive_good_cube_root_not_power_of_two
#print axioms good_four_power_forbids_separated_cubic_root
end Erdos406Work
