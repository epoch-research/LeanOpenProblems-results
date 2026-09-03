import FormalConjecturesUtil

/-!
A character-sum lemma for a norm-one circle in odd-degree characteristic-three fields.
This auxiliary file does not settle Erdős 714.
-/

open Finset Polynomial

namespace Erdos714NormCircleTrace

private lemma bounds (m i : ℕ) (hm : 3 ≤ m) (hi : i < m) :
    27 ≤ 3 ^ m ∧ 3 ^ i ≤ 3 ^ (m - 1) ∧ 3 ^ m = 3 * 3 ^ (m - 1) := by
  refine ⟨Nat.pow_le_pow_right (n := 3) (i := 3) (by omega) hm,
    Nat.pow_le_pow_right (by omega) (by omega), ?_⟩
  have he : m = (m - 1) + 1 := by omega
  conv_lhs => rw [he]
  rw [pow_succ, mul_comm]

theorem not_dvd_positive (m i : ℕ) (hm : 3 ≤ m) (hi0 : 0 < i) (hi : i < m) :
    ¬ (3 ^ m + 1) ∣ (4 * 3 ^ i - 4) := by
  obtain ⟨hq, hpi, hpow⟩ := bounds m i hm hi
  have hi3 : 3 ≤ 3 ^ i := Nat.pow_le_pow_right (n := 3) (i := 1) (by omega) hi0
  have hpos : 0 < 4 * 3 ^ i - 4 := by omega
  have hlt : 4 * 3 ^ i - 4 < 2 * (3 ^ m + 1) := by omega
  rintro ⟨k, hk⟩
  have hk1 : k = 1 := by
    have : 0 < k := by
      by_contra h
      have hk0 : k = 0 := by omega
      rw [hk0, mul_zero] at hk
      omega
    nlinarith
  rw [hk1, mul_one] at hk
  have h3i : 3 ∣ 3 ^ i := Nat.pow_dvd_pow 3 hi0
  have h3m : 3 ∣ 3 ^ m := Nat.pow_dvd_pow 3 (by omega : 1 ≤ m)
  have hi' := Nat.mod_eq_zero_of_dvd h3i
  have hm' := Nat.mod_eq_zero_of_dvd h3m
  omega

theorem not_dvd_negative (m i : ℕ) (hm : 3 ≤ m) (hi : i < m) :
    ¬ (3 ^ m + 1) ∣ (4 * 3 ^ i + 4) := by
  obtain ⟨hq, hpi, hpow⟩ := bounds m i hm hi
  have hlt : 4 * 3 ^ i + 4 < 2 * (3 ^ m + 1) := by omega
  rintro ⟨k, hk⟩
  have hk1 : k = 1 := by
    have : 0 < k := by
      by_contra h
      have hk0 : k = 0 := by omega
      rw [hk0, mul_zero] at hk
      omega
    nlinarith
  rw [hk1, mul_one] at hk
  by_cases hi0 : i = 0
  · simp [hi0] at hk
    omega
  by_cases hi1 : i = 1
  · simp [hi1] at hk
    omega
  have h9i : 9 ∣ 3 ^ i := Nat.pow_dvd_pow 3 (by omega : 2 ≤ i)
  have h9m : 9 ∣ 3 ^ m := Nat.pow_dvd_pow 3 (by omega : 2 ≤ m)
  have hi' := Nat.mod_eq_zero_of_dvd h9i
  have hm' := Nat.mod_eq_zero_of_dvd h9m
  omega

section Characters
variable {E : Type*} [Field E]

/-- Orthogonality, indexed by the powers of a primitive root. -/
theorem sum_power {n : ℕ} {ζ : E} (hζ : IsPrimitiveRoot ζ n) (k : ℕ) :
    ∑ j ∈ range n, (ζ ^ j) ^ k = if n ∣ k then (n : E) else 0 := by
  have hcomm : ∀ j : ℕ, (ζ ^ j) ^ k = (ζ ^ k) ^ j := by
    intro j
    simp only [← pow_mul, Nat.mul_comm]
  simp_rw [hcomm]
  by_cases hk : n ∣ k
  · rw [(hζ.pow_eq_one_iff_dvd k).mpr hk]
    simp [hk]
  · rw [if_neg hk]
    have hne : ζ ^ k - 1 ≠ 0 := sub_ne_zero.mpr (mt (hζ.pow_eq_one_iff_dvd k).mp hk)
    have hp : (ζ ^ k) ^ n = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have h := geom_sum_mul (ζ ^ k) n
    rw [hp, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right hne

variable [CharP E 3]

def traceSum (m : ℕ) (x : E) : E := ∑ i ∈ range m, x ^ (3 ^ i)

theorem traceSum_artinSchreier (m : ℕ) (x : E) (hx : x ^ (3 ^ m) = x) :
    traceSum m (x ^ 3 - x) = 0 := by
  unfold traceSum
  simp_rw [sub_pow_char_pow]
  have ht : ∀ i : ℕ, (x ^ 3) ^ (3 ^ i) = x ^ (3 ^ (i + 1)) := by
    intro i
    rw [← pow_mul, pow_succ']
  simp_rw [ht]
  rw [Finset.sum_range_sub (fun i : ℕ => x ^ (3 ^ i)) m]
  simp [hx]

omit [CharP E 3] in
private lemma weighted_term (t : E) (ht : t ≠ 0) (i : ℕ) :
    t⁻¹ ^ 4 * (t ^ (4 * 3 ^ i) + t⁻¹ ^ (4 * 3 ^ i) + 1) =
      t ^ (4 * 3 ^ i - 4) + t⁻¹ ^ (4 * 3 ^ i + 4) + t⁻¹ ^ 4 := by
  have hi : 4 ≤ 4 * 3 ^ i := by
    have h := Nat.one_le_pow i 3 (by omega)
    omega
  rw [pow_sub₀ t ht hi, pow_add, inv_pow]
  ring

/-- One Fourier coefficient of the circle trace is nonzero. -/
theorem weighted_trace_sum (m : ℕ) (hm : 3 ≤ m) {ζ : E}
    (hζ : IsPrimitiveRoot ζ (3 ^ m + 1)) :
    ∑ j ∈ range (3 ^ m + 1), (ζ ^ j)⁻¹ ^ 4 *
      traceSum m ((ζ ^ j) ^ 4 + (ζ ^ j)⁻¹ ^ 4 + 1) = 1 := by
  have hn : ((3 ^ m + 1 : ℕ) : E) = 1 := by
    have h3 : (3 : E) = 0 := CharP.cast_eq_zero E 3
    push_cast
    rw [h3, zero_pow (by omega : m ≠ 0), zero_add]
  have hconst : ∑ j ∈ range (3 ^ m + 1), (ζ ^ j)⁻¹ ^ 4 = 0 := by
    simp_rw [← inv_pow]
    rw [sum_power hζ.inv, if_neg]
    have hq := (bounds m 0 hm (by omega)).1
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hpos : ∀ i ∈ range m,
      (∑ j ∈ range (3 ^ m + 1), (ζ ^ j) ^ (4 * 3 ^ i - 4)) =
        if i = 0 then (1 : E) else 0 := by
    intro i hi
    rw [sum_power hζ]
    by_cases hi0 : i = 0
    · simp [hi0, hn]
    · rw [if_neg hi0, if_neg (not_dvd_positive m i hm (by omega) (mem_range.mp hi))]
  have hneg : ∀ i ∈ range m,
      (∑ j ∈ range (3 ^ m + 1), (ζ ^ j)⁻¹ ^ (4 * 3 ^ i + 4)) = 0 := by
    intro i hi
    simp_rw [← inv_pow]
    rw [sum_power hζ.inv, if_neg (not_dvd_negative m i hm (mem_range.mp hi))]
  have hz : ζ ≠ 0 := hζ.ne_zero (Nat.succ_ne_zero _)
  calc
    _ = ∑ j ∈ range (3 ^ m + 1), ∑ i ∈ range m,
        (ζ ^ j)⁻¹ ^ 4 * ((ζ ^ j) ^ (4 * 3 ^ i) +
          (ζ ^ j)⁻¹ ^ (4 * 3 ^ i) + 1) := by
      simp only [traceSum, Finset.mul_sum, add_pow_char_pow, one_pow, ← pow_mul, Nat.mul_assoc]
    _ = ∑ i ∈ range m, ∑ j ∈ range (3 ^ m + 1),
        ((ζ ^ j) ^ (4 * 3 ^ i - 4) + (ζ ^ j)⁻¹ ^ (4 * 3 ^ i + 4) + (ζ ^ j)⁻¹ ^ 4) := by
      simp_rw [weighted_term _ (pow_ne_zero _ hz)]
      exact Finset.sum_comm
    _ = ∑ i ∈ range m, (if i = 0 then (1 : E) else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hpos i hi, hneg i hi, hconst]
      simp
    _ = 1 := by simp [show 0 < m by omega]

theorem exists_torus_parameter (m : ℕ) (hm : 3 ≤ m) {ζ : E}
    (hζ : IsPrimitiveRoot ζ (3 ^ m + 1)) :
    ∃ w : E, w ≠ 0 ∧ w ^ (3 ^ m + 1) = 1 ∧
      traceSum m (w ^ 4 + w⁻¹ ^ 4 + 1) ≠ 0 := by
  have hz : ζ ≠ 0 := hζ.ne_zero (Nat.succ_ne_zero _)
  have ht : ∃ j ∈ range (3 ^ m + 1), traceSum m ((ζ ^ j) ^ 4 + (ζ ^ j)⁻¹ ^ 4 + 1) ≠ 0 := by
    by_contra! h
    have he := weighted_trace_sum m hm hζ
    have hzero : ∑ j ∈ range (3 ^ m + 1), (ζ ^ j)⁻¹ ^ 4 *
        traceSum m ((ζ ^ j) ^ 4 + (ζ ^ j)⁻¹ ^ 4 + 1) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [h j hj, mul_zero]
    rw [hzero] at he
    exact zero_ne_one he
  obtain ⟨j, -, hj⟩ := ht
  refine ⟨ζ ^ j, pow_ne_zero j hz, ?_, hj⟩
  rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]

end Characters

section Descent
variable {F E : Type*} [Field F] [Field E] [Fintype F] [Algebra F E]

/-- The roots of `X^q-X` in an extension are precisely the embedded base field. -/
theorem pow_fixed_mem_range (x : E) (hx : x ^ Fintype.card F = x) :
    ∃ a : F, algebraMap F E a = x := by
  let p : F[X] := X ^ Fintype.card F - X
  have hp : p ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero F Fintype.one_lt_card
  have hs : p.Splits := by
    rw [Polynomial.splits_iff_card_roots]
    dsimp [p]
    rw [FiniteField.roots_X_pow_card_sub_X,
      FiniteField.X_pow_card_sub_X_natDegree_eq F Fintype.one_lt_card]
    exact Finset.card_univ
  have hr : (p.map (algebraMap F E)).IsRoot x := by
    simpa [p, Polynomial.IsRoot] using sub_eq_zero.mpr hx
  exact hs.mem_range_of_isRoot hp hr

end Descent

/-- In every odd-degree characteristic-three field of order at least 27, the norm-one
circle has a point whose squared-coordinate product is outside the Artin–Schreier image. -/
theorem exists_circle_parameter {F : Type*} [Field F] [CharP F 3] [Fintype F]
    (m : ℕ) (hm : 3 ≤ m) (hodd : Odd m) (hcard : Fintype.card F = 3 ^ m) :
    ∃ u v : F, u ^ 2 + v ^ 2 = 1 ∧ ∀ x : F, x ^ 3 - x ≠ -u ^ 2 * v ^ 2 := by
  let E := AlgebraicClosure F
  have h3F : (3 : F) = 0 := CharP.cast_eq_zero F 3
  have h3E : (3 : E) = 0 := CharP.cast_eq_zero E 3
  have hn : ((3 ^ m + 1 : ℕ) : F) = 1 := by
    push_cast
    rw [h3F, zero_pow (by omega : m ≠ 0), zero_add]
  letI : NeZero ((3 ^ m + 1 : ℕ) : F) := ⟨by rw [hn]; exact one_ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot E (3 ^ m + 1)
  obtain ⟨w, hw0, hw, ht⟩ := exists_torus_parameter m hm hζ
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : E) (by decide : 0 < 2)
  have hqmod : 3 ^ m % 4 = 3 := by
    obtain ⟨k, hk⟩ := hodd
    have hk' : m = 2 * k + 1 := by omega
    rw [hk', pow_add, pow_mul]
    norm_num [Nat.mul_mod, Nat.pow_mod]
  have hi4 : i ^ 4 = 1 := by
    calc i ^ 4 = (i ^ 2) ^ 2 := by ring
         _ = 1 := by rw [hi]; ring
  have hiq : i ^ (3 ^ m) = -i := by
    conv_lhs => rw [← Nat.mod_add_div (3 ^ m) 4]
    rw [pow_add, pow_mul, hi4, one_pow, mul_one, hqmod]
    calc i ^ 3 = i ^ 2 * i := by ring
         _ = -i := by rw [hi]; ring
  have hwq : w ^ (3 ^ m) = w⁻¹ := by
    apply (mul_right_cancel₀ hw0)
    rw [inv_mul_cancel₀ hw0, ← pow_succ, hw]
  have hwiq : (w⁻¹) ^ (3 ^ m) = w := by rw [inv_pow, hwq, inv_inv]
  have huq : (-(w + w⁻¹)) ^ (3 ^ m) = -(w + w⁻¹) := by
    change (iterateFrobenius E 3 m) (-(w + w⁻¹)) = -(w + w⁻¹)
    rw [map_neg, map_add]
    simp only [iterateFrobenius_def]
    rw [hwq, hwiq, add_comm]
  have hvq : (i * (w - w⁻¹)) ^ (3 ^ m) = i * (w - w⁻¹) := by
    rw [mul_pow, sub_pow_char_pow, hiq, hwq, hwiq]
    ring
  obtain ⟨u, hu⟩ := pow_fixed_mem_range (F := F) (-(w + w⁻¹)) (by rw [hcard]; exact huq)
  obtain ⟨v, hv⟩ := pow_fixed_mem_range (F := F) (i * (w - w⁻¹)) (by rw [hcard]; exact hvq)
  have hwi : w * w⁻¹ = 1 := mul_inv_cancel₀ hw0
  have hwi2 : w ^ 2 * w⁻¹ ^ 2 = 1 := by rw [← mul_pow, hwi, one_pow]
  have hcircle : u ^ 2 + v ^ 2 = 1 := by
    apply (algebraMap F E).injective
    simp only [map_add, map_pow, map_one, hu, hv]
    linear_combination (w - w⁻¹) ^ 2 * hi + 4 * hwi + h3E
  have hd : algebraMap F E (-u ^ 2 * v ^ 2) = w ^ 4 + w⁻¹ ^ 4 + 1 := by
    simp only [map_mul, map_neg, map_pow, hu, hv]
    calc -(-(w + w⁻¹)) ^ 2 * (i * (w - w⁻¹)) ^ 2 =
        (w + w⁻¹) ^ 2 * (w - w⁻¹) ^ 2 := by rw [mul_pow, hi]; ring
      _ = _ := by linear_combination -2 * hwi2 - h3E
  refine ⟨u, v, hcircle, ?_⟩
  intro x hx
  apply ht
  have he : (algebraMap F E x) ^ 3 - algebraMap F E x = w ^ 4 + w⁻¹ ^ 4 + 1 := by
    rw [← hd, ← hx]
    simp
  rw [← he]
  apply traceSum_artinSchreier
  rw [← map_pow, ← hcard, FiniteField.pow_card]

#print axioms weighted_trace_sum
#print axioms exists_torus_parameter
#print axioms exists_circle_parameter

end Erdos714NormCircleTrace
