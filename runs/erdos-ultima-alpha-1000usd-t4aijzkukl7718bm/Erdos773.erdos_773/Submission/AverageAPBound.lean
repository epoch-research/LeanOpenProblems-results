import FormalConjecturesUtil
import Submission.APBounds

/-! An average bound for three-term arithmetic progressions of squares.
This file does not settle Erdős 773. -/
namespace Erdos773.AverageAP
open Finset
set_option maxHeartbeats 1000000

lemma ap_parametrization {a b c N : ℕ} (hab : a < b) (hbc : b < c)
    (he : a ^ 2 + c ^ 2 = 2 * b ^ 2) (hcN : c ≤ N) :
    ∃ r ∈ Icc 1 (4 * N), ∃ s ∈ Icc 1 (4 * N),
      ∃ k ∈ Icc 1 (4 * N / (max r s) ^ 2),
        4 * a + k * r ^ 2 = 2 * k * s ^ 2 ∧
        4 * b = k * (2 * s ^ 2 + 2 * r * s + r ^ 2) ∧
        4 * c = k * (2 * s ^ 2 + 4 * r * s + r ^ 2) := by
  obtain ⟨hy, hd, hb, hc, hfac⟩ := squareAP_parameters hab hbc he
  let y := c - b
  let d := 2 * b - (a + c)
  change 0 < y at hy
  change 0 < d at hd
  change a + y + d = b at hb
  change a + 2 * y + d = c at hc
  change 2 * y ^ 2 = d * (2 * a + d) at hfac
  obtain ⟨g,r,s,hg,hrs,hdr,hys⟩ :=
    Nat.exists_coprime' (Nat.gcd_pos_of_pos_left y hd)
  have hr : 0 < r := by
    by_contra! hh
    have hz : r = 0 := by omega
    rw [hz, zero_mul] at hdr
    omega
  have hs : 0 < s := by
    by_contra! hh
    have hz : s = 0 := by omega
    rw [hz, zero_mul] at hys
    omega
  have hfac' : (2 * g) * s ^ 2 = r * (2 * a + r * g) := by
    apply Nat.eq_of_mul_eq_mul_right hg
    simpa only [hdr, hys, pow_two, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm]
      using hfac
  have hr2g : r ∣ 2 * g := (hrs.pow_right 2).dvd_of_dvd_mul_right
    ⟨2 * a + r * g, hfac'⟩
  obtain ⟨k,hkg⟩ := hr2g
  have hk : 0 < k := by
    by_contra! hh
    have hz : k = 0 := by omega
    rw [hz, mul_zero] at hkg
    omega
  have he' : k * s ^ 2 = 2 * a + r * g := by
    apply Nat.eq_of_mul_eq_mul_left hr
    calc
      r * (k * s ^ 2) = (r * k) * s ^ 2 := by ring
      _ = _ := by rw [← hkg]; exact hfac'
  have hkr : k * r ^ 2 = 2 * d := by
    calc
      _ = r * (r * k) := by ring
      _ = r * (2 * g) := by rw [← hkg]
      _ = _ := by rw [hdr]; ring
  have hkrs : k * r * s = 2 * y := by
    calc
      _ = s * (r * k) := by ring
      _ = s * (2 * g) := by rw [← hkg]
      _ = _ := by rw [hys]; ring
  have hA : 4 * a + k * r ^ 2 = 2 * k * s ^ 2 := by
    rw [hkr]
    have hh : k * s ^ 2 = 2 * a + d := by simpa only [← hdr] using he'
    nlinarith only [hh]
  have hB : 4 * b = k * (2 * s ^ 2 + 2 * r * s + r ^ 2) := by
    nlinarith only [hb,hA,hkr,hkrs]
  have hC : 4 * c = k * (2 * s ^ 2 + 4 * r * s + r ^ 2) := by
    nlinarith only [hc,hA,hkr,hkrs]
  have hkmax : k * (max r s) ^ 2 ≤ 4 * N := by
    rcases le_total r s with h | h
    · rw [max_eq_right h]
      nlinarith only [hC, hcN, Nat.zero_le (k * r * s), Nat.zero_le (k * r ^ 2)]
    · rw [max_eq_left h]
      nlinarith only [hC, hcN, Nat.zero_le (k * r * s), Nat.zero_le (k * s ^ 2)]
  have hmax : 0 < max r s := lt_of_lt_of_le hr (le_max_left _ _)
  have hmaxN : max r s ≤ 4 * N := by
    have hh := Nat.mul_le_mul_right ((max r s) ^ 2) hk
    exact (Nat.le_self_pow (by decide : 2 ≠ 0) (max r s)).trans
      ((by simpa using hh : (max r s) ^ 2 ≤ k * (max r s) ^ 2).trans hkmax)
  have hkN := (Nat.le_div_iff_mul_le (pow_pos hmax 2)).mpr hkmax
  exact ⟨r, mem_Icc.mpr ⟨hr,(le_max_left r s).trans hmaxN⟩,
    s, mem_Icc.mpr ⟨hs,(le_max_right r s).trans hmaxN⟩,
    k, mem_Icc.mpr ⟨hk,hkN⟩, hA,hB,hC⟩

def parameterImage (M : ℕ) (rs : ℕ × ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  (Icc 1 (M / (max rs.1 rs.2) ^ 2)).image (fun k =>
    (((2 * k * rs.2 ^ 2 - k * rs.1 ^ 2) / 4,
      k * (2 * rs.2 ^ 2 + 2 * rs.1 * rs.2 + rs.1 ^ 2) / 4),
      k * (2 * rs.2 ^ 2 + 4 * rs.1 * rs.2 + rs.1 ^ 2) / 4))

lemma squareAPs_card_le_parameters (N : ℕ) :
    (squareAPs N).card ≤
      ∑ r ∈ Icc 1 (4 * N), ∑ s ∈ Icc 1 (4 * N), 4 * N / (max r s) ^ 2 := by
  have hsub : squareAPs N ⊆
      ((Icc 1 (4 * N)) ×ˢ (Icc 1 (4 * N))).biUnion (parameterImage (4 * N)) := by
    rintro ⟨⟨a,b⟩,c⟩ ht
    obtain ⟨ht, hab, hbc, he⟩ := mem_filter.mp ht
    dsimp only at hab hbc he
    have hcN : c ≤ N := by
      simp only [mem_product, mem_Icc] at ht
      exact ht.2.2
    obtain ⟨r,hr,s,hs,k,hk,hA,hB,hC⟩ := ap_parametrization hab hbc he hcN
    apply mem_biUnion.mpr
    refine ⟨(r,s), mem_product.mpr ⟨hr,hs⟩, ?_⟩
    apply mem_image.mpr
    refine ⟨k, hk, ?_⟩
    have ha : 2 * k * s ^ 2 - k * r ^ 2 = 4 * a := by omega
    simp [ha, ← hB, ← hC]
  calc
    _ ≤ (((Icc 1 (4*N)) ×ˢ (Icc 1 (4*N))).biUnion (parameterImage (4*N))).card :=
      card_le_card hsub
    _ ≤ ∑ rs ∈ (Icc 1 (4*N)) ×ˢ (Icc 1 (4*N)), (parameterImage (4*N) rs).card :=
      card_biUnion_le
    _ ≤ ∑ rs ∈ (Icc 1 (4*N)) ×ˢ (Icc 1 (4*N)), 4*N / (max rs.1 rs.2) ^ 2 := by
      apply sum_le_sum
      intro rs hrs
      exact card_image_le.trans_eq (by simp)
    _ = _ := by rw [sum_product]

lemma max_sum_bound (M : ℕ) :
    (∑ r ∈ Icc 1 M, ∑ s ∈ Icc 1 M, M / (max r s) ^ 2) ≤
      2 * ∑ r ∈ Icc 1 M, r * (M / r ^ 2) := by
  have hpoint (r s : ℕ) : M / (max r s) ^ 2 ≤
      (if s ≤ r then M / r ^ 2 else 0) + (if r ≤ s then M / s ^ 2 else 0) := by
    rcases le_total r s with h | h
    · simp [max_eq_right h, h]
    · simp [max_eq_left h, h]
  have hsum (r : ℕ) (hr : r ∈ Icc 1 M) :
      ∑ s ∈ Icc 1 M, (if s ≤ r then M / r ^ 2 else 0) = r * (M / r ^ 2) := by
    have hf : (Icc 1 M).filter (fun s => s ≤ r) = Icc 1 r := by
      ext s
      simp only [mem_filter, mem_Icc]
      have := (mem_Icc.mp hr).2
      omega
    rw [← sum_filter, hf]
    simp
  calc
    _ ≤ ∑ r ∈ Icc 1 M, ∑ s ∈ Icc 1 M,
        ((if s ≤ r then M / r ^ 2 else 0) + (if r ≤ s then M / s ^ 2 else 0)) := by
      exact sum_le_sum (fun r hr => sum_le_sum (fun s hs => hpoint r s))
    _ = (∑ r ∈ Icc 1 M, ∑ s ∈ Icc 1 M, if s ≤ r then M / r ^ 2 else 0) +
        (∑ s ∈ Icc 1 M, ∑ r ∈ Icc 1 M, if r ≤ s then M / s ^ 2 else 0) := by
      simp only [sum_add_distrib]
      congr 1
      exact sum_comm
    _ = _ := by
      rw [sum_congr rfl hsum]
      omega

lemma sum_floor_bound (M : ℕ) :
    (∑ r ∈ Icc 1 M, (r : ℝ) * (M / r ^ 2 : ℕ)) ≤ (M : ℝ) * harmonic M := by
  have hp (r : ℕ) (hr : r ∈ Icc 1 M) :
      (r : ℝ) * (M / r ^ 2 : ℕ) ≤ (M : ℝ) / r := by
    have hrpos : (0 : ℝ) < r := by exact_mod_cast (mem_Icc.mp hr).1
    have hprod : (r : ℝ) ^ 2 * (M / r ^ 2 : ℕ) ≤ M := by
      exact_mod_cast Nat.mul_div_le M (r ^ 2)
    apply (le_div_iff₀ hrpos).mpr
    nlinarith only [hprod]
  calc
    _ ≤ ∑ r ∈ Icc 1 M, (M : ℝ) / r := sum_le_sum hp
    _ = _ := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      simp [div_eq_mul_inv, mul_sum]

lemma squareAPs_log_bound (N : ℕ) :
    ((squareAPs N).card : ℝ) ≤ 8 * (N : ℝ) * (1 + Real.log (4 * N)) := by
  have hnat := (squareAPs_card_le_parameters N).trans (max_sum_bound (4 * N))
  have hreal : ((squareAPs N).card : ℝ) ≤
      2 * ∑ r ∈ Icc 1 (4 * N), (r : ℝ) * (4 * N / r ^ 2 : ℕ) := by
    exact_mod_cast hnat
  have h := sum_floor_bound (4 * N)
  have hh := harmonic_le_one_add_log (4 * N)
  have hmul := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (4 * N) : (0:ℝ) ≤ (4*N:ℕ))
  push_cast at h hmul
  nlinarith only [hreal,h,hmul]

#print axioms ap_parametrization
#print axioms squareAPs_log_bound
end Erdos773.AverageAP
