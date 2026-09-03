import FormalConjecturesUtil
import Submission.CofactorReflection
import Submission.TerminalCompression

/-! Divisor switching for close largest prime factors. This supplies a counting
bound, not an orientation-balance theorem. -/

namespace Erdos371DivisorGapSwitch

open Erdos371Cofactor Erdos371TerminalCompression

def modPoints (a t e r M : ℕ) : Finset ℕ :=
  (Finset.range (M + 1)).filter fun q => Nat.ModEq a (t * q + e) r

lemma modPoints_card_le {a t : ℕ} (hcop : a.Coprime t) (e r M : ℕ) :
    (modPoints a t e r M).card ≤ M / a + 1 := by
  calc
    _ ≤ (Finset.range (M / a + 1)).card := by
      apply Finset.card_le_card_of_injOn (fun q => q / a)
      · intro q hq
        simp only [Finset.mem_coe, modPoints, Finset.mem_filter] at hq
        obtain ⟨hqM, _⟩ := hq
        have hqle : q ≤ M := by have := Finset.mem_range.mp hqM; omega
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hqle))
      · intro q hq s hs he
        change q / a = s / a at he
        simp only [Finset.mem_coe, modPoints, Finset.mem_filter] at hq hs
        have hmul := Nat.ModEq.add_right_cancel' e (hq.2.trans hs.2.symm)
        have hmod := Nat.ModEq.cancel_left_of_coprime hcop hmul
        have hq0 := Nat.mod_add_div q a
        have hs0 := Nat.mod_add_div s a
        change q % a = s % a at hmod
        rw [hmod, he] at hq0
        omega
    _ = _ := Finset.card_range _

def switchCandidates (a t N : ℕ) : Finset ℕ :=
  if a.Coprime t then
    ((modPoints a t 0 1 (N / a)).image fun q => a * (q + (t * q - 1) / a)) ∪
    ((modPoints a t 1 0 (N / a)).image fun q => a * (q + (t * q + 1) / a) - 1)
  else ∅

lemma switchCandidates_card_le (a t N : ℕ) :
    (switchCandidates a t N).card ≤ 2 * (N / a ^ 2 + 1) := by
  unfold switchCandidates
  split_ifs with hcop
  · calc
      _ ≤ (modPoints a t 0 1 (N / a)).card + (modPoints a t 1 0 (N / a)).card :=
        (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le)
      _ ≤ (N / a / a + 1) + (N / a / a + 1) :=
        Nat.add_le_add (modPoints_card_le hcop _ _ _) (modPoints_card_le hcop _ _ _)
      _ = _ := by rw [Nat.div_div_eq_div_mul]; simp [pow_two]; omega
  · simp

def switchCover (A T N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 A).biUnion fun a =>
    (Finset.Icc 1 (a / T)).biUnion fun t => switchCandidates a t N

lemma switchCover_card_bound {T : ℕ} (hT : 0 < T) (A N : ℕ) :
    ((switchCover A T N).card : ℝ) ≤
      2 * (N : ℝ) / T * H A + 2 * (A : ℝ)^2 / T := by
  have hT' : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hc : (switchCover A T N).card ≤
      ∑ a ∈ Finset.Icc 1 A, (a / T) * (2 * (N / a ^ 2 + 1)) := by
    apply Finset.card_biUnion_le.trans
    apply Finset.sum_le_sum
    intro a ha
    apply Finset.card_biUnion_le.trans
    calc
      _ ≤ ∑ _t ∈ Finset.Icc 1 (a / T), 2 * (N / a ^ 2 + 1) :=
        Finset.sum_le_sum (fun t _ => switchCandidates_card_le a t N)
      _ = _ := by simp
  have hs : (∑ a ∈ Finset.Icc 1 A, (a : ℝ)) ≤ (A : ℝ)^2 := by
    calc
      _ ≤ ∑ _a ∈ Finset.Icc 1 A, (A : ℝ) :=
        Finset.sum_le_sum (fun a ha => Nat.cast_le.mpr (Finset.mem_Icc.mp ha).2)
      _ = _ := by simp [pow_two]
  calc
    _ ≤ ∑ a ∈ Finset.Icc 1 A,
        ((a / T : ℕ) : ℝ) * (2 * (((N / a ^ 2 : ℕ) : ℝ) + 1)) := by exact_mod_cast hc
    _ ≤ ∑ a ∈ Finset.Icc 1 A,
        ((a : ℝ) / T) * (2 * ((N : ℝ) / (a : ℝ)^2 + 1)) := by
      apply Finset.sum_le_sum
      intro a ha
      apply mul_le_mul (Nat.cast_div_le) _ (by positivity) (by positivity)
      have hd : ((N / a ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) / ((a ^ 2 : ℕ) : ℝ) := Nat.cast_div_le
      push_cast at hd
      linarith
    _ = ∑ a ∈ Finset.Icc 1 A,
        (2 * (N : ℝ) / T * (1 / a) + (2 / T) * a) := by
      apply Finset.sum_congr rfl
      intro a ha
      have ha' : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (Finset.mem_Icc.mp ha).1; omega)
      field_simp
    _ = 2 * (N : ℝ) / T * H A + (2 / T) * ∑ a ∈ Finset.Icc 1 A, (a : ℝ) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rfl
    _ ≤ _ := by
      have hb := mul_le_mul_of_nonneg_left hs (show 0 ≤ (2 : ℝ) / T by positivity)
      convert add_le_add_left hb (2 * (N : ℝ) / T * H A) using 1 <;> ring

lemma coprime_of_neighbor_relation {a c t q : ℕ}
    (he : a * c + 1 = t * q ∨ a * c = t * q + 1) : a.Coprime t := by
  apply Nat.coprime_of_dvd'
  intro r hr hra hrt
  have hrac : r ∣ a * c := dvd_mul_of_dvd_left hra c
  have hrtq : r ∣ t * q := dvd_mul_of_dvd_left hrt q
  rcases he with he | he
  · rw [← he] at hrtq
    exact (Nat.dvd_add_iff_right hrac).2 hrtq
  · rw [he] at hrac
    exact (Nat.dvd_add_iff_right hrtq).2 hrac

lemma mem_switchCandidates_descent {a c t q N : ℕ} (ha : 0 < a)
    (he : a * c + 1 = t * q) (hN : a * (q + c) ≤ N) :
    a * (q + c) ∈ switchCandidates a t N := by
  have hcop := coprime_of_neighbor_relation (Or.inl he)
  rw [switchCandidates, if_pos hcop]
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  refine ⟨q, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      apply Nat.lt_succ_of_le
      apply (Nat.le_div_iff_mul_le ha).mpr
      nlinarith
    · change (t * q + 0) % a = 1 % a
      rw [← he]
      simp
  · have hc : (t * q - 1) / a = c := by
      have ht : t * q - 1 = a * c := by omega
      rw [ht, Nat.mul_div_right _ ha]
    rw [hc]

lemma mem_switchCandidates_ascent {a c t q N : ℕ} (ha : 0 < a)
    (he : a * c = t * q + 1) (hN : a * (q + c) ≤ N) :
    a * (q + c) - 1 ∈ switchCandidates a t N := by
  have hcop := coprime_of_neighbor_relation (Or.inr he)
  rw [switchCandidates, if_pos hcop]
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  refine ⟨q, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      apply Nat.lt_succ_of_le
      apply (Nat.le_div_iff_mul_le ha).mpr
      nlinarith
    · change (t * q + 1) % a = 0 % a
      rw [← he]
      simp
  · have hc : (t * q + 1) / a = c := by
      rw [← he, Nat.mul_div_right _ ha]
    rw [hc]

lemma cofactor_difference_bound {a c t q T : ℕ} (hq : T < q)
    (hc : c * T ≤ q) (he : a * c + 1 = t * q ∨ a * c = t * q + 1) :
    t * T ≤ a := by
  have hh := Nat.mul_le_mul_left a hc
  by_contra hn
  have hb := Nat.mul_le_mul_right q (show a + 1 ≤ t * T by omega)
  rcases he with he | he <;> nlinarith

lemma mem_switchCover_of_close {n N A T : ℕ} (hn : 3 ≤ n) (hnN : n < N)
    (hT : 0 < T)
    (hA : min (cofactor n) (cofactor (n + 1)) ≤ A)
    (hq : T < min (P n) (P (n + 1)))
    (hc : Nat.dist (P n) (P (n + 1)) * T ≤ min (P n) (P (n + 1))) :
    n ∈ switchCover A T N := by
  have hne := Erdos371PrimeDiscrepancy.consecutive_ne n
  change P (n + 1) ≠ P n at hne
  by_cases hinc : P n < P (n + 1)
  · have hba := (comparison_iff_cofactor_reverse hn).mp hinc
    rw [min_eq_right hba.le] at hA
    rw [min_eq_left hinc.le] at hq hc
    rw [Nat.dist_eq_sub_of_le hinc.le] at hc
    let a := cofactor (n + 1)
    let t := cofactor n - a
    let q := P n
    let c := P (n + 1) - q
    have ha : 0 < a := cofactor_pos (by omega)
    have ht : 0 < t := Nat.sub_pos_of_lt hba
    have hpq : q + c = P (n + 1) := by dsimp [q, c]; omega
    have hba' : a + t = cofactor n := by dsimp [a, t]; omega
    have hprod1 : a * (q + c) = n + 1 := by rw [hpq]; exact cofactor_mul _
    have hprod2 : (a + t) * q = n := by rw [hba']; exact cofactor_mul _
    have he : a * c = t * q + 1 := by nlinarith [hprod1, hprod2]
    have htT : t ≤ a / T := (Nat.le_div_iff_mul_le hT).mpr
      (cofactor_difference_bound hq hc (Or.inr he))
    apply Finset.mem_biUnion.mpr
    refine ⟨a, Finset.mem_Icc.mpr ⟨ha, hA⟩, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨t, Finset.mem_Icc.mpr ⟨ht, htT⟩, ?_⟩
    have hm := mem_switchCandidates_ascent ha he (show a * (q + c) ≤ N by omega)
    simpa only [hprod1, Nat.add_sub_cancel] using hm
  · have hdec : P (n + 1) < P n := by omega
    have hab : cofactor n < cofactor (n + 1) := by
      have hnc := cofactor_consecutive_ne hn
      have hh : ¬cofactor (n + 1) < cofactor n :=
        fun hh => hinc ((comparison_iff_cofactor_reverse hn).mpr hh)
      omega
    rw [min_eq_left hab.le] at hA
    rw [min_eq_right hdec.le] at hq hc
    rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hdec.le] at hc
    let a := cofactor n
    let t := cofactor (n + 1) - a
    let q := P (n + 1)
    let c := P n - q
    have ha : 0 < a := cofactor_pos (by omega)
    have ht : 0 < t := Nat.sub_pos_of_lt hab
    have hpq : q + c = P n := by dsimp [q, c]; omega
    have hba' : a + t = cofactor (n + 1) := by dsimp [a, t]; omega
    have hprod1 : a * (q + c) = n := by rw [hpq]; exact cofactor_mul _
    have hprod2 : (a + t) * q = n + 1 := by rw [hba']; exact cofactor_mul _
    have he : a * c + 1 = t * q := by nlinarith [hprod1, hprod2]
    have htT : t ≤ a / T := (Nat.le_div_iff_mul_le hT).mpr
      (cofactor_difference_bound hq hc (Or.inl he))
    apply Finset.mem_biUnion.mpr
    refine ⟨a, Finset.mem_Icc.mpr ⟨ha, hA⟩, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨t, Finset.mem_Icc.mpr ⟨ht, htT⟩, ?_⟩
    have hm := mem_switchCandidates_descent ha he (show a * (q + c) ≤ N by omega)
    simpa only [hprod1] using hm

end Erdos371DivisorGapSwitch

#print axioms Erdos371DivisorGapSwitch.switchCover_card_bound
#print axioms Erdos371DivisorGapSwitch.mem_switchCover_of_close

