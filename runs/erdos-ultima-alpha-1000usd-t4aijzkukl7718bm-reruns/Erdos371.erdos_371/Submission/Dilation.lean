import FormalConjecturesUtil

/-! Exact dilation identities for comparisons of largest prime factors. -/

namespace Erdos371Dilation

abbrev P := Nat.maxPrimeFac

def cmp (a b : ℕ) : ℤ := if a < b then 1 else -1

def sign (n : ℕ) : ℤ := cmp (P n) (P (n + 1))

def middle (n : ℕ) : Prop :=
  (P n < P (2 * n + 1) ∧ P (2 * n + 1) < P (n + 1)) ∨
  (P (n + 1) < P (2 * n + 1) ∧ P (2 * n + 1) < P n)

instance (n : ℕ) : Decidable (middle n) := inferInstanceAs (Decidable (_ ∨ _))

lemma consecutive_ne (n : ℕ) : P (n + 1) ≠ P n := by
  rcases n with _ | _ | n
  · simp [P]
  · decide +kernel
  · intro h
    have hp := Nat.prime_maxPrimeFac_of_one_lt (n + 2) (by omega)
    have hd : P (n + 2) ∣ n + 2 + 1 := by
      rw [← h]
      exact Nat.maxPrimeFac_dvd
    exact hp.not_dvd_one ((Nat.dvd_add_iff_right Nat.maxPrimeFac_dvd).2 hd)

lemma two_mul {n : ℕ} (hn : 2 ≤ n) : P (2 * n) = P n := by
  rw [P, Nat.maxPrimeFac_mul (by decide) (by omega)]
  have h2 : Nat.maxPrimeFac 2 = 2 := by decide +kernel
  rw [h2, max_eq_right]
  exact (Nat.prime_maxPrimeFac_of_one_lt n (by omega)).two_le

lemma cmp_insert {a b c : ℕ} (hab : a ≠ b) (hbc : b ≠ c) :
    cmp a b + cmp b c =
      if (a < b ∧ b < c) ∨ (c < b ∧ b < a) then 2 * cmp a c else 0 := by
  unfold cmp
  split_ifs <;> omega

lemma sign_pair {n : ℕ} (hn : 0 < n) :
    sign (2 * n) + sign (2 * n + 1) =
      if middle n then 2 * sign n else 0 := by
  by_cases hn1 : n = 1
  · subst n
    decide +kernel
  · have hn2 : 2 ≤ n := by omega
    have ha := consecutive_ne (2 * n)
    have hb := consecutive_ne (2 * n + 1)
    have he : 2 * n + 1 + 1 = 2 * (n + 1) := by omega
    rw [two_mul hn2] at ha
    rw [he, two_mul (by omega)] at hb
    simpa only [sign, middle, he, two_mul hn2, two_mul (by omega : 2 ≤ n + 1)] using
      (cmp_insert ha.symm hb.symm)


def total (N : ℕ) : ℤ := ∑ n ∈ Finset.range N, sign n

def middleTotal (N : ℕ) : ℤ :=
  ∑ n ∈ Finset.range N, if middle n then sign n else 0

lemma total_two_succ (N : ℕ) :
    total (2 * (N + 1)) = total (2 * N) + sign (2 * N) + sign (2 * N + 1) := by
  unfold total
  have he : 2 * (N + 1) = (2 * N + 1) + 1 := by omega
  rw [he, Finset.sum_range_succ, Finset.sum_range_succ]

lemma total_doubling {N : ℕ} (hN : 0 < N) :
    total (2 * N) = 2 + 2 * middleTotal N := by
  cases N with
  | zero => omega
  | succ N =>
    induction N with
    | zero => decide +kernel
    | succ N ih =>
      have hi := ih (by omega)
      rw [total_two_succ, hi]
      have hp := sign_pair (n := N + 1) (by omega)
      have hmstep : middleTotal (N + 1 + 1) = middleTotal (N + 1) +
          (if middle (N + 1) then sign (N + 1) else 0) := by
        exact Finset.sum_range_succ _ _
      rw [hmstep]
      by_cases hm : middle (N + 1)
      · simp only [hm, if_true] at hp ⊢
        linarith
      · simp only [hm, if_false] at hp ⊢
        linarith


lemma total_eq_count (N : ℕ) :
    total N = 2 * (((Finset.range N).filter (fun n => P n < P (n + 1))).card : ℤ) - N := by
  have hs (n : ℕ) : sign n = 2 * (if P n < P (n + 1) then (1 : ℤ) else 0) - 1 := by
    unfold sign cmp
    split_ifs <;> norm_num
  simp only [total, hs, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp

open Filter
open scoped Topology

lemma partialDensity_eq_total {N : ℕ} (hN : N ≠ 0) :
    {n | P n < P (n + 1)}.partialDensity Set.univ N =
      ((total N : ℝ) / N + 1) / 2 := by
  have he : {n | P n < P (n + 1)} ∩ Set.Iio N =
      ↑((Finset.range N).filter (fun n => P n < P (n + 1))) := by
    ext n
    simp [and_comm]
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio,
    he, Set.ncard_coe_finset]
  have ht : (total N : ℝ) =
      2 * (((Finset.range N).filter (fun n => P n < P (n + 1))).card : ℝ) - N := by
    exact_mod_cast total_eq_count N
  rw [ht]
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  field_simp
  ring

lemma density_half_iff_total_mean_zero :
    {n | P n < P (n + 1)}.HasDensity (1 / 2) ↔
      Tendsto (fun N : ℕ => (total N : ℝ) / N) atTop (𝓝 0) := by
  constructor
  · intro h
    have hh : Tendsto (fun N : ℕ =>
        2 * {n | P n < P (n + 1)}.partialDensity Set.univ N - 1)
        atTop (𝓝 (2 * (1 / 2 : ℝ) - 1)) :=
      (tendsto_const_nhds.mul h).sub tendsto_const_nhds
    norm_num at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hd := partialDensity_eq_total (Nat.ne_of_gt hN)
    linarith
  · intro h
    have hh : Tendsto (fun N : ℕ => ((total N : ℝ) / N + 1) / 2)
        atTop (𝓝 (1 / 2 : ℝ)) := by
      convert (h.add tendsto_const_nhds).div_const (2 : ℝ) using 1; norm_num
    apply hh.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact (partialDensity_eq_total (Nat.ne_of_gt hN)).symm

end Erdos371Dilation

#print axioms Erdos371Dilation.total_doubling
#print axioms Erdos371Dilation.density_half_iff_total_mean_zero
