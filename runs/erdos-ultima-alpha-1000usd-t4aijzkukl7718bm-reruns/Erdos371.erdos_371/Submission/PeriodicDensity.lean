import FormalConjecturesUtil

/-! Density of periodic predicates, for investigating the cutoff approach to Erdős 371. -/

open Filter
open scoped Topology

namespace Erdos371Exploration

lemma periodic_count_blocks (p : ℕ → Prop) [DecidablePred p] {Q : ℕ}
    (hp : ∀ n, p (n + Q) ↔ p n) (r q : ℕ) :
    ((Finset.range (r + Q * q)).filter p).card =
      q * ((Finset.range Q).filter p).card + ((Finset.range r).filter p).card := by
  let f : ℕ → ℕ := fun n => if p n then 1 else 0
  have hf (n : ℕ) : f (Q + n) = f n := by simp [f, Nat.add_comm Q n, hp]
  have hcount (n : ℕ) : ((Finset.range n).filter p).card = ∑ x ∈ Finset.range n, f x := by
    simpa [f] using (Finset.sum_boole (R := ℕ) p (Finset.range n)).symm
  have hb (n : ℕ) : ((Finset.range (n + Q)).filter p).card =
      ((Finset.range n).filter p).card + ((Finset.range Q).filter p).card := by
    simp only [hcount]
    rw [Nat.add_comm n Q, Finset.sum_range_add]
    have he : (∑ x ∈ Finset.range n, f (Q + x)) = ∑ x ∈ Finset.range n, f x := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hf x
    change (∑ x ∈ Finset.range Q, f x) + (∑ x ∈ Finset.range n, f (Q + x)) =
      (∑ x ∈ Finset.range n, f x) + (∑ x ∈ Finset.range Q, f x)
    rw [he, Nat.add_comm]
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc, hb, ih, Nat.succ_mul]
      omega

lemma periodic_count_remainder (p : ℕ → Prop) [DecidablePred p] {Q : ℕ}
    (hp : ∀ n, p (n + Q) ↔ p n) (n : ℕ) :
    ((Finset.range n).filter p).card =
      (n / Q) * ((Finset.range Q).filter p).card +
        ((Finset.range (n % Q)).filter p).card := by
  have h := periodic_count_blocks p hp (n % Q) (n / Q)
  rwa [Nat.mod_add_div] at h

lemma partialDensity_eq_count (p : ℕ → Prop) [DecidablePred p] (n : ℕ) :
    {n | p n}.partialDensity Set.univ n =
      (((Finset.range n).filter p).card : ℝ) / n := by
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
  congr 2
  have he : {n | p n} ∩ Set.Iio n = ↑((Finset.range n).filter p) := by
    ext k
    simp [and_comm]
  rw [he, Set.ncard_coe_finset]

lemma periodic_half_density (p : ℕ → Prop) [DecidablePred p] {Q : ℕ} (hQ : 0 < Q)
    (hp : ∀ n, p (n + Q) ↔ p n)
    (hc : 2 * ((Finset.range Q).filter p).card = Q) :
    {n | p n}.HasDensity (1 / 2) := by
  let c := fun n => ((Finset.range n).filter p).card
  have hbound (n : ℕ) :
      (n : ℝ) - Q ≤ 2 * (c n : ℝ) ∧ 2 * (c n : ℝ) ≤ (n : ℝ) + Q := by
    have hform := periodic_count_remainder p hp n
    change c n = (n / Q) * c Q + c (n % Q) at hform
    have hrem : c (n % Q) ≤ n % Q := by
      exact le_trans (Finset.card_filter_le _ _) (by simp)
    have hdiv := Nat.mod_add_div n Q
    have hrlt := Nat.mod_lt n hQ
    have hc' : 2 * c Q = Q := hc
    have ha : 2 * c n + Q ≥ n ∧ 2 * c n ≤ n + Q := by
      constructor <;> nlinarith
    constructor
    · have hr : (n : ℝ) ≤ 2 * (c n : ℝ) + Q := by exact_mod_cast ha.1
      linarith
    · exact_mod_cast ha.2
  have hlim : Tendsto (fun n : ℕ => (Q : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hlow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) - Q / n) atTop (𝓝 (1 / 2)) := by
    simpa using tendsto_const_nhds.sub hlim
  have hupp : Tendsto (fun n : ℕ => (1 / 2 : ℝ) + Q / n) atTop (𝓝 (1 / 2)) := by
    simpa using tendsto_const_nhds.add hlim
  rw [Set.HasDensity]
  simp_rw [partialDensity_eq_count]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hb := (hbound n).1
    change (1 / 2 : ℝ) - Q / n ≤ (c n : ℝ) / n
    apply (le_div_iff₀ hn').mpr
    have he : ((1 / 2 : ℝ) - Q / n) * n = (n : ℝ) / 2 - Q := by
      field_simp
    rw [he]
    have hQ' : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
    linarith
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hb := (hbound n).2
    change (c n : ℝ) / n ≤ (1 / 2 : ℝ) + Q / n
    apply (div_le_iff₀ hn').mpr
    have he : ((1 / 2 : ℝ) + Q / n) * n = (n : ℝ) / 2 + Q := by
      field_simp
    rw [he]
    have hQ' : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
    linarith

end Erdos371Exploration
